module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38Frame
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38Cover

public section

namespace CFSG.AGLEmbedding.ChevOuter.U38

open CFSG.Quasithin CFSG.AGLEmbedding.ChevOuter CFSG.AGLEmbedding.ChevOuter.GF64
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.LowTwoRank
open scoped Matrix

theorem eigenvalue_cube {M : Matrix (Fin 3) (Fin 3) GF64} (hM3 : M ^ 3 = 1)
    {b : Fin 3 → (Fin 3 → GF64)} (hb : LinearIndependent GF64 b) {c : GF64} {i : Fin 3}
    (hM : M *ᵥ b i = c • b i) : c ^ 3 = 1 := by
  have h1 := pow_mulVec_of_eigen hM 3
  rw [hM3, Matrix.one_mulVec] at h1
  have hbi : b i ≠ 0 := hb.ne_zero i
  have := smul_left_injective GF64 hbi
    (show (1 : GF64) • b i = c ^ 3 • b i by rw [one_smul]; exact h1)
  exact this.symm

theorem card_le_nine_elem_su (T : Subgroup SU) (hT : CFSG.Open.IsElemAbelian 3 T) :
    Nat.card T ≤ 9 := by
  classical
  by_contra hlt
  push Not at hlt
  set φ : T →* GL (Fin 3) GF64 ⧸ StatedScalars (Fin 3) GF64 :=
    (QuotientGroup.mk' (StatedScalars (Fin 3) GF64)).comp (SU.subtype.comp T.subtype) with hφ
  have hφt : ∀ t : T, φ t =
      (((t : SU) : GL (Fin 3) GF64) : GL (Fin 3) GF64 ⧸ StatedScalars (Fin 3) GF64) :=
    fun t => rfl
  have hker : Nat.card φ.ker ≤ 3 := by
    have hmem : ∀ t : φ.ker, (t.1 : SU) ∈ unitaryScalars hU 3 := by
      intro t
      have h1 := MonoidHom.mem_ker.1 t.2
      rw [hφt, QuotientGroup.eq_one_iff] at h1
      rw [unitaryScalars_eq hU (by norm_num), Subgroup.mem_subgroupOf]
      exact h1
    have hinj : Function.Injective
        (fun t : φ.ker => (⟨(t.1 : SU), hmem t⟩ : unitaryScalars hU 3)) := by
      intro s t hst
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun u : unitaryScalars hU 3 => (u : SU)) hst
    calc Nat.card φ.ker ≤ Nat.card (unitaryScalars hU 3) := Nat.card_le_card_of_injective _ hinj
      _ = 3 := card_scalars
  have hrange : 3 < Nat.card φ.range := by
    have := Subgroup.card_ker_mul_card_range φ
    by_contra hle
    push Not at hle
    have : Nat.card φ.ker * Nat.card φ.range ≤ 3 * 3 := Nat.mul_le_mul hker hle
    omega
  have hcommR : ∀ x ∈ φ.range, ∀ y ∈ φ.range, x * y = y * x := by
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg φ (hT.1.is_comm.comm s t)
  have hT3 : ∀ t : T, ((t : SU) : GL (Fin 3) GF64) ^ 3 = 1 := fun t => by
    have := hT.2 t t.2
    exact congrArg (fun s : SU => (s : GL (Fin 3) GF64)) this
  have hexpR : ∀ x ∈ φ.range, x ^ 3 = 1 := by
    rintro _ ⟨t, rfl⟩
    rw [← map_pow]
    have : t ^ 3 = 1 := Subtype.ext (hT.2 t t.2)
    rw [this, map_one]
  rcases frame_or_heis three_ne_zero_GF64 omegaC_cube omegaC_ne_one φ.range hcommR hexpR hrange
    with ⟨b, hb, hbE, -⟩ | ⟨y₁, y₂, hy₁, hy₂, ζ, hζ1, hζ⟩
  · choose c hc using fun (t : T) (i : Fin 3) => hbE ((t : SU) : GL (Fin 3) GF64) ⟨t, rfl⟩ i
    have hc3 : ∀ t i, c t i ^ 3 = 1 := by
      intro t i
      refine eigenvalue_cube ?_ hb (hc t i)
      rw [← Units.val_pow_eq_pow_val, hT3 t, Units.val_one]
    have hdet : ∀ t, c t 0 * c t 1 * c t 2 = 1 := by
      intro t
      rw [← det_eq_prod_of_eigenbasis hb (hc t)]
      exact (mem_SU_iff'.1 (t : SU).2).1
    have hBu : IsUnit (Matrix.of fun r i => b i r : Matrix (Fin 3) (Fin 3) GF64) :=
      Matrix.isUnit_iff_isUnit_det _ |>.2 (isUnit_det_of_linearIndependent hb)
    have hne : ∀ t i, c t i ≠ 0 := by
      intro t i h0
      have := hc3 t i
      rw [h0] at this
      norm_num at this
    let r : T → Fin 3 → rootsOfUnity 3 GF64 := fun t i =>
      ⟨Units.mk0 (c t i) (hne t i), (mem_rootsOfUnity 3 _).2 (Units.ext (by simp [hc3 t i]))⟩
    have hr : ∀ t i, (((r t i : rootsOfUnity 3 GF64) : GF64ˣ) : GF64) = c t i := fun t i => rfl
    have hinj : Function.Injective (fun t : T => (r t 0, r t 1)) := by
      intro s t hst
      have hst' : (r s 0, r s 1) = (r t 0, r t 1) := hst
      have h0r : r s 0 = r t 0 := congrArg Prod.fst hst'
      have h1r : r s 1 = r t 1 := congrArg Prod.snd hst'
      have h0 : c s 0 = c t 0 := by rw [← hr, ← hr, h0r]
      have h1 : c s 1 = c t 1 := by rw [← hr, ← hr, h1r]
      have h2 : c s 2 = c t 2 := by
        have hs := hdet s
        have ht := hdet t
        have hne' : c t 0 * c t 1 ≠ 0 := mul_ne_zero (hne t 0) (hne t 1)
        rw [h0, h1] at hs
        exact mul_left_cancel₀ hne' (hs.trans ht.symm)
      have hcs : c s = c t := by
        funext i
        fin_cases i
        exacts [h0, h1, h2]
      have hM := mul_eigenmatrix (hc s)
      rw [hcs, ← mul_eigenmatrix (hc t)] at hM
      have := (hBu.mul_left_inj).1 hM
      exact Subtype.ext (Subtype.ext (Units.ext this))
    have hcardle : Nat.card T ≤ Nat.card (rootsOfUnity 3 GF64 × rootsOfUnity 3 GF64) :=
      Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_prod] at hcardle
    have h3 : Nat.card (rootsOfUnity 3 GF64) ≤ 3 := card_rootsOfUnity GF64 3
    have := Nat.mul_le_mul h3 h3
    omega
  · obtain ⟨t₁, ht₁⟩ := hy₁
    obtain ⟨t₂, ht₂⟩ := hy₂
    have hc12 : Commute ((t₁ : SU) : GL (Fin 3) GF64) ((t₂ : SU) : GL (Fin 3) GF64) :=
      congrArg (fun t : T => ((t : SU) : GL (Fin 3) GF64)) (hT.1.is_comm.comm t₁ t₂)
    exact hζ1 (zeta_eq_one_of_commute hc12 ht₁ ht₂ hζ)

end CFSG.AGLEmbedding.ChevOuter.U38
