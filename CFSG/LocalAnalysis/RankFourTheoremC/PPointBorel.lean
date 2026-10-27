module

public import CFSG.CharacterTheory.PSL2Table.Basic
public import CFSG.LocalAnalysis.SectionRank.OddCover.PSL2
import CFSG.CharacterTheory.PSL2Table.Tori
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoFacts
import CFSG.LocalAnalysis.RankFourTheoremC.PPointSemilinear

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open Subgroup CFSG.SectionRank.OddCover
open scoped MatrixGroups

theorem exists_conj_of_card_eq_pow_factorization {P : Type*} [Group P] [Finite P] {p : ℕ}
    [Fact p.Prime] {E E' : Subgroup P} (hE : Nat.card E = p ^ (Nat.card P).factorization p)
    (hE' : Nat.card E' = p ^ (Nat.card P).factorization p) :
    ∃ g : P, ∀ y, y ∈ E ↔ g * y * g⁻¹ ∈ E' := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq P (Sylow.ofCard E hE) (Sylow.ofCard E' hE')
  have h := congrArg (fun Q : Sylow p P => (Q : Subgroup P)) hg
  simp only [Sylow.coe_subgroup_smul, Sylow.coe_ofCard] at h
  have hmap : E.map (MulAut.conj g).toMonoidHom = E' := by
    rw [← h]
    ext x
    rw [Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
    rfl
  refine ⟨g, fun y => ?_⟩
  rw [← hmap]
  exact (Subgroup.mem_map_iff_mem (MulAut.conj g).injective).symm

theorem borel_conj_unip {F : Type} [Field F] (B : SL(2, F))
    (hB : (B : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) (t : F) :
    B * CFSG.PSL2Table.unip t * B⁻¹ =
      CFSG.PSL2Table.unip (((B : Matrix (Fin 2) (Fin 2) F) 0 0) ^ 2 * t) := by
  have hdet := CFSG.PSL2Table.det_entries B
  rw [hB, mul_zero, sub_zero] at hdet
  apply CFSG.PSL2Table.SL_ext <;>
    simp [CFSG.PSL2Table.mul_apply_SL, Matrix.adjugate_fin_two, hB]
  · exact hdet
  · ring
  · linear_combination hdet

theorem exists_borelTorusData {K : Type} [Group K] [Finite K] {F : Type} [Field F] [Finite F]
    {n : ℕ} (hF : Nat.card F = 3 ^ n)
    (e : K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) (T : Sylow 3 K) :
    ∃ f : F → K, Function.Injective f ∧ (∀ s t, f (s + t) = f s * f t) ∧
      (∀ t, f t ∈ (T : Subgroup K)) ∧ (∀ k ∈ (T : Subgroup K), ∃ t, f t = k) ∧
      (∀ a : Fˣ, ∃ τ ∈ normalizer ((T : Subgroup K) : Set K),
        ∀ t : F, τ * f t * τ⁻¹ = f ((a : F) ^ 2 * t)) ∧
      ∀ τ ∈ normalizer ((T : Subgroup K) : Set K), ∃ b : Fˣ, ∀ t : F,
        τ * f t * τ⁻¹ = f ((b : F) ^ 2 * t) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hfac : (Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)).factorization 3 = n :=
    factorization_card_psl_two hp (by norm_num) hF
  set U₀ : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    (pslU (K := F)).range with hU₀
  have hU₀card : Nat.card U₀ =
      3 ^ (Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)).factorization 3 := by
    rw [hfac, ← hF]
    exact (Nat.card_congr (MonoidHom.ofInjective (pslU_injective (K := F))).toEquiv).symm
  set A : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    (T : Subgroup K).map e.toMonoidHom with hA
  have hAcard : Nat.card A =
      3 ^ (Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)).factorization 3 := by
    have h1 : Nat.card (T : Subgroup K) = 3 ^ (Nat.card K).factorization 3 :=
      Sylow.card_eq_multiplicity T
    have h2 : Nat.card K = Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
      Nat.card_congr e.toEquiv
    rw [← h2, ← h1]
    exact (Nat.card_congr (e.subgroupMap (T : Subgroup K)).toEquiv).symm
  obtain ⟨g, hg⟩ := exists_conj_of_card_eq_pow_factorization hU₀card hAcard
  set f : F → K := fun t => e.symm (g * pslU (Multiplicative.ofAdd t) * g⁻¹) with hf
  have hfmem : ∀ t, f t ∈ (T : Subgroup K) := by
    intro t
    have h1 : g * pslU (Multiplicative.ofAdd t) * g⁻¹ ∈ A := (hg _).mp ⟨_, rfl⟩
    obtain ⟨k, hk, hke⟩ := h1
    have : e.symm (g * pslU (Multiplicative.ofAdd t) * g⁻¹) = k := by
      rw [← hke]; simp
    show e.symm (g * pslU (Multiplicative.ofAdd t) * g⁻¹) ∈ (T : Subgroup K)
    rw [this]
    exact hk
  have hsurj : ∀ k ∈ (T : Subgroup K), ∃ t, f t = k := by
    intro k hk
    have h1 : g⁻¹ * e k * g ∈ U₀ := by
      refine (hg _).mpr ?_
      rw [show g * (g⁻¹ * e k * g) * g⁻¹ = e k by group]
      exact ⟨k, hk, rfl⟩
    obtain ⟨u, hu⟩ := h1
    refine ⟨u.toAdd, ?_⟩
    simp only [hf]
    have : pslU (Multiplicative.ofAdd u.toAdd) = g⁻¹ * e k * g := by simpa using hu
    rw [this, show g * (g⁻¹ * e k * g) * g⁻¹ = e k by group]
    simp
  refine ⟨f, ?_, ?_, hfmem, hsurj, ?_, ?_⟩
  · intro s t hst
    have := e.symm.injective hst
    have h2 : pslU (Multiplicative.ofAdd s) = pslU (Multiplicative.ofAdd t) := by
      simpa using this
    exact Multiplicative.ofAdd.injective (pslU_injective h2)
  · intro s t
    simp only [hf]
    rw [← map_mul]
    congr 1
    rw [ofAdd_add, map_mul]
    group
  · intro a
    have hrel : ∀ t : F, e.symm (g * pslMk (slD a) * g⁻¹) * f t * (e.symm (g * pslMk (slD a) *
        g⁻¹))⁻¹ = f ((a : F) ^ 2 * t) := by
      intro t
      simp only [hf]
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      calc g * pslMk (slD a) * g⁻¹ * (g * pslU (Multiplicative.ofAdd t) * g⁻¹) *
            (g * pslMk (slD a) * g⁻¹)⁻¹
          = g * (pslMk (slD a) * pslU (Multiplicative.ofAdd t) * (pslMk (slD a))⁻¹) * g⁻¹ := by
            group
        _ = _ := by rw [pslD_conj_pslU]
    refine ⟨e.symm (g * pslMk (slD a) * g⁻¹), ?_, hrel⟩
    set τ : K := e.symm (g * pslMk (slD a) * g⁻¹) with hτ
    have hmaps : ∀ h ∈ (T : Subgroup K), τ * h * τ⁻¹ ∈ (T : Subgroup K) := by
      intro h hh
      obtain ⟨u, rfl⟩ := hsurj h hh
      rw [hrel u]
      exact hfmem _
    let c : ↥(T : Subgroup K) → ↥(T : Subgroup K) := fun h => ⟨τ * h * τ⁻¹, hmaps h h.2⟩
    have hcinj : Function.Injective c := by
      intro h h' hh
      have h2 : τ * (h : K) * τ⁻¹ = τ * (h' : K) * τ⁻¹ :=
        congrArg (Subtype.val : ↥(T : Subgroup K) → K) hh
      exact Subtype.ext (mul_left_cancel (mul_right_cancel h2))
    have hcsurj : Function.Surjective c := Finite.surjective_of_injective hcinj
    rw [mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hmaps h hh, fun hh => ?_⟩
    obtain ⟨⟨t, ht⟩, hct⟩ := hcsurj ⟨τ * h * τ⁻¹, hh⟩
    have := congrArg (Subtype.val : ↥(T : Subgroup K) → K) hct
    have h2 : τ * t * τ⁻¹ = τ * h * τ⁻¹ := this
    have : t = h := by simpa using h2
    exact this ▸ ht

  ·
    intro τ hτ
    have hFp : CharP F 3 := charP_three_of_card_eq_pow hF
    have hcharF : ringChar F ≠ 2 := by
      rw [ringChar.eq F 3]
      norm_num
    have hτA : e τ ∈ normalizer (A : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) :=
      Subgroup.le_normalizer_map e.toMonoidHom ⟨τ, hτ, rfl⟩
    set β : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F := g⁻¹ * e τ * g with hβ
    have hU₀eq : U₀ = CFSG.PSL2Table.unipotent F := by
      ext y
      constructor
      · rintro ⟨t, rfl⟩
        exact CFSG.PSL2Table.mk_unip_mem_unipotent t.toAdd
      · intro hy
        obtain ⟨t, rfl⟩ := (CFSG.PSL2Table.mem_unipotent_iff_exists y).mp hy
        exact ⟨Multiplicative.ofAdd t, rfl⟩
    have hβU : β ∈ normalizer ((CFSG.PSL2Table.unipotent F : Subgroup _) : Set _) := by
      rw [← hU₀eq, mem_normalizer_iff]
      intro y
      rw [hg y, hg (β * y * β⁻¹)]
      have h1 : g * (β * y * β⁻¹) * g⁻¹ = e τ * (g * y * g⁻¹) * (e τ)⁻¹ := by
        simp only [hβ]
        group
      rw [h1]
      exact mem_normalizer_iff.mp hτA (g * y * g⁻¹)
    rw [CFSG.AGLEmbedding.normalizer_unipotent_eq_borel hcharF] at hβU
    obtain ⟨B, hB, hBβ⟩ := hβU
    have hB10 : (B : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := CFSG.PSL2Table.mem_borelSL_iff B |>.mp hB
    have hBa : (B : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
      have hdet := CFSG.PSL2Table.det_entries B
      rw [hB10, mul_zero, sub_zero] at hdet
      exact left_ne_zero_of_mul_eq_one hdet
    refine ⟨Units.mk0 _ hBa, fun t => ?_⟩
    have hconj : β * pslU (Multiplicative.ofAdd t) * β⁻¹ =
        pslU (Multiplicative.ofAdd (((B : Matrix (Fin 2) (Fin 2) F) 0 0) ^ 2 * t)) := by
      have hu : ∀ s : F,
          pslU (Multiplicative.ofAdd s) = CFSG.PSL2Table.mk (CFSG.PSL2Table.unip s) := fun s => rfl
      rw [← hBβ, hu, hu, ← map_inv, ← map_mul, ← map_mul,
        borel_conj_unip B hB10 t]
    simp only [hf, Units.val_mk0]
    have h2 : e τ * (g * pslU (Multiplicative.ofAdd t) * g⁻¹) * (e τ)⁻¹ =
        g * (β * pslU (Multiplicative.ofAdd t) * β⁻¹) * g⁻¹ := by
      simp only [hβ]
      group
    calc τ * e.symm (g * pslU (Multiplicative.ofAdd t) * g⁻¹) * τ⁻¹
        = e.symm (e τ * (g * pslU (Multiplicative.ofAdd t) * g⁻¹) * (e τ)⁻¹) := by
          simp
      _ = _ := by rw [h2, hconj]

end CFSG.LocalAnalysis.RankFourTheoremC
