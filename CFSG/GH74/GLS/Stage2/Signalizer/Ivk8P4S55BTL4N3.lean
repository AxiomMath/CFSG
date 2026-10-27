module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTL4N2

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

namespace BL4

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {F : Type} [Field F] {p : ℕ} {W : Subgroup (projectiveSL 4 F)}

theorem pow_four_of_mem_scalars {s : SpecialLinearGroup (Fin 4) F} (hs : s ∈ scalars 4 F) :
    s ^ 4 = 1 := by
  obtain ⟨c, hc, hsc⟩ := mem_scalars.mp hs
  rw [← SpecialLinearGroup.toGL_inj, map_pow, map_one]
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, SpecialLinearGroup.coe_GL_coe_matrix, hsc, ← map_pow,
    ← Units.val_pow_eq_pow_val, hc, Units.val_one, map_one, Units.val_one]

variable [Finite F] [Fact p.Prime]

theorem isNilpotent_comap (hWp : IsPGroup p ↥W) : Group.IsNilpotent ↥(W.comap (proj 4 F)) := by
  have : Group.IsNilpotent ↥W := hWp.isNilpotent
  let f : ↥(W.comap (proj 4 F)) →* ↥W :=
    ((proj 4 F).comp (W.comap (proj 4 F)).subtype).codRestrict W fun x => x.2
  refine Subgroup.isNilpotent_of_ker_le_center f fun x hx => ?_
  have hx1 : proj 4 F (x : SpecialLinearGroup (Fin 4) F) = 1 :=
    congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  have hxs : (x : SpecialLinearGroup (Fin 4) F) ∈ scalars 4 F := by
    have := MonoidHom.mem_ker.mpr hx1
    rwa [ker_proj] at this
  have hxc := Subgroup.mem_center_iff.mp (scalars_le_center 4 F hxs)
  rw [Subgroup.mem_center_iff]
  intro y
  exact Subtype.ext (hxc y)

variable [CharP F p]

theorem exists_ne_zero_mem (hp2 : p ≠ 2) (hW : W ≠ ⊥) (hWp : IsPGroup p ↥W) :
    (∃ v ∈ fixSp p W ⊓ comSp p W, v ≠ 0) ∧ fixSp p W ≠ ⊤ := by
  obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hW
  obtain ⟨g, hg⟩ := proj_surjective 4 F (w : projectiveSL 4 F)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hWp
  have hwn : (w : projectiveSL 4 F) ^ p ^ n = 1 := by
    have : w ^ Nat.card ↥W = 1 := pow_card_eq_one'
    rw [hn] at this
    exact congrArg Subtype.val this
  set x : GL (Fin 4) F := SpecialLinearGroup.toGL (g ^ 4) with hxdef
  have hgW : proj 4 F g ∈ W := hg ▸ w.2
  have hxW : x ∈ preGL W := ⟨g ^ 4, by
    show proj 4 F (g ^ 4) ∈ W
    rw [map_pow]; exact pow_mem hgW 4, rfl⟩
  have hgs : g ^ p ^ n ∈ scalars 4 F := by
    have : g ^ p ^ n ∈ (proj 4 F).ker := by rw [MonoidHom.mem_ker, map_pow, hg, hwn]
    rwa [ker_proj] at this
  have hxp : x ^ p ^ n = 1 := by
    rw [hxdef, ← map_pow, ← pow_mul, mul_comm, pow_mul, pow_four_of_mem_scalars hgs, map_one]
  have hx1 : x ≠ 1 := by
    intro h
    have hg4 : g ^ 4 = 1 := SpecialLinearGroup.toGL_injective (by rw [← hxdef, h, map_one])
    have hww : (w : projectiveSL 4 F) ^ 4 = 1 := by rw [← hg, ← map_pow, hg4, map_one]
    have hd4 : orderOf (w : projectiveSL 4 F) ∣ 4 := orderOf_dvd_of_pow_eq_one hww
    have hdp : orderOf (w : projectiveSL 4 F) ∣ p ^ n := orderOf_dvd_of_pow_eq_one hwn
    have hcop : Nat.Coprime 4 (p ^ n) := by
      refine Nat.Coprime.pow_right n ?_
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact Nat.Coprime.pow_left 2
        ((Nat.coprime_primes Nat.prime_two Fact.out).mpr (Ne.symm hp2))
    have h1 := Nat.eq_one_of_dvd_coprimes hcop hd4 hdp
    exact hw1 (Subtype.ext (orderOf_eq_one_iff.mp h1))
  have hD : ∃ v, (x : Matrix (Fin 4) (Fin 4) F) *ᵥ v - v ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hx1
    apply Units.ext
    ext i j
    have := congrFun (hall (Pi.single j 1)) i
    simp only [Pi.sub_apply, mulVec_single_one, Pi.zero_apply, sub_eq_zero, Matrix.col_apply]
      at this
    rw [Units.val_one, Matrix.one_apply, this, Pi.single_apply]
  obtain ⟨v₀, hv₀⟩ := hD
  have hv₀D : (x : Matrix (Fin 4) (Fin 4) F) *ᵥ v₀ - v₀ ∈ comSp p W :=
    Submodule.subset_span ⟨x, v₀, ⟨hxW, n, hxp⟩, rfl⟩
  have hCtop : fixSp p W ≠ ⊤ := fun h => hv₀ (by
    have hv : v₀ ∈ fixSp p W := h ▸ Submodule.mem_top
    rw [hv x ⟨hxW, n, hxp⟩, sub_self])
  refine ⟨?_, hCtop⟩
  have : Nontrivial ↥(comSp p W) := ⟨⟨⟨_, hv₀D⟩, 0, fun h => hv₀ (congrArg Subtype.val h)⟩⟩
  have hnil := isNilpotent_comap hWp
  obtain ⟨S⟩ : Nonempty (Sylow p ↥(W.comap (proj 4 F))) := inferInstance
  have hHD : ∀ h : ↥(W.comap (proj 4 F)), ∀ v ∈ comSp p W,
      Matrix.mulVecLin ((h : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) v ∈
        comSp p W :=
    fun h v hv => mulVec_mem_comSp (A := SpecialLinearGroup.toGL h.1)
      (Subgroup.le_normalizer ⟨h.1, h.2, rfl⟩) hv
  let ρ : ↥(W.comap (proj 4 F)) →* Module.End F ↥(comSp p W) :=
    { toFun := fun h => (Matrix.mulVecLin ((h : SpecialLinearGroup (Fin 4) F) :
        Matrix (Fin 4) (Fin 4) F)).restrict (hHD h)
      map_one' := by
        ext v
        simp
      map_mul' := fun a b => by
        ext v
        simp [mulVec_mulVec] }
  obtain ⟨⟨v, hvD⟩, hv0, hvfix⟩ :=
    CFSG.LieType.BorelTits.exists_fixed_ne_zero ρ p (S : Subgroup _) S.isPGroup'
  refine ⟨v, ⟨fun y hy => ?_, hvD⟩, fun h => hv0 (Subtype.ext h)⟩
  obtain ⟨⟨t, ht, rfl⟩, m, hm⟩ := hy
  have htS : (⟨t, ht⟩ : ↥(W.comap (proj 4 F))) ∈ S := by
    refine mem_sylow_of_normal S ⟨m, ?_⟩
    apply Subtype.ext
    apply SpecialLinearGroup.toGL_injective
    simpa using hm
  exact congrArg Subtype.val (hvfix _ htS)

theorem exists_subspace (hp2 : p ≠ 2) (hW : W ≠ ⊥) (hWp : IsPGroup p ↥W) :
    ∃ N : Submodule F (Fin 4 → F), N ≠ ⊥ ∧ N ≠ ⊤ ∧
      (∀ A : GL (Fin 4) F,
        A ∈ normalizer ((preGL W : Subgroup (GL (Fin 4) F)) : Set (GL (Fin 4) F)) →
          ∀ v ∈ N, (A : Matrix (Fin 4) (Fin 4) F) *ᵥ v ∈ N) ∧
      ∀ A : GL (Fin 4) F, (∀ w ∈ W, (conjAut 4 F A * dualAut 4 F) w ∈ W) →
        ∀ c ∈ N, ∀ d ∈ N, (((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ c) ⬝ᵥ d = 0 := by
  obtain ⟨⟨v, hv, hv0⟩, hCtop⟩ := exists_ne_zero_mem hp2 hW hWp
  refine ⟨fixSp p W ⊓ comSp p W, fun h => hv0 (by rw [h] at hv; exact hv),
    fun h => hCtop (eq_top_iff.mpr (h ▸ inf_le_left)), fun A hA u hu =>
      ⟨mulVec_mem_fixSp hA hu.1, mulVec_mem_comSp hA hu.2⟩, fun A hA c hc d hd =>
      dot_fixSp_comSp (isPElt_graph hA) hc.1 hd.2⟩

end BL4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
