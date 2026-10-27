module

public import CFSG.LieType.Chevalley.RankOneGaussian
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResTLPsl

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG.Open CFSG.Open.StatedAPI CFSG.LieType.Chevalley
open scoped commutatorElement

set_option linter.unusedSectionVars false

@[expose] def ExcOthNoL2 {G : Type*} [Group G] (P : Subgroup G) : Prop :=
  ∀ (F : Type) [Field F], IsEmpty ((↥P ⧸ Subgroup.center ↥P) ≃* StatedProj (StatedSL 2 F))

theorem ExcOthNoL2.of_equiv {G H : Type*} [Group G] [Group H] {P : Subgroup G} {Q : Subgroup H}
    (e : ↥P ≃* ↥Q) (h : ExcOthNoL2 Q) : ExcOthNoL2 P := by
  intro F _
  refine ⟨fun φ => (h F).false ?_⟩
  refine (QuotientGroup.congr (Subgroup.center ↥Q) (Subgroup.center ↥P) e.symm ?_).trans φ
  ext z
  simp only [Subgroup.mem_map, Subgroup.mem_center_iff]
  constructor
  · rintro ⟨w, hw, rfl⟩ g
    apply e.injective
    simpa using hw (e g)
  · intro hz
    refine ⟨e z, fun g => ?_, by simp⟩
    apply e.symm.injective
    simpa using hz (e.symm g)

theorem ExcOthNoL2.map_conj {G : Type*} [Group G] {P : Subgroup G} (h : ExcOthNoL2 P) (g : G) :
    ExcOthNoL2 (P.map (MulAut.conj g).toMonoidHom) :=
  ExcOthNoL2.of_equiv (P.equivMapOfInjective _ (MulAut.conj g).injective).symm h

section SL2

variable {K : Type} [Field K]

theorem excOth_uSL_add (a b : K) : uSL (a + b) = uSL a * uSL b := by
  apply SL2_ext <;> simp [coe_uSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
    Fin.sum_univ_two] <;> ring

theorem excOth_vSL_add (a b : K) : vSL (a + b) = vSL a * vSL b := by
  apply SL2_ext <;> simp [coe_vSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
    Fin.sum_univ_two] <;> ring

theorem excOth_uSL_zero : (uSL (0 : K)) = 1 := by
  apply SL2_ext <;> simp [coe_uSL]

theorem excOth_vSL_zero : (vSL (0 : K)) = 1 := by
  apply SL2_ext <;> simp [coe_vSL]

theorem excOth_uSL_inv (a : K) : (uSL a)⁻¹ = uSL (-a) := by
  rw [inv_eq_of_mul_eq_one_right]
  rw [← excOth_uSL_add, add_neg_cancel, excOth_uSL_zero]

theorem excOth_vSL_inv (a : K) : (vSL a)⁻¹ = vSL (-a) := by
  rw [inv_eq_of_mul_eq_one_right]
  rw [← excOth_vSL_add, add_neg_cancel, excOth_vSL_zero]

theorem excOth_comm_uv_entry (s t : K) :
    ((⁅uSL s, vSL t⁆ : SL2 K) : Matrix (Fin 2) (Fin 2) K) 1 0 = s * t ^ 2 := by
  rw [commutatorElement_def, excOth_uSL_inv, excOth_vSL_inv]
  simp [coe_uSL, coe_vSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem excOth_comm_u_one_entry (M : SL2 K) :
    ((⁅M, uSL 1⁆ : SL2 K) : Matrix (Fin 2) (Fin 2) K) 1 0 =
      -((M : Matrix (Fin 2) (Fin 2) K) 1 0) ^ 2 := by
  have hdet := det_SL2 M
  rw [commutatorElement_def, excOth_uSL_inv]
  simp [coe_uSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

@[expose] def excOth_uHom (K : Type) [Field K] : Multiplicative K →* SL2 K :=
  MonoidHom.mk' (fun s => uSL (Multiplicative.toAdd s)) fun a b => excOth_uSL_add _ _

@[expose] def excOth_vHom (K : Type) [Field K] : Multiplicative K →* SL2 K :=
  MonoidHom.mk' (fun s => vSL (Multiplicative.toAdd s)) fun a b => excOth_vSL_add _ _

theorem excOth_sl2_heis {G : Type*} [Group G] {F : Type} [Field F]
    (φ : (G ⧸ Subgroup.center G) ≃* StatedProj (StatedSL 2 F)) (ρ : SL2 K →* G)
    (hK : 3 ≤ Nat.card K)
    (hker : ∀ B : SL2 K, ρ B = 1 → (B : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) {c : G}
    (hc : c ∉ Subgroup.center G) (hcu : ∀ s : K, Commute (ρ (uSL s)) c)
    (hcv : ∀ t : K, Commute (ρ (vSL t)) c) : False := by
  refine excTL_false_of_heis φ (H := Multiplicative K) (by rwa [Nat.card_congr Multiplicative.toAdd])
    (ρ.comp (excOth_uHom K)) (ρ.comp (excOth_vHom K)) c hc (fun s => hcu _) (fun t => hcv _)
    ?_
  intro s t hs ht hz
  have hs0 : Multiplicative.toAdd s ≠ 0 := fun h => hs (by simpa using h)
  have ht0 : Multiplicative.toAdd t ≠ 0 := fun h => ht (by simpa using h)
  set M : SL2 K := ⁅uSL (Multiplicative.toAdd s), vSL (Multiplicative.toAdd t)⁆ with hM
  have hxy : ⁅(ρ.comp (excOth_uHom K)) s, (ρ.comp (excOth_vHom K)) t⁆ = ρ M := by
    rw [hM, map_commutatorElement]
    rfl
  rw [hxy] at hz
  have hcomm := Subgroup.mem_center_iff.1 hz (ρ (uSL 1))
  have h1 : ρ ⁅M, uSL 1⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm.symm
  have h2 := hker _ h1
  rw [excOth_comm_u_one_entry, hM, excOth_comm_uv_entry] at h2
  have h3 : (Multiplicative.toAdd s * Multiplicative.toAdd t ^ 2) ^ 2 = 0 := by
    linear_combination -h2
  have := pow_eq_zero_iff (two_ne_zero) |>.1 h3
  exact mul_ne_zero hs0 (pow_ne_zero 2 ht0) this

end SL2

section Gen

variable {K : Type} [Field K]

theorem excOth_SL2_closure :
    Subgroup.closure ({g : SL2 K | ∃ t : K, g = uSL t} ∪ {g : SL2 K | ∃ t : K, g = vSL t}) = ⊤ := by
  rw [eq_top_iff]
  intro g _
  set C := Subgroup.closure ({g : SL2 K | ∃ t : K, g = uSL t} ∪
    {g : SL2 K | ∃ t : K, g = vSL t}) with hC
  have hu : ∀ t, uSL t ∈ C := fun t => Subgroup.subset_closure (Or.inl ⟨t, rfl⟩)
  have hv : ∀ t, vSL t ∈ C := fun t => Subgroup.subset_closure (Or.inr ⟨t, rfl⟩)
  have hW : (WSL : SL2 K) ∈ C := by
    have : (WSL : SL2 K) = uSL 1 * vSL (-1) * uSL 1 := by
      apply SL2_ext <;> simp [coe_WSL, coe_uSL, coe_vSL, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.mul_apply, Fin.sum_univ_two]
    rw [this]
    exact C.mul_mem (C.mul_mem (hu _) (hv _)) (hu _)
  have hH : ∀ t : Kˣ, (HSL t : SL2 K) ∈ C := by
    intro t
    have h1 : (HSL t : SL2 K) * WSL = uSL (t : K) * vSL (-((t⁻¹ : Kˣ) : K)) * uSL (t : K) := by
      apply SL2_ext <;> simp [coe_HSL, coe_WSL, coe_uSL, coe_vSL,
        Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    have h2 : (HSL t : SL2 K) = uSL (t : K) * vSL (-((t⁻¹ : Kˣ) : K)) * uSL (t : K) * WSL⁻¹ := by
      rw [← h1]; group
    rw [h2]
    exact C.mul_mem (C.mul_mem (C.mul_mem (hu _) (hv _)) (hu _)) (C.inv_mem hW)
  by_cases hc : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
  · rw [eq_HSL_mul_uSL hc]
    exact C.mul_mem (hH _) (hu _)
  · rw [eq_uSL_mul_HSL_mul_WSL_mul_uSL hc]
    exact C.mul_mem (C.mul_mem (C.mul_mem (hu _) (hH _)) hW) (hu _)

theorem excOth_SL2_hom_ext {G : Type*} [Group G] {f g : SL2 K →* G}
    (hu : ∀ t, f (uSL t) = g (uSL t)) (hv : ∀ t, f (vSL t) = g (vSL t)) : f = g := by
  refine MonoidHom.eq_of_eqOn_dense excOth_SL2_closure ?_
  rintro _ (⟨t, rfl⟩ | ⟨t, rfl⟩)
  · exact hu t
  · exact hv t

end Gen

end CFSG.HardMathSupport.Dickson.Sec6.I1431
