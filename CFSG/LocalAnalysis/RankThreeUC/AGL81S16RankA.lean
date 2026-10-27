module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16Norm
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16QAux
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16RankOrth

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.ClassicalGroups.Unitary Matrix
open CFSG.LieType.Universal.Unitary (SUid)

section Struct

variable {F : Type} [Field F] [Finite F] {σ : F ≃+* F}

@[expose] def fixSp (E : Subgroup (SUid σ 4)) : Submodule F (Fin 4 → F) where
  carrier := {x | ∀ a ∈ E, a • x = x}
  add_mem' := fun {x y} hx hy a ha => by rw [smul_add, hx a ha, hy a ha]
  zero_mem' := fun a _ => smul_zero a
  smul_mem' := fun c x hx a ha => by rw [smul_comm, hx a ha]

theorem mem_fixSp {E : Subgroup (SUid σ 4)} {x : Fin 4 → F} :
    x ∈ fixSp E ↔ ∀ a ∈ E, a • x = x := Iff.rfl

@[expose] def commSp (E : Subgroup (SUid σ 4)) : Submodule F (Fin 4 → F) :=
  Submodule.span F {y | ∃ a ∈ E, ∃ x : Fin 4 → F, y = a • x - x}

theorem sub_mem_commSp {E : Subgroup (SUid σ 4)} {a : SUid σ 4} (ha : a ∈ E) (x : Fin 4 → F) :
    a • x - x ∈ commSp E :=
  Submodule.subset_span ⟨a, ha, x, rfl⟩

theorem herm_nil {a : SUid σ 4} (ha : a * a = 1) (x y : Fin 4 → F) :
    herm σ (a • x - x) y = herm σ x (a • y - y) := by
  have h1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have h2 : herm σ (a • x) y = herm σ x (a • y) := by
    have := herm_inv_smul_left a x y
    rwa [h1] at this
  rw [herm_sub_left, herm_sub_right, h2]

theorem neg_eq_self_vec (h2 : (2 : F) = 0) (y : Fin 4 → F) : -y = y := by
  have : y + y = 0 := by rw [← two_smul F y, h2, zero_smul]
  exact neg_eq_of_add_eq_zero_right this

theorem smul_nil {a : SUid σ 4} (ha : a * a = 1) (h2 : (2 : F) = 0) (x : Fin 4 → F) :
    a • (a • x - x) = a • x - x := by
  have h3 : a • a • x = x := by rw [← mul_smul, ha, one_smul]
  have h5 : a • (a • x - x) = x - a • x := by rw [smul_sub, h3]
  have h6 : x - a • x = -(a • x - x) := (neg_sub _ _).symm
  rw [h5, h6, neg_eq_self_vec h2]

theorem fixSp_eq_horth (hσ : IsUnitaryInvolution σ) {E : Subgroup (SUid σ 4)}
    (hE2 : ∀ a ∈ E, a * a = 1) : fixSp E = horth σ (commSp E) := by
  ext x
  constructor
  · intro hx
    refine mem_horth.mpr fun y hy => ?_
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, z, rfl⟩ := hy
      rw [herm_nil (hE2 a ha), hx a ha, sub_self, herm_zero_right]
    | zero => exact herm_zero_left σ x
    | add y y' _ _ h1 h2 => rw [herm_add_left, h1, h2, add_zero]
    | smul c y _ h1 => rw [herm_smul_left, h1, mul_zero]
  · intro hx a ha
    have h0 : a • x - x = 0 := by
      apply eq_zero_of_herm σ
      intro y
      rw [herm_conj σ hσ.invol y (a • x - x), ← herm_nil (hE2 a ha),
        mem_horth.mp hx _ (sub_mem_commSp ha y), map_zero]
    exact sub_eq_zero.mp h0

theorem card_commSp_mul_card_fixSp (hσ : IsUnitaryInvolution σ) {E : Subgroup (SUid σ 4)}
    (hE2 : ∀ a ∈ E, a * a = 1) :
    Nat.card ↥(commSp E) * Nat.card ↥(fixSp E) = Nat.card (Fin 4 → F) := by
  rw [fixSp_eq_horth hσ hE2]
  exact card_mul_card_horth hσ _

theorem exists_ne_zero_mem_fixSp {E : Subgroup (SUid σ 4)} (hE2 : ∀ a ∈ E, a * a = 1)
    (hev : Even (Nat.card (Fin 4 → F))) : ∃ x ∈ fixSp E, x ≠ 0 := by
  have hP : IsPGroup 2 ↥E := fun a => ⟨1, Subtype.ext (by simpa [pow_two] using hE2 a.1 a.2)⟩
  obtain ⟨x, hx0, hx⟩ := exists_ne_zero_fixed hP hev (MulAction.toPermHom ↥E (Fin 4 → F))
    (fun a => smul_zero (a : SUid σ 4))
  exact ⟨x, fun a ha => hx ⟨a, ha⟩, hx0⟩

theorem finrank_commSp_add_finrank_fixSp (hσ : IsUnitaryInvolution σ) {E : Subgroup (SUid σ 4)}
    (hE2 : ∀ a ∈ E, a * a = 1) :
    Module.finrank F ↥(commSp E) + Module.finrank F ↥(fixSp E) = 4 := by
  have h := card_commSp_mul_card_fixSp hσ hE2
  have e1 : Nat.card ↥(commSp E) = Nat.card F ^ Module.finrank F ↥(commSp E) :=
    Module.natCard_eq_pow_finrank
  have e2 : Nat.card ↥(fixSp E) = Nat.card F ^ Module.finrank F ↥(fixSp E) :=
    Module.natCard_eq_pow_finrank
  rw [e1, e2, ← pow_add] at h
  have hF : 1 < Nat.card F := Finite.one_lt_card
  rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  exact Nat.pow_right_injective hF h


end Struct

end CFSG.LocalAnalysis.RankThreeUC
