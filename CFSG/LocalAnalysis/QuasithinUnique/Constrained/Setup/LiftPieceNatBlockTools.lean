module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelBlockDict

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Family CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.Layer.Actor CFSG.QuasithinUnique.Setup.Offender
open scoped Multiplicative MatrixGroups LinearAlgebra.Projectivization commutatorElement

section Conj

variable {G : Type} [Group G] {V : Subgroup G}

theorem autOn_map_conj [V.Normal] (B : Subgroup G) (t : G) :
    autOn (B.map (MulAut.conj t).toMonoidHom) V =
      (autOn B V).map (MulAut.conj (MulAut.conjNormal (H := V) t)).toMonoidHom := by
  rw [autOn_eq_map_conjNormal, autOn_eq_map_conjNormal, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [map_mul, map_inv, MulAut.conj_apply]

theorem map_conj_modComm [V.Normal] (A : Subgroup (MulAut V)) (t : G) :
    (modComm V A).map (MulAut.conj t).toMonoidHom =
      modComm V (A.map (MulAut.conj (MulAut.conjNormal (H := V) t)).toMonoidHom) := by
  unfold modComm
  rw [MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨a, ha, v, rfl⟩, rfl⟩
    refine ⟨MulAut.conjNormal (H := V) t * a * (MulAut.conjNormal (H := V) t)⁻¹,
      ⟨a, ha, rfl⟩, MulAut.conjNormal (H := V) t v, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply,
      MulAut.conjNormal_apply, MulEquiv.symm_apply_apply]
    group
  · rintro ⟨_, ⟨a, ha, rfl⟩, v', rfl⟩
    refine ⟨_, ⟨a, ha, (MulAut.conjNormal (H := V) t).symm v', rfl⟩, ?_⟩
    have hv' : ((v' : V) : G) = t * (((MulAut.conjNormal (H := V) t).symm v' : V) : G) * t⁻¹ := by
      conv_lhs => rw [← (MulAut.conjNormal (H := V) t).apply_symm_apply v']
      rw [MulAut.conjNormal_apply]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply,
      MulAut.conjNormal_apply]
    rw [hv']
    group

end Conj

section Family

variable {G : Type} [Group G] [Finite G]

theorem nat_others
    {R M V : Subgroup G} {n : ℕ} {F : Type} [Field F]
    (hS : EvenSL2Setting (⊤ : Subgroup G) R M V n F) {r : ℕ} {Lc : Fin r → Subgroup (MulAut V)}
    (hLc : IsCompList (autOn (⊤ : Subgroup G) V) r Lc) :
    ∀ i j, j ≠ i → ∀ x ∈ Lc j, ∀ u : V, (u : G) ∈ modComm V (Lc i) → x u = u := by
  classical
  have hFfin : Finite F := Nat.finite_of_card_ne_zero (by rw [hS.card_eq]; positivity)
  let _ : Fintype F := Fintype.ofFinite F
  let _ : Fintype (ℙ F (Fin 2 → F)) := Fintype.ofFinite _
  let _ : DecidableEq (ℙ F (Fin 2 → F)) := Classical.decEq _
  obtain ⟨⟨W, hW1, hW2, hW3, θ, hmax, himg⟩⟩ := even_SL2_original_images hS hLc
  have layer := hmax.offenders.family.layer
  set ψ := (binPsi θ).toMonoidHom with hψ
  intro i j hji x hx u hu
  have hu' := (mem_modComm_iff θ (Lc i) u).1 hu
  have h1 := layer.others_fix i j hji (ψ x) (Subgroup.mem_map_of_mem ψ hx) (vecOf θ u) hu'
  have h2 : vecOf θ (x u) = vecOf θ u := by
    rw [← binPsi_vecOf]
    exact h1
  exact vecOf_injective θ h2

theorem nat_autOn_LS_normalizer
    {R M V : Subgroup G} {n : ℕ} {F : Type} [Field F]
    (hS : EvenSL2Setting (⊤ : Subgroup G) R M V n F) {r : ℕ} {Lc : Fin r → Subgroup (MulAut V)}
    (hLc : IsCompList (autOn (⊤ : Subgroup G) V) r Lc)
    (hle : autOn (thompsonJ R) V ≤ autOn (oddOrderSubgroup (⊤ : Subgroup G)) V) (j : Fin r) :
    autOn (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R) V ≤
      Subgroup.normalizer (Lc j : Set (MulAut V)) := by
  have hbridge := even_SL2_original_bridge hS hLc
  have hbaum := even_SL2_natural_baumann hS hLc hle
  rw [hbaum.image_LS, hbridge.K_eq, hbridge.K_prod]
  refine iSup_le fun i => ?_
  by_cases hij : i = j
  · subst hij
    exact Subgroup.le_normalizer
  · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.1
      (hbridge.commute i j hij)).trans (Subgroup.centralizer_le_normalizer _)

end Family

end CFSG.QuasithinUnique.Setup.Lift
