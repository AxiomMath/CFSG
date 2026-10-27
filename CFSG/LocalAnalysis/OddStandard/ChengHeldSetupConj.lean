module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldSetup
public import CFSG.LocalAnalysis.OddStandard.Solomon75StdBasicConj
public import CFSG.LieType.CurtisTits.Conclusion

public section

namespace CFSG.OddStandard.ChengHeld

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)

section Conjugate

variable {G : Type} [Group G]

theorem mem_conjugate_iff {H : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate H g ↔ g * x * g⁻¹ ∈ H :=
  Solomon75.mem_conjugate_iff'

theorem conj_mem_conjugate {H : Subgroup G} {g x : G} (hx : x ∈ H) :
    g⁻¹ * x * g ∈ CFSG.conjugate H g :=
  Solomon75.conj_mem_conjugate hx

theorem conjugate_inf (H K : Subgroup G) (g : G) :
    CFSG.conjugate (H ⊓ K) g = CFSG.conjugate H g ⊓ CFSG.conjugate K g :=
  Subgroup.map_inf_eq _ _ _ (MulAut.conj g⁻¹).injective

theorem conjugate_centralizer (H : Subgroup G) (g : G) :
    CFSG.conjugate (centralizer (H : Set G)) g =
      centralizer ((CFSG.conjugate H g : Subgroup G) : Set G) :=
  (Solomon75.centralizer_conjugate H g).symm

theorem conjugate_normalizer (H : Subgroup G) (g : G) :
    CFSG.conjugate (normalizer (H : Set G)) g =
      normalizer ((CFSG.conjugate H g : Subgroup G) : Set G) :=
  (Solomon75.normalizer_conjugate H g).symm

theorem card_conjugate (H : Subgroup G) (g : G) :
    Nat.card (CFSG.conjugate H g) = Nat.card H :=
  Solomon75.card_conjugate H g

end Conjugate

section Transport

variable {G : Type} [Group G] [Finite G]

theorem isSylowOf_conjugate {P K : Subgroup G} (h : IsSylowOf 2 P K) (g : G) :
    IsSylowOf 2 (CFSG.conjugate P g) (CFSG.conjugate K g) :=
  isSylowOf_map h (MulAut.conj g⁻¹).toMonoidHom

omit [Finite G] in
theorem isCyclic_sylow_of_eq_conjugate {C C' : Subgroup G} {g : G}
    (hC' : C' = CFSG.conjugate C g)
    (hcyc : ∀ T : Subgroup G, T ≤ C → IsPGroup 2 T → IsCyclic T) (R : Sylow 2 C') :
    IsCyclic (R : Subgroup C') := by
  set T : Subgroup G := (R : Subgroup C').map C'.subtype with hT
  have hTp : IsPGroup 2 T := R.isPGroup'.map _
  have hTC : T ≤ C' := map_subtype_le _
  have hT₀ : T.map (MulAut.conj g⁻¹).symm.toMonoidHom ≤ C := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ CFSG.conjugate C g := hC' ▸ hTC hy
    rw [mem_conjugate_iff] at hy'
    simpa using hy'
  have hcyc' := hcyc _ hT₀ (hTp.map _)
  have e1 := Subgroup.equivMapOfInjective T (MulAut.conj g⁻¹).symm.toMonoidHom
    (MulAut.conj g⁻¹).symm.injective
  have e2 := Subgroup.equivMapOfInjective (R : Subgroup C') C'.subtype C'.subtype_injective
  have hcycT : IsCyclic ↥T := isCyclic_of_surjective e1.symm.toMonoidHom e1.symm.surjective
  exact isCyclic_of_surjective e2.symm.toMonoidHom e2.symm.surjective

variable {A : Subgroup G}

theorem Hyp.conj (h : Hyp G A) (g : G) : Hyp G (CFSG.conjugate A g) := by
  have e : ↥A ≃* ↥(CFSG.conjugate A g) :=
    Subgroup.equivMapOfInjective A (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective
  have hc : (center ↥A).map (e : ↥A →* ↥(CFSG.conjugate A g)) = center ↥(CFSG.conjugate A g) :=
    Subgroup.map_center_eq e
  refine ⟨⟨h.setting.simple, h.setting.nonab, h.setting.kProper,
    Solomon75.standardComponentIsStandard_conjugate g h.setting.standard⟩, ?_, ?_, ?_⟩
  · exact LieType.CurtisTits.lieModel_of_mulEquiv (QuotientGroup.congr _ _ e hc) h.model
  · rw [← hc, Subgroup.card_map_of_injective e.injective]
    exact h.even
  · intro R
    exact isCyclic_sylow_of_eq_conjugate (conjugate_centralizer A g).symm
      (fun T hT hp => h.isCyclic_of_isPGroup hT hp) R

namespace Datum

variable (d : Datum A) (g : G)

@[expose] def conj : Datum (CFSG.conjugate A g) where
  q := g⁻¹ * d.q * g
  q_mem := conj_mem_conjugate d.q_mem
  q_cent := by
    rw [← conjugate_centralizer]
    exact conj_mem_conjugate d.q_cent
  q_ord := by
    rw [show g⁻¹ * d.q * g = (MulAut.conj g⁻¹) d.q by simp, MulEquiv.orderOf_eq]
    exact d.q_ord
  X := CFSG.conjugate d.X g
  X_sylow := by
    rw [← conjugate_normalizer]
    exact isSylowOf_conjugate d.X_sylow g

@[simp] theorem conj_q : (d.conj g).q = g⁻¹ * d.q * g := rfl

@[simp] theorem conj_X : (d.conj g).X = CFSG.conjugate d.X g := rfl

theorem mem_conj_X_iff {x : G} : x ∈ (d.conj g).X ↔ g * x * g⁻¹ ∈ d.X := mem_conjugate_iff

theorem conj_center_two_part_eq :
    (d.conj g).X ⊓ CFSG.conjugate A g ⊓ centralizer ((CFSG.conjugate A g : Subgroup G) : Set G) =
      CFSG.conjugate (d.X ⊓ A ⊓ centralizer (A : Set G)) g := by
  rw [conjugate_inf, conjugate_inf, conjugate_centralizer]
  rfl

theorem card_conj_center_two_part :
    Nat.card ↥((d.conj g).X ⊓ CFSG.conjugate A g ⊓
        centralizer ((CFSG.conjugate A g : Subgroup G) : Set G)) =
      Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) := by
  rw [conj_center_two_part_eq, card_conjugate]

theorem exists_conj_datum (h : Hyp G A) {z : G} (hz : IsConj d.q z) :
    ∃ g : G, (d.conj g).q = z ∧ ∀ x ∈ d.X, x * z = z * x → x ∈ (d.conj g).X := by
  obtain ⟨g, hg1, hg2⟩ := d.exists_conj_config h hz
  exact ⟨g, hg1, fun x hx hxz => (d.mem_conj_X_iff g).mpr (hg2 x hx hxz)⟩

end Datum

end Transport

end CFSG.OddStandard.ChengHeld
