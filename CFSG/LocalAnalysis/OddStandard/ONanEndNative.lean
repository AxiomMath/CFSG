module

public import CFSG.LocalAnalysis.OddStandard.ONanEndStage
public import CFSG.Sporadic.Bridge.ONSurj
public import CFSG.Sporadic.ON
public import CFSG.Sporadic.ONOddCore.Involutions
public import CFSG.Sporadic.Schreier.ONInvolution
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.OddStandard.ONanRec

open Subgroup CFSG.Blueprint CFSG.ONSchreier

theorem card_centralizer_subgroup' {M : Type*} [Group M] (K : Subgroup M) (t : K) :
    Nat.card (Subgroup.centralizer ({t} : Set K)) =
      Nat.card ↥(K ⊓ Subgroup.centralizer ({(t : M)} : Set M)) := by
  rw [← Subgroup.card_map_of_injective K.subtype_injective]
  congr 2
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.coe_subtype]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, congrArg Subtype.val hy⟩
  · rintro ⟨hx, hxt⟩
    exact ⟨⟨x, hx⟩, Subtype.ext hxt, rfl⟩

theorem inf_centralizer_conj_eq_map' {M : Type*} [Group M] (K : Subgroup M) {g : M} (hg : g ∈ K)
    (t : M) :
    K ⊓ Subgroup.centralizer ({g * t * g⁻¹} : Set M) =
      (K ⊓ Subgroup.centralizer ({t} : Set M)).map (MulAut.conj g).toMonoidHom := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨hx, hxt⟩
    refine ⟨g⁻¹ * x * g, ⟨K.mul_mem (K.mul_mem (K.inv_mem hg) hx) hg, ?_⟩, by group⟩
    calc g⁻¹ * x * g * t = g⁻¹ * (x * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * x) * g := by rw [hxt]
      _ = t * (g⁻¹ * x * g) := by group
  · rintro ⟨y, ⟨hy, hyt⟩, rfl⟩
    refine ⟨K.mul_mem (K.mul_mem hg hy) (K.inv_mem hg), ?_⟩
    calc g * y * g⁻¹ * (g * t * g⁻¹) = g * (y * t) * g⁻¹ := by group
      _ = g * (t * y) * g⁻¹ := by rw [hyt]
      _ = g * t * g⁻¹ * (g * y * g⁻¹) := by group

theorem bridge_ON :
    Nonempty (NativeSporadic.ON ≃* TauCeti.Sporadic.onanPresentation.Group) := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  exact ⟨e⟩

theorem involution_facts_of_equiv
    {X : Type} [Group X] (e : X ≃* Pv)
    (hconj : ∀ x ∈ Pv, orderOf x = 2 → ∃ g ∈ Pv, x = g * onz * g⁻¹)
    (hcard : Nat.card ↥(Pv ⊓ Subgroup.centralizer ({onz} : Set (Equiv.Perm (Fin N))) :
      Subgroup (Equiv.Perm (Fin N))) = 161280) :
    OneClass X ∧ ∀ z : X, orderOf z = 2 →
      Nat.card (Subgroup.centralizer ({z} : Set X)) = 161280 := by
  have key : ∀ w : X, orderOf w = 2 → ∃ g ∈ Pv, (e w : Equiv.Perm (Fin N)) = g * onz * g⁻¹ := by
    intro w hw
    refine hconj _ (e w).2 ?_
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact hw
  refine ⟨fun u v hu hv => ?_, fun z hz => ?_⟩
  · obtain ⟨g1, hg1, h1⟩ := key u hu
    obtain ⟨g2, hg2, h2⟩ := key v hv
    have hc : IsConj (e u) (e v) := by
      rw [isConj_iff]
      refine ⟨⟨g2 * g1⁻¹, Pv.mul_mem hg2 (Pv.inv_mem hg1)⟩, Subtype.ext ?_⟩
      show g2 * g1⁻¹ * (e u : Equiv.Perm (Fin N)) * (g2 * g1⁻¹)⁻¹ = _
      rw [h1, h2]
      group
    obtain ⟨c, hc'⟩ := isConj_iff.1 hc
    refine isConj_iff.2 ⟨e.symm c, e.injective ?_⟩
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hc'
  · obtain ⟨g, hg, hgz⟩ := key z hz
    rw [card_centralizer_equiv e z, card_centralizer_subgroup' Pv (e z), hgz,
      inf_centralizer_conj_eq_map' Pv hg, Subgroup.card_map_of_injective
      (MulAut.conj g).injective, hcard]

theorem onNativeFacts_ON :
    OnNativeFacts NativeSporadic.ON := by
  obtain ⟨-, -, -, hM, -, hcard⟩ := at_on_full_involution_centralizer
  have h := involution_facts_of_equiv (X := NativeSporadic.ON) onEquivPv
    CFSG.Sporadic.ONOddCore.cti_on_all_involutions_conjugate (by rw [← hM]; exact hcard)
  exact ⟨(CFSG.Sporadic.ON.fam_on_simplicity).2.2, bridge_ON, h.1, h.2⟩

end CFSG.OddStandard.ONanRec
