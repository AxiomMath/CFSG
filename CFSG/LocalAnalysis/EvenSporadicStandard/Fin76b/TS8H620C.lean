module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8H620B

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace OHyp69

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {β : G} {B : Subgroup G} {S : Subgroup G}
  (h : OHyp69 L z t T E B β S)

include h

theorem T_le_normalizer_E : T ≤ normalizer (E : Set G) := by
  intro s hs
  have hsL : s ∈ normalizer (L : Set G) := h.oe.cfg.cent_le (h.oe.cfg.T_le hs)
  set f : G →* G := (MulAut.conj s).toMonoidHom with hf
  have hfinj : Function.Injective f := (MulAut.conj s).injective
  have hf_apply : ∀ p, f p = s * p * s⁻¹ := fun p => by simp [f]
  have hEle : E.map f ≤ T ⊓ L := by
    rintro _ ⟨e, he, rfl⟩
    rw [hf_apply]
    exact ⟨T.mul_mem (T.mul_mem hs (h.oe.E_le_T he)) (T.inv_mem hs),
      (mem_normalizer_iff.1 hsL e).1 (h.oe.E_le_L he)⟩
  have hEE : E.map f = E := h.oe.econfig.unique _ hEle ⟨E.equivMapOfInjective f hfinj⟩
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hfx : f x ∈ E.map f := Subgroup.mem_map.2 ⟨x, hx, rfl⟩
    rw [hEE, hf_apply] at hfx
    exact hfx
  · intro hx
    have hfx : f x ∈ E.map f := by
      rw [hEE, hf_apply]
      exact hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hfx
    rw [hfinj hyx] at hy
    exact hy

theorem T_le_M {α : G} (hα : AlphaSpec S z t α) (hM : OuterMFacts E S z t) :
    T ≤ normalizer ((S ⊔ E : Subgroup G) : Set G) := by
  intro s hs
  have hsN : s ∈ normalizer (E : Set G) ⊓ centralizer ({z} : Set G) :=
    ⟨h.T_le_normalizer_E hs, h.oe.cfg.T_le hs⟩
  exact hM.NH_le hsN

theorem exists_Rs {α : G} (hα : AlphaSpec S z t α) (hF : EFacts611 E t)
    (hM : OuterMFacts E S z t) (hp : OuterPairing h hα) :
    ∃ Rs : Subgroup G, IsPGroup 2 Rs ∧ z ∈ Rs ∧ T ≤ Rs ∧
      Rs ≤ normalizer ((Fsub h hα ⊓ centralizer ({α} : Set G) : Subgroup G) : Set G) ∧
      (∀ P : Subgroup G, IsPGroup 2 P →
        P ≤ normalizer ((Fsub h hα ⊓ centralizer ({α} : Set G) : Subgroup G) : Set G) →
          Rs ≤ P → P = Rs) ∧
      ¬ 2 ∣ Rs.relIndex (centralizer ({z} : Set G)) := by
  have hc := h.oe.cfg
  have hMN : normalizer ((S ⊔ E : Subgroup G) : Set G) ≤
      normalizer ((Fsub h hα ⊓ centralizer ({α} : Set G) : Subgroup G) : Set G) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro q
    refine ⟨fun hq => h.QF_normal hα hg hq, fun hq => ?_⟩
    have e := h.QF_normal hα (inv_mem hg) hq
    rwa [show g⁻¹ * (g * q * g⁻¹) * g⁻¹⁻¹ = q by group] at e
  have hTN : T ≤ normalizer ((Fsub h hα ⊓ centralizer ({α} : Set G) : Subgroup G) : Set G) :=
    (h.T_le_M hα hM).trans hMN
  obtain ⟨Rs, ⟨h1, h2, h3⟩, hmax⟩ :=
    (Set.toFinite {P : Subgroup G | IsPGroup 2 P ∧ T ≤ P ∧
      P ≤ normalizer ((Fsub h hα ⊓ centralizer ({α} : Set G) : Subgroup G) : Set G)}).exists_maximalFor
      id _ ⟨T, hc.T_pgroup, le_rfl, hTN⟩
  refine ⟨Rs, h1, h2 hc.z_mem, h2, h3,
    fun P hP hPN hle => le_antisymm (hmax ⟨hP, h2.trans hle, hPN⟩ hle) hle, ?_⟩
  refine h.relIndex_cent_z_odd h1 ?_
  exact Subgroup.card_le_of_le (le_inf h2 hc.T_le)

end OHyp69

end CFSG.EvenSporadicStandard.Fin76b
