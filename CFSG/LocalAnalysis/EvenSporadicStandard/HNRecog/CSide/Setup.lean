module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.BaseBridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Swap.Structure

public section

namespace CFSG.EvenSporadicStandard.HNRecog.CSide

open Subgroup Module CFSG.RankThree.Literature.FSmith CFSG.EvenSporadicStandard.HNRecog.Fpf

variable {C : Type} [Group C] {Q : Subgroup C} [hQn : Q.Normal]
  [Module (ZMod 2) (Additive (Abelianization Q))]

structure CSideSetup (C : Type) [Group C] (Q : Subgroup C) [hQn : Q.Normal]
    [Module (ZMod 2) (Additive (Abelianization Q))] where
  e : C ⧸ Q ≃* A5WrTwo
  θ : ↥(commutator C) →* A5 × A5
  σ : A5 × A5 →* (Additive (Abelianization Q) ≃ₗ[ZMod 2] Additive (Abelianization Q))
  surj : Function.Surjective θ
  ker : ∀ l : ↥(commutator C), θ l = 1 ↔ (l : C) ∈ Q
  emb : ∀ l : ↥(commutator C), A5WrTwo.baseEmb (θ l) = e (QuotientGroup.mk (l : C))
  sigma_eq : ∀ l : ↥(commutator C), σ (θ l) = conjLinEquiv hQn (l : C)
  std : Swap.StdHyp σ

theorem WeakHyp.nonempty_setup [Finite C] (hC : WeakHyp C Q) : Nonempty (CSideSetup C Q) := by
  obtain ⟨e, θ, σ, hsurj, hker, hemb, hsig, hinj, hirr⟩ := hC.exists_hom_baseEmb
  have hfr : finrank (ZMod 2) (Additive (Abelianization Q)) = 8 := by
    rw [hC.plus.finrank_quotient]
  exact ⟨⟨e, θ, σ, hsurj, hker, hemb, hsig, ⟨hinj, hfr, hirr⟩⟩⟩

theorem CSideSetup.rho_eq (S : CSideSetup C Q) {l : C} (hl : l ∈ commutator C) :
    conjLinEquiv hQn l = S.σ (S.θ ⟨l, hl⟩) :=
  (S.sigma_eq ⟨l, hl⟩).symm

theorem map_commutator_mk : (commutator C).map (QuotientGroup.mk' Q) = commutator (C ⧸ Q) := by
  rw [_root_.commutator_def, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective Q)]
  rfl

theorem mem_commutator_of_mk_mem (hQL : Q ≤ commutator C) {t : C}
    (ht : (t : C ⧸ Q) ∈ commutator (C ⧸ Q)) : t ∈ commutator C := by
  rw [← map_commutator_mk] at ht
  obtain ⟨l, hl, hlt⟩ := Subgroup.mem_map.mp ht
  have hq : l⁻¹ * t ∈ Q := by
    have h1 : (QuotientGroup.mk' Q) l = (QuotientGroup.mk' Q) t := hlt
    have h2 : (l : C ⧸ Q) = (t : C ⧸ Q) := h1
    exact QuotientGroup.eq.mp h2
  have : t = l * (l⁻¹ * t) := by group
  rw [this]
  exact mul_mem hl (hQL hq)

theorem mk_mem_commutator_of_mem {t : C} (ht : t ∈ commutator C) :
    (t : C ⧸ Q) ∈ commutator (C ⧸ Q) := by
  rw [← map_commutator_mk]
  exact Subgroup.mem_map.mpr ⟨t, ht, rfl⟩

end CFSG.EvenSporadicStandard.HNRecog.CSide
