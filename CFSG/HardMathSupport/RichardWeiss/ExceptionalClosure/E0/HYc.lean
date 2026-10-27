module

public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.HYt

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry CFSG.AGLEmbedding CFSG.Open CFSG.Quasithin
  CFSG.HardMathSupport.RichardWeiss.Proving Equiv Equiv.Perm
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def charClosure (S A : Subgroup G) : Subgroup G :=
  (⨆ α : S ≃* S, (A.subgroupOf S).map α.toMonoidHom).map S.subtype

theorem charClosure_le_S (S A : Subgroup G) : charClosure S A ≤ S := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem le_charClosure {S A : Subgroup G} (hAS : A ≤ S) : A ≤ charClosure S A := by
  intro a ha
  refine ⟨⟨a, hAS ha⟩, ?_, rfl⟩
  refine Subgroup.mem_iSup_of_mem (MulEquiv.refl S) ⟨⟨a, hAS ha⟩, ha, rfl⟩

theorem charClosure_characteristic (S A : Subgroup G) :
    ((charClosure S A).subgroupOf S).Characteristic := by
  have e : (charClosure S A).subgroupOf S = ⨆ α : S ≃* S, (A.subgroupOf S).map α.toMonoidHom :=
    Subgroup.comap_map_eq_self_of_injective S.subtype_injective _
  rw [e]
  rw [Subgroup.characteristic_iff_map_le]
  intro φ
  rw [Subgroup.map_iSup]
  refine iSup_le fun α => ?_
  rw [Subgroup.map_map]
  exact le_iSup (fun β : S ≃* S => (A.subgroupOf S).map β.toMonoidHom) (α.trans φ)

@[expose] def HYc (S L : Subgroup G) : Prop :=
  charClosure S ⁅S, ⁅blockV S L, L⁆⁆ ≤ Qt S L

theorem false_of_E0_HYc [Finite G] {X S L : Subgroup G} (hA : Asc81bHyp X S)
    (hL : IsWeakSBlock X S L) (hSL : S ≤ Subgroup.normalizer (L : Set G)) {N : ℕ} (hN : 10 ≤ N)
    {θ : ↥(L ⊔ S) →* Perm (Fin N)} (hNS : NaturalSectionTheta S L N θ)
    (hθS : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ S)
    {Δ₀ : Finset (Fin N)} {P : Subgroup (Perm (Fin N))} {ω : Perm (Fin N)}
    (hshape : E0Shape P ω Δ₀)
    (hθ : (S.subgroupOf (L ⊔ S)).map θ =
      P ⊔ Subgroup.closure {τ | ∃ x, x ∉ Δ₀ ∧ τ = swap x (ω x)})
    (hYc : HYc S L) : False := by
  have D := shortData_Qt hA hL hSL
  have hθQ : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ pCoreOf 2 (L ⊔ S) := by
    obtain ⟨π, hπ, hπker, hAθ, hequiv, hf⟩ := hNS
    exact fun m hm => inf_centralizer_blockV_le_twoCore hA hL hSL ⟨hθS m hm, hf m hm⟩
  have hVS : blockV S L ≤ S := D.hVQ.trans D.hQS
  have hAS : ⁅S, ⁅blockV S L, L⁆⁆ ≤ S := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hyS : y ∈ S := hVS (D.commutator_le hy)
    exact S.mul_mem (S.mul_mem (S.mul_mem hx hyS) (S.inv_mem hx)) (S.inv_mem hyS)
  refine false_of_E0_core hA hL hSL hN hNS hθS hshape hθ (Qt S L) D (Qt_le_Qs S L)
    (charClosure S ⁅S, ⁅blockV S L, L⁆⁆) (charClosure_le_S _ _)
    (charClosure_characteristic _ _) ?_ hYc ?_
  · intro s hs v hv
    exact le_charClosure hAS (Subgroup.commutator_mem_commutator hs hv)
  · intro m hm y hy
    exact ⟨(Qt S L).mul_mem (D.hMQ m m.2 y hy) ((Qt S L).inv_mem hy), (hy.2 _ (hθQ m hm)).2⟩

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0
