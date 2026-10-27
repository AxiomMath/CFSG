module

public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.HYt

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry CFSG.AGLEmbedding CFSG.Open CFSG.Quasithin
  CFSG.HardMathSupport.RichardWeiss.Proving Equiv Equiv.Perm
open scoped commutatorElement

variable {G : Type} [Group G]

theorem e0_eprop_sq {N : ℕ} {P : Subgroup (Perm (Fin N))} {ω : Perm (Fin N)} {Δ₀ : Finset (Fin N)}
    (h : E0Shape P ω Δ₀) {σ : Perm (Fin N)} (hσ : E0Shape.Eprop P ω Δ₀ σ) : σ * σ = 1 := by
  refine Equiv.ext fun z => ?_
  simp only [Perm.mul_apply, Perm.one_apply]
  by_cases hz : z ∈ Δ₀
  · obtain ⟨p, hp, hpx⟩ := hσ.1
    rw [hpx z hz, hpx _ (h.P_mem hp hz)]
    have := congrArg (fun f : Perm (Fin N) => f z) (h.Psq p hp)
    simpa using this
  · rcases hσ.2 z hz with h1 | h1
    · rw [h1, h1]
    · rw [h1, e0_eprop_swap h hσ hz h1]

theorem Phi_le_twoCore [Finite G] {X S L : Subgroup G} (hA : Asc81bHyp X S)
    (hL : IsWeakSBlock X S L) (hSL : S ≤ Subgroup.normalizer (L : Set G)) {N : ℕ}
    {θ : ↥(L ⊔ S) →* Perm (Fin N)} (hNS : NaturalSectionTheta S L N θ)
    (hθS : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ S)
    {Δ₀ : Finset (Fin N)} {P : Subgroup (Perm (Fin N))} {ω : Perm (Fin N)}
    (hshape : E0Shape P ω Δ₀)
    (hθ : (S.subgroupOf (L ⊔ S)).map θ =
      P ⊔ Subgroup.closure {τ | ∃ x, x ∉ Δ₀ ∧ τ = swap x (ω x)}) :
    Phi S ≤ pCoreOf 2 (L ⊔ S) := by
  have hθQ : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ pCoreOf 2 (L ⊔ S) := by
    obtain ⟨π, hπ, hπker, hAθ, hequiv, hf⟩ := hNS
    exact fun m hm => inf_centralizer_blockV_le_twoCore hA hL hSL ⟨hθS m hm, hf m hm⟩
  have hE : ∀ s : ↥(L ⊔ S), (s : G) ∈ S → E0Shape.Eprop P ω Δ₀ (θ s) := by
    intro s hs
    have := Subgroup.mem_map_of_mem θ (Subgroup.mem_subgroupOf.2 hs)
    rw [hθ] at this
    exact E0Shape.mem_E0grp_prop hshape this
  let K : Subgroup G := (θ.ker).map (L ⊔ S).subtype
  have hKQ : K ≤ pCoreOf 2 (L ⊔ S) := by
    rintro _ ⟨m, hm, rfl⟩
    exact hθQ m hm
  refine le_trans ?_ hKQ
  unfold Phi
  refine sup_le ?_ ?_
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    have haM : a ∈ L ⊔ S := Subgroup.mem_sup_right ha
    have hbM : b ∈ L ⊔ S := Subgroup.mem_sup_right hb
    have hcS : ⁅a, b⁆ ∈ S :=
      S.mul_mem (S.mul_mem (S.mul_mem ha hb) (S.inv_mem ha)) (S.inv_mem hb)
    have hcM : ⁅a, b⁆ ∈ L ⊔ S := Subgroup.mem_sup_right hcS
    refine ⟨⟨⁅a, b⁆, hcM⟩, ?_, rfl⟩
    have e : (⟨⁅a, b⁆, hcM⟩ : ↥(L ⊔ S)) = ⁅(⟨a, haM⟩ : ↥(L ⊔ S)), ⟨b, hbM⟩⁆ := rfl
    rw [SetLike.mem_coe, MonoidHom.mem_ker, e, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (e0_eprop_comm hshape (hE ⟨a, haM⟩ ha) (hE ⟨b, hbM⟩ hb))
  · rw [Subgroup.closure_le]
    rintro _ ⟨s, hs, rfl⟩
    have hsM : s ∈ L ⊔ S := Subgroup.mem_sup_right hs
    have hs2 : s ^ 2 ∈ L ⊔ S := Subgroup.mem_sup_right (S.pow_mem hs 2)
    refine ⟨⟨s ^ 2, hs2⟩, ?_, rfl⟩
    have e : (⟨s ^ 2, hs2⟩ : ↥(L ⊔ S)) = (⟨s, hsM⟩ : ↥(L ⊔ S)) ^ 2 := rfl
    rw [SetLike.mem_coe, MonoidHom.mem_ker, e, map_pow, pow_two]
    exact e0_eprop_sq hshape (hE ⟨s, hsM⟩ hs)

theorem false_of_E0_HYz [Finite G] {X S L : Subgroup G} (hA : Asc81bHyp X S)
    (hL : IsWeakSBlock X S L) (hSL : S ≤ Subgroup.normalizer (L : Set G)) {N : ℕ} (hN : 10 ≤ N)
    {θ : ↥(L ⊔ S) →* Perm (Fin N)} (hNS : NaturalSectionTheta S L N θ)
    (hθS : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ S)
    {Δ₀ : Finset (Fin N)} {P : Subgroup (Perm (Fin N))} {ω : Perm (Fin N)}
    (hshape : E0Shape P ω Δ₀)
    (hθ : (S.subgroupOf (L ⊔ S)).map θ =
      P ⊔ Subgroup.closure {τ | ∃ x, x ∉ Δ₀ ∧ τ = swap x (ω x)})
    (hYz : ∀ y ∈ Phi S, y ^ 2 = 1 → (∀ z ∈ Phi S, z * y = y * z) → y ∈ Qt S L) : False := by
  have D := shortData_Qt hA hL hSL
  have hθQ : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ pCoreOf 2 (L ⊔ S) := by
    obtain ⟨π, hπ, hπker, hAθ, hequiv, hf⟩ := hNS
    exact fun m hm => inf_centralizer_blockV_le_twoCore hA hL hSL ⟨hθS m hm, hf m hm⟩
  have hPhiQ := Phi_le_twoCore hA hL hSL hNS hθS hshape hθ
  have hVel : IsElemAbelian 2 (blockV S L) :=
    CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.isElemAbelian_blockV S L
  have hVS : blockV S L ≤ S := D.hVQ.trans D.hQS
  have hOQ : OmZPhi S ≤ Qt S L := by
    rw [OmZPhi_eq_closure]
    exact (Subgroup.closure_le _).2 fun y hy => hYz y hy.1 hy.2.1 hy.2.2
  refine false_of_E0_core hA hL hSL hN hNS hθS hshape hθ (Qt S L) D (Qt_le_Qs S L)
    (OmZPhi S) (OmZPhi_le_S S) (OmZPhi_characteristic S) ?_ hOQ ?_
  · intro s hs v hv'
    have hv := D.commutator_le hv'
    have hcV : s * v * s⁻¹ * v⁻¹ ∈ blockV S L :=
      (blockV S L).mul_mem (D.hMV s (Subgroup.mem_sup_right hs) v hv) ((blockV S L).inv_mem hv)
    refine mem_OmZPhi_of_central
      (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hs (hVS hv)))
      (by have := hVel.2 _ hcV; exact this) (fun z hz => ?_)
    exact blockV_comm S L (hPhiQ hz) hcV
  · intro m hm y hy
    exact ⟨(Qt S L).mul_mem (D.hMQ m m.2 y hy) ((Qt S L).inv_mem hy), (hy.2 _ (hθQ m hm)).2⟩

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0
