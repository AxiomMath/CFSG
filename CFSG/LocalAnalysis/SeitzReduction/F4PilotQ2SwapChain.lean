module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2SwapChainEdge
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2SwapEdgeChains

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect)
open CFSG.SeitzReduction.SeitzQ2 (SwapParam TwistOn)
open CFSG.LieType.Ree (ReeTag)


section Canonical

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem map_C3Levi_eq_perfectCore {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X₀)
    (hX₀ : Nat.card X₀ = Nat.card K + 1) (ψ : MulAut (adjointGroup .F4 K)) :
    (C3Levi K).map ψ.toMonoidHom =
      perfectCore (centralizer
        ((X₀.map ψ.toMonoidHom : Subgroup _) : Set (adjointGroup .F4 K))) := by
  have : Finite (ModGL Tag.F4 K) := finite_modGL
  rw [centralizer_map_mulAut, ← CFSG.Quasithin.map_perfectCore,
    perfectCore_centralizer_nonsplit hXJ hcyc hX₀]

theorem map_C3Levi_eq_of_map_eq {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X₀)
    (hX₀ : Nat.card X₀ = Nat.card K + 1) {ψ ψ' : MulAut (adjointGroup .F4 K)}
    (h : X₀.map ψ.toMonoidHom = X₀.map ψ'.toMonoidHom) :
    (C3Levi K).map ψ.toMonoidHom = (C3Levi K).map ψ'.toMonoidHom := by
  rw [map_C3Levi_eq_perfectCore hXJ hcyc hX₀, map_C3Levi_eq_perfectCore hXJ hcyc hX₀, h]

end Canonical

section Frames

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

theorem subgroupToG_trans_symm_eq (e : L ≃* adjointGroup .F4 K) (ψ : MulAut (adjointGroup .F4 K))
    (W : Subgroup (adjointGroup .F4 K)) :
    subgroupToG (e.trans ψ.symm) W = subgroupToG e (W.map ψ.toMonoidHom) := by
  unfold subgroupToG
  congr 1
  rw [Subgroup.map_map]
  rfl

theorem subgroupToG_map_conj_eq (e : L ≃* adjointGroup .F4 K) (W : Subgroup (adjointGroup .F4 K))
    (m : adjointGroup .F4 K) :
    subgroupToG e (W.map (MulAut.conj m).toMonoidHom) =
      (subgroupToG e W).map (MulAut.conj ((e.symm m : L) : G)).toMonoidHom := by
  unfold subgroupToG
  rw [Subgroup.map_map, Subgroup.map_map, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

theorem map_mulAut_mul {M : Type*} [Group M] (a b : MulAut M) (W : Subgroup M) :
    W.map (a * b).toMonoidHom = (W.map b.toMonoidHom).map a.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

theorem map_mulAut_one {M : Type*} [Group M] (W : Subgroup M) :
    W.map (1 : MulAut M).toMonoidHom = W := by
  ext x
  simp

end Frames

section Realized

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K ReeTag.F4.prime]

theorem exists_realized {t : G} (hw : F4Work L K t 1) (e : L ≃* adjointGroup .F4 K)
    {X₀ : Subgroup (adjointGroup .F4 K)} (P : SwapParam t (subgroupToG e (C3Levi K)))
    (hinj : Function.Injective P.Ψ)
    (hrange : P.Ψ.range = centralizerPerfectCore (subgroupToG e X₀))
    (P' : SwapParam t (subgroupToG (e.trans (graphAutF4 K).symm) (C3Levi K)))
    (hinj' : Function.Injective P'.Ψ)
    (hrange' : P'.Ψ.range = centralizerPerfectCore (subgroupToG (e.trans (graphAutF4 K).symm) X₀))
    (ψ : MulAut (adjointGroup .F4 K)) :
    ∃ (D : Subgroup G) (Q : SwapParam t D), Function.Injective Q.Ψ ∧
      D = subgroupToG e ((C3Levi K).map ψ.toMonoidHom) ∧
      Q.Ψ.range = centralizerPerfectCore (subgroupToG e (X₀.map ψ.toMonoidHom)) := by
  have hK1 : Nat.card K = 2 ^ 1 := hw.card_eq
  obtain ⟨-, hNF, -⟩ := even_F4_exact_automorphism_normal_form le_rfl K hK1
  obtain ⟨⟨g, k⟩, hgk, -⟩ := hNF ψ
  let g' : adjointGroup .F4 K := g
  have hgk' : ψ = MulAut.conj g' * graphAutF4 K ^ (k : ℕ) := hgk
  set n : G := ((e.symm g' : L) : G) with hn
  have hnt : n * t = t * n := mem_centralizer_iff.1 hw.mem_centralizer _ (e.symm g').2
  have : Finite (ModGL Tag.F4 K) := finite_modGL
  have : Finite (adjointGroup .F4 K) := inferInstance
  obtain ⟨k, hk⟩ := k
  have hk2 : k = 0 ∨ k = 1 := by omega
  rcases hk2 with rfl | rfl
  · rw [pow_zero, mul_one] at hgk'
    subst hgk'
    obtain ⟨Q, hQinj, hQr⟩ := E8Pilot.exists_swapParam_conj P hinj n hnt
    refine ⟨_, Q, hQinj, (subgroupToG_map_conj_eq e _ g').symm, ?_⟩
    rw [hQr, hrange, map_centralizerPerfectCore, ← subgroupToG_map_conj_eq]
  · rw [pow_one] at hgk'
    subst hgk'
    obtain ⟨Q, hQinj, hQr⟩ := E8Pilot.exists_swapParam_conj P' hinj' n hnt
    refine ⟨_, Q, hQinj, ?_, ?_⟩
    · rw [subgroupToG_trans_symm_eq, ← subgroupToG_map_conj_eq, map_mulAut_mul]
    · rw [hQr, hrange', map_centralizerPerfectCore, subgroupToG_trans_symm_eq,
        ← subgroupToG_map_conj_eq, map_mulAut_mul]

end Realized

section Model

variable {K : Type} [Field K]

@[expose] def TwoModelEdge (X₀ xPP bPP A : Subgroup (adjointGroup .F4 K))
    (ψ ψ' : MulAut (adjointGroup .F4 K)) : Prop :=
  ∃ ψ₁ ψ₂ : MulAut (adjointGroup .F4 K), X₀.map ψ₁.toMonoidHom = X₀.map ψ.toMonoidHom ∧
    X₀.map ψ₂.toMonoidHom = X₀.map ψ'.toMonoidHom ∧
    (X₀ ⊔ xPP).map ψ₁.toMonoidHom = (X₀ ⊔ xPP).map ψ₂.toMonoidHom ∧
    A ≤ bPP.map ψ₁.toMonoidHom ∧ A ≤ bPP.map ψ₂.toMonoidHom

end Model

section Chain

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K ReeTag.F4.prime]

theorem exists_twistOn_of_modelEdge {t : G} (hw : F4Work L K t 1) (e : L ≃* adjointGroup .F4 K)
    {xPP bPP : Subgroup (adjointGroup .F4 K)} (hF : TwoStdPairFacts K xPP bPP)
    {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X₀)
    (hX₀ : Nat.card X₀ = 3) {A : Subgroup (adjointGroup .F4 K)} {S₀ : Set (adjointGroup .F4 K)}
    (hA : closure S₀ = A) (hS₀ : ∀ a ∈ S₀, ∃ k : ℕ, a ^ 2 ^ k = 1)
    {ψ ψ' : MulAut (adjointGroup .F4 K)} (h : TwoModelEdge X₀ xPP bPP A ψ ψ')
    {D D' : Subgroup G} (Q : SwapParam t D) (Q' : SwapParam t D')
    (hQ : Function.Injective Q.Ψ) (hQ' : Function.Injective Q'.Ψ)
    (hD : D = subgroupToG e ((C3Levi K).map ψ.toMonoidHom))
    (hD' : D' = subgroupToG e ((C3Levi K).map ψ'.toMonoidHom))
    (hr : Q.Ψ.range = centralizerPerfectCore (subgroupToG e (X₀.map ψ.toMonoidHom)))
    (hr' : Q'.Ψ.range = centralizerPerfectCore (subgroupToG e (X₀.map ψ'.toMonoidHom))) :
    ∃ s : ℤˣ, TwistOn s Q Q' (subgroupToG e A) := by
  have hK2 : Nat.card K = 2 := by rw [hw.card_eq, pow_one]
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  have hX₀' : Nat.card X₀ = Nat.card K + 1 := by rw [hX₀, hK2]
  obtain ⟨ψ₁, ψ₂, h1, h2, hT, hA1, hA2⟩ := h
  have hcl : closure (modelEmb e '' S₀) = subgroupToG e A := by
    rw [← MonoidHom.map_closure, hA, subgroupToG_eq_map]
  rw [← hcl]
  refine exists_twistOn_of_frames_F4_two hw hF hXJ hcyc hX₀ (e.trans ψ₁.symm) (e.trans ψ₂.symm)
    Q Q' hQ hQ' ?_ ?_ ?_ ?_ ?_ _ ?_
  · rw [hD, subgroupToG_trans_symm_eq, map_C3Levi_eq_of_map_eq hXJ hcyc hX₀' h1]
  · rw [hD', subgroupToG_trans_symm_eq, map_C3Levi_eq_of_map_eq hXJ hcyc hX₀' h2]
  · rw [hr, subgroupToG_trans_symm_eq, h1]
  · rw [hr', subgroupToG_trans_symm_eq, h2]
  · rw [subgroupToG_trans_symm_eq, subgroupToG_trans_symm_eq, hT]
  · rintro _ ⟨a, ha, rfl⟩
    have haA : a ∈ A := hA ▸ subset_closure ha
    obtain ⟨k, hk⟩ := hS₀ a ha
    refine ⟨?_, ?_, k, by rw [← map_pow, hk, map_one]⟩
    · rw [subgroupToG_trans_symm_eq, subgroupToG_eq_map]
      exact ⟨a, hA1 haA, rfl⟩
    · rw [subgroupToG_trans_symm_eq, subgroupToG_eq_map]
      exact ⟨a, hA2 haA, rfl⟩

theorem exists_twistOn_of_transGen {t : G} (hw : F4Work L K t 1) (e : L ≃* adjointGroup .F4 K)
    {xPP bPP : Subgroup (adjointGroup .F4 K)} (hF : TwoStdPairFacts K xPP bPP)
    {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X₀)
    (hX₀ : Nat.card X₀ = 3) (P : SwapParam t (subgroupToG e (C3Levi K)))
    (hinj : Function.Injective P.Ψ)
    (hrange : P.Ψ.range = centralizerPerfectCore (subgroupToG e X₀))
    (P' : SwapParam t (subgroupToG (e.trans (graphAutF4 K).symm) (C3Levi K)))
    (hinj' : Function.Injective P'.Ψ)
    (hrange' : P'.Ψ.range = centralizerPerfectCore (subgroupToG (e.trans (graphAutF4 K).symm) X₀))
    {A : Subgroup (adjointGroup .F4 K)} {S₀ : Set (adjointGroup .F4 K)}
    (hA : closure S₀ = A) (hS₀ : ∀ a ∈ S₀, ∃ k : ℕ, a ^ 2 ^ k = 1)
    {ψ ψ' : MulAut (adjointGroup .F4 K)} (h : Relation.TransGen (TwoModelEdge X₀ xPP bPP A) ψ ψ') :
    ∀ {D D' : Subgroup G} (Q : SwapParam t D) (Q' : SwapParam t D'),
      Function.Injective Q.Ψ → Function.Injective Q'.Ψ →
      D = subgroupToG e ((C3Levi K).map ψ.toMonoidHom) →
      D' = subgroupToG e ((C3Levi K).map ψ'.toMonoidHom) →
      Q.Ψ.range = centralizerPerfectCore (subgroupToG e (X₀.map ψ.toMonoidHom)) →
      Q'.Ψ.range = centralizerPerfectCore (subgroupToG e (X₀.map ψ'.toMonoidHom)) →
      ∃ s : ℤˣ, TwistOn s Q Q' (subgroupToG e A) := by
  have ht2 : t * t = 1 := by rw [← sq, ← hw.orderOf_eq, pow_orderOf_eq_one]
  induction h with
  | single hab =>
    intro D D' Q Q' hQ hQ' hD hD' hr hr'
    exact exists_twistOn_of_modelEdge hw e hF hXJ hcyc hX₀ hA hS₀ hab Q Q' hQ hQ' hD hD' hr hr'
  | @tail ψ₁ ψ₂ _ hbc ih =>
    intro D D' Q Q' hQ hQ' hD hD' hr hr'
    obtain ⟨D₁, Q₁, hQ₁, hD₁, hr₁⟩ :=
      exists_realized hw e P hinj hrange P' hinj' hrange' ψ₁
    obtain ⟨s, hs⟩ := ih Q Q₁ hQ hQ₁ hD hD₁ hr hr₁
    obtain ⟨s', hs'⟩ :=
      exists_twistOn_of_modelEdge hw e hF hXJ hcyc hX₀ hA hS₀ hbc Q₁ Q' hQ₁ hQ' hD₁ hD' hr₁ hr'
    exact ⟨s' * s, twistOn_trans ht2 hs hs'⟩

end Chain

section RankOne

variable {K : Type} [Field K]

theorem closure_rootGroups_eq_levi_singleton (i : Fin (Tag.rank .F4)) :
    closure (((Adjoint.f4Datum K).rootGroup (Pi.single i 1) : Set (adjointGroup .F4 K)) ∪
      (Adjoint.f4Datum K).rootGroup (-Pi.single i 1)) =
      CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {i} := by
  rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq,
    CFSG.LieType.CurtisTits.levi_singleton]
  rfl

theorem exists_pow_eq_one_of_mem_rootGroups [CharP K 2] {i : Fin (Tag.rank .F4)}
    {a : adjointGroup .F4 K}
    (ha : a ∈ ((Adjoint.f4Datum K).rootGroup (Pi.single i 1) : Set (adjointGroup .F4 K)) ∪
      (Adjoint.f4Datum K).rootGroup (-Pi.single i 1)) : ∃ k : ℕ, a ^ 2 ^ k = 1 := by
  refine ⟨1, ?_⟩
  have hsq : ∀ γ, IsRoot .F4 γ → ∀ a ∈ (Adjoint.f4Datum K).rootGroup γ, a ^ 2 = 1 := by
    intro γ hγ a ha
    obtain ⟨c, hc⟩ := (mem_rootGroup_iff_pinnedX hγ).1 ha
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hc, sq, ← pinnedX_add, ← two_mul, CharTwo.two_eq_zero, zero_mul,
      pinnedX_zero, Subgroup.coe_one]
  rw [pow_one]
  rcases ha with ha | ha
  · exact hsq _ (isRoot_single .F4 i) a ha
  · exact hsq _ (isRoot_neg_single .F4 i) a ha

end RankOne

section Main

local instance f4PilotQ2SwapChainNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

@[expose] def TwoChainModelInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime], Nat.card K = 2 →
    ∀ X₀ : Subgroup (adjointGroup .F4 K),
      X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K) → IsCyclic X₀ →
      Nat.card X₀ = 3 →
    ∃ xPP bPP : Subgroup (adjointGroup .F4 K), TwoStdPairFacts K xPP bPP ∧
      Relation.TransGen (TwoModelEdge X₀ xPP bPP
        (CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {1})) 1 (graphAutF4 K) ∧
      Relation.TransGen (TwoModelEdge X₀ xPP bPP
        (CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {2})) 1 (graphAutF4 K) ∧
      ∃ ψW : MulAut (adjointGroup .F4 K),
        CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {0} ≤
          (C3Levi K).map ψW.toMonoidHom ∧
        CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {3} ≤
          (C3Levi K).map ψW.toMonoidHom ∧
        Relation.TransGen (TwoModelEdge X₀ xPP bPP
          (CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {0})) ψW (graphAutF4 K) ∧
        Relation.TransGen (TwoModelEdge X₀ xPP bPP
          (CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {3})) ψW 1

theorem twoSwapChainInput_of_model (h : TwoChainModelInput) :
    TwoSwapChainInput := by
  intro G _ _ L K _ _ _ e t hw X₀ hXJ hcyc hX₀ P hinj hrange P' hinj' hrange'
  have hK2 : Nat.card K = 2 := by rw [hw.card_eq, pow_one]
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  obtain ⟨xPP, bPP, hF, h1, h2, ψW, hW0, hW3, h0, h3⟩ := h K hK2 X₀ hXJ hcyc hX₀
  have hP1D : subgroupToG e (C3Levi K) =
      subgroupToG e ((C3Levi K).map (1 : MulAut (adjointGroup .F4 K)).toMonoidHom) := by
    rw [map_mulAut_one]
  have hP1r : P.Ψ.range = centralizerPerfectCore
      (subgroupToG e (X₀.map (1 : MulAut (adjointGroup .F4 K)).toMonoidHom)) := by
    rw [map_mulAut_one]
    exact hrange
  have hPφD : subgroupToG (e.trans (graphAutF4 K).symm) (C3Levi K) =
      subgroupToG e ((C3Levi K).map (graphAutF4 K).toMonoidHom) :=
    subgroupToG_trans_symm_eq e _ _
  have hPφr : P'.Ψ.range = centralizerPerfectCore
      (subgroupToG e (X₀.map (graphAutF4 K).toMonoidHom)) := by
    rw [hrange', subgroupToG_trans_symm_eq]
  have hgen := fun (i : Fin (Tag.rank .F4)) => closure_rootGroups_eq_levi_singleton (K := K) i
  have h2el := fun (i : Fin (Tag.rank .F4)) (a : adjointGroup .F4 K)
      (ha : a ∈ ((Adjoint.f4Datum K).rootGroup (Pi.single i 1) : Set (adjointGroup .F4 K)) ∪
        (Adjoint.f4Datum K).rootGroup (-Pi.single i 1)) => exists_pow_eq_one_of_mem_rootGroups ha
  refine ⟨exists_twistOn_of_transGen hw e hF hXJ hcyc hX₀ P hinj hrange P' hinj' hrange'
      (hgen 1) (h2el 1) h1 P P' hinj hinj' hP1D hPφD hP1r hPφr,
    exists_twistOn_of_transGen hw e hF hXJ hcyc hX₀ P hinj hrange P' hinj' hrange'
      (hgen 2) (h2el 2) h2 P P' hinj hinj' hP1D hPφD hP1r hPφr, ?_⟩
  obtain ⟨DR, R, hR, hDR, hrR⟩ := exists_realized hw e P hinj hrange P' hinj' hrange' ψW
  obtain ⟨σ, hσ⟩ := exists_twistOn_of_transGen hw e hF hXJ hcyc hX₀ P hinj hrange P' hinj'
    hrange' (hgen 0) (h2el 0) h0 R P' hR hinj' hDR hPφD hrR hPφr
  obtain ⟨σ', hσ'⟩ := exists_twistOn_of_transGen hw e hF hXJ hcyc hX₀ P hinj hrange P' hinj'
    hrange' (hgen 3) (h2el 3) h3 R P hR hinj hDR hP1D hrR hP1r
  exact ⟨DR, R, σ, σ', hDR ▸ subgroupToG_mono e hW0, hDR ▸ subgroupToG_mono e hW3, hσ, hσ'⟩

end Main

end CFSG.SeitzReduction.F4Pilot
