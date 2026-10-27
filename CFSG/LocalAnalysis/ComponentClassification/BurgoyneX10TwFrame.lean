module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneX10T1Frame

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.X10

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.Timmesfeld CFSG.ClassicalInvolution.WeakCT
  CFSG.ComponentClassification.CatLeafProof
open CFSG.ClassicalInvolution.Generic (Commutes)
open scoped MatrixGroups

theorem specialLinear_frame_rankOne {m p f : ℕ} (hadm : StatedLieAdmissible .PSL (m + 1) p f)
    (hm : 3 ≤ m) {F : Type} [Field F] [Finite F] (hF : Nat.card F = p ^ f) {G : Type} [Group G]
    {U : Fin m → Subgroup G}
    (hcomm : ∀ i j : Fin m, i ≠ j → ¬ j.val = i.val + 1 → ¬ i.val = j.val + 1 →
      ∀ u ∈ U i, ∀ v ∈ U j, u * v = v * u)
    {ρ : Fin m → SL(2, F) →* G} (hρ : ∀ k, Function.Injective (ρ k) ∧ (ρ k).range = U k)
    (hψ : ∀ i j : Fin m, j.val = i.val + 1 → ∃ ψ : SL(3, F) →* G,
      ψ.comp (blk F 0) = ρ i ∧ ψ.comp (blk F 1) = ρ j) :
    ∃ Ψ : SL(m + 1, F) →* G, Ψ.ker ≤ Subgroup.center _ ∧ Ψ.range = ⨆ k, U k ∧
      ∀ k : Fin m, (CurtisTits.rankOne (SpecialLinear.rootDatum m F).rootGroup k).map Ψ =
        U k := by
  obtain ⟨Ψ, hker, hrange, -, -, hrk⟩ := weakCT_of_frame_subgroup (RingEquiv.refl F)
    (CurtisTits.curtisTitsConclusion_specialLinear hadm hF hm)
    (leviConePresented_specialLinear m F) (ARS.simplyLacedLevis_specialLinear m F)
    (⟨0, by omega⟩ : Fin m) hcomm hρ hψ
  exact ⟨Ψ, hker, hrange, hrk⟩

theorem exists_conj_le_rootGroup
    {τ : Tag} {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) {S : Type} [Group S]
    (Ψ : S →* adjointGroup τ K) {R X : Subgroup S}
    (hR : R.map Ψ = (adjDatum (rootOperatorFamily τ) K).rootGroup β ⊔
      (adjDatum (rootOperatorFamily τ) K).rootGroup (-β))
    (hXR : X ≤ R) (hX : IsPGroup p X) :
    ∃ y : S, (X.map (MulAut.conj y).toMonoidHom).map Ψ ≤
      (adjDatum (rootOperatorFamily τ) K).rootGroup β := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hK
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  set Ub := (adjDatum (rootOperatorFamily τ) K).rootGroup β with hUb
  set L := Ub ⊔ (adjDatum (rootOperatorFamily τ) K).rootGroup (-β) with hL
  obtain ⟨-, ⟨eQ⟩, -⟩ := odd_arbitrary_root_pair_SL2_p_components τ K hK2 hβ
  have hLmap : L.map (adjointGroup τ K).subtype =
      rootSubgroup τ K β ⊔ rootSubgroup τ K (-β) := by
    rw [hL, Subgroup.map_sup, map_subtype_rootGroup _ hβ, map_subtype_rootGroup _ (IsRoot.neg hβ)]
  let eL : SL2 K ≃* L := (eQ.trans (MulEquiv.subgroupCongr hLmap.symm)).trans
    (L.equivMapOfInjective _ (adjointGroup τ K).subtype_injective).symm
  have : Finite L := Finite.of_equiv _ eL.toEquiv
  have hcardL : Nat.card L = Nat.card K * (Nat.card K ^ 2 - 1) := by
    rw [← Nat.card_congr eL.toEquiv]
    exact card_SL2 K
  have hUL : Ub ≤ L := le_sup_left
  have hcardU : Nat.card Ub = Nat.card K := by
    rw [Nat.card_congr (Ub.equivMapOfInjective _ (adjointGroup τ K).subtype_injective).toEquiv,
      hUb, map_subtype_rootGroup _ hβ, CFSG.Blueprint.Chevalley.card_rootSubgroup]
  set U' : Subgroup L := Ub.subgroupOf L with hU'
  have hcardU' : Nat.card U' = Nat.card K := by
    rw [hU', ← hcardU]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUL).toEquiv
  have hpU' : IsPGroup p U' := IsPGroup.of_card (n := f) (by rw [hcardU', hK])
  have hidx : U'.index = Nat.card K ^ 2 - 1 := by
    have h := U'.card_mul_index
    rw [hcardU', hcardL] at h
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h
  have hpidx : ¬ p ∣ U'.index := by
    rw [hidx]
    intro hdvd
    have h1 : p ∣ Nat.card K ^ 2 := by
      rw [hK]
      exact dvd_pow (dvd_pow_self p (by omega)) two_ne_zero
    have h2 : 1 ≤ Nat.card K ^ 2 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ Nat.card_pos.ne')
    have h3 : p ∣ Nat.card K ^ 2 - (Nat.card K ^ 2 - 1) := Nat.dvd_sub h1 hdvd
    rw [Nat.sub_sub_self h2] at h3
    exact hp.one_lt.ne' (Nat.dvd_one.mp h3)
  let P₁ : Sylow p L := hpU'.toSylow hpidx
  have hXL : X.map Ψ ≤ L := by
    rw [← hR]
    exact Subgroup.map_mono hXR
  have hpH : IsPGroup p ((X.map Ψ).subgroupOf L) :=
    (hX.map Ψ).comap_of_injective L.subtype L.subtype_injective
  obtain ⟨P₂, hP₂⟩ := hpH.exists_le_sylow
  obtain ⟨l, hl⟩ := MulAction.exists_smul_eq L P₁ P₂
  obtain ⟨y₁, -, hy₁⟩ : (l : adjointGroup τ K) ∈ R.map Ψ := by
    rw [hR]
    exact l.2
  refine ⟨y₁⁻¹, ?_⟩
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  have hmem : (⟨Ψ x, hXL ⟨x, hx, rfl⟩⟩ : L) ∈ (P₂ : Subgroup L) :=
    hP₂ (by rw [Subgroup.mem_subgroupOf]; exact ⟨x, hx, rfl⟩)
  rw [← hl, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hmem
  obtain ⟨u, hu, hu'⟩ := hmem
  have hu'' : (l : adjointGroup τ K) * u * (l : adjointGroup τ K)⁻¹ = Ψ x :=
    congrArg Subtype.val hu'
  have hconj : Ψ ((MulAut.conj y₁⁻¹) x) = (u : adjointGroup τ K) := by
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, inv_inv, hy₁, ← hu'']
    group
  change Ψ ((MulAut.conj y₁⁻¹).toMonoidHom x) ∈ Ub
  rw [MulEquiv.coe_toMonoidHom, hconj]
  exact Subgroup.mem_subgroupOf.mp ((IsPGroup.mem_toSylow hpU' hpidx).mp hu)

theorem exists_psi_A5_E6_rankOne
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    ∃ Ψ : SL(5 + 1, K) →* adjointGroup .E6 K,
      Ψ.ker ≤ Subgroup.center (SL(5 + 1, K)) ∧
      Ψ.range.map (adjointGroup .E6 K).subtype = pairSpan .E6 K (Set.range e6A5Root) ∧
      ∀ k : Fin 5, (CurtisTits.rankOne (SpecialLinear.rootDatum 5 K).rootGroup k).map Ψ =
        (adjDatum (rootOperatorFamily .E6) K).rootGroup (e6A5Root k) ⊔
          (adjDatum (rootOperatorFamily .E6) K).rootGroup (-e6A5Root k) := by
  obtain ⟨hf, h3⟩ := one_le_and_three_le_of_card hp hp2 hK
  have hadm : StatedLieAdmissible .PSL (5 + 1) p f := ⟨hp, hf, by norm_num, by simp, by simp⟩
  obtain ⟨O, C, hE⟩ := exists_e6_chevalleyExtras K
  obtain ⟨ρ, hρ, hcomm, hψ⟩ := exists_levi_frame hE rfl e6A5Node e6A5_adj e6A5_nadj
  obtain ⟨Ψ, hker, hrange, hrk⟩ := specialLinear_frame_rankOne (m := 5) hadm (by norm_num) hK
    hcomm hρ hψ
  refine ⟨Ψ, hker, ?_, hrk⟩
  rw [hrange]
  exact map_subtype_iSup_rootPair e6A5Root (fun k => isRoot_single _ _)
theorem exists_psi_A7_E7_rankOne
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    ∃ Ψ : SL(7 + 1, K) →* adjointGroup .E7 K,
      Ψ.ker ≤ Subgroup.center (SL(7 + 1, K)) ∧
      Ψ.range.map (adjointGroup .E7 K).subtype = pairSpan .E7 K (Set.range e7A7Root) ∧
      ∀ k : Fin 7, (CurtisTits.rankOne (SpecialLinear.rootDatum 7 K).rootGroup k).map Ψ =
        (e7AdjointDatum K).rootGroup (e7A7Root k) ⊔ (e7AdjointDatum K).rootGroup (-e7A7Root k) := by
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hK
  have hadm : StatedLieAdmissible .PSL 8 p f := ⟨hp, hf, by norm_num, by simp, by simp⟩
  obtain ⟨O, C, hE⟩ := exists_e7_chevalleyExtras K
  choose ρF hρFi hρFr hρFv using exists_rankOne_param hE
  set n := weylWordElt .E7 K e7BetaWord with hn
  set U : Fin 7 → Subgroup (adjointGroup .E7 K) := fun k =>
    (e7AdjointDatum K).rootGroup (e7A7Root k) ⊔ (e7AdjointDatum K).rootGroup (-e7A7Root k)
      with hU_def
  let ρ : Fin 7 → SL(2, K) →* adjointGroup .E7 K := fun k =>
    if k = 0 then (MulAut.conj n).toMonoidHom.comp (ρF (e7Node 5)) else ρF (e7A7Node k)
  have hρ0 : ρ 0 = (MulAut.conj n).toMonoidHom.comp (ρF (e7Node 5)) := by simp [ρ]
  have hρk : ∀ k, k ≠ 0 → ρ k = ρF (e7A7Node k) := fun k hk => by simp [ρ, hk]
  have hU0 : U 0 =
      (e7AdjointDatum K).rootGroup e7BetaRoot ⊔ (e7AdjointDatum K).rootGroup (-e7BetaRoot) := by
    simp [hU_def, e7A7Root]
  have hUk : ∀ k, k ≠ 0 → U k = CurtisTits.rankOne (e7AdjointDatum K).rootGroup (e7A7Node k) :=
      fun k hk => by
    have h : e7A7Root k = Pi.single (e7A7Node k) 1 := by simp [e7A7Root, hk]
    simp only [hU_def, h]
    rfl
  have hr0 : (ρ 0).range = U 0 := by
    rw [hρ0, hU0, MonoidHom.range_comp, hρFr]
    change ((e7AdjointDatum K).rootGroup (Pi.single (e7Node 5) 1) ⊔
      (e7AdjointDatum K).rootGroup (-Pi.single (e7Node 5) 1)).map _ = _
    rw [map_conj_weylWordElt_rootPair e7BetaWord (isRoot_single _ _), wordReflect_e7BetaWord]
  have hρ' : ∀ k, Function.Injective (ρ k) ∧ (ρ k).range = U k := by
    intro k
    by_cases hk : k = 0
    · subst hk
      refine ⟨?_, hr0⟩
      rw [hρ0]
      exact (MulAut.conj n).injective.comp (hρFi _)
    · rw [hρk k hk, hUk k hk]
      exact ⟨hρFi _, hρFr _⟩
  have h0 : ∀ j : Fin 7, j ≠ 0 → j ≠ 1 → Commutes (U 0) (U j) := by
    intro j hj0 hj1
    rw [hU0, hUk j hj0]
    obtain ⟨h1, h2, h3, h4, h5⟩ := e7A7_root_orth j hj0 hj1
    exact commutes_rootPair_of_noG2 noG2_E7 isRoot_e7BetaRoot (isRoot_single _ _) h1 h2 h3 h4 h5
  have hcomm : ∀ i j : Fin 7, i ≠ j → ¬ j.val = i.val + 1 → ¬ i.val = j.val + 1 →
      ∀ u ∈ U i, ∀ v ∈ U j, u * v = v * u := by
    intro i j hij h1 h2 u hu v hv
    by_cases hi : i = 0
    · subst hi
      exact h0 j (fun h => hij h.symm) (e7A7_ne_one j h1) u hu v hv
    · by_cases hj : j = 0
      · subst hj
        exact (h0 i hi (e7A7_ne_one i h2) v hv u hu).symm
      · rw [hUk i hi] at hu
        rw [hUk j hj] at hv
        obtain ⟨hne, hc1, hc2⟩ := e7A7_nadj i j hij h1 h2 hi hj
        exact commutes_rankOne_of_cartan_eq_zero hE rfl hne hc1 hc2 u hu v hv
  have hψ : ∀ i j : Fin 7, j.val = i.val + 1 → ∃ ψ : SL(3, K) →* adjointGroup .E7 K,
      ψ.comp (ClassicalInvolution.WeakCT.blk K 0) = ρ i ∧
        ψ.comp (ClassicalInvolution.WeakCT.blk K 1) = ρ j := by
    intro i j hij
    have hj0 : j ≠ 0 := fun h => by subst h; simp at hij
    by_cases hi : i = 0
    · subst hi
      obtain rfl : j = 1 := Fin.ext (by simpa using hij)
      obtain ⟨emb, -, -, hv⟩ := exists_sl3Levi hE rfl (k := e7Node 4) e7Node_five_ne_six
        e7_cartan_56 e7_cartan_65 e7_sl3_witness_56
      obtain ⟨h0', h1'⟩ := sl3_comp_blk hv (hρFv (e7Node 5)) (hρFv (e7Node 6))
      refine ⟨(MulAut.conj n).toMonoidHom.comp emb, ?_, ?_⟩
      · rw [hρ0, MonoidHom.comp_assoc, h0']
      · rw [hρk 1 (by decide), MonoidHom.comp_assoc, h1']
        refine MonoidHom.ext fun A => ?_
        have hA : ρF (e7Node 6) A ∈ CurtisTits.rankOne (e7AdjointDatum K).rootGroup (e7Node 6) := by
          rw [← hρFr]
          exact ⟨A, rfl⟩
        rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          (commute_weylWordElt hE e7BetaWord e7BetaWord_orth hA).eq, mul_inv_cancel_right]
        rfl
    · obtain ⟨hne, hc1, hc2, l, hl⟩ := e7A7_adj i j hij hi
      obtain ⟨emb, -, -, hv⟩ := exists_sl3Levi hE rfl hne hc1 hc2 hl
      rw [hρk i hi, hρk j hj0]
      exact ⟨emb, sl3_comp_blk hv (hρFv _) (hρFv _)⟩
  have hrt : ∀ k, IsRoot .E7 (e7A7Root k) := by
    intro k
    by_cases hk : k = 0
    · rw [hk, show e7A7Root 0 = e7BetaRoot by simp [e7A7Root]]
      exact isRoot_e7BetaRoot
    · rw [show e7A7Root k = Pi.single (e7A7Node k) 1 by simp [e7A7Root, hk]]
      exact isRoot_single _ _
  obtain ⟨Ψ, hker, hrange, hrk⟩ := specialLinear_frame_rankOne (m := 7) hadm (by norm_num) hK
    hcomm hρ' hψ
  refine ⟨Ψ, hker, ?_, hrk⟩
  rw [hrange]
  exact map_subtype_iSup_rootPair e7A7Root hrt

end CFSG.ComponentClassification.Burgoyne.X10
