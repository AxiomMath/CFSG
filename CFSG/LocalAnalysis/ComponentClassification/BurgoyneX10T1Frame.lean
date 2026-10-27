module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofTwE6Frame

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.X10

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.Timmesfeld CFSG.ClassicalInvolution.WeakCT
  CFSG.ComponentClassification.CatLeafProof
open scoped MatrixGroups

theorem spinPlus_frame_rankOne {n p f : ℕ} (hadm : StatedLieAdmissible .POmegaPlus n p f)
    (hn3 : 3 ≤ n) {F : Type} [Field F] [Finite F] (hF : Nat.card F = p ^ f) {G : Type} [Group G]
    {U : Fin n → Subgroup G}
    (hcomm : ∀ i j : Fin n, i ≠ j → ¬ edgeD n i j → ¬ edgeD n j i →
      ∀ u ∈ U i, ∀ v ∈ U j, u * v = v * u)
    {ρ : Fin n → SL(2, F) →* G} (hρ : ∀ k, Function.Injective (ρ k) ∧ (ρ k).range = U k)
    (hψ : ∀ i j : Fin n, edgeD n i j → ∃ ψ : SL(3, F) →* G,
      ψ.comp (blk F 0) = ρ i ∧ ψ.comp (blk F 1) = ρ j) :
    ∃ Ψ : spinGroup (Spin.quadPlus n F) →* G, Ψ.ker ≤ Subgroup.center _ ∧
      Ψ.range = ⨆ k, U k ∧
      ∀ k : Fin n, (CurtisTits.rankOne (Spin.plusDatum n F hn3).rootGroup k).map Ψ = U k := by
  obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan (Spin.plusDatum n F hn3).isFiniteType
    (Dv := (Spin.plusDatum n F hn3).divisible) rfl
  have hE := Steinberg.SpinPlus.chevalleyExtras hn3 O Steinberg.SpinPlus.commC
    (Steinberg.SpinPlus.commutatorFormula hn3 O)
  obtain ⟨x', hD, -⟩ := exists_simplyLacedLevis hE rfl
    (fun α _ β _ _ _ => Steinberg.SpinPlus.commC_natAbs α β (1, 1)) LevisSpin.edgeD_asymm
    (fun _ _ h => LevisSpin.cartanD_of_edgeD h)
    (fun _ _ hij h1 h2 => LevisSpin.cartanD_of_not_edgeD hij h1 h2)
    (fun _ _ h => LevisSpin.edgeD_neighbour hn3 h)
    (Spin.plusDatum_steinbergExtras hn3).torus_iSupIndep
    (fun (k : Fin n) => by
      have h := (Steinberg.SpinPlus.isCTGroupDatum (K := F) hn3).sq_mem k
      rw [← weylElement_spinPlus hn3 k] at h
      exact h)
  obtain ⟨Ψ, hker, hrange, -, -, hrk⟩ := weakCT_of_frame_subgroup (RingEquiv.refl F)
    (CurtisTits.curtisTitsConclusion_spinPlus hadm hF hn3) (leviConePresented_spinPlus F hn3) hD
    (⟨0, by omega⟩ : Fin n) hcomm hρ hψ
  exact ⟨Ψ, hker, hrange, hrk⟩

theorem exists_psi_D5_E6_rankOne
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    ∃ Ψ : spinGroup (Spin.quadPlus 5 K) →* adjointGroup .E6 K,
      Ψ.ker ≤ Subgroup.center (spinGroup (Spin.quadPlus 5 K)) ∧
      Ψ.range = ⨆ k, CurtisTits.rankOne (adjDatum (rootOperatorFamily .E6) K).rootGroup
        (e6D5Node k) ∧
      ∀ k : Fin 5, (CurtisTits.rankOne (Spin.plusDatum 5 K (by norm_num)).rootGroup k).map Ψ =
        CurtisTits.rankOne (adjDatum (rootOperatorFamily .E6) K).rootGroup (e6D5Node k) := by
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hK
  have hadm : StatedLieAdmissible .POmegaPlus 5 p f := ⟨hp, hf, by norm_num⟩
  obtain ⟨O, C, hE⟩ := exists_e6_chevalleyExtras K
  obtain ⟨ρ, hρ, hcomm, hψ⟩ := exists_levi_frame hE rfl e6D5Node e6D5_adj e6D5_nadj
  exact spinPlus_frame_rankOne hadm (by norm_num) hK hcomm hρ hψ

theorem exists_psi_e6D5Tw
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    ∃ Ψ : spinGroup (Spin.quadPlus 5 K) →* adjointGroup .E6 K,
      Ψ.ker ≤ Subgroup.center (spinGroup (Spin.quadPlus 5 K)) ∧
      Ψ.range.map (adjointGroup .E6 K).subtype = pairSpan .E6 K (Set.range e6D5TwRoot) ∧
      ∀ k : Fin 5, (CurtisTits.rankOne (Spin.plusDatum 5 K (by norm_num)).rootGroup k).map Ψ =
        (adjDatum (rootOperatorFamily .E6) K).rootGroup (e6D5TwRoot k) ⊔
          (adjDatum (rootOperatorFamily .E6) K).rootGroup (-e6D5TwRoot k) := by
  obtain ⟨Ψ, hker, hrange, hrk⟩ := exists_psi_D5_E6_rankOne hp hp2 hK
  set c := MulAut.conj (weylWordElt .E6 K e6D5TwWord) with hc
  have hrt : ∀ k, IsRoot .E6 (e6D5TwRoot k) := fun k => by
    rw [← wordReflect_e6D5TwWord k]
    exact isRoot_wordReflect _ (isRoot_single _ _)
  have hmap : ∀ k, (CurtisTits.rankOne (adjDatum (rootOperatorFamily .E6) K).rootGroup
      (e6D5Node k)).map c.toMonoidHom =
      (adjDatum (rootOperatorFamily .E6) K).rootGroup (e6D5TwRoot k) ⊔
        (adjDatum (rootOperatorFamily .E6) K).rootGroup (-e6D5TwRoot k) := fun k => by
    rw [← wordReflect_e6D5TwWord k]
    exact map_conj_weylWordElt_rootPair e6D5TwWord (isRoot_single _ _)
  refine ⟨c.toMonoidHom.comp Ψ, fun x hx => hker ?_, ?_, fun k => ?_⟩
  · rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hx
    rw [MonoidHom.mem_ker]
    exact c.injective (by rw [MulEquiv.coe_toMonoidHom] at hx; rw [hx, map_one])
  · rw [MonoidHom.range_comp, hrange, Subgroup.map_iSup]
    simp only [hmap]
    exact map_subtype_iSup_rootPair e6D5TwRoot hrt
  · rw [← Subgroup.map_map, hrk k]
    exact hmap k

theorem card_SL2 (K : Type) [Field K] [Finite K] :
    Nat.card (SL2 K) = Nat.card K * (Nat.card K ^ 2 - 1) := by
  let := Fintype.ofFinite K
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    Nat.card_eq_fintype_card, show Fintype.card K ^ 2 - Fintype.card K =
      Fintype.card K * (Fintype.card K - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
    Nat.mul_div_cancel _ (by omega), mul_comm]

theorem exists_conj_rootGroup_le
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (Ψ : spinGroup (Spin.quadPlus 5 K) →* adjointGroup .E6 K)
    (hrk : (CurtisTits.rankOne (Spin.plusDatum 5 K (by norm_num)).rootGroup (0 : Fin 5)).map Ψ =
      (adjDatum (rootOperatorFamily .E6) K).rootGroup (e6D5TwRoot 0) ⊔
        (adjDatum (rootOperatorFamily .E6) K).rootGroup (-e6D5TwRoot 0)) :
    ∃ y : spinGroup (Spin.quadPlus 5 K),
      ((Spin.plusRootGroup 5 K (by norm_num) (Pi.single 0 1)).map
        (MulAut.conj y).toMonoidHom).map Ψ ≤
        (adjDatum (rootOperatorFamily .E6) K).rootGroup (e6D5TwRoot 0) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hK
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have hβ : IsRoot .E6 (e6D5TwRoot 0) := isRoot_single _ _
  set Ub := (adjDatum (rootOperatorFamily .E6) K).rootGroup (e6D5TwRoot 0) with hUb
  set L := Ub ⊔ (adjDatum (rootOperatorFamily .E6) K).rootGroup (-e6D5TwRoot 0) with hL
  set X := Spin.plusRootGroup 5 K (by norm_num) (Pi.single 0 1) with hX
  obtain ⟨-, ⟨eQ⟩, -⟩ := odd_arbitrary_root_pair_SL2_p_components .E6 K hK2 hβ
  have hLmap : L.map (adjointGroup .E6 K).subtype =
      rootSubgroup .E6 K (e6D5TwRoot 0) ⊔ rootSubgroup .E6 K (-e6D5TwRoot 0) := by
    rw [hL, Subgroup.map_sup, map_subtype_rootGroup _ hβ, map_subtype_rootGroup _ (IsRoot.neg hβ)]
  let eL : SL2 K ≃* L := (eQ.trans (MulEquiv.subgroupCongr hLmap.symm)).trans
    (L.equivMapOfInjective _ (adjointGroup .E6 K).subtype_injective).symm
  have : Finite L := Finite.of_equiv _ eL.toEquiv
  have hcardL : Nat.card L = Nat.card K * (Nat.card K ^ 2 - 1) := by
    rw [← Nat.card_congr eL.toEquiv]
    exact card_SL2 K
  have hUL : Ub ≤ L := le_sup_left
  have hcardU : Nat.card Ub = Nat.card K := by
    rw [Nat.card_congr (Ub.equivMapOfInjective _ (adjointGroup .E6 K).subtype_injective).toEquiv,
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
    rw [← hrk]
    exact Subgroup.map_mono le_sup_left
  have hpX : IsPGroup p X := by
    rw [hX, Spin.plusRootGroup_single]
    have hM : IsPGroup p (Multiplicative K) := IsPGroup.of_card (n := f) hK
    exact hM.of_surjective (Spin.rootD K _ 0).rangeRestrict (MonoidHom.rangeRestrict_surjective _)
  have hpH : IsPGroup p ((X.map Ψ).subgroupOf L) :=
    (hpX.map Ψ).comap_of_injective L.subtype L.subtype_injective
  obtain ⟨P₂, hP₂⟩ := hpH.exists_le_sylow
  obtain ⟨l, hl⟩ := MulAction.exists_smul_eq L P₁ P₂
  obtain ⟨y₁, -, hy₁⟩ : (l : adjointGroup .E6 K) ∈
      (CurtisTits.rankOne (Spin.plusDatum 5 K (by norm_num)).rootGroup (0 : Fin 5)).map Ψ := by
    rw [hrk]
    exact l.2
  refine ⟨y₁⁻¹, ?_⟩
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  have hmem : (⟨Ψ x, hXL ⟨x, hx, rfl⟩⟩ : L) ∈ (P₂ : Subgroup L) :=
    hP₂ (by rw [Subgroup.mem_subgroupOf]; exact ⟨x, hx, rfl⟩)
  rw [← hl, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hmem
  obtain ⟨u, hu, hu'⟩ := hmem
  have hu'' : (l : adjointGroup .E6 K) * u * (l : adjointGroup .E6 K)⁻¹ = Ψ x :=
    congrArg Subtype.val hu'
  have hconj : Ψ ((MulAut.conj y₁⁻¹) x) = (u : adjointGroup .E6 K) := by
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, inv_inv, hy₁, ← hu'']
    group
  change Ψ ((MulAut.conj y₁⁻¹).toMonoidHom x) ∈ Ub
  rw [MulEquiv.coe_toMonoidHom, hconj]
  exact Subgroup.mem_subgroupOf.mp ((IsPGroup.mem_toSylow hpU' hpidx).mp hu)

end CFSG.ComponentClassification.Burgoyne.X10
