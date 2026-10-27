module

public import CFSG.GH74.GLS.C3.Layer1.Thm1Transport
public import CFSG.GH74.GLS.C3.Layer1.Thm1Leaves
public import CFSG.GH74.GLS.C3.Layer1.Thm1Quat
public import CFSG.GH74.GLS.C3.Layer1.Thm1AutA7

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.C3.Layer1

@[expose] def B_thm1_P31_comp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → NoV2 G →
    ∀ (x y : G) (K : Subgroup G), Is2TerminalU2Triple x y K →
      (HasL2Model (kBar K) Odd ∨ Nonempty (kBar K ≃* alternatingGroup (Fin 7))) →
      (∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K) ∧
      (∀ K' : Subgroup G, IsPCompIn 2 (centralizer ({x} : Set G)) K' → K' = K)

@[expose] def B_thm1_P31_layer : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → NoV2 G →
    ∀ (x y : G) (K : Subgroup G), Is2TerminalU2Triple x y K →
      (HasL2Model (kBar K) Odd ∨ Nonempty (kBar K ≃* alternatingGroup (Fin 7))) →
      (∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K) →
      ∀ T : Subgroup G, Setup1D x K T → ∀ f z : G, f ∈ T → orderOf f = 2 →
        (∀ p ∈ T ⊓ K, f * p = p * f) → P34.InducesFAutL2A7 f K →
        z ∈ T ⊓ K → orderOf z = 2 → (∀ p ∈ T ⊓ K, z * p = p * z) →
        pLayerOf 2 (K ⊓ centralizer ({f} : Set G)) ≠ ⊥ ∨
          (Nonempty (kBar K ≃* alternatingGroup (Fin 7)) ∧
            pLayerOf 2 (K ⊓ centralizer ({f * z} : Set G)) ≠ ⊥)

end CFSG.GH74.GLS

namespace CFSG.GH74.GLS.C3.Layer1.Thm1

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1
open scoped commutatorElement

theorem exists_isElementaryAbelian_card_pRank {H : Type} [Group H] [Finite H] :
    ∃ A : Subgroup H, IsElementaryAbelian 2 ↥A ∧ Nat.card ↥A = 2 ^ pRank 2 H := by
  have hne : Set.Nonempty {r : ℕ | ∃ A : Subgroup H, IsElementaryAbelian 2 ↥A ∧
      Nat.card ↥A = 2 ^ r} :=
    ⟨0, ⊥, Back.isElementaryAbelian_of_forall
      (fun u hu v hv => by rw [Subgroup.mem_bot.1 hu, Subgroup.mem_bot.1 hv])
      (fun u hu => by rw [Subgroup.mem_bot.1 hu, one_mul]), by simp⟩
  have hbdd : BddAbove {r : ℕ | ∃ A : Subgroup H, IsElementaryAbelian 2 ↥A ∧
      Nat.card ↥A = 2 ^ r} := by
    refine ⟨Nat.card H, ?_⟩
    rintro r ⟨B, -, hB⟩
    calc r ≤ 2 ^ r := (Nat.lt_pow_self (by norm_num)).le
      _ = Nat.card B := hB.symm
      _ ≤ Nat.card H := Subgroup.card_le_card_group B
  exact Nat.sSup_mem hne hbdd

theorem exists_conj_le_of_isSylowOf {G : Type} [Group G] [Finite G] {P K X : Subgroup G}
    (hP : IsSylowOf 2 P K) (hXK : X ≤ K) (hX : IsPGroup 2 ↥X) :
    ∃ k ∈ K, ∀ y ∈ X, k⁻¹ * y * k ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, rfl⟩ := hP
  obtain ⟨Q', hQ'⟩ := (hX.comap_subtype (K := K)).exists_le_sylow
  obtain ⟨c, rfl⟩ := MulAction.exists_smul_eq K Q Q'
  refine ⟨c, c.2, fun y hy => ?_⟩
  have hy' : (⟨y, hXK hy⟩ : K) ∈ ((c • Q : Sylow 2 K) : Subgroup K) := hQ' hy
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy'
  exact ⟨_, hy', by simp [MulAut.inv_apply]⟩

theorem exists_E₁ {G : Type} [Group G] [Finite G] {C T : Subgroup G} (hT : IsSylowOf 2 T C)
    (hrank : pRank 2 ↥C = 4) :
    ∃ E₁ : Subgroup G, E₁ ≤ T ∧ IsElementaryAbelian 2 ↥E₁ ∧ 16 ≤ Nat.card ↥E₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, hA, hcard⟩ := exists_isElementaryAbelian_card_pRank (H := ↥C)
  rw [hrank] at hcard
  have hE₀ : IsElementaryAbelian 2 ↥(A.map C.subtype) := by
    have := hA
    exact IsElementaryAbelian.map_subtype
  have hE₀card : Nat.card ↥(A.map C.subtype) = 16 := by
    rw [Subgroup.card_map_of_injective C.subtype_injective, hcard]
    norm_num
  have hE₀p : IsPGroup 2 ↥(A.map C.subtype) := IsElementaryAbelian.isPGroup 2 _
  obtain ⟨c, -, hc⟩ := exists_conj_le_of_isSylowOf hT (Subgroup.map_subtype_le A) hE₀p
  refine ⟨(A.map C.subtype).map (MulAut.conj c⁻¹).toMonoidHom, ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    have := hc y hy
    simpa [MulAut.conj_apply] using this
  · have := hE₀
    exact IsElementaryAbelian.map _
  · rw [Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective, hE₀card]

theorem card_le_two_of_noV2 {G : Type} [Group G] [Finite G] (hV : NoV2 G) {x y : G}
    {K : Subgroup G} (h𝒰 : Is2TerminalU2Triple x y K) :
    ∀ A : Subgroup G, A ≤ CMK (centralizer ({x} : Set G)) K → IsElementaryAbelian 2 ↥A →
      Nat.card ↥A ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro A hAC hA
  by_contra hlt
  push Not at hlt
  have hAC' : A ≤ CxK x K := hAC
  obtain ⟨r, hr⟩ := (IsPGroup.iff_card).1 (IsElementaryAbelian.isPGroup 2 ↥A)
  have hr2 : 2 ≤ r := by
    by_contra hr2
    push Not at hr2
    have h2r : 2 ^ r ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hA' : IsElementaryAbelian 2 ↥(A.subgroupOf (CxK x K)) := by
    have := hA
    exact IsElementaryAbelian.subgroupOf hAC'
  have hcard : Nat.card ↥(A.subgroupOf (CxK x K)) = 2 ^ r := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC').toEquiv]
    exact hr
  have h2 : 2 ≤ pRank 2 ↥(CxK x K) :=
    hr2.trans (LieType.SteinbergBR.le_pRank_of_card one_lt_two _ hA' hcard)
  exact hV ⟨x, y, K, h𝒰.1, h𝒰.2.1, Or.inl h2, fun _ => h𝒰⟩

theorem not_hasL2Model_nine_of_noV2 {G : Type} [Group G] (hV : NoV2 G) {x y : G}
    {K : Subgroup G} (h𝒰 : Is2TerminalU2Triple x y K) :
    ¬ HasL2Model (kBar K) (fun q => q = 9) := fun h =>
  hV ⟨x, y, K, h𝒰.1, h𝒰.2.1, Or.inl (h𝒰.2.2.2.2 h).1, fun _ => h𝒰⟩

theorem kBar_autData
    {G : Type} [Group G] [Finite G] (h2hb : IVK.IVK_1_2h_b) (hV : NoV2 G)
    {x y : G} {K : Subgroup G} (h𝒰 : Is2TerminalU2Triple x y K)
    (hshape : HasL2Model (kBar K) Odd ∨ Nonempty (kBar K ≃* alternatingGroup (Fin 7))) :
    Function.Injective (MulAut.conj : kBar K →* MulAut (kBar K)) ∧ AutLevelF (kBar K) := by
  rcases hshape with h | ⟨⟨e7⟩⟩
  · obtain ⟨F, _, _, _, ⟨e⟩⟩ := exists_l2_model_of_hasL2Model h
    exact ⟨IVK.conj_injective_of_L2 e, autLevelF_of_L2 h2hb (not_hasL2Model_nine_of_noV2 hV h𝒰) h⟩
  · exact ⟨conj_injective_of_A7 e7, autLevelF_of_A7 e7⟩

theorem quaternion_isMaximalClass (e : ℕ) (he : 1 ≤ e) :
    P34.IsMaximalClassTwoGroup (QuaternionGroup (2 ^ e)) := by
  obtain ⟨hcl, hcard⟩ := quaternionGroup_class e he
  have hp : IsPGroup 2 (QuaternionGroup (2 ^ e)) := IsPGroup.of_card hcard
  have : Group.IsNilpotent (QuaternionGroup (2 ^ e)) := hp.isNilpotent
  exact ⟨hp, this, by rw [hcl, hcard]⟩

theorem isMaximalClassTwoGroup_of_equiv {X Y : Type} [Group X] [Group Y] [Finite X]
    (e : X ≃* Y) (h : P34.IsMaximalClassTwoGroup X) : P34.IsMaximalClassTwoGroup Y := by
  obtain ⟨hp, hnil, hcard⟩ := h
  refine ⟨hp.of_equiv e, ?_⟩
  have hnY : Group.IsNilpotent Y := Group.nilpotent_of_surjective e.toMonoidHom e.surjective
  have h1 : Group.nilpotencyClass Y ≤ Group.nilpotencyClass X :=
    Group.nilpotencyClass_le_of_surjective e.toMonoidHom e.surjective
  have h2 : Group.nilpotencyClass X ≤ Group.nilpotencyClass Y :=
    have := hnY
    Group.nilpotencyClass_le_of_surjective e.symm.toMonoidHom e.symm.surjective
  refine ⟨hnY, ?_⟩
  rw [← Nat.card_congr e.toEquiv, ← hcard, le_antisymm h1 h2]

theorem exists_Q_of_card_le_two {G : Type} [Group G] [Finite G] {M : Subgroup G}
    (hQ2 : ∀ A : Subgroup G, A ≤ M → IsElementaryAbelian 2 ↥A → Nat.card ↥A ≤ 2) :
    ∃ Q : Subgroup G, IsSylowOf 2 Q M ∧ (IsCyclic ↥Q ∨ P34.IsMaximalClassTwoGroup ↥Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := exists_isSylowOf 2 M
  refine ⟨Q, hQ, ?_⟩
  have hrank : DisconnectedInvolutionGraph.Helpers.NoCommutingDistinctInvolutions ↥Q := by
    intro u v huv
    by_contra hne
    have hu : orderOf (u : ↥Q) = 2 := u.2
    have hv : orderOf (v : ↥Q) = 2 := v.2
    obtain ⟨V, hVle, hV, hVcard⟩ :=
      LocalAnalysis.ComponentInitial.AlternatingFourGroup.exists_elementary_four_of_commute hu hv
        huv (fun h => hne (Subtype.ext h))
    have hVM : V.map Q.subtype ≤ M := by
      refine (Subgroup.map_subtype_le V).trans hQ.le
    have hVe : IsElementaryAbelian 2 ↥(V.map Q.subtype) := by
      have := hV
      exact IsElementaryAbelian.map_subtype
    have := hQ2 _ hVM hVe
    rw [Subgroup.card_map_of_injective Q.subtype_injective, hVcard] at this
    omega
  rcases DisconnectedInvolutionGraph.Helpers.rank_one_two_cyclic_or_quaternion hQ.isPGroup hrank
    with hc | ⟨e, he, ⟨eq⟩⟩
  · exact Or.inl hc
  · exact Or.inr (isMaximalClassTwoGroup_of_equiv eq (quaternion_isMaximalClass e he))

theorem thm1_P31s_of
    (h2hb : IVK.IVK_1_2h_b) (hL1 : B_thm1_P31_comp) (hL2 : B_thm1_P31_layer) :
    B_thm1_P31s := by
  intro G _ _ hG hV x y K h𝒰 hshape
  obtain ⟨hKN, huniq⟩ := hL1 G hG hV x y K h𝒰 hshape
  have hKC : K ≤ centralizer ({x} : Set G) := h𝒰.1.1.2.1
  have hxK : ∀ k ∈ K, x * k = k * x := fun k hk =>
    (mem_centralizer_singleton_iff.1 (hKC hk)).symm
  have hxC : x ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 rfl
  have hQ2 := card_le_two_of_noV2 hV h𝒰
  obtain ⟨hcen, hAut⟩ := kBar_autData h2hb hV h𝒰 hshape
  refine ⟨hKN, huniq, exists_Q_of_card_le_two hQ2, ?_⟩
  intro T hT
  obtain ⟨E₁, hE₁T, hE₁, hE₁16⟩ :=
    exists_E₁ hT.sylowT (by rw [h𝒰.2.2.1.2, hG.pRank_eq_four])
  obtain ⟨f, z, hfT, hf2, hfc, hfx, hind, hinn, hdih, hzP, hz2, hzc, hzu⟩ :=
    transport_G hKC hKN hT.sylowT hxC hxK hcen hAut hE₁T hE₁ hE₁16 hQ2
  have hfC : f ∈ centralizer ({x} : Set G) := hT.sylowT.le hfT
  have hzC : z ∈ centralizer ({x} : Set G) := hT.sylowT.le hzP.1
  refine ⟨?_, hdih, z, hzP, hz2, hzc, hzu⟩
  rcases hL2 G hG hV x y K h𝒰 hshape hKN T hT f z hfT hf2 hfc hind hzP hz2 hzc with hl | ⟨hA7, hl⟩
  · exact ⟨f, ⟨hfT, hf2, hfc, hfx, hl⟩, hind⟩
  ·
    have hfz : f * z = z * f := hfc z hzP
    have hzT : z ∈ T := hzP.1
    have hzK : z ∈ K := hzP.2
    have hfzC : f * z ∈ centralizer ({x} : Set G) := Subgroup.mul_mem _ hfC hzC
    have hφz : Back.actHom hKN ⟨z, hzC⟩ ∈ IVK.innAut (kBar K) := by
      rw [Back.actHom_of_mem hKN hzK hzC]
      exact ⟨_, rfl⟩
    have hφfz : Back.actHom hKN ⟨f * z, hfzC⟩ ∉ IVK.innAut (kBar K) := by
      intro h
      apply hinn hfC
      have h1 := (Back.actHom hKN).map_mul ⟨f, hfC⟩ ⟨z, hzC⟩
      have e : (⟨f, hfC⟩ * ⟨z, hzC⟩ : ↥(centralizer ({x} : Set G))) = ⟨f * z, hfzC⟩ := rfl
      rw [e] at h1
      rw [h1] at h
      have := (IVK.innAut (kBar K)).mul_mem h ((IVK.innAut (kBar K)).inv_mem hφz)
      simpa using this
    have hfz1 : f * z ≠ 1 := fun h => hφfz (by
      have : (⟨f * z, hfzC⟩ : ↥(centralizer ({x} : Set G))) = 1 := Subtype.ext h
      rw [this, map_one]
      exact (IVK.innAut (kBar K)).one_mem)
    have hφx : Back.actHom hKN ⟨x, hxC⟩ = 1 :=
      (Back.actHom_eq_one_iff_commutator_mem hKN ⟨x, hxC⟩).2 (fun k hk => by
        have : ⁅k, x⁆ = 1 := by
          rw [commutatorElement_def, ← hxK k hk]
          group
        rw [this]
        exact (pPrimeCoreOf 2 K).one_mem)
    have hfzx : f * z ≠ x := fun h => hφfz (by
      have : (⟨f * z, hfzC⟩ : ↥(centralizer ({x} : Set G))) = ⟨x, hxC⟩ := Subtype.ext h
      rw [this, hφx]
      exact (IVK.innAut (kBar K)).one_mem)
    have hf2' : orderOf (f * z) = 2 := by
      refine orderOf_eq_prime ?_ hfz1
      have hff : f * f = 1 := by
        have := pow_orderOf_eq_one f
        rwa [hf2, sq] at this
      have hzz : z * z = 1 := by
        have := pow_orderOf_eq_one z
        rwa [hz2, sq] at this
      calc (f * z) ^ 2 = f * z * (f * z) := sq _
        _ = f * (z * f) * z := by simp only [mul_assoc]
        _ = f * (f * z) * z := by rw [← hfz]
        _ = (f * f) * (z * z) := by simp only [mul_assoc]
        _ = 1 := by rw [hff, hzz, one_mul]
    refine ⟨f * z, ⟨T.mul_mem hfT hzT, hf2', fun p hp => ?_, hfzx, hl⟩, ?_⟩
    · have h1 := hfc p hp
      have h2 := hzc p hp
      calc f * z * p = f * (z * p) := by group
        _ = f * (p * z) := by rw [h2]
        _ = (f * p) * z := by group
        _ = (p * f) * z := by rw [h1]
        _ = p * (f * z) := by group
    · have hφfz1 : Back.actHom hKN ⟨f * z, hfzC⟩ ≠ 1 := fun h =>
        hφfz (by rw [h]; exact (IVK.innAut (kBar K)).one_mem)
      exact ⟨U1a.mem_normalizer_of_norm hKN hfzC, hφfz1, Or.inr ⟨hA7, hφfz⟩⟩
end CFSG.GH74.GLS.C3.Layer1.Thm1
