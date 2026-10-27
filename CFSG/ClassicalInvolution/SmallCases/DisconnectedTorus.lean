module

public import CFSG.ClassicalInvolution.SmallCases.DisconnectedA2
public import CFSG.ClassicalInvolution.SmallCases.DisconnectedTight
public import CFSG.ClassicalInvolution.TwoGroupCase.TightPair

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open CFSG.DisconnectedInvolutionGraph.Helpers

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}

theorem UniqueInvolutionNormal.tightlyEmbedded (hK : UniqueInvolutionNormal K z) :
    classicalInvolutionTightlyEmbedded K := by
  intro g hg
  by_contra hodd
  have h2 : 2 ∣ Nat.card (K ⊓ K.map (MulAut.conj g).toMonoidHom : Subgroup G) :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  have := Fact.mk Nat.prime_two
  obtain ⟨⟨t, ht⟩, ht2⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have ht2' : orderOf t = 2 := by rw [← Subgroup.orderOf_mk t ht]; exact ht2
  obtain ⟨htK, htK'⟩ := ht
  have h1 : t = z := hK.2.2.1 t htK ht2'
  have h3 : t = g * z * g⁻¹ := hK.conj_unique g t htK' ht2'
  have hgz : g * z * g⁻¹ = z := by rw [← h3, h1]
  apply hg
  have hgC : g ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * z = (g * z * g⁻¹) * g := by group
      _ = z * g := by rw [hgz]
  exact mem_normalizer_of_mem_centralizer_of_normal hK.2.2.2.1 hK.2.2.2.2 hgC

@[expose] def CommutingSylowForcesCommuting (K : Subgroup G) : Prop :=
  ∀ g : G, g ∉ Subgroup.normalizer (K : Set G) → ∀ P₁ P₂ : Subgroup G,
    IsSylow2Of P₁ K → IsSylow2Of P₂ (conjSubgroup g K) →
      (∀ x ∈ P₁, ∀ y ∈ P₂, x * y = y * x) →
        ∀ a ∈ K, ∀ b ∈ conjSubgroup g K, a * b = b * a

theorem a2_pair_torus (hK : UniqueInvolutionNormal K z) (hT : SingleMemberControl K)
    (hCSM : CommutingSylowForcesCommuting K)
    {T₀ : Subgroup G} (hzS : z ∈ T₀) (hSC : T₀ ≤ Subgroup.centralizer ({z} : Set G)) {g : G}
    (hgS : g * z * g⁻¹ ∈ T₀) (hgz : g * z * g⁻¹ ≠ z) :
    ∃ R S : Subgroup G, z ∈ R ∧ PairData K g R S ∧ IsCyclic R ∧
      S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G) < S ⊓ conjSubgroup g K ∧
      ((Nat.card R = 2 ∧ Nat.card (S ⊓ Subgroup.normalizer (R : Set G) : Subgroup G) = 4 ∧
          (∀ y ∈ S ⊓ Subgroup.normalizer (R : Set G), y * y = 1) ∧
          S ⊓ Subgroup.centralizer (R : Set G) = S ⊓ Subgroup.normalizer (R : Set G)) ∨
        ((⨆ s ∈ S, conjSubgroup s R) = S ⊓ Subgroup.normalizer (R : Set G) ∧
          Nonempty ((S ⊓ Subgroup.normalizer (R : Set G) : Subgroup G) ≃* R × R))) := by
  obtain ⟨hne, -, hKz', hzN, -, -⟩ := a2_pair_of_tight hK hT hzS hSC hgS hgz
  have hzK : z ∈ K := hK.2.1
  have hg : g ∉ Subgroup.normalizer (K : Set G) := fun h => hne (conjSubgroup_eq_self_iff.mpr h)
  have hzo : orderOf z = 2 := hK.1
  have hP : IsPGroup 2 (Subgroup.zpowers z) := isPGroup_two_zpowers_of_orderOf_two hzo
  have hPA : Subgroup.zpowers z ≤ K ⊓ Subgroup.normalizer (conjSubgroup g K : Set G) :=
    (Subgroup.zpowers_le).mpr ⟨hzK, hzN⟩
  obtain ⟨R, S, hPR, d⟩ := exists_pairData hK.tightlyEmbedded hg hP hPA
  have hzR : z ∈ R := hPR (Subgroup.mem_zpowers z)
  have hR1 : R ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at hzR
    subst hzR
    simp at hzo
  have hU : ∀ x ∈ R, ∀ y ∈ R, orderOf x = 2 → orderOf y = 2 → x = y := fun x hx y hy hx2 hy2 =>
    (hK.2.2.1 x (d.R_le_K hx) hx2).trans (hK.2.2.1 y (d.R_le_K hy) hy2).symm
  have hnot : ¬ S ≤ Subgroup.normalizer (R : Set G) := by
    intro hSN
    have h : S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G) = S ⊓ conjSubgroup g K :=
      d.S₁_eq_S₀_iff.mpr hSN
    have hc : Nat.card R = 2 ^ (Nat.card K).factorization 2 := by
      rw [← d.card_S₁ hR1, h, d.natCard_S₀, card_conjSubgroup]
    have hRK : IsSylow2Of R K := isSylow2Of_of_card d.R_le_K d.R_two hc.ge
    have hS₀ : IsSylow2Of (S ⊓ conjSubgroup g K) (conjSubgroup g K) :=
      isSylow2Of_of_card inf_le_right (d.S_two.to_le inf_le_left) d.natCard_S₀.ge
    have hcomm : ∀ x ∈ R, ∀ y ∈ S ⊓ conjSubgroup g K, x * y = y * x := by
      intro x hx y hy
      have hy' : y ∈ S ⊓ conjSubgroup g K ⊓ Subgroup.normalizer (R : Set G) := by
        rw [h]
        exact hy
      exact (d.S₁_commute y hy' x hx).symm
    have hall := hCSM g hg R (S ⊓ conjSubgroup g K) hRK hS₀ hcomm
    apply hKz'
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hall a ha (g * z * g⁻¹) (mem_conjSubgroup_of_mem hzK)
  have hlt := d.S₁_lt_iff.mpr hnot
  have hab := d.commute_of_S₁_lt hR1 hlt
  have hcyc : IsCyclic R := by
    have hrank : NoCommutingDistinctInvolutions R := by
      intro a b hab'
      apply Subtype.ext
      have := hU (a.1 : G) a.1.2 (b.1 : G) b.1.2
        (by rw [Subgroup.orderOf_coe]; exact a.2) (by rw [Subgroup.orderOf_coe]; exact b.2)
      exact Subtype.ext this
    have hcomm : ∀ x y : R, x * y = y * x := fun x y => Subtype.ext (hab x x.2 y y.2)
    let _ : CommGroup R := { (inferInstance : Group R) with mul_comm := hcomm }
    exact rank_one_abelian_two_group_cyclic R d.R_two hrank
  exact ⟨R, S, hzR, d, hcyc, hlt, d.five_of_unique_involution hR1 hU hlt⟩

omit [Finite G] in
theorem UniqueInvolutionNormal.conj_eq_of_commuting (hK : UniqueInvolutionNormal K z)
    (hT : SingleMemberControl K) (hCSM : CommutingSylowForcesCommuting K) (Q : Sylow 2 K) {g : G}
    (h : ∀ x ∈ conjSubgroup g ((Q : Subgroup K).map K.subtype),
      ∀ y ∈ (Q : Subgroup K).map K.subtype, x * y = y * x) : conjSubgroup g K = K := by
  by_contra hne
  have hg : g ∉ Subgroup.normalizer (K : Set G) := fun hg => hne (conjSubgroup_eq_self_iff.mpr hg)
  have hall := hCSM g hg _ _ (isSylow2Of_map_subtype Q)
    ((isSylow2Of_map_subtype Q).conj g) (fun x hx y hy => (h y hy x hx).symm)
  have hz1 : z ≠ 1 := by
    rintro rfl
    simpa using hK.1
  apply hne
  refine hT z hz1 (isPGroup_two_zpowers_of_orderOf_two hK.1) _
    (conjSubgroup_mem_conjugateSet g (self_mem_conjugateSet K)) _ (self_mem_conjugateSet K) ?_
    hK.2.2.2.1
  intro b hb
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (hall z hK.2.1 b hb).symm

omit [Finite G] in
theorem singleMemberControl_of_controlC (hC : ControlC K) (hE : ∀ X Y, ¬ commutingAdj K X Y) :
    SingleMemberControl K := by
  intro t ht1 ht2 A hA B hB hAt hBt
  exact (eq_of_mem_deltaComp_of_edgeless hE (hC t ht1 ht2 A hA B hB hAt hBt)).symm

theorem uniqueInvolutionNormal_of_quaternion_sylow (hz : orderOf z = 2) (hzK : z ∈ K)
    (hKC : K ≤ Subgroup.centralizer ({z} : Set G))
    (hKn : (K.subgroupOf (Subgroup.centralizer ({z} : Set G))).Normal) (T : Sylow 2 K)
    (hT : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((T : Subgroup K) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    UniqueInvolutionNormal K z :=
  ⟨hz, hzK, (unique_involution_of_quaternion_sylow hzK hz hKC T hT).1, hKC, hKn⟩

theorem twoSubgroupsFourGenerated_of_tight_csm (hK : UniqueInvolutionNormal K z)
    (hT : SingleMemberControl K) (hCSM : CommutingSylowForcesCommuting K) (Q : Sylow 2 K)
    (hQ : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((Q : Subgroup K) ≃* QuaternionGroup (2 ^ (r - 2))))
    (hz : z ∈ (Q : Subgroup K).map K.subtype) (S : Sylow 2 G)
    (hQS : (Q : Subgroup K).map K.subtype ≤ S) (hE2 : CentralizerTwoRankOne K)
    (hE3 : NormalizerQuotientTwoGenerated K) : TwoSubgroupsFourGenerated G :=
  twoSubgroupsFourGenerated_of_tight_quaternion Q hQ hz hK.1 hK.2.2.2.1 hK.2.2.2.2 S hQS
    (fun _ h => hK.conj_eq_of_commuting hT hCSM Q h) hE2 hE3

end CFSG.ClassicalInvolution
