module

public import CFSG.GH74.Uniqueness.SU.SU4Defs
public import CFSG.LocalAnalysis.RankTwoShapes.AlperinFusion
public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneInvolutions

public section

namespace CFSG.GH74.Uniqueness.SU.SU10

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.RankTwoShapes

variable {G : Type} [Group G]

section Finite

variable [Finite G]

theorem two_le_pRank_of_commuting_involutions {Q : Subgroup G} {a b : G} (ha : a ∈ Q) (hb : b ∈ Q)
    (ha2 : orderOf a = 2) (hb2 : orderOf b = 2) (hne : a ≠ b) (hab : a * b = b * a) :
    2 ≤ Open.pRank 2 Q := by
  have haa : a ^ 2 = 1 := ha2 ▸ pow_orderOf_eq_one a
  have hbb : b ^ 2 = 1 := hb2 ▸ pow_orderOf_eq_one b
  have hcomm : ∀ x ∈ zpowers a, ∀ y ∈ zpowers b, x * y = y * x := by
    rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩
    have hc : Commute a b := hab
    exact (hc.zpow_zpow i j).eq
  have hel : Open.IsElemAbelian 2 (zpowers a ⊔ zpowers b) :=
    SU1.IsElemAbelian.sup (SU1.isElemAbelian_zpowers haa) (SU1.isElemAbelian_zpowers hbb) hcomm
  have hEQ : zpowers a ⊔ zpowers b ≤ Q :=
    sup_le (Subgroup.zpowers_le.2 ha) (Subgroup.zpowers_le.2 hb)
  obtain ⟨k, hk⟩ := SU1.IsElemAbelian.exists_card Nat.prime_two hel
  have hbE : b ∈ zpowers a ⊔ zpowers b := Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have hk1 : k ≤ 1 := by omega
    have hcardA : Nat.card (zpowers a) = 2 := by rw [Nat.card_zpowers, ha2]
    have hle : zpowers a ≤ zpowers a ⊔ zpowers b := le_sup_left
    have hcard_le : Nat.card (zpowers a ⊔ zpowers b : Subgroup G) ≤ 2 := by
      rw [hk]
      calc 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
        _ = 2 := by norm_num
    have heq : zpowers a = zpowers a ⊔ zpowers b :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcardA]; exact hcard_le)
    have hbA : b ∈ zpowers a := by rw [heq]; exact hbE
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hbA
    have hj' : a ^ (j % 2) = a ^ j := by
      simpa [ha2] using zpow_mod_orderOf a j
    rcases Int.emod_two_eq_zero_or_one j with h0 | h1
    · rw [h0, zpow_zero, hj] at hj'
      rw [← hj', orderOf_one] at hb2
      exact absurd hb2 (by norm_num)
    · rw [h1, zpow_one, hj] at hj'
      exact hne hj'
  exact le_trans hk2 (SU1.le_pRank (by norm_num) hEQ hel hk)

theorem eq_of_orderOf_two_of_pRank_le_one {Q : Subgroup G} (hQ : IsPGroup 2 Q)
    (hr : Open.pRank 2 Q ≤ 1) {a b : G} (ha : a ∈ Q) (hb : b ∈ Q) (ha2 : orderOf a = 2)
    (hb2 : orderOf b = 2) : a = b := by
  have : Nontrivial ↥Q := ⟨⟨⟨a, ha⟩, 1, fun h => by
    have := congrArg Subtype.val h
    simp only [OneMemClass.coe_one] at this
    rw [this, orderOf_one] at ha2
    exact absurd ha2 (by norm_num)⟩⟩
  have hnc : CFSG.DisconnectedInvolutionGraph.Helpers.NoCommutingDistinctInvolutions ↥Q := by
    intro f s hcomm
    by_contra hne
    have hf : orderOf (f : Q) = 2 := f.property
    have hs : orderOf (s : Q) = 2 := s.property
    have h2 := two_le_pRank_of_commuting_involutions (Q := Q) (a := ((f : Q) : G))
      (b := ((s : Q) : G)) (f : Q).2 (s : Q).2 ((Subgroup.orderOf_coe _).trans hf)
      ((Subgroup.orderOf_coe _).trans hs)
      (fun h => hne (Subtype.ext (Subtype.ext h))) (congrArg Subtype.val hcomm)
    omega
  obtain ⟨c, -, hc⟩ := CFSG.DisconnectedInvolutionGraph.Helpers.rank_one_two_group_unique_involution
    hQ hnc
  have h1 := hc ⟨⟨a, ha⟩, (Subgroup.orderOf_coe (⟨a, ha⟩ : Q)).symm ▸ ha2⟩
  have h2 := hc ⟨⟨b, hb⟩, (Subgroup.orderOf_coe (⟨b, hb⟩ : Q)).symm ▸ hb2⟩
  have := h1.trans h2.symm
  exact congrArg (fun t : CFSG.DisconnectedInvolutionGraph.Helpers.Involution ↥Q => ((t : Q) : G))
    this

theorem le_gammaTwo_self {S : Subgroup G} (hr : 2 ≤ Open.pRank 2 S) : S ≤ gammaTwo S := by
  refine le_trans (Subgroup.le_normalizer (H := S)) ?_
  unfold gammaTwo Open.properTwoGenCoreGamma
  exact le_iSup_of_le S (le_iSup_of_le le_rfl (le_iSup_of_le hr le_rfl))

theorem normalizer_le_gammaTwo {S Q : Subgroup G} (hQS : Q ≤ S) (hr : 2 ≤ Open.pRank 2 Q) :
    normalizer (Q : Set G) ≤ gammaTwo S := by
  unfold gammaTwo Open.properTwoGenCoreGamma
  exact le_iSup_of_le Q (le_iSup_of_le hQS (le_iSup_of_le hr le_rfl))

theorem exists_conj_mem_of_le (S : Sylow 2 G) {M : Subgroup G} (hSM : (S : Subgroup G) ≤ M)
    {u : G} (hu : orderOf u = 2) (huM : u ∈ M) :
    ∃ m ∈ M, m⁻¹ * u * m ∈ (S : Subgroup G) := by
  have hu' : orderOf (⟨u, huM⟩ : M) = 2 := (Subgroup.orderOf_coe (⟨u, huM⟩ : M)).symm.trans hu
  have hp : IsPGroup 2 (zpowers (⟨u, huM⟩ : M)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hu']
    simp
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M Q (S.subtype hSM)
  have hmem : MulAut.conj m • (⟨u, huM⟩ : M) ∈ ((m • Q : Sylow 2 M) : Subgroup M) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hQ (Subgroup.mem_zpowers _))
  rw [hm, Sylow.coe_subtype, Subgroup.mem_subgroupOf] at hmem
  refine ⟨(m : G)⁻¹, M.inv_mem m.2, ?_⟩
  simpa [MulAut.smul_def, mul_assoc] using hmem

theorem controls_involution_fusion_of_mem (S : Sylow 2 G) {M : Subgroup G}
    (hM : gammaTwo (S : Subgroup G) ≤ M) {x g : G} (hx : x ∈ (S : Subgroup G)) (hx2 : orderOf x = 2)
    (hg : g⁻¹ * x * g ∈ (S : Subgroup G)) : ∃ m ∈ M, g⁻¹ * x * g = m⁻¹ * x * m := by
  have hP : zpowers x ≤ (S : Subgroup G) := Subgroup.zpowers_le.2 hx
  have hPg : (zpowers x).map (MulAut.conj g⁻¹).toMonoidHom ≤ (S : Subgroup G) := by
    rw [MonoidHom.map_zpowers]
    exact Subgroup.zpowers_le.2 (by simpa using hg)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc, hcg⟩ := alperin_centric_radical_fusion S hP hPg
  rw [← hcg x (Subgroup.mem_zpowers x)]
  clear hcg hPg hg
  induction hc with
  | one => exact ⟨1, M.one_mem, by group⟩
  | @step c n Q _ hQ hPQ hn ih =>
    obtain ⟨m, hmM, hm⟩ := ih
    have hyQ : c⁻¹ * x * c ∈ Q := by
      apply hPQ
      refine ⟨x, Subgroup.mem_zpowers x, ?_⟩
      simp
    by_cases hr : 2 ≤ Open.pRank 2 Q
    · have hnM : n ∈ M := hM (normalizer_le_gammaTwo hQ.1 hr hn)
      refine ⟨m * n, M.mul_mem hmM hnM, ?_⟩
      calc (c * n)⁻¹ * x * (c * n) = n⁻¹ * (c⁻¹ * x * c) * n := by group
        _ = n⁻¹ * (m⁻¹ * x * m) * n := by rw [hm]
        _ = (m * n)⁻¹ * x * (m * n) := by group
    · refine ⟨m, hmM, ?_⟩
      have hQp : IsPGroup 2 Q := (S.isPGroup').to_le hQ.1
      have hyn : n⁻¹ * (c⁻¹ * x * c) * n ∈ Q :=
        (Subgroup.mem_normalizer_iff''.mp hn _).mp hyQ
      have hy2 : orderOf (c⁻¹ * x * c) = 2 := by
        simpa [hx2] using (MulAut.conj c⁻¹).orderOf_eq x
      have hyn2 : orderOf (n⁻¹ * (c⁻¹ * x * c) * n) = 2 := by
        simpa [hy2] using (MulAut.conj n⁻¹).orderOf_eq (c⁻¹ * x * c)
      have heq := eq_of_orderOf_two_of_pRank_le_one hQp (by omega) hyn hyQ hyn2 hy2
      calc (c * n)⁻¹ * x * (c * n) = n⁻¹ * (c⁻¹ * x * c) * n := by group
        _ = c⁻¹ * x * c := heq
        _ = m⁻¹ * x * m := hm

theorem controls_involution_fusion (S : Sylow 2 G) {M : Subgroup G}
    (hrank : 2 ≤ Open.pRank 2 (S : Subgroup G)) (hM : gammaTwo (S : Subgroup G) ≤ M) {u g : G}
    (hu : orderOf u = 2) (huM : u ∈ M) (hug : g⁻¹ * u * g ∈ M) :
    ∃ m ∈ M, m⁻¹ * u * m = g⁻¹ * u * g := by
  have hSM : (S : Subgroup G) ≤ M := (le_gammaTwo_self hrank).trans hM
  have hv2 : orderOf (g⁻¹ * u * g) = 2 := by
    simpa [hu] using (MulAut.conj g⁻¹).orderOf_eq u
  obtain ⟨m₁, hm₁, hu₁⟩ := exists_conj_mem_of_le S hSM hu huM
  obtain ⟨m₂, hm₂, hv₁⟩ := exists_conj_mem_of_le S hSM hv2 hug
  have hu₁2 : orderOf (m₁⁻¹ * u * m₁) = 2 := by
    simpa [hu] using (MulAut.conj m₁⁻¹).orderOf_eq u
  have hgS : (m₁⁻¹ * g * m₂)⁻¹ * (m₁⁻¹ * u * m₁) * (m₁⁻¹ * g * m₂) ∈ (S : Subgroup G) := by
    have : (m₁⁻¹ * g * m₂)⁻¹ * (m₁⁻¹ * u * m₁) * (m₁⁻¹ * g * m₂) = m₂⁻¹ * (g⁻¹ * u * g) * m₂ := by
      group
    rw [this]
    exact hv₁
  obtain ⟨m₃, hm₃, hm₃eq⟩ := controls_involution_fusion_of_mem S hM hu₁ hu₁2 hgS
  refine ⟨m₁ * m₃ * m₂⁻¹, M.mul_mem (M.mul_mem hm₁ hm₃) (M.inv_mem hm₂), ?_⟩
  have h1 : (m₁⁻¹ * g * m₂)⁻¹ * (m₁⁻¹ * u * m₁) * (m₁⁻¹ * g * m₂) = m₂⁻¹ * (g⁻¹ * u * g) * m₂ := by
    group
  have h2 : m₃⁻¹ * (m₁⁻¹ * u * m₁) * m₃ = m₂⁻¹ * (g⁻¹ * u * g) * m₂ := by
    rw [← h1]
    exact hm₃eq.symm
  calc (m₁ * m₃ * m₂⁻¹)⁻¹ * u * (m₁ * m₃ * m₂⁻¹)
      = m₂ * (m₃⁻¹ * (m₁⁻¹ * u * m₁) * m₃) * m₂⁻¹ := by group
    _ = m₂ * (m₂⁻¹ * (g⁻¹ * u * g) * m₂) * m₂⁻¹ := by rw [h2]
    _ = g⁻¹ * u * g := by group

end Finite

end CFSG.GH74.Uniqueness.SU.SU10
