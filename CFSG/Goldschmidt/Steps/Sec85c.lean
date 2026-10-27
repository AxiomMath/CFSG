module

public import CFSG.Goldschmidt.StatementsG3
import CFSG.Goldschmidt.Steps.Sec8Basic
import CFSG.Goldschmidt.Steps.Sec8LemmaA
import CFSG.Goldschmidt.Steps.Sec84b
import CFSG.Goldschmidt.Steps.Sec85a
import CFSG.Goldschmidt.Steps.Sec85b
import CFSG.CharacterTheory.TwoRankLowerBound.AbelianRankOne
import CFSG.Walter.Bender1970.S4.Rank
import CFSG.Walter.Bender1970.S38.JR

public section

namespace CFSG.Goldschmidt.Sec8

open CFSG.Open CFSG.GorensteinWalter

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A : Subgroup G}

theorem mem_normalizer_commutator {K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((⁅K, K⁆ : Subgroup G) : Set G) := by
  rw [← Walter.map_conj_eq_iff_mem_normalizer] at hg ⊢
  rw [Subgroup.map_commutator, hg]

theorem le_qCoreOf_two_of_le_centralizer {H Y : Subgroup G} (hE : componentLayerOf H = ⊥)
    (hYH : Y ≤ H) (hY2 : IsPGroup 2 Y)
    (hYq : ∀ q : ℕ, q.Prime → Y ≤ Subgroup.centralizer (qCoreOf H q : Set G)) :
    Y ≤ qCoreOf H 2 := by
  have hF : generalizedFittingSubgroupOf H = CFSG.fittingSubgroupOf H := by
    unfold generalizedFittingSubgroupOf
    rw [hE, sup_bot_eq]
    rfl
  have hYC : Y ≤ Subgroup.centralizer (generalizedFittingSubgroupOf H : Set G) := by
    rw [Subgroup.le_centralizer_iff, hF, (show CFSG.fittingSubgroupOf H = _ from CFSG.GorensteinWalter.fittingSubgroupOf_eq_iSup_qCoreOf H)]
    exact iSup_le fun q =>
      Subgroup.le_centralizer_iff.mp (hYq _ (Nat.prime_of_mem_primeFactors q.1.2))
  have hYF : Y ≤ CFSG.fittingSubgroupOf H := fun y hy => by
    have h1 := Walter.inf_centralizer_generalizedFitting_le H ⟨hYH hy, hYC hy⟩
    rwa [hF] at h1
  exact Walter.le_qCoreOf_of_le_fittingSubgroupOf Nat.prime_two hYF hY2

omit [Finite G] in
theorem conj_sq_eq_one {g t : G} (ht2 : t ^ 2 = 1) : (g * t * g⁻¹) ^ 2 = 1 := by
  rw [sq] at ht2 ⊢
  calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
    _ = 1 := by rw [ht2]; group

theorem exists_not_isCyclic (h81 : S_G81) (h84 : S_G84) (hset : GoldSetting G S A)
    (h4 : Nat.card A = 4) (hS : ¬ IsMulCommutative (S : Subgroup G)) {a : G} (ha : a ∈ A)
    (ha1 : a ≠ 1) {H : Subgroup G} (hH : H ∈ Walter.benderM a) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ¬ IsCyclic (qCoreOf H p) := by
  by_contra hno
  simp only [not_exists, not_and, not_not] at hno
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE := componentLayerOf_eq_bot h81 hset h4 ha ha1 hH hno
  have hΩ := zpowers_eq_omega1 h81 h84 hset h4 ha ha1 hH
  have ha2 : a ^ 2 = 1 := hset.elem.2 a ha
  set P := qCoreOf H 2 with hPdef
  have hPp : IsPGroup 2 P := qCoreOf_isPGroup H 2
  have hSH : (S : Subgroup G) ≤ H := le_of_mem_benderM hset h4 ha hH
  have hHP : H ≤ Subgroup.normalizer (P : Set G) :=
    le_normalizer_of_isNormalIn (qCoreOf_normal_in H 2)
  have hPS : P ≤ S := by
    have hR : IsPGroup 2 ((S : Subgroup G) ⊔ P : Subgroup G) :=
      IsPGroup.to_sup_of_normal_right' S.isPGroup' hPp (hSH.trans hHP)
    exact le_sup_right.trans (S.is_maximal' hR le_sup_left).le
  have hinv : ∀ t ∈ P, t ^ 2 = 1 → t ≠ 1 → t = a := fun t htP ht2 ht1 =>
    eq_of_mem_omega1 ha1 ha2 hΩ htP ht2 ht1
  obtain ⟨n, hn, hnc⟩ := exists_not_mem_centralizer hset h4
  obtain ⟨hca, -⟩ := conj_conj_eq_mul hset h4 hn hnc ha ha1
  obtain ⟨x, -, hxS, hxa⟩ := exists_conj_normalizer hset h4 (N := ⊤) le_top ha
    (Subgroup.mem_top n⁻¹) (by simpa using conj_mem hn ha)
  have hxa' : x⁻¹ * a * x ≠ a := by
    rw [hxa]
    simpa using hca
  have hxS' : ∀ s ∈ (S : Subgroup G), x * s * x⁻¹ ∈ (S : Subgroup G) := fun s hs =>
    (Subgroup.mem_normalizer_iff.mp hxS s).mp hs
  have hxS'' : ∀ s ∈ (S : Subgroup G), x⁻¹ * s * x ∈ (S : Subgroup G) := fun s hs => by
    simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxS) s).mp hs
  set X := conjSub x P with hXdef
  have hXS : X ≤ S := fun z hz => by
    simpa [mul_assoc] using hxS'' _ (hPS (mem_conjSub.mp hz))
  have hXH : X ≤ H := hXS.trans hSH
  have hSX : (S : Subgroup G) ≤ Subgroup.normalizer (X : Set G) := fun s hs =>
    mem_normalizer_of_conj_le fun z hz => by
      rw [mem_conjSub] at hz ⊢
      have e : x * (s⁻¹ * z * s) * x⁻¹ =
          (x * s * x⁻¹)⁻¹ * (x * z * x⁻¹) * (x * s * x⁻¹)⁻¹⁻¹ := by group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp
        (Subgroup.inv_mem _ (hHP (hSH (hxS' s hs)))) _).mp hz
  have hXP : X ⊓ P = ⊥ := by
    by_contra hne
    obtain ⟨t, ⟨htX, htP⟩, ht1, ht2⟩ := exists_involution (hPp.to_le inf_le_right) hne
    have h1 := hinv _ (mem_conjSub.mp htX) (conj_sq_eq_one ht2) (conj_ne_one ht1)
    rw [hinv t htP ht2 ht1] at h1
    apply hxa'
    calc x⁻¹ * a * x = x⁻¹ * (x * a * x⁻¹) * x := by rw [h1]
      _ = a := by group
  have hXC : X ≤ Subgroup.centralizer (P : Set G) := fun z hz =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => by
      have hc1 : z * y * z⁻¹ * y⁻¹ ∈ P :=
        P.mul_mem ((Subgroup.mem_normalizer_iff.mp (hHP (hXH hz)) y).mp hy) (P.inv_mem hy)
      have hc2 : z * y * z⁻¹ * y⁻¹ ∈ X := by
        have := (Subgroup.mem_normalizer_iff.mp (hSX (hPS hy)) z⁻¹).mp (X.inv_mem hz)
        simpa [mul_assoc] using X.mul_mem hz this
      have h : z * y * z⁻¹ * y⁻¹ ∈ X ⊓ P := ⟨hc2, hc1⟩
      rw [hXP, Subgroup.mem_bot] at h
      calc y * z = (z * y * z⁻¹ * y⁻¹)⁻¹ * (z * y) := by group
        _ = z * y := by rw [h, inv_one, one_mul]
  have hX' : ⁅X, X⁆ ≤ P := by
    refine le_qCoreOf_two_of_le_centralizer hE ((commutator_self_le X).trans hXH)
      (S.isPGroup'.to_le ((commutator_self_le X).trans hXS)) fun q hq => ?_
    by_cases hq2 : q = 2
    · subst hq2
      exact (commutator_self_le X).trans hXC
    · have := hno q hq hq2
      exact commutator_le_centralizer_of_isCyclic
        (hXH.trans (le_normalizer_of_isNormalIn (qCoreOf_normal_in H q)))
  have hXab : ∀ z₁ ∈ X, ∀ z₂ ∈ X, z₁ * z₂ = z₂ * z₁ := fun z₁ h₁ z₂ h₂ => by
    have h : ⁅z₁, z₂⁆ ∈ X ⊓ P := ⟨commutator_self_le X (Subgroup.commutator_mem_commutator h₁ h₂),
      hX' (Subgroup.commutator_mem_commutator h₁ h₂)⟩
    rw [hXP, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
    exact h
  have hPab : ∀ p₁ ∈ P, ∀ p₂ ∈ P, p₁ * p₂ = p₂ * p₁ := fun p₁ h₁ p₂ h₂ => by
    have h := hXab _ (conj_mem_conjSub (g := x) h₁) _ (conj_mem_conjSub (g := x) h₂)
    calc p₁ * p₂ = x * ((x⁻¹ * p₁ * x) * (x⁻¹ * p₂ * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * p₂ * x) * (x⁻¹ * p₁ * x)) * x⁻¹ := by rw [h]
      _ = p₂ * p₁ := by group
  have hPcyc : IsCyclic P := by
    let _inst : CommGroup P :=
      { (inferInstance : Group P) with mul_comm := fun u v => Subtype.ext (hPab _ u.2 _ v.2) }
    obtain ⟨k, hk⟩ := hPp.exists_card_eq
    refine TwoRankLowerBound.Helpers.abelian_two_group_cyclic_of_unique_involution_of_card_eq_pow
      k P hPp hk fun u v hu hv => Subtype.ext ?_
    have key : ∀ w : P, orderOf w = 2 → (w : G) = a := fun w hw => by
      rw [← Subgroup.orderOf_coe] at hw
      refine hinv _ w.2 (by rw [← hw]; exact pow_orderOf_eq_one _) fun h => ?_
      rw [h, orderOf_one] at hw
      exact absurd hw (by norm_num)
    rw [key u hu, key v hv]
  have hS'P : ⁅(S : Subgroup G), (S : Subgroup G)⁆ ≤ P := by
    refine le_qCoreOf_two_of_le_centralizer hE ((commutator_self_le _).trans hSH)
      (S.isPGroup'.to_le (commutator_self_le _)) fun q hq => ?_
    by_cases hq2 : q = 2
    · subst hq2
      exact commutator_le_centralizer_of_isCyclic (hSH.trans hHP)
    · have := hno q hq hq2
      exact commutator_le_centralizer_of_isCyclic
        (hSH.trans (le_normalizer_of_isNormalIn (qCoreOf_normal_in H q)))
  have hS' : ⁅(S : Subgroup G), (S : Subgroup G)⁆ = ⊥ := by
    by_contra hne
    obtain ⟨t, htS, ht1, ht2⟩ := exists_involution (S.isPGroup'.to_le (commutator_self_le _)) hne
    rw [hinv t (hS'P htS) ht2 ht1] at htS
    have h1 : x⁻¹ * a * x ∈ ⁅(S : Subgroup G), (S : Subgroup G)⁆ := by
      simpa using (Subgroup.mem_normalizer_iff.mp
        (mem_normalizer_commutator (Subgroup.inv_mem _ hxS)) a).mp htS
    have h2 : (x⁻¹ * a * x) ^ 2 = 1 := by simpa using conj_sq_eq_one (g := x⁻¹) ha2
    have h3 : x⁻¹ * a * x ≠ 1 := by simpa using conj_ne_one (n := x⁻¹) ha1
    exact hxa' (hinv _ (hS'P h1) h2 h3)
  refine hS ⟨⟨fun u v => Subtype.ext ?_⟩⟩
  have h := Subgroup.commutator_mem_commutator u.2 v.2
  rw [hS', Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
  exact h

end CFSG.Goldschmidt.Sec8
