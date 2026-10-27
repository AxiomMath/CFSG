module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank632Defs
public import CFSG.Blueprint.Catalog
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank632NearCyclic
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank632SzSylow
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank632Factors
import CFSG.RankThree.PartTwo.KFacts.KP7Suzuki

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Blueprint Subgroup

private theorem lemmaA_pow_eq_one_of_mem_closure {G : Type*} [Group G] {a c : G} {n : ℕ}
    (ha : a ^ n = 1) (hc : c ^ n = 1) (hac : a * c = c * a) {y : G}
    (hy : y ∈ closure ({a, c} : Set G)) : y ^ n = 1 := by
  have hcomm : IsMulCommutative (closure ({a, c} : Set G)) := by
    apply isMulCommutative_closure
    intro u hu v hv _
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact Commute.refl _
    · exact hac
    · exact hac.symm
    · exact Commute.refl _
  induction hy using Subgroup.closure_induction with
  | mem u hu =>
    rcases hu with rfl | rfl
    · exact ha
    · exact hc
  | one => exact one_pow n
  | mul u v hu hv ihu ihv =>
    have huv : Commute u v := congrArg Subtype.val (hcomm.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
    rw [huv.mul_pow, ihu, ihv, one_mul]
  | inv u hu ihu => rw [inv_pow, ihu, inv_one]

private theorem lemmaA_mem_normalizer_of_map_conj_eq {G : Type*} [Group G] {H : Subgroup G}
    {y : G} (h : H.map (MulAut.conj y).toMonoidHom = H) : y ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    rw [← h]
    exact ⟨u, hu, rfl⟩
  · intro hu
    rw [← h] at hu
    obtain ⟨v, hv, hvu⟩ := hu
    have hvu' : v = u := by
      simpa [MulAut.conj_apply] using hvu
    rwa [← hvu']

private theorem lemmaA_false_of_embedding {Y : Type} [Group Y]
    [Finite Y] {N : Subgroup Y} {x : Y}
    (hnear : ∀ Q : Subgroup Y, Q ≤ N → IsPGroup 2 Q → (∀ q ∈ Q, x * q = q * x) →
      NearCyclic Q)
    {H : Type} [Group H] [Finite H] {f : ℕ} (hH : SuzukiModel H 2 f) (δ : H →* Y)
    (hδ : Function.Injective δ) (hδN : ∀ s, δ s ∈ N) (hδx : ∀ s, x * δ s = δ s * x) : False := by
  obtain ⟨Q₀⟩ := (Sylow.nonempty : Nonempty (Sylow 2 H))
  have hQ := hnear ((Q₀ : Subgroup H).map δ)
    (by rintro _ ⟨s, -, rfl⟩; exact hδN s)
    (Q₀.isPGroup'.map δ)
    (by rintro _ ⟨s, -, rfl⟩; exact hδx s)
  exact SuzukiModel.not_nearCyclic_sylow hH Q₀
    (NearCyclic.of_mulEquiv ((Q₀ : Subgroup H).equivMapOfInjective δ hδ) hQ)

private theorem lemmaA_mem_normalizer {Y : Type} [Group Y]
    [Finite Y] {N : Subgroup Y} [N.Normal] {r : ℕ} {S : Fin r → Subgroup Y}
    (hS : SimpleFactorData N S) (hSz : ∀ i, ∃ f, SuzukiModel (S i) 2 f) {x : Y}
    (hx : x ^ 3 = 1)
    (hnear : ∀ Q : Subgroup Y, Q ≤ N → IsPGroup 2 Q → (∀ q ∈ Q, x * q = q * x) →
      NearCyclic Q)
    (i : Fin r) : x ∈ normalizer ((S i : Subgroup Y) : Set Y) := by
  by_contra hxi
  obtain ⟨f, hf⟩ := hSz i
  obtain ⟨δ, hδ, hδN, hδx⟩ :=
    hS.exists_diagonal hx (i := i) fun h => hxi (lemmaA_mem_normalizer_of_map_conj_eq h)
  exact lemmaA_false_of_embedding hnear hf δ hδ hδN hδx

private theorem lemmaA_mem_of_conj_eq {Y : Type*} [Group Y] {K : Subgroup Y} (hK : K.Normal)
    {x z g : Y} (hxK : x ∈ K) (hz : z ^ 3 = 1) (hxz : x * z = z * x) {b : ℕ} (hb : ¬ 3 ∣ b)
    (hg : g * x * g⁻¹ = x * z ^ b) : z ∈ K := by
  have h1 : x * (g * x * g⁻¹)⁻¹ ∈ K := K.mul_mem hxK (K.inv_mem (hK.conj_mem x hxK g))
  have hcomm : Commute x (z ^ b) := Commute.pow_right hxz b
  have h2 : x * (g * x * g⁻¹)⁻¹ = (z ^ b)⁻¹ := by
    rw [hg, mul_inv_rev, ← mul_assoc, hcomm.inv_right.eq, mul_inv_cancel_right]
  rw [h2] at h1
  have h3 : (z ^ b) ^ b ∈ K := K.pow_mem (inv_inv (z ^ b) ▸ K.inv_mem h1) b
  rw [← pow_mul, pow_eq_pow_mod _ hz] at h3
  have hbb : b * b % 3 = 1 := by
    have : b % 3 = 1 ∨ b % 3 = 2 := by omega
    rcases this with h | h <;> simp [Nat.mul_mod, h]
  rwa [hbb, pow_one] at h3

private theorem lemmaA_exists_involution {Y : Type} [Group Y]
    {H : Subgroup Y} {f : ℕ} (hH : SuzukiModel H 2 f) {x z : Y} (hx : x ^ 3 = 1)
    (hz : z ^ 3 = 1) (hxz : x * z = z * x) (hxH : x ∈ normalizer (H : Set Y))
    (hzH : z ∈ normalizer (H : Set Y)) :
    ∃ t ∈ H, orderOf t = 2 ∧ x * t = t * x ∧ z * t = t * z := by
  obtain ⟨t, ht, hfix⟩ :=
    CFSG.RankThree.PartTwo.KFacts.KP7.exists_involution_fixed_of_suzukiModel hH
      H.normalizerMonoidHom (E := (closure ({x, z} : Set Y)).subgroupOf (normalizer (H : Set Y)))
      fun y hy => Subtype.ext (by
        simpa using lemmaA_pow_eq_one_of_mem_closure hx hz hxz (mem_subgroupOf.1 hy))
  have hfx := congrArg Subtype.val
    (hfix ⟨x, hxH⟩ (mem_subgroupOf.2 (subset_closure (by simp))))
  have hfz := congrArg Subtype.val
    (hfix ⟨z, hzH⟩ (mem_subgroupOf.2 (subset_closure (by simp))))
  simp only [normalizerMonoidHom_apply_apply_coe] at hfx hfz
  exact ⟨t, t.2, by rw [Subgroup.orderOf_coe, ht], mul_inv_eq_iff_eq_mul.1 hfx,
    mul_inv_eq_iff_eq_mul.1 hfz⟩

private theorem lemmaA_false_of_two_factors {Y : Type} [Group Y] [Finite Y] {N : Subgroup Y}
    {r : ℕ} {S : Fin r → Subgroup Y} (hS : SimpleFactorData N S) {x z : Y}
    (hcyc : ∀ Q : Subgroup Y, Q ≤ N → IsPGroup 2 Q → (∀ q ∈ Q, x * q = q * x) →
      (∀ q ∈ Q, z * q = q * z) → IsCyclic Q)
    {i j : Fin r} (hij : i ≠ j) {t₀ t₁ : Y} (ht₀ : t₀ ∈ S i) (ht₁ : t₁ ∈ S j)
    (ho₀ : orderOf t₀ = 2) (ho₁ : orderOf t₁ = 2) (hx₀ : x * t₀ = t₀ * x)
    (hz₀ : z * t₀ = t₀ * z) (hx₁ : x * t₁ = t₁ * x) (hz₁ : z * t₁ = t₁ * z) : False := by
  set Q := closure ({t₀, t₁} : Set Y)
  have hQN : Q ≤ N := closure_le _ |>.2 (by
    rintro _ (rfl | rfl)
    · exact hS.le i ht₀
    · exact hS.le j ht₁)
  have hQp : IsPGroup 2 Q := fun q => ⟨1, Subtype.ext (by
    simpa using lemmaA_pow_eq_one_of_mem_closure (ho₀ ▸ pow_orderOf_eq_one t₀)
      (ho₁ ▸ pow_orderOf_eq_one t₁) (hS.commute hij ht₀ ht₁) q.2)⟩
  have hcen : ∀ w : Y, w * t₀ = t₀ * w → w * t₁ = t₁ * w → ∀ q ∈ Q, w * q = q * w := by
    intro w hw₀ hw₁ q hq
    have hle : Q ≤ centralizer ({w} : Set Y) := closure_le _ |>.2 (by
      rintro _ (rfl | rfl)
      · exact mem_centralizer_singleton_iff.2 hw₀.symm
      · exact mem_centralizer_singleton_iff.2 hw₁.symm)
    exact (mem_centralizer_singleton_iff.1 (hle hq)).symm
  have : IsCyclic Q := hcyc Q hQN hQp (hcen x hx₀ hx₁) (hcen z hz₀ hz₁)
  have ha : t₀ ∈ Q := subset_closure (by simp)
  have hb : t₁ ∈ Q := subset_closure (by simp)
  have heq : zpowers (⟨t₀, ha⟩ : Q) = zpowers ⟨t₁, hb⟩ := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers,
      Subgroup.orderOf_mk, Subgroup.orderOf_mk, ho₀, ho₁]
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (heq ▸ mem_zpowers (⟨t₁, hb⟩ : Q))
  have hk' : t₀ ^ k = t₁ := by simpa using congrArg Subtype.val hk
  have hmem : t₁ ∈ S i ⊓ S j := ⟨hk' ▸ zpow_mem ht₀ k, ht₁⟩
  rw [hS.inf_eq_bot hij, mem_bot] at hmem
  rw [hmem, orderOf_one] at ho₁
  exact absurd ho₁ (by norm_num)

private theorem lemmaA_eq_of_fin_one {Y : Type*} [Group Y] {N : Subgroup Y}
    {S : Fin 1 → Subgroup Y} (hS : SimpleFactorData N S) : N = S 0 := by
  obtain ⟨e, he⟩ := hS.prod
  refine le_antisymm (fun n hn => ?_) (hS.le 0)
  have h := he 0 (e.symm ⟨n, hn⟩) fun j hj => absurd (Subsingleton.elim j 0) hj
  rw [MulEquiv.apply_symm_apply] at h
  change n = ((e.symm ⟨n, hn⟩ 0 : S 0) : Y) at h
  rw [h]
  exact (e.symm ⟨n, hn⟩ 0).2

private theorem lemmaA_exists_normal_index_three {Y C : Type*} [Group Y] [Group C] [Finite C]
    [IsCyclic C] (φ : Y →* C) {x : Y} (hx : orderOf (φ x) = 3) :
    ∃ K : Subgroup Y, K.Normal ∧ K.index = 3 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := φ.range)
  have hord : orderOf g = Nat.card φ.range := orderOf_eq_card_of_forall_mem_zpowers hg
  have h3 : 3 ∣ Nat.card φ.range := by
    rw [← hx, ← Subgroup.orderOf_mk (φ x) (MonoidHom.mem_range.2 ⟨x, rfl⟩)]
    exact orderOf_dvd_natCard _
  refine ⟨(zpowers (g ^ 3)).comap φ.rangeRestrict, inferInstance, ?_⟩
  rw [index_comap_of_surjective _ φ.rangeRestrict_surjective]
  have hcard : Nat.card (zpowers (g ^ 3)) = Nat.card φ.range / 3 := by
    rw [Nat.card_zpowers, orderOf_pow_of_dvd three_ne_zero (hord ▸ h3), hord]
  have h := (zpowers (g ^ 3)).card_mul_index
  rw [hcard] at h
  obtain ⟨m, hm⟩ := h3
  have hpos : 0 < Nat.card φ.range := Nat.card_pos
  rw [hm, Nat.mul_div_cancel_left m (by norm_num)] at h
  exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < m) (h.trans (mul_comm 3 m))

private theorem lemmaA_false_of_simple {Y : Type} [Group Y]
    [Finite Y] {H : Subgroup Y} [H.Normal] {f : ℕ} (hf : SuzukiModel H 2 f) {x : Y}
    (hx : x ^ 3 = 1)
    (hnear : ∀ Q : Subgroup Y, Q ≤ H → IsPGroup 2 Q → (∀ q ∈ Q, x * q = q * x) →
      NearCyclic Q)
    (hO3 : ∀ K : Subgroup Y, K.Normal → K.index ≠ 3) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (MulAut H) := CFSG.RankThree.PartTwo.KFacts.KP7.finite_mulAut H
  have hα1 : (MulAut.conjNormal x : MulAut H) ≠ 1 := by
    intro h1
    refine lemmaA_false_of_embedding hnear hf H.subtype H.subtype_injective (fun s => s.2)
      fun s => ?_
    have hs := congrArg Subtype.val (DFunLike.congr_fun h1 s)
    rw [MulAut.conjNormal_apply] at hs
    exact mul_inv_eq_iff_eq_mul.1 hs
  have hα3 : (MulAut.conjNormal x : MulAut H) ^ 3 = 1 := by rw [← map_pow, hx, map_one]
  have hαI : (MulAut.conjNormal x : MulAut H) ∉
      CFSG.ComponentClassification.OuterAutomorphisms.inner H := by
    intro hαI
    have hp : IsPGroup 3 (zpowers (MulAut.conjNormal x : MulAut H)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hα3 hα1, pow_one])
    have hmem := mem_inf.2 ⟨mem_zpowers _, hαI⟩
    rw [CFSG.RankThree.PartTwo.KFacts.KP7.inf_inner_eq_bot hf hp, mem_bot] at hmem
    exact hα1 hmem
  let φ : Y →* CFSG.ComponentClassification.OuterAutomorphisms.Outer H :=
    (QuotientGroup.mk' _).comp MulAut.conjNormal
  have hφx : φ x ≠ 1 := by
    simpa [φ, QuotientGroup.eq_one_iff] using hαI
  have hφ3 : orderOf (φ x) = 3 := orderOf_eq_prime (by rw [← map_pow, hx, map_one]) hφx
  have : IsCyclic (CFSG.ComponentClassification.OuterAutomorphisms.Outer H) :=
    (CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0} H 2 f hf).1.1
  obtain ⟨K, hK, hKi⟩ := lemmaA_exists_normal_index_three φ hφ3
  exact hO3 K hK hKi

theorem false_of_normal_suzuki_product {Y : Type} [Group Y]
    [Finite Y] {N : Subgroup Y} [N.Normal] (hN3 : ¬ 3 ∣ Nat.card N) {r : ℕ} (hr : 1 ≤ r)
    {S : Fin r → Subgroup Y} (hS : SimpleFactorData N S)
    (hSz : ∀ i, ∃ f, SuzukiModel (S i) 2 f) {x z g : Y} (hx : x ^ 3 = 1) (hz : z ^ 3 = 1)
    (hxz : x * z = z * x) {b : ℕ} (hb : ¬ 3 ∣ b) (hg : g * x * g⁻¹ = x * z ^ b)
    (hcyc : ∀ Q : Subgroup Y, Q ≤ N → IsPGroup 2 Q → (∀ q ∈ Q, x * q = q * x) →
      (∀ q ∈ Q, z * q = q * z) → IsCyclic Q)
    (hnear : ∀ Q : Subgroup Y, Q ≤ N → IsPGroup 2 Q → (∀ q ∈ Q, x * q = q * x) →
      NearCyclic Q)
    (hO3 : ∀ K : Subgroup Y, K.Normal → K.index ≠ 3) : False := by
  have hxN := lemmaA_mem_normalizer hS hSz hx hnear
  have hzN : ∀ i, z ∈ normalizer ((S i : Subgroup Y) : Set Y) :=
    mem_iInf.1 (lemmaA_mem_of_conj_eq hS.normal_iInf_normalizer (mem_iInf.2 hxN) hz hxz hb hg)
  have ht : ∀ i, ∃ t ∈ S i, orderOf t = 2 ∧ x * t = t * x ∧ z * t = t * z := fun i => by
    obtain ⟨f, hf⟩ := hSz i
    exact lemmaA_exists_involution hf hx hz hxz (hxN i) (hzN i)
  obtain rfl : r = 1 := by
    by_contra hr1
    obtain ⟨t₀, ht₀, ho₀, hx₀, hz₀⟩ := ht ⟨0, by omega⟩
    obtain ⟨t₁, ht₁, ho₁, hx₁, hz₁⟩ := ht ⟨1, by omega⟩
    exact lemmaA_false_of_two_factors hS hcyc (by simp [Fin.ext_iff]) ht₀ ht₁ ho₀ ho₁ hx₀ hz₀
      hx₁ hz₁
  obtain rfl := lemmaA_eq_of_fin_one hS
  obtain ⟨f, hf⟩ := hSz 0
  exact lemmaA_false_of_simple hf hx hnear hO3

end CFSG.LocalAnalysis.RankThreeTheoremC
