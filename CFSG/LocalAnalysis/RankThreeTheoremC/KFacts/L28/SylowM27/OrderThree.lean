module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Walter.Cited.HuppertAlperin

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.L28.SylowM27

open Subgroup CFSG.ABGLocalTools

variable {X : Type*} [Group X] [Finite X]

theorem eq_one_or_eq_or_eq_inv {y z : X} (hz : orderOf z = 3) (hy : y ∈ zpowers z) :
    y = 1 ∨ y = z ∨ y = z⁻¹ := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  rw [← zpow_mod_orderOf, hz]
  have h3 : z ^ 3 = 1 := hz ▸ pow_orderOf_eq_one z
  have hk : k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨ k % ((3 : ℕ) : ℤ) = 2 := by omega
  rcases hk with h | h | h <;> rw [h]
  · exact Or.inl (zpow_zero z)
  · exact Or.inr (Or.inl (zpow_one z))
  · refine Or.inr (Or.inr (eq_inv_of_mul_eq_one_left ?_))
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, ← pow_succ]
    exact h3

theorem conj_eq_self_of_odd {x d : X} (hd : orderOf d = 3) (hx : Odd (orderOf x))
    (hxd : x * d * x⁻¹ ∈ zpowers d) : x * d * x⁻¹ = d := by
  rcases eq_one_or_eq_or_eq_inv hd hxd with h | h | h
  · rw [conj_eq_one_iff] at h
    rw [h, orderOf_one] at hd
    omega
  · exact h
  · have h1 : x * d = d⁻¹ * x := by rw [← h]; group
    have h2 : x * d⁻¹ = d * x := by
      have : x * d⁻¹ * x⁻¹ = d := by
        rw [show x * d⁻¹ * x⁻¹ = (x * d * x⁻¹)⁻¹ by group, h, inv_inv]
      calc x * d⁻¹ = x * d⁻¹ * x⁻¹ * x := by group
        _ = d * x := by rw [this]
    have hc : Commute (x ^ 2) d := by
      show x ^ 2 * d = d * x ^ 2
      rw [pow_two, mul_assoc, h1, ← mul_assoc, h2, mul_assoc]
    obtain ⟨m, hm⟩ := hx
    have hx' : x = (x ^ 2) ^ (m + 1) := by
      rw [← pow_mul, show 2 * (m + 1) = orderOf x + 1 by omega, pow_succ, pow_orderOf_eq_one,
        one_mul]
    have hc' : Commute x d := by
      rw [hx']
      exact hc.pow_left _
    rw [hc'.eq, mul_inv_cancel_right]

theorem exists_conj_eq_inv {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (S : Sylow 3 G) (hS : Nat.card S = 3) {z : G}
    (hzS : z ∈ S) (hz1 : z ≠ 1) : ∃ t : G, t * z * t⁻¹ = z⁻¹ := by
  have hz : orderOf z = 3 := by
    have h : orderOf z ∣ 3 := by
      rw [← hS, ← Subgroup.orderOf_mk z hzS]
      exact orderOf_dvd_natCard _
    rcases (Nat.dvd_prime Nat.prime_three).mp h with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hz1
    · exact h
  have hSz : (S : Subgroup G) = zpowers z :=
    (Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hzS)
      (by rw [Nat.card_zpowers, hz, hS])).symm
  by_contra hcon
  push Not at hcon
  have hNC : Subgroup.normalizer (S : Set G) ≤ Subgroup.centralizer (S : Set G) := by
    intro n hn
    have hnz : n * z * n⁻¹ ∈ zpowers z := hSz ▸ (mem_normalizer_iff.mp hn z).mp hzS
    have hnz' : n * z * n⁻¹ = z := by
      rcases eq_one_or_eq_or_eq_inv hz hnz with h | h | h
      · rw [conj_eq_one_iff] at h
        exact absurd h hz1
      · exact h
      · exact absurd h (hcon n)
    have hc : Commute n z := by
      show n * z = z * n
      calc n * z = n * z * n⁻¹ * n := by group
        _ = z * n := by rw [hnz']
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hs' : s ∈ (S : Subgroup G) := hs
    rw [hSz] at hs'
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hs'
    exact ((hc.zpow_right k).eq).symm
  have hcomp := MonoidHom.ker_transferSylow_isComplement' S hNC
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MonoidHom.transferSylow S hNC).ker with h | h
  · rw [h] at hcomp
    have hStop : (S : Subgroup G) = ⊤ := Subgroup.isComplement'_bot_left.mp hcomp
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have ha : a ∈ zpowers z := hSz ▸ hStop ▸ Subgroup.mem_top a
    have hb : b ∈ zpowers z := hSz ▸ hStop ▸ Subgroup.mem_top b
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hb
    rw [← zpow_add, ← zpow_add, add_comm]
  · rw [h] at hcomp
    have hSbot : (S : Subgroup G) = ⊥ := Subgroup.isComplement'_top_left.mp hcomp
    have hzS' : z ∈ (S : Subgroup G) := hzS
    rw [hSbot, Subgroup.mem_bot] at hzS'
    exact hz1 hzS'

theorem commute_of_card_inf_eq_three {K Q : Subgroup X} [hKn : K.Normal]
    (hQ : Nat.card Q = 3 ^ 3) (hD : Nat.card ↥(Q ⊓ K) = 3) {x y : X} (hx : x ∈ Q)
    (hy : y ∈ Q ⊓ K) : x * y = y * x := by
  by_cases hy1 : y = 1
  · rw [hy1, mul_one, one_mul]
  have hyord : orderOf y = 3 := by
    have h : orderOf y ∣ 3 := by
      rw [← hD, ← Subgroup.orderOf_mk y hy]
      exact orderOf_dvd_natCard _
    rcases (Nat.dvd_prime Nat.prime_three).mp h with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hy1
    · exact h
  have hDy : Q ⊓ K = zpowers y :=
    (Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hy) (by rw [Nat.card_zpowers, hyord, hD])).symm
  have hconj : x * y * x⁻¹ ∈ zpowers y := by
    rw [← hDy]
    exact ⟨Q.mul_mem (Q.mul_mem hx hy.1) (Q.inv_mem hx), hKn.conj_mem y hy.2 x⟩
  have hodd : Odd (orderOf x) := by
    have h : orderOf x ∣ 3 ^ 3 := by
      rw [← hQ, ← Subgroup.orderOf_mk x hx]
      exact orderOf_dvd_natCard _
    exact Odd.of_dvd_nat (by decide) h
  have h := conj_eq_self_of_odd hyord hodd hconj
  calc x * y = x * y * x⁻¹ * x := by group
    _ = y * x := by rw [h]

theorem pow_three_mem {K Q : Subgroup X} [hKn : K.Normal] (hQ : Nat.card Q = 3 ^ 3)
    (hQnab : ¬ IsMulCommutative Q) (hD : Nat.card ↥(Q ⊓ K) = 3) {a : X} (ha : a ∈ Q)
    (ha9 : orderOf a = 9) : a ^ 3 ∈ K := by
  by_contra ha3
  apply hQnab
  set N : Subgroup Q := K.subgroupOf Q with hN
  have hNn : N.Normal := hKn.subgroupOf Q
  have hNcard : Nat.card N = 3 := by
    rw [hN, ← Subgroup.inf_subgroupOf_left,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv, hD]
  have hidx : Nat.card (Q ⧸ N) = 9 := by
    have h := N.card_mul_index
    rw [hNcard, hQ, Subgroup.index_eq_card] at h
    omega
  set f : Q →* Q ⧸ N := QuotientGroup.mk' N with hf
  have hord : orderOf (f ⟨a, ha⟩) = 9 := by
    have hdvd : orderOf (f ⟨a, ha⟩) ∣ 3 ^ 2 := by
      have := orderOf_map_dvd f ⟨a, ha⟩
      rwa [Subgroup.orderOf_mk, ha9] at this
    have hne : f ⟨a, ha⟩ ^ 3 ≠ 1 := by
      intro h
      apply ha3
      rw [← map_pow, hf, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hN,
        Subgroup.mem_subgroupOf] at h
      simpa using h
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    interval_cases k
    · exfalso
      apply hne
      have h1 : orderOf (f ⟨a, ha⟩) = 1 := by simpa using hk'
      rw [orderOf_eq_one_iff.mp h1, one_pow]
    · exfalso
      apply hne
      have := pow_orderOf_eq_one (f ⟨a, ha⟩)
      rwa [hk', pow_one] at this
    · simpa using hk'
  have hcyc : IsCyclic (Q ⧸ N) := isCyclic_of_orderOf_eq_card _ (by rw [hord, hidx])
  refine f.isMulCommutative_of_isCyclic_of_ker_le_center ?_
  rw [hf, QuotientGroup.ker_mk']
  intro y hy
  rw [Subgroup.mem_center_iff]
  intro x
  have hyK : (y : X) ∈ K := Subgroup.mem_subgroupOf.mp hy
  exact Subtype.ext (commute_of_card_inf_eq_three hQ hD x.2 ⟨y.2, hyK⟩)

theorem false_of_card_inf_eq_three {K Q : Subgroup X} [hKn : K.Normal] (hKs : IsSimpleGroup K)
    (hKnab : ∃ a b : K, a * b ≠ b * a) (hsyl : IsSylowOf 3 (Q ⊓ K) K) (hQ : Nat.card Q = 3 ^ 3)
    (hQnab : ¬ IsMulCommutative Q) {a : X} (ha : a ∈ Q) (ha9 : orderOf a = 9)
    (hD : Nat.card ↥(Q ⊓ K) = 3) : False := by
  set z : X := a ^ 3 with hz
  have hzK : z ∈ K := pow_three_mem hQ hQnab hD ha ha9
  have hzD : z ∈ Q ⊓ K := ⟨Q.pow_mem ha 3, hzK⟩
  have hzord : orderOf z = 3 := by
    rw [hz, orderOf_pow' a (by norm_num), ha9]
    norm_num
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hzord; omega
  have hDz : Q ⊓ K = zpowers z :=
    (Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hzD) (by rw [Nat.card_zpowers, hzord, hD])).symm
  obtain ⟨S, hS⟩ := hsyl.exists_sylow_eq_subgroupOf
  have hScard : Nat.card S = 3 := by
    rw [show Nat.card S = Nat.card ((Q ⊓ K).subgroupOf K) by rw [hS],
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, hD]
  have hzS : (⟨z, hzK⟩ : K) ∈ (S : Subgroup K) := by
    rw [hS]
    exact Subgroup.mem_subgroupOf.mpr hzD
  have : IsSimpleGroup K := hKs
  obtain ⟨t', ht'⟩ := exists_conj_eq_inv hKnab S hScard hzS
    (fun h => hz1 (congrArg Subtype.val h))
  set t : X := (t' : X) with ht
  have htK : t ∈ K := t'.2
  have htz : t * z * t⁻¹ = z⁻¹ := congrArg Subtype.val ht'
  set b : X := t * a * t⁻¹ with hb
  have hb3 : b ^ 3 = z⁻¹ := by rw [hb, conj_pow, ← hz, htz]
  have hbord : orderOf b = 9 := by
    have := orderOf_injective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective a
    rw [ha9] at this
    simpa [hb, MulAut.conj_apply] using this
  set R : Subgroup X := Subgroup.centralizer {z} ⊓ (K ⊔ zpowers a) with hR
  have hTR : zpowers a ≤ R := by
    refine zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨?_, Subgroup.mem_sup_right (mem_zpowers a)⟩)
    rw [Subgroup.mem_centralizer_singleton_iff, hz]
    exact (Commute.self_pow a 3).eq
  have hT₂R : zpowers b ≤ R := by
    refine zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
    · rw [Subgroup.mem_centralizer_singleton_iff, show z = (b ^ 3)⁻¹ by rw [hb3, inv_inv]]
      exact ((Commute.self_pow b 3).inv_right).eq
    · rw [hb]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left htK)
        (Subgroup.mem_sup_right (mem_zpowers a))) (Subgroup.mem_sup_left (K.inv_mem htK))
  have hTp : IsPGroup 3 (zpowers a) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, ha9]; norm_num)
  have hT₂p : IsPGroup 3 (zpowers b) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hbord]; norm_num)
  have hAK : zpowers a ⊓ K = Q ⊓ K := by
    have hle : Q ⊓ K ≤ zpowers a ⊓ K := by
      rw [hDz]
      exact le_inf (zpowers_le.mpr (Subgroup.pow_mem _ (mem_zpowers a) 3)) (zpowers_le.mpr hzK)
    exact hsyl.eq_of_le hle inf_le_right hTp.to_inf_left
  have hidx : ¬ 3 ∣ (zpowers a).relIndex R := by
    intro h3
    have h1 := Subgroup.relIndex_mul_relIndex (zpowers a) R (K ⊔ zpowers a) hTR inf_le_right
    rw [relIndex_sup_eq_relIndex_of_normal K (zpowers a),
      ← Subgroup.inf_relIndex_right (zpowers a) K, hAK] at h1
    obtain ⟨-, -, hnd⟩ := isSylowOf_iff.mp hsyl
    exact hnd (h1 ▸ h3.mul_right _)
  have hcard : Nat.card (zpowers b) = Nat.card (zpowers a) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, hbord, ha9]
  obtain ⟨r, hrR, hr⟩ := CFSG.Walter.Huppert.exists_conj_eq hTR hT₂R hTp hT₂p hidx hcard
  have hbmem : b ∈ (zpowers a).map (MulAut.conj r).toMonoidHom := hr ▸ mem_zpowers b
  obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.mp hbmem
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
  have hbr : r * a ^ i * r⁻¹ = b := by simpa [MulAut.conj_apply] using hyb
  have hrR' := Subgroup.mem_inf.mp hrR
  have hrz : Commute r z := Subgroup.mem_centralizer_singleton_iff.mp hrR'.1
  have hpow : (a ^ i) ^ 3 = z ^ i := by
    rw [hz, ← zpow_natCast (a ^ i) 3, ← zpow_natCast a 3, ← zpow_mul, ← zpow_mul, mul_comm]
  have hzi : z ^ i = z⁻¹ := by
    rw [← hb3, ← hbr, conj_pow, hpow, (hrz.zpow_right i).eq, mul_inv_cancel_right]
  have hi1 : (3 : ℤ) ∣ i + 1 := by
    have h : z ^ (i + 1) = 1 := by rw [zpow_add_one, hzi, inv_mul_cancel]
    have := orderOf_dvd_iff_zpow_eq_one.mpr h
    rwa [hzord] at this
  set π : X →* X ⧸ K := QuotientGroup.mk' K with hπ
  have hπt : π t = 1 := (QuotientGroup.eq_one_iff t).mpr htK
  have hπb : π b = π a := by
    rw [hb, map_mul, map_mul, map_inv, hπt, one_mul, inv_one, mul_one]
  have hπr : π r ∈ zpowers (π a) := by
    have hmap : (K ⊔ zpowers a).map π ≤ zpowers (π a) := by
      rw [Subgroup.map_sup, hπ, QuotientGroup.map_mk'_self, bot_sup_eq, MonoidHom.map_zpowers]
    exact hmap (Subgroup.mem_map_of_mem π hrR'.2)
  have hcomm : Commute (π r) (π a) := by
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hπr
    rw [← hj]
    exact (Commute.refl (π a)).zpow_left j
  have hai : π a ^ i = π a := by
    have h1 : π b = π r * π a ^ i * (π r)⁻¹ := by
      rw [← hbr, map_mul, map_mul, map_inv, map_zpow]
    rw [(hcomm.zpow_right i).eq, mul_inv_cancel_right] at h1
    rw [← h1, hπb]
  have haiK : a ^ (i - 1) ∈ K := by
    rw [← QuotientGroup.eq_one_iff (N := K), ← QuotientGroup.mk'_apply, ← hπ, map_zpow,
      zpow_sub_one, hai, mul_inv_cancel]
  have haiD : a ^ (i - 1) ∈ Q ⊓ K := hAK ▸ ⟨zpow_mem (mem_zpowers a) _, haiK⟩
  have h3 : (a ^ (i - 1)) ^ 3 = 1 := by
    have := pow_card_eq_one' (G := ↥(Q ⊓ K)) (x := ⟨_, haiD⟩)
    rw [hD] at this
    exact congrArg Subtype.val this
  have h9 : (9 : ℤ) ∣ (i - 1) * 3 := by
    have h : a ^ ((i - 1) * 3) = 1 := by
      rw [zpow_mul, show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, h3]
    have := orderOf_dvd_iff_zpow_eq_one.mpr h
    rwa [ha9] at this
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC.L28.SylowM27
