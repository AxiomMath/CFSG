module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank619Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank620L32
public import CFSG.LieType.BorelTits.Basic
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627L32Data

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614I

open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
open CFSG.LocalAnalysis.RankThreeTheoremC

variable {G : Type} [Group G] [Finite G]

structure L32Data (M B H S K : Subgroup G) (z b : G) (f : ↥K →* GL32) : Prop
    extends Data619 M B H S K z f where
  S_le : S ≤ K ⊔ pCoreOf 2 H
  S_index : (pCoreOf 2 H).relIndex S = 4
  K_perfect : ⁅K, K⁆ = K
  B_card : Nat.card B = 9
  B_comm : ∀ a ∈ B, ∀ c ∈ B, a * c = c * a
  B_exp : ∀ a ∈ B, a ^ 3 = 1
  b_mem : b ∈ B
  b_not_mem : b ∉ zpowers z
  b_cent : ⁅zpowers b, K⁆ ≤ pCoreOf 2 H

variable {M B H S K : Subgroup G} {z b : G} {f : ↥K →* GL32}

omit [Finite G] in
theorem relIndex_eq_of_sup {Y T N A : Subgroup G} (hTY : T ≤ Y) (hNA : N ≤ A)
    (hAY : A ≤ Y) (hYN : Y ≤ normalizer (N : Set G)) (hY : Y ≤ T ⊔ N) :
    A.relIndex T = A.relIndex Y := by
  have hNY : N ≤ Y := hNA.trans hAY
  have : (N.subgroupOf Y).Normal := (normal_subgroupOf_iff_le_normalizer hNY).2 hYN
  let π : ↥Y →* ↥Y ⧸ N.subgroupOf Y := QuotientGroup.mk' (N.subgroupOf Y)
  let ψ : ↥T →* ↥Y ⧸ N.subgroupOf Y := π.comp (inclusion hTY)
  have hψ : Function.Surjective ψ := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    have hy : (y : G) ∈ T ⊔ N := hY y.2
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right T N (hTY.trans hYN)] at hy
    obtain ⟨t, ht, n, hn, hty⟩ := Set.mem_mul.1 hy
    refine ⟨⟨t, ht⟩, ?_⟩
    change ((⟨t, hTY ht⟩ : ↥Y) : ↥Y ⧸ N.subgroupOf Y) = y
    rw [QuotientGroup.eq, mem_subgroupOf]
    simpa [← hty] using hn
  have hker : π.ker ≤ A.subgroupOf Y := by
    rw [QuotientGroup.ker_mk']
    exact subgroupOf_mono Y hNA
  have h1 : ((A.subgroupOf Y).map π).index = (A.subgroupOf Y).index :=
    index_map_eq _ (QuotientGroup.mk'_surjective _) hker
  have h2 : (((A.subgroupOf Y).map π).comap ψ).index = ((A.subgroupOf Y).map π).index :=
    index_comap_of_surjective _ hψ
  have h3 : ((A.subgroupOf Y).map π).comap ψ = A.subgroupOf T := by
    change ((A.subgroupOf Y).map π).comap (π.comp (inclusion hTY)) = _
    rw [← comap_comap, comap_map_eq, sup_of_le_left hker]
    ext t
    simp [mem_subgroupOf]
  change (A.subgroupOf T).index = (A.subgroupOf Y).index
  rw [← h3, h2, h1]

theorem L32Data.S_le_H (h : L32Data M B H S K z b f) : S ≤ H := h.maxInv.1.1

theorem L32Data.isPGroup_S (h : L32Data M B H S K z b f) : IsPGroup 2 S := h.maxInv.1.2.1

theorem L32Data.B_le_normalizer_S (h : L32Data M B H S K z b f) : B ≤ normalizer (S : Set G) :=
  h.maxInv.1.2.2

theorem L32Data.H_le (h : L32Data M B H S K z b f) : H ≤ normalizer (pCoreOf 2 H : Set G) :=
  h.eq_normalizer.le

theorem L32Data.isPGroup_core (h : L32Data M B H S K z b f) : IsPGroup 2 (pCoreOf 2 H) :=
  h.isPGroup_S.to_le h.core_le

theorem L32Data.X_le_H (h : L32Data M B H S K z b f) : K ⊔ pCoreOf 2 H ≤ H :=
  sup_le h.K_le (CFSG.LieType.BorelTits.pCoreOf_le 2 H)

theorem L32Data.X_le_normalizer (h : L32Data M B H S K z b f) :
    K ⊔ pCoreOf 2 H ≤ normalizer (pCoreOf 2 H : Set G) :=
  h.X_le_H.trans h.H_le

theorem L32Data.H_le_normalizer_X (h : L32Data M B H S K z b f) :
    H ≤ normalizer ((K ⊔ pCoreOf 2 H : Subgroup G) : Set G) :=
  fun _ hg => Subgroup.inf_normalizer_le_normalizer_sup K (pCoreOf 2 H)
    ⟨h.K_normal hg, h.eq_normalizer.le hg⟩

theorem L32Data.pCoreOf_X (h : L32Data M B H S K z b f) :
    pCoreOf 2 (K ⊔ pCoreOf 2 H) = pCoreOf 2 H := by
  refine le_antisymm ?_ ?_
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans h.X_le_H)
      (h.H_le_normalizer_X.trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_sup_right
      (h.X_le_H.trans h.eq_normalizer.le) (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)

theorem L32Data.charTwo_X (h : L32Data M B H S K z b f) :
    (K ⊔ pCoreOf 2 H) ⊓ centralizer (pCoreOf 2 (K ⊔ pCoreOf 2 H) : Set G) ≤
      pCoreOf 2 (K ⊔ pCoreOf 2 H) := by
  rw [h.pCoreOf_X]
  exact (inf_le_inf_right _ h.X_le_H).trans (h.charTwo H h.twoLocal)

theorem L32Data.exists_mul (h : L32Data M B H S K z b f) {x : G}
    (hx : x ∈ K ⊔ pCoreOf 2 H) : ∃ k ∈ K, ∃ o ∈ pCoreOf 2 H, x = k * o := by
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right K (pCoreOf 2 H)
    (h.K_le.trans h.H_le)] at hx
  obtain ⟨k, hk, o, ho, rfl⟩ := Set.mem_mul.1 hx
  exact ⟨k, hk, o, ho, rfl⟩

theorem L32Data.exists_mul_S (h : L32Data M B H S K z b f) {s : G} (hs : s ∈ S) :
    ∃ k ∈ K ⊓ S, ∃ o ∈ pCoreOf 2 H, s = k * o := by
  obtain ⟨k, hk, o, ho, rfl⟩ := h.exists_mul (h.S_le hs)
  refine ⟨k, ⟨hk, ?_⟩, o, ho, rfl⟩
  simpa using S.mul_mem hs (S.inv_mem (h.core_le ho))

omit [Finite G] in
@[expose] def l32V (K S : Subgroup G) (f : ↥K →* GL32) : Subgroup GL32 :=
  (S.subgroupOf K).map f

omit [Finite G] in
theorem mem_l32V {v : GL32} : v ∈ l32V K S f ↔ ∃ k : ↥K, (k : G) ∈ S ∧ f k = v := by
  simp [l32V, mem_map, mem_subgroupOf]

theorem L32Data.f_mem_V_iff (h : L32Data M B H S K z b f) (k : ↥K) :
    f k ∈ l32V K S f ↔ (k : G) ∈ S := by
  rw [mem_l32V]
  refine ⟨fun ⟨k', hk'S, hk'⟩ => ?_, fun hk => ⟨k, hk, rfl⟩⟩
  have h1 : f (k'⁻¹ * k) = 1 := by rw [map_mul, map_inv, hk', inv_mul_cancel]
  have h2 : ((k'⁻¹ * k : ↥K) : G) ∈ pCoreOf 2 H := (h.f_ker _).1 h1
  have h3 : (k : G) = (k' : G) * ((k'⁻¹ * k : ↥K) : G) := by simp
  rw [h3]
  exact S.mul_mem hk'S (h.core_le h2)

omit [Finite G] in
theorem l32_normalizer_map {Q : Subgroup G} {k : ↥K}
    (hk : (k : G) ∈ normalizer (Q : Set G)) :
    f k ∈ normalizer (((Q.subgroupOf K).map f : Subgroup GL32) : Set GL32) := by
  have key : ∀ {k : ↥K}, (k : G) ∈ normalizer (Q : Set G) → ∀ v ∈ (Q.subgroupOf K).map f,
      f k * v * (f k)⁻¹ ∈ (Q.subgroupOf K).map f := by
    rintro k hk _ ⟨k', hk', rfl⟩
    refine ⟨k * k' * k⁻¹, ?_, by simp⟩
    have hk'' : (k' : G) ∈ Q := hk'
    exact (mem_normalizer_iff.1 hk _).1 hk''
  rw [mem_normalizer_iff]
  intro v
  refine ⟨key hk v, fun hv => ?_⟩
  have := key (k := k⁻¹) (by simpa using inv_mem hk) _ hv
  simpa [mul_assoc] using this

theorem L32Data.conj_mem_S (h : L32Data M B H S K z b f) {k : ↥K}
    (hk : f k ∈ normalizer (l32V K S f : Set GL32)) {s : G} (hs : s ∈ S) :
    (k : G) * s * (k : G)⁻¹ ∈ S := by
  obtain ⟨k₁, hk₁, o, ho, rfl⟩ := h.exists_mul_S hs
  have h1 : (k : G) * (k₁ * o) * (k : G)⁻¹ =
      ((k : G) * k₁ * (k : G)⁻¹) * ((k : G) * o * (k : G)⁻¹) := by group
  rw [h1]
  refine S.mul_mem ?_ (h.core_le ((mem_normalizer_iff.1 (h.H_le (h.K_le k.2)) o).1 ho))
  have h2 : f k * f ⟨k₁, hk₁.1⟩ * (f k)⁻¹ ∈ l32V K S f :=
    (mem_normalizer_iff.1 hk _).1 ((h.f_mem_V_iff ⟨k₁, hk₁.1⟩).2 hk₁.2)
  rw [← map_inv, ← map_mul, ← map_mul, h.f_mem_V_iff] at h2
  exact h2

theorem L32Data.mem_normalizer_of (h : L32Data M B H S K z b f) {k : ↥K}
    (hk : f k ∈ normalizer (l32V K S f : Set GL32)) : (k : G) ∈ normalizer (S : Set G) := by
  rw [mem_normalizer_iff]
  intro s
  refine ⟨h.conj_mem_S hk, fun hs => ?_⟩
  have hk' : f k⁻¹ ∈ normalizer (l32V K S f : Set GL32) := by
    rw [map_inv]
    exact inv_mem hk
  have := h.conj_mem_S hk' hs
  simpa [mul_assoc] using this

theorem L32Data.mem_normalizer_S_iff (h : L32Data M B H S K z b f) (k : ↥K) :
    (k : G) ∈ normalizer (S : Set G) ↔ f k ∈ normalizer (l32V K S f : Set GL32) :=
  ⟨l32_normalizer_map, h.mem_normalizer_of⟩

theorem L32Data.l_mem_normalizer (h : L32Data M B H S K z b f) :
    f ⟨z, h.z_mem_K⟩ ∈ normalizer (l32V K S f : Set GL32) :=
  (h.mem_normalizer_S_iff ⟨z, h.z_mem_K⟩).1 (h.B_le_normalizer_S h.z_mem_B)

theorem L32Data.z_not_mem (h : L32Data M B H S K z b f) : z ∉ pCoreOf 2 H := by
  intro hz
  obtain ⟨n, hn⟩ := h.isPGroup_core ⟨z, hz⟩
  have h1 : z ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have h2 : orderOf z ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h1
  rw [h.z_order] at h2
  have h3 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2
  omega

theorem L32Data.orderOf_l (h : L32Data M B H S K z b f) :
    orderOf (f ⟨z, h.z_mem_K⟩) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : f ⟨z, h.z_mem_K⟩ ≠ 1 := fun h1 => h.z_not_mem ((h.f_ker _).1 h1)
  have h2 : f ⟨z, h.z_mem_K⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have h3 : (⟨z, h.z_mem_K⟩ : ↥K) ^ 3 = 1 :=
      Subtype.ext (by simpa [h.z_order] using pow_orderOf_eq_one z)
    rw [h3, map_one]
  exact orderOf_eq_prime h2 h1

theorem L32Data.isPGroup_V (h : L32Data M B H S K z b f) : IsPGroup 2 (l32V K S f) :=
  (h.isPGroup_S.comap_subtype (K := K)).map f

theorem L32Data.ker (h : L32Data M B H S K z b f) :
    f.ker = (pCoreOf 2 H).subgroupOf K := by
  ext k
  rw [MonoidHom.mem_ker, mem_subgroupOf]
  exact h.f_ker k

theorem L32Data.card_V (h : L32Data M B H S K z b f) : Nat.card (l32V K S f) = 4 := by
  have h1 : Nat.card (l32V K S f) = (pCoreOf 2 H).relIndex (S ⊓ K) := by
    rw [l32V, ← relIndex_ker, h.ker]
    change ((pCoreOf 2 H).comap K.subtype).relIndex (S.subgroupOf K) = _
    rw [relIndex_comap, subgroupOf_map_subtype]
  have h2 : (pCoreOf 2 H).relIndex (S ⊓ K) = (pCoreOf 2 H).relIndex S := by
    refine relIndex_eq_of_sup inf_le_left le_rfl h.core_le (h.S_le_H.trans h.H_le) ?_
    intro s hs
    obtain ⟨k, hk, o, ho, rfl⟩ := h.exists_mul_S hs
    exact mul_mem (mem_sup_left ⟨hk.2, hk.1⟩) (mem_sup_right ho)
  rw [h1, h2]
  exact h.S_index

theorem L32Data.relIndex_K (h : L32Data M B H S K z b f) :
    (pCoreOf 2 H).relIndex K = 168 := by
  rw [relIndex, ← h.ker, index_ker, MonoidHom.range_eq_top.2 h.f_surj, card_top]
  exact L32Insp.card_GL

theorem L32Data.relIndex_X (h : L32Data M B H S K z b f) :
    (pCoreOf 2 H).relIndex (K ⊔ pCoreOf 2 H) = 168 := by
  rw [← relIndex_eq_of_sup le_sup_left le_rfl le_sup_right h.X_le_normalizer le_rfl]
  exact h.relIndex_K

theorem L32Data.card_X (h : L32Data M B H S K z b f) :
    Nat.card (K ⊔ pCoreOf 2 H : Subgroup G) = Nat.card (pCoreOf 2 H : Subgroup G) * 168 := by
  rw [← relIndex_bot_left, ← relIndex_mul_relIndex ⊥ (pCoreOf 2 H) (K ⊔ pCoreOf 2 H) bot_le
    le_sup_right, h.relIndex_X, relIndex_bot_left]

theorem L32Data.index_normalizer_eq_seven (h : L32Data M B H S K z b f) :
    ((((K ⊔ pCoreOf 2 H) ⊓ normalizer (S : Set G) : Subgroup G)).subgroupOf
      (K ⊔ pCoreOf 2 H)).index = 7 := by
  have h1 : ((K ⊔ pCoreOf 2 H) ⊓ normalizer (S : Set G)).relIndex K =
      ((K ⊔ pCoreOf 2 H) ⊓ normalizer (S : Set G)).relIndex (K ⊔ pCoreOf 2 H) :=
    relIndex_eq_of_sup le_sup_left (le_inf le_sup_right (h.core_le.trans le_normalizer))
      inf_le_left h.X_le_normalizer le_rfl
  have h2 : ((K ⊔ pCoreOf 2 H) ⊓ normalizer (S : Set G)).subgroupOf K =
      (normalizer (l32V K S f : Set GL32)).comap f := by
    ext k
    rw [mem_subgroupOf, mem_comap, mem_inf]
    exact ⟨fun hk => (h.mem_normalizer_S_iff k).1 hk.2,
      fun hk => ⟨mem_sup_left k.2, (h.mem_normalizer_S_iff k).2 hk⟩⟩
  change ((K ⊔ pCoreOf 2 H) ⊓ normalizer (S : Set G)).relIndex (K ⊔ pCoreOf 2 H) = 7
  rw [← h1, relIndex, h2, index_comap_of_surjective _ h.f_surj]
  exact L32Insp.index_normalizer_eq_seven h.orderOf_l h.isPGroup_V h.card_V
    h.l_mem_normalizer

theorem pow_two_eq_of_odd {a c i j : ℕ} (hi : ¬ 2 ∣ i) (hj : ¬ 2 ∣ j)
    (h : 2 ^ a * i = 2 ^ c * j) : a = c := by
  have hi0 : i ≠ 0 := fun h0 => hi (h0 ▸ dvd_zero 2)
  have hj0 : j ≠ 0 := fun h0 => hj (h0 ▸ dvd_zero 2)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := congrArg (padicValNat 2) h
  rw [padicValNat.mul (by positivity) hi0, padicValNat.mul (by positivity) hj0,
    padicValNat.prime_pow, padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hi,
    padicValNat.eq_zero_of_not_dvd hj] at h1
  simpa using h1

theorem L32Data.card_sylow (h : L32Data M B H S K z b f) {R : Subgroup G}
    (hRX : R ≤ K ⊔ pCoreOf 2 H) (hR2 : IsPGroup 2 R)
    (hRi : ¬ 2 ∣ (R.subgroupOf (K ⊔ pCoreOf 2 H)).index) :
    Nat.card R = Nat.card (pCoreOf 2 H : Subgroup G) * 8 := by
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hR2
  obtain ⟨c, hc⟩ := IsPGroup.iff_card.1 h.isPGroup_core
  have hi : ¬ 2 ∣ R.relIndex (K ⊔ pCoreOf 2 H) := hRi
  have hX : Nat.card R * R.relIndex (K ⊔ pCoreOf 2 H) =
      Nat.card (pCoreOf 2 H : Subgroup G) * 168 := by
    have := relIndex_mul_relIndex ⊥ R (K ⊔ pCoreOf 2 H) bot_le hRX
    rw [relIndex_bot_left, relIndex_bot_left] at this
    exact this.trans h.card_X
  have hX' : 2 ^ a * R.relIndex (K ⊔ pCoreOf 2 H) = 2 ^ (c + 3) * 21 := by
    rw [← ha, hX, hc]
    ring
  have hac : a = c + 3 := pow_two_eq_of_odd hi (by norm_num) hX'
  rw [ha, hc, hac]
  ring

theorem L32Data.card_S (h : L32Data M B H S K z b f) :
    Nat.card S = Nat.card (pCoreOf 2 H : Subgroup G) * 4 := by
  have := relIndex_mul_relIndex ⊥ (pCoreOf 2 H) S bot_le h.core_le
  rw [relIndex_bot_left, relIndex_bot_left, h.S_index] at this
  exact this.symm

theorem L32Data.le_normalizer_of_sylow (h : L32Data M B H S K z b f) {R : Subgroup G}
    (hSR : S ≤ R) (hRX : R ≤ K ⊔ pCoreOf 2 H) (hR2 : IsPGroup 2 R)
    (hRi : ¬ 2 ∣ (R.subgroupOf (K ⊔ pCoreOf 2 H)).index) : R ≤ normalizer (S : Set G) := by
  have hR := h.card_sylow hRX hR2 hRi
  have hSR' : Nat.card S * S.relIndex R = Nat.card R := by
    have := relIndex_mul_relIndex ⊥ S R bot_le hSR
    rwa [relIndex_bot_left, relIndex_bot_left] at this
  have hm : S.relIndex R = 2 := by
    have hpos : 0 < Nat.card (pCoreOf 2 H : Subgroup G) * 4 := by
      have := Nat.card_pos (α := ↥(pCoreOf 2 H))
      omega
    have h1 : Nat.card (pCoreOf 2 H : Subgroup G) * 4 * S.relIndex R =
        Nat.card (pCoreOf 2 H : Subgroup G) * 4 * 2 :=
      calc Nat.card (pCoreOf 2 H : Subgroup G) * 4 * S.relIndex R
          = Nat.card S * S.relIndex R := by rw [h.card_S]
        _ = Nat.card R := hSR'
        _ = Nat.card (pCoreOf 2 H : Subgroup G) * 4 * 2 := by rw [hR]; ring
    exact Nat.eq_of_mul_eq_mul_left hpos h1
  exact (normal_subgroupOf_iff_le_normalizer hSR).1 (normal_of_index_eq_two hm)

theorem L32Data.pCoreOf_normalizer_eq (h : L32Data M B H S K z b f) :
    pCoreOf 2 ((K ⊔ pCoreOf 2 H) ⊓ normalizer (S : Set G)) = S := by
  have hSP : S ≤ (K ⊔ pCoreOf 2 H) ⊓ normalizer (S : Set G) := le_inf h.S_le le_normalizer
  have hSQ : S ≤ pCoreOf 2 ((K ⊔ pCoreOf 2 H) ⊓ normalizer (S : Set G)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hSP inf_le_right h.isPGroup_S
  refine le_antisymm ?_ hSQ
  set P := (K ⊔ pCoreOf 2 H) ⊓ normalizer (S : Set G)
  have hQ2 : IsPGroup 2 (pCoreOf 2 P) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P
  have hQP : pCoreOf 2 P ≤ P := CFSG.LieType.BorelTits.pCoreOf_le 2 P
  have hPQ : P ≤ normalizer (pCoreOf 2 P : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P
  have hzP : z ∈ P := ⟨mem_sup_left h.z_mem_K, h.B_le_normalizer_S h.z_mem_B⟩
  set W : Subgroup GL32 := ((pCoreOf 2 P).subgroupOf K).map f
  have hVW : l32V K S f ≤ W := map_mono (subgroupOf_mono K hSQ)
  have hW2 : IsPGroup 2 W := (hQ2.comap_subtype (K := K)).map f
  have hlW : f ⟨z, h.z_mem_K⟩ ∈ normalizer (W : Set GL32) :=
    l32_normalizer_map (Q := pCoreOf 2 P) (hPQ hzP)
  have hWV : W ≤ l32V K S f :=
    L32Insp.le_of_normal_two_subgroup h.orderOf_l h.card_V h.isPGroup_V
      h.l_mem_normalizer hVW hW2 hlW
  intro q hq
  obtain ⟨k, hk, o, ho, rfl⟩ := h.exists_mul (hQP hq).1
  have hoS : o ∈ S := h.core_le ho
  have hkQ : k ∈ pCoreOf 2 P := by
    simpa using (pCoreOf 2 P).mul_mem hq ((pCoreOf 2 P).inv_mem (hSQ hoS))
  have hkW : f ⟨k, hk⟩ ∈ W := ⟨⟨k, hk⟩, hkQ, rfl⟩
  exact S.mul_mem ((h.f_mem_V_iff ⟨k, hk⟩).1 (hWV hkW)) hoS

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614I
