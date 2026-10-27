module

public import CFSG.Quasithin.Vol2.Ch4Sec3L4316Rank
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Fix
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open scoped Pointwise

theorem frattini_quot_mul_self_eq_one {A : Type} [Group A] [Finite A] {Y : Subgroup A}
    (hY : IsPGroup 2 Y) : ∀ w : ↥Y ⧸ frattini ↥Y, w * w = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (IsPGroup 2 ↥Y) := ⟨hY⟩
  have hEA : CFSG.IsElementaryAbelian 2 (↥Y ⧸ frattini ↥Y) :=
    CFSG.isElementaryAbelian_quotient_frattini
  intro w
  rw [← pow_two]
  exact (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (CFSG.IsElementaryAbelian.exponent_dvd_p 2 (↥Y ⧸ frattini ↥Y))) w

theorem two_pow_orderOf_le_card_frattini_quot {A : Type} [Group A] [Finite A] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {z : A} (hz : orderOf z = p) {Y : Subgroup A}
    (hY : IsPGroup 2 Y) (hzY : z ∈ normalizer (Y : Set A)) (hnc : ∃ y ∈ Y, z * y ≠ y * z) :
    2 ^ orderOf (2 : ZMod p) ≤ Nat.card (↥Y ⧸ frattini ↥Y) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hsq := frattini_quot_mul_self_eq_one hY
  obtain ⟨φ, hφdef⟩ : ∃ φ, CFSG.Quasithin.H13.Ch4.L4316.conjFrattini Y ⟨z, hzY⟩ = φ :=
    ⟨_, rfl⟩
  have hφ1 : φ ≠ 1 := by
    intro h
    obtain ⟨y, hyY, hyz⟩ := hnc
    have hodd : Odd (orderOf z) := by
      rw [hz]
      exact hp.odd_of_ne_two hp2
    have hle := CFSG.Quasithin.H13.Ch4.L4316.le_centralizer_of_conjFrattini_eq_one hY hzY hodd
      (hφdef.trans h)
    exact hyz (Subgroup.mem_centralizer_iff.mp (hle hyY) z (Set.mem_singleton z))
  have hzN : (⟨z, hzY⟩ : ↥(normalizer (Y : Set A))) ^ p = 1 := by
    apply Subtype.ext
    show z ^ p = 1
    rw [← hz]
    exact pow_orderOf_eq_one z
  have hφpow : φ ^ p = 1 := by
    rw [← hφdef, ← map_pow (CFSG.Quasithin.H13.Ch4.L4316.conjFrattini Y), hzN, map_one]
  have hφord : orderOf φ = p := by
    rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hφpow) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hφ1
    · exact h
  have hcomm : ∀ a b : ↥Y ⧸ frattini ↥Y, a * b = b * a := by
    intro a b
    have hab : (a * b) * (a * b) = 1 := hsq _
    calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right hab).symm
      _ = b * a := by
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (hsq a), inv_eq_of_mul_eq_one_right (hsq b)]
  let _ : CommGroup (↥Y ⧸ frattini ↥Y) :=
    { (inferInstance : Group (↥Y ⧸ frattini ↥Y)) with mul_comm := hcomm }
  haveI : Finite (↥Y ⧸ frattini ↥Y) := inferInstance
  have h1 := CFSG.QuasithinUnique.Setup.X1.two_pow_orderOf_le_index_fixV hsq hp2 hφord
  exact h1.trans (CFSG.QuasithinUnique.Setup.X1.index_fixV_le_card _)

theorem false_of_elemAbelian_sylow {A : Type} [Group A] [Finite A] (L K₀ : Subgroup A) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {z : A} (hz : orderOf z = p) (hK₀L : K₀ ≤ L) (hzK : z ∈ K₀)
    (hy : ∃ y ∈ pCoreOf 2 K₀, z * y ≠ y * z) {d m : ℕ} (hd : orderOf (2 : ZMod p) = d)
    (hn : Nat.card L = 2 ^ d * m) (hm : Odd m) {g : A} (hgL : g ∈ L) (hg : orderOf g = 4) :
    False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := pCoreOf 2 K₀ with hYdef
  have hYP : IsPGroup 2 Y := pCoreOf_isPGroup 2 K₀
  have hYL : Y ≤ L := (pCoreOf_le 2 K₀).trans hK₀L
  have hzY : z ∈ normalizer (Y : Set A) := localGroup_le_normalizer_pCoreOf 2 K₀ hzK
  have hbound := two_pow_orderOf_le_card_frattini_quot hp hp2 hz hYP hzY hy
  rw [hd] at hbound
  obtain ⟨j, hj⟩ := hYP.exists_card_eq
  have hdvd : 2 ^ j ∣ 2 ^ d * m := by
    rw [← hj, ← hn]
    exact Subgroup.card_dvd_of_le hYL
  have hcop : Nat.Coprime (2 ^ j) m := by
    refine Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr ?_)
    obtain ⟨k, hk⟩ := hm
    omega
  have hjd : j ≤ d :=
    (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp (hcop.dvd_of_dvd_mul_right hdvd)
  have hQY : Nat.card (↥Y ⧸ frattini ↥Y) ≤ Nat.card ↥Y := by
    rw [← Subgroup.card_mul_index (frattini ↥Y)]
    exact Nat.le_mul_of_pos_left _ Nat.card_pos
  have hQeq : Nat.card (↥Y ⧸ frattini ↥Y) = Nat.card ↥Y := by
    refine le_antisymm hQY ?_
    rw [hj]
    exact (Nat.pow_le_pow_right (by norm_num) hjd).trans hbound
  have hdj : d ≤ j := by
    have h2 : 2 ^ d ≤ 2 ^ j := by
      rw [← hj, ← hQeq]
      exact hbound
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2
  have hcardY : Nat.card ↥Y = 2 ^ d := by
    rw [hj, le_antisymm hjd hdj]
  have hΦ : frattini ↥Y = ⊥ := by
    have hmul := Subgroup.card_mul_index (frattini ↥Y)
    have hidx : (frattini ↥Y).index = Nat.card (↥Y ⧸ frattini ↥Y) := rfl
    rw [hidx, hQeq] at hmul
    rw [Subgroup.eq_bot_iff_card]
    refine Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥Y)) ?_
    rw [one_mul]
    exact hmul
  have hsqY : ∀ a ∈ Y, a * a = 1 := by
    intro a ha
    have h1 : ((⟨a, ha⟩ * ⟨a, ha⟩ : ↥Y) : ↥Y ⧸ frattini ↥Y) = 1 := by
      rw [QuotientGroup.mk_mul]
      exact frattini_quot_mul_self_eq_one hYP _
    have hmem : (⟨a, ha⟩ * ⟨a, ha⟩ : ↥Y) ∈ frattini ↥Y := (QuotientGroup.eq_one_iff _).mp h1
    rw [hΦ, Subgroup.mem_bot] at hmem
    simpa using congrArg Subtype.val hmem
  have hcardLy : Nat.card ↥(Y.subgroupOf L) = 2 ^ d := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYL).toEquiv, hcardY]
  have hLy : IsPGroup 2 (Y.subgroupOf L) := IsPGroup.of_card hcardLy
  have hidx : (Y.subgroupOf L).index = m := by
    have h1 := Subgroup.card_mul_index (Y.subgroupOf L)
    rw [hcardLy, hn] at h1
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
  have hnd : ¬ 2 ∣ (Y.subgroupOf L).index := by
    rw [hidx]
    obtain ⟨k, hk⟩ := hm
    omega
  obtain ⟨YS, hYS⟩ : ∃ YS : Sylow 2 ↥L, (YS : Subgroup ↥L) = Y.subgroupOf L :=
    ⟨IsPGroup.toSylow hLy hnd, rfl⟩
  haveI : Finite (Sylow 2 ↥L) := Sylow.finite_of_finiteIndex YS
  obtain ⟨x, hxg⟩ : ∃ x : ↥L, (x : A) = g := ⟨⟨g, hgL⟩, rfl⟩
  have hxord : orderOf x = 4 := by
    rw [← Subgroup.orderOf_coe, hxg, hg]
  have hxz : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hxord] <;> norm_num)
  obtain ⟨P, hP⟩ := IsPGroup.exists_le_sylow hxz
  have hxP : x ∈ (P : Subgroup ↥L) := hP (Subgroup.mem_zpowers x)
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq ↥L YS P
  have hxh : x ∈ MulAut.conj h • (YS : Subgroup ↥L) := by
    have hxh' : x ∈ ((h • YS : Sylow 2 ↥L) : Subgroup ↥L) := by
      rw [hh]
      exact hxP
    exact hxh'
  obtain ⟨s, hs, hsx⟩ :=
    (Subgroup.mem_smul_pointwise_iff_exists x (MulAut.conj h) (YS : Subgroup ↥L)).mp hxh
  rw [hYS] at hs
  have hss : s * s = 1 := by
    apply Subtype.ext
    simpa using hsqY (s : A) (Subgroup.mem_subgroupOf.mp hs)
  have hxeq : x = h * s * h⁻¹ := hsx.symm
  have hxx : x * x = 1 := by
    rw [hxeq]
    calc h * s * h⁻¹ * (h * s * h⁻¹) = h * (s * s) * h⁻¹ := by group
      _ = 1 := by rw [hss, mul_one, mul_inv_cancel]
  have hgg : g * g = 1 := by
    simpa [hxg] using congrArg Subtype.val hxx
  have hdvd4 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hgg)
  rw [hg] at hdvd4
  norm_num at hdvd4

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
