module

public import CFSG.Quasithin.Vol2.Ch10SecKITk
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalRows
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

theorem two_pow_orderOf_dvd_card {A : Type} [Group A] [Finite A] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {z : A} (hz : orderOf z = p) {Y : Subgroup A} (hY : IsPGroup 2 Y)
    (hzY : z ∈ normalizer (Y : Set A)) (hnc : ∃ y ∈ Y, z * y ≠ y * z) :
    2 ^ orderOf (2 : ZMod p) ∣ Nat.card Y := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hy, hyz⟩ := hnc
  obtain ⟨k, hk1, hk2, hdvd⟩ :=
    CFSG.Quasithin.Vol2.Ch10.SecB.C10KH.dvd_two_pow_sub_one_of_act hY hp hp2 hz hzY
      ⟨y, hy, fun h => hyz (mul_inv_eq_iff_eq_mul.mp h)⟩
  have hpow : (2 : ZMod p) ^ k = 1 := by
    have h := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    rw [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one,
      sub_eq_zero] at h
    exact h
  have hd : orderOf (2 : ZMod p) ≤ k := orderOf_le_of_pow_eq_one hk1 hpow
  obtain ⟨m, hm⟩ := hY.exists_card_eq
  rw [hm] at hk2 ⊢
  exact pow_dvd_pow 2 (hd.trans ((Nat.pow_le_pow_iff_right (by norm_num)).mp hk2))

theorem two_pow_orderOf_dvd_of_pCoreOf {A : Type} [Group A] [Finite A] (L K₀ : Subgroup A)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {z : A} (hz : orderOf z = p) (hK₀L : K₀ ≤ L)
    (hzK : z ∈ K₀) (hy : ∃ y ∈ pCoreOf 2 K₀, z * y ≠ y * z) {n : ℕ} (hn : Nat.card L = n) :
    2 ^ orderOf (2 : ZMod p) ∣ n := by
  have h1 := two_pow_orderOf_dvd_card hp hp2 hz (pCoreOf_isPGroup 2 K₀)
    (localGroup_le_normalizer_pCoreOf 2 K₀ hzK) hy
  have h2 : Nat.card (pCoreOf 2 K₀) ∣ Nat.card L :=
    Subgroup.card_dvd_of_le ((pCoreOf_le 2 K₀).trans hK₀L)
  rw [hn] at h2
  exact h1.trans h2

theorem false_of_not_dvd {A : Type} [Group A] [Finite A] (L K₀ : Subgroup A) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {z : A} (hz : orderOf z = p) (hK₀L : K₀ ≤ L) (hzK : z ∈ K₀)
    (hy : ∃ y ∈ pCoreOf 2 K₀, z * y ≠ y * z) {n : ℕ} (hn : Nat.card L = n)
    (hord : ¬ 2 ^ orderOf (2 : ZMod p) ∣ n) : False :=
  hord (two_pow_orderOf_dvd_of_pCoreOf L K₀ hp hp2 hz hK₀L hzK hy hn)

theorem orderOf_two_zmod_eq (p d : ℕ) (hd : 0 < d) (h1 : (2 : ZMod p) ^ d = 1)
    (hk : ∀ k < d, 0 < k → (2 : ZMod p) ^ k ≠ 1) : orderOf (2 : ZMod p) = d :=
  (orderOf_eq_iff hd).mpr ⟨h1, fun k hkd hk0 => hk k hkd hk0⟩

theorem row_of_ord (s : TauCeti.SporadicName) (p n : ℕ)
    (hcard : ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A),
      Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic s).Group) → Nat.card L = n)
    (hord : ¬ 2 ^ orderOf (2 : ZMod p) ∣ n) : KFactSporLocalRow s p := by
  intro A _ _ L K₀ z hL _ _ hp hp5 _ hz hK₀L hzK _ _ _ hy _
  exact (false_of_not_dvd L K₀ hp (by omega) hz hK₀L hzK hy (hcard A L hL) hord).elim

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
