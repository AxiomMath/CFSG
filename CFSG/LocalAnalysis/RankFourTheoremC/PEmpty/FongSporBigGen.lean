module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalGenW
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalOrd
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalTransport

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

theorem commute_of_big_prime {A : Type} [Group A] [Finite A] (L K₀ : Subgroup A) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) {w : A} (hw : orderOf w = r) (hwK : w ∈ K₀) (hK₀L : K₀ ≤ L)
    {e m : ℕ} (hn : Nat.card L = 2 ^ e * m) (hm : Odd m) (hbig : e < orderOf (2 : ZMod r)) :
    ∀ y ∈ pCoreOf 2 K₀, w * y = y * w := by
  intro y hy
  by_contra hne
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYP : IsPGroup 2 (pCoreOf 2 K₀) := pCoreOf_isPGroup 2 K₀
  have hYL : pCoreOf 2 K₀ ≤ L := (pCoreOf_le 2 K₀).trans hK₀L
  have hwY : w ∈ normalizer ((pCoreOf 2 K₀ : Subgroup A) : Set A) :=
    localGroup_le_normalizer_pCoreOf 2 K₀ hwK
  have hdvd := two_pow_orderOf_dvd_card hr hr2 hw hYP hwY ⟨y, hy, hne⟩
  obtain ⟨j, hj⟩ := hYP.exists_card_eq
  have hdvd2 : 2 ^ j ∣ 2 ^ e * m := by
    rw [← hj, ← hn]
    exact Subgroup.card_dvd_of_le hYL
  have hcop : Nat.Coprime (2 ^ j) m := by
    refine Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr ?_)
    obtain ⟨k, hk⟩ := hm
    omega
  have hjd : j ≤ e :=
    (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp (hcop.dvd_of_dvd_mul_right hdvd2)
  rw [hj] at hdvd
  have hle : orderOf (2 : ZMod r) ≤ j := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
  omega

@[expose] def BigW (X : Type) [Group X] (p r : ℕ) : Prop :=
  ∃ (z₀ t₀ : X) (W : Set X), orderOf z₀ = p ∧ t₀ * t₀ = 1 ∧ t₀ ≠ 1 ∧ z₀ * t₀ = t₀ * z₀ ∧
    (∀ w ∈ W, orderOf w = r ∧ w * t₀ = t₀ * w) ∧ z₀ ∈ closure W

theorem BigW.of_mulEquiv {X Y : Type} [Group X] [Group Y] (f : X ≃* Y) {p r : ℕ}
    (h : BigW X p r) : BigW Y p r := by
  obtain ⟨z₀, t₀, W, hz, ht2, ht1, hzt, hW, hcl⟩ := h
  refine ⟨f z₀, f t₀, f '' W, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq]
    exact hz
  · rw [← map_mul, ht2, map_one]
  · exact fun h => ht1 (f.injective (by rw [h, map_one]))
  · rw [← map_mul, ← map_mul, hzt]
  · rintro _ ⟨w, hw, rfl⟩
    obtain ⟨h1, h2⟩ := hW w hw
    exact ⟨by rw [MulEquiv.orderOf_eq]; exact h1, by rw [← map_mul, ← map_mul, h2]⟩
  · rw [closure_image_eq_map]
    exact Subgroup.mem_map_of_mem _ hcl

theorem false_of_bigW {G : Type} [Group G] [Finite G] {p r : ℕ} (hp : p.Prime)
    (hsyl : ¬ p ^ 2 ∣ Nat.card G) (hr : r.Prime) (hr2 : r ≠ 2) {e m : ℕ}
    (hcard : Nat.card G = 2 ^ e * m) (hm : Odd m) (hbig : e < orderOf (2 : ZMod r))
    (hW : BigW G p r) {K : Subgroup G} {z : G} (hz : orderOf z = p)
    (hN : normalizer (zpowers z : Set G) ≤ K)
    (hcl : ∀ U : Subgroup G, IsPGroup 2 U → z ∈ normalizer (U : Set G) → U ⊓ K ≠ ⊥ →
      normalizer (U : Set G) ≤ K)
    (hy : ∃ y ∈ pCoreOf 2 K, z * y ≠ y * z) : False := by
  obtain ⟨z', t', W', hz', ht2, ht1, hzt, hW', hcl'⟩ := hW
  obtain ⟨g, hg⟩ := exists_conj_zpowers hp hsyl hz hz'
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hg
  let φ : G ≃* G := MulAut.conj g⁻¹
  have hφ : ∀ x : G, φ x = g⁻¹ * x * g := fun x => by simp [φ, MulAut.conj_apply]
  have hzz1 : z ∈ zpowers (φ z') := by
    refine mem_zpowers_iff.mpr ⟨j, ?_⟩
    rw [← map_zpow, hj, hφ]
    group
  have hzt1 : φ z' * φ t' = φ t' * φ z' := by rw [← map_mul, ← map_mul, hzt]
  have hzt2 : z * φ t' = φ t' * z := commute_of_mem_zpowers hzz1 hzt1
  have ht21 : φ t' * φ t' = 1 := by rw [← map_mul, ht2, map_one]
  have ht11 : φ t' ≠ 1 := fun h => ht1 (φ.injective (by rw [h, map_one]))
  have hWc : ∀ w ∈ φ '' W', ∀ y ∈ pCoreOf 2 K, w * y = y * w := by
    rintro _ ⟨w, hw, rfl⟩ y hy
    obtain ⟨h1, h2⟩ := hW' w hw
    have hcomm : φ w * φ t' = φ t' * φ w := by rw [← map_mul, ← map_mul, h2]
    have hwK : φ w ∈ K := mem_of_centralizes_involution hN hcl ht21 ht11 hzt2 hcomm
    have hord : orderOf (φ w) = r := by rw [MulEquiv.orderOf_eq]; exact h1
    exact commute_of_big_prime ⊤ K hr hr2 hord hwK le_top (by rw [Subgroup.card_top]; exact hcard)
      hm hbig y hy
  have hzcl : z ∈ closure (φ '' W') := by
    have h1 : φ z' ∈ closure (φ '' W') := by
      rw [closure_image_eq_map]
      exact Subgroup.mem_map_of_mem _ hcl'
    exact (zpowers_le.mpr h1) hzz1
  obtain ⟨y, hyY, hyz⟩ := hy
  have hcent : closure (φ '' W') ≤ Subgroup.centralizer ({y} : Set G) := by
    rw [closure_le]
    intro w hw
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact hWc w hw y hyY
  have := Subgroup.mem_centralizer_singleton_iff.mp (hcent hzcl)
  exact hyz this

theorem row_of_bigW {s : TauCeti.SporadicName} {p r : ℕ} (X : Type) [Group X]
    (hX : ∀ (G : Type) [Group G],
      Nonempty (G ≃* (TauCeti.CFSGIndex.sporadic s).Group) → Nonempty (G ≃* X)) {e m : ℕ}
    (hcard : Nat.card X = 2 ^ e * m) (hm : Odd m) (hsyl : ¬ p ^ 2 ∣ m) (hr : r.Prime)
    (hr2 : r ≠ 2) (hbig : e < orderOf (2 : ZMod r)) (hW : BigW X p r) :
    KFactSporLocalRow s p := by
  apply row_of_model
  intro G _ _ ⟨e'⟩ hp hp5 K z hz hK hzK hN hcl hy hNN
  obtain ⟨φ⟩ := hX G ⟨e'⟩
  have hGX : Nat.card G = 2 ^ e * m := by
    rw [Nat.card_congr φ.toEquiv]
    exact hcard
  have hsylG : ¬ p ^ 2 ∣ Nat.card G := by
    rw [hGX]
    intro hd
    have hcop : Nat.Coprime (p ^ 2) (2 ^ e) :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).mpr (by omega))
    exact hsyl (hcop.dvd_of_dvd_mul_left hd)
  exact (false_of_bigW hp hsylG hr hr2 hGX hm hbig (BigW.of_mulEquiv φ.symm hW) hz hN hcl hy).elim

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
