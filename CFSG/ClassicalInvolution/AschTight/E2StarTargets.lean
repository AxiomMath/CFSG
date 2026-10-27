module

public import CFSG.ClassicalInvolution.AschTight.Sec19Targets
public import CFSG.ClassicalInvolution.AschTight.Thm6Tight

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

variable {G : Type} [Group G]

theorem IsQuaternionSub.eq_of_mul_self_eq_one {P : Subgroup G} (hP : IsQuaternionSub P)
    {x y : G} (hx : x ∈ P) (hy : y ∈ P) (hx2 : x * x = 1) (hy2 : y * y = 1) (hx1 : x ≠ 1)
    (hy1 : y ≠ 1) : x = y := by
  obtain ⟨a, b, ha4, -, hb2, hbab, hcl⟩ := hP
  have hconj : ∀ i : ℤ, b * a ^ i * b⁻¹ = a ^ (-i) := fun i => by
    rw [← _root_.conj_zpow, hbab, inv_zpow']
  have hconj' : ∀ i : ℤ, b⁻¹ * a ^ i * b = a ^ (-i) := fun i => by
    have h1 := hconj (-i)
    rw [neg_neg] at h1
    calc b⁻¹ * a ^ i * b = b⁻¹ * (b * a ^ (-i) * b⁻¹) * b := by rw [h1]
      _ = a ^ (-i) := by group
  have hbN : b ∈ Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      rw [hconj]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) _
    · intro hw
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hw
      have e : w = b⁻¹ * a ^ i * b := by rw [hi]; group
      rw [e, hconj']
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) _
  have hN2 : a ^ (orderOf a / 2) ≠ 1 :=
    pow_ne_one_of_lt_orderOf (by omega) (by omega)
  have hinA : ∀ w ∈ P, w * w = 1 → w ∈ Subgroup.zpowers a := by
    intro w hw hw2
    rw [← hcl, closure_pair_eq_sup_zpowers] at hw
    have hw' : w ∈ ((Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G) : Set G) := hw
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ (Subgroup.zpowers_le.mpr hbN)] at hw'
    obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_mul.mp hw'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    have hb2' : b ^ (2 : ℤ) = a ^ ((orderOf a / 2 : ℕ) : ℤ) := by
      rw [zpow_two, hb2, zpow_natCast]
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · rw [← two_mul, zpow_mul, hb2', ← zpow_mul]
      exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) _)
        (Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) _)
    · exfalso
      apply hN2
      have hw_eq : a ^ i * b ^ (2 * m + 1) = a ^ (i + ((orderOf a / 2 : ℕ) : ℤ) * m) * b := by
        rw [zpow_add_one, zpow_mul, hb2', ← zpow_mul, ← mul_assoc, ← zpow_add]
      rw [hw_eq] at hw2
      have e : ∀ j : ℤ, a ^ j * b * (a ^ j * b) = b * b := fun j => by
        calc a ^ j * b * (a ^ j * b) = a ^ j * (b * a ^ j * b⁻¹) * (b * b) := by group
          _ = b * b := by rw [hconj, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]
      rw [e, hb2] at hw2
      exact hw2
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hinA x hx hx2)
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hinA y hy hy2)
  exact zpow_eq_zpow_of_mul_self_eq_one hx2 hy2 hx1 hy1

theorem mem_normalizer_oddCoreOf_of_mem_normalizer [Finite G] {K : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (K : Set G)) :
    n ∈ Subgroup.normalizer (oddCoreOf K : Set G) := by
  have key : ∀ m ∈ Subgroup.normalizer (K : Set G), ∀ x ∈ oddCoreOf K,
      m * x * m⁻¹ ∈ oddCoreOf K := by
    intro m hm x hx
    obtain ⟨o, ho, rfl⟩ := hx
    let φ := normalizerConj K ⟨m, hm⟩
    have hnormal : ((classicalInvolutionOddCore ↥K).map φ.toMonoidHom).Normal :=
      Subgroup.Normal.map (classicalInvolutionOddCore_normal ↥K) φ.toMonoidHom φ.surjective
    have hodd : Odd (Nat.card ↥((classicalInvolutionOddCore ↥K).map φ.toMonoidHom)) := by
      rw [Subgroup.card_map_of_injective φ.injective]
      exact CFSG.ComponentClassification.OddCore.odd_card ↥K
    have hle : (classicalInvolutionOddCore ↥K).map φ.toMonoidHom ≤
        classicalInvolutionOddCore ↥K := by
      unfold classicalInvolutionOddCore
      exact le_sSup ⟨hnormal, hodd⟩
    exact ⟨φ o, hle ⟨o, ho, rfl⟩, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key n hn x, fun hx => ?_⟩
  have := key n⁻¹ (Subgroup.inv_mem _ hn) _ hx
  rwa [show n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x by group] at this

theorem conj_mem_cStar {K : Subgroup G} {n x : G} (hn : n ∈ Subgroup.normalizer (K : Set G))
    (hx : x ∈ cStar K) : n * x * n⁻¹ ∈ cStar K := by
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
  have hk' : (⟨n, hn⟩ * k * ⟨n, hn⟩⁻¹ : Subgroup.normalizer (K : Set G)) ∈
      ((oddCoreQuotientAut K).comp (normalizerConj K)).ker :=
    (MonoidHom.normal_ker _).conj_mem k hk ⟨n, hn⟩
  refine Subgroup.mem_map.mpr ⟨_, hk', ?_⟩
  simp only [map_mul, map_inv, Subgroup.coe_subtype]

theorem mem_centralizerModOdd_of_mem_cStar [Finite G] {H K : Subgroup G} {x : G} (hxH : x ∈ H)
    (hx : x ∈ cStar K) : x ∈ centralizerModOdd H K := by
  obtain ⟨hxN, h⟩ := mem_cStar_iff.mp hx
  refine ⟨hxH, hxN, mem_normalizer_oddCoreOf_of_mem_normalizer hxN, fun l hl => ?_⟩
  refine ⟨_, h ⟨l⁻¹, K.inv_mem hl⟩, ?_⟩
  simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, normalizerConj_apply_coe,
    commutatorElement_def]
  group

variable {p f : ℕ} [Fact p.Prime] [Finite G]

theorem cStarTwoRankOne_of_quaternion_of_le [IsSimpleGroup G] {K : Subgroup G} {z : G}
    {S : Sylow 2 G} {W : Subgroup G} (hd : Sec19Data p f K z S W)
    (hQ : IsQuaternionSub ((S : Subgroup G) ⊓
      centralizerModOdd (gammaGen (CoreAssembly.conjClass K) z) K))
    (hSX : (S : Subgroup G) ≤ gammaGen (CoreAssembly.conjClass K) z) : CStarTwoRankOne K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNC := normalizer_eq_centralizer_of_tight hd.tight.toTightBranch
  intro a ha b hb ha2 hb2 hab
  have haC : a ∈ Subgroup.centralizer ({z} : Set G) := hNC ▸ cStar_le_normalizer K ha
  have hbC : b ∈ Subgroup.centralizer ({z} : Set G) := hNC ▸ cStar_le_normalizer K hb
  have ha2' : a * a = 1 := by rw [← _root_.sq, ← ha2, pow_orderOf_eq_one]
  have hb2' : b * b = 1 := by rw [← _root_.sq, ← hb2, pow_orderOf_eq_one]
  have hE2 : IsPGroup 2 ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b) := by
    refine IsPGroup.iff_orderOf.mpr fun w => ?_
    obtain ⟨i, j, hij⟩ := exists_zpow_mul_zpow_of_mem_sup hab w.2
    have hw2 : (w : G) ^ 2 = 1 := by
      rw [← hij, _root_.sq]
      have hc : Commute a b := hab
      calc a ^ i * b ^ j * (a ^ i * b ^ j) = (a ^ i * a ^ i) * (b ^ j * b ^ j) := by
            rw [mul_assoc, ← mul_assoc (b ^ j), ((hc.zpow_zpow i j).symm.eq), mul_assoc,
              mul_assoc]
        _ = 1 := by
            rw [← zpow_add, ← zpow_add, ← two_mul, ← two_mul, zpow_mul, zpow_mul, zpow_two,
              zpow_two, ha2', hb2', one_zpow, one_zpow, one_mul]
    have hdvd : orderOf w ∣ 2 ^ 1 := by
      rw [pow_one, ← Subgroup.orderOf_coe]
      exact orderOf_dvd_of_pow_eq_one hw2
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact ⟨k, hk⟩
  have hEz : Subgroup.zpowers a ⊔ Subgroup.zpowers b ≤ Subgroup.centralizer ({z} : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr haC) (Subgroup.zpowers_le.mpr hbC)
  obtain ⟨c, hc, hcE⟩ := exists_conj_le_of_sylow_le S hd.hSz hEz hE2
  have hcN : c ∈ Subgroup.normalizer (K : Set G) := hNC ▸ hc
  have hca : c * a * c⁻¹ ∈ (S : Subgroup G) :=
    hcE (conj_mem_conjSub (Subgroup.mem_sup_left (Subgroup.mem_zpowers a)))
  have hcb : c * b * c⁻¹ ∈ (S : Subgroup G) :=
    hcE (conj_mem_conjSub (Subgroup.mem_sup_right (Subgroup.mem_zpowers b)))
  have ha' : c * a * c⁻¹ ∈ (S : Subgroup G) ⊓
      centralizerModOdd (gammaGen (CoreAssembly.conjClass K) z) K :=
    ⟨hca, mem_centralizerModOdd_of_mem_cStar (hSX hca) (conj_mem_cStar hcN ha)⟩
  have hb' : c * b * c⁻¹ ∈ (S : Subgroup G) ⊓
      centralizerModOdd (gammaGen (CoreAssembly.conjClass K) z) K :=
    ⟨hcb, mem_centralizerModOdd_of_mem_cStar (hSX hcb) (conj_mem_cStar hcN hb)⟩
  have hsq : ∀ x : G, x * x = 1 → c * x * c⁻¹ * (c * x * c⁻¹) = 1 := fun x hx => by
    calc c * x * c⁻¹ * (c * x * c⁻¹) = c * (x * x) * c⁻¹ := by group
      _ = 1 := by rw [hx]; group
  have hne : ∀ x : G, orderOf x = 2 → c * x * c⁻¹ ≠ 1 := fun x hx h1 => by
    have : x = 1 := by
      calc x = c⁻¹ * (c * x * c⁻¹) * c := by group
        _ = 1 := by rw [h1]; group
    rw [this, orderOf_one] at hx
    omega
  have h1 := IsQuaternionSub.eq_of_mul_self_eq_one hQ ha' hb' (hsq a ha2') (hsq b hb2')
    (hne a ha2) (hne b hb2)
  calc a = c⁻¹ * (c * a * c⁻¹) * c := by group
    _ = c⁻¹ * (c * b * c⁻¹) * c := by rw [h1]
    _ = b := by group

theorem cStarTwoRankOne_of_sec19 (h6 : C19_6Tmp p f) (h14 : C19_14Tmp p f)
    (h16 : C19_16Tmp p f) [IsSimpleGroup G] {K : Subgroup G} {z : G} {S : Sylow 2 G}
    {W : Subgroup G} (hd : Sec19Data p f K z S W) : CStarTwoRankOne K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine cStarTwoRankOne_of_quaternion_of_le hd ((h6 G K z S W hd).resolve_left
    (h14 G K z S W hd)) fun s hs => ?_
  rw [← xGroup_eq_gammaGen]
  exact h16 G K z hd.tight hd.ih s (hd.hSz hs) (S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hs))

theorem e2StarS3Tmp_of_targets (h6 : C19_6Tmp p f) (h14 : C19_14Tmp p f)
    (h16 : C19_16Tmp p f) (hW : W69 p f) (hIH : IHAllD p f) (h8 : IHInterface8 p)
    (hAE : AEmptyD p f) : E2StarS3Tmp p f := by
  intro G _ _ _ K z ht0 hA hih hc
  have ht := S19R.tightStd_of_tightBranchD ht0
  have hstand := ascStand_of_tightD hIH h8 hAE ht
  obtain ⟨Q₀, S, hRS, -, hSz, -⟩ := exists_sylow_setup ht
  obtain ⟨W, hWmem, hWS⟩ := hW G _ K hstand S
  exact cStarTwoRankOne_of_sec19 h6 h14 h16 ⟨ht, hA, hih, hc, ⟨Q₀, hRS⟩, hSz, hWmem, hWS⟩

end CFSG.ClassicalInvolution.Disconnected.AschTight
