module

public import CFSG.GH74.GLS.Bg.Pu5.L299Abs
public import CFSG.GH74.GLS.C3.Layer1.Thm1Quat
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankTwoCoverDihedral
public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneQuaternionRecognition
public import CFSG.GH74.E2.TermLeaves
public import CFSG.GH74.Uniqueness.SU.SU1BgNormalEp2
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Gen
public import CFSG.RankThree.PartOne.K1214.Basic
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.GLS.Bg.Pu5

open Subgroup CFSG.GH74.GLS CFSG.GH74.Uniqueness.SU

theorem dvd_of_pow_mul_eq {Y : Type} [Group Y] {a : Y} {k e : ℕ} (hk : 2 ≤ k) (ha : orderOf a = 2 ^ k)
    (he : e % 4 = 3) {i : ℕ} (hi : a ^ (e * i) = a ^ i) : 2 ^ (k - 1) ∣ i := by
  obtain ⟨u, hu1, hu2⟩ : ∃ u, e = 2 * u + 1 ∧ u % 2 = 1 := ⟨e / 2, by omega, by omega⟩
  have h1 : a ^ (2 * u * i) = 1 := by
    have h0 : a ^ (e * i) = a ^ (2 * u * i) * a ^ i := by
      rw [← pow_add]
      congr 1
      rw [hu1]
      ring
    rw [h0] at hi
    simpa using hi
  rw [← orderOf_dvd_iff_pow_eq_one, ha] at h1
  have hk' : 2 ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hk', mul_assoc] at h1
  have h2 : 2 ^ (k - 1) ∣ u * i := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1
  have hcop : Nat.Coprime (2 ^ (k - 1)) u :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by omega))
  exact hcop.dvd_of_dvd_mul_left h2

theorem isNonabelianMaximalClass_of_cyclic_index_two {Y : Type} [Group Y] [Finite Y] {a s : Y} {k e : ℕ}
    (hk : 2 ≤ k) (ha : orderOf a = 2 ^ k) (hidx : (zpowers a).index = 2) (hs2 : s * s = 1)
    (hconj : s * a * s⁻¹ = a ^ e) (he : e % 4 = 3) : IsNonabelianMaximalClassTwoGroup Y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  set A := zpowers a with hAdef
  have hcardA : Nat.card ↥A = 2 ^ k := by rw [hAdef, Nat.card_zpowers, ha]
  have hcardY : Nat.card Y = 2 ^ k * 2 := by
    have := Subgroup.card_mul_index A
    rw [hidx, hcardA] at this
    exact this.symm
  have hYp : IsPGroup 2 Y := IsPGroup.of_card (n := k + 1) (by rw [hcardY, pow_succ])
  have hsA : s ∉ A := by
    intro hs
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hs
    have hcomm : s * a = a * s := by
      rw [← hi]
      exact ((Commute.refl a).zpow_left i).eq
    have h1 : a ^ (e * 1) = a ^ 1 := by
      rw [mul_one, ← hconj, hsinv, hcomm, mul_assoc, hs2, mul_one, pow_one]
    have h2 := dvd_of_pow_mul_eq hk ha he h1
    have h3 : 2 ^ (k - 1) = 1 := Nat.dvd_one.1 h2
    have h4 : k - 1 = 0 := by
      have := Nat.pow_right_injective (le_refl 2) (show 2 ^ (k - 1) = 2 ^ 0 by simpa using h3)
      exact this
    omega
  set h : Y := a ^ (2 ^ (k - 1)) with hh
  have hhh : h * h = 1 := by
    rw [hh, ← pow_add, ← two_mul, ← pow_succ']
    have : k - 1 + 1 = k := by omega
    rw [this, ← ha]
    exact pow_orderOf_eq_one a
  have hA' : ∀ y ∈ A, y * s = s * y → y = 1 ∨ y = h := by
    intro y hy hys
    obtain ⟨i, hi⟩ := Submonoid.mem_powers_iff _ _ |>.1 (mem_powers_iff_mem_zpowers.2 hy)
    have h1 : a ^ (e * i) = a ^ i := by
      have h2 : s * a ^ i * s⁻¹ = (a ^ e) ^ i := by rw [← hconj, conj_pow]
      rw [← pow_mul] at h2
      have h3 : s * y * s⁻¹ = y := by rw [← hys, mul_assoc, mul_inv_cancel, mul_one]
      rw [← hi] at h3
      rw [h2] at h3
      exact h3
    obtain ⟨j, hj⟩ := dvd_of_pow_mul_eq hk ha he h1
    have hy' : y = h ^ j := by rw [← hi, hj, pow_mul]
    rcases Nat.even_or_odd j with ⟨m, hm⟩ | ⟨m, hm⟩
    · left
      rw [hy', hm, ← two_mul, pow_mul, sq, hhh, one_pow]
    · right
      rw [hy', hm, pow_succ, pow_mul, sq, hhh, one_pow, one_mul]
  have hcen : ∀ y : Y, y * s = s * y → y = 1 ∨ y = h ∨ y = s ∨ y = s * h := by
    intro y hys
    by_cases hyA : y ∈ A
    · rcases hA' y hyA hys with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
    · have hsy : s * y ∈ A := by
        have hsy' : s⁻¹ * y ∈ A := by
          rw [Subgroup.mul_mem_iff_of_index_two hidx, inv_mem_iff]
          exact iff_of_false hsA hyA
        rwa [hsinv] at hsy'
      have hcom : (s * y) * s = s * (s * y) := by
        calc (s * y) * s = s * (y * s) := mul_assoc _ _ _
          _ = s * (s * y) := by rw [hys]
      rcases hA' (s * y) hsy hcom with h1 | h1
      · right; right; left
        have : s * (s * y) = s * 1 := by rw [h1]
        rw [← mul_assoc, hs2, one_mul, mul_one] at this
        exact this
      · right; right; right
        have : s * (s * y) = s * h := by rw [h1]
        rw [← mul_assoc, hs2, one_mul] at this
        exact this
  have hc4 : Nat.card ↥(centralizer ({s} : Set Y)) ≤ 2 ^ 2 := by
    have hmem : ∀ y : ↥(centralizer ({s} : Set Y)), (y : Y) ∈ ({1, h, s, s * h} : Finset Y) := by
      intro y
      have hy := Subgroup.mem_centralizer_singleton_iff.1 y.2
      rcases hcen _ hy with h1 | h1 | h1 | h1 <;> simp [h1]
    have hinj : Function.Injective (fun y : ↥(centralizer ({s} : Set Y)) =>
        (⟨(y : Y), hmem y⟩ : ↥({1, h, s, s * h} : Finset Y))) := by
      intro y y' hyy
      have h' := congrArg Subtype.val hyy
      exact Subtype.ext h'
    have hfin : Nat.card ↥({1, h, s, s * h} : Finset Y) = ({1, h, s, s * h} : Finset Y).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    have hle := Nat.card_le_card_of_injective _ hinj
    rw [hfin] at hle
    have h4' : ({1, h, s, s * h} : Finset Y).card ≤ 4 := Finset.card_le_four
    norm_num
    omega
  have h8 : 2 ^ 3 ≤ Nat.card Y := by
    rw [hcardY]
    calc 2 ^ 3 = 2 ^ 2 * 2 := by norm_num
      _ ≤ 2 ^ k * 2 := Nat.mul_le_mul_right 2 (Nat.pow_le_pow_right (by norm_num) hk)
  obtain ⟨m, hm, hl⟩ := SU1.b_maximalClass_of_small_centralizer 2 Nat.prime_two Y hYp h8 s hc4
  have hm3 : 3 ≤ m := by
    by_contra hcon
    push Not at hcon
    have : 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h8' : 2 ^ 3 ≤ 2 ^ m := hm ▸ h8
    omega
  have hnab : ¬ IsMulCommutative Y := by
    intro hcomm
    have : Group.IsNilpotent Y := hYp.isNilpotent
    have h1 : Group.nilpotencyClass Y ≤ 1 := Group.IsNilpotent.nilpotencyClass_le_one_iff.mpr hcomm
    apply hl
    rw [Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le]
    omega
  exact Stage1.Thm3.Sec6.B.maxClass_of_lcs Y hYp hnab m hm hl

theorem isNonabelianMaximalClass_dihedral {m : ℕ} (hm : 2 ≤ m) :
    IsNonabelianMaximalClassTwoGroup (DihedralGroup (2 ^ m)) := by
  have : NeZero (2 ^ m) := ⟨by positivity⟩
  refine isNonabelianMaximalClass_of_cyclic_index_two (a := DihedralGroup.r 1) (s := DihedralGroup.sr 0)
    (k := m) (e := 2 ^ m - 1) hm ?_ ?_ ?_ ?_ ?_
  · rw [DihedralGroup.orderOf_r_one]
  · exact CFSG.ProperTwoGeneratedCore.Lemma37.dihedral_index_zpowers_r_one
  · exact DihedralGroup.sr_mul_self 0
  · rw [DihedralGroup.r_one_pow, DihedralGroup.inv_sr, DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr]
    congr 1
    have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    rw [Nat.cast_sub h1]
    have : ((2 ^ m : ℕ) : ZMod (2 ^ m)) = 0 := ZMod.natCast_self _
    push_cast at this ⊢
    rw [this]
    ring
  · have h1 : 2 ^ 2 ∣ 2 ^ m := pow_dvd_pow 2 hm
    have h2 : 0 < 2 ^ m := by positivity
    omega

theorem isNonabelianMaximalClass_semidihedral {n : ℕ} (hn : 4 ≤ n) :
    IsNonabelianMaximalClassTwoGroup (CFSG.Open.SemidihedralGroup n) := by
  have hn3 : 3 ≤ n := by omega
  have := CFSG.Semidihedral.presentation_finite n hn3
  refine isNonabelianMaximalClass_of_cyclic_index_two (a := CFSG.Semidihedral.r n)
    (s := CFSG.Semidihedral.s n) (k := n - 1) (e := 2 ^ (n - 2) - 1) (by omega) ?_ ?_ ?_ ?_ ?_
  · rw [CFSG.Semidihedral.orderOf_r n hn3]
    rfl
  · exact CFSG.Semidihedral.rotation_index n hn3
  · have h := CFSG.Semidihedral.s_sq n
    rwa [sq] at h
  · exact CFSG.Semidihedral.s_conj_r n
  · have h1 : 2 ^ 2 ∣ 2 ^ (n - 2) := pow_dvd_pow 2 (by omega)
    have h2 : 0 < 2 ^ (n - 2) := by positivity
    omega

theorem isNonabelianMaximalClass_quaternion {e : ℕ} (he : 1 ≤ e) :
    IsNonabelianMaximalClassTwoGroup (QuaternionGroup (2 ^ e)) := by
  obtain ⟨hcl, hcard⟩ := C3.Layer1.Thm1.quaternionGroup_class e he
  have hp : IsPGroup 2 (QuaternionGroup (2 ^ e)) := IsPGroup.of_card hcard
  have hnil : Group.IsNilpotent (QuaternionGroup (2 ^ e)) := hp.isNilpotent
  refine ⟨hp, ?_, hnil, ?_⟩
  · intro hc
    have := Group.IsNilpotent.nilpotencyClass_le_one_iff.mpr hc
    omega
  · rw [hcl, hcard]

theorem two_le_pRank_of_not_cyclic_of_not_maxClass {Y : Type} [Group Y] [Finite Y] (hY : IsPGroup 2 Y)
    (hnc : ¬ IsCyclic Y) (hnm : ¬ IsNonabelianMaximalClassTwoGroup Y) : 2 ≤ CFSG.pRank 2 Y := by
  by_contra hlt
  push Not at hlt
  have hrank : CFSG.DisconnectedInvolutionGraph.Helpers.NoCommutingDistinctInvolutions Y := by
    intro a b hab
    by_contra hne
    have := CFSG.GH74.E2.two_le_pRank_of_commuting_involutions a.2 b.2
      (fun h => hne (Subtype.ext h)) hab
    omega
  rcases CFSG.DisconnectedInvolutionGraph.Helpers.rank_one_two_cyclic_or_quaternion hY hrank with
    hcyc | ⟨e, he, ⟨ι⟩⟩
  · exact hnc hcyc
  · exact hnm (isNonabelianMaximalClassTwoGroup_of_mulEquiv ι (isNonabelianMaximalClass_quaternion he))

theorem isPGroup_sup_zpowers_of_normalizes {G : Type} [Group G] [Finite G] {Y : Subgroup G} {v : G}
    (hY : IsPGroup 2 ↥Y) (hvN : v ∈ normalizer (Y : Set G)) (hv2 : ∃ k : ℕ, v ^ 2 ^ k = 1) :
    IsPGroup 2 ↥(Y ⊔ zpowers v) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hv2
  have hprod := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer (A := Y)
    (B := zpowers v) (zpowers_le.2 hvN)
  obtain ⟨a, ha⟩ := hY.exists_card_eq
  have hxo : orderOf v ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hxo
  rw [Nat.card_zpowers, hb, ha, ← pow_add] at hprod
  have hdvd : Nat.card ↥(Y ⊔ zpowers v) ∣ 2 ^ (a + b) := Dvd.intro _ hprod
  obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  exact IsPGroup.of_card hc

theorem exists_four_normalized {G : Type} [Group G] [Finite G] {Y : Subgroup G} {v : G}
    (hY : IsPGroup 2 ↥Y) (hvN : v ∈ normalizer (Y : Set G)) (hv2 : ∃ k : ℕ, v ^ 2 ^ k = 1)
    (hnc : ¬ IsCyclic ↥Y) (hnm : ¬ IsNonabelianMaximalClassTwoGroup ↥Y) :
    ∃ U : Subgroup G, U ≤ Y ∧ Nat.card ↥U = 4 ∧ (∀ u ∈ U, u * u = 1) ∧ v ∈ normalizer (U : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P : Subgroup G := Y ⊔ zpowers v with hP
  have hP2 : IsPGroup 2 ↥P := isPGroup_sup_zpowers_of_normalizes hY hvN hv2
  have hYP : Y ≤ P := le_sup_left
  have hvP : v ∈ P := Subgroup.mem_sup_right (Subgroup.mem_zpowers v)
  have hnormal : (Y.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYP).2
      (sup_le Subgroup.le_normalizer (zpowers_le.2 hvN))
  have hrank : 2 ≤ CFSG.pRank 2 ↥(Y.subgroupOf P) := by
    rw [Stage1.Thm2.Recip.pRank_eq_of_mulEquiv' (Subgroup.subgroupOfEquivOfLe hYP)]
    exact two_le_pRank_of_not_cyclic_of_not_maxClass hY hnc hnm
  have hnm' : ¬ IsNonabelianMaximalClassTwoGroup ↥(Y.subgroupOf P) := fun h =>
    hnm (isNonabelianMaximalClassTwoGroup_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hYP) h)
  rcases SU1.b_normal_Ep2 2 Nat.prime_two ↥P hP2 (Y.subgroupOf P) hnormal hrank with
    ⟨E, hEn, hEY, hEel, hE4⟩ | ⟨-, ⟨m, hm1, ⟨e⟩⟩ | ⟨n, hn4, ⟨e⟩⟩⟩
  · refine ⟨E.map P.subtype, ?_, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hx
      exact Subgroup.mem_subgroupOf.1 (hEY he)
    · rw [Subgroup.card_map_of_injective P.subtype_injective, hE4]
      norm_num
    · rintro _ ⟨e, he, rfl⟩
      have h2 := ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 E).1 hEel).2 e he
      have h3 : ((e : ↥P) : G) * (e : G) = 1 := by
        rw [← sq]
        exact congrArg Subtype.val h2
      simpa using h3
    · rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨e, he, rfl⟩
        exact ⟨⟨v, hvP⟩ * e * ⟨v, hvP⟩⁻¹, hEn.conj_mem e he _, by simp⟩
      · rintro ⟨e, he, hex⟩
        refine ⟨⟨v, hvP⟩⁻¹ * e * ⟨v, hvP⟩, by simpa using hEn.conj_mem e he ⟨v, hvP⟩⁻¹, ?_⟩
        have : (e : G) = v * x * v⁻¹ := by simpa using hex
        simp only [Subgroup.coe_subtype, Subgroup.coe_mul, InvMemClass.coe_inv, this]
        group
  · by_cases hm2 : 2 ≤ m
    · exact absurd (isNonabelianMaximalClassTwoGroup_of_mulEquiv e.symm
        (isNonabelianMaximalClass_dihedral hm2)) hnm'
    · have hm : m = 1 := by omega
      subst hm
      have hcard : Nat.card ↥Y = 4 := by
        rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYP).toEquiv, Nat.card_congr e.toEquiv]
        simp
      refine ⟨Y, le_refl _, hcard, ?_, ?_⟩
      · intro u hu
        have h1 : ∀ g : DihedralGroup (2 ^ 1), g * g = 1 := by decide
        have h2 := h1 (e ((Subgroup.subgroupOfEquivOfLe hYP).symm ⟨u, hu⟩))
        have h3 := congrArg (fun g => (Subgroup.subgroupOfEquivOfLe hYP) (e.symm g)) h2
        simpa using congrArg Subtype.val h3
      · exact hvN
  · exact absurd (isNonabelianMaximalClassTwoGroup_of_mulEquiv e.symm
      (isNonabelianMaximalClass_semidihedral hn4)) hnm'

end CFSG.GH74.GLS.Bg.Pu5
