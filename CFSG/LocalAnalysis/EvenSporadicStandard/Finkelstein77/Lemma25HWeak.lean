module

public import CFSG.GH74.Uniqueness.SU.SU1BgNormalEp2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.Lemma25Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.Lemma25HBig
public import CFSG.LocalAnalysis.ComponentClassification.Foote5HallWeak

public section

namespace CFSG.EvenSporadicStandard.Finkelstein77.Lemma25HProof

open Subgroup CFSG CFSG.ABGLocalTools CFSG.ComponentClassification
  CFSG.ComponentClassification.FooteLit.F5 CFSG.ComponentClassification.Foote5.HallGen
  CFSG.ComponentClassification.Asc76X CFSG.ComponentClassification.AschbacherTheorem3
  CFSG.EvenSporadicStandard.Finkelstein77.Lemma25Proof

variable {G : Type} [Group G]

theorem isDihedral_or_isSemidihedral_of_inv_le [Finite G] {D S₀ : Subgroup G}
    (hD : IsDihedralTwoGroup D) (h16 : 16 ≤ Nat.card D) (hDS : D ≤ S₀)
    (hp : IsPGroup 2 S₀) (hinv : ∀ x ∈ S₀, x * x = 1 → x ∈ D) :
    IsDihedralTwoGroup S₀ ∨ IsSemidihedralTwoGroup S₀ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn, ⟨eD⟩⟩ := id hD
  have : NeZero (2 ^ (n - 1)) := ⟨by positivity⟩
  obtain ⟨c, hcD, hco, hcard, hDc⟩ := data_of_mulEquiv eD
  have hpos : 0 < 2 ^ (n - 1) := by positivity
  have hm : 3 ≤ n - 1 := by
    by_contra h
    have : 2 ^ (n - 1) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨u, huD, hu⟩ : ∃ u ∈ D, u ∉ zpowers c := by
    by_contra hall
    push Not at hall
    have hle : D ≤ zpowers c := hall
    have := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, hco, hcard] at this
    omega
  have hu2 : u * u = 1 := ((hDc u huD).resolve_left hu).1
  have huc : u * c * u⁻¹ = c⁻¹ := ((hDc u huD).resolve_left hu).2
  have hu1 : u ≠ 1 := fun h => hu (h ▸ one_mem _)
  set z : G := c ^ (2 ^ (n - 2)) with hz
  have hcpow : c ^ (2 ^ (n - 1)) = 1 := by rw [← hco]; exact pow_orderOf_eq_one c
  have hz2 : z * z = 1 := by
    rw [hz, ← pow_add, ← two_mul, ← pow_succ' 2 (n - 2), show n - 2 + 1 = n - 1 by omega]
    exact hcpow
  have hz1 : z ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hco] at this
    have h2 : 2 ^ (n - 1) ≤ 2 ^ (n - 2) := Nat.le_of_dvd (by positivity) this
    have h3 : 2 ^ (n - 2) < 2 ^ (n - 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hzD : z ∈ D := pow_mem hcD _
  have hzc : z ∈ zpowers c := pow_mem (mem_zpowers c) _
  have hzu : z ≠ u := fun h => hu (h ▸ hzc)
  have hcomm : z * u = u * z := by
    have h1 : u * z * u⁻¹ = z⁻¹ := by
      rw [hz, ← conj_pow, huc, inv_pow]
    have h2 : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
    rw [h2] at h1
    calc z * u = (u * z * u⁻¹) * u := by rw [h1]
      _ = u * z := by group
  have hb : BareDatum 0 z u := bareDatum_zero hz2 hz1 hu2 hu1 hzu hcomm
  have hE₀D : dsub z u ≤ D := sup_le (zpowers_le.mpr hzD) (zpowers_le.mpr huD)
  have hE₀S : dsub z u ≤ S₀ := hE₀D.trans hDS
  have hE₀sq : ∀ x ∈ dsub z u, x * x = 1 := by
    intro x hx
    obtain ⟨i, rfl | rfl⟩ := (hb.mem_dsub_iff).mp hx
    · rw [← (Commute.refl z).mul_zpow, hz2, one_zpow]
    · exact hb.refl_sq i
  have hE₀card : Nat.card (dsub z u) = 4 := by
    obtain ⟨φ⟩ := hb.nonempty_mulEquiv_dihedral
    rw [Nat.card_congr φ.toEquiv, DihedralGroup.nat_card]
    norm_num
  have hrank : ∃ E : Subgroup ↥S₀, E ≤ ⊤ ∧ Open.IsElemAbelian 2 E ∧ Nat.card E = 2 ^ 2 := by
    refine ⟨(dsub z u).subgroupOf S₀, le_top, isElemAbelian_of_mul_self (fun x hx => ?_), ?_⟩
    · exact Subtype.ext (by simpa using hE₀sq _ (mem_subgroupOf.mp hx))
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₀S).toEquiv, hE₀card]
      norm_num
  have hinvc : ∀ a ∈ zpowers c, a * a = 1 → a = 1 ∨ a = z := by
    intro a ha ha2
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
    have h1 : c ^ (i + i) = 1 := by rw [zpow_add]; exact ha2
    have h2 : ((2 ^ (n - 1) : ℕ) : ℤ) ∣ i + i := by
      rw [← hco]; exact orderOf_dvd_iff_zpow_eq_one.mpr h1
    obtain ⟨j, hj⟩ : ((2 ^ (n - 2) : ℕ) : ℤ) ∣ i := by
      refine Int.dvd_of_mul_dvd_mul_left (a := 2) (by norm_num) ?_
      have e1 : ((2 ^ (n - 1) : ℕ) : ℤ) = 2 * ((2 ^ (n - 2) : ℕ) : ℤ) := by
        rw [show n - 1 = (n - 2) + 1 by omega]; push_cast; ring
      rw [e1, ← two_mul] at h2
      exact h2
    have hcj : c ^ i = z ^ j := by
      rw [hj, zpow_mul, hz, zpow_natCast]
    rw [hcj]
    exact zpow_eq_one_or_self hz2 j
  have hstar : ∀ E : Subgroup ↥S₀, E.Normal → E ≤ ⊤ → Open.IsElemAbelian 2 E →
      Nat.card E = 2 ^ 2 → False := by
    intro E hEn _ hEab hEcard
    set E' : Subgroup G := E.map S₀.subtype with hE'
    have hE'card : Nat.card E' = 4 := by
      rw [hE', Subgroup.card_map_of_injective S₀.subtype_injective, hEcard]
      norm_num
    have hE'sq : ∀ x ∈ E', x * x = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      have : x ^ 2 = 1 := hEab.2 x hx
      simpa [sq] using congrArg Subtype.val this
    have hE'D : ∀ x ∈ E', x ∈ D := by
      rintro _ ⟨x, hx, rfl⟩
      exact hinv _ x.2 (hE'sq _ ⟨x, hx, rfl⟩)
    obtain ⟨a, haE', ha1, haz⟩ := Hall32.exists_mem_ne_ne hE'card 1 z
    have haD : a ∈ D := hE'D a haE'
    have ha2 : a * a = 1 := hE'sq a haE'
    have hna : a ∉ zpowers c := fun hac => (hinvc a hac ha2).elim ha1 haz
    have haI : a * c * a⁻¹ = c⁻¹ := ((hDc a haD).resolve_left hna).2
    have hcS : c ∈ S₀ := hDS hcD
    have hcconj : c * a * c⁻¹ ∈ E' := by
      obtain ⟨a', ha'E, rfl⟩ := haE'
      have := hEn.conj_mem a' ha'E ⟨c, hcS⟩
      exact ⟨_, this, by simp⟩
    have hc2 : c * c ∈ E' := by
      have h1 : (c * a * c⁻¹) * a⁻¹ ∈ E' := mul_mem hcconj (inv_mem haE')
      have h3 : a * c⁻¹ * a⁻¹ = c := by
        calc a * c⁻¹ * a⁻¹ = (a * c * a⁻¹)⁻¹ := by group
          _ = c := by rw [haI]; simp
      have h2 : (c * a * c⁻¹) * a⁻¹ = c * c := by
        calc (c * a * c⁻¹) * a⁻¹ = c * (a * c⁻¹ * a⁻¹) := by group
          _ = c * c := by rw [h3]
      rwa [h2] at h1
    have hc4 : c * c * (c * c) = 1 := hE'sq _ hc2
    have hdvd : orderOf c ∣ 4 :=
      orderOf_dvd_of_pow_eq_one
        (by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq, sq]; exact hc4)
    rw [hco] at hdvd
    have h4 : 2 ^ (n - 1) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    have h8 : 2 ^ 3 ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) hm
    omega
  rcases CFSG.GH74.Uniqueness.SU.SU1.dihedral_or_semidihedral_of_no_normal_four (P := ↥S₀) hp
      (Q := ⊤) hstar hrank with ⟨m, hm', ⟨φ⟩⟩ | ⟨n', hn', ⟨φ⟩⟩
  · left
    exact ⟨m + 1, by omega, ⟨by rw [Nat.add_sub_cancel]; exact Subgroup.topEquiv.symm.trans φ⟩⟩
  · right
    exact ⟨n', hn', ⟨Subgroup.topEquiv.symm.trans φ⟩⟩

theorem pow_mem_centralizer_of_weak [Finite G] {D S₀ : Subgroup G}
    (hD : IsDihedralTwoGroup D) (h8 : 8 ≤ Nat.card D) (hDS₀ : D ≤ S₀)
    (hinv : ∀ x ∈ S₀, x * x = 1 → x ∈ D) (hcard : Nat.card S₀ ≤ 2 * Nat.card D) :
    ∀ m ∈ normalizer (S₀ : Set G), ∃ k : ℕ, m ^ (2 ^ k) ∈ centralizer (S₀ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn, ⟨e⟩⟩ := id hD
  have hcardD : Nat.card D = 2 * 2 ^ (n - 1) := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have : NeZero (2 ^ (n - 1)) := ⟨by positivity⟩
  obtain ⟨c, hcD, hco, hDc, hDd⟩ := data_of_mulEquiv e
  rw [← hco] at hDc
  have key : ∀ m ∈ normalizer (S₀ : Set G), ∀ d ∈ D, m * d * m⁻¹ ∈ D := by
    intro m hm d hd
    obtain ⟨a, ha, b, hb, ha2, hb2, rfl⟩ := exists_mul hDd hDc hd
    have hconj : ∀ x ∈ D, x * x = 1 → m * x * m⁻¹ ∈ D := fun x hx hx2 =>
      hinv _ ((mem_normalizer_iff.mp hm x).mp (hDS₀ hx)) (by
        rw [show m * x * m⁻¹ * (m * x * m⁻¹) = m * (x * x) * m⁻¹ by group, hx2]; group)
    rw [show m * (a * b) * m⁻¹ = (m * a * m⁻¹) * (m * b * m⁻¹) by group]
    exact mul_mem (hconj a ha ha2) (hconj b hb hb2)
  have hND : ∀ m ∈ normalizer (S₀ : Set G), m ∈ normalizer (D : Set G) := by
    intro m hm
    refine mem_normalizer_iff.mpr fun d => ⟨key m hm d, fun h => ?_⟩
    have := key m⁻¹ (inv_mem hm) _ h
    rwa [inv_inv, show m⁻¹ * (m * d * m⁻¹) * m = d by group] at this
  have hAut := isPGroup_mulAut_of_dihedral hD h8
  intro m hm
  obtain ⟨a, ha⟩ := pow_mem_centralizer_of_isPGroup_mulAut hAut (hND m hm)
  set m' := m ^ (2 ^ a) with hm'
  have hm'N : m' ∈ normalizer (S₀ : Set G) := pow_mem hm _
  have hcomm : ∀ d ∈ D, m' * d = d * m' := fun d hd => (mem_centralizer_iff.mp ha d hd).symm
  refine ⟨a + n, ?_⟩
  rw [pow_add, pow_mul, mem_centralizer_iff]
  intro s hs
  set s' := m' * s * m'⁻¹ with hs'
  have hs'S : s' ∈ S₀ := (mem_normalizer_iff.mp hm'N s).mp hs
  have hd : s⁻¹ * s' ∈ D := by
    by_cases hsD : s ∈ D
    · rw [hs', hcomm s hsD, mul_inv_cancel_right, inv_mul_cancel]
      exact one_mem _
    · have hs'D : s' ∉ D := fun h => hsD (by
        have : s = m'⁻¹ * s' * m' := by rw [hs']; group
        rw [this, show m'⁻¹ * s' * m' = m'⁻¹ * (s' * m') by group, ← hcomm s' h]
        group
        exact h)
      exact inv_mul_mem_of_card_le hDS₀ hcard hs hs'S hsD hs'D
  set d := s⁻¹ * s' with hddef
  have hpow : ∀ j : ℕ, m' ^ j * s * (m' ^ j)⁻¹ = s * d ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hdj : m' * d ^ j * m'⁻¹ = d ^ j := by
        rw [hcomm _ (pow_mem hd j), mul_inv_cancel_right]
      calc m' ^ (j + 1) * s * (m' ^ (j + 1))⁻¹ = m' * (m' ^ j * s * (m' ^ j)⁻¹) * m'⁻¹ := by
            group
        _ = (m' * s * m'⁻¹) * (m' * d ^ j * m'⁻¹) := by rw [ih]; group
        _ = s * d ^ (j + 1) := by
          rw [hdj, ← hs', show s' = s * d by rw [hddef]; group, pow_succ', mul_assoc]
  have hd1 : d ^ (2 ^ n) = 1 := by
    have h1 := Subgroup.orderOf_dvd_natCard D hd
    rw [hcardD, show 2 * 2 ^ (n - 1) = 2 ^ n by
      rw [← pow_succ']; congr 1; omega] at h1
    exact orderOf_dvd_iff_pow_eq_one.mp h1
  have h := hpow (2 ^ n)
  rw [hd1, mul_one] at h
  calc s * m' ^ 2 ^ n = m' ^ 2 ^ n * s * (m' ^ 2 ^ n)⁻¹ * m' ^ 2 ^ n := by rw [h]
    _ = m' ^ 2 ^ n * s := by group

theorem isDihedral_or_isSemidihedral_of_weak [Finite G]
    {D : Subgroup G} (hD : IsDihedralTwoGroup D) (h16 : 16 ≤ Nat.card D)
    (hW : HallWeakConclusion D) {P : Subgroup G}
    (hP : IsSylowOf 2 P (normalClosure (D : Set G))) :
    IsDihedralTwoGroup P ∨ IsSemidihedralTwoGroup P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀, T, hT, hDS₀, hS₀T, hsc, hinv, hcard⟩ := hW
  have h8 : 8 ≤ Nat.card D := by omega
  obtain ⟨k, hk⟩ := sylow_conj_eq_inf_of_B3 hT hDS₀ hS₀T hsc
    (pow_mem_centralizer_of_weak hD h8 hDS₀ hinv hcard) hP
  set N : Subgroup G := normalClosure (D : Set G) with hN
  set Pk : Subgroup G := P.map (MulAut.conj k⁻¹).toMonoidHom with hPk
  have hPkS : Pk ≤ S₀ := hk ▸ inf_le_left
  have hDN : D ≤ N := fun d hd => subset_normalClosure hd
  have hDPk : D ≤ Pk := hk ▸ le_inf hDS₀ hDN
  have e : P ≃* Pk := mulEquivConj P k
  by_cases hPD : Pk = D
  · exact Or.inl (isDihedral_of_mulEquiv (e.trans (MulEquiv.subgroupCongr hPD)) hD)
  · have hSPk : Pk = S₀ := by
      refine Subgroup.eq_of_le_of_card_ge hPkS ?_
      obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le hDPk
      have hDpos : 0 < Nat.card D := Nat.card_pos
      have hc1 : c ≠ 1 := by
        intro h
        apply hPD
        exact (Subgroup.eq_of_le_of_card_ge hDPk (by rw [hc, h, mul_one])).symm
      have hc0 : c ≠ 0 := by
        rintro rfl
        have : 0 < Nat.card Pk := Nat.card_pos
        rw [hc, mul_zero] at this
        exact lt_irrefl _ this
      have hc2 : 2 ≤ c := by omega
      calc Nat.card S₀ ≤ 2 * Nat.card D := hcard
        _ ≤ c * Nat.card D := Nat.mul_le_mul_right _ hc2
        _ = Nat.card Pk := by rw [hc, mul_comm]
    rcases isDihedral_or_isSemidihedral_of_inv_le hD h16 hDS₀ (hT.isPGroup.to_le hS₀T) hinv with
      h | h
    · exact Or.inl (isDihedral_of_mulEquiv (e.trans (MulEquiv.subgroupCongr hSPk)) h)
    · exact Or.inr (isSemidihedral_of_mulEquiv (e.trans (MulEquiv.subgroupCongr hSPk)) h)

end CFSG.EvenSporadicStandard.Finkelstein77.Lemma25HProof
