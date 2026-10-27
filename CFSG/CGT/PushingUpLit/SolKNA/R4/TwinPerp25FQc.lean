module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25FQa
public import CFSG.ClassicalInvolution.Asc77.AscT7U7
public import CFSG.ClassicalInvolution.Asc77.AscT7U1

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.C2516

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T7F2
open CFSG.ClassicalInvolution.Asc77.T7F2.Out

variable {G : Type} [Group G] [Finite G] {R N : Subgroup G} {x y z : G} {n : ℕ}

theorem isFAut_of_pm_action {n' : ℕ} (s : Setting R N x y (n' + 2)) (hN2 : IsPGroup 2 ↥N) {m : G}
    (hmN : m ∈ N) {i j : ℤ} (hx : m * x * m⁻¹ = x ^ i) (hy : m * y * m⁻¹ = y * x ^ j)
    (hi : (2 : ℤ) ^ (n' + 2 + 1) ∣ i - (1 + 2 ^ (n' + 2))) (hj : (2 : ℤ) ^ (n' + 2) ∣ j) :
    IsFAut R m := by
  have c := s.coord
  have hx' : m * x * m⁻¹ = x ^ ((1 : ℤ) + 2 ^ (n' + 2)) := by
    rw [hx, c.zpow_eq_iff]
    exact hi
  obtain ⟨k, hk⟩ := hj
  have hxj : x ^ j = 1 ∨ x ^ j = x ^ (2 ^ (n' + 2)) := by
    rcases Int.even_or_odd' k with ⟨k', rfl | rfl⟩
    · left
      have h0 : x ^ j = x ^ (0 : ℤ) := by
        rw [c.zpow_eq_iff, hk, sub_zero]
        exact ⟨k', by ring⟩
      rwa [zpow_zero] at h0
    · right
      rw [hk, ← zpow_natCast, c.zpow_eq_iff]
      refine ⟨k', ?_⟩
      push_cast
      ring
  refine T7U.isFAut_of_action_pm s hN2 hmN hx' ?_
  rcases hxj with h | h
  · left
    rw [hy, h, mul_one]
  · right
    rw [hy, h]

theorem classify_fAut (s : Setting R N x y n) (hn : 2 ≤ n) (hN2 : IsPGroup 2 ↥N)
    (hqR : IsQuatSub R) (hz : IsUniqueInvolution R z) {m : G} (hmN : m ∈ N) (hm2 : m * m = 1)
    {i : ℤ} (hx : m * x * m⁻¹ = x ^ i)
    (hi : (2 : ℤ) ^ (n + 1) ∣ i - (1 + 2 ^ n) ∨ (2 : ℤ) ^ (n + 1) ∣ i - (-1 + 2 ^ n)) :
    ∃ w ∈ R, (m * w) * (m * w) = 1 ∧ IsFAut R (m * w) := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
  have c := s.coord
  obtain ⟨i', j, hodd, hx', hy'⟩ := s.coord_of_mem hmN
  have hii : (2 : ℤ) ^ (n' + 2 + 1) ∣ i - i' := by
    have := c.zpow_eq_iff.mp (hx.symm.trans hx')
    exact this
  obtain ⟨hc1, hc2⟩ := involution_cond c hm2 hx' hy'
  set P : ℤ := (2 : ℤ) ^ n' with hP
  have h2 : (2 : ℤ) ^ (n' + 2) = 4 * P := by rw [hP]; ring
  have h3 : (2 : ℤ) ^ (n' + 2 + 1) = 8 * P := by rw [hP]; ring
  rw [h3] at hii hc1 hc2
  rw [h2, h3] at hi
  have hP0 : 0 < P := by positivity
  have hPodd : IsCoprime (2 : ℤ) P → True := fun _ => trivial
  rcases hi with hA | hB
  ·
    have hA' : 8 * P ∣ i' - (1 + 4 * P) := by
      have := dvd_sub hA hii
      have e : i - (1 + 4 * P) - (i - i') = i' - (1 + 4 * P) := by ring
      rwa [e] at this
    obtain ⟨a, ha⟩ := hA'
    have hi' : i' = 1 + 4 * P + 8 * P * a := by linarith
    obtain ⟨b, hb⟩ := hc2
    have hjb : j * (1 + 2 * P + 4 * P * a) = 4 * P * b := by
      have e : j * (i' + 1) = 2 * (j * (1 + 2 * P + 4 * P * a)) := by rw [hi']; ring
      have : 2 * (j * (1 + 2 * P + 4 * P * a)) = 2 * (4 * P * b) := by
        rw [← e, hb]; ring
      linarith
    have hcop : IsCoprime (1 + 2 * P + 4 * P * a) (4 * P) := by
      have hodd' : Odd (1 + 2 * P + 4 * P * a) := ⟨P + 2 * P * a, by ring⟩
      have h2c : IsCoprime (2 : ℤ) (1 + 2 * P + 4 * P * a) := Int.isCoprime_two_left.mpr hodd'
      have hpow : IsCoprime ((2 : ℤ) ^ (n' + 2)) (1 + 2 * P + 4 * P * a) := h2c.pow_left
      rw [h2] at hpow
      exact hpow.symm
    have hj4 : 4 * P ∣ j := by
      have : 4 * P ∣ j * (1 + 2 * P + 4 * P * a) := ⟨b, hjb⟩
      exact hcop.symm.dvd_of_dvd_mul_right this
    have hiA : (2 : ℤ) ^ (n' + 2 + 1) ∣ i' - (1 + 2 ^ (n' + 2)) := by
      rw [h2, h3]; exact ⟨a, by rw [hi']; ring⟩
    have hF := isFAut_of_pm_action s hN2 hmN hx' hy' hiA (by rw [h2]; exact hj4)
    exact ⟨1, R.one_mem, by simpa using hm2, by simpa using hF⟩
  ·
    have hB' : 8 * P ∣ i' - (-1 + 4 * P) := by
      have := dvd_sub hB hii
      have e : i - (-1 + 4 * P) - (i - i') = i' - (-1 + 4 * P) := by ring
      rwa [e] at this
    obtain ⟨a, ha⟩ := hB'
    have hi' : i' = -1 + 4 * P + 8 * P * a := by linarith
    obtain ⟨b, hb⟩ := hc2
    have hjeven : Even j := by
      have h1 : j * (4 * P + 8 * P * a) = 8 * P * b := by
        have : i' + 1 = 4 * P + 8 * P * a := by rw [hi']; ring
        rw [← this]; exact hb
      have h2' : 4 * P * (j * (1 + 2 * a)) = 4 * P * (2 * b) := by linarith
      have h3' : j * (1 + 2 * a) = 2 * b := mul_left_cancel₀ (by positivity) h2'
      have hodd' : Odd (1 + 2 * a) := ⟨a, by ring⟩
      rcases Int.even_or_odd j with hje | hjo
      · exact hje
      · exfalso
        have : Odd (j * (1 + 2 * a)) := hjo.mul hodd'
        rw [h3'] at this
        exact (Int.not_odd_iff_even.mpr ⟨b, by ring⟩) this
    have hmyN : m * y ∈ N := N.mul_mem hmN (s.hRN c.hb)
    have hxy : (m * y) * x * (m * y)⁻¹ = x ^ (-i') := by
      calc (m * y) * x * (m * y)⁻¹ = m * (y * x * y⁻¹) * m⁻¹ := by group
        _ = m * x⁻¹ * m⁻¹ := by rw [c.hbab]
        _ = (m * x * m⁻¹)⁻¹ := by group
        _ = x ^ (-i') := by rw [hx', zpow_neg]
    have hyy : (m * y) * y * (m * y)⁻¹ = y * x ^ j := by
      calc (m * y) * y * (m * y)⁻¹ = m * y * m⁻¹ := by group
        _ = y * x ^ j := hy'
    have hodd2 : Odd (-i') := by simpa using hodd.neg
    obtain ⟨k, hkx, hky⟩ := adjust c hodd2 hjeven hxy hyy
    set m'' : G := (m * y) * x ^ k with hm''
    have hxk : x ^ k ∈ R := R.zpow_mem c.ha k
    have hm''N : m'' ∈ N := N.mul_mem hmyN (s.hRN hxk)
    have hxm'' : m'' * x * m''⁻¹ = x ^ ((1 : ℤ) + 2 ^ (n' + 2)) := by
      rw [hm'', hkx, c.zpow_eq_iff]
      exact ⟨-(a + 1), by rw [hi', h2, h3]; ring⟩
    have hym'' : m'' * y * m''⁻¹ = y := hky
    have hF : IsFAut R m'' := isFAut_of_action s hN2 hm''N hxm'' hym''
    have hsqR : m'' * m'' ∈ R := by
      have e : m'' * m'' = (m * (y * x ^ k) * m⁻¹) * (y * x ^ k) := by
        rw [hm'']
        calc m * y * x ^ k * (m * y * x ^ k) = (m * (y * x ^ k) * m⁻¹) * (m * m) * (y * x ^ k) := by
              group
          _ = (m * (y * x ^ k) * m⁻¹) * (y * x ^ k) := by rw [hm2, mul_one]
      rw [e]
      have hyk : y * x ^ k ∈ R := R.mul_mem c.hb hxk
      exact R.mul_mem (s.conj_mem_R hmN hyk) hyk
    have hsqC : m'' * m'' ∈ Subgroup.centralizer (R : Set G) := by
      have hmma : (m'' * m'') * x * (m'' * m'')⁻¹ = x := by
        rw [coord_mul_a hxm'' hxm'']
        have : x ^ (((1 : ℤ) + 2 ^ (n' + 2)) * ((1 : ℤ) + 2 ^ (n' + 2))) = x ^ (1 : ℤ) := by
          rw [c.zpow_eq_iff]
          exact ⟨1 + 2 ^ (n' + 1), by ring⟩
        simpa using this
      have hmmb : (m'' * m'') * y * (m'' * m'')⁻¹ = y := by
        calc (m'' * m'') * y * (m'' * m'')⁻¹ = m'' * (m'' * y * m''⁻¹) * m''⁻¹ := by group
          _ = y := by rw [hym'', hym'']
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      exact (centralizes_of_fixes c hmma hmmb r hr)
    have hsqz : m'' * m'' ∈ Subgroup.zpowers z :=
      T7U.inf_centralizer_le_zpowers hqR hz ⟨hsqR, hsqC⟩
    obtain ⟨r, hrR, hr2, hrF⟩ := T7U.exists_involution_of_isFAut hqR hz s.hRN hN2 s.hNR hm''N hF hsqz
    refine ⟨y * x ^ k * r, R.mul_mem (R.mul_mem c.hb hxk) hrR, ?_, ?_⟩
    · have : m * (y * x ^ k * r) = m'' * r := by rw [hm'']; group
      rw [this]; exact hr2
    · have : m * (y * x ^ k * r) = m'' * r := by rw [hm'']; group
      rw [this]; exact hrF

end CFSG.CGT.PushingUpLit.SolKNA.R4.C2516
