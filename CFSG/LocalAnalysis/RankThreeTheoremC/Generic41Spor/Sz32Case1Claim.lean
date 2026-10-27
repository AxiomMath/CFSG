module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Defs
import CFSG.GroupTheory.BurnsideNormalComplement
public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

section Elementary

variable {Y : Type} [Group Y] {a c : Y}

theorem szh3_a_mem_Q0 : a ∈ sz32Q0 a c := Subgroup.mem_sup_left (Subgroup.mem_zpowers a)

theorem szh3_c_mem_Q0 : c ∈ sz32Q0 a c := Subgroup.mem_sup_right (Subgroup.mem_zpowers c)

theorem szh3_Z_le_Q0 : sz32Z a c ≤ sz32Q0 a c := by
  refine sup_le ?_ ?_
  · exact Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ szh3_a_mem_Q0 5)
  · exact Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ szh3_c_mem_Q0 5)

theorem szh3_mem_Q0 (hac : a * c = c * a) {v : Y} (hv : v ∈ sz32Q0 a c) :
    ∃ s t : ℤ, v = a ^ s * c ^ t := by
  have hcomm : Commute a c := hac
  let T : Subgroup Y :=
    { carrier := {v | ∃ s t : ℤ, v = a ^ s * c ^ t}
      one_mem' := ⟨0, 0, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨s, t, rfl⟩ ⟨s', t', rfl⟩
        refine ⟨s + s', t + t', ?_⟩
        rw [zpow_add, zpow_add]
        exact Commute.mul_mul_mul_comm (hcomm.zpow_zpow s' t).symm (a ^ s) (c ^ t')
      inv_mem' := by
        rintro _ ⟨s, t, rfl⟩
        refine ⟨-s, -t, ?_⟩
        rw [mul_inv_rev, ← zpow_neg, ← zpow_neg]
        exact (hcomm.zpow_zpow (-s) (-t)).symm.eq }
  have h1 : Subgroup.zpowers a ≤ T := by
    rw [Subgroup.zpowers_le]
    exact ⟨1, 0, by simp⟩
  have h2 : Subgroup.zpowers c ≤ T := by
    rw [Subgroup.zpowers_le]
    exact ⟨0, 1, by simp⟩
  exact sup_le h1 h2 hv

theorem szh3_zpow_eq_one_of_eq (hinf : Subgroup.zpowers a ⊓ Subgroup.zpowers c = ⊥) {m n : ℤ}
    (h : a ^ m = c ^ n) : a ^ m = 1 := by
  have h1 : a ^ m ∈ Subgroup.zpowers a ⊓ Subgroup.zpowers c :=
    ⟨Subgroup.zpow_mem_zpowers a m, h ▸ Subgroup.zpow_mem_zpowers c n⟩
  rw [hinf] at h1
  exact Subgroup.mem_bot.mp h1

theorem szh3_dvd_of_zpow_eq_one {g : Y} (hg : orderOf g = 25) {s : ℤ} (h : g ^ (5 * s) = 1) :
    5 ∣ s := by
  have h1 := orderOf_dvd_iff_zpow_eq_one.mpr h
  rw [hg] at h1
  omega

theorem szh3_pow_five (hac : a * c = c * a) (s t : ℤ) :
    (a ^ s * c ^ t) ^ 5 = a ^ (5 * s) * c ^ (5 * t) := by
  have hcomm : Commute a c := hac
  have e1 : (a ^ s) ^ 5 = a ^ (5 * s) := by
    rw [← zpow_natCast, ← zpow_mul]; norm_num [mul_comm]
  have e2 : (c ^ t) ^ 5 = c ^ (5 * t) := by
    rw [← zpow_natCast, ← zpow_mul]; norm_num [mul_comm]
  rw [(hcomm.zpow_zpow s t).mul_pow, e1, e2]

theorem szh3_exists_zpow_eq {g : Y} (hg : orderOf g = 25) {t : ℤ} (ht : ¬ 5 ∣ t) :
    ∃ u : ℤ, (g ^ t) ^ u = g := by
  have h1 : ¬ 5 ∣ t.natAbs := by omega
  have h2 : Nat.Coprime t.natAbs 25 := by
    have : Nat.Coprime t.natAbs (5 ^ 2) :=
      Nat.Coprime.pow_right 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr h1).symm
    simpa using this
  have h3 : IsCoprime t 25 := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact h2
  obtain ⟨u, v, huv⟩ := h3
  refine ⟨u, ?_⟩
  have h25 : g ^ (25 : ℤ) = 1 := by
    rw [zpow_ofNat, ← hg]; exact pow_orderOf_eq_one g
  calc (g ^ t) ^ u = g ^ (t * u) := by rw [← zpow_mul]
    _ = g ^ (1 - 25 * v) := by congr 1; linarith
    _ = g := by rw [zpow_sub, zpow_mul, h25, one_zpow, zpow_one]; simp

end Elementary

section Case1

variable {Y : Type} [Group Y] [Finite Y] {Pb : Subgroup Y} {a c y : Y}

theorem szh3_Q0_le (hY : Sz32Case2Data Pb a c y) : sz32Q0 a c ≤ Pb :=
  sup_le (Subgroup.zpowers_le.mpr hY.pres.a_mem) (Subgroup.zpowers_le.mpr hY.pres.c_mem)

theorem szh3_dvd_of_pow5_eq_one (hY : Sz32Case2Data Pb a c y) {s t : ℤ}
    (h : (a ^ s * c ^ t) ^ 5 = 1) : 5 ∣ s ∧ 5 ∣ t := by
  rw [szh3_pow_five hY.pres.ac] at h
  have h1 : a ^ (5 * s) = c ^ (-(5 * t)) := by
    rw [zpow_neg]; exact eq_inv_of_mul_eq_one_left h
  have h2 := szh3_zpow_eq_one_of_eq hY.pres.inf h1
  have h3 : c ^ (5 * t) = 1 := by rw [h2, one_mul] at h; exact h
  exact ⟨szh3_dvd_of_zpow_eq_one hY.pres.ord_a h2, szh3_dvd_of_zpow_eq_one hY.facts.ord_c h3⟩

theorem szh3_conj_Q0_mem (hY : Sz32Case2Data Pb a c y) {h : Y}
    (hh : h ∈ Subgroup.normalizer (Pb : Set Y)) {q : Y} (hq : q ∈ sz32Q0 a c) :
    h * q * h⁻¹ ∈ sz32Q0 a c := by
  have hB : (sz32Q0 a c).map (MulAut.conj h).toMonoidHom = sz32Q0 a c := by
    apply hY.facts.Q0_unique
    · rintro _ ⟨q, hq, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hh q).mp (szh3_Q0_le hY hq)
    · haveI := hY.facts.Q0_comm
      infer_instance
    · rw [Subgroup.card_map_of_injective (MulAut.conj h).injective, hY.facts.Q0_card]
  rw [← hB]
  exact ⟨q, hq, rfl⟩

theorem szh3_Q0_le_pCore (hY : Sz32Case2Data Pb a c y) (ha : a ∈ CFSG.pCore 5 Y) :
    sz32Q0 a c ≤ CFSG.pCore 5 Y := by
  obtain ⟨g, hg, hswap⟩ := hY.swap
  have hmemQ : g⁻¹ * a * g ∈ sz32Q0 a c := by
    have := szh3_conj_Q0_mem hY (inv_mem hg) (szh3_a_mem_Q0 (a := a) (c := c))
    simpa using this
  have ha' : g⁻¹ * a * g ∈ CFSG.pCore 5 Y := by
    have := (inferInstance : (CFSG.pCore 5 Y).Normal).conj_mem a ha g⁻¹
    simpa using this
  have h5 : a ^ 5 ∈ (Subgroup.zpowers (c ^ 5)).map (MulAut.conj g).toMonoidHom := by
    rw [hswap]; exact Subgroup.mem_zpowers _
  obtain ⟨x, hx, hxa⟩ := h5
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hxa' : g * (c ^ 5) ^ m * g⁻¹ = a ^ 5 := hxa
  have e : (g⁻¹ * a * g) ^ 5 = g⁻¹ * a ^ 5 * g := by
    have := @conj_pow _ _ 5 g⁻¹ a
    simpa using this
  have e2 : (g⁻¹ * a * g) ^ 5 = (c ^ 5) ^ m := by
    rw [e, ← hxa']; group
  have hne : (g⁻¹ * a * g) ^ 5 ≠ 1 := by
    intro h1
    rw [e] at h1
    have h2 : a ^ 5 = 1 := by
      have := congrArg (fun z => g * z * g⁻¹) h1
      simpa [mul_assoc] using this
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hY.pres.ord_a] at h3
    omega
  obtain ⟨s, t, hst⟩ := szh3_mem_Q0 hY.pres.ac hmemQ
  have ht : ¬ 5 ∣ t := by
    intro ht5
    apply hne
    rw [e2]
    have hc5 : c ^ (5 * t) = 1 := by
      apply orderOf_dvd_iff_zpow_eq_one.mp
      rw [hY.facts.ord_c]
      obtain ⟨t', rfl⟩ := ht5
      exact ⟨t', by push_cast; ring⟩
    have h1 : (g⁻¹ * a * g) ^ 5 = a ^ (5 * s) * c ^ (5 * t) := by
      rw [hst, szh3_pow_five hY.pres.ac]
    rw [hc5, mul_one] at h1
    have h2 : a ^ (5 * s) = c ^ (5 * m) := by
      rw [← h1, e2, ← zpow_natCast, ← zpow_mul]; norm_num [mul_comm]
    have h3 := szh3_zpow_eq_one_of_eq hY.pres.inf h2
    rw [← e2, h1, h3]
  have hct : c ^ t ∈ CFSG.pCore 5 Y := by
    have h1 : c ^ t = (a ^ s)⁻¹ * (g⁻¹ * a * g) := by
      rw [hst]; group
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.zpow_mem _ ha s)) ha'
  obtain ⟨u, hu⟩ := szh3_exists_zpow_eq hY.facts.ord_c ht
  have hc : c ∈ CFSG.pCore 5 Y := hu ▸ Subgroup.zpow_mem _ hct u
  exact sup_le (Subgroup.zpowers_le.mpr ha) (Subgroup.zpowers_le.mpr hc)

theorem szh3_mem_Q0_of_commute (hY : Sz32Case2Data Pb a c y) {v : Y} (hv : v ∈ Pb)
    (hcomm : ∀ q ∈ sz32Q0 a c, q * v = v * q) : v ∈ sz32Q0 a c := by
  haveI hQ0 := hY.facts.Q0_comm
  have h1 : sz32Q0 a c ≤ Subgroup.centralizer (Subgroup.zpowers v : Set Y) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hqv : Commute q v := hcomm q hq
    exact (hqv.symm.zpow_left k).eq
  have h2 : Subgroup.zpowers v ≤ Subgroup.centralizer (Subgroup.zpowers v : Set Y) :=
    Subgroup.le_centralizer _
  have h3 : sz32Q0 a c ⊔ Subgroup.zpowers v ≤ Subgroup.centralizer (Subgroup.zpowers v : Set Y) :=
    sup_le h1 h2
  have h4 : Subgroup.zpowers v ≤ Subgroup.centralizer ((sz32Q0 a c ⊔ Subgroup.zpowers v : Subgroup Y) : Set Y) :=
    Subgroup.le_centralizer_iff.mp h3
  have h5 : Subgroup.zpowers v ≤ Subgroup.centralizer (sz32Q0 a c : Set Y) :=
    Subgroup.le_centralizer_iff.mp h1
  have h6 : sz32Q0 a c ⊔ Subgroup.zpowers v ≤ Subgroup.centralizer (sz32Q0 a c : Set Y) :=
    sup_le (Subgroup.le_centralizer _) h5
  have h7 : sz32Q0 a c ≤ Subgroup.centralizer ((sz32Q0 a c ⊔ Subgroup.zpowers v : Subgroup Y) : Set Y) :=
    Subgroup.le_centralizer_iff.mp h6
  have hcommB : IsMulCommutative (sz32Q0 a c ⊔ Subgroup.zpowers v : Subgroup Y) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mp (sup_le h7 h4)
  have hB : sz32Q0 a c ⊔ Subgroup.zpowers v = sz32Q0 a c := by
    apply hY.facts.Q0_unique
    · exact sup_le (szh3_Q0_le hY) (Subgroup.zpowers_le.mpr hv)
    · exact hcommB
    · rw [← hY.facts.Q0_card]
      exact Subgroup.card_le_of_le le_sup_left
  rw [← hB]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers v)

theorem szh3_centralizer_le (hY : Sz32Case2Data Pb a c y) (hN : (sz32Q0 a c).Normal) :
    Subgroup.centralizer (sz32Q0 a c : Set Y) ≤ sz32Q0 a c := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨S, hS⟩ := hY.sylow
  haveI hQ0 := hY.facts.Q0_comm
  set Q₀ := sz32Q0 a c with hQ₀
  set D := Subgroup.centralizer (Q₀ : Set Y) with hD
  haveI hDN : D.Normal := inferInstance
  have hQD : Q₀ ≤ D := Subgroup.le_centralizer Q₀
  have hPD : Pb ⊓ D = Q₀ := by
    apply le_antisymm
    · intro v hv
      exact szh3_mem_Q0_of_commute hY hv.1 (fun q hq => (Subgroup.mem_centralizer_iff.mp hv.2 q hq))
    · exact le_inf (szh3_Q0_le hY) hQD
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 5 Pb ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_top, ?_, ?_⟩
    · rw [← hS]; exact S.isPGroup'
    · rw [Subgroup.relIndex_top_right, ← hS]; exact S.not_dvd_index
  have hSylD : CFSG.ABGLocalTools.IsSylowOf 5 (Pb ⊓ D) D :=
    hSyl.inf_of_le_normalizer le_top (by rw [Subgroup.normalizer_eq_top_iff.mpr hDN])
  obtain ⟨P', hP'⟩ := hSylD.exists_sylow_eq_subgroupOf
  have hnorm : Subgroup.normalizer (P' : Set D) ≤ Subgroup.centralizer (P' : Set D) := by
    intro n _
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hh' : (h : Y) ∈ Q₀ := by
      have h1 : h ∈ (Pb ⊓ D).subgroupOf D := by rw [← hP']; exact hh
      have h2 := Subgroup.mem_subgroupOf.mp h1
      rwa [hPD] at h2
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp n.2 (h : Y) hh'
  obtain ⟨K, hKN, hK5, -, -, hKchar, -, hKsup, -, -, -⟩ :=
    CFSG.GroupTheory.burnside_normal_complement P' hnorm
  haveI : K.Characteristic := hKchar
  have hKmap : K.map D.subtype ≤ primeComplementCore (G := Y) 5 := by
    apply normal_coprime_le_primeComplementCore
    · infer_instance
    · rw [Subgroup.card_map_of_injective D.subtype_injective]
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr hK5
  rw [hY.core, le_bot_iff] at hKmap
  have hK : K = ⊥ := (Subgroup.map_eq_bot_iff_of_injective K D.subtype_injective).mp hKmap
  intro x hx
  have hx1 : (⟨x, hx⟩ : D) ∈ K ⊔ (P' : Subgroup D) := by rw [hKsup]; trivial
  rw [hK, bot_sup_eq, hP'] at hx1
  have h2 := Subgroup.mem_subgroupOf.mp hx1
  rwa [hPD] at h2

theorem szh3_mem_Z_of_pow5 (hY : Sz32Case2Data Pb a c y) {v : Y} (hv : v ∈ sz32Q0 a c)
    (h5 : v ^ 5 = 1) : v ∈ sz32Z a c := by
  obtain ⟨s, t, rfl⟩ := szh3_mem_Q0 hY.pres.ac hv
  obtain ⟨⟨s', rfl⟩, ⟨t', rfl⟩⟩ := szh3_dvd_of_pow5_eq_one hY h5
  have e1 : a ^ (5 * s') = (a ^ 5) ^ s' := by rw [zpow_mul, zpow_ofNat]
  have e2 : c ^ (5 * t') = (c ^ 5) ^ t' := by rw [zpow_mul, zpow_ofNat]
  rw [e1, e2]
  exact Subgroup.mul_mem_sup (Subgroup.zpow_mem_zpowers _ _) (Subgroup.zpow_mem_zpowers _ _)

theorem szh3_coprime_centralizes (hY : Sz32Case2Data Pb a c y) (hN : (sz32Q0 a c).Normal)
    {k : Y} (hkZ : k ∈ Subgroup.centralizer (sz32Z a c : Set Y))
    (hk : Nat.Coprime (orderOf k) 5) : k ∈ Subgroup.centralizer (sz32Q0 a c : Set Y) := by
  haveI hQ0 := hY.facts.Q0_comm
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have hq' : k * q * k⁻¹ ∈ sz32Q0 a c := hN.conj_mem q hq k
  have hq5 : q ^ 5 ∈ sz32Z a c := hY.facts.pow5 q (szh3_Q0_le hY hq)
  have hfix : k * q ^ 5 * k⁻¹ = q ^ 5 := by
    have h1 := Subgroup.mem_centralizer_iff.mp hkZ (q ^ 5) hq5
    rw [← h1, mul_assoc, mul_inv_cancel, mul_one]
  set w := q⁻¹ * (k * q * k⁻¹) with hw
  have hwQ : w ∈ sz32Q0 a c := Subgroup.mul_mem _ (Subgroup.inv_mem _ hq) hq'
  have hw5 : w ^ 5 = 1 := by
    have hc0 : Commute q (k * q * k⁻¹) :=
      Subgroup.mul_comm_of_mem_isMulCommutative (sz32Q0 a c) hq hq'
    rw [hw, hc0.inv_left.mul_pow, inv_pow, conj_pow, hfix, inv_mul_cancel]
  have hwZ : w ∈ sz32Z a c := szh3_mem_Z_of_pow5 hY hwQ hw5
  have hkw : k * w * k⁻¹ = w := by
    have h1 := Subgroup.mem_centralizer_iff.mp hkZ w hwZ
    rw [← h1, mul_assoc, mul_inv_cancel, mul_one]
  have hind : ∀ j : ℕ, k ^ j * q * (k ^ j)⁻¹ = q * w ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have e1 : k ^ (j + 1) * q * (k ^ (j + 1))⁻¹ = k * (k ^ j * q * (k ^ j)⁻¹) * k⁻¹ := by
        rw [pow_succ', mul_inv_rev]; group
      rw [e1, ih]
      have e2 : k * (q * w ^ j) * k⁻¹ = (k * q * k⁻¹) * (k * w ^ j * k⁻¹) := by group
      have hqw : q * w = k * q * k⁻¹ := by rw [hw]; group
      rw [e2, ← conj_pow, hkw, pow_succ', ← mul_assoc, hqw]
  have hwr : w ^ orderOf k = 1 := by
    have h1 := hind (orderOf k)
    rw [pow_orderOf_eq_one] at h1
    simpa using h1.symm
  have hw1 : w = 1 := by
    have h1 : orderOf w ∣ orderOf k := orderOf_dvd_of_pow_eq_one hwr
    have h2 : orderOf w ∣ 5 := orderOf_dvd_of_pow_eq_one hw5
    have h3 : orderOf w ∣ Nat.gcd (orderOf k) 5 := Nat.dvd_gcd h1 h2
    rw [hk] at h3
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  have h1 : k * q * k⁻¹ = q := by
    have := hw1
    rw [hw] at this
    exact (inv_mul_eq_one.mp this).symm
  have h2 : k * q = q * k := by
    calc k * q = (k * q * k⁻¹) * k := by group
      _ = q * k := by rw [h1]
  exact h2.symm

theorem szh3_isPGroup_centralizer_Z (hY : Sz32Case2Data Pb a c y) (hN : (sz32Q0 a c).Normal)
    (hcent : Subgroup.centralizer (sz32Q0 a c : Set Y) ≤ sz32Q0 a c) :
    IsPGroup 5 (Subgroup.centralizer (sz32Z a c : Set Y)) := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨S, hS⟩ := hY.sylow
  have hPb5 : IsPGroup 5 Pb := by rw [← hS]; exact S.isPGroup'
  set K := Subgroup.centralizer (sz32Z a c : Set Y) with hK
  have hn : Nat.card K ≠ 0 := Nat.card_pos.ne'
  have hprime : ∀ {d : ℕ}, d.Prime → d ∣ Nat.card K → d = 5 := by
    intro d hd hdK
    haveI : Fact d.Prime := ⟨hd⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := K) d hdK
    by_contra hd5
    have hcop : Nat.Coprime (orderOf (x : Y)) 5 := by
      rw [Subgroup.orderOf_coe, hx]; exact (Nat.coprime_primes hd Nat.prime_five).mpr hd5
    have h1 := szh3_coprime_centralizes hY hN x.2 hcop
    have h2 : (x : Y) ∈ Pb := szh3_Q0_le hY (hcent h1)
    obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.mp hPb5 (⟨x, h2⟩ : Pb)
    have hj' : d = 5 ^ j := by
      rw [← hx, ← Subgroup.orderOf_coe x, ← hj]
      exact Subgroup.orderOf_coe (⟨(x : Y), h2⟩ : Pb)
    have h5d : 5 ∣ d := by
      rcases j with _ | j
      · simp at hj'; exact absurd hj' hd.one_lt.ne'
      · rw [hj']; exact dvd_pow_self 5 (Nat.succ_ne_zero j)
    exact hd5 ((Nat.prime_dvd_prime_iff_eq Nat.prime_five hd).mp h5d).symm
  exact IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd hn hprime)

theorem szh3_false_of_pCore_eq (hY : Sz32Case2Data Pb a c y)
    (hQ : CFSG.pCore 5 Y = sz32Q0 a c) : False := by
  have hN : (sz32Q0 a c).Normal := hQ ▸ (inferInstance : (CFSG.pCore 5 Y).Normal)
  have hcent := szh3_centralizer_le hY hN
  have hZN : (sz32Z a c).Normal := by
    constructor
    intro z hz g
    have hmap : (sz32Z a c).map (MulAut.conj g).toMonoidHom = sz32Z a c := by
      apply hY.wc g
      rintro _ ⟨w, hw, rfl⟩
      exact szh3_Q0_le hY (hN.conj_mem w (szh3_Z_le_Q0 hw) g)
    rw [← hmap]
    exact ⟨z, hz, rfl⟩
  haveI := hZN
  have hKN : (Subgroup.centralizer (sz32Z a c : Set Y)).Normal := inferInstance
  have hK5 := szh3_isPGroup_centralizer_Z hY hN hcent
  have hKle : Subgroup.centralizer (sz32Z a c : Set Y) ≤ CFSG.pCore 5 Y := le_sSup ⟨hKN, hK5⟩
  have hPK : y ∈ Subgroup.centralizer (sz32Z a c : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzQ : z ∈ Pb := szh3_Q0_le hY (szh3_Z_le_Q0 hz)
    exact ((hY.facts.center z hzQ).mpr hz y hY.pres.y_mem).symm
  have hy : y ∈ sz32Q0 a c := hQ ▸ hKle hPK
  exact hY.pres.y_not hy

theorem szh3_pCore_eq_Q0 (hY : Sz32Case2Data Pb a c y) (hQR : sz32Q0 a c ≤ CFSG.pCore 5 Y)
    (hRP : CFSG.pCore 5 Y ≤ Pb) (hne : CFSG.pCore 5 Y ≠ Pb) : CFSG.pCore 5 Y = sz32Q0 a c := by
  have hcardP : Nat.card Pb = 5 ^ 5 := hY.facts.card
  have hcardQ : Nat.card (sz32Q0 a c) = 5 ^ 4 := hY.facts.Q0_card
  have hd1 : Nat.card (CFSG.pCore 5 Y) ∣ 5 ^ 5 := hcardP ▸ Subgroup.card_dvd_of_le hRP
  have hd2 : 5 ^ 4 ∣ Nat.card (CFSG.pCore 5 Y) := hcardQ ▸ Subgroup.card_dvd_of_le hQR
  obtain ⟨j, hj, hjR⟩ := (Nat.dvd_prime_pow Nat.prime_five).mp hd1
  have h4 : 4 ≤ j := by
    rw [hjR] at hd2
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hd2
  have hj' : j = 4 ∨ j = 5 := by omega
  rcases hj' with rfl | rfl
  · exact (Subgroup.eq_of_le_of_card_ge hQR (by rw [hcardQ, hjR])).symm
  · exact absurd (Subgroup.eq_of_le_of_card_ge hRP (by rw [hcardP, hjR])) hne

theorem szh3_case1_claim (hY : Sz32Case2Data Pb a c y) (ha : a ∈ pCoreOf 5 (⊤ : Subgroup Y)) :
    ∀ g : Y, ∀ t ∈ Pb, g * t * g⁻¹ ∈ Pb := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have haR : a ∈ CFSG.pCore 5 Y := by rwa [pCoreOf_top_eq_pCore] at ha
  have hQR := szh3_Q0_le_pCore hY haR
  obtain ⟨S, hS⟩ := hY.sylow
  have hRP : CFSG.pCore 5 Y ≤ Pb := by
    rw [← hS]
    exact IsPGroup.le_sylow_of_normal CFSG.pCore_isPGroup S
  by_cases hRP' : CFSG.pCore 5 Y = Pb
  · intro g t ht
    rw [← hRP'] at ht ⊢
    exact (inferInstance : (CFSG.pCore 5 Y).Normal).conj_mem t ht g
  · exact (szh3_false_of_pCore_eq hY (szh3_pCore_eq_Q0 hY hQR hRP hRP')).elim

theorem sz32_case1_claim' {Y : Type} [Group Y] [Finite Y] {Pb : Subgroup Y} {a c y : Y}
    (hY : Sz32Case2Data Pb a c y) (ha : a ∈ pCoreOf 5 (⊤ : Subgroup Y)) :
    ∀ g : Y, ∀ t ∈ Pb, g * t * g⁻¹ ∈ Pb :=
  szh3_case1_claim hY ha

end Case1

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
