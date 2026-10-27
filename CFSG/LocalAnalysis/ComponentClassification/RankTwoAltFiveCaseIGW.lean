module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveCaseISylow
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSmallCover
public import CFSG.Sporadic.Recognition.JankoWongPSLNine

public section

namespace CFSG.ComponentClassification.RankTwoAltFive

open Subgroup Equiv Equiv.Perm CFSG.Open CFSG.ABGLocalTools CFSG.GorensteinWalter
  CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.RankTwoAlt

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem orderOf_ne_fifteen (σ : Perm (Fin 7)) : orderOf σ ≠ 15 := by
  intro h
  have hsum : σ.cycleType.sum ≤ 7 := by
    rw [sum_cycleType]
    exact (Finset.card_le_univ _).trans (by simp)
  have hmem : ∀ n ∈ σ.cycleType, n = 3 ∨ n = 5 := by
    intro n hn
    have h2 := two_le_of_mem_cycleType hn
    have hd : n ∣ 15 := h ▸ dvd_of_mem_cycleType hn
    have hle : n ≤ 7 := (Multiset.le_sum_of_mem hn).trans hsum
    interval_cases n <;> simp_all
  have hlcm : σ.cycleType.lcm = 15 := by rw [lcm_cycleType, h]
  by_cases h3 : 3 ∈ σ.cycleType
  · by_cases h5 : 5 ∈ σ.cycleType
    · obtain ⟨s, hs⟩ := Multiset.exists_cons_of_mem h3
      rw [hs] at h5 hsum
      have h5' : 5 ∈ s := by
        rcases Multiset.mem_cons.mp h5 with h' | h'
        · exact absurd h' (by norm_num)
        · exact h'
      have := Multiset.le_sum_of_mem h5'
      rw [Multiset.sum_cons] at hsum
      omega
    · have hd : σ.cycleType.lcm ∣ 3 := Multiset.lcm_dvd.mpr fun n hn => by
        rcases hmem n hn with rfl | rfl
        · exact dvd_rfl
        · exact absurd hn h5
      rw [hlcm] at hd
      norm_num at hd
  · have hd : σ.cycleType.lcm ∣ 5 := Multiset.lcm_dvd.mpr fun n hn => by
      rcases hmem n hn with rfl | rfl
      · exact absurd hn h3
      · exact dvd_rfl
    rw [hlcm] at hd
    norm_num at hd

@[expose] def a7inv : alternatingGroup (Fin 7) :=
  ⟨swap 0 1 * swap 2 3, mem_alternatingGroup.mpr (by decide)⟩

@[expose] def a7c456 : alternatingGroup (Fin 7) :=
  ⟨swap 4 5 * swap 5 6, mem_alternatingGroup.mpr (by decide)⟩

theorem a7inv_facts : a7inv ^ 2 = 1 ∧ a7inv ≠ 1 ∧ a7c456 * a7inv = a7inv * a7c456 ∧
    a7c456 ^ 3 = 1 ∧ a7c456 ≠ 1 := by
  decide +kernel

namespace CaseICoords

variable {A B R T : Subgroup G} (c : CaseICoords A B R T)

theorem commute_range_B_of_odd {s : c.H} (hs : (s : G) ∈ R) (hs1 : (s : G) ≠ 1)
    {q : c.Hbar} (hq : (s : c.Hbar) * q = q * s) (hodd : Odd (orderOf q)) (b : B) :
    q * c.barOf c.B_le_H b = c.barOf c.B_le_H b * q := by
  have hs2 : s * s = 1 := Subtype.ext (c.mul_self_of_mem_R hs)
  obtain ⟨y, rfl, hys⟩ := exists_lift_commute c.odd_card_core hs2 q hq
  have hyodd : Odd (orderOf (y : G)) := by
    rw [Subgroup.orderOf_coe]
    exact odd_orderOf_of_odd_mk c.odd_card_core hodd
  have hyB := c.mem_centralizer_of_odd hs hs1 y.2 (congrArg Subtype.val hys).symm hyodd
  rw [barOf_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (mem_centralizer_iff.mp hyB b b.2).symm

theorem false_of_equiv_alt7 (e : c.Hbar ≃* alternatingGroup (Fin 7)) : False := by
  obtain ⟨s, hs, hs1, hsb1, -, hsb2⟩ := c.exists_mem_R
  obtain ⟨hi2, hi1, hic, hc3, hc1⟩ := a7inv_facts
  have ht2 : e (s : c.Hbar) ^ 2 = 1 := by rw [← map_pow, sq, hsb2, map_one]
  have ht1 : e (s : c.Hbar) ≠ 1 := fun h => hsb1 (e.injective (by rw [h, map_one]))
  obtain ⟨g, hg⟩ := isConj_iff.mp
    (isConj_of_sq_eq_one_of_le_seven (by norm_num) hi2 hi1 ht2 ht1)
  set q := e.symm (g * a7c456 * g⁻¹) with hq
  have hq3 : q ^ 3 = 1 := by
    rw [hq, ← map_pow, conj_pow, hc3, mul_one, mul_inv_cancel, map_one]
  have hq1 : q ≠ 1 := fun h => hc1 (by
    have h' : g * a7c456 * g⁻¹ = 1 := e.symm.injective (by rw [← hq, h, map_one])
    calc a7c456 = g⁻¹ * (g * a7c456 * g⁻¹) * g := by group
      _ = 1 := by rw [h', mul_one, inv_mul_cancel])
  have hqo : orderOf q = 3 := orderOf_eq_prime hq3 hq1
  have hqs : (s : c.Hbar) * q = q * s := by
    apply e.injective
    rw [map_mul, map_mul, hq, MulEquiv.apply_symm_apply, ← hg]
    calc g * a7inv * g⁻¹ * (g * a7c456 * g⁻¹) = g * (a7inv * a7c456) * g⁻¹ := by group
      _ = g * (a7c456 * a7inv) * g⁻¹ := by rw [hic]
      _ = g * a7c456 * g⁻¹ * (g * a7inv * g⁻¹) := by group
  have hcomm := c.commute_range_B_of_odd hs hs1 hqs (by rw [hqo]; decide) (c.ψB c5)
  set b := c.barOf c.B_le_H (c.ψB c5) with hb
  have hinj := c.barOf_injective c.B_le_H c.ψB.symm
  have hb5 : b ^ 5 = 1 := by
    rw [hb, ← map_pow, ← map_pow, c5_pow_five, map_one, map_one]
  have hb1 : b ≠ 1 := fun h => c5_ne_one (c.ψB.injective (hinj
    (by rw [← hb, h, map_one]; exact (map_one (c.barOf c.B_le_H)).symm)))
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hbo : orderOf b = 5 := orderOf_eq_prime hb5 hb1
  have hcomm' : Commute (e q : Perm (Fin 7)) (e b : Perm (Fin 7)) := by
    show (e q : Perm (Fin 7)) * e b = e b * e q
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hcomm]
  have ho3 : orderOf (e q : Perm (Fin 7)) = 3 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hqo]
  have ho5 : orderOf (e b : Perm (Fin 7)) = 5 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hbo]
  have h15 := hcomm'.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [ho3, ho5]; norm_num)
  rw [ho3, ho5] at h15
  exact orderOf_ne_fifteen _ h15

theorem card_le_nine
    {L : Subgroup c.Hbar} {K : Type} [Field K] [Finite K] (hK : IsOddPrimePower (Nat.card K))
    (e : L ≃* PSL2 K) (hRL : c.Rbar ≤ L) (h16 : ¬ 16 ∣ Nat.card L) : Nat.card K ≤ 9 := by
  obtain ⟨s, hs, hs1, hsb1, hsV, hsb2⟩ := c.exists_mem_R
  set sb := (s : c.Hbar) with hsb
  have hsbL : sb ∈ L := hRL hsV
  set t := e ⟨sb, hsbL⟩ with ht_def
  have ht : orderOf t = 2 := by
    rw [ht_def, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [sq]; exact hsb2) hsb1
  obtain ⟨p, n, hp, hpodd, hn, hq⟩ := hK
  have hqodd : Odd (Nat.card K) := by rw [hq]; exact hpodd.pow
  have hq3 : 3 ≤ Nat.card K := by
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      rcases (by omega : p = 2 ∨ 3 ≤ p) with h | h
      · rw [h] at hpodd; exact absurd hpodd (by decide)
      · exact h
    rw [hq]
    exact hp3.trans (Nat.le_self_pow (by omega) p)
  have key : ∀ ε : ℤ, (ε = 1 ∨ ε = -1) → (Nat.card K : ℤ) ≡ ε [ZMOD 4] →
      (Nat.card K : ℤ) - ε ≤ 8 := by
    intro ε hε1 hε
    obtain ⟨m, hm, ⟨d⟩⟩ :=
      CFSG.ABGDGroups.psl2_centralizer_involution_dihedral ⟨p, n, hp, hpodd, hn, hq⟩ hε hε1 ht
    have hm0 : m ≠ 0 := by
      rintro rfl
      rcases hε1 with rfl | rfl <;> omega
    obtain ⟨k, m', hm'odd, hmk⟩ := Nat.exists_eq_two_pow_mul_odd hm0
    set z : centralizer ({t} : Set (PSL2 K)) := d.symm (DihedralGroup.r 1 ^ (2 ^ k)) with hz_def
    have hz : orderOf z = m' := by
      rw [hz_def, MulEquiv.orderOf_eq, orderOf_pow' _ (pow_ne_zero k two_ne_zero),
        DihedralGroup.orderOf_r_one, hmk, Nat.gcd_mul_right_left, Nat.mul_div_cancel_left _
          (pow_pos two_pos k)]
    set yL : L := e.symm (z : PSL2 K) with hyL
    have hyc : sb * (yL : c.Hbar) = (yL : c.Hbar) * sb := by
      have hzt : (z : PSL2 K) * t = t * z := mem_centralizer_singleton_iff.mp z.2
      have hte : e.symm t = ⟨sb, hsbL⟩ := by rw [ht_def, MulEquiv.symm_apply_apply]
      have := congrArg e.symm hzt
      rw [map_mul, map_mul, hte] at this
      have := congrArg Subtype.val this
      simp only [Subgroup.coe_mul] at this
      exact this.symm
    have hyord : orderOf (yL : c.Hbar) = m' := by
      rw [Subgroup.orderOf_coe, hyL, MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hz]
    have h1 := c.eq_one_of_commute_of_odd ⟨p, n, hp, hpodd, hn, hq⟩ (Or.inl ⟨e⟩) hRL hs hs1
      yL.2 hyc (hyord ▸ hm'odd)
    rw [h1, orderOf_one] at hyord
    have hcardC : Nat.card (centralizer ({t} : Set (PSL2 K))) = 2 * m := by
      rw [Nat.card_congr d.toEquiv, DihedralGroup.nat_card]
    have hdvd : 2 * m ∣ Nat.card L := by
      have h1 := Subgroup.card_subgroup_dvd_card (centralizer ({t} : Set (PSL2 K)))
      rwa [hcardC, ← Nat.card_congr e.toEquiv] at h1
    rw [hmk, ← hyord, mul_one] at hdvd
    have hk : k ≤ 2 := by
      by_contra hk
      apply h16
      exact (show (16 : ℕ) ∣ 2 * 2 ^ k by
        rw [← pow_succ']
        exact (pow_dvd_pow 2 (by omega : 4 ≤ k + 1))).trans hdvd
    have hm4 : m ≤ 4 := by
      rw [hmk, ← hyord, mul_one]
      calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk
        _ = 4 := by norm_num
    have : (Nat.card K : ℤ) - ε = 2 * m := by rw [← hm]
    omega
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hqodd) with h | h
  · have := key 1 (Or.inl rfl) (by show (Nat.card K : ℤ) % 4 = 1 % 4; omega)
    omega
  · have := key (-1) (Or.inr rfl) (by show (Nat.card K : ℤ) % 4 = (-1) % 4; omega)
    omega

theorem not_isPGroup_Hbar : ¬ IsPGroup 2 c.Hbar := by
  intro h2
  have hinj := c.barOf_injective c.B_le_H c.ψB.symm
  obtain ⟨k, hk⟩ := h2 (c.barOf c.B_le_H (c.ψB y0))
  have h3 : c.barOf c.B_le_H (c.ψB y0) ^ 3 = 1 := by
    rw [← map_pow, ← map_pow, ← orderOf_y0, pow_orderOf_eq_one, map_one, map_one]
  have h1 := eq_one_of_pow_three h3 hk
  have : y0 = 1 := c.ψB.injective (hinj (by rw [h1, map_one, map_one]))
  exact absurd this (by decide)

theorem Rbar_le_range_B : c.Rbar ≤ (c.barOf c.B_le_H).range := by
  rintro _ ⟨r, rfl⟩
  exact ⟨⟨r, c.pair.R_le r.2⟩, rfl⟩

theorem range_Bx_le {L : Subgroup c.Hbar} [L.Normal] (hLi : Odd L.index) :
    (c.barOf c.Bx_le_H).range ≤ L := by
  obtain ⟨s, hs, hs1, -, -, -⟩ := c.exists_mem_R
  have hsB : (s : G) ∈ B := c.pair.R_le hs
  have hs2 : (s : G) * s = 1 := c.mul_self_of_mem_R hs
  set s' : G := c.x * s * c.x⁻¹ with hs'
  have hs'Bx : s' ∈ c.Bx := ⟨s, hsB, rfl⟩
  have hs'2 : s' * s' = 1 := by
    calc s' * s' = c.x * ((s : G) * s) * c.x⁻¹ := by rw [hs']; group
      _ = 1 := by rw [hs2, mul_one, mul_inv_cancel]
  have hs'1 : (⟨s', hs'Bx⟩ : c.Bx) ≠ 1 := fun h => hs1 (by
    have h1 : s' = 1 := congrArg Subtype.val h
    have : (s : G) = c.x⁻¹ * s' * c.x := by rw [hs']; group
    rw [this, h1, mul_one, inv_mul_cancel])
  refine c.range_le_of_mem c.Bx_le_H c.equivBx hs'1 (c.mem_of_mul_self hLi ?_)
  rw [← map_mul, show (⟨s', hs'Bx⟩ : c.Bx) * ⟨s', hs'Bx⟩ = 1 from Subtype.ext hs'2, map_one]

theorem commutatorElement_k1_y0_ne_one : ⁅k1, y0⁆ ≠ 1 := by decide

theorem range_B_le_commutator {L : Subgroup c.Hbar} [L.Normal] (hLi : Odd L.index) :
    (c.barOf c.B_le_H).range ≤ ⁅L, L⁆ := by
  have hBL := c.range_B_le hLi
  have hm1 : ⁅c.ψB k1, c.ψB y0⁆ ≠ 1 := fun h => commutatorElement_k1_y0_ne_one
    (c.ψB.injective (by rw [map_commutatorElement, h, map_one]))
  refine c.range_le_of_mem c.B_le_H c.ψB.symm (m := ⁅c.ψB k1, c.ψB y0⁆) hm1 ?_
  rw [map_commutatorElement]
  exact commutator_mem_commutator (hBL ⟨_, rfl⟩) (hBL ⟨_, rfl⟩)

theorem range_Bx_le_commutator {L : Subgroup c.Hbar} [L.Normal] (hLi : Odd L.index) :
    (c.barOf c.Bx_le_H).range ≤ ⁅L, L⁆ := by
  have hBL := c.range_Bx_le hLi
  set b₁ : c.Bx := c.equivBx.symm k1
  set b₂ : c.Bx := c.equivBx.symm y0
  have hm1 : ⁅b₁, b₂⁆ ≠ 1 := fun h => commutatorElement_k1_y0_ne_one
    (c.equivBx.symm.injective (by rw [map_commutatorElement, h, map_one]))
  refine c.range_le_of_mem c.Bx_le_H c.equivBx (m := ⁅b₁, b₂⁆) hm1 ?_
  rw [map_commutatorElement]
  exact commutator_mem_commutator (hBL ⟨_, rfl⟩) (hBL ⟨_, rfl⟩)

namespace IsOuter

variable {c} {u : G} (hu : c.IsOuter u)
include hu

theorem eight_dvd_of_odd_index {L : Subgroup c.Hbar} (hLi : Odd L.index) : 8 ∣ Nat.card L := by
  have h8 := hu.eight_dvd_Hbar
  rw [← L.card_mul_index] at h8
  exact (Nat.Coprime.pow_left 3 (Nat.coprime_two_left.mpr hLi)).dvd_of_dvd_mul_right h8

theorem not_sixteen_dvd (L : Subgroup c.Hbar) : ¬ 16 ∣ Nat.card L := fun h =>
  hu.not_sixteen_dvd_Hbar (h.trans (Subgroup.card_subgroup_dvd_card L))

theorem exists_normal_equiv_alt6 :
    ∃ L : Subgroup c.Hbar, L.Normal ∧ Odd L.index ∧ Nonempty (L ≃* alternatingGroup (Fin 6)) := by
  rcases gw_cases hu.hasDihedralSylowTwo with h2 | hA7 | ⟨K, _, _, hK, L, hLn, hLi, hLm⟩
  · exact absurd h2 c.not_isPGroup_Hbar
  · obtain ⟨e⟩ := hA7
    exact (c.false_of_equiv_alt7 e).elim
  · have hqodd : Odd (Nat.card K) := by
      obtain ⟨p, n, -, hpodd, -, hq⟩ := hK
      rw [hq]
      exact hpodd.pow
    have hq3 : 3 ≤ Nat.card K := by
      obtain ⟨p, n, hp, hpodd, hn, hq⟩ := hK
      have hp3 : 3 ≤ p := by
        have := hp.two_le
        rcases (by omega : p = 2 ∨ 3 ≤ p) with h | h
        · rw [h] at hpodd; exact absurd hpodd (by decide)
        · exact h
      rw [hq]
      exact hp3.trans (Nat.le_self_pow (by omega) p)
    have h60 : 60 ∣ Nat.card L :=
      c.card_range_B ▸ Subgroup.card_dvd_of_le (c.range_B_le hLi)
    have h8 := hu.eight_dvd_of_odd_index hLi
    have h16 := hu.not_sixteen_dvd L
    rcases hLm with hL | hL
    ·
      obtain ⟨e⟩ := hL
      have hle := c.card_le_nine hK e (c.Rbar_le hLi) h16
      rw [Nat.card_congr e.toEquiv, psl2_card_formula K hK] at h60 h8
      have h9 : Nat.card K = 9 := by
        obtain ⟨k, hk⟩ := hqodd
        interval_cases h : Nat.card K <;> omega
      obtain ⟨e9⟩ :=
        CFSG.Sporadic.Recognition.JankoWong.nonempty_mulEquiv_alternatingGroup_six_of_card_nine h9
      exact ⟨L, hLn, hLi, ⟨e.trans e9⟩⟩
    ·
      exfalso
      obtain ⟨e⟩ := hL
      have hgt : 3 < Nat.card K := by
        rcases (by omega : Nat.card K = 3 ∨ 3 < Nat.card K) with h | h
        · rw [Nat.card_congr e.toEquiv, pgl2_card_formula, h] at h60
          norm_num at h60
        · exact h
      obtain ⟨e'⟩ := commutator_mulEquiv_psl2_of_mulEquiv_pgl2_card_gt_three K hK hgt e
      set L' := ⁅L, L⁆ with hL'
      have heL' : L' ≃* PSL2 K :=
        ((MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator L)).symm.trans
          ((commutator L).equivMapOfInjective L.subtype L.subtype_injective).symm).trans e'
      have hBL' := c.range_B_le_commutator hLi
      have hle := c.card_le_nine hK heL' (c.Rbar_le_range_B.trans hBL') (hu.not_sixteen_dvd L')
      have h60' : 60 ∣ Nat.card L' := c.card_range_B ▸ Subgroup.card_dvd_of_le hBL'
      have hL'card := psl2_card_formula K hK
      rw [← Nat.card_congr heL'.toEquiv] at hL'card
      rw [Nat.card_congr e.toEquiv, pgl2_card_formula] at h8 h16
      rw [hL'card] at h60'
      have h5 : Nat.card K = 5 := by
        obtain ⟨k, hk⟩ := hqodd
        interval_cases h : Nat.card K <;> omega
      have hL'60 : Nat.card L' = 60 := by rw [hL'card, h5]; norm_num
      have hBeq : (c.barOf c.B_le_H).range = L' :=
        eq_of_le_of_card_ge hBL' (by rw [hL'60, c.card_range_B])
      exact c.false_of_range_le (hBeq ▸ c.range_Bx_le_commutator hLi)

end IsOuter

theorem dvd_card_mulAut_alt6 : 720 ∣ Nat.card (MulAut (alternatingGroup (Fin 6))) := by
  have h := Subgroup.card_dvd_of_injective _
    (CFSG.Quasithin.SteinbergCB.conjPerm_injective (n := 6) (by norm_num))
  rwa [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at h

theorem eq_top_of_equiv_alt6 {Q : Type*} [Group Q] [Finite Q] (hQ : CFSG.pPrimeCore 2 Q = ⊥)
    {L : Subgroup Q} [hLn : L.Normal] (hLi : Odd L.index) (e : L ≃* alternatingGroup (Fin 6)) :
    L = ⊤ := by
  have hZ : center L = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : e z ∈ center (alternatingGroup (Fin 6)) := mem_center_iff.mpr fun g => by
      obtain ⟨b, rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul, (mem_center_iff.mp hz) b]
    rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at hz'
    exact mem_bot.mpr (e.injective (by rw [hz', map_one]))
  have hCL : centralizer (L : Set Q) ⊓ L = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyC, hyL⟩
    have : (⟨y, hyL⟩ : L) ∈ center L := mem_center_iff.mpr fun g =>
      Subtype.ext ((mem_centralizer_iff.mp hyC) g g.2)
    rw [hZ, mem_bot] at this
    exact mem_bot.mpr (congrArg Subtype.val this)
  have hinj : Function.Injective
      ((QuotientGroup.mk' L).comp (centralizer (L : Set Q)).subtype) := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have hyL : (y : Q) ∈ L := (QuotientGroup.eq_one_iff _).mp hy
    exact Subtype.ext (mem_bot.mp (hCL ▸ mem_inf.mpr ⟨y.2, hyL⟩))
  have hCodd : Nat.Coprime 2 (Nat.card (centralizer (L : Set Q))) := by
    have hd := Subgroup.card_dvd_of_injective _ hinj
    rw [← index_eq_card] at hd
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
      fun h2 => hLi.not_two_dvd_nat (h2.trans hd)
  have hC : centralizer (L : Set Q) = ⊥ :=
    (CFSG.pPrimeCore_eq_bot_iff.mp hQ) _ inferInstance hCodd
  have hφ : Function.Injective (MulAut.conjNormal (H := L) : Q →* MulAut L) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have : g ∈ centralizer (L : Set Q) := by
      rw [mem_centralizer_iff]
      intro h hh
      have := congrArg (fun φ : MulAut L => ((φ ⟨h, hh⟩ : L) : Q)) hg
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
      calc h * g = g * h * g⁻¹ * g := by rw [this]
        _ = g * h := by group
    rw [hC] at this
    exact mem_bot.mp this
  have hAut : Nat.card (MulAut L) = Nat.card (MulAut (alternatingGroup (Fin 6))) :=
    Nat.card_congr (MulAut.congr e).toEquiv
  have hdvd := Subgroup.card_dvd_of_injective _ hφ
  rw [hAut] at hdvd
  have hle :=
    CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.automorphism_card_le
  have h720 := dvd_card_mulAut_alt6
  have hLcard : Nat.card L = 360 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    rfl
  have hQcard := L.card_mul_index
  rw [hLcard] at hQcard
  rw [← hQcard] at hdvd
  obtain ⟨a, ha⟩ := h720
  have hpos : 0 < Nat.card (MulAut (alternatingGroup (Fin 6))) := Nat.card_pos
  rw [ha] at hle hpos hdvd
  have ha2 : a ≤ 2 := by omega
  have ha0 : 0 < a := by omega
  have hidx : L.index ∣ 2 * a := by
    rw [show 720 * a = 360 * (2 * a) by ring] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd
  have hi1 : L.index = 1 := by
    have h4 : L.index ≤ 4 := (Nat.le_of_dvd (by omega) hidx).trans (by omega)
    obtain ⟨k, hk⟩ := hLi
    have hk1 : k = 0 ∨ k = 1 := by omega
    rcases hk1 with rfl | rfl
    · simpa using hk
    · exfalso
      rw [hk] at hidx
      interval_cases a <;> omega
  exact index_eq_one.mp hi1

namespace IsOuter

variable {c} {u : G} (hu : c.IsOuter u)
include hu

theorem nonempty_equiv_alt6 :
    Nonempty (c.Hbar ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨L, hLn, hLi, ⟨e⟩⟩ := hu.exists_normal_equiv_alt6
  have hQ : CFSG.pPrimeCore 2 c.Hbar = ⊥ :=
    CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have hL := eq_top_of_equiv_alt6 hQ hLi e
  exact ⟨((MulEquiv.subgroupCongr hL).trans Subgroup.topEquiv).symm.trans e⟩

end IsOuter

end CaseICoords

end CFSG.ComponentClassification.RankTwoAltFive
