module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CInputs
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open Subgroup

private noncomputable def mulAutCenterQuotient {C : Type} [Group C] :
    MulAut C →* MulAut (C ⧸ Subgroup.center C) where
  toFun φ := QuotientGroup.congr (Subgroup.center C) (Subgroup.center C) φ
    (Subgroup.characteristic_iff_map_eq.mp inferInstance φ)
  map_one' := by
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H x =>
      change (((1 : MulAut C) x : C) : C ⧸ Subgroup.center C) =
        (x : C ⧸ Subgroup.center C)
      rw [MulAut.one_apply]
  map_mul' φ ψ := by
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H x =>
      change (((φ * ψ) x : C) : C ⧸ Subgroup.center C) =
        ((φ (ψ x) : C) : C ⧸ Subgroup.center C)
      rw [MulAut.mul_apply]

theorem card_mulAut_dvd_card_mulAut_quotient_center {C : Type} [Group C] [Finite C]
    (hC : Group.IsPerfect C) :
    Nat.card (MulAut C) ∣ Nat.card (MulAut (C ⧸ Subgroup.center C)) := by
  refine Subgroup.card_dvd_of_injective (mulAutCenterQuotient (C := C)) ?_
  rw [injective_iff_map_eq_one]
  intro φ hφ
  let : Bracket C C := commutatorElement
  have hdelta : ∀ x : C, φ x * x⁻¹ ∈ Subgroup.center C := by
    intro x
    have hz : x⁻¹ * φ x ∈ Subgroup.center C := by
      have hq : ((φ x : C) : C ⧸ Subgroup.center C) =
          (x : C ⧸ Subgroup.center C) := by
        have h := congrArg (fun f : MulAut (C ⧸ Subgroup.center C) =>
          f (x : C ⧸ Subgroup.center C)) hφ
        rw [MulAut.one_apply] at h
        change ((φ x : C) : C ⧸ Subgroup.center C) =
          (x : C ⧸ Subgroup.center C) at h
        exact h
      exact QuotientGroup.eq.mp hq.symm
    have hconj := Subgroup.instNormalCenter.conj_mem (x⁻¹ * φ x) hz (φ x)
    convert hconj using 1
    group
  have hcomm : ∀ a b : C, φ ⁅a, b⁆ = ⁅a, b⁆ := by
    intro a b
    have hza : φ a * a⁻¹ ∈ Subgroup.center C := hdelta a
    have hzb : φ b * b⁻¹ ∈ Subgroup.center C := hdelta b
    have hleft : ∀ z x y : C, z ∈ Subgroup.center C → ⁅z * x, y⁆ = ⁅x, y⁆ := by
      intro z x y hz
      rw [commutatorElement_mul_left_eq_conj_mul]
      have hzy : ⁅z, y⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact (Subgroup.mem_center_iff.mp hz y).symm
      have hzc : z * ⁅x, y⁆ * z⁻¹ = ⁅x, y⁆ := by
        rw [(Subgroup.mem_center_iff.mp hz ⁅x, y⁆).symm]
        simp
      rw [hzy, hzc]
      simp
    have hright : ∀ z x y : C, z ∈ Subgroup.center C → ⁅x, y * z⁆ = ⁅x, y⁆ := by
      intro z x y hz
      rw [commutatorElement_mul_right_eq_mul_conj]
      have hxy : ⁅x, z⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact Subgroup.mem_center_iff.mp hz x
      have hzc : z * ⁅x, y⁆ * z⁻¹ = ⁅x, y⁆ := by
        rw [(Subgroup.mem_center_iff.mp hz ⁅x, y⁆).symm]
        simp
      rw [hxy]
      simpa [mul_assoc] using hzc
    rw [map_commutatorElement]
    conv_lhs =>
      rw [show φ a = (φ a * a⁻¹) * a by group,
        show φ b = (φ b * b⁻¹) * b by group]
    rw [hleft (φ a * a⁻¹) a ((φ b * b⁻¹) * b) hza]
    rw [show (φ b * b⁻¹) * b = b * (φ b * b⁻¹) by
      exact (Subgroup.mem_center_iff.mp hzb b).symm]
    rw [hright (φ b * b⁻¹) a b hzb]
  let K : Subgroup C :=
    { carrier := {x | φ x = x}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, ha, hb]
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [map_inv, ha] }
  have hK : commutator C ≤ K :=
    Subgroup.commutator_le.mpr (fun a _ b _ => by
      simp only [K, Set.mem_setOf_eq]
      exact hcomm a b)
  have htop : (⊤ : Subgroup C) ≤ K := by
    rw [← hC.commutator_eq_top]
    exact hK
  apply MulEquiv.ext
  intro x
  exact htop (Subgroup.mem_top x)

private lemma open_pRank_le_one_of_not_dvd_sq {d : ℕ} (hd : d.Prime) {G : Type*} [Group G]
    [Finite G] (H : Subgroup G) (h : ¬ d ^ 2 ∣ Nat.card G) :
    CFSG.Open.pRank d H ≤ 1 := by
  by_contra hge
  push_neg at hge
  obtain ⟨E, -, -, hEcard⟩ := CFSG.SectionRank.exists_pRank hd.one_lt H
  have hdvd : Nat.card E ∣ Nat.card G := Subgroup.card_subgroup_dvd_card E
  have hE : d ^ 2 ∣ Nat.card E := by
    rw [hEcard]
    exact Nat.pow_dvd_pow d hge
  exact h (hE.trans hdvd)

theorem pRank_top_le_one_of_not_dvd_sq {d : ℕ} (hd : d.Prime) {G : Type*} [Group G] [Finite G]
    (h : ¬ d ^ 2 ∣ Nat.card G) : pRank d (⊤ : Subgroup G) ≤ 1 := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
    ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (⊤ : Subgroup G)]
  exact open_pRank_le_one_of_not_dvd_sq hd (⊤ : Subgroup G) h

private lemma prime_eq_five_or_seven_of_dvd_L34 {d : ℕ} (hd : d.Prime) (hd5 : 5 ≤ d)
    (h : d ∣ 2 ^ 8 * 3 ^ 3 * 5 * 7) : d = 5 ∨ d = 7 := by
  have h2 : ¬ d ∣ 2 ^ 8 := by
    intro hdvd
    have hdvd2 : d ∣ 2 := hd.dvd_of_dvd_pow hdvd
    have := Nat.le_of_dvd (by norm_num : 0 < 2) hdvd2
    omega
  have h3 : ¬ d ∣ 3 ^ 3 := by
    intro hdvd
    have hdvd3 : d ∣ 3 := hd.dvd_of_dvd_pow hdvd
    have := Nat.le_of_dvd (by norm_num : 0 < 3) hdvd3
    omega
  rcases hd.dvd_mul.mp h with h1 | h7
  · rcases hd.dvd_mul.mp h1 with h2' | h5
    · rcases hd.dvd_mul.mp h2' with h28 | h33
      · exact absurd h28 h2
      · exact absurd h33 h3
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hd (by norm_num)).mp h5)
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hd (by norm_num)).mp h7)

private lemma prime_eq_five_of_dvd_1440 {d : ℕ} (hd : d.Prime) (hd5 : 5 ≤ d)
    (h : d ∣ 1440) : d = 5 := by
  have h1440 : (1440 : ℕ) = 2 ^ 5 * 3 ^ 2 * 5 := by norm_num
  rw [h1440] at h
  rcases hd.dvd_mul.mp h with h1 | h5
  · rcases hd.dvd_mul.mp h1 with h2 | h3
    · have hdvd2 : d ∣ 2 := hd.dvd_of_dvd_pow h2
      have := Nat.le_of_dvd (by norm_num : 0 < 2) hdvd2
      omega
    · have hdvd3 : d ∣ 3 := hd.dvd_of_dvd_pow h3
      have := Nat.le_of_dvd (by norm_num : 0 < 3) hdvd3
      omega
  · exact (Nat.prime_dvd_prime_iff_eq hd (by norm_num)).mp h5

private lemma prime_eq_seven_or_eleven_of_dvd_factorial {d : ℕ} (hd : d.Prime) (hd5 : 5 ≤ d)
    (h : d ∣ Nat.factorial 11) (hne : d ≠ 5) : d = 7 ∨ d = 11 := by
  have hle : d ≤ 11 := (Nat.Prime.dvd_factorial hd).mp h
  interval_cases d
  · exact absurd rfl hne
  · exact absurd hd (by norm_num)
  · exact Or.inl rfl
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact Or.inr rfl

private lemma not_dvd_sq_L34_order_five : ¬ 5 ^ 2 ∣ 2 ^ 8 * 3 ^ 3 * 5 * 7 := by norm_num

private lemma not_dvd_sq_L34_order_seven : ¬ 7 ^ 2 ∣ 2 ^ 8 * 3 ^ 3 * 5 * 7 := by norm_num

private lemma not_dvd_sq_1440 : ¬ 5 ^ 2 ∣ 1440 := by norm_num

private lemma not_dvd_sq_factorial_eleven_seven : ¬ 7 ^ 2 ∣ Nat.factorial 11 := by
  norm_num [Nat.factorial]

private lemma not_dvd_sq_factorial_eleven_eleven : ¬ 11 ^ 2 ∣ Nat.factorial 11 := by
  norm_num [Nat.factorial]

theorem card_mulAut_dvd_of_isL34Type (hk : KFactAutL34) {C : Type} [Group C] [Finite C]
    (hC : Group.IsPerfect C) (hL : IsL34Type C) :
    Nat.card (MulAut C) ∣ 2 ^ 8 * 3 ^ 3 * 5 * 7 := by
  obtain ⟨d, hd, ⟨e⟩⟩ := hL
  have h1 : Nat.card (MulAut C) ∣ Nat.card (MulAut (C ⧸ Subgroup.center C)) :=
    card_mulAut_dvd_card_mulAut_quotient_center hC
  have h2 : Nat.card (MulAut (C ⧸ Subgroup.center C)) =
      Nat.card (MulAut (TauCeti.CFSGIndex.lie d).Group) :=
    Nat.card_congr (MulAut.congr e).toEquiv
  rw [h2] at h1
  exact h1.trans (hk d hd)

theorem card_mulAut_dvd_of_isA11Type (hk : KFactAutA11) {C : Type} [Group C] [Finite C]
    (hL : IsA11Type C) : Nat.card (MulAut C) ∣ Nat.factorial 11 := by
  obtain ⟨e⟩ := hL
  have h2 : Nat.card (MulAut C) =
      Nat.card (MulAut (alternatingGroup (Fin 11))) :=
    Nat.card_congr (MulAut.congr e).toEquiv
  rw [h2]
  exact hk

theorem card_mulAut_dvd_of_isA6Type (hk : KFactAutA6) {C : Type} [Group C] [Finite C]
    (hC : Group.IsPerfect C) (hL : IsA6Type C) : Nat.card (MulAut C) ∣ 1440 := by
  obtain ⟨e⟩ := hL
  have h1 : Nat.card (MulAut C) ∣ Nat.card (MulAut (C ⧸ Subgroup.center C)) :=
    card_mulAut_dvd_card_mulAut_quotient_center hC
  have h2 : Nat.card (MulAut (C ⧸ Subgroup.center C)) =
      Nat.card (MulAut (alternatingGroup (Fin 6))) :=
    Nat.card_congr (MulAut.congr e).toEquiv
  rw [h2] at h1
  exact h1.trans hk

theorem pRank_mulAut_le_one (hk : ZKFacts) {d : ℕ} (hd : d.Prime) (hd5 : 5 ≤ d) {C : Type}
    [Group C] [Finite C] (hq : CFSG.IsQuasisimple C)
    (hC : IsL34Type C ∨ IsA6Type C ∨ (IsA11Type C ∧ d ≠ 5)) :
    pRank d (⊤ : Subgroup (MulAut C)) ≤ 1 := by
  refine pRank_top_le_one_of_not_dvd_sq hd ?_
  intro hdvd2
  obtain ⟨hperf, -, -⟩ := hq
  have hdvd : d ∣ Nat.card (MulAut C) :=
    dvd_trans ⟨d, by ring⟩ hdvd2
  rcases hC with hL34 | hA6 | ⟨hA11, hdne5⟩
  · have hdiv := card_mulAut_dvd_of_isL34Type hk.autL34 hperf hL34
    have h2 : d ^ 2 ∣ 2 ^ 8 * 3 ^ 3 * 5 * 7 := hdvd2.trans hdiv
    have h1 : d ∣ 2 ^ 8 * 3 ^ 3 * 5 * 7 := hdvd.trans hdiv
    rcases prime_eq_five_or_seven_of_dvd_L34 hd hd5 h1 with h5 | h7
    · subst h5; exact not_dvd_sq_L34_order_five h2
    · subst h7; exact not_dvd_sq_L34_order_seven h2
  · have hdiv := card_mulAut_dvd_of_isA6Type hk.autA6 hperf hA6
    have h2 : d ^ 2 ∣ 1440 := hdvd2.trans hdiv
    have h1 : d ∣ 1440 := hdvd.trans hdiv
    have h5 := prime_eq_five_of_dvd_1440 hd hd5 h1
    subst h5
    exact not_dvd_sq_1440 h2
  · have hdiv := card_mulAut_dvd_of_isA11Type hk.autA11 hA11
    have h2 : d ^ 2 ∣ Nat.factorial 11 := hdvd2.trans hdiv
    have h1 : d ∣ Nat.factorial 11 := hdvd.trans hdiv
    rcases prime_eq_seven_or_eleven_of_dvd_factorial hd hd5 h1 hdne5 with h7 | h11
    · subst h7; exact not_dvd_sq_factorial_eleven_seven h2
    · subst h11; exact not_dvd_sq_factorial_eleven_eleven h2

theorem dvd_card_of_dvd_card_mulAut (hk : ZKFacts) {d : ℕ} (hd : d.Prime) (hd5 : 5 ≤ d)
    {C : Type} [Group C] [Finite C] (hq : CFSG.IsQuasisimple C)
    (hC : IsL34Type C ∨ IsA11Type C) (h : d ∣ Nat.card (MulAut C)) : d ∣ Nat.card C := by
  obtain ⟨hperf, -, -⟩ := hq
  rcases hC with hL34 | hA11
  · have hdiv := card_mulAut_dvd_of_isL34Type hk.autL34 hperf hL34
    obtain ⟨d', hd', ⟨e⟩⟩ := hL34
    have h1 : d ∣ 2 ^ 8 * 3 ^ 3 * 5 * 7 := h.trans hdiv
    have hcard : Nat.card (C ⧸ Subgroup.center C) = 20160 := by
      rw [Nat.card_congr e.toEquiv]
      exact hk.cardL34 d' hd'
    have hquot : Nat.card (C ⧸ Subgroup.center C) ∣ Nat.card C :=
      Subgroup.card_quotient_dvd_card (Subgroup.center C)
    rcases prime_eq_five_or_seven_of_dvd_L34 hd hd5 h1 with h5 | h7
    · subst h5
      exact dvd_trans (by norm_num : 5 ∣ 20160) (hcard ▸ hquot)
    · subst h7
      exact dvd_trans (by norm_num : 7 ∣ 20160) (hcard ▸ hquot)
  · have hdiv := card_mulAut_dvd_of_isA11Type hk.autA11 hA11
    obtain ⟨e⟩ := hA11
    have h1 : d ∣ Nat.factorial 11 := h.trans hdiv
    have hcard : Nat.card C = Nat.card (alternatingGroup (Fin 11)) :=
      Nat.card_congr e.toEquiv
    have hle : d ≤ 11 := (Nat.Prime.dvd_factorial hd).mp h1
    rw [hcard]
    have hcardAlt : Nat.card (alternatingGroup (Fin 11)) = 19958400 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      norm_num [Nat.factorial]
    rw [hcardAlt]
    interval_cases d
    · norm_num
    · exact absurd hd (by norm_num)
    · norm_num
    · exact absurd hd (by norm_num)
    · exact absurd hd (by norm_num)
    · exact absurd hd (by norm_num)
    · norm_num

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
