module

public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.Timmesfeld.Orders.Exceptional
public import CFSG.ClassicalInvolution.Orders.Classical
public import CFSG.ClassicalInvolution.Orders.Twisted
public import CFSG.ClassicalInvolution.Orders.Ree
public import CFSG.LieType.Ree.SuzukiOrder

public section

namespace CFSG.EvenSmallLie.CatalogOrders

open CFSG.Assembly.LowTwoRank CFSG.Open CFSG.Blueprint

@[expose] def lieOrd : StatedLieTag → ℕ → ℕ → ℕ
  | .PSL, n, q => ordA (n - 1) q
  | .PSU, n, q => ordTwistedA (n - 1) q
  | .PSp, n, q => ordBC n q
  | .POmegaOdd, n, q => ordBC n q
  | .POmegaPlus, n, q => ordD n q
  | .POmegaMinus, n, q => ordTwistedD n q
  | .G2, _, q => ordG2 q
  | .F4, _, q => ordF4 q
  | .E6, _, q => ordE6 q
  | .E7, _, q => ordE7 q
  | .E8, _, q => ordE8 q
  | .twistedE6, _, q => ordTwistedE6 q
  | .trialityD4, _, q => ordTrialityD4 q
  | .twistedB2, _, q => ordSuzuki q
  | .twistedG2, _, q => ordRee q
  | .twistedF4, _, _ => 0
  | .Tits, _, _ => 0

@[expose] def lieExp : StatedLieTag → ℕ → ℕ
  | .PSL, n => (n - 1) * n / 2
  | .PSU, n => (n - 1) * n / 2
  | .PSp, n => n * n
  | .POmegaOdd, n => n * n
  | .POmegaPlus, n => n * (n - 1)
  | .POmegaMinus, n => n * (n - 1)
  | .G2, _ => 6
  | .F4, _ => 24
  | .E6, _ => 36
  | .E7, _ => 63
  | .E8, _ => 120
  | .twistedE6, _ => 36
  | .trialityD4, _ => 12
  | .twistedB2, _ => 2
  | .twistedG2, _ => 3
  | .twistedF4, _ => 0
  | .Tits, _ => 0

@[expose] def lieMin : StatedLieTag → ℕ
  | .PSL => 2
  | .PSU => 3
  | .PSp => 2
  | .POmegaOdd => 3
  | .POmegaPlus => 4
  | .POmegaMinus => 4
  | _ => 0

@[expose] def lieAdm : StatedLieTag → ℕ → ℕ → Bool
  | .twistedB2, p, f => p == 2 && f % 2 == 1 && 3 ≤ f
  | .twistedG2, p, f => p == 3 && f % 2 == 1 && 3 ≤ f
  | _, _, _ => true

@[expose] def searchTags : List StatedLieTag :=
  [.PSL, .PSU, .PSp, .POmegaOdd, .POmegaPlus, .POmegaMinus, .G2, .F4, .E6, .E7, .E8,
    .twistedE6, .trialityD4, .twistedB2, .twistedG2]

theorem dvd_mul_div_of_dvd {a P d : ℕ} (h : d ∣ P) : a ∣ a * P / d := by
  rw [Nat.mul_div_assoc a h]
  exact dvd_mul_right a _

theorem sub_one_dvd_sq_sub_one (q : ℕ) : q - 1 ∣ q ^ 2 - 1 := by
  simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow q 1 2

theorem add_one_dvd_sq_sub_one (q : ℕ) : q + 1 ∣ q ^ 2 - 1 :=
  ⟨q - 1, by
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · simp
    · zify [Nat.one_le_pow 2 q hq, hq]
      ring⟩

theorem toNat_sq_sub_neg_one_sq (q : ℕ) : ((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2).toNat = q ^ 2 - 1 := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  · have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
    rw [show ((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2) = ((q ^ 2 - 1 : ℕ) : ℤ) by push_cast [h1]; ring]
    exact Int.toNat_natCast _

theorem pow_dvd_ordA {n : ℕ} (hn : 2 ≤ n) (q : ℕ) : q ^ ((n - 1) * n / 2) ∣ ordA (n - 1) q := by
  have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  unfold ordA
  rw [hn1]
  refine dvd_mul_div_of_dvd ((Nat.gcd_dvd_right _ _).trans ((sub_one_dvd_sq_sub_one q).trans ?_))
  exact Finset.dvd_prod_of_mem (fun i => q ^ i - 1) (Finset.mem_Icc.mpr ⟨le_rfl, hn⟩)

theorem pow_dvd_ordTwistedA {n : ℕ} (hn : 2 ≤ n) (q : ℕ) :
    q ^ ((n - 1) * n / 2) ∣ ordTwistedA (n - 1) q := by
  have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  unfold ordTwistedA
  rw [hn1]
  refine dvd_mul_div_of_dvd ((Nat.gcd_dvd_right _ _).trans ((add_one_dvd_sq_sub_one q).trans ?_))
  rw [← toNat_sq_sub_neg_one_sq]
  exact Finset.dvd_prod_of_mem (fun i => ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat)
    (Finset.mem_Icc.mpr ⟨le_rfl, hn⟩)

theorem pow_dvd_ordBC {n : ℕ} (hn : 1 ≤ n) (q : ℕ) : q ^ (n * n) ∣ ordBC n q := by
  unfold ordBC
  refine dvd_mul_div_of_dvd ((Nat.gcd_dvd_right _ _).trans ((sub_one_dvd_sq_sub_one q).trans ?_))
  exact Finset.dvd_prod_of_mem (fun i => q ^ (2 * i) - 1) (Finset.mem_Icc.mpr ⟨le_rfl, hn⟩)

theorem pow_dvd_ordD (n q : ℕ) : q ^ (n * (n - 1)) ∣ ordD n q := by
  unfold ordD
  rw [mul_assoc (q ^ (n * (n - 1)))]
  exact dvd_mul_div_of_dvd ((Nat.gcd_dvd_right _ _).trans (dvd_mul_right _ _))

theorem pow_dvd_ordTwistedD (n q : ℕ) : q ^ (n * (n - 1)) ∣ ordTwistedD n q := by
  unfold ordTwistedD
  rw [mul_assoc (q ^ (n * (n - 1)))]
  exact dvd_mul_div_of_dvd ((Nat.gcd_dvd_right _ _).trans (dvd_mul_right _ _))

theorem pow_dvd_ordE6 (q : ℕ) : q ^ 36 ∣ ordE6 q := by
  unfold ordE6
  simp only [mul_assoc]
  refine dvd_mul_div_of_dvd ((Nat.gcd_dvd_right _ _).trans ?_)
  exact (((((sub_one_dvd_sq_sub_one q).mul_left _).mul_left _).mul_left _).mul_left _).mul_left _

theorem pow_dvd_ordTwistedE6 (q : ℕ) : q ^ 36 ∣ ordTwistedE6 q := by
  unfold ordTwistedE6
  simp only [mul_assoc]
  refine dvd_mul_div_of_dvd ((Nat.gcd_dvd_right _ _).trans ?_)
  exact (((((add_one_dvd_sq_sub_one q).mul_left _).mul_left _).mul_left _).mul_left _).mul_left _

theorem pow_dvd_ordE7 (q : ℕ) : q ^ 63 ∣ ordE7 q := by
  unfold ordE7
  simp only [mul_assoc]
  refine dvd_mul_div_of_dvd ((Nat.gcd_dvd_right _ _).trans ?_)
  exact ((((((sub_one_dvd_sq_sub_one q).mul_left _).mul_left _).mul_left _).mul_left _).mul_left
    _).mul_left _

theorem pow_lieExp_dvd {t : StatedLieTag} {n : ℕ} (hn : lieMin t ≤ n) (q : ℕ) :
    q ^ lieExp t n ∣ lieOrd t n q := by
  cases t <;> simp only [lieMin, lieExp, lieOrd] at hn ⊢
  · exact pow_dvd_ordA hn q
  · exact pow_dvd_ordTwistedA (by omega) q
  · exact pow_dvd_ordBC (by omega) q
  · exact pow_dvd_ordBC (by omega) q
  · exact pow_dvd_ordD n q
  · exact pow_dvd_ordTwistedD n q
  · unfold ordG2; simp only [mul_assoc]; exact dvd_mul_right _ _
  · unfold ordF4; simp only [mul_assoc]; exact dvd_mul_right _ _
  · exact pow_dvd_ordE6 q
  · exact pow_dvd_ordE7 q
  · unfold ordE8; simp only [mul_assoc]; exact dvd_mul_right _ _
  · exact pow_dvd_ordTwistedE6 q
  · unfold ordTrialityD4; simp only [mul_assoc]; exact dvd_mul_right _ _
  · unfold ordSuzuki; simp only [mul_assoc]; exact dvd_mul_right _ _
  · unfold ordRee; simp only [mul_assoc]; exact dvd_mul_right _ _
  · exact dvd_zero _
  · exact dvd_zero _

theorem one_le_lieExp {t : StatedLieTag} (ht : t ∈ searchTags) {n : ℕ} (hn : lieMin t ≤ n) :
    1 ≤ lieExp t n := by
  cases t <;> simp only [lieMin, lieExp, searchTags] at hn ht ⊢ <;> try omega
  · have : 1 * 2 ≤ (n - 1) * n := Nat.mul_le_mul (by omega) (by omega)
    omega
  · have : 2 * 3 ≤ (n - 1) * n := Nat.mul_le_mul (by omega) (by omega)
    omega
  · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

theorem le_lieExp_add_one {t : StatedLieTag} {n : ℕ} (hn : lieMin t ≤ n)
    (h0 : n = 0 ∨ t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaOdd ∨ t = .POmegaPlus ∨
      t = .POmegaMinus) : n ≤ lieExp t n + 1 := by
  rcases h0 with rfl | h | h | h | h | h | h
  · omega
  all_goals subst h; simp only [lieMin, lieExp] at hn ⊢
  · have : (n - 1) * 2 ≤ (n - 1) * n := Nat.mul_le_mul le_rfl (by omega)
    omega
  · have : (n - 1) * 2 ≤ (n - 1) * n := Nat.mul_le_mul le_rfl (by omega)
    omega
  · nlinarith
  · nlinarith
  · have : n * 1 ≤ n * (n - 1) := Nat.mul_le_mul le_rfl (by omega)
    omega
  · have : n * 1 ≤ n * (n - 1) := Nat.mul_le_mul le_rfl (by omega)
    omega

theorem le_log_of_pow_dvd {N q a : ℕ} (hN : N ≠ 0) (hq : 2 ≤ q) (h : q ^ a ∣ N) :
    a ≤ Nat.log 2 N := by
  have h1 : q ^ a ≤ N := Nat.le_of_dvd (Nat.pos_of_ne_zero hN) h
  exact Nat.le_log_of_pow_le (by norm_num) ((Nat.pow_le_pow_left hq a).trans h1)

@[expose] def lieSearch (ps : List ℕ) (N : ℕ) (C : StatedLieTag → ℕ → ℕ → ℕ → Bool) : Bool :=
  ps.all fun p =>
    (List.range (Nat.log 2 N)).all fun f =>
      searchTags.all fun t =>
        (List.range (Nat.log 2 N + 2)).all fun n =>
          !(decide (lieMin t ≤ n) && lieAdm t p (f + 1) &&
              N % ((p ^ (f + 1)) ^ lieExp t n) == 0 && N % lieOrd t n (p ^ (f + 1)) == 0) ||
            C t n (p ^ (f + 1)) (lieOrd t n (p ^ (f + 1)))

theorem lieSearch_sound {ps : List ℕ} {N : ℕ} (hN : N ≠ 0)
    (hps : ∀ p : ℕ, p.Prime → p ∣ N → p ∈ ps) {C : StatedLieTag → ℕ → ℕ → ℕ → Bool}
    (hS : lieSearch ps N C = true) {t : StatedLieTag} (ht : t ∈ searchTags) {n p f : ℕ}
    (hp : p.Prime) (hf : 1 ≤ f) (hn : lieMin t ≤ n) (hnB : n ≤ lieExp t n + 1)
    (hadm : lieAdm t p f = true) (hd : lieOrd t n (p ^ f) ∣ N) :
    C t n (p ^ f) (lieOrd t n (p ^ f)) = true := by
  have hq : 2 ≤ p ^ f := hp.two_le.trans (Nat.le_self_pow (by omega) p)
  have hqd : (p ^ f) ^ lieExp t n ∣ N := (pow_dvd_pow_of_dvd (dvd_refl _) _).trans
    ((pow_lieExp_dvd hn _).trans hd)
  have he := one_le_lieExp ht hn
  have hpN : p ∣ N := (dvd_pow_self p (by omega : f ≠ 0)).trans
    ((dvd_pow_self (p ^ f) (by omega : lieExp t n ≠ 0)).trans hqd)
  have hpmem : p ∈ ps := hps p hp hpN
  have hfB : f ≤ Nat.log 2 N := le_log_of_pow_dvd hN hp.two_le
    ((pow_dvd_pow p (Nat.le_mul_of_pos_right f he)).trans (by rw [pow_mul]; exact hqd))
  have heB : lieExp t n ≤ Nat.log 2 N := le_log_of_pow_dvd hN hq hqd
  unfold lieSearch at hS
  rw [List.all_eq_true] at hS
  have h1 := hS p hpmem
  rw [List.all_eq_true] at h1
  have h2 := h1 (f - 1) (List.mem_range.2 (by omega))
  rw [List.all_eq_true] at h2
  have h3 := h2 t ht
  rw [List.all_eq_true] at h3
  have h4 := h3 n (List.mem_range.2 (by omega))
  rw [Nat.sub_add_cancel hf] at h4
  have hg : (decide (lieMin t ≤ n) && lieAdm t p f && N % ((p ^ f) ^ lieExp t n) == 0 &&
      N % lieOrd t n (p ^ f) == 0) = true := by
    simp [hn, hadm, Nat.mod_eq_zero_of_dvd hqd, Nat.mod_eq_zero_of_dvd hd]
  rw [hg] at h4
  simpa using h4

theorem card_eq_lieOrd_of_classical {G : Type} [Group G] {t : StatedLieTag} {n p f : ℕ}
    (h : StatedClassicalModel G t n p f) : Nat.card G = lieOrd t n (p ^ f) := by
  by_cases hp2 : p = 2
  · subst hp2
    obtain ⟨h1, h2, h3, h4, h5⟩ := Timmesfeld.card_statedClassicalModel_two h
    cases t
    case PSL => exact h1 rfl
    case PSU => exact h2 rfl
    case PSp => exact h3 rfl
    case POmegaOdd => exact absurd rfl h.1.2.2.2
    case POmegaPlus => exact h4 rfl
    case POmegaMinus => exact h5 rfl
    all_goals exact h.2.elim
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2 h
    cases t
    case PSL => exact h1 rfl
    case PSU => exact h2 rfl
    case PSp => exact h3 rfl
    case POmegaOdd => exact h4 rfl
    case POmegaPlus => exact h5 rfl
    case POmegaMinus => exact h6 rfl
    all_goals exact h.2.elim

theorem card_eq_lieOrd_of_exceptional
    {G : Type} [Group G] {t : StatedLieTag} {p f : ℕ}
    (h : ChevalleyExceptionalModel G t p f) : Nat.card G = lieOrd t 0 (p ^ f) := by
  by_cases hp2 : p = 2
  · subst hp2
    have hc := Timmesfeld.card_chevalleyExceptionalModel_two h
    cases t
    case G2 => exact hc
    case F4 => exact hc
    case E6 => exact hc
    case E7 => exact hc
    case E8 => exact hc
    case twistedE6 => exact hc
    case trialityD4 => exact hc
    all_goals exact h.2.elim
  · have hc := ClassicalInvolution.card_chevalleyExceptionalModel_of_ne_two hp2 h
    cases t
    case G2 => exact hc
    case F4 => exact hc
    case E6 => exact hc
    case E7 => exact hc
    case E8 => exact hc
    case twistedE6 => exact hc
    case trialityD4 => exact hc
    all_goals exact h.2.elim

theorem card_eq_lieOrd_of_suzuki
    {G : Type} [Group G] {p f : ℕ} (h : SuzukiModel G p f) :
    p = 2 ∧ (∃ a : ℕ, 1 ≤ a ∧ f = 2 * a + 1) ∧ Nat.card G = lieOrd .twistedB2 0 (p ^ f) := by
  obtain ⟨hp, a, ha, K, _, _, hf, hK, ⟨e⟩⟩ := h
  refine ⟨hp, ⟨a, ha, hf⟩, ?_⟩
  subst hp
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hf]
  rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK', hf]
  simp only [lieOrd, ordSuzuki]
  ring

theorem card_eq_lieOrd_of_ree
    {G : Type} [Group G] {p f : ℕ} (h : ReeTitsModel G .twistedG2 p f) :
    p = 3 ∧ (∃ a : ℕ, 1 ≤ a ∧ f = 2 * a + 1) ∧ Nat.card G = lieOrd .twistedG2 0 (p ^ f) := by
  obtain ⟨hp, a, ha, hfa, hc⟩ := ClassicalInvolution.card_of_reeTitsModel_twistedG2 h
  subst hp
  exact ⟨rfl, ⟨a, ha, hfa⟩, hc⟩

end CFSG.EvenSmallLie.CatalogOrders
