module

public import CFSG.HardMathSupport.Solomon.Coordinator.L514CRank
public import CFSG.HardMathSupport.Solomon.Coordinator.L514CSize
public import CFSG.HardMathSupport.Solomon.Coordinator.L514CL2Arith
public import CFSG.HardMathSupport.Solomon.Coordinator.L514CL2U32

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.RankThree.PartTwo.Sec4 CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs

theorem l514c_isL3Raw {r : ℕ} {Y : Type} [Group Y] (h : IsL3Eps r Y) : IsL3Raw r Y := by
  rcases h with ⟨-, h⟩ | ⟨-, h⟩
  · exact Or.inl h
  · exact Or.inr h

theorem l514c_center_eq_bot_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : Subgroup.center B = ⊥) : Subgroup.center A = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have : e z ∈ Subgroup.center B := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    apply e.symm.injective
    simp [hz (e.symm g)]
  rw [h, Subgroup.mem_bot] at this
  simpa using this

theorem l514c_center_eq_bot {r : ℕ} {Y : Type} [Group Y] (h : IsL3Eps r Y) :
    Subgroup.center Y = ⊥ := by
  rcases l514c_simple_or_card h with ⟨hs, h3⟩ | hc
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with h1 | h1
    · exact h1
    · exfalso
      have hcomm : ∀ a b : Y, a * b = b * a := fun a b =>
        Subgroup.mem_center_iff.1 (h1 ▸ Subgroup.mem_top b) a
      obtain ⟨hr, -, h8⟩ := l514c_card_bounds (l514c_isL3Raw h)
      have h256 : 2 ^ 8 ≤ r ^ 8 := Nat.pow_le_pow_left hr 8
      have hfin : Finite Y := Nat.finite_of_card_ne_zero (fun h0 => by rw [h0] at h8; omega)
      let _ : CommGroup Y := { ‹Group Y› with mul_comm := hcomm }
      have hp := IsSimpleGroup.prime_card (α := Y)
      have h3' : Nat.card Y = 3 :=
        ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h3).symm
      omega
  · obtain ⟨hr, -, h8⟩ := l514c_card_bounds (l514c_isL3Raw h)
    have hr2 : r = 2 := by
      by_contra hne
      have : 3 ^ 8 ≤ r ^ 8 := Nat.pow_le_pow_left (by omega) 8
      omega
    subst hr2
    rcases h with ⟨hmod, -⟩ | ⟨-, F, hF, hFin, hcard, ⟨e⟩⟩
    · omega
    · exact l514c_center_eq_bot_of_mulEquiv e
        (l514c_center_statedProj_su_two (by rw [hcard]; norm_num))

theorem l514c_card_psl2 {F : Type} [Field F] [Finite F] :
    Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSL 2 F)) * Nat.gcd 2 (Nat.card F - 1) =
      Nat.card F * (Nat.card F ^ 2 - 1) := by
  have h0 : Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSL 2 F)) =
      Nat.card F ^ (2 * (2 - 1) / 2) * (∏ j ∈ Finset.Icc 2 2, (Nat.card F ^ j - 1)) /
        Nat.gcd 2 (Nat.card F - 1) :=
    Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := F) (n := 2) (by norm_num)
  rw [h0]
  have hd : Nat.gcd 2 (Nat.card F - 1) ∣ Nat.card F * (Nat.card F ^ 2 - 1) := by
    refine Dvd.dvd.mul_left ?_ _
    have h1 : Nat.card F - 1 ∣ Nat.card F ^ 2 - 1 := by
      simpa using Nat.sub_dvd_pow_sub_pow (Nat.card F) 1 2
    exact (Nat.gcd_dvd_right 2 _).trans h1
  simpa using Nat.div_mul_cancel (by simpa using hd)

theorem l514c_final {p a p' b N e x y c : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (ha : 1 ≤ a)
    (hp' : p'.Prime) (hb : 1 ≤ b) (hr2 : 2 ≤ p ^ a) (he : 1 ≤ e ∧ e ≤ 2)
    (hx : x + 1 = (p' ^ b) ^ 2) (hy : y + 1 = (p ^ a) ^ 2)
    (hc : c + 1 = (p ^ a) ^ 3 ∨ c = (p ^ a) ^ 3 + 1)
    (hN3 : N * 3 = (p ^ a) ^ 3 * (y * c)) (hNe : N * e = p' ^ b * x)
    (h72 : p ^ a = 2 → N = 72) : False := by
  by_cases h2 : p ^ a = 2
  · have hN := h72 h2
    subst hN
    have hR' : 2 ≤ p' ^ b := hp'.two_le.trans (Nat.le_self_pow (by omega) _)
    generalize p' ^ b = R' at hx hNe hR'
    have : R' ≤ 5 := by
      by_contra hcon
      have h6 : 6 ≤ R' := by omega
      have : 6 * 6 ≤ R' * R' := Nat.mul_le_mul h6 h6
      have hxx : 35 ≤ x := by nlinarith
      have : 6 * 35 ≤ R' * x := Nat.mul_le_mul h6 hxx
      have : R' * 35 ≤ R' * x := Nat.mul_le_mul_left _ hxx
      nlinarith
    obtain ⟨he1, he2⟩ := he
    interval_cases R' <;> (try norm_num at hx) <;> interval_cases e <;> omega
  · have h4 : 4 ≤ p ^ a := by
      by_contra hlt
      have h3 : p ^ a = 3 := by omega
      have : p ∣ p ^ a := dvd_pow_self p (by omega)
      rw [h3] at this
      exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 this)
    apply l514c_arith hp hp3 ha hp' hb h4 he hx hy hc
    calc 3 * (p' ^ b * x) = 3 * (N * e) := by rw [hNe]
      _ = e * (N * 3) := by ring
      _ = _ := by rw [hN3]

theorem l514c_not_typeL2 {r : ℕ} {Y : Type} [Group Y] (h : IsL3Eps r Y) {F : Type} [Field F]
    [Finite F] (hN : Nat.card Y = Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSL 2 F))) : False := by
  obtain ⟨p', b, hK'⟩ := exists_piField_true F
  have hr' : Nat.card F = p' ^ b := by
    have := hK'.card
    rwa [piCard, Bool.cond_true] at this
  have hpsl2 := l514c_card_psl2 (F := F)
  rw [hr', ← hN] at hpsl2
  have hne1 : 1 ≤ Nat.gcd 2 (p' ^ b - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hne2 : Nat.gcd 2 (p' ^ b - 1) ≤ 2 := Nat.gcd_le_left _ (by norm_num)
  have hpow : 1 ≤ p' ^ b := Nat.one_le_pow _ _ hK'.prime.pos
  obtain ⟨x, hx⟩ : ∃ x, x = (p' ^ b) ^ 2 - 1 := ⟨_, rfl⟩
  have hx' : x + 1 = (p' ^ b) ^ 2 := by
    have : 1 ≤ (p' ^ b) ^ 2 := Nat.one_le_pow _ _ hpow
    omega
  rw [← hx] at hpsl2
  rcases h with ⟨hr, hP⟩ | ⟨hr, hP⟩
  · obtain ⟨p, a, hp, ha, hrp, h1⟩ := l514c_card_psl hP
    have hg : Nat.gcd 3 (r - 1) = 3 :=
      Nat.gcd_eq_left (Nat.dvd_of_mod_eq_zero (by omega))
    rw [hg] at h1
    have hp3 : p ≠ 3 := by
      rintro rfl
      rw [hrp, Nat.pow_mod] at hr
      simp [Nat.zero_pow (by omega : 0 < a)] at hr
    have hr2 : 2 ≤ p ^ a := by
      have := Nat.one_lt_pow (by omega : a ≠ 0) hp.one_lt
      omega
    obtain ⟨y, hy⟩ : ∃ y, y = (p ^ a) ^ 2 - 1 := ⟨_, rfl⟩
    have hy' : y + 1 = (p ^ a) ^ 2 := by
      have : 1 ≤ (p ^ a) ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega
    have hc' : (p ^ a) ^ 3 - 1 + 1 = (p ^ a) ^ 3 := by
      have : 1 ≤ (p ^ a) ^ 3 := Nat.one_le_pow _ _ (by omega)
      omega
    subst hrp
    rw [← hy] at h1
    refine l514c_final hp hp3 ha hK'.prime hK'.one_le hr2 ⟨hne1, hne2⟩ hx' hy'
      (Or.inl hc') (N := Nat.card Y) h1 hpsl2 ?_
    intro h2
    rw [h2] at hr
    omega
  · obtain ⟨p, a, hp, ha, hrp, h1⟩ := l514c_card_psu hP
    have hg : Nat.gcd 3 (r + 1) = 3 :=
      Nat.gcd_eq_left (Nat.dvd_of_mod_eq_zero (by omega))
    rw [hg] at h1
    have hp3 : p ≠ 3 := by
      rintro rfl
      rw [hrp, Nat.pow_mod] at hr
      simp [Nat.zero_pow (by omega : 0 < a)] at hr
    have hr2 : 2 ≤ p ^ a := by
      have := Nat.one_lt_pow (by omega : a ≠ 0) hp.one_lt
      omega
    obtain ⟨y, hy⟩ : ∃ y, y = (p ^ a) ^ 2 - 1 := ⟨_, rfl⟩
    have hy' : y + 1 = (p ^ a) ^ 2 := by
      have : 1 ≤ (p ^ a) ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega
    subst hrp
    rw [← hy] at h1
    refine l514c_final hp hp3 ha hK'.prime hK'.one_le hr2 ⟨hne1, hne2⟩ hx' hy'
      (Or.inr rfl) (N := Nat.card Y) h1 hpsl2 ?_
    intro h2
    rw [h2] at h1 hy'
    (try norm_num at h1)
    (try norm_num at hy')
    omega

theorem lemma514Cover_inputL3L2_holds : LocalBalance.Lemma514CoverNs.InputL3L2 := by
  intro Y _ r r' h hL2
  obtain ⟨F, hF, hFin, -, ⟨e⟩⟩ := hL2
  have hZ := l514c_center_eq_bot h
  refine l514c_not_typeL2 h (F := F) ?_
  rw [← Nat.card_congr e.toEquiv,
    Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Y), hZ, Subgroup.card_bot,
    mul_one]

end CFSG.HardMathSupport.Solomon.Coordinator
