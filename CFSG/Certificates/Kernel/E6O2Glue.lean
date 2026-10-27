module

public import CFSG.Certificates.Kernel.E6O2Sound
public import CFSG.Certificates.Kernel.E6Syl3Glue
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6O2RegularDefs

public section

namespace CFSG.KC.E6O2

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.LieType.SeitzGeneration.ExcWideThree.E6Order3 CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.KC.E6Syl3


theorem triPairing_e6Shift_pow {b : Fin Tag.E6.rank → ZMod 3} {w : WeylGroup Tag.E6}
    (hw : w ∈ charStabilizer (triChar b)) (m : ℕ) :
    triPairing b (e6Shift (w ^ m)) = (m : ZMod 3) * triPairing b (e6Shift w) := by
  induction m with
  | zero => rw [pow_zero, e6Shift_one, triPairing_zero, Nat.cast_zero, zero_mul]
  | succ m ih =>
    rw [pow_succ', triPairing_e6Shift_mul hw, ih, Nat.cast_succ]
    ring

theorem o2At_pow {w : WeylGroup Tag.E6} {c : ZMod 3} (m : ℕ) (h : O2At (w ^ m) ((m : ZMod 3) * c)) :
    O2At w c := by
  intro V hV hVS
  refine h V hV fun b hb => ⟨pow_mem (hVS b hb).1 m, ?_⟩
  rw [triPairing_e6Shift_pow (hVS b hb).1, (hVS b hb).2]
  ring

@[expose] noncomputable def tpConj (b : Fin Tag.E6.rank → ZMod 3) (g : WeylGroup Tag.E6) :
    Fin Tag.E6.rank → ZMod 3 := fun i => triPairing b (g • Pi.single i 1)

theorem tpConj_apply (b : Fin Tag.E6.rank → ZMod 3) (g : WeylGroup Tag.E6)
    (v : Fin Tag.E6.rank → ℤ) : triPairing (tpConj b g) v = triPairing b (g • v) := by
  have hv : v = ∑ j : Fin Tag.E6.rank, v j • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hv]
  change _ = tpHom b _
  rw [Finset.smul_sum, map_sum]
  unfold triPairing
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_comm, map_zsmul]
  change _ = v j • triPairing b _
  simp only [tpConj, zsmul_eq_mul]
  ring

theorem tpConj_injective (g : WeylGroup Tag.E6) :
    Function.Injective fun b : Fin Tag.E6.rank → ZMod 3 => tpConj b g := by
  intro b b' e
  funext j
  have e1 := tpConj_apply b g (g⁻¹ • Pi.single j 1)
  have e2 := tpConj_apply b' g (g⁻¹ • Pi.single j 1)
  simp only at e
  rw [e, e2, smul_inv_smul, tp_smul_single] at e1
  rw [← tp_smul_single b j]
  exact e1.symm

theorem o2At_conj {y : WeylGroup Tag.E6} {c : ZMod 3} (h : O2At y c) (g : WeylGroup Tag.E6) :
    O2At (g * y * g⁻¹) c := by
  classical
  intro V hV hVS
  have hS : ∀ b ∈ V, InS y c (tpConj b g) := by
    intro b hb
    have hfix := triPairing_smul_of_mem (hVS b hb).1
    refine ⟨fun v => ?_, ?_⟩
    · rw [triChar_apply, triChar_apply, tpConj_apply, tpConj_apply]
      congr 1
      have e := hfix (g • v)
      rwa [mul_smul, mul_smul, inv_smul_smul] at e
    · rw [tpConj_apply, tpConj_apply]
      have e1 : g • e6Shift y = (g * y * g⁻¹) • e6Shift g + e6Shift (g * y * g⁻¹) - e6Shift g := by
        have h1 := e6Shift_mul (g * y * g⁻¹) g
        rw [inv_mul_cancel_right, e6Shift_mul g y] at h1
        rw [← h1]
        abel
      have e2 : g • e6Omega3 = (3 : ℤ) • e6Shift g + e6Omega3 := by
        rw [three_smul_e6Shift]
        abel
      rw [e1, e2]
      change tpHom b _ = c * tpHom b _
      rw [map_sub, map_add, map_add, map_zsmul]
      change triPairing b _ + triPairing b _ - triPairing b _ =
        c * ((3 : ℤ) • triPairing b _ + triPairing b _)
      rw [hfix, (hVS b hb).2, zsmul_eq_mul, Int.cast_ofNat,
        show (3 : ZMod 3) = 0 from rfl, zero_mul, zero_add]
      ring
  obtain ⟨α, hα, hk⟩ := h (V.image fun b => tpConj b g)
    (by rw [Finset.card_image_of_injective _ (tpConj_injective g)]; exact hV)
    (by
      intro b' hb'
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hb'
      exact hS b hb)
  refine ⟨g • α, IsRoot.smul hα g, fun b hb => ?_⟩
  rw [← tpConj_apply]
  exact hk _ (Finset.mem_image_of_mem _ hb)

theorem factorization_E6_two : (51840 : ℕ).factorization 2 = 7 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e : (51840 : ℕ) = 2 ^ 7 * 405 := by norm_num
  rw [Nat.factorization_def _ Nat.prime_two, e, padicValNat.mul (by norm_num) (by norm_num),
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]

theorem factorization_E6_five : (51840 : ℕ).factorization 5 = 1 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have e : (51840 : ℕ) = 5 ^ 1 * 10368 := by norm_num
  rw [Nat.factorization_def _ (by norm_num), e, padicValNat.mul (by norm_num) (by norm_num),
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]

theorem prime_dvd_51840 {p : ℕ} (hp : p.Prime) (h : p ∣ 51840) : p = 2 ∨ p = 3 ∨ p = 5 := by
  have e : (51840 : ℕ) = 2 ^ 7 * 3 ^ 4 * 5 := by norm_num
  rw [e] at h
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1
        (hp.dvd_of_dvd_pow h)))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h))

theorem o2At_of_sylow {p : ℕ} [Fact p.Prime] {S : Subgroup (WeylGroup Tag.E6)}
    (hS : Nat.card S = p ^ (Nat.card (WeylGroup Tag.E6)).factorization p) {L : List (List ℕ)}
    (hcov : ∀ y ∈ S, ∃ t ∈ L, e6Certificate.Represents t y) {W : List (List (List ℕ))}
    (hc : o2Check L W = true) {y : WeylGroup Tag.E6} (hy : orderOf y = p) (c : ZMod 3) :
    O2At y c := by
  obtain ⟨g, hg⟩ := CFSG.KC.E7Plane.exists_conj_mem_of_orderOf S hS hy
  obtain ⟨t, ht, hrep⟩ := hcov _ hg
  have hne : g⁻¹ * y * g ≠ 1 := by
    intro e
    have h1 : y = 1 := by
      have e' : y = g * (g⁻¹ * y * g) * g⁻¹ := by group
      rw [e', e]
      group
    rw [h1, orderOf_one] at hy
    exact (Fact.out : p.Prime).one_lt.ne hy
  have h := o2At_conj (o2Check_sound hc ht hrep hne c) g
  have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
  rwa [e] at h

theorem e6O2Regular_of_checks {g2 g5 gw : List (List ℕ)} {w2 w3 w5 : List (List (List ℕ))}
    (h2 : subCheck g2 128 (pcTups 2 g2) = true) (h5 : subCheck g5 5 (pcTups 5 g5) = true)
    (hq : qCheckWith gw (qTups gw) = true) (c2 : o2Check (pcTups 2 g2) w2 = true)
    (c3 : o2Check (qTups gw) w3 = true) (c5 : o2Check (pcTups 5 g5) w5 = true) :
    E6O2Regular := by
  have hcardW := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.card_weylGroup_E6
  have hprime : ∀ y : WeylGroup Tag.E6, (orderOf y).Prime → ∀ c, O2At y c := by
    intro y hp c
    rcases prime_dvd_51840 hp (hcardW ▸ orderOf_dvd_natCard y) with h | h | h
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨hcard, hcov⟩ := exists_subgroup_of_subCheck h2
      exact o2At_of_sylow (by rw [hcard, hcardW, factorization_E6_two]; norm_num) hcov c2 h c
    · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨hcard, hcov⟩ := exists_subgroup_of_qCheck hq
      exact o2At_of_sylow (by rw [hcard, hcardW, factorization_E6]; norm_num) hcov c3 h c
    · have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      obtain ⟨hcard, hcov⟩ := exists_subgroup_of_subCheck h5
      exact o2At_of_sylow (by rw [hcard, hcardW, factorization_E6_five]; norm_num) hcov c5 h c
  intro w hw1 c V hV hVS
  have hn1 : orderOf w ≠ 1 := fun e => hw1 (orderOf_eq_one_iff.1 e)
  have hpos : orderOf w ≠ 0 := (orderOf_pos w).ne'
  have hp := Nat.minFac_prime hn1
  have hy : orderOf (w ^ (orderOf w / (orderOf w).minFac)) = (orderOf w).minFac :=
    orderOf_pow_orderOf_div hpos (Nat.minFac_dvd _)
  exact o2At_pow _ (hprime _ (by rw [hy]; exact hp) _) V hV hVS

end CFSG.KC.E6O2
