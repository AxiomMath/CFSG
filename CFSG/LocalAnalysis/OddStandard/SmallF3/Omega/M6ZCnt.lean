module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IOrd
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2FiveCard

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap CFSG.GroupTheory.WeirSylow

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem m6z_natCard_oGroup_eight_plus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 8) (hs : quadSign Q = 1) :
    Nat.card (OGroup Q) = 39617438515200 := by
  have hplus : IsPlusType Q :=
    (isPlusType_iff_quadSign_eq_one hQ (d := 4) (by rw [hdim])).mpr hs
  have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type (K := ZMod 3) (V := V)
    (QuadraticMap.nondegenerate_polar_iff.mpr hQ) (m := 3) (by rw [hdim]) (ε := 1)
    (Or.inl ⟨rfl, hplus⟩)
  have hval : 2 * (Nat.card (ZMod 3) : ℤ) ^ (3 * (3 + 1)) *
      ((Nat.card (ZMod 3) : ℤ) ^ (3 + 1) - 1) *
      (∏ i ∈ Finset.Icc 1 3, (((Nat.card (ZMod 3) : ℤ) ^ 2) ^ i - 1)) = 39617438515200 := by
    rw [Nat.card_zmod]
    decide +kernel
  exact_mod_cast h.trans hval

theorem m6z_natCard_oGroup_eight_minus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 8) (hs : quadSign Q = -1) :
    Nat.card (OGroup Q) = 40607874478080 := by
  have hnplus : ¬ IsPlusType Q := fun h => by
    have h1 : quadSign Q = 1 :=
      (isPlusType_iff_quadSign_eq_one hQ (d := 4) (by rw [hdim])).mp h
    rw [hs] at h1
    exact (by decide : (-1 : ℤˣ) ≠ 1) h1
  have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type (K := ZMod 3) (V := V)
    (QuadraticMap.nondegenerate_polar_iff.mpr hQ) (m := 3) (by rw [hdim]) (ε := -1)
    (Or.inr ⟨rfl, hnplus⟩)
  have hval : 2 * (Nat.card (ZMod 3) : ℤ) ^ (3 * (3 + 1)) *
      ((Nat.card (ZMod 3) : ℤ) ^ (3 + 1) - (-1)) *
      (∏ i ∈ Finset.Icc 1 3, (((Nat.card (ZMod 3) : ℤ) ^ 2) ^ i - 1)) = 40607874478080 := by
    rw [Nat.card_zmod]
    decide +kernel
  exact_mod_cast h.trans hval

theorem m6z_card_four_plus_mul (hQ : Q.Nondegenerate) {t : OGroup Q} (htt : t * t = 1)
    (hty : invType t = (4, 1)) :
    Nat.card {u : OGroup Q // u * u = 1 ∧ invType u = (4, 1)} *
      (Nat.card (OGroup (Q.restrict (fixSp t))) * Nat.card (OGroup (Q.restrict (commSp t)))) =
      Nat.card (OGroup Q) := by
  rw [← natCard_centralizer_involution hQ htt]
  have hiff : ∀ u : OGroup Q, (u * u = 1 ∧ invType u = (4, 1)) ↔
      u ∈ MulAction.orbit (ConjAct (OGroup Q)) t := by
    intro u
    rw [ConjAct.mem_orbit_conjAct, isConj_comm]
    constructor
    · rintro ⟨huu, hu⟩
      exact (isConj_iff_invType_eq hQ htt huu).mpr (hty.trans hu.symm)
    · intro hc
      obtain ⟨c, hc⟩ := isConj_iff.mp hc
      have huu : u * u = 1 := by
        rw [← hc]
        calc c * t * c⁻¹ * (c * t * c⁻¹) = c * (t * t) * c⁻¹ := by group
          _ = 1 := by rw [htt]; group
      exact ⟨huu, by rw [← hc, invType_conj hQ htt c, hty]⟩
  rw [Nat.card_congr (Equiv.subtypeEquivRight hiff),
    Subgroup.nat_card_centralizer_nat_card_stabilizer, ← Nat.card_prod,
    Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (ConjAct (OGroup Q)) t)]
  exact Nat.card_congr ConjAct.ofConjAct.toEquiv

private theorem m6z_fixSp_data (hQ : Q.Nondegenerate) {t : OGroup Q} (htt : t * t = 1)
    (hty : invType t = (4, 1)) :
    Module.finrank (ZMod 3) (fixSp t) + 4 = Module.finrank (ZMod 3) V ∧
      quadSign (Q.restrict (fixSp t)) = quadSign Q := by
  have hd : invDim t = 4 := congrArg Prod.fst hty
  have hs : invSign t = 1 := congrArg Prod.snd hty
  refine ⟨?_, ?_⟩
  · have h := finrank_fixSp_add_finrank_commSp (Q := Q) t
    have hd' : Module.finrank (ZMod 3) (commSp t) = 4 := hd
    omega
  · have h := quadSign_fixSp_eq hQ htt
    rw [hd, hs] at h
    have h1 : ((-1 : ℤˣ)) ^ (4 * (Module.finrank (ZMod 3) V - 4)) = 1 :=
      Even.neg_one_pow ⟨2 * (Module.finrank (ZMod 3) V - 4), by omega⟩
    rw [h, h1, mul_one, mul_one]

private theorem m6z_card_four_plus_aux (hQ : Q.Nondegenerate)
    (h5 : 5 ≤ Module.finrank (ZMod 3) V) {a M : ℕ} (hM : Nat.card (OGroup Q) = M)
    (hfix : ∀ t : OGroup Q, t * t = 1 → invType t = (4, 1) →
      Nat.card (OGroup (Q.restrict (fixSp t))) = a) :
    Nat.card {u : OGroup Q // u * u = 1 ∧ invType u = (4, 1)} * (a * 1152) = M := by
  obtain ⟨t, htt, hty⟩ := (exists_involution_of_type hQ 4 1).mpr
    ⟨by omega, fun h => by omega, fun h => by omega⟩
  have hdimC : Module.finrank (ZMod 3) (commSp t) = 4 := congrArg Prod.fst hty
  have hsgnC : quadSign (Q.restrict (commSp t)) = 1 := congrArg Prod.snd hty
  have h := m6z_card_four_plus_mul hQ htt hty
  rw [hfix t htt hty, natCard_oGroup_four_plus (nondegenerate_restrict_commSp hQ htt) hdimC hsgnC,
    hM] at h
  exact h

theorem m6z_card_four_plus_five (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 5) :
    Nat.card {u : OGroup Q // u * u = 1 ∧ invType u = (4, 1)} = 45 := by
  have h := m6z_card_four_plus_aux hQ (by omega) (natCard_oGroup_five hQ hdim) (a := 2)
    (fun t htt hty => natCard_oGroup_one (nondegenerate_restrict_fixSp hQ htt)
      (by have := (m6z_fixSp_data hQ htt hty).1; omega))
  omega

theorem m6z_card_four_plus_six_plus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = 1) :
    Nat.card {u : OGroup Q // u * u = 1 ∧ invType u = (4, 1)} = 5265 := by
  have h := m6z_card_four_plus_aux hQ (by omega) (natCard_oGroup_six_plus hQ hdim hs) (a := 4)
    (fun t htt hty => natCard_oGroup_two_plus (nondegenerate_restrict_fixSp hQ htt)
      (by have := (m6z_fixSp_data hQ htt hty).1; omega)
      (by rw [(m6z_fixSp_data hQ htt hty).2]; exact hs))
  omega

theorem m6z_card_four_plus_six_minus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = -1) :
    Nat.card {u : OGroup Q // u * u = 1 ∧ invType u = (4, 1)} = 2835 := by
  have h := m6z_card_four_plus_aux hQ (by omega) (natCard_oGroup_six_minus hQ hdim hs) (a := 8)
    (fun t htt hty => natCard_oGroup_two_minus (nondegenerate_restrict_fixSp hQ htt)
      (by have := (m6z_fixSp_data hQ htt hty).1; omega)
      (by rw [(m6z_fixSp_data hQ htt hty).2]; exact hs))
  omega

theorem m6z_card_four_plus_seven (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 7) :
    Nat.card {u : OGroup Q // u * u = 1 ∧ invType u = (4, 1)} = 331695 := by
  have h := m6z_card_four_plus_aux hQ (by omega) (natCard_oGroup_seven hQ hdim) (a := 48)
    (fun t htt hty => natCard_oGroup_three (nondegenerate_restrict_fixSp hQ htt)
      (by have := (m6z_fixSp_data hQ htt hty).1; omega))
  omega

theorem m6z_card_four_plus_eight_minus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 8) (hs : quadSign Q = -1) :
    Nat.card {u : OGroup Q // u * u = 1 ∧ invType u = (4, 1)} = 24479091 := by
  have h := m6z_card_four_plus_aux hQ (by omega) (m6z_natCard_oGroup_eight_minus hQ hdim hs)
    (a := 1440)
    (fun t htt hty => natCard_oGroup_four_minus (nondegenerate_restrict_fixSp hQ htt)
      (by have := (m6z_fixSp_data hQ htt hty).1; omega)
      (by rw [(m6z_fixSp_data hQ htt hty).2]; exact hs))
  omega

theorem m6z_card_four_plus_eight_plus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 8) (hs : quadSign Q = 1) :
    Nat.card {u : OGroup Q // u * u = 1 ∧ invType u = (4, 1)} = 29852550 := by
  have h := m6z_card_four_plus_aux hQ (by omega) (m6z_natCard_oGroup_eight_plus hQ hdim hs)
    (a := 1152)
    (fun t htt hty => natCard_oGroup_four_plus (nondegenerate_restrict_fixSp hQ htt)
      (by have := (m6z_fixSp_data hQ htt hty).1; omega)
      (by rw [(m6z_fixSp_data hQ htt hty).2]; exact hs))
  omega

end CFSG.OddStandard.SmallF3.Omega
