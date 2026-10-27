module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatStatement
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatAlt
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatTypeDet

public section

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (ProperFixedComponent IsAltType)
open CFSG.Timmesfeld.Orders (odd_pow_sub_one odd_pow_add_one)
open scoped Nat

theorem card_of_lieModel_POmega_two {X : Type} [Group X] {t : StatedLieTag} {m f : ℕ}
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus) (h : LieModel X t m 2 f) :
    Nat.card X = F4Pilot.evenLieOrder t m f :=
  F4Pilot.card_eq_evenLieOrder_of_mem_classicalTags (by rcases ht with rfl | rfl <;> decide) h

theorem prod_two_mul_factors_le (q n : ℕ) :
    ∏ i ∈ Finset.Icc 1 n, (q ^ (2 * i) - 1) ≤ q ^ (n * (n + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_Icc_succ_top (by omega)]
    calc (∏ i ∈ Finset.Icc 1 n, (q ^ (2 * i) - 1)) * (q ^ (2 * (n + 1)) - 1)
        ≤ q ^ (n * (n + 1)) * q ^ (2 * (n + 1)) := Nat.mul_le_mul ih (Nat.sub_le _ _)
      _ = q ^ ((n + 1) * (n + 1 + 1)) := by rw [← pow_add]; congr 1; ring

theorem ordD_two_pow_bounds {n f : ℕ} (hn : 2 ≤ n) (hf : 1 ≤ f) :
    2 ^ (f * (n * (n - 1))) ∣ Open.ordD n (2 ^ f) ∧ 0 < Open.ordD n (2 ^ f) ∧
      Open.ordD n (2 ^ f) ≤ 2 ^ (3 * (f * (n * (n - 1)))) := by
  obtain ⟨r, hr, hm⟩ := (F4Pilot.profile_idxD (by omega : 1 ≤ n) hf).two
  refine ⟨hm ▸ Dvd.intro _ rfl, hm ▸ Nat.mul_pos (by positivity) hr.pos, ?_⟩
  set q := 2 ^ f with hq
  have h1 : Odd (q ^ n - 1) := odd_pow_sub_one hf (by omega)
  have hord : Open.ordD n q = q ^ (n * (n - 1)) *
      ((q ^ n - 1) * ∏ i ∈ Finset.Icc 1 (n - 1), (q ^ (2 * i) - 1)) := by
    rw [Open.ordD, Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr h1), Nat.div_one, mul_assoc]
  have hP := prod_two_mul_factors_le q (n - 1)
  rw [show n - 1 + 1 = n by omega] at hP
  calc Open.ordD n q = q ^ (n * (n - 1)) *
        ((q ^ n - 1) * ∏ i ∈ Finset.Icc 1 (n - 1), (q ^ (2 * i) - 1)) := hord
    _ ≤ q ^ (n * (n - 1)) * (q ^ n * q ^ ((n - 1) * n)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.sub_le _ _) hP)
    _ = 2 ^ (f * (n * (n - 1) + (n + (n - 1) * n))) := by
        rw [hq, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add, ← mul_add, ← mul_add]
    _ ≤ 2 ^ (3 * (f * (n * (n - 1)))) := by
        refine Nat.pow_le_pow_right (by norm_num) ?_
        have h2 : n ≤ n * (n - 1) := Nat.le_mul_of_pos_right _ (by omega)
        have h3 : (n - 1) * n = n * (n - 1) := by ring
        rw [h3]
        nlinarith

theorem ordTwistedD_two_pow_bounds {n f : ℕ} (hn : 3 ≤ n) (hf : 1 ≤ f) :
    2 ^ (f * (n * (n - 1))) ∣ Open.ordTwistedD n (2 ^ f) ∧ 0 < Open.ordTwistedD n (2 ^ f) ∧
      Open.ordTwistedD n (2 ^ f) ≤ 2 ^ (3 * (f * (n * (n - 1)))) := by
  obtain ⟨r, hr, hm⟩ := (F4Pilot.profile_idx2D (by omega : 1 ≤ n) hf).two
  refine ⟨hm ▸ Dvd.intro _ rfl, hm ▸ Nat.mul_pos (by positivity) hr.pos, ?_⟩
  set q := 2 ^ f with hq
  have hq2 : 2 ≤ q := by
    rw [hq]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have h1 : Odd (q ^ n + 1) := odd_pow_add_one hf (by omega)
  have hord : Open.ordTwistedD n q = q ^ (n * (n - 1)) *
      ((q ^ n + 1) * ∏ i ∈ Finset.Icc 1 (n - 1), (q ^ (2 * i) - 1)) := by
    rw [Open.ordTwistedD, Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr h1), Nat.div_one,
      mul_assoc]
  have hP := prod_two_mul_factors_le q (n - 1)
  rw [show n - 1 + 1 = n by omega] at hP
  have hplus : q ^ n + 1 ≤ q ^ (n + 1) := by
    have : 1 ≤ q ^ n := Nat.one_le_pow _ _ (by omega)
    rw [pow_succ]
    nlinarith
  calc Open.ordTwistedD n q = q ^ (n * (n - 1)) *
        ((q ^ n + 1) * ∏ i ∈ Finset.Icc 1 (n - 1), (q ^ (2 * i) - 1)) := hord
    _ ≤ q ^ (n * (n - 1)) * (q ^ (n + 1) * q ^ ((n - 1) * n)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul hplus hP)
    _ = 2 ^ (f * (n * (n - 1) + (n + 1 + (n - 1) * n))) := by
        rw [hq, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add, ← mul_add, ← mul_add]
    _ ≤ 2 ^ (3 * (f * (n * (n - 1)))) := by
        refine Nat.pow_le_pow_right (by norm_num) ?_
        have h2 : n + 1 ≤ n * (n - 1) := by
          have : n * 2 ≤ n * (n - 1) := Nat.mul_le_mul_left _ (by omega)
          omega
        have h3 : (n - 1) * n = n * (n - 1) := by ring
        rw [h3]
        nlinarith

theorem evenLieOrder_POmega_bounds {t : StatedLieTag} (ht : t = .POmegaPlus ∨ t = .POmegaMinus)
    {m f : ℕ} (hm : 4 ≤ m) (hf : 1 ≤ f) :
    2 ^ (f * (m * (m - 1))) ∣ F4Pilot.evenLieOrder t m f ∧ 0 < F4Pilot.evenLieOrder t m f ∧
      F4Pilot.evenLieOrder t m f ≤ 2 ^ (3 * (f * (m * (m - 1)))) := by
  rcases ht with rfl | rfl
  · exact ordD_two_pow_bounds (by omega) hf
  · exact ordTwistedD_two_pow_bounds (by omega) hf

theorem two_pow_twelve_dvd_evenLieOrder_POmega {t : StatedLieTag}
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus) {m f : ℕ} (hm : 4 ≤ m) (hf : 1 ≤ f) :
    2 ^ 12 ∣ F4Pilot.evenLieOrder t m f := by
  refine (Nat.pow_dvd_pow 2 ?_).trans (evenLieOrder_POmega_bounds ht hm hf).1
  have h1 : 4 * 3 ≤ m * (m - 1) := Nat.mul_le_mul hm (by omega)
  have h2 : m * (m - 1) ≤ f * (m * (m - 1)) := Nat.le_mul_of_pos_left _ hf
  omega

theorem two_pow_twelve_dvd_card_of_lieModel_POmega {X : Type} [Group X] {t : StatedLieTag}
    {m f : ℕ} (ht : t = .POmegaPlus ∨ t = .POmegaMinus) (h : LieModel X t m 2 f) :
    2 ^ 12 ∣ Nat.card X := by
  rw [card_of_lieModel_POmega_two ht h]
  exact two_pow_twelve_dvd_evenLieOrder_POmega ht (four_le_of_lieModel_POmega ht h)
    (one_le_of_lieModel_POmega ht h)

theorem ordD_four_two_eq : Open.ordD 4 (2 ^ 1) = 174182400 := by decide

theorem ordTwistedD_four_two_eq : Open.ordTwistedD 4 (2 ^ 1) = 197406720 := by decide

theorem evenLieOrder_POmega_ne_factorial_div_two {t : StatedLieTag}
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus) {m f k : ℕ} (hm : 4 ≤ m) (hf : 1 ≤ f) :
    F4Pilot.evenLieOrder t m f ≠ k ! / 2 := by
  intro hk
  obtain ⟨hdvd, hpos, hle⟩ := evenLieOrder_POmega_bounds ht hm hf
  set M := f * (m * (m - 1)) with hM
  have hk2 : 2 ≤ k := by
    by_contra h
    interval_cases k <;> simp at hk <;> omega
  have hk! : k ! = 2 * F4Pilot.evenLieOrder t m f := by
    rw [hk, Nat.mul_div_cancel' (Nat.dvd_factorial (by norm_num) hk2)]
  have hdvd2 : 2 ^ (M + 1) ∣ k ! := by
    rw [hk!, pow_succ, mul_comm]
    exact Nat.mul_dvd_mul_left 2 hdvd
  have hlt : M + 1 < k := by
    have h1 := Nat.emultiplicity_two_factorial_lt (show k ≠ 0 by omega)
    have h2 := le_emultiplicity_of_pow_dvd hdvd2
    exact_mod_cast lt_of_le_of_lt h2 h1
  have hfac : (M + 2)! ≤ k ! := Nat.factorial_le (by omega)
  have hkle : k ! ≤ 2 ^ (3 * M + 1) := by
    rw [hk!, pow_succ]
    omega
  have hM12 : M ≤ 12 := by
    by_contra h
    have := LinearPilot.two_pow_lt_factorial_of_thirteen_le (show 13 ≤ M by omega)
    omega
  have h12 : 12 ≤ m * (m - 1) := by
    have : 4 * 3 ≤ m * (m - 1) := Nat.mul_le_mul hm (by omega)
    omega
  have hTM : m * (m - 1) ≤ M := Nat.le_mul_of_pos_left _ hf
  have hf1 : f = 1 := by
    by_contra h
    have : 2 * 12 ≤ f * (m * (m - 1)) := Nat.mul_le_mul (by omega) h12
    omega
  have hm4 : m = 4 := by
    by_contra h
    have : 5 * 4 ≤ m * (m - 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  subst hf1 hm4
  have hk13 : 13 < k := by omega
  have hk15 : k < 15 := by
    by_contra h
    have h1 : (15 : ℕ)! ≤ k ! := Nat.factorial_le (by omega)
    have h2 : 2 ^ (3 * M + 1) ≤ 2 ^ 37 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 2 ^ 37 < (15 : ℕ)! := by decide
    omega
  rcases ht with rfl | rfl
  · change Open.ordD 4 (2 ^ 1) = k ! / 2 at hk
    rw [ordD_four_two_eq] at hk
    revert hk
    interval_cases k
    decide
  · change Open.ordTwistedD 4 (2 ^ 1) = k ! / 2 at hk
    rw [ordTwistedD_four_two_eq] at hk
    revert hk
    interval_cases k
    decide

theorem catOmegaAlternating : CatOmegaAlternating := by
  intro S _ _ _ _ ⟨n, hn, ⟨e⟩⟩ σ hσ t m f D ht hD hDm
  have hm : 4 ≤ m := four_le_of_lieModel_POmega ht hDm
  have hf : 1 ≤ f := one_le_of_lieModel_POmega ht hDm
  have hcardDZ := card_of_lieModel_POmega_two ht hDm
  have hσ2 : σ ^ 2 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hσσ : ∀ y, σ (σ y) = y := fun y => by
    have := congrArg (fun ψ : MulAut S => ψ y) hσ2
    simpa [pow_two] using this
  set P : Subgroup S := D.map (fixedSubgroup σ).subtype with hPdef
  have hPF : P ≤ fixedSubgroup σ := map_subtype_le D
  have hPsub : P.subgroupOf (fixedSubgroup σ) = D :=
    comap_map_eq_self_of_injective (fixedSubgroup σ).subtype_injective D
  have hPne : P ≠ ⊤ := by
    intro htop
    have hσ1 : σ = 1 := by
      ext y
      exact hPF (htop ▸ mem_top y)
    rw [hσ1, orderOf_one] at hσ
    exact absurd hσ (by norm_num)
  have hPC : ProperFixedComponent σ P :=
    ⟨hσσ, hPF, hPsub ▸ LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hD, hPne⟩
  have hcardP : Nat.card P = Nat.card D :=
    card_map_of_injective (fixedSubgroup σ).subtype_injective
  have hdvdS : Nat.card (D ⧸ center D) ∣ Nat.card S :=
    (card_quotient_dvd_card (center D)).trans (hcardP ▸ card_subgroup_dvd_card P)
  have hSn : Nat.card S = n ! / 2 := by
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  by_cases hn6 : n = 6
  · subst hn6
    rw [hSn, hcardDZ, show (6 : ℕ)! / 2 = 360 by decide] at hdvdS
    exact absurd ((two_pow_twelve_dvd_evenLieOrder_POmega ht hm hf).trans hdvdS) (by decide)
  ·
    set L := P.subgroupOf (fixedSubgroup σ) with hLdef
    let eLD : L ≃* D := MulEquiv.subgroupCongr hPsub
    have hqL : IsQuasisimple L := (LocalAnalysis.ComponentInitial.isQuasisimple_congr eLD).2 hD.1
    obtain ⟨-, ⟨eZ⟩⟩ := hPC.fusionZStar_equiv_of_quasisimple hqL
    let eP : P ⧸ Open.fusionZStar P ≃* D ⧸ center D :=
      eZ.trans (QuotientGroup.congr (center L) (center D) eLD (Subgroup.map_center_eq eLD))
    obtain ⟨hPC', ⟨eT⟩⟩ := hPC.map e
    have hAlt := CFSG.ComponentClassification.CatLeaf.isAltType_of_properFixedComponent_alternating
      hn hn6 hPC'
    have hAltD : IsAltType (D ⧸ center D) := IsAltType.of_mulEquiv (eP.symm.trans eT) hAlt
    obtain ⟨Ω, _, _, hΩ, ⟨eA⟩⟩ := hAltD
    have : Nontrivial Ω := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    have hcardΩ : F4Pilot.evenLieOrder t m f = (Fintype.card Ω)! / 2 := by
      rw [← hcardDZ, Nat.card_congr eA.toEquiv, nat_card_alternatingGroup,
        Nat.card_eq_fintype_card]
    exact evenLieOrder_POmega_ne_factorial_div_two ht hm hf hcardΩ

end CFSG.SeitzReduction.OmegaPilot
