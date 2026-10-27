module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatAlt
public import CFSG.Timmesfeld.Orders.Distinct
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatCovers

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (ProperFixedComponent IsAltType)
open scoped Nat

theorem card_of_lieModel_PSp_two_pow {X : Type} [Group X] {m f : ℕ}
    (h : LieModel X .PSp m 2 f) : Nat.card X = Open.ordBC m (2 ^ f) :=
  (Timmesfeld.card_statedClassicalModel_two (F4Pilot.statedClassicalModel_of_lieModel_psp h)).2.2.1
    rfl

theorem ordBC_two_pow_bounds {m f : ℕ} (hf : 1 ≤ f) :
    2 ^ (f * (m * m)) ∣ Open.ordBC m (2 ^ f) ∧ 0 < Open.ordBC m (2 ^ f) ∧
      Open.ordBC m (2 ^ f) ≤ 2 ^ (3 * (f * (m * m))) := by
  obtain ⟨r, hr, hm⟩ := (Timmesfeld.Orders.profile_ordBC (n := m) hf).two
  refine ⟨hm ▸ Dvd.intro _ rfl, hm ▸ Nat.mul_pos (by positivity) hr.pos, ?_⟩
  set q := 2 ^ f with hq
  have hq2 : 2 ≤ q := by
    rw [hq]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hgcd : Nat.gcd 2 (q - 1) = 1 :=
    Nat.coprime_two_left.mpr (Timmesfeld.Orders.odd_two_pow_sub_one (by omega))
  have hP : ∏ i ∈ Finset.Icc 1 m, (q ^ (2 * i) - 1) ≤ (q ^ (2 * m)) ^ m := by
    have h := Finset.prod_le_pow_card (Finset.Icc 1 m) (fun i => q ^ (2 * i) - 1) (q ^ (2 * m))
      (fun i hi => le_trans (Nat.sub_le _ _)
        (Nat.pow_le_pow_right (by omega) (by simp only [Finset.mem_Icc] at hi; omega)))
    rwa [Nat.card_Icc, Nat.add_sub_cancel] at h
  calc Open.ordBC m q = q ^ (m * m) * ∏ i ∈ Finset.Icc 1 m, (q ^ (2 * i) - 1) := by
        rw [Open.ordBC, hgcd, Nat.div_one]
    _ ≤ q ^ (m * m) * (q ^ (2 * m)) ^ m := Nat.mul_le_mul_left _ hP
    _ = 2 ^ (3 * (f * (m * m))) := by
        rw [hq, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_add]
        congr 1
        ring

theorem ordBC_two_one_eq : Open.ordBC 2 (2 ^ 1) = 720 := by decide

theorem ordBC_two_two_eq : Open.ordBC 2 (2 ^ 2) = 979200 := by decide

theorem ordBC_two_three_eq : Open.ordBC 2 (2 ^ 3) = 1056706560 := by decide

theorem ordBC_three_one_eq : Open.ordBC 3 (2 ^ 1) = 1451520 := by decide

theorem ordBC_two_pow_ne_factorial_div_two {m f k : ℕ} (hm : 2 ≤ m) (hf : 1 ≤ f) :
    Open.ordBC m (2 ^ f) ≠ k ! / 2 := by
  intro hk
  obtain ⟨hdvd, hpos, hle⟩ := ordBC_two_pow_bounds (m := m) hf
  set M := f * (m * m) with hM
  have hk2 : 2 ≤ k := by
    by_contra h
    interval_cases k <;> simp at hk <;> omega
  have hk! : k ! = 2 * Open.ordBC m (2 ^ f) := by
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
  have hmm : 4 ≤ m * m := Nat.mul_le_mul hm hm
  have hTM : m * m ≤ M := Nat.le_mul_of_pos_left _ hf
  have hf3 : f ≤ 3 := by
    by_contra h
    have : 4 * 4 ≤ f * (m * m) := Nat.mul_le_mul (by omega) hmm
    omega
  have hm3 : m ≤ 3 := by
    by_contra h
    have : 4 * 4 ≤ m * m := Nat.mul_le_mul (by omega) (by omega)
    omega
  have hk16 : k < 16 := by
    by_contra h
    have h1 : (16 : ℕ)! ≤ k ! := Nat.factorial_le (by omega)
    have h2 : 2 ^ (3 * M + 1) ≤ 2 ^ 37 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 2 ^ 37 < (16 : ℕ)! := by decide
    omega
  interval_cases m <;> interval_cases f <;> simp only [hM] at hM12 hlt <;>
    first
    | omega
    | (rw [ordBC_two_one_eq] at hk; revert hk; interval_cases k <;> decide)
    | (rw [ordBC_two_two_eq] at hk; revert hk; interval_cases k <;> decide)
    | (rw [ordBC_two_three_eq] at hk; revert hk; interval_cases k <;> decide)
    | (rw [ordBC_three_one_eq] at hk; revert hk; interval_cases k <;> decide)

theorem two_pow_four_dvd_ordBC {m f : ℕ} (hm : 2 ≤ m) (hf : 1 ≤ f) :
    2 ^ 4 ∣ Open.ordBC m (2 ^ f) := by
  obtain ⟨hdvd, -, -⟩ := ordBC_two_pow_bounds (m := m) hf
  have hmm : 4 ≤ m * m := Nat.mul_le_mul hm hm
  have hTM : m * m ≤ f * (m * m) := Nat.le_mul_of_pos_left _ hf
  exact (Nat.pow_dvd_pow 2 (by omega)).trans hdvd

@[expose] def CatSp2mAlternating : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    (∃ n : ℕ, 5 ≤ n ∧ Nonempty (S ≃* alternatingGroup (Fin n))) →
    ∀ σ : MulAut S, orderOf σ = 2 → ∀ (m f : ℕ) (D : Subgroup (fixedSubgroup σ)),
      IsComponent D → LieModel D .PSp m 2 f → False

theorem catSp2mAlternating : CatSp2mAlternating := by
  intro S _ _ _ _ ⟨n, hn, ⟨e⟩⟩ σ hσ m f D hD hDm
  have hcl := F4Pilot.statedClassicalModel_of_lieModel_psp hDm
  have hf : 1 ≤ f := hcl.1.2.1
  have hm : 2 ≤ m := hcl.1.2.2.1
  have hcardD := card_of_lieModel_PSp_two_pow hDm
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
  have hdvdS : Nat.card D ∣ Nat.card S := hcardP ▸ card_subgroup_dvd_card P
  have hSn : Nat.card S = n ! / 2 := by
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  by_cases hn6 : n = 6
  · subst hn6
    rw [hSn, hcardD, show (6 : ℕ)! / 2 = 360 by decide] at hdvdS
    exact absurd ((two_pow_four_dvd_ordBC hm hf).trans hdvdS) (by decide)
  ·
    set L := P.subgroupOf (fixedSubgroup σ) with hLdef
    let eLD : L ≃* D := MulEquiv.subgroupCongr hPsub
    have hsD : IsSimpleGroup D := F4Pilot.isSimpleGroup_of_lieModel_PSp hDm
    have hsL : IsSimpleGroup L := eLD.isSimpleGroup
    have hqL : IsQuasisimple L := (LocalAnalysis.ComponentInitial.isQuasisimple_congr eLD).2 hD.1
    have hZL : center L = ⊥ := F4Pilot.center_eq_bot_of_isQuasisimple hqL hsL
    obtain ⟨-, ⟨eZ⟩⟩ := hPC.fusionZStar_equiv_of_quasisimple hqL
    let eP : P ⧸ Open.fusionZStar P ≃* D :=
      (eZ.trans ((QuotientGroup.quotientMulEquivOfEq hZL).trans QuotientGroup.quotientBot)).trans
        eLD
    obtain ⟨hPC', ⟨eT⟩⟩ := hPC.map e
    have hAlt := CFSG.ComponentClassification.CatLeaf.isAltType_of_properFixedComponent_alternating
      hn hn6 hPC'
    obtain ⟨Ω, _, _, hΩ, ⟨eA⟩⟩ := IsAltType.of_mulEquiv (eP.symm.trans eT) hAlt
    have : Nontrivial Ω := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    apply ordBC_two_pow_ne_factorial_div_two hm hf (k := Fintype.card Ω)
    rw [← hcardD, Nat.card_congr eA.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card]

theorem catSp6Alternating_of_catSp2mAlternating (h : CatSp2mAlternating) :
    F4Pilot.CatSp6Alternating :=
  fun S _ _ hS hna hA σ hσ f D hD hD6 => h S hS hna hA σ hσ 3 f D hD hD6

end CFSG.SeitzReduction.SymplecticPilot
