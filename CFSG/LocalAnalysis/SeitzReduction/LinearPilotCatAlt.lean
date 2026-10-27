module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatStatement
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafAlt
public import CFSG.LocalAnalysis.ComponentInitial.LocalBMaximalPropagation
public import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.SeitzReduction.LinearPilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (ProperFixedComponent IsAltType)
open scoped Nat

theorem card_of_lieModel_PSL_two {X : Type} [Group X] {m f : ℕ} (h : LieModel X .PSL m 2 f) :
    Nat.card X = Open.ordA (m - 1) (2 ^ f) :=
  (Timmesfeld.card_statedClassicalModel_two
    (ComponentClassification.CatLeaf.statedClassicalModel_of_lieModel_psl h)).1 rfl

theorem ordA_two_pow_bounds {n f : ℕ} (hn : 1 ≤ n) (hf : 1 ≤ f) :
    2 ^ (f * (n * (n + 1) / 2)) ∣ Open.ordA n (2 ^ f) ∧ 0 < Open.ordA n (2 ^ f) ∧
      Open.ordA n (2 ^ f) ≤ 2 ^ (3 * (f * (n * (n + 1) / 2))) := by
  set q := 2 ^ f with hq
  set T := n * (n + 1) / 2 with hT
  have hq2 : 2 ≤ q := by
    rw [hq]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  set P := ∏ i ∈ Finset.Icc 2 (n + 1), (q ^ i - 1) with hP
  set g := Nat.gcd (n + 1) (q - 1) with hg
  have hgP : g ∣ P := by
    have h1 : g ∣ q - 1 := Nat.gcd_dvd_right _ _
    have h2 : q - 1 ∣ q ^ 2 - 1 := by simpa using Nat.sub_dvd_pow_sub_pow q 1 2
    have h3 : q ^ 2 - 1 ∣ P :=
      Finset.dvd_prod_of_mem (fun i => q ^ i - 1) (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)
    exact h1.trans (h2.trans h3)
  have hPpos : 0 < P := Finset.prod_pos fun i hi => by
    have h2i : 2 ≤ i := (Finset.mem_Icc.mp hi).1
    have : 1 < q ^ i := Nat.one_lt_pow (by omega) (by omega)
    omega
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ (by omega)
  have hord : Open.ordA n q = q ^ T * (P / g) := by
    rw [Open.ordA, Nat.mul_div_assoc _ hgP]
  have hT2 : (n + 1) * n = 2 * T := by
    rw [hT, mul_comm]
    exact (Nat.mul_div_cancel' (Nat.even_mul_succ_self n).two_dvd).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [hord, hq, ← pow_mul]
    exact Dvd.intro _ rfl
  · rw [hord]
    exact Nat.mul_pos (by positivity) (Nat.div_pos (Nat.le_of_dvd hPpos hgP) hgpos)
  · have hPle : P ≤ (q ^ (n + 1)) ^ n := by
      have h := Finset.prod_le_pow_card (Finset.Icc 2 (n + 1)) (fun i => q ^ i - 1)
        (q ^ (n + 1)) (fun i hi =>
          le_trans (Nat.sub_le _ _) (Nat.pow_le_pow_right (by omega) (Finset.mem_Icc.mp hi).2))
      rwa [Nat.card_Icc, show n + 1 + 1 - 2 = n by omega] at h
    calc Open.ordA n q = q ^ T * (P / g) := hord
      _ ≤ q ^ T * P := Nat.mul_le_mul_left _ (Nat.div_le_self _ _)
      _ ≤ q ^ T * (q ^ (n + 1)) ^ n := Nat.mul_le_mul_left _ hPle
      _ = 2 ^ (3 * (f * T)) := by
        have e1 : q ^ T = 2 ^ (f * T) := by rw [hq, ← pow_mul]
        have e2 : (q ^ (n + 1)) ^ n = 2 ^ (f * (2 * T)) := by
          rw [hq, ← pow_mul, ← pow_mul, hT2]
        rw [e1, e2, ← pow_add]
        congr 1
        ring

theorem two_pow_lt_factorial_of_thirteen_le {M : ℕ} (hM : 13 ≤ M) :
    2 ^ (3 * M + 1) < (M + 2)! := by
  induction M, hM using Nat.le_induction with
  | base => decide
  | succ M hM ih =>
    calc 2 ^ (3 * (M + 1) + 1) = 2 ^ (3 * M + 1) * 8 := by ring
      _ < (M + 2)! * 8 := Nat.mul_lt_mul_of_pos_right ih (by norm_num)
      _ ≤ (M + 2)! * (M + 2 + 1) := Nat.mul_le_mul_left _ (by omega)
      _ = (M + 1 + 2)! := by
        rw [mul_comm]
        exact (Nat.factorial_succ (M + 2)).symm

theorem ordA_two_pow_eq_factorial_div_two {n f k : ℕ} (hn : 2 ≤ n) (hf : 1 ≤ f)
    (hk : Open.ordA n (2 ^ f) = k ! / 2) : (n = 2 ∧ f = 2) ∨ (n = 3 ∧ f = 1) := by
  obtain ⟨hdvd, hpos, hle⟩ := ordA_two_pow_bounds (by omega : 1 ≤ n) hf
  set M := f * (n * (n + 1) / 2) with hM
  have hk2 : 2 ≤ k := by
    by_contra h
    interval_cases k <;> simp at hk <;> omega
  have hk! : k ! = 2 * Open.ordA n (2 ^ f) := by
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
    have := two_pow_lt_factorial_of_thirteen_le (show 13 ≤ M by omega)
    omega
  have hT3 : 3 ≤ n * (n + 1) / 2 := by
    have : 2 * 3 ≤ n * (n + 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  have hTM : n * (n + 1) / 2 ≤ M := Nat.le_mul_of_pos_left _ hf
  have hf4 : f ≤ 4 := by
    by_contra h
    have : 5 * 3 ≤ f * (n * (n + 1) / 2) := Nat.mul_le_mul (by omega) hT3
    omega
  have hn4 : n ≤ 4 := by
    by_contra h
    have : 5 * 6 ≤ n * (n + 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  have hk16 : k < 16 := by
    by_contra h
    have h1 : (16 : ℕ)! ≤ k ! := Nat.factorial_le (by omega)
    have h2 : 2 ^ (3 * M + 1) ≤ 2 ^ 37 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 2 ^ 37 < (16 : ℕ)! := by decide
    omega
  interval_cases n <;> interval_cases f <;> simp only [hM] at hM12 hlt <;>
    first
    | omega
    | (left; omega)
    | (right; omega)
    | (exfalso; revert hk; interval_cases k <;> decide)

theorem catSLmAlternating : CatSLmAlternating := by
  intro S _ _ _ _ ⟨n, hn, ⟨e⟩⟩ σ hσ m f D hm hD hDm
  have hf : 1 ≤ f :=
    (ComponentClassification.CatLeaf.statedClassicalModel_of_lieModel_psl hDm).1.2.1
  have hcardDZ := card_of_lieModel_PSL_two hDm
  obtain ⟨hdvd, -, -⟩ := ordA_two_pow_bounds (by omega : 1 ≤ m - 1) hf
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
    exfalso
    rw [hSn, hcardDZ, show (6 : ℕ)! / 2 = 360 by decide] at hdvdS
    have h2 := hdvd.trans hdvdS
    set M := f * ((m - 1) * (m - 1 + 1) / 2) with hM
    have hM3 : M ≤ 3 := by
      by_contra h
      have h16 : 2 ^ 4 ∣ 2 ^ M := Nat.pow_dvd_pow 2 (by omega)
      have := h16.trans h2
      revert this
      decide
    have hT3 : 3 ≤ (m - 1) * (m - 1 + 1) / 2 := by
      have : 2 * 3 ≤ (m - 1) * (m - 1 + 1) := Nat.mul_le_mul (by omega) (by omega)
      omega
    have hTM : (m - 1) * (m - 1 + 1) / 2 ≤ M := Nat.le_mul_of_pos_left _ hf
    have hf1 : f = 1 := by
      by_contra h
      have : 2 * 3 ≤ f * ((m - 1) * (m - 1 + 1) / 2) := Nat.mul_le_mul (by omega) hT3
      omega
    have hm3 : m = 3 := by
      by_contra h
      have : 3 * 4 ≤ (m - 1) * (m - 1 + 1) := Nat.mul_le_mul (by omega) (by omega)
      omega
    subst hf1 hm3
    revert hdvdS
    decide
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
    have hcardΩ : Open.ordA (m - 1) (2 ^ f) = (Fintype.card Ω)! / 2 := by
      rw [← hcardDZ, Nat.card_congr eA.toEquiv, nat_card_alternatingGroup,
        Nat.card_eq_fintype_card]
    rcases ordA_two_pow_eq_factorial_div_two (by omega) hf hcardΩ with ⟨h2, hf2⟩ | ⟨h3, hf1⟩
    · exfalso
      have hm3 : m = 3 := by omega
      subst hm3 hf2
      exact CFSG.ComponentClassification.CatLeaf.not_isL34Type_of_isAltType
        ⟨Ω, inferInstance, inferInstance, hΩ, ⟨eA⟩⟩ hDm
    · exact ⟨by omega, hf1⟩

end CFSG.SeitzReduction.LinearPilot
