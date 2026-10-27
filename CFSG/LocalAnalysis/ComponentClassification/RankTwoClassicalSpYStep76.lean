module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalJ2Cert
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalStep79
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSpYDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Open (IsElemAbelian standardComponentIsStandard standardComponentOddCore ordTwistedA)
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoExceptional
open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b

variable {G : Type} [Group G] [Finite G]

theorem Levi75Y.exists_quotient {A : Subgroup G} {D : ClassicalModel A} {T Y W L : Subgroup G}
    (hH : RankTwoHyp G A) (hA : AS76b.Hyp31 A) (hl : Levi75Y D T Y W L) :
    ∃ (H : Type) (_ : Group H) (_ : Finite H) (B : Subgroup H), Nat.card H < Nat.card G ∧
      RankTwoHyp H B ∧ standardComponentOddCore H = ⊥ ∧
        Nonempty (rankTwoQuot B ≃* rankTwoQuot L) := by
  have hLA : L ≤ A := hl.L_le.trans inf_le_left
  have hLW : L ≤ centralizer (Y : Set G) := hl.L_le.trans inf_le_right
  have hH' : RankTwoHyp ↥(centralizer (Y : Set G)) (L.subgroupOf (centralizer (Y : Set G))) :=
    ⟨LocalAnalysis.ComponentInitial.kProper_subgroup
        (fun e h => SectionRank.catalog_of_mulEquiv e h) hH.kProper _, hl.standard,
      hl.not_normal, RankTwoL3Even.two_le_pRank_centralizer_subgroupOf hl.Y_le hLA hH.rank⟩
  have hWlt := card_centralizer_lt hH hA.oddCore hl.Y_ne_bot
  obtain ⟨B, hB', hO', ⟨f⟩⟩ := RankTwoSporadic.exists_rankTwoHyp_quotient hH'
  refine ⟨_, inferInstance, inferInstance, B, ?_, hB', hO',
    ⟨f.symm.trans (quotCenterCongr (subgroupOfEquivOfLe hLW))⟩⟩
  exact lt_of_le_of_lt (Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)) hWlt

omit [Finite G] in
theorem Levi75Y.a5 {A : Subgroup G} {D : ClassicalModel A}
    {T Y W L : Subgroup G} (hl : Levi75Y D T Y W L) (hD : D.IsLTwoFour) :
    Nonempty (rankTwoQuot L ≃* alternatingGroup (Fin 5)) := by
  have hlevi := hl.levi
  cases D with
  | linear n m hn hm hnm K hK e =>
    obtain ⟨rfl, rfl⟩ := hD
    exact nonempty_equiv_a5_of_psl hlevi
  | unitary n m hn hm K hK e =>
    obtain ⟨rfl, rfl⟩ := hD
    rcases hlevi with ⟨h5, -⟩ | ⟨-, hT⟩
    · omega
    · exact nonempty_equiv_a5_of_psl hT
  | symplectic n m hn hm hnm K hK e =>
    obtain ⟨rfl, rfl⟩ := hD
    rcases hlevi with ⟨h3, -⟩ | ⟨-, hT⟩
    · omega
    · exact nonempty_equiv_a5_of_psl hT
  | orthPlus n m hn hm K hK e =>
    obtain ⟨rfl, rfl⟩ := hD
    rcases hlevi with ⟨h6, -⟩ | ⟨h5, -⟩ | ⟨-, hT⟩
    · omega
    · omega
    · exact nonempty_equiv_a5_of_psl hT
  | orthMinus n m hn hm K hK b c hbc e =>
    obtain ⟨rfl, rfl⟩ := hD
    rcases hlevi with ⟨h6, -⟩ | ⟨h5, -⟩ | ⟨-, hT⟩
    · omega
    · omega
    · exact nonempty_equiv_a5_of_psl hT

theorem Levi75Y.cfg76 {A : Subgroup G} {D : ClassicalModel A}
    {R T Y W L : Subgroup G} {g : G} (hH : RankTwoHyp G A) (hA : AS76b.Hyp31 A)
    (hch : Choice74 D R T g) (hl : Levi75Y D T Y W L) (hD : D.IsLTwoFour) : Cfg76 A R Y L :=
  ⟨hA, hH.kProper, hch.sylowR, hch.not_le, hl.Y_le, hl.L_le, hl.a5 hD, hl.oddCenter,
    hl.standard, hl.not_normal, hl.noInv, hl.outerFree hD⟩

theorem step76L3Y_of (hSuz : SuzL34DiagInput) (h32 : AS76b.Lemma32) (h4 : RankTwoL3EvenStandard)
    {A : Subgroup G} {D : ClassicalModel A} {R T Y W L : Subgroup G} {g : G}
    (hH : RankTwoHyp G A) (hA : AS76b.Hyp31 A) (hch : Choice74 D R T g)
    (hl : Levi75Y D T Y W L) (hD : D.IsLinearFiveFour) : False := by
  have hy := hl.diag hD
  have hZ := hl.oddCenter
  have hlevi := hl.levi
  have hstd := hl.standard
  have hnn := hl.not_normal
  obtain rfl := hl.L_eq
  have hT : StatedClassicalModel (rankTwoQuot (AS76b.layerCentralizer A Y)) .PSL 3 2 2 := by
    cases D with
    | linear n m hn hm hnm K hK e =>
      obtain ⟨rfl, rfl⟩ := hD
      exact hlevi
    | unitary => exact hD.elim
    | symplectic => exact hD.elim
    | orthPlus => exact hD.elim
    | orthMinus => exact hD.elim
  exact false_of_triality_four hSuz h32 hA hH hch.sylowR hl.Y_le hstd hnn hZ hT (h4 _ _) hy

theorem step76L2Y_of
    (h4 : Asc75Theorem4)
    (h32 : Lemma32) (h34 : Asc08Lemma34) (h5 : Asc08Lemma310) (hJ : J2Std.J2StdFacts)
    (hSp44 : Sp44Endgame) {A : Subgroup G} {D : ClassicalModel A} {R T Y W L : Subgroup G}
    {g : G} (hH : RankTwoHyp G A) (hA : AS76b.Hyp31 A) (hch : Choice74 D R T g)
    (hl : Levi75Y D T Y W L) (hD : D.IsLTwoFour) : False := by
  have hc := hl.cfg76 hH hA hch hD
  by_cases hfam : D.family = .symplectic
  · obtain ⟨y, s, y₃, rfl, hsp⟩ := hl.spFour hD hfam
    exact hSp44 G A R W L y s y₃ hc hsp
  obtain ⟨D', s, x, hY, hs, hWs, hLs, hDs, hxL, hx5, hlay, hnoZ⟩ := hl.sym hD hfam
  have hc' : Cfg76 A R (rightConjugate Y s) W := hLs ▸ hc.conj hs
  have hYs : rightConjugate Y s = D' ⊔ L := by
    rw [hY]
    change (D' ⊔ W).map (MulAut.conj s⁻¹).toMonoidHom = D' ⊔ L
    rw [Subgroup.map_sup]
    change rightConjugate D' s ⊔ rightConjugate W s = D' ⊔ L
    rw [hDs, hWs]
  set Z := D' ⊔ zpowers x with hZdef
  have hZYs : Z ≤ rightConjugate Y s := by
    rw [hYs]
    exact sup_le_sup_left (zpowers_le.mpr hxL) D'
  have hZA : Z ≤ A := hZYs.trans hc'.Y_le
  have hLYs : L ≤ rightConjugate Y s := by
    rw [hYs]
    exact le_sup_right
  obtain ⟨c, hcYx, r, hr, hcr⟩ := hc.exists_conj h5 h32 hJ hxL hx5
  have hcZ : c ∈ centralizer (Z : Set G) := by
    obtain ⟨hcY, hcx⟩ := mem_inf.mp hcYx
    refine mem_centralizer_sup ?_ ?_
    · exact centralizer_le (show D' ≤ Y by rw [hY]; exact le_sup_left) hcY
    · rw [mem_centralizer_iff]
      intro y hy
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
      exact (Commute.zpow_left (mem_centralizer_singleton_iff.mp hcx).symm k).eq
  have hxW : s⁻¹ * x * s ∈ W := by
    rw [← hLs, mem_rightConjugate_iff]
    simpa [mul_assoc] using hxL
  have hxW5 : orderOf (s⁻¹ * x * s) = 5 := by
    have := orderOf_injective (MulAut.conj s⁻¹).toMonoidHom (MulAut.conj s⁻¹).injective x
    simpa [MulAut.conj_apply, hx5] using this
  have hRE := hc'.R_le_E h5 h32 hxW hxW5
  have hr2 : r ^ 2 = 1 := (h32 G A hA R hch.sylowR).2 r hr
  have hmem := hc'.conj_mem_E h4 h32 h34 h5 hZYs hZA hlay hnoZ c hcZ r (hRE hr) hr2
  exact hcr (((Cfg76.E76_le_centralizer).trans (centralizer_le hLYs)) hmem)

theorem step76Y_of_inputs
    (h2 : RankTwoBenderStandard) (h4 : RankTwoL3EvenStandard) (hSuz : SuzL34DiagInput)
    (h75 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34) (h5 : Asc08Lemma310)
    (hJ : J2Std.J2StdFacts) (hSp44 : Sp44Endgame) : Step76Y := by
  intro G _ _ A D R T Y W L g hH hA hTy hch hl ih
  obtain ⟨H, _, _, B, hlt, hB, hO, ⟨eB⟩⟩ := hl.exists_quotient hH hA
  have hq := hch.four_le
  have hlevi := hl.levi
  have hm2 : ∀ m : ℕ, 4 ≤ 2 ^ m → 2 ≤ m := by
    intro m hm
    by_contra h
    interval_cases m <;> norm_num at hm
  have hclass : ∀ {t : StatedLieTag} {n m : ℕ}, StatedClassicalModel (rankTwoQuot L) t n 2 m →
      ((t = .PSL ∧ 4 ≤ n) ∨ (t = .PSU ∧ 4 ≤ n) ∨ (t = .PSp ∧ 2 ≤ n) ∨
        ((t = .POmegaPlus ∨ t = .POmegaMinus) ∧ 4 ≤ n)) →
      EvenSmallLie.CatalogOrders.lieMin t ≤ n →
      7 ≤ m * EvenSmallLie.CatalogOrders.lieExp t n → False := by
    intro t n m hT ht hn he
    have hT' := SectionRank.statedClassicalModel_of_mulEquiv eB hT
    exact ih H B hlt hB hO
      (classicalEvenType_of_model hT' ht (two_pow_seven_dvd_of_model hn he hT'))
  have hbender : ∀ {m : ℕ}, 3 ≤ m → StatedClassicalModel (rankTwoQuot L) .PSL 2 2 m → False :=
    fun hm hT => false_of_bender h2 hB hO hm (SectionRank.statedClassicalModel_of_mulEquiv eB hT)
  have hL2' : D.IsLTwoFour → False :=
    step76L2Y_of h75 h32 h34 h5 hJ hSp44 hH hA hch hl
  have hL3' : D.IsLinearFiveFour → False := step76L3Y_of hSuz h32 h4 hH hA hch hl
  cases D with
  | linear n m hn hm hnm K hK e =>
    have hm' := hm2 m hq
    simp only [ClassicalModel.LeviType] at hlevi
    rcases Nat.lt_or_ge n 6 with h6 | h6
    · rcases Nat.lt_or_ge n 5 with h5 | h5
      ·
        obtain rfl : n = 4 := by omega
        rcases Nat.lt_or_ge m 3 with h3 | h3
        · obtain rfl : m = 2 := by omega
          exact hL2' ⟨rfl, rfl⟩
        · exact hbender h3 hlevi
      ·
        obtain rfl : n = 5 := by omega
        have hT' := SectionRank.statedClassicalModel_of_mulEquiv eB hlevi
        have hm2' : m = 2 := (h4 H B hB m hm' hT').1 hO
        subst hm2'
        exact hL3' ⟨rfl, rfl⟩
    · exact hclass hlevi (Or.inl ⟨rfl, by omega⟩)
        (by simp [EvenSmallLie.CatalogOrders.lieMin]; omega)
        (by
          simp only [EvenSmallLie.CatalogOrders.lieExp]
          have hP : 3 * 4 ≤ (n - 2 - 1) * (n - 2) := Nat.mul_le_mul (by omega) (by omega)
          have hP2 : 6 ≤ (n - 2 - 1) * (n - 2) / 2 := by omega
          calc 7 ≤ 2 * 6 := by norm_num
            _ ≤ m * ((n - 2 - 1) * (n - 2) / 2) := Nat.mul_le_mul hm' hP2)
  | unitary n m hn hm K hK e =>
    have hm' := hm2 m hq
    simp only [ClassicalModel.LeviType] at hlevi
    rcases hlevi with ⟨h5, hT⟩ | ⟨rfl, hT⟩
    · rcases Nat.lt_or_ge n 6 with h6 | h6
      · obtain rfl : n = 5 := by omega
        exact false_of_psu_three h2 hB hO hm' (SectionRank.statedClassicalModel_of_mulEquiv eB hT)
      · exact hclass hT (Or.inr (Or.inl ⟨rfl, by omega⟩))
          (by simp [EvenSmallLie.CatalogOrders.lieMin]; omega)
          (by
            simp only [EvenSmallLie.CatalogOrders.lieExp]
            have hP : 3 * 4 ≤ (n - 2 - 1) * (n - 2) := Nat.mul_le_mul (by omega) (by omega)
            have hP2 : 6 ≤ (n - 2 - 1) * (n - 2) / 2 := by omega
            calc 7 ≤ 2 * 6 := by norm_num
              _ ≤ m * ((n - 2 - 1) * (n - 2) / 2) := Nat.mul_le_mul hm' hP2)
    · rcases Nat.lt_or_ge m 3 with h3 | h3
      · obtain rfl : m = 2 := by omega
        exact hL2' ⟨rfl, rfl⟩
      · exact hbender h3 hT
  | symplectic n m hn hm hnm K hK e =>
    have hm' := hm2 m hq
    simp only [ClassicalModel.LeviType] at hlevi
    rcases hlevi with ⟨h3, hT⟩ | ⟨rfl, hT⟩
    · exact hclass hT (Or.inr (Or.inr (Or.inl ⟨rfl, by omega⟩)))
        (by simp [EvenSmallLie.CatalogOrders.lieMin]; omega)
        (by
          simp only [EvenSmallLie.CatalogOrders.lieExp]
          have hP : 2 * 2 ≤ (n - 1) * (n - 1) := Nat.mul_le_mul (by omega) (by omega)
          calc 7 ≤ 2 * (2 * 2) := by norm_num
            _ ≤ m * ((n - 1) * (n - 1)) := Nat.mul_le_mul hm' hP)
    · rcases Nat.lt_or_ge m 3 with h3 | h3
      · obtain rfl : m = 2 := by omega
        exact hL2' ⟨rfl, rfl⟩
      · exact hbender h3 hT
  | orthPlus n m hn hm K hK e =>
    have hm' := hm2 m hq
    simp only [ClassicalModel.LeviType] at hlevi
    rcases hlevi with ⟨h6, hT⟩ | ⟨rfl, hT⟩ | ⟨rfl, hT⟩
    · exact hclass hT (Or.inr (Or.inr (Or.inr ⟨Or.inl rfl, by omega⟩)))
        (by simp [EvenSmallLie.CatalogOrders.lieMin]; omega)
        (by
          simp only [EvenSmallLie.CatalogOrders.lieExp]
          have hP : 4 * 3 ≤ (n - 2) * (n - 2 - 1) := Nat.mul_le_mul (by omega) (by omega)
          calc 7 ≤ 2 * (4 * 3) := by norm_num
            _ ≤ m * ((n - 2) * (n - 2 - 1)) := Nat.mul_le_mul hm' hP)
    · exact hclass hT (Or.inl ⟨rfl, le_rfl⟩) (by simp [EvenSmallLie.CatalogOrders.lieMin])
        (by simp only [EvenSmallLie.CatalogOrders.lieExp]; omega)
    · rcases Nat.lt_or_ge m 3 with h3 | h3
      · obtain rfl : m = 2 := by omega
        exact hL2' ⟨rfl, rfl⟩
      · exact hbender h3 hT
  | orthMinus n m hn hm K hK b c hbc e =>
    have hm' := hm2 m hq
    simp only [ClassicalModel.LeviType] at hlevi
    rcases hlevi with ⟨h6, hT⟩ | ⟨rfl, hT⟩ | ⟨rfl, hT⟩
    · exact hclass hT (Or.inr (Or.inr (Or.inr ⟨Or.inr rfl, by omega⟩)))
        (by simp [EvenSmallLie.CatalogOrders.lieMin]; omega)
        (by
          simp only [EvenSmallLie.CatalogOrders.lieExp]
          have hP : 4 * 3 ≤ (n - 2) * (n - 2 - 1) := Nat.mul_le_mul (by omega) (by omega)
          calc 7 ≤ 2 * (4 * 3) := by norm_num
            _ ≤ m * ((n - 2) * (n - 2 - 1)) := Nat.mul_le_mul hm' hP)
    · exact hclass hT (Or.inr (Or.inl ⟨rfl, le_rfl⟩)) (by simp [EvenSmallLie.CatalogOrders.lieMin])
        (by simp only [EvenSmallLie.CatalogOrders.lieExp]; omega)
    · rcases Nat.lt_or_ge m 3 with h3 | h3
      · obtain rfl : m = 2 := by omega
        exact hL2' ⟨rfl, rfl⟩
      · exact hbender h3 hT

theorem step76Y_of_certs
    (h2 : RankTwoBenderStandard) (h4 : RankTwoL3EvenStandard)
    (hSuz : SuzL34DiagInput) (h75 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34)
    (h5 : Asc08Lemma310) (hSp44 : Sp44Endgame) : Step76Y :=
  step76Y_of_inputs h2 h4 hSuz h75 h32 h34 h5 (J2Std.j2StdFacts_of_check J2Std.j2_stdCheck) hSp44

theorem rankTwoClassicalEvenStandard_of_stepsY (hII : ClassicalHypII) (h74 : Step74)
    (h75 : Step75Y) (h76 : Step76Y) : RankTwoClassicalEvenStandard := by
  suffices h : ∀ (N : ℕ) (G : Type) [Group G] [Finite G] (A : Subgroup G), Nat.card G = N →
      RankTwoHyp G A → standardComponentOddCore G = ⊥ →
        ¬ RankTwoClassicalEvenType (rankTwoQuot A) by
    intro G _ _ A hH hO
    exact h _ G A rfl hH hO
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro G _ _ A hN hH hO hT
    obtain ⟨D⟩ := nonempty_classicalModel hT
    have hA := hyp31_of hII hH hO hT
    obtain ⟨R, T, g, hc⟩ := h74 G A D hA hT
    obtain ⟨Y, W, L, hl⟩ := h75 G A D R T g hA hT hc
    exact h76 G A D R T Y W L g hH hA hT hc hl fun G' _ _ A' hlt hH' hO' =>
      ih _ (hN ▸ hlt) G' A' rfl hH' hO'

end CFSG.ComponentClassification.RankTwoClassical
