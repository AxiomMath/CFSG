module

public import CFSG.LieType.OutStructureSevenOneThreeFive

public section

namespace CFSG.LieType.OutStructure

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag

theorem card_center_dvd_genericOrders_fst (hGA : CFSG.Open.GriessAllModelsStatement) {L : Type}
    [Group L] [Finite L] (hq : CFSG.Open.IsQuasisimple L) {t : StatedLieTag} {n r f : ℕ}
    (hcl : StatedClassicalModel (L ⧸ Subgroup.center L) t n r f) (ht : t = .PSL ∨ t = .PSU)
    (hn : 7 ≤ n) : Nat.card (Subgroup.center L) ∣ (genericOrders t n r f).1 := by
  have hdvd := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.center_dvd_table hGA
    ⟨⟨hq.1⟩, hq.2,
      CFSG.HardMathSupport.Timmesfeld.ComponentBalance.exists_noncomm_quotient_center_of_quasisimple
        hq⟩
    (MulEquiv.refl _) (CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.lieModel_of_classical hcl)
  have hb : (genericOrders t n r f).2 = 1 := by rcases ht with rfl | rfl <;> rfl
  have he : exceptionalOrders t n r f = (1, 1) := by
    rcases ht with rfl | rfl <;>
    · unfold exceptionalOrders
      split <;> first | rfl | (exfalso; omega)
  rw [hb, he] at hdvd
  simpa using hdvd

theorem pRank_succ_le_of_centralizes_maximal {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) {L : Subgroup X} {x : X} (hxord : orderOf x = p) (hxL : x ∉ L)
    {E : Subgroup X} (hEL : E ≤ L) (hE : CFSG.Open.IsElemAbelian p E)
    (hEmax : Nat.card E = p ^ CFSG.Open.pRank p L) (hc : ∀ a ∈ E, a * x = x * a) :
    CFSG.Open.pRank p L + 1 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) :=
  (pRank_lt_sup_zpowers_of_centralizes_maximal hp hxord hxL hEL hE hEmax hc).trans_le
    (CFSG.SectionRank.pRank_mono hp.one_lt le_top)

theorem isPClosedMod_of_outFiveExceptional_of_three_le_pRank
    (hGA : CFSG.Open.GriessAllModelsStatement) {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) {L : Subgroup X} (hL : CFSG.IsComponent L) (hLn : L.Normal)
    (hX3 : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 3) (hL3 : 3 ≤ CFSG.Open.pRank p L)
    (hex : OutFiveExceptional (↥L ⧸ Subgroup.center ↥L) p) :
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsPClosedMod p
      (L ⊔ Subgroup.centralizer (L : Set X)) := by
  by_contra hnot
  have := hLn
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hq : CFSG.Open.IsQuasisimple ↥L := ⟨Group.isPerfect_def.mp hL.1.1, hL.1.2.1⟩
  have hLtop : CFSG.Open.pRank p (⊤ : Subgroup ↥L) = CFSG.Open.pRank p L :=
    (CFSG.SectionRank.pRank_eq_pRank_top_subgroup L).symm
  have hZ : ¬ p ∣ Nat.card (Subgroup.center ↥L) := by
    intro hdvd
    rcases hex with ⟨N, r, f, hcl, hN, -⟩ | ⟨N, r, f, hcl, hN, -⟩
    · have ha : p ∣ (genericOrders .PSL N r f).1 :=
        hdvd.trans (card_center_dvd_genericOrders_fst hGA hq hcl (Or.inl rfl) (by omega))
      have h3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (↥L ⧸ Subgroup.center ↥L)) := by
        by_contra h3
        exact (not_dvd_of_pRank_le_three_of_statedPSL hcl (by omega) hp hp2 (by omega)).2
          (ha.trans (Nat.gcd_dvd_right _ _))
      obtain ⟨-, h2⟩ := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.lieCoverRankHighLin_aux hGA
        ⟨hq.1⟩ hp hp2 hdvd h3 (Or.inl ⟨by decide, hcl⟩) (Or.inl rfl) ha
      have := (CFSG.SectionRank.pRank_mono hp.one_lt (le_top : L ≤ ⊤)).trans hX3
      omega
    · have ha : p ∣ (genericOrders .PSU N r f).1 :=
        hdvd.trans (card_center_dvd_genericOrders_fst hGA hq hcl (Or.inr rfl) (by omega))
      have h3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (↥L ⧸ Subgroup.center ↥L)) := by
        by_contra h3
        exact (not_dvd_of_pRank_le_three_of_statedPSU hcl (by omega) hp hp2 (by omega)).2
          (ha.trans (Nat.gcd_dvd_right _ _))
      obtain ⟨-, h2⟩ := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.lieCoverRankHighLin_aux hGA
        ⟨hq.1⟩ hp hp2 hdvd h3 (Or.inl ⟨by decide, hcl⟩) (Or.inr rfl) ha
      have := (CFSG.SectionRank.pRank_mono hp.one_lt (le_top : L ≤ ⊤)).trans hX3
      omega
  have hrkS : CFSG.Open.pRank p (⊤ : Subgroup (↥L ⧸ Subgroup.center ↥L)) ≤ 3 := by
    rw [CFSG.HardMathSupport.Timmesfeld.ComponentBalance.pRank_quotient_center_eq_of_not_dvd
      hp hZ, hLtop]
    exact (CFSG.SectionRank.pRank_mono hp.one_lt le_top).trans hX3
  have key : ∀ x : X, orderOf x = p → x ∉ L → ∀ E : Subgroup X, E ≤ L →
      CFSG.Open.IsElemAbelian p E → Nat.card E = p ^ CFSG.Open.pRank p L →
      (∀ a ∈ E, a * x = x * a) → False := fun x hx hxL E hEL hE hEmax hEc => by
    have := pRank_succ_le_of_centralizes_maximal hp hx hxL hEL hE hEmax hEc
    omega
  have hcen : ∀ c : X, c ∈ Subgroup.centralizer (L : Set X) → orderOf c = p → False := by
    intro c hcC hcord
    have hcL : c ∉ L := by
      intro hcL
      have hmem : (⟨c, hcL⟩ : ↥L) ∈ Subgroup.center ↥L :=
        Subgroup.mem_center_iff.mpr fun g => Subtype.ext
          (Subgroup.mem_centralizer_iff.mp hcC g.1 g.2)
      apply hZ
      have hord : orderOf (⟨⟨c, hcL⟩, hmem⟩ : ↥(Subgroup.center ↥L)) = p := by
        rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hcord]
      rw [← hord]
      exact orderOf_dvd_natCard _
    obtain ⟨E, hEL, hE, hEcard⟩ :=
      CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := p) (H := L) le_rfl
    exact key c hcord hcL E hEL hE hEcard fun a ha =>
      Subgroup.mem_centralizer_iff.mp hcC a (hEL ha)
  rcases hex with ⟨N, r, f, hcl, hN, -⟩ | ⟨N, r, f, hcl, hN, -⟩
  · obtain ⟨hpq, hq1⟩ := not_dvd_of_pRank_le_three_of_statedPSL hcl (by omega) hp hp2 hrkS
    obtain ⟨-, K, _, _, hKcard, ⟨eS⟩⟩ := hcl
    let e : (↥L ⧸ Subgroup.center ↥L) ≃* projectiveSL N K :=
      eS.trans ((projectiveSpecialLinearGroupEquivStatedProj N K).symm.trans
        (LinearCover.projectiveSpecialLinearEquivProjectiveSL N K))
    have hdiv : ¬ p ∣ Nat.gcd N (Nat.card K - 1) := fun h =>
      hq1 (by rw [← hKcard]; exact h.trans (Nat.gcd_dvd_right _ _))
    rcases hInput_linear_of_exists_of_cross hL e (by omega) hp hp2 hZ (by rwa [hKcard]) hdiv
        (fun hnot hc => exists_orderOf_eq_not_mem_of_projectiveSL hL e (by omega) hp hp2 hdiv
          hnot hc) hnot with
      ⟨c, hcC, hcord⟩ | ⟨x, hxord, hxU, E, hEL, hE, hEmax, hEc⟩
    · exact hcen c hcC hcord
    · exact key x hxord (fun hx => hxU (Subgroup.mem_sup_left hx)) E hEL hE hEmax hEc
  · obtain ⟨hpq, hq1⟩ := not_dvd_of_pRank_le_three_of_statedPSU hcl (by omega) hp hp2 hrkS
    obtain ⟨⟨hr, hf, -, h32⟩, K, _, _, hKcard, ⟨eS⟩⟩ := hcl
    let hU : UnitaryFieldData r f K := ⟨hr, hf, by rw [hKcard, ← pow_mul, mul_comm]⟩
    have hq' : ¬(N = 3 ∧ r ^ f = 2) := by
      rintro ⟨h1, h2⟩
      exact h32 (by rw [h1, h2])
    let ePU : primeFormP hU ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) ≃*
        unitaryPSU hU N :=
      Classical.choice (nonempty_primeFormP_mulEquiv hU isPrimeFormGram_one)
    let e : (↥L ⧸ Subgroup.center ↥L) ≃*
        primeFormP hU ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) :=
      eS.trans (ePU.trans (unitaryPSUEquiv hU (by omega))).symm
    have hpr : p ≠ r := fun h => hpq (h ▸ dvd_pow_self p (by omega))
    have hdiv : ¬ p ∣ Nat.gcd N (r ^ f + 1) := fun h => hq1 (h.trans (Nat.gcd_dvd_right _ _))
    rcases hInput_unitary_of_exists_of_cross hL hU e (by omega) hq' hp hp2 hpr hZ hdiv
        (fun hnot hc => exists_orderOf_eq_not_mem_of_primeFormP hL hU e (by omega) hq' hp hdiv
          hnot hc) hnot with
      ⟨c, hcC, hcord⟩ | ⟨x, hxord, hxU, E, hEL, hE, hEmax, hEc⟩
    · exact hcen c hcC hcord
    · exact key x hxord (fun hx => hxU (Subgroup.mem_sup_left hx)) E hEL hE hEmax hEc

end CFSG.LieType.OutStructure

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.LocalAnalysis.RankThreeUC.S15 Subgroup

theorem nineTenPClosed_of_exceptional_two
    (hex : ∀ (G : Type) [Group G] [Finite G] (M Q H E : Subgroup G) (p : ℕ),
      NineSettingGen G M p Q H E 2 → H ∈ H2Fam M Q → p ∉ sigmaM G M → 3 < p →
      ∀ C : Subgroup (StarGroup p H), CFSG.IsComponent C → 2 ≤ CFSG.Open.pRank 3 C →
        CFSG.LieType.OutStructure.OutFiveExceptional (↥C ⧸ Subgroup.center ↥C) p →
        CFSG.Open.pRank p C ≤ 2 →
        IsPClosedMod p ((C ⊔ centralizer (C : Set (StarGroup p H))).subgroupOf
          (normalizer (C : Set (StarGroup p H))))) :
    ∀ (G : Type) [Group G] [Finite G] (M Q H E : Subgroup G) (p : ℕ),
      NineSettingGen G M p Q H E 2 → H ∈ H2Fam M Q → p ∉ sigmaM G M → 3 < p →
      ∀ C : Subgroup (StarGroup p H), CFSG.IsComponent C → 2 ≤ CFSG.Open.pRank 3 C →
        IsPClosedMod p ((C ⊔ centralizer (C : Set (StarGroup p H))).subgroupOf
          (normalizer (C : Set (StarGroup p H)))) := by
  refine nineTenPClosed_of_exceptional ?_
  intro G _ _ M Q H E p h hH2 hp hp3 C hC h3C hexC
  by_cases hC2 : CFSG.Open.pRank p C ≤ 2
  · exact hex G M Q H E p h hH2 hp hp3 C hC h3C hexC hC2
  have hp5 : 5 ≤ p := by
    have hp4 : p ≠ 4 := by
      rintro rfl
      exact (by decide : ¬ Nat.Prime 4) h.prime
    omega
  let N : Subgroup (StarGroup p H) := normalizer (C : Set (StarGroup p H))
  have hcomp : CFSG.IsComponent (C.subgroupOf N) :=
    CFSG.LocalCores.component_overgroup hC Subgroup.le_normalizer
  have hnorm : (C.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  let e : ↥(C.subgroupOf N) ≃* ↥C := Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer
  have hexN : CFSG.LieType.OutStructure.OutFiveExceptional
      (↥(C.subgroupOf N) ⧸ Subgroup.center ↥(C.subgroupOf N)) p :=
    hexC.of_mulEquiv (QuotientGroup.congr (center ↥(C.subgroupOf N)) (center ↥C) e
      (Subgroup.map_center_eq e))
  have hX3 : CFSG.Open.pRank p (⊤ : Subgroup ↥N) ≤ 3 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup N]
    exact (CFSG.SectionRank.pRank_mono h.prime.one_lt le_top).trans
      (h.pRank_star_le_three hH2 hp)
  have hL3 : 3 ≤ CFSG.Open.pRank p (C.subgroupOf N) := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (C.subgroupOf N),
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv h.prime.one_lt e,
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup C]
    omega
  have hres := CFSG.LieType.OutStructure.isPClosedMod_of_outFiveExceptional_of_three_le_pRank
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement h.prime hp5 hcomp hnorm
    hX3 hL3 hexN
  have heq : (C.subgroupOf N) ⊔ centralizer (C.subgroupOf N : Set ↥N) =
      (C ⊔ centralizer (C : Set (StarGroup p H))).subgroupOf N := by
    rw [CFSG.centralizer_subgroupOf_eq C N Subgroup.le_normalizer]
    rw [Subgroup.subgroupOf_sup Subgroup.le_normalizer
      (Subgroup.centralizer_le_normalizer (C : Set (StarGroup p H)))]
  rw [heq] at hres
  exact hres

end CFSG.LocalAnalysis.RankThreeUC.AGL81C

namespace CFSG.LieType.OutStructure

theorem nineTenInputs_of_exceptional_two
    (hex : ∀ (G : Type) [Group G] [Finite G] (M Q H E : Subgroup G) (p : ℕ),
      CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSettingGen G M p Q H E 2 →
      H ∈ CFSG.LocalAnalysis.RankThreeUC.AGL81C.H2Fam M Q →
      p ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M → 3 < p →
      ∀ C : Subgroup (CFSG.LocalAnalysis.RankThreeUC.AGL81C.StarGroup p H), CFSG.IsComponent C →
        2 ≤ CFSG.Open.pRank 3 C → OutFiveExceptional (↥C ⧸ Subgroup.center ↥C) p →
        CFSG.Open.pRank p C ≤ 2 →
        CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsPClosedMod p
          ((C ⊔ Subgroup.centralizer
              (C : Set (CFSG.LocalAnalysis.RankThreeUC.AGL81C.StarGroup p H))).subgroupOf
            (Subgroup.normalizer
              (C : Set (CFSG.LocalAnalysis.RankThreeUC.AGL81C.StarGroup p H))))) :
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineTenInputs :=
  ⟨sevenOneUsed_holds,
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.nineTenPClosed_of_exceptional_two hex⟩

end CFSG.LieType.OutStructure
