module

public import CFSG.LocalAnalysis.RankThreeTheoremC.FullCoreCases
public import CFSG.LocalAnalysis.RankThreeTheoremC.PConstrainedOvergroups
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.InvariantTwoWithin
public import CFSG.LocalAnalysis.ABGTheoremB.Basic
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.RelativePairGeometry
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.ConstrainedGlobalization
import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionCentralizer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def TransitivityReduction (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M D : Subgroup G), ExtremalObstruction p P M D →
    ¬ (P : Subgroup G) ≤ normalizer (D : Set G) →
      ∀ z ∈ D, z ≠ 1 → z ∈ centralizer (P : Set G) → z ^ p = 1 →
        normalizer ((zpowers z : Subgroup G) : Set G) ≤ M

@[expose] def GL83InvariantTwoSylow (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M D : Subgroup G), ExtremalObstruction p P M D →
    ¬ (P : Subgroup G) ≤ normalizer (D : Set G) → IsMulCommutative D →
      ∀ z ∈ D, z ≠ 1 → z ∈ centralizer (P : Set G) → z ^ p = 1 →
        ∀ T : Subgroup G, invariantTwoMaximalWithin D M T →
          CFSG.ABGLocalTools.IsSylowOf 2 T (CFSG.ABGTheoremB.pPrimeCoreIn p M ⊔
            CFSG.ABGTheoremB.pPrimeCoreIn p (normalizer ((zpowers z : Subgroup G) : Set G)))

@[expose] def GL83InvariantTwoTransitivity (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M D : Subgroup G), ExtremalObstruction p P M D →
    ¬ (P : Subgroup G) ≤ normalizer (D : Set G) → IsMulCommutative D →
      ∀ T T' : Subgroup G, rankTwoMaximalInvariantTwoSubgroup D T →
        rankTwoMaximalInvariantTwoSubgroup D T' →
          ∃ c : G, c ∈ centralizer (D : Set G) ∧ T'.map (MulAut.conj c).toMonoidHom = T

theorem normalizer_le_of_isSylowOf_two_of_le (hD1 : TheoremD1 G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M)
    {R X T : Subgroup G} (hRM : R ≤ M) (hRp : IsPGroup p R) (hR3 : 3 ≤ CFSG.Open.pRank p R)
    (hXM : X ≤ M) (hRX : R ≤ normalizer (X : Set G)) (hX : Nat.Coprime p (Nat.card X))
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T X) (hTne : T ≠ ⊥) : normalizer (T : Set G) ≤ M := by
  classical
  have hprime := sigmaA_prime p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₁, hS₁⟩ := hT
  let φ := ambientSubgroupActionHom R X hRX
  let _ : MulDistribMulAction R X := MulDistribMulAction.compHom X φ
  obtain ⟨S, hS⟩ := coprime_pGroup_has_invariant_sylow p hprime hRp hX 2 Nat.prime_two
  have hSinv : ∀ g : R, (S : Subgroup X).map (φ g).toMonoidHom = S := by
    intro g
    have h := congrArg (fun T : Sylow 2 X => (T : Subgroup X)) (hS g)
    rw [Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def] at h
    exact h
  have hRT₀ : R ≤ normalizer (((S : Subgroup X).map X.subtype : Subgroup G) : Set G) :=
    (ambient_subgroup_action_image_invariant_iff R X hRX S).1 hSinv
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq X S₁ S
  have hT₀ : (S : Subgroup X).map X.subtype = T.map (MulAut.conj (x : G)).toMonoidHom := by
    have hcomm : X.subtype.comp (MulAut.conj x).toMonoidHom =
        (MulAut.conj (x : G)).toMonoidHom.comp X.subtype := by
      ext y
      rfl
    rw [← hx, sylow_conjugate_eq_map, ← hS₁, Subgroup.map_map, Subgroup.map_map, hcomm]
  have hT₀ne : (S : Subgroup X).map X.subtype ≠ ⊥ := by
    rw [hT₀]
    intro h
    exact hTne ((map_eq_bot_iff_of_injective (f := (MulAut.conj (x : G)).toMonoidHom) T
      (MulAut.conj (x : G)).injective).mp h)
  have hlocal : IsTwoLocal (normalizer (((S : Subgroup X).map X.subtype : Subgroup G) : Set G)) :=
    ⟨_, hT₀ne, S.isPGroup'.map X.subtype, rfl⟩
  have hNT₀ := le_of_three_le_pRank_inf hD1 hp hM hlocal
    (hR3.trans (pRank_mono p hprime.one_lt (le_inf hRT₀ hRM)))
  have hmap : (normalizer (T : Set G)).map (MulAut.conj (x : G)).toMonoidHom ≤ M := by
    rw [Subgroup.map_equiv_normalizer_eq, ← hT₀]
    exact hNT₀
  exact (conjugate_subgroup_le_iff_of_conjugator_mem _ M (x : G) (hXM x.2)).1 hmap

theorem normalizer_le_of_isSylowOf_two (hS : Setting G) (hD1 : TheoremD1 G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M)
    {X T : Subgroup G} (hXM : X ≤ M) (hPX : (P : Subgroup G) ≤ normalizer (X : Set G))
    (hX : Nat.Coprime p (Nat.card X)) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T X)
    (hTne : T ≠ ⊥) : normalizer (T : Set G) ≤ M := by
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  exact normalizer_le_of_isSylowOf_two_of_le hD1 hp hM hPM P.isPGroup' hP3.ge hXM hPX hX hT hTne

omit [Finite G] in
theorem le_normalizer_zpowers_of_le_centralizer {P : Subgroup G} {z : G}
    (hz : z ∈ centralizer (P : Set G)) : P ≤ normalizer ((zpowers z : Subgroup G) : Set G) :=
  (le_centralizer_iff.mp (zpowers_le.mpr hz)).trans (centralizer_le_normalizer _)

omit [Finite G] in
theorem centralizer_singleton_le_normalizer_zpowers (z : G) :
    centralizer ({z} : Set G) ≤ normalizer ((zpowers z : Subgroup G) : Set G) := by
  refine le_trans ?_ (centralizer_le_normalizer _)
  rw [zpowers_eq_closure, centralizer_closure]

@[expose] def TransitivityComponentCase (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M D : Subgroup G), ExtremalObstruction p P M D →
    ¬ (P : Subgroup G) ≤ normalizer (D : Set G) →
      ∀ z ∈ D, z ≠ 1 → z ∈ centralizer (P : Set G) → z ^ p = 1 →
        ∀ hPN : (P : Subgroup G) ≤ normalizer ((zpowers z : Subgroup G) : Set G),
          IsCyclic (((P.subtype hPN : Subgroup _) ⊓
            CFSG.Op_p'p p (normalizer ((zpowers z : Subgroup G) : Set G))).map
              (normalizer ((zpowers z : Subgroup G) : Set G)).subtype) →
          ¬ CFSG.ABGLocalTools.IsPConstrained p
              (normalizer ((zpowers z : Subgroup G) : Set G)) →
            normalizer ((zpowers z : Subgroup G) : Set G) ≤ M

theorem transitivityReduction_of_componentCase (hS : Setting G)
    (h : TransitivityComponentCase G) : TransitivityReduction G := by
  intro p hp P M D hext hPD z hzD hz1 hzc hzp
  have hPN := le_normalizer_zpowers_of_le_centralizer hzc
  have hfact : Fact p.Prime := ⟨sigmaA_prime p hp⟩
  by_cases hcon : CFSG.ABGLocalTools.IsPConstrained p
      (normalizer ((zpowers z : Subgroup G) : Set G))
  · exact hext.le_of_isPConstrained hS hp hPD hPN hcon
  by_cases hRc : IsCyclic (((P.subtype hPN : Subgroup _) ⊓
      CFSG.Op_p'p p (normalizer ((zpowers z : Subgroup G) : Set G))).map
        (normalizer ((zpowers z : Subgroup G) : Set G)).subtype)
  · exact h p hp P M D hext hPD z hzD hz1 hzc hzp hPN hRc hcon
  · exact hext.le_of_two_le_pRank_inf_Op_p'p hS hp hPD hPN
      (two_le_pRank_inf_Op_p'p_of_not_isCyclic (sigmaA_odd p hp) hPN hRc)

theorem ExtremalObstruction.isMulCommutative_of_normalizer_le (hS : Setting G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M D : Subgroup G}
    (hext : ExtremalObstruction p P M D)
    (hN : ∀ z ∈ D, z ≠ 1 → z ∈ centralizer (P : Set G) → z ^ p = 1 →
      normalizer ((zpowers z : Subgroup G) : Set G) ≤ M) :
    IsMulCommutative D := by
  have hprime := sigmaA_prime p hp
  have hodd := sigmaA_odd p hp
  by_contra hD
  have hZne : (center D).map D.subtype ≠ ⊥ := by
    intro h
    have hc := hext.card_center_eq hprime hodd hD
    rw [h, card_bot] at hc
    exact hprime.one_lt.ne hc
  obtain ⟨⟨z, hzZ⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZne
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hzD : z ∈ D := map_subtype_le _ hzZ
  have hzc := hext.center_le_centralizer hprime hodd hD hzZ
  have hzp := (hext.pow_eq_one_and_commutator_mem hprime hodd).1 z hzD
  exact hext.centralizer_not_le_of_mem_center hS hp hD hzZ hz1'
    ((centralizer_singleton_le_normalizer_zpowers z).trans (hN z hzD hz1' hzc hzp))

omit [Finite G] in
theorem le_normalizer_pPrimeCoreIn_sup {p : ℕ} {A M N : Subgroup G} (hAM : A ≤ M) (hAN : A ≤ N) :
    A ≤ normalizer ((CFSG.ABGTheoremB.pPrimeCoreIn p M ⊔ CFSG.ABGTheoremB.pPrimeCoreIn p N :
      Subgroup G) : Set G) :=
  (le_inf (hAM.trans (CFSG.ABGTheoremB.le_normalizer_map_subtype M _))
    (hAN.trans (CFSG.ABGTheoremB.le_normalizer_map_subtype _ _))).trans
    (inf_normalizer_le_normalizer_sup _ _)

theorem coprime_card_pPrimeCoreIn_sup {p : ℕ} [Fact p.Prime] {M N : Subgroup G} (hNM : N ≤ M) :
    Nat.Coprime p (Nat.card ↥(CFSG.ABGTheoremB.pPrimeCoreIn p M ⊔
      CFSG.ABGTheoremB.pPrimeCoreIn p N)) := by
  have hB : CFSG.ABGTheoremB.pPrimeCoreIn p N ≤ M :=
    (CFSG.ABGTheoremB.pPrimeCoreIn_le p N).trans hNM
  have hBc : Nat.Coprime p (Nat.card ((CFSG.ABGTheoremB.pPrimeCoreIn p N).subgroupOf M)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hB).toEquiv, CFSG.ABGTheoremB.pPrimeCoreIn,
      card_map_of_injective N.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  have hsup := normal_coprime_sup_coprime p ((CFSG.ABGTheoremB.pPrimeCoreIn p N).subgroupOf M)
    (CFSG.pPrimeCore p M) CFSG.pPrimeCore_normal hBc CFSG.pPrimeCore_coprime_card
  have himage : (((CFSG.ABGTheoremB.pPrimeCoreIn p N).subgroupOf M) ⊔
      CFSG.pPrimeCore p M).map M.subtype =
        CFSG.ABGTheoremB.pPrimeCoreIn p M ⊔ CFSG.ABGTheoremB.pPrimeCoreIn p N := by
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hB, sup_comm]
    rfl
  rw [← himage, card_map_of_injective M.subtype_injective]
  exact hsup

theorem transitivityCase_of_steps (hS : Setting G) (hD1 : TheoremD1 G)
    (hR : TransitivityReduction G) (h13 : GL83InvariantTwoSylow G)
    (h15 : GL83InvariantTwoTransitivity G) : TransitivityCase G := by
  intro p hp P M D hext hPD
  have hprime := sigmaA_prime p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  have hN := hR p hp P M D hext hPD
  have hDab := hext.isMulCommutative_of_normalizer_le hS hp hN
  have hM := hext.obstruction.1
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  have hDM : D ≤ M := hext.obstruction.2.1.trans hPM
  obtain ⟨A, hAP, hA, hAc⟩ := pRank_attained p (P : Subgroup G) (by rw [hP3]; norm_num)
  rw [hP3] at hAc
  obtain ⟨-, z, hzD, hz1, hzc, hzp, -⟩ := isolatedPlane_structure hprime P.isPGroup'
    (hext.isIsolatedPlane_of_isMulCommutative hprime hDab) hAP
    ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p A).2 hA) hAc
  have hPN₀ := le_normalizer_zpowers_of_le_centralizer hzc
  have hN₀M := hN z hzD hz1 hzc hzp
  have hCD : centralizer (D : Set G) ≤ M := by
    refine le_trans ?_ ((centralizer_le_normalizer _).trans hN₀M)
    rw [zpowers_eq_closure, centralizer_closure]
    exact centralizer_le (Set.singleton_subset_iff.mpr hzD)
  obtain ⟨T, hO2T, hT⟩ := exists_invariantTwoMaximalWithin_containing D M (pCoreOf 2 M)
    (pCoreOf_le 2 M) (pCoreOf_isPGroup 2 M) (hDM.trans (localGroup_le_normalizer_pCoreOf 2 M))
  have hTne : T ≠ ⊥ := fun h => twoLocal_pCoreOf_ne_bot M hM.1.1 (le_bot_iff.mp (h ▸ hO2T))
  have hXM : CFSG.ABGTheoremB.pPrimeCoreIn p M ⊔ CFSG.ABGTheoremB.pPrimeCoreIn p
      (normalizer ((zpowers z : Subgroup G) : Set G)) ≤ M :=
    sup_le (CFSG.ABGTheoremB.pPrimeCoreIn_le p M)
      ((CFSG.ABGTheoremB.pPrimeCoreIn_le p _).trans hN₀M)
  have hPX : (P : Subgroup G) ≤ normalizer ((CFSG.ABGTheoremB.pPrimeCoreIn p M ⊔
      CFSG.ABGTheoremB.pPrimeCoreIn p (normalizer ((zpowers z : Subgroup G) : Set G)) :
        Subgroup G) : Set G) :=
    le_normalizer_pPrimeCoreIn_sup hPM hPN₀
  have hNT := normalizer_le_of_isSylowOf_two hS hD1 hp hM hXM hPX
    (coprime_card_pPrimeCoreIn_sup hN₀M) (h13 p hp P M D hext hPD hDab z hzD hz1 hzc hzp T hT)
    hTne
  have hTglob := invariantTwoMaximalWithin_global_of_normalizer_le D M T hDM hT hNT
  exact ⟨hCD, T, hTglob, hNT, fun T' hT' => h15 p hp P M D hext hPD hDab T T' hTglob hT'⟩

@[expose] def GL83InvariantTwoContainment (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M D : Subgroup G), ExtremalObstruction p P M D →
    ¬ (P : Subgroup G) ≤ normalizer (D : Set G) → IsMulCommutative D →
      ∀ T : Subgroup G, rankTwoMaximalInvariantTwoSubgroup D T → T ≤ M

theorem gl83InvariantTwoTransitivity_of_containment (hS : Setting G)
    (hR : TransitivityReduction G) (h13 : GL83InvariantTwoSylow G)
    (hcont : GL83InvariantTwoContainment G) : GL83InvariantTwoTransitivity G := by
  intro p hp P M D hext hPD hDab T T' hT hT'
  have hprime := sigmaA_prime p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  have hN := hR p hp P M D hext hPD
  have hM := hext.obstruction.1
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  obtain ⟨A, hAP, hA, hAc⟩ := pRank_attained p (P : Subgroup G) (by rw [hP3]; norm_num)
  rw [hP3] at hAc
  obtain ⟨-, z, hzD, hz1, hzc, hzp, -⟩ := isolatedPlane_structure hprime P.isPGroup'
    (hext.isIsolatedPlane_of_isMulCommutative hprime hDab) hAP
    ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p A).2 hA) hAc
  have hPN₀ := le_normalizer_zpowers_of_le_centralizer hzc
  have hN₀M := hN z hzD hz1 hzc hzp
  have hPX : (P : Subgroup G) ≤ normalizer ((CFSG.ABGTheoremB.pPrimeCoreIn p M ⊔
      CFSG.ABGTheoremB.pPrimeCoreIn p (normalizer ((zpowers z : Subgroup G) : Set G)) :
        Subgroup G) : Set G) :=
    le_normalizer_pPrimeCoreIn_sup hPM hPN₀
  have hX := h13 p hp P M D hext hPD hDab z hzD hz1 hzc hzp
  have hTX := (hX T (global_invariant_two_maximal_is_maximal_within D M T hT
    (hcont p hp P M D hext hPD hDab T hT))).le
  have hT'X := (hX T' (global_invariant_two_maximal_is_maximal_within D M T' hT'
    (hcont p hp P M D hext hPD hDab T' hT'))).le
  exact rank_two_maximal_two_subgroups_common_signalizer_transitivity p hprime D T' T _
    (P.isPGroup'.to_le hext.obstruction.2.1) hT' hT (coprime_card_pPrimeCoreIn_sup hN₀M)
    (hext.obstruction.2.1.trans hPX) hT'X hTX

theorem transitivityCase_of_containment (hS : Setting G) (hD1 : TheoremD1 G)
    (hR : TransitivityReduction G) (h13 : GL83InvariantTwoSylow G)
    (hcont : GL83InvariantTwoContainment G) : TransitivityCase G :=
  transitivityCase_of_steps hS hD1 hR h13
    (gl83InvariantTwoTransitivity_of_containment hS hR h13 hcont)

end CFSG.LocalAnalysis.RankThreeTheoremC
