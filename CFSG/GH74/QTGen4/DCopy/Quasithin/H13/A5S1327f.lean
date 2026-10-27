module

public import CFSG.Quasithin.H13.A5S1327f
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1327e
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Statements
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1327fS331

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open CFSG.LieType.BorelTits
open scoped commutatorElement

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem thompsonJ_not_le_centralizer_F4 (h5172 : Stmt5_1_7_two_F4)
    {H : Subgroup G} (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) :
    ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G) := by
  intro hJ
  have hZH' : ⁅quasithinOmegaOneCenter T, H⁆ ≠ ⊥ := by
    intro h
    apply hHZ
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (by rw [Subgroup.commutator_comm]; exact h)
  obtain ⟨hLJ, -, -⟩ := h5172 G T _ L V H 2 S.hyp501 S.isCh5Module hH hZH'
  have hLC : L ≤ Subgroup.centralizer (V : Set G) := by
    rw [hLJ]
    refine Subgroup.commutator_le.mpr fun l hl j hj => ?_
    have hlN := S.frame.L_le hl
    have hjN := S.frame.T_le (thompsonJ_le_self T hj)
    have hcN : ⁅l, j⁆ ∈ Subgroup.normalizer (V : Set G) := by
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hlN hjN)
        (Subgroup.inv_mem _ hlN)) (Subgroup.inv_mem _ hjN)
    refine S.frame.mem_centralizer_of_rho ⟨_, hcN⟩ ?_
    have e : (⟨⁅l, j⁆, hcN⟩ : ↥(Subgroup.normalizer (V : Set G))) =
        ⟨l, hlN⟩ * ⟨j, hjN⟩ * (⟨l, hlN⟩)⁻¹ * (⟨j, hjN⟩)⁻¹ := by
      apply Subtype.ext
      simp [commutatorElement_def]
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv,
      S.frame.rho_eq_one_of_mem ⟨j, hjN⟩ (hJ hj)]
    group
  obtain ⟨g, hgL, hg⟩ := (S.frame.image_L c3p).2 c3p_sign
  have h1 := S.frame.rho_eq_one_of_mem g (hLC hgL)
  rw [hg] at h1
  exact absurd h1 (by decide)

theorem triple_of_F4 (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4)
    (h5172 : Stmt5_1_7_two_F4) {H : Subgroup G} (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hsolv : Group.IsSolvable ↥H) (hS3 : Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3)))
    (h3 : ¬ ThreeTop (S.H0 H)) : F6.IsGoldschmidtTripleIn (S.H0 H) (S.L1 ⊔ T) H := by
  have hTH : T ≤ H := hH.1.1
  obtain ⟨⟨j, hjJ, hjN, hj⟩, -⟩ :=
    S.lemma_13_2_4_two_b (S.thompsonJ_not_le_centralizer_F4 h5172 hH hHZ)
  have hjT : j ∈ T := thompsonJ_le_self T hjJ
  have hpow3 := S.pow_three_pow_mem_F4 h331 hH hHZ hsolv hS3
  refine ⟨(S.H0_eq_sup hTH).symm, S.quotient_L1T_equiv_S3 hjT hjN hj,
    S.quotient_pCore_equiv_S3_F4 h331 h1222 hH hHZ hsolv hS3, ?_⟩
  rw [S.inf_L1T_eq_T hTH hjT hjN hj hpow3 h3]
  exact isSylowTwoOf_of_le S.h13.sylow (hTH.trans le_sup_right)

theorem f618_of_F4 (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4)
    (h5172 : Stmt5_1_7_two_F4) (hF618 : F6.TheoremF618Cat)
    {H : Subgroup G} (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hsolv : Group.IsSolvable ↥H) (hS3 : Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3)))
    (hO2 : pCoreOf 2 (S.H0 H) ≠ ⊥) (h3 : ¬ ThreeTop (S.H0 H)) :
    IsGoldschmidtAmalgam
        (((S.L1 ⊔ T).subgroupOf (S.H0 H)).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(S.H0 H))))
        ((H.subgroupOf (S.H0 H)).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(S.H0 H)))) ∧
      F6.F618ConclusionCat
        (((S.L1 ⊔ T).subgroupOf (S.H0 H)).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(S.H0 H))))
        ((H.subgroupOf (S.H0 H)).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(S.H0 H)))) := by
  have htriple := S.triple_of_F4 h331 h1222 h5172 hH hHZ hsolv hS3 h3
  rcases htriple.goldschmidt_mod_pPrimeCore with ⟨-, hAm, -⟩ | ⟨-, -, ⟨e⟩, -, -⟩
  · have := S.h13.simple
    have hSQ : CFSG.SectionRank.IsSQTKCat ↥(S.H0 H) :=
      (qtkeCore_of_cat S.h13.nonabelian S.h13.qtke).1 _ hO2
    exact ⟨hAm, hF618 _ _ _ hAm.toIsGoldschmidtTriple
      ⟨↥(S.H0 H), inferInstance, inferInstance, hSQ, ⟨MulEquiv.refl _⟩⟩⟩
  · exfalso
    apply h3
    intro q
    refine ⟨1, ?_⟩
    have hq : e q ∈ oTwoUpper (⊤ : Subgroup (Equiv.Perm (Fin 3))) := by
      rw [← Subgroup.map_top_of_surjective e.toMonoidHom e.surjective, oTwoUpper_map]
      exact ⟨q, q.2, rfl⟩
    have h1 : e ((q : _) ^ 3) = 1 := by rw [map_pow]; exact oTwoUpper_perm3 _ hq
    apply Subtype.ext
    simpa using (map_eq_one_iff e e.injective).mp h1

end Setting

end CFSG.Quasithin.H13.A5
