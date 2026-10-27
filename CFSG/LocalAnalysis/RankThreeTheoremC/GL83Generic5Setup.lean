module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Ctx
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericCaseLayer
import CFSG.LocalAnalysis.RankThreeTheoremC.PlaneTheoremE
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerOdd

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

section Setup

variable {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

theorem gen5_prime (hl : Gen5Local G p P M x) : p.Prime := sigmaA_prime p hl.sigma

theorem gen5_five_le (hG : Gen5Global G) (hl : Gen5Local G p P M x) : 5 ≤ p :=
  (hG.layer p hl.sigma P M hl.core hl.fail hl.larger x hl.generic).1

theorem gen5_psl (hG : Gen5Global G) (hl : Gen5Local G p P M x) :
    haveI : Fact p.Prime := ⟨gen5_prime hl⟩
    Nonempty (gen5L x ≃* PSL(2, GaloisField p 2)) := by
  obtain ⟨-, hf, m, hm2, ⟨e⟩⟩ :=
    hG.layer p hl.sigma P M hl.core hl.fail hl.larger x hl.generic
  obtain ⟨hxP, ⟨-, hx1, hxp, -, -⟩, hsyl, hrk⟩ := hl.generic
  obtain ⟨rfl, -⟩ := eq_two_of_isSylowOf_mulEquiv_psl hsyl (rankThreeLayer_le _)
    (le_normalizer_rankThreeLayer _) ⟨hxP, mem_centralizer_singleton_iff.mpr rfl⟩ hx1 hxp
    (fun c hc => mem_centralizer_singleton_iff.mp hc) hrk.le hm2 e
  exact ⟨e⟩

theorem gen5_P_abelian (hG : Gen5Global G) (hl : Gen5Local G p P M x) :
    (P : Subgroup G) ≤ centralizer ({x} : Set G) ∧ IsMulCommutative (P : Subgroup G) :=
  (generic_central_abelian hG.setting hG.d1 hG.u0 hG.layer hl.sigma hl.core hl.fail hl.larger
    hl.generic).2

theorem gen5_sylow (hG : Gen5Global G) (hl : Gen5Local G p P M x) :
    IsSylowOf p (gen5U (P : Subgroup G) x) (gen5L x) := by
  have : Fact p.Prime := ⟨gen5_prime hl⟩
  have h := hl.generic.2.2.1.inf_of_le_normalizer (rankThreeLayer_le _)
    (le_normalizer_rankThreeLayer _)
  rwa [inf_of_le_left (gen5_P_abelian hG hl).1] at h

theorem gen5_U_elemAbelian (hG : Gen5Global G) (hl : Gen5Local G p P M x) :
    IsElemAbelian p (gen5U (P : Subgroup G) x) ∧ Nat.card (gen5U (P : Subgroup G) x) = p ^ 2 := by
  have : Fact p.Prime := ⟨gen5_prime hl⟩
  obtain ⟨e⟩ := gen5_psl hG hl
  have hK : Nat.card (GaloisField p 2) = p ^ 2 := GaloisField.card p 2 (by norm_num)
  have hU := gen5_sylow hG hl
  have hPab := (gen5_P_abelian hG hl).2
  refine ⟨⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun u hu => pow_eq_one_of_mem_isSylowOf_psl hK e hU hu⟩,
    ?_⟩
  · have h := hPab.is_comm.comm ⟨a, a.2.1⟩ ⟨b, b.2.1⟩
    have h2 := congrArg Subtype.val h
    exact h2
  · rw [hU.card_eq, factorization_card_of_mulEquiv_psl hK e]

theorem gen5_not_le (hG : Gen5Global G) (hl : Gen5Local G p P M x) : ¬ gen5L x ≤ M := by
  have : Fact p.Prime := ⟨gen5_prime hl⟩
  obtain ⟨e⟩ := gen5_psl hG hl
  obtain ⟨-, ⟨-, -, -, -, hxCM⟩, hsyl, -⟩ := hl.generic
  exact not_rankThreeLayer_le_of_mulEquiv_psl hG.setting hG.u0 hl.sigma hl.core hxCM hsyl le_rfl e

theorem gen5_centralizer_le (hG : Gen5Global G) (hl : Gen5Local G p P M x)
    {a : G} (ha : a ∈ gen5U (P : Subgroup G) x) (ha1 : a ≠ 1) :
    centralizer ({a} : Set G) ≤ M := by
  have : Fact p.Prime := ⟨gen5_prime hl⟩
  obtain ⟨e⟩ := gen5_psl hG hl
  obtain ⟨hU, -, hPab⟩ := generic_central_abelian hG.setting hG.d1 hG.u0 hG.layer hl.sigma
    hl.core hl.fail hl.larger hl.generic
  obtain ⟨hxL, -⟩ := layer_data_of_isGenericPoint hl.generic le_rfl e
  obtain ⟨-, ⟨-, hx1, hxp, -, -⟩, -, -⟩ := hl.generic
  refine centralizer_le_of_not_mem_zpowers hG.setting hl.sigma hl.core hU hPab ha.1 ha1
    ((gen5_U_elemAbelian hG hl).1.2 a ha) fun hax => ha1 ?_
  exact mem_zpowers_layer_eq_one hx1 hxp hxL ha.2 hax

theorem gen5_normalizer_le (hG : Gen5Global G) (hl : Gen5Local G p P M x)
    {D : Subgroup G} (hD : D ≤ gen5U (P : Subgroup G) x) (hD1 : D ≠ ⊥) :
    normalizer (D : Set G) ≤ M := by
  have : Fact p.Prime := ⟨gen5_prime hl⟩
  have hΓ : rankThreeGamma 1 p (gen5U (P : Subgroup G) x) ≤ M :=
    gamma_one_le_of_forall_centralizer_le hG.setting hG.u0 hl.sigma hl.core inf_le_left
      fun y hy hy1 _ => gen5_centralizer_le hG hl hy hy1
  have hUe := (gen5_U_elemAbelian hG hl).1
  have hDe : IsElemAbelian p D := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun d hd => hUe.2 d (hD hd)⟩
    have h := hUe.1.is_comm.comm ⟨a, hD a.2⟩ ⟨b, hD b.2⟩
    have h2 := congrArg Subtype.val h
    exact h2
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (elementary_isPGroup p D hDe)
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hD1 (Subgroup.card_eq_one.mp (by rw [hk, pow_zero]))
  exact (gamma_le_iff 1 p _ M).mp hΓ D hD
    ((Nat.one_le_iff_ne_zero.mpr hk0).trans (le_pRank_of_elemAbelian_card le_rfl hDe hk))

theorem gen5_centralizer_U_le (hG : Gen5Global G) (hl : Gen5Local G p P M x) :
    centralizer ((gen5U (P : Subgroup G) x : Subgroup G) : Set G) ≤ M := by
  have hne : gen5U (P : Subgroup G) x ≠ ⊥ := by
    intro h
    have hc := (gen5_U_elemAbelian hG hl).2
    rw [h, card_bot] at hc
    have := (gen5_prime hl).one_lt
    nlinarith
  exact (centralizer_le_normalizer _).trans (gen5_normalizer_le hG hl le_rfl hne)

theorem gen5_coprime_le (hG : Gen5Global G) (hl : Gen5Local G p P M x)
    {X : Subgroup G} (hX : ¬ p ∣ Nat.card X)
    (hN : gen5U (P : Subgroup G) x ≤ normalizer (X : Set G)) : X ≤ M := by
  obtain ⟨hUe, hUc⟩ := gen5_U_elemAbelian hG hl
  rw [CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane p
    (gen5_prime hl) _ X (fun u => Subtype.ext (hUe.2 u u.2)) hUc hX hN]
  refine iSup_le fun u => iSup_le fun hu1 => inf_le_right.trans ?_
  exact gen5_centralizer_le hG hl u.2 fun h => hu1 (Subtype.ext h)

end Setup

end CFSG.LocalAnalysis.RankThreeTheoremC
