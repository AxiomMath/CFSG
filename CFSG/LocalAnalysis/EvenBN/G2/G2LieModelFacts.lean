module

public import CFSG.Blueprint.Catalog
public import CFSG.RankThree.GF2n.Stroth80.Sec117Config
public import Certificates.Certificate3951
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate120
import CFSG.Quasithin.Vol2.GoldschmidtF431G2ModelData
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenInvolutions
import CFSG.LocalAnalysis.EvenBN.G2.Automorphisms
import CFSG.RankThree.Chevalley.EvenPinnedRootSL2
import CFSG.ClassicalGroups.SpecialLinear.InvolutionInverts
import CFSG.LieType.Simplicity.Exceptional
import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
public import CFSG.LieType.Chevalley.RootCommutatorData
import CFSG.GroupTheory.HallHigmanPiCore
import CFSG.LieType.Chevalley.LangStronglyOrthogonalCommute
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeBasic
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Native
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.Reduced
import CFSG.Quasithin.Background.A3Structure312
import CFSG.Quasithin.Background.F3
import CFSG.Quasithin.Background.SmithB42G2FNat
import CFSG.Quasithin.Background.SmithB42G2FOff
import CFSG.Quasithin.EmptyFaithful.S1414Defs
import CFSG.Quasithin.EmptyFaithful.S1417Sylow
import CFSG.Quasithin.EmptyFaithful.S141Statements
import CFSG.Quasithin.H13.J4Order
import CFSG.Quasithin.H13.J4OrderBase
import CFSG.Quasithin.Recognition.F4Moufang
import CFSG.Quasithin.Recognition.F4Thirtyone
import CFSG.Quasithin.Vol2.Ch11G2Q8LineGen
import CFSG.Quasithin.Vol2.Ch11SecBFacts22
import CFSG.Quasithin.Vol2.Ch11SecBFacts22G
import CFSG.Quasithin.Vol2.Ch11StatementsF
import CFSG.Quasithin.Vol2.Ch11StatementsG
import CFSG.Quasithin.Vol2.Ch11StatementsH
import CFSG.Quasithin.Vol2.Ch11StatementsInputs
import CFSG.RankThree.PartTwo.Sec12.Notation
import CFSG.RankThree.PartTwo.Sec8.Pairs
import CFSG.RankThree.PartTwo.Sec8.Statements
import CFSG.Sporadic.Schreier.J4SProfileNode
import Certificates.Certificate8026Base

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.RankThree.GF2n.Stroth80 (IsLBImage)

theorem lieModel_G2_params {X : Type} [Group X] {m x : ℕ}
    (hX : LieModel X .G2 m 2 x) : m = 0 ∧ 2 ≤ x := by
  obtain ⟨-, -, hm, h3⟩ := hX.admissible
  refine ⟨hm, ?_⟩
  by_contra hlt
  have h2 : 2 ^ x ≤ 2 := (Nat.pow_le_pow_right (by norm_num) (by omega : x ≤ 1)).trans_eq rfl
  omega

private theorem vSL_one_eq_transvection {K : Type} [Field K] :
    ((vSL 1 : SL2 K) : Matrix (Fin 2) (Fin 2) K) = Matrix.transvection 1 0 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_vSL, Matrix.transvection]

theorem exists_orderOf_eq_card_add_one_pinnedX_conj_eq_inv
    {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2] {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) :
    ∃ g : adjointGroup τ K, orderOf g = Nat.card K + 1 ∧
      (⟨pinnedX τ K α 1, pinnedX_mem_adjointGroup α 1⟩ : adjointGroup τ K) * g *
        ⟨pinnedX τ K α 1, pinnedX_mem_adjointGroup α 1⟩ = g⁻¹ := by
  obtain ⟨S, hS, hTS⟩ :=
    CFSG.ClassicalGroups.SpecialLinear.exists_orderOf_eq_card_add_one_conj_eq_inv (K := K)
  obtain ⟨hinj, hrange, -, hX, -⟩ :=
    CFSG.RankThree.Chevalley.even_Chevalley_pinned_root_SL2_maps τ K
      (CFSG.LieType.Chevalley.IsRoot.neg hα)
  have hv : rootSL2 τ K (-α) (vSL 1) = pinnedX τ K α 1 := by rw [(hX 1).2, neg_neg]
  have hmem : ∀ A, rootSL2 τ K (-α) A ∈ adjointGroup τ K := fun A => by
    have h : rootSL2 τ K (-α) A ∈ (rootSL2 τ K (-α)).range := ⟨A, rfl⟩
    rw [hrange] at h
    exact sup_le (rootSubgroup_le_adjointGroup _) (rootSubgroup_le_adjointGroup _) h
  have hvS : vSL 1 * S * vSL 1 = S⁻¹ := by
    refine Subtype.ext ?_
    simpa only [Matrix.SpecialLinearGroup.coe_mul, vSL_one_eq_transvection] using hTS
  refine ⟨⟨_, hmem S⟩, ?_, Subtype.ext ?_⟩
  · rw [Subgroup.orderOf_mk, orderOf_injective _ hinj, hS]
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hv, ← map_mul, ← map_mul, hvS, map_inv]

private theorem exists_conj_eq_inv_adjointGroup_G2
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (z : adjointGroup .G2 K) (hz : orderOf z = 2) :
    ∃ g : adjointGroup .G2 K, orderOf g = Nat.card K + 1 ∧ z⁻¹ * g * z = g⁻¹ := by
  have key : ∀ α, IsRoot .G2 α →
      IsConj z ⟨pinnedX .G2 K α 1, pinnedX_mem_adjointGroup α 1⟩ →
      ∃ g : adjointGroup .G2 K, orderOf g = Nat.card K + 1 ∧ z⁻¹ * g * z = g⁻¹ := by
    intro α hα hzy
    obtain ⟨c, hc⟩ := isConj_iff.mp hzy
    obtain ⟨g, hg, hgy⟩ := exists_orderOf_eq_card_add_one_pinnedX_conj_eq_inv (K := K) hα
    set y : adjointGroup .G2 K := ⟨pinnedX .G2 K α 1, pinnedX_mem_adjointGroup α 1⟩
    have hy : y⁻¹ = y := inv_eq_of_mul_eq_one_right
      (Subtype.ext (CFSG.ComponentClassification.UnbalancedCatalog.pinnedX_mul_self α 1))
    have hz' : z = c⁻¹ * y * c := by rw [← hc]; group
    refine ⟨c⁻¹ * g * c, ?_, ?_⟩
    · rw [show c⁻¹ * g * c = MulAut.conj c⁻¹ g by simp, MulEquiv.orderOf_eq, hg]
    · calc z⁻¹ * (c⁻¹ * g * c) * z = c⁻¹ * (y⁻¹ * g * y) * c := by rw [hz']; group
        _ = c⁻¹ * g⁻¹ * c := by rw [hy, hgy]
        _ = (c⁻¹ * g * c)⁻¹ := by group
  rcases even_G2_involutions_conjugate_to_root_elements K (ringChar.eq K 2) z hz with h | h
  · exact key g2c isRoot_g2c h
  · exact key g2v isRoot_g2v h

private theorem orderOf_g2N_one_one
    {K : Type} [Field K] [CharP K 2] : orderOf (g2N (1 : K) 1 0 0 0 0) = 8 := by
  have h2 : g2N (1 : K) 1 0 0 0 0 ^ 2 = g2N 0 0 1 1 1 0 := by
    rw [sq, g2N_mul_self]
    exact g2N_eq_g2N (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)
  have h4 : g2N (1 : K) 1 0 0 0 0 ^ 4 = g2N 0 0 0 0 0 1 := by
    rw [show 4 = 2 * 2 by norm_num, pow_mul, h2, sq, g2N_mul_self]
    exact g2N_eq_g2N (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)
  have h8 : g2N (1 : K) 1 0 0 0 0 ^ 8 = 1 := by
    rw [show 8 = 4 * 2 by norm_num, pow_mul, h4, sq, g2N_mul_self, ← g2N_zero]
    exact g2N_eq_g2N (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)
  have hne : ¬ g2N (1 : K) 1 0 0 0 0 ^ 2 ^ 2 = 1 := by
    rw [show 2 ^ 2 = 4 by norm_num, h4, ← g2N_zero]
    exact fun h => one_ne_zero (g2N_injective h).2.2.2.2.2
  exact (orderOf_eq_prime_pow (p := 2) (n := 2) hne (by norm_num [h8])).trans
    (by norm_num : 2 ^ (2 + 1) = 8)

private theorem isElemAbelian_two_of_forall_sq_eq_one {Y : Type*} [Group Y] {E : Subgroup Y}
    (h : ∀ e ∈ E, e ^ 2 = 1) : CFSG.Open.IsElemAbelian 2 E := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, h⟩
  have h1 : ∀ y ∈ E, y⁻¹ = y := fun y hy => inv_eq_of_mul_eq_one_right (by rw [← sq, h y hy])
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← h1 _ (mul_mem a.2 b.2), mul_inv_rev, h1 _ a.2,
    h1 _ b.2]

section Model

variable
  {X : Type} [Group X] {m x : ℕ}

theorem exists_conj_eq_inv_of_lieModel_G2
    (hX : LieModel X .G2 m 2 x) (d : X) (hd : orderOf d = 2) :
    ∃ τ : X, orderOf τ = 2 ^ x + 1 ∧ d⁻¹ * τ * d = τ⁻¹ := by
  obtain ⟨rfl, -⟩ := lieModel_G2_params hX
  obtain ⟨-, K, _, _, _, hK, ⟨e⟩⟩ := CFSG.Quasithin.H13.F431.G2.g2_model_data hX
  obtain ⟨g, hg, hgd⟩ := exists_conj_eq_inv_adjointGroup_G2 (e d) (by rw [e.orderOf_eq]; exact hd)
  refine ⟨e.symm g, by rw [e.symm.orderOf_eq, hg, hK], e.injective ?_⟩
  simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply] using hgd

theorem card_le_of_sq_eq_one_of_lieModel_G2 (hX : LieModel X .G2 m 2 x)
    {E : Subgroup (MulAut X)} (hE : ∀ e ∈ E, e ^ 2 = 1) : Nat.card E ≤ 2 ^ (3 * x) := by
  obtain ⟨rfl, hx⟩ := lieModel_G2_params hX
  obtain ⟨-, K, _, _, _, hK, ⟨e⟩⟩ := CFSG.Quasithin.H13.F431.G2.g2_model_data hX
  have hE' : CFSG.Open.IsElemAbelian 2 (E.map (MulAut.congr e).toMonoidHom) := by
    refine isElemAbelian_two_of_forall_sq_eq_one ?_
    rintro _ ⟨f, hf, rfl⟩
    rw [← map_pow, hE f hf, map_one]
  calc Nat.card E = Nat.card (E.map (MulAut.congr e).toMonoidHom) :=
        (Subgroup.card_map_of_injective (MulAut.congr e).injective).symm
    _ ≤ Nat.card K ^ 3 := (Model.card_le_of_isElemAbelian hK hx hE').1
    _ = 2 ^ (3 * x) := by rw [hK, ← pow_mul, mul_comm]

theorem mul_le_of_isLBImage_of_lieModel_G2 (hX : LieModel X .G2 m 2 x) {t : X} {a n : ℕ}
    {N : Subgroup X} {E : Subgroup (MulAut X)} (hE : IsLBImage t a n N E) :
    a * (n - 2) ≤ 3 * x :=
  (Nat.pow_le_pow_iff_right (by norm_num)).mp
    (hE.card_le.trans (card_le_of_sq_eq_one_of_lieModel_G2 hX hE.sq_eq_one))

theorem exists_orderOf_eq_eight_of_lieModel_G2
    (hX : LieModel X .G2 m 2 x) : ∃ g : X, orderOf g = 8 := by
  obtain ⟨rfl, -⟩ := lieModel_G2_params hX
  obtain ⟨-, K, _, _, _, -, ⟨e⟩⟩ := CFSG.Quasithin.H13.F431.G2.g2_model_data hX
  have hmem : g2N (1 : K) 1 0 0 0 0 ∈ adjointGroup .G2 K := by
    simp only [g2N]
    exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (pinnedX_mem_adjointGroup _ _)
      (pinnedX_mem_adjointGroup _ _)) (pinnedX_mem_adjointGroup _ _))
      (pinnedX_mem_adjointGroup _ _)) (pinnedX_mem_adjointGroup _ _))
      (pinnedX_mem_adjointGroup _ _)
  exact ⟨e.symm ⟨_, hmem⟩, by rw [e.symm.orderOf_eq, Subgroup.orderOf_mk, orderOf_g2N_one_one]⟩

theorem isSimpleGroup_of_lieModel_G2
    (hX : LieModel X .G2 m 2 x) : IsSimpleGroup X :=
  (CFSG.LieType.Simplicity.fam_g2_simplicity X 2 x
    (hX.chevalleyExceptionalModel (by decide))).2

theorem card_eq_ordG2_of_lieModel_G2 (hX : LieModel X .G2 m 2 x) :
    Nat.card X = CFSG.Open.ordG2 (2 ^ x) :=
  CFSG.Timmesfeld.ExceptionalOrders.card_of_untwistedChevalleyModel_G2
    (hX.chevalleyExceptionalModel (by decide)).2

end Model

end CFSG.LocalAnalysis.EvenBN.G2
