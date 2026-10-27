module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotNonsplit
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotAlignFieldTwist
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_mono le_perfectCore_of_perfect)

local instance e8PilotQ2PieceTorusNeZeroRank : NeZero Tag.E8.rank := ⟨by decide⟩

section SL2

variable {K : Type} [Field K] {K₂ : Type} [Field K₂]

theorem eq_one_of_ne_zero_of_natCard_eq_two [Finite K] (hK : Nat.card K = 2) {x : K}
    (hx : x ≠ 0) : x = 1 := by
  have := Fintype.ofFinite K
  have h := FiniteField.pow_card_sub_one_eq_one x hx
  rwa [← Nat.card_eq_fintype_card, hK, show 2 - 1 = 1 from rfl, pow_one] at h

theorem pow_three_eq_one_of_natCard_eq_four [Finite K₂] (hK₂ : Nat.card K₂ = 2 ^ 2) (l : K₂ˣ) :
    l ^ 3 = 1 := by
  have := Fintype.ofFinite K₂
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  have h := FiniteField.pow_card_sub_one_eq_one (l : K₂) l.ne_zero
  rwa [← Nat.card_eq_fintype_card, hK₂] at h

theorem exists_inv_mul_map_mul_eq_HSL_of_card_two [Finite K] [Finite K₂] [CharP K₂ 2]
    (hK : Nat.card K = 2) (hK₂ : Nat.card K₂ = 2 ^ 2) (ι : K →+* K₂) {A : SL2 K}
    (hA : orderOf A = 3) :
    ∃ P : SL2 K₂, ∃ l : K₂ˣ, 3 ≤ orderOf l ∧
      P⁻¹ * Matrix.SpecialLinearGroup.map ι A * P = HSL l := by
  have : CharP K 2 := F4Pilot.charP_two_of_natCard_eq_two_pow (f := 1) (by rw [hK]; rfl)
  have hc := F4Pilot.apply_one_zero_ne_zero_of_orderOf_eq (A := A) (by rw [hA, hK])
  have htr : Matrix.trace (A : Matrix (Fin 2) (Fin 2) K) = 1 := by
    refine eq_one_of_ne_zero_of_natCard_eq_two hK fun ht => ?_
    have hA2 : A ^ 2 = 1 := by
      refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
      rw [F4Pilot.sq_eq_trace_smul_sub_one, ht, zero_smul, zero_sub, Matrix.neg_apply,
        CharTwo.neg_eq, Matrix.SpecialLinearGroup.coe_one]
    have h2 := orderOf_le_of_pow_eq_one (by norm_num) hA2
    omega
  obtain ⟨l, hl⟩ := F4Pilot.exists_three_le_orderOf (K := K₂) (by rw [hK₂]; norm_num)
  have hl3 : (l : K₂) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, pow_three_eq_one_of_natCard_eq_four hK₂ l, Units.val_one]
  obtain ⟨hl1, hl2⟩ := F4Pilot.ne_one_and_sq_ne_one_of_three_le_orderOf hl
  have hq : (l : K₂) ^ 2 - (1 : K₂) * l + 1 = 0 := by
    have h1 : ((l : K₂) - 1) * ((l : K₂) ^ 2 + l + 1) = 0 := by linear_combination hl3
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd (Units.ext (by rw [Units.val_one]; exact sub_eq_zero.1 h)) hl1
    · linear_combination h + (-(l : K₂)) * (CharTwo.two_eq_zero : (2 : K₂) = 0)
  have hll : (l : K₂) ≠ ((l⁻¹ : K₂ˣ) : K₂) := by
    intro h
    refine hl2 (Units.ext ?_)
    rw [Units.val_pow_eq_pow_val, Units.val_one, sq]
    conv_lhs => rhs; rw [h]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hc' :
      ((Matrix.SpecialLinearGroup.map ι A : SL2 K₂) : Matrix (Fin 2) (Fin 2) K₂) 1 0 ≠ 0 := by
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
    exact (_root_.map_ne_zero _).2 hc
  have htr' : Matrix.trace ((Matrix.SpecialLinearGroup.map ι A : SL2 K₂) :
      Matrix (Fin 2) (Fin 2) K₂) = 1 := by
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.trace_fin_two,
      Matrix.map_apply, Matrix.map_apply, ← map_add, ← Matrix.trace_fin_two, htr, map_one]
  obtain ⟨P, hP⟩ := F4Pilot.exists_inv_mul_mul_eq_HSL _ hc' l (by rw [htr']; exact hq) hll
  exact ⟨P, l, hl, hP⟩

end SL2

section Theta


variable {K : Type} [Field K] {K₂ : Type} [Field K₂]

theorem exists_conj_baseChangeGL_eq_highDiag_of_card_two [Finite K] [Finite K₂] [CharP K₂ 2]
    (hK : Nat.card K = 2) (hK₂ : Nat.card K₂ = 2 ^ 2) (ι : K →+* K₂) {x : ModGL .E8 K}
    (hxJ : x ∈ EPilot.highRootSL2 .E8 K) (hx : orderOf x = 3) :
    ∃ n ∈ EPilot.highRootSL2 .E8 K₂, ∃ l : K₂ˣ, 3 ≤ orderOf l ∧
      n⁻¹ * baseChangeGL ι x * n = rootDiagUnit .E8 (EPilot.highDiag .E8 l) := by
  have : CharP K 2 := F4Pilot.charP_two_of_natCard_eq_two_pow (f := 1) (by rw [hK]; rfl)
  rw [← E6Pilot.range_rootSL2_highRoot] at hxJ
  obtain ⟨A, rfl⟩ := hxJ
  have hA : orderOf A = 3 := by
    rw [← hx, orderOf_injective _ E6Pilot.rootSL2_highRoot_injective]
  obtain ⟨P, l, hl, hP⟩ := exists_inv_mul_map_mul_eq_HSL_of_card_two hK hK₂ ι hA
  refine ⟨rootSL2 .E8 K₂ (highRoot .E8) P, E6Pilot.rootSL2_highRoot_mem_highRootSL2 P, l, hl, ?_⟩
  rw [E6Pilot.baseChangeGL_rootSL2_highRoot, ← map_inv, ← map_mul, ← map_mul, hP,
    E6Pilot.rootSL2_highRoot_HSL (Or.inr (Or.inr rfl))]

theorem le_rootSpan_perpRoots_of_perfect_of_le_centralizer [Finite K] [Finite K₂] [CharP K₂ 2]
    (hK : Nat.card K = 2) (hK₂ : Nat.card K₂ = 2 ^ 2) (ι : K →+* K₂) {x : ModGL .E8 K}
    (hxJ : x ∈ EPilot.highRootSL2 .E8 K) (hx : orderOf x = 3) {Q : Subgroup (ModGL .E8 K₂)}
    (hQ : ⁅Q, Q⁆ = Q) (hQC : Q ≤ adjointGroup .E8 K₂)
    (hQx : Q ≤ centralizer ({baseChangeGL ι x} : Set (ModGL .E8 K₂))) :
    Q ≤ rootSpan .E8 K₂ (EPilot.perpRoots .E8) := by
  obtain ⟨n, hnJ, l, hl, hn⟩ := exists_conj_baseChangeGL_eq_highDiag_of_card_two hK hK₂ ι hxJ hx
  obtain ⟨hl1, hl2⟩ := F4Pilot.ne_one_and_sq_ne_one_of_three_le_orderOf hl
  have hnC : n ∈ adjointGroup .E8 K₂ := EPilot.highRootSL2_le_adjointGroup hnJ
  set Q' := Q.map (MulAut.conj n⁻¹).toMonoidHom with hQ'
  have hQ'le : Q' ≤ torusGroup .E8 K₂ ⊔ rootSpan .E8 K₂ (EPilot.perpRoots .E8) := by
    rw [← EPilot.toralCentralizer_highDiag (Or.inr (Or.inr rfl)) hl1 hl2]
    rintro _ ⟨q, hq, rfl⟩
    have hqx : q * baseChangeGL ι x = baseChangeGL ι x * q :=
      mem_centralizer_singleton_iff.1 (hQx hq)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    refine mem_toralCentralizer.2 ⟨mul_mem (mul_mem (inv_mem hnC) (hQC hq)) hnC, ?_⟩
    rw [← hn]
    calc n⁻¹ * baseChangeGL ι x * n * (n⁻¹ * q * n) * (n⁻¹ * baseChangeGL ι x * n)⁻¹ =
        n⁻¹ * (baseChangeGL ι x * q) * (baseChangeGL ι x)⁻¹ * n := by group
      _ = n⁻¹ * q * n := by rw [← hqx]; group
  have hQ'perf : ⁅Q', Q'⁆ = Q' := by rw [hQ', ← map_commutator, hQ]
  have hQ'D : Q' ≤ rootSpan .E8 K₂ (EPilot.perpRoots .E8) := by
    rw [← hQ'perf]
    exact (Subgroup.commutator_mono hQ'le hQ'le).trans
      (F4Pilot.commutator_sup_le_of_comm_of_le_normalizer
        (fun x hx y hy => (triangular_borel_structure.{0, 0} .E8 K₂).1 x hx y hy)
        (torusGroup_le_normalizer_rootSpan fun α hα => hα.1))
  intro q hq
  have h1 : n⁻¹ * q * n ∈ rootSpan .E8 K₂ (EPilot.perpRoots .E8) :=
    hQ'D ⟨q, hq, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
  have h2 : n * (n⁻¹ * q * n) * n⁻¹ = n⁻¹ * q * n := by
    rw [E6Pilot.commute_of_mem_highRootSL2_of_mem_perpLevi (Or.inr (Or.inr rfl)) hnJ h1,
      mul_inv_cancel_right]
  have h3 : q = n⁻¹ * q * n := by
    rw [← h2]
    group
  rw [h3]
  exact h1

end Theta

section Weyl


variable {K : Type} [Field K] {K₂ : Type} [Field K₂]

theorem conj_wordElt_mem_rootSL2 {F : Type} [Field F] (ω : List (Fin (Tag.rank .E8)))
    {x : ModGL .E8 F} (hx : x ∈ EPilot.highRootSL2 .E8 F) :
    wordElt F ω * x * (wordElt F ω)⁻¹ ∈
      rootSubgroup .E8 F ((coxeterSystem .E8).wordProd ω • highRoot .E8) ⊔
        rootSubgroup .E8 F (-((coxeterSystem .E8).wordProd ω • highRoot .E8)) := by
  have h : (EPilot.highRootSL2 .E8 F).map (MulAut.conj (wordElt F ω)).toMonoidHom =
      rootSubgroup .E8 F ((coxeterSystem .E8).wordProd ω • highRoot .E8) ⊔
        rootSubgroup .E8 F (-((coxeterSystem .E8).wordProd ω • highRoot .E8)) := by
    rw [EPilot.highRootSL2, Subgroup.map_sup,
      map_conj_prod_weylElt_rootSubgroup F ω (isRoot_highRoot .E8),
      map_conj_prod_weylElt_rootSubgroup F ω (IsRoot.neg (isRoot_highRoot .E8)), smul_neg]
  rw [← h]
  exact ⟨x, hx, rfl⟩

theorem mem_centralizer_corootTuple_of_perfect_of_le_centralizer_word [Finite K] [Finite K₂]
    [CharP K₂ 2] (hK : Nat.card K = 2) (hK₂ : Nat.card K₂ = 2 ^ 2) (ι : K →+* K₂)
    {x : ModGL .E8 K} (hxJ : x ∈ EPilot.highRootSL2 .E8 K) (hx : orderOf x = 3)
    (ω : List (Fin (Tag.rank .E8))) {Q : Subgroup (ModGL .E8 K₂)} (hQ : ⁅Q, Q⁆ = Q)
    (hQC : Q ≤ adjointGroup .E8 K₂)
    (hQx : Q ≤ centralizer ({baseChangeGL ι (wordElt K ω * x * (wordElt K ω)⁻¹)} :
      Set (ModGL .E8 K₂)))
    {g : ModGL .E8 K₂} (hg : g ∈ Q) (c : K₂ˣ) :
    g ∈ centralizer ({(rootDiagUnit .E8
      (corootTuple ((coxeterSystem .E8).wordProd ω • highRoot .E8) c))} :
        Set (ModGL .E8 K₂)) := by
  set m := wordElt K₂ ω with hm
  have hmC : m ∈ adjointGroup .E8 K₂ := wordElt_mem_adjointGroup ω
  have hι : baseChangeGL ι (wordElt K ω * x * (wordElt K ω)⁻¹) = m * baseChangeGL ι x * m⁻¹ := by
    rw [map_mul, map_mul, map_inv, baseChangeGL_wordElt]
  set Q' := Q.map (MulAut.conj m⁻¹).toMonoidHom with hQ'
  have hQ'perf : ⁅Q', Q'⁆ = Q' := by rw [hQ', ← map_commutator, hQ]
  have hQ'C : Q' ≤ adjointGroup .E8 K₂ := by
    rintro _ ⟨q, hq, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact mul_mem (mul_mem (inv_mem hmC) (hQC hq)) hmC
  have hQ'x : Q' ≤ centralizer ({baseChangeGL ι x} : Set (ModGL .E8 K₂)) := by
    rintro _ ⟨q, hq, rfl⟩
    have hqx := mem_centralizer_singleton_iff.1 (hQx hq)
    rw [hι] at hqx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [mem_centralizer_singleton_iff]
    calc m⁻¹ * q * m * baseChangeGL ι x = m⁻¹ * (q * (m * baseChangeGL ι x * m⁻¹)) * m := by
          group
      _ = m⁻¹ * ((m * baseChangeGL ι x * m⁻¹) * q) * m := by rw [hqx]
      _ = baseChangeGL ι x * (m⁻¹ * q * m) := by group
  have hD := le_rootSpan_perpRoots_of_perfect_of_le_centralizer hK hK₂ ι hxJ hx hQ'perf hQ'C hQ'x
  have hgD : m⁻¹ * g * m ∈ rootSpan .E8 K₂ (EPilot.perpRoots .E8) :=
    hD ⟨g, hg, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
  have hcomm := (EPilot.commute_of_mem_highTorusLine_of_mem_rootSpan
    (EPilot.rootDiagUnit_highDiag_mem_highTorusLine c) hgD).eq
  have hconj : rootDiagUnit .E8 (corootTuple ((coxeterSystem .E8).wordProd ω • highRoot .E8) c) =
      m * rootDiagUnit .E8 (EPilot.highDiag .E8 c) * m⁻¹ := by
    rw [← list_prod_weylElt_conj_corootTuple, corootTuple_highRoot]
  rw [hconj, mem_centralizer_singleton_iff]
  set d := rootDiagUnit .E8 (EPilot.highDiag (K := K₂) .E8 c)
  calc g * (m * d * m⁻¹) = m * ((m⁻¹ * g * m) * d) * m⁻¹ := by group
    _ = m * (d * (m⁻¹ * g * m)) * m⁻¹ := by rw [hcomm]
    _ = m * d * m⁻¹ * g := by group

end Weyl

end CFSG.SeitzReduction.E8Pilot
