module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.HardMathSupport.Lang.TwE6Step3.PlaneConj
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.HeisTorusU87Arith
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups
public import CFSG.RankThree.PartOne.KE6.E8T3Stab
public import CFSG.RankThree.PartOne.KE6.Tw6Transport
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import Certificates.Data.ExceptionalSL3

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6

open CFSG.Open CFSG.SectionRank CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.E6 CFSG.RankThree.Lattice CFSG.HardMathSupport.Lang.TwE6Step3
  CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups Pointwise

section SLTorus

variable {Ω : Type} [Field Ω]

noncomputable def diagSUSL (a b : Ωˣ) : Matrix.SpecialLinearGroup (Fin 3) Ω :=
  ⟨Matrix.diagonal ![((a : Ω)), ((b : Ω)), (((a : Ω) * (b : Ω))⁻¹)], by
    rw [Matrix.det_diagonal]
    have hU : (∏ i : Fin 3, (![a, b, (a * b)⁻¹] : Fin 3 → Ωˣ) i) = 1 := by
      rw [Fin.prod_univ_three]
      simp [mul_inv_cancel]
    have hcoe : (∏ i : Fin 3, ![((a : Ω)), ((b : Ω)), (((a : Ω) * (b : Ω))⁻¹)] i)
        = ↑(∏ i : Fin 3, (![a, b, (a * b)⁻¹] : Fin 3 → Ωˣ) i) := by
      rw [Units.coe_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i <;> simp
    rw [hcoe, hU, Units.val_one]⟩

theorem diagSUSL_mul (a b a' b' : Ωˣ) :
    diagSUSL a b * diagSUSL a' b' = diagSUSL (a * a') (b * b') := by
  apply Subtype.ext
  show Matrix.diagonal ![((a : Ω)), ((b : Ω)), (((a : Ω) * (b : Ω))⁻¹)] *
      Matrix.diagonal ![((a' : Ω)), ((b' : Ω)), (((a' : Ω) * (b' : Ω))⁻¹)] =
    Matrix.diagonal ![(((a * a' : Ωˣ) : Ω)), (((b * b' : Ωˣ) : Ω)),
      ((((a * a' : Ωˣ) : Ω) * ((b * b' : Ωˣ) : Ω))⁻¹)]
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;>
    simp [Pi.mul_apply, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm]

theorem diagSUSL_one : diagSUSL (1 : Ωˣ) 1 = 1 := by
  apply Subtype.ext
  show Matrix.diagonal ![((1 : Ω)), ((1 : Ω)), (((1 : Ω) * (1 : Ω))⁻¹)] = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp

noncomputable def diagSUSLHom : (Ωˣ × Ωˣ) →* Matrix.SpecialLinearGroup (Fin 3) Ω where
  toFun p := diagSUSL p.1 p.2
  map_one' := diagSUSL_one
  map_mul' p q := (diagSUSL_mul p.1 p.2 q.1 q.2).symm

theorem diagSUSL_injective : Function.Injective (fun p : Ωˣ × Ωˣ => diagSUSL p.1 p.2) := by
  intro p q hpq
  have h := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) Ω =>
    (g : Matrix (Fin 3) (Fin 3) Ω)) hpq
  have h0 := congrFun (congrFun h 0) 0
  have h1 := congrFun (congrFun h 1) 1
  simp only [diagSUSL, Matrix.diagonal_apply_eq, Matrix.cons_val_zero,
    Matrix.cons_val_one] at h0 h1
  exact Prod.ext (Units.ext h0) (Units.ext h1)

noncomputable def qTorusSL (q q₀ : ℕ) : Subgroup (Matrix.SpecialLinearGroup (Fin 3) Ω) :=
  ((rootsOfUnity q Ω).prod (rootsOfUnity q Ω)).map (diagSUSLHom (Ω := Ω))

theorem card_qTorusSL {q q₀ : ℕ} [Fact q.Prime] {ζ : Ω} (hζ : IsPrimitiveRoot ζ q) :
    Nat.card (qTorusSL (Ω := Ω) q q₀) = q ^ 2 := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hinj : Function.Injective (diagSUSLHom (Ω := Ω)) := by
    intro a b hab
    exact diagSUSL_injective hab
  rw [qTorusSL, Subgroup.card_map_of_injective (f := diagSUSLHom (Ω := Ω)) hinj]
  rw [(Nat.card_congr (Subgroup.prodEquiv (rootsOfUnity q Ω) (rootsOfUnity q Ω)).toEquiv).trans
    (Nat.card_prod _ _), hζ.card_rootsOfUnity, pow_two]

theorem isElemAbelian_qTorusSL (q q₀ : ℕ) :
    IsElemAbelian q (qTorusSL (Ω := Ω) q q₀) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨p, hp, hp'⟩ := Subgroup.mem_map.1 a.2
    obtain ⟨r, hr, hr'⟩ := Subgroup.mem_map.1 b.2
    apply Subtype.ext
    change a.1 * b.1 = b.1 * a.1
    rw [← hp', ← hr', ← map_mul, ← map_mul, mul_comm p r]
  · obtain ⟨p, hp, hp'⟩ := Subgroup.mem_map.1 hx
    obtain ⟨ha, hb⟩ := hp
    have hap : (p.1 : Ωˣ) ^ q = 1 := (mem_rootsOfUnity q p.1).mp ha
    have hbp : (p.2 : Ωˣ) ^ q = 1 := (mem_rootsOfUnity q p.2).mp hb
    rw [← hp']
    rw [show diagSUSLHom p ^ q = diagSUSLHom (p ^ q) from (map_pow diagSUSLHom p q).symm]
    have hp1 : p ^ q = 1 := by
      refine Prod.ext ?_ ?_
      · simpa using hap
      · simpa using hbp
    rw [hp1, map_one]

private theorem diagSUSL_entry_pow {q q₀ : ℕ} (hqd : q ∣ q₀ + 1) {a b : Ωˣ}
    (ha : a ∈ rootsOfUnity q Ω) (hb : b ∈ rootsOfUnity q Ω) :
    ∀ i : Fin 3, ![((a : Ω)), ((b : Ω)), (((a : Ω) * (b : Ω))⁻¹)] i ^ (q₀ + 1) = 1 := by
  obtain ⟨m, hm⟩ := hqd
  have haq : (a : Ω) ^ q = 1 := by
    have := (mem_rootsOfUnity q a).mp ha
    simpa using congrArg (fun z : Ωˣ => (z : Ω)) this
  have hbq : (b : Ω) ^ q = 1 := by
    have := (mem_rootsOfUnity q b).mp hb
    simpa using congrArg (fun z : Ωˣ => (z : Ω)) this
  intro i
  fin_cases i
  · simp [hm, pow_mul, haq]
  · simp [hm, pow_mul, hbq]
  · simp [hm, pow_mul, mul_pow, haq, hbq]

private theorem diagSUSL_prod {q₀ : ℕ} {a b : Ωˣ} :
    ∏ i : Fin 3, ![((a : Ω)), ((b : Ω)), (((a : Ω) * (b : Ω))⁻¹)] i = 1 := by
  have hU : (∏ i : Fin 3, (![a, b, (a * b)⁻¹] : Fin 3 → Ωˣ) i) = 1 := by
    rw [Fin.prod_univ_three]
    simp [mul_inv_cancel]
  have hcoe : (∏ i : Fin 3, ![((a : Ω)), ((b : Ω)), (((a : Ω) * (b : Ω))⁻¹)] i)
      = ↑(∏ i : Fin 3, (![a, b, (a * b)⁻¹] : Fin 3 → Ωˣ) i) := by
    rw [Units.coe_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    fin_cases i <;> simp
  rw [hcoe, hU, Units.val_one]

theorem qTorusSL_toGL_mem_unitarySet {q q₀ : ℕ} (hq1 : 1 ≤ q₀) (hqd : q ∣ q₀ + 1) :
    ∀ X ∈ qTorusSL (Ω := Ω) q q₀, Matrix.SpecialLinearGroup.toGL X ∈ unitarySet q₀ 3 := by
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨ha, hb⟩ := hp
  change Matrix.SpecialLinearGroup.toGL (diagSUSL p.1 p.2) ∈ unitarySet q₀ 3
  have hd := diagSUSL_entry_pow (Ω := Ω) hqd ha hb
  have hprod := diagSUSL_prod (Ω := Ω) (q₀ := q₀) (a := p.1) (b := p.2)
  have hdet : IsUnit (Matrix.diagonal
      ![((p.1 : Ω)), ((p.2 : Ω)), (((p.1 : Ω) * (p.2 : Ω))⁻¹)]).det := by
    rw [Matrix.det_diagonal, hprod]
    exact isUnit_one
  have hmem := diagonal_mem_unitary (Ω := Ω) (q := q₀) (n := 3) hq1 hd hprod hdet
  have heq : Matrix.SpecialLinearGroup.toGL (diagSUSL p.1 p.2) =
      Matrix.nonsingInvUnit (Matrix.diagonal
        ![((p.1 : Ω)), ((p.2 : Ω)), (((p.1 : Ω) * (p.2 : Ω))⁻¹)]) hdet := by
    apply Units.ext
    rfl
  rw [heq]
  exact hmem

end SLTorus

section Transport

variable {Ω : Type} [Field Ω]

theorem exists_qTorus_in_layer {q q₀ : ℕ} [Fact q.Prime] {ζ : Ω} (hζ : IsPrimitiveRoot ζ q)
    (hq1 : 1 ≤ q₀) (hqd : q ∣ q₀ + 1)
    {Φ : Matrix.SpecialLinearGroup (Fin 3) Ω ≃*
      Matrix.SpecialLinearGroup (Fin 3) Ω}
    {H : Matrix.SpecialLinearGroup (Fin 3) Ω}
    (hchar : ∀ X : Matrix.SpecialLinearGroup (Fin 3) Ω, X ∈ fixSubgroup Φ ↔
      ∃ Y ∈ unitarySet q₀ 3,
        Matrix.SpecialLinearGroup.toGL X =
          Matrix.SpecialLinearGroup.toGL H * Y * (Matrix.SpecialLinearGroup.toGL H)⁻¹)
    {Fr : Ω →+* Ω} {S : Set (Fin Tag.E6.rank → ℤ)}
    (e : ↥(rootSpan Tag.E6 Ω S ⊓ (tw6Theta Ω Fr).eqLocus (MonoidHom.id _)) ≃*
      ↥(fixSubgroup Φ)) :
    ∃ T : Subgroup (ModGL Tag.E6 Ω),
      T ≤ rootSpan Tag.E6 Ω S ⊓ (tw6Theta Ω Fr).eqLocus (MonoidHom.id _) ∧
      IsElemAbelian q T ∧ Nat.card T = q ^ 2 := by
  classical
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  set T_SL : Subgroup (Matrix.SpecialLinearGroup (Fin 3) Ω) :=
    qTorusSL (Ω := Ω) q q₀ with hT_SL
  have hT_SL_card : Nat.card T_SL = q ^ 2 := card_qTorusSL hζ
  have hT_SL_el : IsElemAbelian q T_SL := isElemAbelian_qTorusSL q q₀
  set T_Φ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) Ω) :=
    T_SL.map (MulAut.conj H).toMonoidHom with hT_Φ
  have hT_Φ_le : T_Φ ≤ fixSubgroup Φ := by
    rintro _ ⟨Y, hY, rfl⟩
    change H * Y * H⁻¹ ∈ fixSubgroup Φ
    rw [hchar]
    refine ⟨Matrix.SpecialLinearGroup.toGL Y, qTorusSL_toGL_mem_unitarySet hq1 hqd Y hY, ?_⟩
    rw [map_mul, map_mul, map_inv]
  have hT_Φ_card : Nat.card T_Φ = q ^ 2 := by
    rw [hT_Φ, Subgroup.card_map_of_injective (MulAut.conj H).injective, hT_SL_card]
  have hT_Φ_el : IsElemAbelian q T_Φ :=
    CFSG.Open.IsElemAbelian.map hT_SL_el (MulAut.conj H).toMonoidHom
  set T_sub : Subgroup ↥(fixSubgroup Φ) :=
    T_Φ.subgroupOf (fixSubgroup Φ) with hT_sub
  have hT_sub_card : Nat.card T_sub = q ^ 2 := by
    have hmap : T_sub.map (fixSubgroup Φ).subtype = T_Φ :=
      Subgroup.map_subgroupOf_eq_of_le hT_Φ_le
    rw [← hT_Φ_card, ← hmap,
      Subgroup.card_map_of_injective (fixSubgroup Φ).subtype_injective]
  have hT_sub_el : IsElemAbelian q T_sub :=
    CFSG.Open.IsElemAbelian.subgroupOf hT_Φ_el (fixSubgroup Φ)
  set T_layer : Subgroup ↥(rootSpan Tag.E6 Ω S ⊓ (tw6Theta Ω Fr).eqLocus (MonoidHom.id _)) :=
    T_sub.map e.symm.toMonoidHom with hT_layer
  have hT_layer_card : Nat.card T_layer = q ^ 2 := by
    rw [hT_layer, Subgroup.card_map_of_injective e.symm.injective, hT_sub_card]
  have hT_layer_el : IsElemAbelian q T_layer :=
    CFSG.Open.IsElemAbelian.map hT_sub_el e.symm.toMonoidHom
  exact ⟨T_layer.map (rootSpan Tag.E6 Ω S ⊓
      (tw6Theta Ω Fr).eqLocus (MonoidHom.id _)).subtype,
    Subgroup.map_subtype_le _,
    CFSG.Open.IsElemAbelian.map hT_layer_el _,
    by rw [Subgroup.card_map_of_injective
      (rootSpan Tag.E6 Ω S ⊓ (tw6Theta Ω Fr).eqLocus (MonoidHom.id _)).subtype_injective,
      hT_layer_card]⟩

end Transport

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6
