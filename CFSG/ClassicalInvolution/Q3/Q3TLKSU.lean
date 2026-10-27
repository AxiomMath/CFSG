module

public import CFSG.ClassicalInvolution.Q3.Q3TLKSp
public import CFSG.ClassicalInvolution.Q3.Q3TLKD4On
public import CFSG.ClassicalInvolution.Q3.Q3Y2WireU
public import CFSG.ClassicalInvolution.Q3.Q3TY32
public import CFSG.ClassicalInvolution.RouteD.TypeULocal
public import CFSG.ClassicalInvolution.Q3.Q3TIVSm

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TLK

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3TY CFSG.ClassicalInvolution.Q3.Q3TIV
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.ClassicalInvolution.RouteD.TwinY (IsTwinAt TwinElt TwinElt.u TwinRow twinYModel
  TwinDatumOn TwinMFGenerationOn)
open CFSG.ClassicalInvolution.Generic.CoreAssembly (LinkedAtProduct)
open CFSG.ClassicalInvolution.Q3 (CompData IsClassicalMember3)
open scoped MatrixGroups


section Model

theorem admissible_psu4 : StatedLieAdmissible .PSU 4 3 1 :=
  ⟨Nat.prime_three, le_rfl, by norm_num, by decide⟩

theorem twinDatum_ne_psu4 {R R' : Subgroup (modelUniv .PSU 4 3 1 Nat.prime_three).K}
    {x x' : (modelUniv .PSU 4 3 1 Nat.prime_three).K}
    (hd : TwinDatumOn .PSU (modelUniv .PSU 4 3 1 Nat.prime_three) R R' x x') : x ≠ x' := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hadm := admissible_psu4
  have hodd : Odd (Nat.card (GaloisField 3 1)) := odd_gf3
  have hK : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 := by
    rw [GaloisField.card 3 (2 * 1) (by norm_num)]
    norm_num
  have h2 : (2 : GaloisField 3 (2 * 1)) ≠ 0 :=
    Models.two_ne_zero_of_charP_ne_two (K := GaloisField 3 (2 * 1)) (p := 3) hp2
  obtain ⟨φ, hφ⟩ := psu_model_equiv (p := 3) (f := 1) hp2 hadm
  obtain ⟨i, hi⟩ := (hφ R).mp hd.mem
  obtain ⟨i', hi'⟩ := (hφ R').mp hd.mem'
  obtain ⟨e₁⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups (p := 3) (t := .PSU)
    (n := 4) (by norm_num) trivial hadm (by decide) (by decide) hd.mem
  obtain ⟨e₂⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups (p := 3) (t := .PSU)
    (n := 4) (by norm_num) trivial hadm (by decide) (by decide) hd.mem'
  have hx : x = sl2Inv e₁ := eq_sl2Inv_of_central3 e₁ hd.hx hd.cx hd.nx
  have hx' : x' = sl2Inv e₂ := eq_sl2Inv_of_central3 e₂ hd.hx' hd.cx' hd.nx'
  have hord : ∀ {R₀ : Subgroup (modelUniv .PSU 4 3 1 Nat.prime_three).K}
      (eR : R₀ ≃* SL(2, GaloisField 3 1)), orderOf (φ (sl2Inv eR)) = 2 := by
    intro R₀ eR
    rw [MulEquiv.orderOf_eq φ]
    exact orderOf_eq_prime (by rw [pow_two]; exact sl2Inv_mul_self hodd eR)
      (sl2Inv_ne_one hodd eR)
  have hxi : φ x = i := hi.eq_of_orderOf_eq_two hK hp2 (Subgroup.mem_map_of_mem _ hd.hx)
    (by rw [hx]; exact hord e₁)
  have hxi' : φ x' = i' := hi'.eq_of_orderOf_eq_two hK hp2 (Subgroup.mem_map_of_mem _ hd.hx')
    (by rw [hx']; exact hord e₂)
  intro hxx
  apply hd.ne
  have hii : i = i' := by rw [← hxi, ← hxi', hxx]
  apply Subgroup.map_injective (f := φ.toMonoidHom) φ.injective
  rw [hi.eq_longRootGroupSU h2, hi'.eq_longRootGroupSU h2, hii]

theorem twinMFGenerationOn3_psu4 :
    TwinMFGenerationOn .PSU (modelUniv .PSU 4 3 1 Nat.prime_three) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact twinMFGenerationOn3_of_strong trivial admissible_psu4 (by decide) (by decide) (by decide)
    (Q3Y2.twinStrong3_psu_four admissible_psu4) fun hd => twinDatum_ne_psu4 hd

end Model

theorem twinLinked3_su4 (h3 : OddThreeFreeInput) (hP : CommutingProductP1Input3)
    (hY2 : TwinYType3On (fun t n => t = .PSU ∧ n = 4)) : TwinLinked3At .PSU 4 := by
  intro G _ _ _ hnab K z hR hshape K₂ hK₂ hK₂K hK₂T w hw
  classical
  have hrow : TwinRow .PSU 4 := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))))
  have hΩ : InClass3 (conjClass3 K) := hR.inClass
  obtain ⟨hex, -⟩ := hR.setup
  have hKΩ : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  obtain ⟨c⟩ := Q3TP.nonempty_tctxS3 Q3TY.yData3S_psu4 h3 hR hshape
  obtain ⟨T, hTz, hTQ⟩ := c.exists_twin
  have hT : IsTwinAt (conjClass3 K) K T z := TCtxS3.isTwinAt3 c hTz hTQ.le
  have hclsT : IsClassicalMember3 T z :=
    Q3TIV.twinInvolution3_of_odd3 h3 G hnab K z hR .PSU 4 hrow hshape T hT
  have hKT : Commutes K T := hT.comm_K T hT.mem hT.ne
  have hTΩ : T ∈ conjClass3 K := hT.mem.1
  obtain ⟨e⟩ := exists_twinElt3 hR.cls hclsT (hex K hKΩ) (hex T hTΩ)
  obtain ⟨hP1u, hO3u⟩ := hP G K z hR T hTΩ hKT e.u e.u_mem_sup
    (twinElt_orderOf_u3 e hR.cls (hex K hKΩ) hKT)
    (twinElt_u_not_mem_left3 e hR.cls (hex K hKΩ) hKT)
    (twinElt_u_not_mem_right3 e hclsT (hex T hTΩ) hKT)
  obtain ⟨ι, hι, D, hcard, i, hkind, -⟩ := hY2 G hnab K z hR .PSU 4 hrow ⟨rfl, rfl⟩ hshape T hT
    hclsT e hP1u hO3u
  have hmod : twinYModel 3 .PSU 4 = (.POmegaPlus, 4) := by simp [twinYModel]
  have hkind' : D.kind i = CompData.model .POmegaPlus 4 := by
    have h := hkind
    rw [hmod] at h
    exact h
  have hone : ∀ j : ι, j = i := by
    have h1 : Nat.card ι = 1 := hcard
    have : Subsingleton ι := (Nat.card_eq_one_iff_unique.mp h1).1
    exact fun j => Subsingleton.elim j i
  have hadm : StatedLieAdmissible .POmegaPlus 4 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl⟩
  have hnc : ∀ R ∈ (D.kind i).fund, ∀ r ∈ R, r ∈ Subgroup.center (D.kind i).G → r = 1 := by
    rw [hkind']
    exact fundNoncentral_model3 trivial hadm (by decide)
  have hmodel : SqTrichotomyC (D.kind i) := by
    rw [hkind']
    exact sqTrichotomyC_of_on sqTrichotomy3_plus4
  exact linked_of_model3 hR hT hclsT e hP1u hO3u D i hone hnc hmodel
    (exists_twin_frame3 h3 hnab hR hrow hshape hT hclsT)
    (fun hZ => false_of_layer_le_centralizer3 h3 hnab hR hrow hshape hT hclsT e
      twinMFGenerationOn3_psu4 hZ)
    (fun J t hJ hJK hJT hJiso hZt =>
      false_of_layer_le_centralizer_tz3 h3 hR hrow hshape hT e hJ hJK hJT hJiso hZt)
    hK₂ hK₂K (hK₂T T hT) hw

theorem twinLinked3_of_inputs (h3 : OddThreeFreeInput) (hP : CommutingProductP1Input3)
    (hY2sp : TwinYType3On (fun t n => t = .PSp ∧ n = 2))
    (hY2su : TwinYType3On (fun t n => t = .PSU ∧ n = 4)) : Q3TY.TwinLinked3 :=
  twinLinked3_of_rows (twinLinked3_sp4 h3 hP hY2sp) (twinLinked3_su4 h3 hP hY2su)

end CFSG.ClassicalInvolution.Q3.Q3TLK
