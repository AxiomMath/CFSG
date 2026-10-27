module

public import CFSG.ClassicalInvolution.Q3.Q3TLKGlobal
public import CFSG.ClassicalInvolution.Q3.Q3TLKLink
public import CFSG.ClassicalInvolution.Q3.Q3TLKMF
public import CFSG.ClassicalInvolution.Q3.Q3TLKOdd
public import CFSG.ClassicalInvolution.Q3.Q3TIVFinal

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TLK

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TY CFSG.ClassicalInvolution.Q3.Q3TIV CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.RouteD.TwinY (IsTwinAt TwinElt TwinElt.u TwinRow twinYModel)
open CFSG.ClassicalInvolution.Generic.CoreAssembly (LinkedAtProduct)
open CFSG.ClassicalInvolution.Q3 (CompData IsClassicalMember3)
open CFSG.Open (classicalInvolutionOddCore)


@[expose] def TwinLinked3At (t : StatedLieTag) (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteD3Setup K z →
      LocalShapeC3 2 (CompData.model t n) (conjClass3 K) z →
      ∀ K₂ ∈ centralizingMembers (conjClass3 K) {z}, K₂ ≠ K →
        (∀ T : Subgroup G, IsTwinAt (conjClass3 K) K T z → K₂ ≠ T) →
        ∀ w : G, IsClassicalMember3 K₂ w → LinkedAtProduct (conjClass3 K) K z w

theorem twinLinked3_of_rows (hsp : TwinLinked3At .PSp 2) (hsu : TwinLinked3At .PSU 4) :
    Q3TY.TwinLinked3 := by
  intro G _ _ _ hnab K z hR t n htn hshape K₂ hK₂ hK₂K hK₂T w hw
  rcases htn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hsp G hnab K z hR hshape K₂ hK₂ hK₂K hK₂T w hw
  · exact hsu G hnab K z hR hshape K₂ hK₂ hK₂K hK₂T w hw

theorem TCtxS3.isTwinAt3 {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}
    {tY : StatedLieTag} {nY : ℕ} {K : Subgroup G} (c : Q3TP.TCtxS3 tY nY Ω K z)
    {T : Subgroup G} (hT : T ∈ centralizingMembers Ω {z}) (hTQ : locImg Ω z T ≤ c.d.Q₁) :
    IsTwinAt Ω K T z where
  mem := hT
  ne := c.twin_ne hT hTQ
  comm_T := fun _ hN hNT => c.commutes_T_of_ne hT hTQ hN hNT
  comm_K := fun _ hN hNK => c.commutes_K_of_ne hN hNK

theorem twinLinked3_sp4 (h3 : OddThreeFreeInput) (hP : CommutingProductP1Input3)
    (hY2 : TwinYType3On (fun t n => t = .PSp ∧ n = 2)) : TwinLinked3At .PSp 2 := by
  intro G _ _ _ hnab K z hR hshape K₂ hK₂ hK₂K hK₂T w hw
  classical
  have hrow : TwinRow .PSp 2 := Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))
  have hΩ : InClass3 (conjClass3 K) := hR.inClass
  obtain ⟨hex, -⟩ := hR.setup
  have hKΩ : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  obtain ⟨c⟩ := Q3TP.nonempty_tctxS3 Q3TP.yData3S_psp2 h3 hR hshape
  obtain ⟨T, hTz, hTQ⟩ := c.exists_twin
  have hT : IsTwinAt (conjClass3 K) K T z := TCtxS3.isTwinAt3 c hTz hTQ.le
  have hclsT : IsClassicalMember3 T z :=
    Q3TIV.twinInvolution3_of_odd3 h3 G hnab K z hR .PSp 2 hrow hshape T hT
  have hKT : Commutes K T := hT.comm_K T hT.mem hT.ne
  have hTΩ : T ∈ conjClass3 K := hT.mem.1
  obtain ⟨e⟩ := exists_twinElt3 hR.cls hclsT (hex K hKΩ) (hex T hTΩ)
  obtain ⟨hP1u, hO3u⟩ := hP G K z hR T hTΩ hKT e.u e.u_mem_sup
    (twinElt_orderOf_u3 e hR.cls (hex K hKΩ) hKT)
    (twinElt_u_not_mem_left3 e hR.cls (hex K hKΩ) hKT)
    (twinElt_u_not_mem_right3 e hclsT (hex T hTΩ) hKT)
  obtain ⟨ι, hι, D, hcard, i, hkind, -⟩ := hY2 G hnab K z hR .PSp 2 hrow ⟨rfl, rfl⟩ hshape T hT
    hclsT e hP1u hO3u
  have hkind' : D.kind i = CompData.model .POmegaOdd 3 := hkind
  have hone : ∀ j : ι, j = i := by
    have h1 : Nat.card ι = 1 := hcard
    have : Subsingleton ι := (Nat.card_eq_one_iff_unique.mp h1).1
    exact fun j => Subsingleton.elim j i
  have hadm : StatedLieAdmissible .POmegaOdd 3 3 1 :=
    ⟨Nat.prime_three, le_rfl, le_rfl, by norm_num⟩
  have hnc : ∀ R ∈ (D.kind i).fund, ∀ r ∈ R, r ∈ Subgroup.center (D.kind i).G → r = 1 := by
    rw [hkind']
    exact fundNoncentral_model3 trivial hadm (by decide)
  have hmodel : SqTrichotomyC (D.kind i) := by
    rw [hkind']
    exact sqTrichotomyC_of_on sqTrichotomy3_odd
  exact linked_of_model3 hR hT hclsT e hP1u hO3u D i hone hnc hmodel
    (exists_twin_frame3 h3 hnab hR hrow hshape hT hclsT)
    (fun hZ => false_of_layer_le_centralizer3 h3 hnab hR hrow hshape hT hclsT e
      twinMFGenerationOn3_psp2 hZ)
    (fun J t hJ hJK hJT hJiso hZt =>
      false_of_layer_le_centralizer_tz3 h3 hR hrow hshape hT e hJ hJK hJT hJiso hZt)
    hK₂ hK₂K (hK₂T T hT) hw

end CFSG.ClassicalInvolution.Q3.Q3TLK
