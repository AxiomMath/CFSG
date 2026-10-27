module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.J4ElevenPlane
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.PlaneNoSig
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Out1SlimEquiv
public import CFSG.RankThree.PartOne.KS.AllInner
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.J4ElevenData
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Witness
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
  CFSG.Sporadic.SmallOddCore CFSG.EvenSporadicStandard.Solomon78 CFSG.RankThree.PartTwo.Sec4
  CFSG.HardMathSupport.Timmesfeld.Tables.Census CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.Blueprint
open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Top

@[irreducible] noncomputable def J4T : Subgroup ↥J := ⊤

theorem J4T_eq_top : J4T = ⊤ := by unfold J4T; rfl

theorem mem_J4T (g : ↥J) : g ∈ J4T := by rw [J4T_eq_top]; exact Subgroup.mem_top g

noncomputable def eJ4T : ↥J ≃* ↥J4T where
  toFun g := ⟨g, mem_J4T g⟩
  invFun x := x.1
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem card_J4T : Nat.card J4T = Nat.card ↥J := by rw [J4T_eq_top, Subgroup.card_top]

end Top

section Final


theorem center_J4T : Subgroup.center ↥J4T = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have : z.1 ∈ Subgroup.center ↥J := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h := congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨g, mem_J4T g⟩)
    rw [Subgroup.coe_mul, Subgroup.coe_mul] at h
    exact h
  rw [center_J, Subgroup.mem_bot] at this
  exact Subtype.ext this

theorem j4_autModel_J4T (hAut : ∀ α : MulAut ↥J, ∃ g : ↥J, α = MulAut.conj g) :
    AutModel J4T J4T := by
  have hall : AllInner ↥J := hAut
  have hall' : AllInner ↥J4T :=
    @AllInner.of_mulEquiv ↥J ↥J4T (Subgroup.toGroup J) (Subgroup.toGroup J4T) eJ4T hall
  exact CFSG.RankThree.PartOne.autModel_self_of_allInner center_J4T hall'

theorem j4_sylow_J4T : ∃ S : Sylow 11 ↥J4T, (S : Subgroup ↥J4T) = Q11.subgroupOf J4T := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hle : Q11 ≤ J4T := by rw [J4T_eq_top]; exact le_top
  have hQ : Nat.card Q11 = 11 ^ (Nat.card J4T).factorization 11 := by
    rw [card_J4T]; exact card_Q11_sylow
  exact ⟨Sylow.ofCard (Q11.subgroupOf J4T)
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]; exact hQ), rfl⟩

theorem j4_pfree_J4T (E : Subgroup ↥J) (hEQ : E ≤ Q11) (hEel : IsElemAbelian 11 E)
    (hE : Nat.card E = 11 ^ 2) :
    PFree 11 (J4T ⊓ Subgroup.centralizer (E : Set ↥J) : Subgroup ↥J) := by
  intro u hu hcop
  have hEc : ∀ e ∈ E, u * e = e * u := fun e he =>
    (Subgroup.mem_centralizer_iff.1 hu.2 e he).symm
  exact @plane_centralizer_trivial ↥J (Subgroup.toGroup J) _ Q11 E qz card_Q11 qz_mem orderOf_qz
    (fun q hq => qz_commute_of_mem hq) Q11_commutator_mem_zpowers Q11_mem_zpowers_of_central
    centralizer_qz_le_normalizer_J4 centralizer_Q11_le (fun q hq => pow_eleven_of_mem hq) hEQ hEel hE
    u hEc hcop

theorem j4_rankOK_J4T (y : ↥J) (hy : orderOf y = 11) :
    RankOK 11 (J4T ⊓ Subgroup.centralizer ({y} : Set ↥J) : Subgroup ↥J) := by
  rw [J4T_eq_top, top_inf_eq]
  exact j4_rankOK_cen hy

theorem j4Eleven_noSig (hAut : ∀ α : MulAut ↥J, ∃ g : ↥J, α = MulAut.conj g) :
    PlaneNoSig 11 ↥J4T :=
  noSig_planes_of_autModel_rank (j4_autModel_J4T hAut)
    (by rw [card_J4T]; exact Nat.le_mul_of_pos_left _ (by norm_num)) (by norm_num) (by norm_num)
    (Q := Q11) j4_sylow_J4T (fun E hEQ hEel hE => j4_pfree_J4T E hEQ hEel hE)
    (fun y _ hy => j4_rankOK_J4T y hy)

end Final

end CFSG.HardMathSupport.Dickson.I271
