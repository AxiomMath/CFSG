module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1OmCFrame
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1OmTransport
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Parts
public import CFSG.LocalAnalysis.GLTheoremA.S10.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S11.Defs
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.I145GW
public import CFSG.LocalAnalysis.GLTheoremA.S4S.KData
public import CFSG.LocalAnalysis.GLTheoremA.S9.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.Milestones.CL_LIT_Gorenstein_Walter_L_balance

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.S172B.Rank

open QuadraticMap Module CFSG.Open CFSG.RankThree.Classical2
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

@[expose] noncomputable def rotOrthDerived (Q : QuadraticForm (ZMod 2) V) {a b : V}
    (h : MinusPair Q a b) : ↥(orthDerived Q) :=
  ⟨rot Q a b, rot_mem_commutator h⟩

theorem isFrame_ofFn {m : ℕ} {a b : Fin m → V} (hp : ∀ i, MinusPair Q (a i) (b i))
    (hperp : ∀ i j, i ≠ j → PairPerp Q (a i, b i) (a j, b j)) :
    IsFrame Q (List.ofFn fun i => (a i, b i)) := by
  refine ⟨?_, ?_⟩
  · intro p hp'
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hp'
    exact hp i
  · rw [List.pairwise_ofFn]
    intro i j hij
    exact hperp i j hij.ne

theorem isElemAbelian_card_closure_rotOrthDerived [FiniteDimensional (ZMod 2) V] {m : ℕ}
    {a b : Fin m → V} (hp : ∀ i, MinusPair Q (a i) (b i))
    (hperp : ∀ i j, i ≠ j → PairPerp Q (a i, b i) (a j, b j)) :
    IsElemAbelian 3 (Subgroup.closure (Set.range fun i => rotOrthDerived Q (hp i))) ∧
      Nat.card (Subgroup.closure (Set.range fun i => rotOrthDerived Q (hp i))) = 3 ^ m := by
  haveI : Finite V := Module.finite_of_finite (ZMod 2)
  have hl : IsFrame Q (List.ofFn fun i => (a i, b i)) := isFrame_ofFn hp hperp
  have himage : (orthDerived Q).subtype '' Set.range (fun i => rotOrthDerived Q (hp i)) =
      rotSet Q (List.ofFn fun i => (a i, b i)) := by
    ext g
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨(a i, b i), List.mem_ofFn.2 ⟨i, rfl⟩, rfl⟩
    · rintro ⟨p, hp', rfl⟩
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hp'
      exact ⟨_, ⟨i, rfl⟩, rfl⟩
  have hmap : (Subgroup.closure (Set.range fun i => rotOrthDerived Q (hp i))).map
      (orthDerived Q).subtype = torus Q (List.ofFn fun i => (a i, b i)) := by
    rw [MonoidHom.map_closure, himage, torus]
  refine ⟨CFSG.LocalAnalysis.GLTheoremA.KD264Lie.om_isElemAbelian_of_map_injective
    (orthDerived Q).subtype (orthDerived Q).subtype_injective (hmap ▸ torus_isElemAbelian hl), ?_⟩
  rw [← Subgroup.card_map_of_injective (orthDerived Q).subtype_injective, hmap, card_torus hl,
    List.length_ofFn]

end CFSG.LocalAnalysis.GLTheoremA.S172B.Rank

end
