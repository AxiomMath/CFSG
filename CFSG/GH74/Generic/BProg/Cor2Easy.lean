module

public import CFSG.GH74.Generic.BProg.Stage2Defs
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.Generic.BProg

open Subgroup

theorem cor2_a {G : Type} [Group G] {M : Subgroup G} (h2 : Stage2Concl2 M) (X B : Subgroup G)
    (hXM : X ≤ M) (hB : InU0 M B) (hBX : B ≤ X) : normalizer (X : Set G) ≤ M := by
  intro g hg
  refine h2 B hB g ?_
  rintro _ ⟨b, hb, rfl⟩
  refine hXM ?_
  have hb' := (mem_normalizer_iff''.1 hg b).1 (hBX hb)
  simpa [MulAut.conj_apply] using hb'

theorem cor2_b {G : Type} [Group G] {M : Subgroup G} (h2 : Stage2Concl2 M) (X B : Subgroup G)
    (hB : InU0 M B) (hsub : (B.subgroupOf X).IsSubnormal) (hBX : B ≤ X) : X ≤ M := by
  have key : ∀ H : Subgroup ↥X, H.IsSubnormal → B ≤ H.map X.subtype → H.map X.subtype ≤ M →
      X ≤ M := by
    intro H hH
    induction hH with
    | top =>
      intro _ hM
      simpa [Subgroup.map_top, Subgroup.range_subtype] using hM
    | step H K h_le _ hN ih =>
      intro hBH hHM
      refine ih (hBH.trans (Subgroup.map_mono h_le)) ?_
      have hKN : K ≤ normalizer (H : Set ↥X) := (normal_subgroupOf_iff_le_normalizer h_le).1 hN
      calc K.map X.subtype ≤ (normalizer (H : Set ↥X)).map X.subtype := Subgroup.map_mono hKN
        _ ≤ normalizer ((H.map X.subtype : Subgroup G) : Set G) := Subgroup.le_normalizer_map _
        _ ≤ M := cor2_a h2 _ B hHM hB hBH
  have hmap : (B.subgroupOf X).map X.subtype = B := Subgroup.map_subgroupOf_eq_of_le hBX
  exact key _ hsub hmap.ge (hmap.le.trans hB.1.1)

theorem cor2_c {G : Type} [Group G] [Finite G] {M : Subgroup G} (h2 : Stage2Concl2 M)
    (X B : Subgroup G) (hX : IsPGroup 2 ↥X) (hB : InU0 M B) (hBX : B ≤ X) : X ≤ M :=
  cor2_b h2 X B hB (CFSG.BaerSuzuki.Helpers.subgroup_isSubnormal_of_isPGroup hX _) hBX

end CFSG.GH74.Generic.BProg
