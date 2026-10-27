module

public import CFSG.ClassicalInvolution.Phan.PhanS6Iso
public import CFSG.ClassicalInvolution.Phan.PhanS3Glue
public import CFSG.ClassicalInvolution.Phan.PhanS4Std

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open SimpleGraph CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanB3.H
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin

section Dict

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {hK : Nat.card K = (p ^ f) ^ 2} {F : Type} [Field F] {h2 : (2 : F) ≠ 0}
  {C : B2Coord hK F h2} {G : Type} [Group G] {K' : Type} [Field K']

variable (M : Std.Model K') (S : PhanFamilyB3 C G)

structure PhanB3Dict where
  step0 : PtStep0 S
  edge : PtEdge S
  iso : ptGraph S ≃g Std.ffGraph M
  geom : ∀ (x y z : G ⧸ parab S {1, 2}) (hxy : (ptGraph S).Adj x y) (hyz : (ptGraph S).Adj y z)
    (hzx : (ptGraph S).Adj z x), Std.GeomPt M (iso x) (iso y) (iso z) →
      Null2 S step0 (.cons hxy (.cons hyz (.cons hzx .nil)))

variable {M S}

theorem PhanB3Dict.pointGeometry (D : PhanB3Dict M S) (hd : Std.DiamTwo M) (ht : Std.TriNull M)
    (hq : Std.QuadNullStd M) (hp : Std.PentNullStd M) : PhanB3PointGeometry S where
  step0 := D.step0
  edge := D.edge
  connected := D.iso.connected_iff.2 hd.1
  ediam_le_two := ediam_le_two_of_iso D.iso hd.1 hd.2
  tri := fun a b c hab hbc hca => by
    refine cycleHomotopic_of_iso D.iso (E' := Std.geomWalks M) ?_ ?_
    · intro y w hw
      obtain ⟨y₂, z, h₁, h₂, h₃, rfl, hg⟩ := hw
      refine cycleHomotopic_of_mem _ ?_
      have := D.geom (D.iso.symm y) (D.iso.symm y₂) (D.iso.symm z)
        (D.iso.symm.toHom.map_adj h₁) (D.iso.symm.toHom.map_adj h₂)
        (D.iso.symm.toHom.map_adj h₃) (by simpa only [RelIso.apply_symm_apply] using hg)
      exact this
    · exact ht _ _ _ _ _ _
  quad := quadNull_of_iso D.iso hq
  pent := pentNull_of_iso D.iso hp

end Dict

section Standard

variable {p f : ℕ} [Fact p.Prime]

@[expose] def PhanB3StdDict (p f : ℕ) [Fact p.Prime] : Prop :=
  p ≠ 2 → 5 ≤ p ^ f → p ^ f % 4 = 3 →
    ∀ (hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2) (h2 : (2 : GaloisField p f) ≠ 0)
      (C : B2Coord hK (GaloisField p f) h2) (M : ModelB3 p f h2)
      (E : PhanFamilyB3 C (spinGroup (quadOdd 3 (GaloisField p f)))),
      GoodFamily E → (∀ i, (E.ι i).range = M.U i) →
      ∃ SM : Std.Model (GaloisField p (2 * f)), SM.q = p ^ f ∧ Nonempty (PhanB3Dict SM E)

@[expose] def StdGeometryFacts : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (M : Std.Model K), 5 ≤ M.q → M.q % 4 = 3 →
    Std.DiamTwo M ∧ Std.TriNull M ∧ Std.QuadNullStd M ∧ Std.PentNullStd M

theorem phanB3StdPointGeometry_of_dict (hd : PhanB3StdDict p f) (hg : StdGeometryFacts) :
    PhanB3StdPointGeometry p f := by
  intro hp2 hq hmod hK h2 C M E hgood hrange
  obtain ⟨SM, hSMq, ⟨D⟩⟩ := hd hp2 hq hmod hK h2 C M E hgood hrange
  obtain ⟨h1, h2', h3, h4⟩ := hg _ SM (by rw [hSMq]; exact hq) (by rw [hSMq]; exact hmod)
  exact D.pointGeometry h1 h2' h3 h4

theorem phanB3Std_of_dict (hd : PhanB3StdDict p f) (hg : StdGeometryFacts) :
    PhanB3StdSimplyTwoConnected p f :=
  phanB3Std_of_pointGeometry (phanB3StdPointGeometry_of_dict hd hg)

end Standard

end CFSG.ClassicalInvolution.PhanB3.S
