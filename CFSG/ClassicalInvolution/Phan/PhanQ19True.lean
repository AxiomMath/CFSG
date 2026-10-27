module

public import CFSG.ClassicalInvolution.Phan.PhanQ18Machinery
public import CFSG.ClassicalInvolution.Phan.PhanD13Final
public import CFSG.ClassicalInvolution.Phan.PhanP21Graph

public section

namespace CFSG.ClassicalInvolution.PhanQ

open SimpleGraph CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanD4
  CFSG.ClassicalInvolution.PhanG CFSG.ClassicalInvolution.PhanP
  CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem

section Facts

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {G : Type} [Group G]

structure PhanD4ShortCycleTrueFacts (S : PhanFamilyD4 K p f G) (h0 : PtStep0 S) : Prop where
  cone : ∀ (a b c : G ⧸ parab S {1, 2, 3}) (hab : (ptGraph S).Adj a b)
    (hbc : (ptGraph S).Adj b c) (hca : (ptGraph S).Adj c a),
    ∃ (e : G ⧸ parab S {1, 2, 3}) (hae : (ptGraph S).Adj a e) (hbe : (ptGraph S).Adj b e)
      (hce : (ptGraph S).Adj c e),
      SolidNull S h0 (.cons hab (.cons hbe (.cons hae.symm .nil)) : (ptGraph S).Walk a a) ∧
      SolidNull S h0 (.cons hbc (.cons hce (.cons hbe.symm .nil)) : (ptGraph S).Walk b b) ∧
      SolidNull S h0 (.cons hca (.cons hae (.cons hce.symm .nil)) : (ptGraph S).Walk c c)
  quad : QuadNull (ptGraph S)
  pent : ApexPentagon (G := ptGraph S)

variable (S : PhanFamilyD4 K p f G)

structure PhanD4PointGeometryTrue : Prop where
  step0 : PtStep0 S
  edge : PtEdge S
  connected : (ptGraph S).Connected
  ediam_le_two : (ptGraph S).ediam ≤ 2
  cone : ∀ (a b c : G ⧸ parab S {1, 2, 3}) (hab : (ptGraph S).Adj a b)
    (hbc : (ptGraph S).Adj b c) (hca : (ptGraph S).Adj c a),
    ∃ (e : G ⧸ parab S {1, 2, 3}) (hae : (ptGraph S).Adj a e) (hbe : (ptGraph S).Adj b e)
      (hce : (ptGraph S).Adj c e),
      SolidNull S step0 (.cons hab (.cons hbe (.cons hae.symm .nil)) : (ptGraph S).Walk a a) ∧
      SolidNull S step0 (.cons hbc (.cons hce (.cons hbe.symm .nil)) : (ptGraph S).Walk b b) ∧
      SolidNull S step0 (.cons hca (.cons hae (.cons hce.symm .nil)) : (ptGraph S).Walk c c)
  quad : QuadNull (ptGraph S)
  pent : ApexPentagon (G := ptGraph S)

variable {S}

theorem PhanD4PointGeometryTrue.connected_phanSystem (H : PhanD4PointGeometryTrue S) :
    (phanSystem S).Connected :=
  phanSystem_connected H.step0 H.connected

variable (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) (hg : GoodFamily S)
  (h2 : (2 : K) ≠ 0)

include hK hq hg h2 in
theorem PhanD4PointGeometryTrue.simplyTwoConnected_phanSystem (H : PhanD4PointGeometryTrue S) :
    (phanSystem S).SimplyTwoConnected := by
  let F := phanFib S H.step0
  have R := phanFib_rigid hK hq hg h2 H.step0 H.edge
  let E : ∀ x : G ⧸ parab S {1, 2, 3}, Set ((ptGraph S).Walk x x) :=
    fun _ => {c | F.FibreNull c}
  have hcone : ConeTriangles E := by
    intro a b c hab hbc hca
    obtain ⟨e, hae, hbe, hce, s₁, s₂, s₃⟩ := H.cone a b c hab hbc hca
    exact ⟨e, hae, hbe, hce,
      cycleHomotopic_of_mem E (fibreNull_of_solidNull hK hq hg h2 H.step0 H.edge s₁),
      cycleHomotopic_of_mem E (fibreNull_of_solidNull hK hq hg h2 H.step0 H.edge s₂),
      cycleHomotopic_of_mem E (fibreNull_of_solidNull hK hq hg h2 H.step0 H.edge s₃)⟩
  have htriv := cycleTrivial_of_cycles_le_five_true E H.connected H.ediam_le_two hcone H.quad
    H.pent
  intro x γ hγ hend
  refine R.twoHomotopic_nil (E := E) (fun _ _ hc => hc)
    (fun {e x'} _ hΓ => by
      obtain ⟨ρ, g, h1, h2', h3⟩ := phanFib_lift hΓ
      exact ⟨ρ, g, h1, h2', h3, trivial⟩) htriv (trivial : F.Q x)
    ⟨hγ, fun i _ => ?_⟩ hend
  fin_cases i <;> simp [phanFib]

end Facts

section Std

set_option linter.unusedSectionVars false

variable (p f : ℕ) [Fact p.Prime]

@[expose] def PhanD4ShortCycleTrue : Prop :=
  ∀ (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f),
    PhanD4ShortCycleTrueFacts (stdModel hp2 hq).S ((stdModel hp2 hq).ptStep0 hp2 hq)

variable {p f}

theorem phanD4Geometry_of_shortCycleTrue (H : PhanD4ShortCycleTrue p f) : PhanD4Geometry p f := by
  intro hp2 hq
  have hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := StdModel.card_K hq
  have h2 : (2 : GaloisField p (2 * f)) ≠ 0 := two_ne_zero_gf hp2 (2 * f)
  have hPG : PhanD4PointGeometryTrue (stdModel hp2 hq).S :=
    ⟨(stdModel hp2 hq).ptStep0 hp2 hq, (stdModel hp2 hq).ptEdge hp2 hq,
      (stdModel hp2 hq).connected hp2 hq, (stdModel hp2 hq).ediam_le_two hp2 hq,
      (H hp2 hq).cone, (H hp2 hq).quad, (H hp2 hq).pent⟩
  exact ⟨(stdModel hp2 hq).S, (stdModel hp2 hq).good, (stdModel hp2 hq).fund,
    hPG.connected_phanSystem, hPG.simplyTwoConnected_phanSystem hK hq (stdModel hp2 hq).good h2⟩

end Std

end CFSG.ClassicalInvolution.PhanQ
