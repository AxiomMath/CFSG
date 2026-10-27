module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DClaim
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DFin

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance

theorem lemma62_of_inputs (i112 : Input11_2Ext) (iL3 : InputL3U3Facts) (iFR : InputFieldRecog)
    (iK : InputKType) (i183 : Input18_3_4) (h514 : Lemma514) (h515 : Lemma515) : Lemma62Stmt := by
  intro G _ _ m hS hC B hExt x hxB hx1 K hK
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hnotN, hnotL2⟩ := hcon
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hB1, b, L, A, hw⟩ := hExt.exists_witness
  have e : Env m B b L A := ⟨hS, hC, hB1, hw, exists_extCtx hS hC hB1 hw⟩
  set X := Subgroup.centralizer ({x} : Set G) with hX
  have hBX : B ≤ X := fun c hc => by
    rw [hX, Subgroup.mem_centralizer_singleton_iff]; exact ea_comm e.X.Bel hc hxB
  have hXtop : X ≠ ⊤ := centralizer_ne_top_of_simple hS hx1
  have hrank : GLATwoLocalRank 3 ↥X ≤ CFSG.Open.pRank 3 B := by
    have h1 : GLATwoLocalRank 3 ↥X ≤ GLATwoLocalRank 3 G := CFSG.LocalAnalysis.GLTheoremB.glaTwoLocalRank_subgroup_le (by norm_num) X
    have h2 : 4 ≤ CFSG.Open.pRank 3 B :=
      CFSG.SectionRank.le_pRank (by norm_num) le_rfl e.X.Bel (k := 4) (by rw [e.X.Bc]; norm_num)
    have h3 : GLATwoLocalRank 3 G = 4 := hC.2.1
    omega
  obtain ⟨-, h3, hy, hcase⟩ := i112 G m 3 hS X B K hXtop e.X.Bel hBX hrank hK hnotN
  obtain ⟨-, hZcard, hR4⟩ := hcase.resolve_left hnotL2
  have hZ : Nat.card ↥(barCenterX 3 X (bClosure B K)) ≤ 9 := by
    rcases hZcard with h | ⟨h, -⟩ <;> omega
  obtain ⟨y, hyB, hyN, hyA⟩ : ∃ y ∈ B, y ∉ Subgroup.normalizer (K : Set G) ∧
      (A ≤ Subgroup.normalizer (K : Set G) ∨ y ∈ A) := by
    by_cases hAN : A ≤ Subgroup.normalizer (K : Set G)
    · obtain ⟨y, hyB, hyN⟩ := IsConcreteLE.not_le_iff_exists.1 hnotN
      exact ⟨y, hyB, hyN, Or.inl hAN⟩
    · obtain ⟨y, hyA, hyN⟩ := IsConcreteLE.not_le_iff_exists.1 hAN
      exact ⟨y, e.X.AB hyA, hyN, Or.inr hyA⟩
  obtain ⟨R, hR⟩ := exists_rData e.X.Bel hBX hK hyB hyN h3 hZ hR4
  obtain ⟨hcomp0, hiso⟩ := hy y hyB hyN
  have hk := exists_k0Data e.X.Bel e.X.Bc e.X.SC hxB hx1 hK hyB hyN h3 hR hiso hcomp0
  obtain ⟨hxW, hWfix⟩ := x_mem_W e.X.Bel e.X.SC hxB hx1 hK hyB hyN h3 hR hk
  have hxA : x ∉ A := fun h => not_mem_A_x iL3 iK h515 e h hx1 hK hnotN hyB hyN h3 hR
  rcases hyA with hAN | hyA
  · exact final_contra iL3 iK h514 h515 e hxB hx1 hK hyB hyN h3 hR hk hxW hWfix hAN hxA
  · exact claim_contra iL3 iK h514 h515 i183 iFR e hxB hx1 hxA hK hyA hyN h3 hR hk

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
