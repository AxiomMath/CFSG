module

public import CFSG.ClassicalInvolution.Q3.Q3TWInputs
public import CFSG.ClassicalInvolution.Q3.Q3WACore
public import CFSG.ClassicalInvolution.Q3.Q3WAComp

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TW

open CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.Steinberg CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic (Commutes conjSub fundamentalSubgroups
  FundamentalSingleClass modelUniv)
open CFSG.ClassicalInvolution.RouteD
open CFSG.ClassicalInvolution.Q3.Q3W

set_option linter.unusedSectionVars false


theorem nonempty_extModel3U_minus {n : ℕ} (hn : 6 ≤ n) (hΘ : LeviEmbed3Minus)
    (hpowT : ∀ R ∈ fundamentalSubgroups .POmegaMinus (minusDatum n (minusCoeffs_irr 3 1)),
      Pow3 R)
    (hpowY : ∀ R ∈ fundamentalSubgroups .POmegaMinus (minusDatum (n - 2) (minusCoeffs_irr 3 1)),
      Pow3 R)
    (hcopT : ∀ z ∈ Subgroup.center (spinGroup (quadMinus n (GaloisField 3 1)
      (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)), ¬ 3 ∣ orderOf z)
    (hcopY : ∀ z ∈ Subgroup.center (spinGroup (quadMinus (n - 2) (GaloisField 3 1)
      (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)), ¬ 3 ∣ orderOf z) :
    Nonempty (ExtModel3U .POmegaMinus .POmegaMinus
      ⟨spinGroup (quadMinus n (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2),
        minusDatum n (minusCoeffs_irr 3 1)⟩
      ⟨spinGroup (quadMinus (n - 2) (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2),
        minusDatum (n - 2) (minusCoeffs_irr 3 1)⟩ 2) := by
  have hn3 : 3 ≤ n := by omega
  have hirr := minusCoeffs_irr 3 1
  have hadm : StatedLieAdmissible .POmegaMinus n 3 1 :=
    ⟨Nat.prime_three, le_rfl, by show 4 ≤ n; omega⟩
  have hadmY : StatedLieAdmissible .POmegaMinus (n - 2) 3 1 :=
    ⟨Nat.prime_three, le_rfl, by show 4 ≤ n - 2; omega⟩
  have hscT0 : FundamentalSingleClass .POmegaMinus
      (modelUniv .POmegaMinus n 3 1 Nat.prime_three).D :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .POmegaMinus n 3 1
      Nat.prime_three trivial hadm (by decide) (by decide)
  have hscY0 : FundamentalSingleClass .POmegaMinus
      (modelUniv .POmegaMinus (n - 2) 3 1 Nat.prime_three).D :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .POmegaMinus (n - 2) 3 1
      Nat.prime_three trivial hadmY (by decide) (by decide)
  have hscY : FundamentalSingleClass .POmegaMinus (minusDatum (n - 2) hirr) := hscY0
  obtain ⟨Θ, hker, hnode, hrange⟩ := hΘ n hn
  let n0 : Fin (n - 1) := twIdx0 hn3
  let n0' : Fin (n - 2 - 1) := ⟨0, by omega⟩
  set DT := minusDatum n hirr with hDT
  set DY := minusDatum (n - 2) hirr with hDY
  set X : Subgroup (spinGroup (quadMinus n (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2)) :=
    ⨆ k : Fin (n - 2 - 1), rankOne DT.rootGroup (nodeMinus (by omega) k) with hX
  have hlong0 : n0.val + 1 < n - 1 := by simp only [n0, twIdx0]; omega
  have hlong0' : n0'.val + 1 < n - 2 - 1 := by simp only [n0']; omega
  have hcommX0 : ∀ k : Fin (n - 2 - 1),
      Commutes (rankOne DT.rootGroup n0) (rankOne DT.rootGroup (nodeMinus (by omega) k)) := by
    intro k
    refine commutes_rankOne_of_cartan_eq_zero_of_longest (minusDatum n hirr)
      (minusDatum_steinbergExtras n hirr) (isLongestRoot_node_minus hirr hlong0).2 ?_
    refine cartanB_eq_zero_of_far (n := n - 1) (Or.inl ?_)
    simp only [nodeMinus, n0, twIdx0]
    omega
  have hcommXθ : Commutes X (rankOneHiMinus hirr hn3) := by
    refine commutes_iSup_left.mpr fun k => ?_
    exact (commutes_rankOneHiMinus hirr hn3 (j := nodeMinus (by omega) k)
      (by simp only [nodeMinus]; omega)).symm
  have hcommX0' : Commutes X (rankOne DT.rootGroup n0) :=
    commutes_iSup_left.mpr fun k => (hcommX0 k).symm
  have himg : ∀ R ∈ fundamentalSubgroups .POmegaMinus DY,
      ∃ g : spinGroup (quadMinus (n - 2) (GaloisField 3 1) (minusCoeffs 3 1).1
        (minusCoeffs 3 1).2),
      R.map Θ = conjSub (Θ g) (rankOne DT.rootGroup (nodeMinus (by omega) n0')) := by
    intro R hR
    obtain ⟨g, hg⟩ := hscY (rankOne DY.rootGroup n0') (rankOne_mem_fund_minus hirr hlong0') R hR
    refine ⟨g, ?_⟩
    rw [hg, ← CFSG.ClassicalInvolution.Generic.conjSub_map, hnode]
  have hlongN : (nodeMinus (n := n) (by omega) n0').val + 1 < n - 1 := by
    simp only [nodeMinus, n0']
    omega
  refine ⟨{
    Rθ := rankOneHiMinus hirr hn3
    twin := fun _ => rankOne DT.rootGroup n0
    Θ := Θ
    Rθ_mem := rankOneHiMinus_mem_fund hirr hn3
    twin_mem := fun _ => rankOne_mem_fund_minus hirr hlong0
    Θ_ker := hker
    Θ_mem := ?_
    Θ_comm := ?_
    twin_comm := ?_
    twin_comm_Θ := ?_
    twin_inj := fun a b _ => Fin.ext (by have h1 := a.isLt; have h2 := b.isLt; omega)
    pow_T := hpowT
    pow_Y := hpowY
    cop_T := hcopT
    cop_Y := hcopY }⟩
  · intro R hR
    obtain ⟨g, hg⟩ := himg R hR
    rw [hg]
    exact conjSub_mem_fundamentalSubgroups (rankOne_mem_fund_minus hirr hlongN) _
  · intro R hR
    obtain ⟨g, hg⟩ := himg R hR
    rw [hg]
    have hgX : Θ g ∈ X := by rw [← hrange]; exact ⟨g, rfl⟩
    have h1 : conjSub (Θ g) (rankOneHiMinus hirr hn3) = rankOneHiMinus hirr hn3 :=
      CFSG.ClassicalInvolution.Generic.conjSub_eq_of_mem_of_commutes hgX hcommXθ
    have h2' : Commutes (rankOne DT.rootGroup (nodeMinus (n := n) (by omega) n0'))
        (rankOneHiMinus hirr hn3) :=
      (commutes_rankOneHiMinus hirr hn3 (j := nodeMinus (n := n) (by omega) n0')
        (by simp only [nodeMinus]; omega)).symm
    have h3 := (CFSG.ClassicalInvolution.Generic.commutes_conjSub_iff (Θ g)).mpr h2'
    rwa [h1] at h3
  · intro i
    exact (commutes_hiMinus_twin hirr hn3).symm
  · intro i R hR
    obtain ⟨g, hg⟩ := himg R hR
    rw [hg]
    have hgX : Θ g ∈ X := by rw [← hrange]; exact ⟨g, rfl⟩
    have h1 := CFSG.ClassicalInvolution.Generic.conjSub_eq_of_mem_of_commutes hgX hcommX0'
    have h2' := hcommX0 n0'
    have h3 := (CFSG.ClassicalInvolution.Generic.commutes_conjSub_iff (Θ g)).mpr h2'
    rwa [h1] at h3

theorem nonempty_extModel3_minus {n : ℕ} (hn : 6 ≤ n) (hΘ : LeviEmbed3Minus) :
    Nonempty (ExtModel3 .POmegaMinus n .POmegaMinus (n - 2) 2) := by
  have hadm : StatedLieAdmissible .POmegaMinus n 3 1 :=
    ⟨Nat.prime_three, le_rfl, by show 4 ≤ n; omega⟩
  have hadmY : StatedLieAdmissible .POmegaMinus (n - 2) 3 1 :=
    ⟨Nat.prime_three, le_rfl, by show 4 ≤ n - 2; omega⟩
  have hpcT := powCop3_model (t := .POmegaMinus) (n := n) trivial hadm (by decide) (by decide)
  have hpcY := powCop3_model (t := .POmegaMinus) (n := n - 2) trivial hadmY (by decide)
    (by decide)
  exact nonempty_extModel3U_minus hn hΘ hpcT.pow3 hpcY.pow3 hpcT.cop hpcY.cop

end CFSG.ClassicalInvolution.Q3.Q3TW
