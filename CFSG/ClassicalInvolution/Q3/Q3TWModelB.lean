module

public import CFSG.ClassicalInvolution.Q3.Q3TWInputs
public import CFSG.ClassicalInvolution.Q3.Q3WACore
public import CFSG.ClassicalInvolution.Q3.Q3WAComp

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TW

open CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.Steinberg CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic (Commutes conjSub fundamentalSubgroups
  FundamentalSingleClass modelUniv)
open CFSG.ClassicalInvolution.RouteD
open CFSG.ClassicalInvolution.Q3.Q3W

set_option linter.unusedSectionVars false


theorem nonempty_extModel3U_odd {n : ℕ} (hn : 5 ≤ n) (hΘ : LeviEmbed3Odd)
    (hpowT : ∀ R ∈ fundamentalSubgroups .POmegaOdd (oddDatum n (GaloisField 3 1)), Pow3 R)
    (hpowY : ∀ R ∈ fundamentalSubgroups .POmegaOdd (oddDatum (n - 2) (GaloisField 3 1)), Pow3 R)
    (hcopT : ∀ z ∈ Subgroup.center (spinGroup (quadOdd n (GaloisField 3 1))),
      ¬ 3 ∣ orderOf z)
    (hcopY : ∀ z ∈ Subgroup.center (spinGroup (quadOdd (n - 2) (GaloisField 3 1))),
      ¬ 3 ∣ orderOf z) :
    Nonempty (ExtModel3U .POmegaOdd .POmegaOdd
      ⟨spinGroup (quadOdd n (GaloisField 3 1)), oddDatum n (GaloisField 3 1)⟩
      ⟨spinGroup (quadOdd (n - 2) (GaloisField 3 1)), oddDatum (n - 2) (GaloisField 3 1)⟩ 2) := by
  have hn3 : 3 ≤ n := by omega
  have hn3' : 3 ≤ n - 2 := by omega
  set F := GaloisField 3 1 with hFdef
  have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField 1
    (by norm_num)
  have hadm : StatedLieAdmissible .POmegaOdd n 3 1 := ⟨Nat.prime_three, le_rfl, hn3, by norm_num⟩
  have hadmY : StatedLieAdmissible .POmegaOdd (n - 2) 3 1 :=
    ⟨Nat.prime_three, le_rfl, hn3', by norm_num⟩
  have hfundM : CFSG.ClassicalInvolution.ModelFacts.IsFundTag .POmegaOdd := trivial
  have hscT0 : FundamentalSingleClass .POmegaOdd (modelUniv .POmegaOdd n 3 1 Nat.prime_three).D :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .POmegaOdd n 3 1 Nat.prime_three
      hfundM hadm (by decide) (by decide)
  have hscY0 : FundamentalSingleClass .POmegaOdd
      (modelUniv .POmegaOdd (n - 2) 3 1 Nat.prime_three).D :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .POmegaOdd (n - 2) 3 1
      Nat.prime_three hfundM hadmY (by decide) (by decide)
  have hscT : FundamentalSingleClass .POmegaOdd (oddDatum n F) := hscT0
  have hscY : FundamentalSingleClass .POmegaOdd (oddDatum (n - 2) F) := hscY0
  obtain ⟨Θ, hker, hnode, hrange⟩ := hΘ n hn
  let n0 : Fin n := zeroB (by omega)
  let n0' : Fin (n - 2) := zeroB (by omega)
  set DT := oddDatum n F with hDT
  set DY := oddDatum (n - 2) F with hDY
  set X : Subgroup (spinGroup (quadOdd n F)) :=
    ⨆ k : Fin (n - 2), rankOne DT.rootGroup (nodeB (n := n) (by omega) k) with hX
  have hlong0 : n0.val + 1 < n := by simp only [n0, zeroB_val]; omega
  have hcommX0 : ∀ k : Fin (n - 2),
      Commutes (rankOne DT.rootGroup n0) (rankOne DT.rootGroup (nodeB (n := n) (by omega) k)) := by
    intro k
    refine commutes_rankOne_oddDatum hn3 h2 (cartanB_eq_zero_of_far ?_)
    simp only [nodeB, n0, zeroB_val]
    omega
  have hcommXθ : Commutes X (rootθB n F) := by
    refine commutes_iSup_left.mpr fun k => ?_
    exact (commutes_rootθB_rankOne hn3 h2 (k := nodeB (n := n) (by omega) k)
      (by simp only [nodeB]; omega)).symm
  have hcommX0' : Commutes X (rankOne DT.rootGroup n0) :=
    commutes_iSup_left.mpr fun k => (hcommX0 k).symm
  have himg : ∀ R ∈ fundamentalSubgroups .POmegaOdd DY, ∃ g : spinGroup (quadOdd (n - 2) F),
      R.map Θ = conjSub (Θ g) (rankOne DT.rootGroup (nodeB (n := n) (by omega) n0')) := by
    intro R hR
    obtain ⟨g, hg⟩ := hscY (rankOne DY.rootGroup n0')
      (rankOne_mem_fundamentalSubgroups_oddDatum hn3' (by simp only [n0', zeroB_val]; omega)) R hR
    refine ⟨g, ?_⟩
    rw [hg, ← CFSG.ClassicalInvolution.Generic.conjSub_map, hnode]
  have h02 : (nodeB (n := n) (by omega) n0').val ≠ 1 := by simp only [nodeB, n0', zeroB_val]; omega
  refine ⟨{
    Rθ := rootθB n F
    twin := fun _ => rankOne DT.rootGroup n0
    Θ := Θ
    Rθ_mem := rootθB_mem_fundamentalSubgroups hn3
    twin_mem := fun _ => rankOne_mem_fundamentalSubgroups_oddDatum hn3 hlong0
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
    exact conjSub_mem_fundamentalSubgroups
      (rankOne_mem_fundamentalSubgroups_oddDatum hn3 (i := nodeB (n := n) (by omega) n0')
        (by simp only [nodeB, n0', zeroB_val]; omega)) _
  · intro R hR
    obtain ⟨g, hg⟩ := himg R hR
    rw [hg]
    have hgX : Θ g ∈ X := by rw [← hrange]; exact ⟨g, rfl⟩
    have h1 : conjSub (Θ g) (rootθB n F) = rootθB n F :=
      CFSG.ClassicalInvolution.Generic.conjSub_eq_of_mem_of_commutes hgX hcommXθ
    have h2' : Commutes (rankOne DT.rootGroup (nodeB (n := n) (by omega) n0')) (rootθB n F) :=
      (commutes_rootθB_rankOne hn3 h2 (k := nodeB (n := n) (by omega) n0') h02).symm
    have h3 := (CFSG.ClassicalInvolution.Generic.commutes_conjSub_iff (Θ g)).mpr h2'
    rwa [h1] at h3
  · intro i
    exact (commutes_rootθB_rankOne hn3 h2 (k := n0) (by simp [n0])).symm
  · intro i R hR
    obtain ⟨g, hg⟩ := himg R hR
    rw [hg]
    have hgX : Θ g ∈ X := by rw [← hrange]; exact ⟨g, rfl⟩
    have h1 := CFSG.ClassicalInvolution.Generic.conjSub_eq_of_mem_of_commutes hgX hcommX0'
    have h2' := hcommX0 n0'
    have h3 := (CFSG.ClassicalInvolution.Generic.commutes_conjSub_iff (Θ g)).mpr h2'
    rwa [h1] at h3


theorem nonempty_extModel3_odd {n : ℕ} (hn : 5 ≤ n) (hΘ : LeviEmbed3Odd) :
    Nonempty (ExtModel3 .POmegaOdd n .POmegaOdd (n - 2) 2) := by
  have hadm : StatedLieAdmissible .POmegaOdd n 3 1 :=
    ⟨Nat.prime_three, le_rfl, by omega, by norm_num⟩
  have hadmY : StatedLieAdmissible .POmegaOdd (n - 2) 3 1 :=
    ⟨Nat.prime_three, le_rfl, by omega, by norm_num⟩
  have hpcT := powCop3_model (t := .POmegaOdd) (n := n) trivial hadm (by decide) (by decide)
  have hpcY := powCop3_model (t := .POmegaOdd) (n := n - 2) trivial hadmY (by decide) (by decide)
  exact nonempty_extModel3U_odd hn hΘ hpcT.pow3 hpcY.pow3 hpcT.cop hpcY.cop

end CFSG.ClassicalInvolution.Q3.Q3TW
