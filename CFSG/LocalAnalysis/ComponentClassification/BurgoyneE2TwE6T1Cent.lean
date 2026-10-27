module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE6T1Root
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofTwE6Kernel
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE7Cent

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2.TwE6T1

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.CatLeafProof CFSG.ClassicalInvolution.ModelFacts
  CFSG.LieType.Chevalley.ToralSign CFSG.ComponentClassification.Burgoyne.E2.TwE7
open CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum

@[expose] def e6Gamma20 : List ((Fin TwistTag.E6.tag.rank → ℤ) × ℤ) :=
  [(e6D5TwRoot 0, -7), (e6D5TwRoot 1, -9), (e6D5TwRoot 2, -9), (e6D5TwRoot 3, -5),
    (e6D5TwRoot 4, -8)]

theorem e6Gamma20_reg : ∀ α ∈ rootFinset TwistTag.E6.tag,
    (∑ j, regCoweight e6Gamma20 j * α j) ≠ 0 ∧ (∑ j, regCoweight e6Gamma20 j * α j).natAbs < 12 :=
  by decide +kernel

theorem e6Gamma20_mem : ∀ y ∈ e6Gamma20, y.1 ∈ Set.range e6D5TwRoot := by
  intro y hy
  simp only [e6Gamma20, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩

theorem e6D5TwRoot_mem_rootFinset : ∀ i : Fin 5, e6D5TwRoot i ∈ rootFinset .E6 := by
  decide +kernel


variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

section Datum

variable (D : OrthogonalSemilinearFixedRootDatum TwistTag.E6.tag p k)

theorem simpleRootsJ_eq_simpleUnion_e6 [Subsingleton (KernelComponent D.χ)] :
    D.simpleRootsJ = simpleUnion D.χ := by
  rw [D.simpleRootsJ_eq]
  ext β
  simp only [unionSimpleRoots, simpleUnion, Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_coe]
  constructor
  · rintro ⟨i, -, h⟩
    exact ⟨i, h⟩
  · rintro ⟨i, h⟩
    refine ⟨i, ?_, h⟩
    obtain ⟨i₀, hJ⟩ := D.isThetaOrbit
    obtain ⟨α₀, hα₀⟩ := Quotient.exists_rep i₀
    have hα₀K : α₀.1 ∈ componentRoots D.χ i₀ := ⟨α₀.2, by rw [← hα₀]⟩
    have hi₀ : i₀ ∈ D.J := by
      rw [hJ]
      exact ⟨0, α₀.1, hα₀K, α₀.1, hα₀K, by simp⟩
    rwa [Subsingleton.elim i i₀]

theorem commute_rootSL2_of_commute_orbitGroup_e6 (hq : 3 ≤ D.q)
    (hcard : ∀ O ∈ D.orbits, orbitCard O = 1 ∨ orbitCard O = 2) {z : ModGL TwistTag.E6.tag k}
    (hz : ∀ w ∈ D.orbitGroup, z * w = w * z) {β : Fin TwistTag.E6.tag.rank → ℤ}
    (hβ : β ∈ D.simpleRootsJ) (A : SL2 k) :
    z * rootSL2 TwistTag.E6.tag k β A = rootSL2 TwistTag.E6.tag k β A * z := by
  have hO : thetaOrbit D.θ β ∈ D.orbits := ⟨β, hβ, rfl⟩
  obtain ⟨j, hj, hjβ⟩ := D.exists_orbitVec_eq hO (self_mem_thetaOrbit D.θ β)
  have hτ : TwistTag.E6.tag ≠ .G2 := by decide
  have hX : ∀ c, (z : Module.End k (RootModule TwistTag.E6.tag k)) *
      (D.orbitX (thetaOrbit D.θ β) c : Module.End k (RootModule TwistTag.E6.tag k)) =
        (D.orbitX (thetaOrbit D.θ β) c : Module.End k (RootModule TwistTag.E6.tag k)) * z :=
    fun c => congrArg Units.val (hz _ (Subgroup.subset_closure ⟨_, hO, c, Or.inl rfl⟩))
  have hY : ∀ c, (z : Module.End k (RootModule TwistTag.E6.tag k)) *
      (D.orbitY (thetaOrbit D.θ β) c : Module.End k (RootModule TwistTag.E6.tag k)) =
        (D.orbitY (thetaOrbit D.θ β) c : Module.End k (RootModule TwistTag.E6.tag k)) * z :=
    fun c => congrArg Units.val (hz _ (Subgroup.subset_closure ⟨_, hO, c, Or.inr rfl⟩))
  have hu := fun t => commute_uSL_of_commute_orbitX D hτ hq hO (hcard _ hO) hX hj t
  have hv := fun t => commute_vSL_of_commute_orbitY D hτ hq hO (hcard _ hO) hY hj t
  rw [hjβ] at hu hv
  have hle : (⊤ : Subgroup (SL2 k)) ≤ (Subgroup.centralizer
      ({z} : Set (ModGL TwistTag.E6.tag k))).comap (rootSL2 TwistTag.E6.tag k β) := by
    rw [← sl2_closure_upper_lower, Subgroup.closure_le]
    rintro _ (⟨t, rfl⟩ | ⟨t, rfl⟩) <;>
      rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    · exact Units.ext (hu t).symm
    · exact Units.ext (hv t).symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle (Subgroup.mem_top A))).symm

theorem orbitCard_of_twenty (hχ : D.χ = signMaskChar TwistTag.E6.tag 20)
    (hθ : ∀ γ, D.θ (toReal γ) =
      toReal (thetaMap (ToralSign.wordElt TwistTag.E6.tag []) TwistTag.E6.perm γ)) :
    ∀ O ∈ D.orbits, orbitCard O = 1 ∨ orbitCard O = 2 := by
  obtain ⟨-, h6, -⟩ := rational_toral_sign_diagram_arithmetic
  have hθp : ThetaProperties TwistTag.E6.perm 2 D.χ (ToralSign.wordElt TwistTag.E6.tag []) := by
    rw [hχ]
    exact h6.theta ⟨20, 27, 1, e6OmegaWords20⟩ (by simp [e6SignDiagramReps]) []
      (by simp [e6OmegaWords20])
  exact fun O hO => orbitCard_eq_of_thetaProperties D hθp hθ hO

theorem eq_of_commute_orbitGroup_twenty (hq : 3 ≤ D.q)
    (hχ : D.χ = signMaskChar TwistTag.E6.tag 20)
    (hθ : ∀ γ, D.θ (toReal γ) =
      toReal (thetaMap (ToralSign.wordElt TwistTag.E6.tag []) TwistTag.E6.perm γ))
    [Subsingleton (KernelComponent D.χ)] {z : ModGL TwistTag.E6.tag k}
    (hzG : z ∈ adjointGroup TwistTag.E6.tag k) (hz : ∀ w ∈ D.orbitGroup, z * w = w * z) :
    ∃ b : Fin TwistTag.E6.tag.rank → kˣ, z = rootDiagUnit TwistTag.E6.tag b ∧
      b (t1Node 0) = 1 ∧ b (t1Node 1) = 1 ∧ b (t1Node 3) = 1 ∧ b (t1Node 5) = 1 ∧
        b (t1Node 2) * b (t1Node 4) = 1 := by
  have hcard := orbitCard_of_twenty D hχ hθ
  have hΔ : D.simpleRootsJ = Set.range e6D5TwRoot := by
    rw [simpleRootsJ_eq_simpleUnion_e6, hχ]
    exact simpleUnion_e6_twenty
  have hmem : ∀ β ∈ Set.range e6D5TwRoot, ∀ A : SL2 k,
      z * rootSL2 TwistTag.E6.tag k β A = rootSL2 TwistTag.E6.tag k β A * z := fun β hβ A =>
    commute_rootSL2_of_commute_orbitGroup_e6 D hq hcard hz (hΔ ▸ hβ) A
  have hroot : ∀ i : Fin 5, IsRoot TwistTag.E6.tag (e6D5TwRoot i) := fun i =>
    mem_rootFinset.1 (e6D5TwRoot_mem_rootFinset i)
  have hT := mem_torusGroup_of_commute_rootTorus (τ := TwistTag.E6.tag) p (Or.inl rfl) hzG
    e6Gamma20
    (fun y hy => by
      obtain ⟨i, hi⟩ := e6Gamma20_mem y hy
      rw [← hi]
      exact hroot i)
    (fun y hy s => hmem y.1 (e6Gamma20_mem y hy) (HSL s)) 12
    (fun α hα => e6Gamma20_reg α (mem_rootFinset.2 hα))
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hT
  have hχb : ∀ i : Fin 5, rootChar b (e6D5TwRoot i) = 1 := fun i =>
    rootChar_eq_one_of_commute (hroot i) (hmem _ ⟨i, rfl⟩ (uSL 1))
  have hs : ∀ (i : Fin 5) (j : Fin 6),
      (e6D5TwRoot i : Fin TwistTag.E6.tag.rank → ℤ) = Pi.single (t1Node j) 1 →
        b (t1Node j) = 1 := fun i j h => by
    have h' := hχb i
    rwa [h, rootChar_single'] at h'
  have h3 := hs 0 3 (by funext i; fin_cases i <;> rfl)
  refine ⟨b, rfl, hs 3 0 (by funext i; fin_cases i <;> rfl),
    hs 1 1 (by funext i; fin_cases i <;> rfl), h3, hs 4 5 (by funext i; fin_cases i <;> rfl), ?_⟩
  have h := (rootChar_e6_eq b (e6D5TwRoot 2)).symm.trans (hχb 2)
  have e0 : (e6D5TwRoot 2 : Fin TwistTag.E6.tag.rank → ℤ) (t1Node 0) = 0 := rfl
  have e1 : (e6D5TwRoot 2 : Fin TwistTag.E6.tag.rank → ℤ) (t1Node 1) = 0 := rfl
  have e2 : (e6D5TwRoot 2 : Fin TwistTag.E6.tag.rank → ℤ) (t1Node 2) = 1 := rfl
  have e3 : (e6D5TwRoot 2 : Fin TwistTag.E6.tag.rank → ℤ) (t1Node 3) = 1 := rfl
  have e4 : (e6D5TwRoot 2 : Fin TwistTag.E6.tag.rank → ℤ) (t1Node 4) = 1 := rfl
  have e5 : (e6D5TwRoot 2 : Fin TwistTag.E6.tag.rank → ℤ) (t1Node 5) = 0 := rfl
  rw [e0, e1, e2, e3, e4, e5, h3] at h
  simpa using h

end Datum

end CFSG.ComponentClassification.Burgoyne.E2.TwE6T1
