module

public import CFSG.ClassicalInvolution.Q3.Q3PlanKronecker
public import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedTotalComponents
public import CFSG.LieType.AlgebraicGroups.ToralTwistPinningRoots

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial

section Expansion

variable {τ : Tag} {k : Type} [Field k]

@[expose] noncomputable def uCoeff (τ : Tag) (k : Type) [Field k] (γ : Fin τ.rank → ℤ) (m : ℕ) :
    Module.End k (RootModule τ k) :=
  ((pinnedData τ γ).2.2 ^ m : ℤ) • pinnedCoeff τ k γ m

theorem uCoeff_zero (γ : Fin τ.rank → ℤ) : uCoeff τ k γ 0 = 1 := by
  simp [uCoeff, pinnedCoeff_zero]

theorem coe_rootSL2_uSL (γ : Fin τ.rank → ℤ) (s : k) :
    ((rootSL2 τ k γ (uSL s) : ModGL τ k) : Module.End k (RootModule τ k)) =
      ∑ m ∈ Finset.range 4, s ^ m • uCoeff τ k γ m := by
  rw [rootSL2_uSL_eq, pinnedX_eq_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [uCoeff]
  rw [smul_pow, smul_assoc, smul_comm]

theorem exists_vCoeff {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    ∃ P : ℕ → Module.End k (RootModule τ k), P 0 = 1 ∧ ∀ s : k,
      ((rootSL2 τ k γ (vSL s) : ModGL τ k) : Module.End k (RootModule τ k)) =
        ∑ m ∈ Finset.range 4, s ^ m • P m := by
  obtain ⟨ε, hε, h⟩ := exists_rootSL2_vSL_eq (K := k) hγ
  refine ⟨fun m => ε ^ m • pinnedCoeff τ k (-γ) m, by simp [pinnedCoeff_zero], fun s => ?_⟩
  rw [h, pinnedX_eq_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [mul_pow, mul_comm, mul_smul]

end Expansion

section Orbit

open OrthogonalSemilinearFixedRootDatum

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  (D : OrthogonalSemilinearFixedRootDatum τ p₀ k)

theorem exists_finset_orbitField {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    ∃ S : Finset k, S.card = D.q ^ orbitCard O ∧ ∀ c ∈ S, c ∈ D.orbitField O := by
  classical
  have hcard := D.card_orbitField hO
  have hfin : Finite (D.orbitField O) := Nat.finite_of_card_ne_zero (by
    rw [hcard]
    exact pow_ne_zero _ (pow_ne_zero _ (Fact.out : p₀.Prime).ne_zero))
  have := Fintype.ofFinite (D.orbitField O)
  refine ⟨Finset.univ.image (fun c : D.orbitField O => (c : k)), ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ Subtype.val_injective, Finset.card_univ,
      ← Nat.card_eq_fintype_card, hcard]
  · intro c hc
    obtain ⟨c', -, rfl⟩ := Finset.mem_image.mp hc
    exact c'.2

theorem commute_rootSL2_uSL_of_commute_orbitX (hq : 4 ≤ D.q) {O : Set (Fin τ.rank → ℤ)}
    (hO : O ∈ D.orbits) {g : ModGL τ k}
    (hg : ∀ c : D.orbitField O, g * D.orbitX O c = D.orbitX O c * g) :
    ∀ j < orbitCard O, ∀ s : k,
      g * rootSL2 τ k (D.orbitVec O j) (uSL s) = rootSL2 τ k (D.orbitVec O j) (uSL s) * g := by
  obtain ⟨S, hScard, hSmem⟩ := exists_finset_orbitField D hO
  refine commute_unit_family D.q hq (orbitCard O) S hScard.ge
    (fun j s => rootSL2 τ k (D.orbitVec O j) (uSL s))
    (fun j m => uCoeff τ k (D.orbitVec O j) m) (fun j => uCoeff_zero _)
    (fun j s => coe_rootSL2_uSL _ s) g ?_
  intro c hc
  have h := hg ⟨c, hSmem c hc⟩
  rw [OrthogonalSemilinearFixedRootDatum.orbitX, D.orbitMap_eq_prod] at h
  have e : ((List.range (orbitCard O)).map fun j =>
      rootSL2 τ k (D.orbitVec O j) (uSL (c ^ D.q ^ j))) =
      (List.range (orbitCard O)).map fun j => D.orbitFactor O j (uSL ⟨c, hSmem c hc⟩) :=
    List.map_congr_left fun j _ => (D.orbitFactor_uSL O j ⟨c, hSmem c hc⟩).symm
  rw [e]
  exact h

theorem commute_rootSL2_vSL_of_commute_orbitY (hq : 4 ≤ D.q) {O : Set (Fin τ.rank → ℤ)}
    (hO : O ∈ D.orbits) {g : ModGL τ k}
    (hg : ∀ c : D.orbitField O, g * D.orbitY O c = D.orbitY O c * g) :
    ∀ j < orbitCard O, ∀ s : k,
      g * rootSL2 τ k (D.orbitVec O j) (vSL s) = rootSL2 τ k (D.orbitVec O j) (vSL s) * g := by
  obtain ⟨S, hScard, hSmem⟩ := exists_finset_orbitField D hO
  choose P hP0 hP using fun j => exists_vCoeff (k := k) (D.isRoot_orbitVec hO j)
  refine commute_unit_family D.q hq (orbitCard O) S hScard.ge
    (fun j s => rootSL2 τ k (D.orbitVec O j) (vSL s)) P hP0 hP g ?_
  intro c hc
  have h := hg ⟨c, hSmem c hc⟩
  rw [OrthogonalSemilinearFixedRootDatum.orbitY, D.orbitMap_eq_prod] at h
  have e : ((List.range (orbitCard O)).map fun j =>
      rootSL2 τ k (D.orbitVec O j) (vSL (c ^ D.q ^ j))) =
      (List.range (orbitCard O)).map fun j => D.orbitFactor O j (vSL ⟨c, hSmem c hc⟩) :=
    List.map_congr_left fun j _ => (D.orbitFactor_vSL O j ⟨c, hSmem c hc⟩).symm
  rw [e]
  exact h

theorem commute_rootSL2_of_commute_orbitGroup (hq : 4 ≤ D.q) {O : Set (Fin τ.rank → ℤ)}
    (hO : O ∈ D.orbits) {g : ModGL τ k} (hg : ∀ x ∈ D.orbitGroup, g * x = x * g)
    {β : Fin τ.rank → ℤ} (hβ : β ∈ O) (A : SL2 k) :
    g * rootSL2 τ k β A = rootSL2 τ k β A * g := by
  obtain ⟨j, hj, rfl⟩ := D.exists_orbitVec_eq hO hβ
  have hu := commute_rootSL2_uSL_of_commute_orbitX D hq hO
    (fun c => hg _ (Subgroup.subset_closure ⟨O, hO, c, Or.inl rfl⟩)) j hj
  have hv := commute_rootSL2_vSL_of_commute_orbitY D hq hO
    (fun c => hg _ (Subgroup.subset_closure ⟨O, hO, c, Or.inr rfl⟩)) j hj
  have htop : (Subgroup.centralizer ({g} : Set (ModGL τ k))).comap
      (rootSL2 τ k (D.orbitVec O j)) = ⊤ := by
    rw [eq_top_iff, ← sl2_closure_upper_lower (K := k), Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
      exact (hu c).symm
    · rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
      exact (hv c).symm
  have : A ∈ (Subgroup.centralizer ({g} : Set (ModGL τ k))).comap
      (rootSL2 τ k (D.orbitVec O j)) := by
    rw [htop]
    exact Subgroup.mem_top A
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff] at this
  exact this.symm

theorem commute_kernelSpan_of_commute_orbitGroups (hq : 4 ≤ D.q) {g : ModGL τ k}
    (hg : ∀ J' : Set.range D.classOrbit, ∀ x ∈ (D.withOrbit J').orbitGroup, g * x = x * g) :
    ∀ y ∈ D.kernelSpan, g * y = y * g := by
  have hle : D.kernelSpan ≤ Subgroup.centralizer ({g} : Set (ModGL τ k)) := by
    rw [kernelSpan, rootSpan_kernelRoots_eq_iSup_rootRankOneGroup]
    refine iSup₂_le fun β hβ => ?_
    have hβΔ : β ∈ unionSimpleRoots D.χ Set.univ := by
      rw [unionSimpleRoots_univ_eq]
      exact hβ
    obtain ⟨i, -, hβi⟩ := hβΔ
    set J' : Set.range D.classOrbit := ⟨D.classOrbit i, i, rfl⟩ with hJ'
    have hβ' : β ∈ (D.withOrbit J').simpleRootsJ := by
      rw [(D.withOrbit J').simpleRootsJ_eq]
      exact ⟨i, D.self_mem_classOrbit i, hβi⟩
    have hO : thetaOrbit D.θ β ∈ (D.withOrbit J').orbits := ⟨β, hβ', rfl⟩
    rintro _ ⟨A, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (commute_rootSL2_of_commute_orbitGroup (D.withOrbit J') hq hO (hg J')
      (self_mem_thetaOrbit D.θ β) A).symm
  intro y hy
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hy)).symm

end Orbit

end CFSG.ClassicalInvolution.Q3
