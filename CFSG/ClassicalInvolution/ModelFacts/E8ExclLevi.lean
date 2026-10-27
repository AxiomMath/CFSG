module

public import CFSG.ClassicalInvolution.ModelFacts.E7ModelLeviStab
public import CFSG.ClassicalInvolution.Generic.SL2Anticommute
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE7Descent
public import CFSG.ClassicalInvolution.RouteD.LocalTwinSp
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.ModelFacts.E7Model

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.LieType.RootSystem RootSpace CFSG.ClassicalInvolution.Generic
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.ClassicalInvolution.ModelFacts.Levi CFSG.ClassicalInvolution.ModelFacts
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD CFSG.Timmesfeld

section Centralizer

variable {k : Type} [Field k]

theorem rootCharStabilizer_thetaE7_le {c : kˣ} (hc : ∀ j : ℕ, 1 ≤ j → j ≤ 3 → c ^ j ≠ 1)
    {w : WeylGroup .E7} (hw : w ∈ rootCharStabilizer (thetaDiag thetaE7 c)) :
    w ∈ kernelReflectionGroup (thetaDiag thetaE7 c) := by
  classical
  have hbasis : ∀ j : Fin (Tag.rank .E7),
      iform thetaE7 (w • Pi.single j 1) = iform thetaE7 (Pi.single j 1) := by
    intro j
    have hroot : IsRoot .E7 (w • (Pi.single j 1 : Fin (Tag.rank .E7) → ℤ)) :=
      IsRoot.smul (isRoot_single _ j) w
    have h := hw (Pi.single j 1)
    rw [rootChar_thetaDiag, rootChar_thetaDiag] at h
    have b1 := abs_iform_thetaE7_le _ (mem_rootFinset.2 hroot)
    have b2 : iform thetaE7 (Pi.single j 1) = 0 ∨ iform thetaE7 (Pi.single j 1) = 1 := by
      rw [iform_thetaE7_single]
      split_ifs <;> simp
    rw [abs_le] at b1
    have h3 : c ^ (iform thetaE7 (w • Pi.single j 1) - iform thetaE7 (Pi.single j 1)) = 1 := by
      rw [zpow_sub, h, mul_inv_cancel]
    have := eq_zero_of_zpow_eq_one hc
      (m := iform thetaE7 (w • Pi.single j 1) - iform thetaE7 (Pi.single j 1)) (N := 3) (by
        rw [abs_le]; omega) h3
    omega
  have hwl : w • thetaE7 = thetaE7 := smul_eq_self_of_iform_single hbasis
  have hstab : w ∈ weylStabilizer .E7 (ofLattice thetaE7) := by
    change weylAct .E7 w (ofLattice thetaE7) = ofLattice thetaE7
    rw [weylAct_ofLattice, hwl]
  rw [(exceptional_Lang_Weyl_chamber_point_stabilizers .E7).2.2.2.2.2 (ofLattice thetaE7)] at hstab
  have hle : Subgroup.closure {s | ∃ α, IsRoot .E7 α ∧
      inner ℝ (ofLattice α) (ofLattice thetaE7) = 0 ∧ s = rootReflection α} ≤
        kernelReflectionGroup (thetaDiag thetaE7 c) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨σ, hσ, hinner, rfl⟩
    obtain ⟨cc, hcc, hform⟩ := exists_inner_ofLattice_eq_iform .E7
    rw [hform] at hinner
    have h1 : (iform σ thetaE7 : ℝ) = 0 := by
      rcases mul_eq_zero.1 hinner with h | h
      · exact absurd h hcc.ne'
      · exact h
    have h2 : iform σ thetaE7 = 0 := by exact_mod_cast h1
    refine rootReflection_mem_kernelReflectionGroup ⟨hσ, ?_⟩
    rw [rootChar_thetaDiag, iform_comm thetaE7 σ, h2]
    simp
  exact hle hstab

theorem toralCentralizer_thetaE7_le_levi {c : kˣ} (hc : ∀ j : ℕ, 1 ≤ j → j ≤ 3 → c ^ j ≠ 1) :
    toralCentralizer .E7 k (thetaDiag thetaE7 c) ≤ parabolicLevi .E7 k JE7 := by
  intro g hg
  have hM := toralCentralizer_le_toralRootGroup (thetaDiag thetaE7 c)
    (fun w hw => rootCharStabilizer_thetaE7_le hc hw) hg
  refine (sup_le (torusGroup_le_parabolicLevi JE7) (iSup₂_le fun σ hσ =>
    rootSubgroup_le_parabolicLevi' ?_)) hM
  obtain ⟨hσr, hσ1⟩ := hσ
  rw [rootChar_thetaDiag] at hσ1
  have b := abs_iform_thetaE7_le σ (mem_rootFinset.2 hσr)
  rw [abs_le] at b
  have h0 := eq_zero_of_zpow_eq_one hc (m := iform thetaE7 σ) (N := 3) (by
    rw [abs_le]; omega) hσ1
  exact mem_parabolicRoots_E7 hσr h0

end Centralizer

section Field

variable {p f : ℕ} [Fact p.Prime]

theorem exists_galoisField_unit_pow_ne_one (hq : 5 ≤ p ^ f) :
    ∃ c : (GaloisField p f)ˣ, ∀ j : ℕ, 1 ≤ j → j ≤ 3 → c ^ j ≠ 1 := by
  have : NeZero f := ⟨by rintro rfl; simp at hq⟩
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := (GaloisField p f)ˣ)
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (NeZero.ne f)
  have hord : orderOf ζ = Nat.card (GaloisField p f) - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hζ, Nat.card_units]
  refine ⟨ζ, fun j hj1 hj3 h => ?_⟩
  have := Nat.le_of_dvd (by omega) (orderOf_dvd_of_pow_eq_one h)
  omega

end Field

section Decomposition

variable {F : Type} [Field F]

@[expose] noncomputable def NJ (F : Type) [Field F] (J : Set (Fin (Tag.rank .E7))) :
    Subgroup (ModGL .E7 F) :=
  Subgroup.closure {g | ∃ j ∈ J, ∃ c : F, g = xUnit .E7 F j c ∨ g = yUnit .E7 F j c}

theorem parabolicLevi_eq_sup (J : Set (Fin (Tag.rank .E7))) :
    parabolicLevi .E7 F J = torusGroup .E7 F ⊔ NJ F J := rfl

theorem conj_mem_NJ {J : Set (Fin (Tag.rank .E7))} {t : ModGL .E7 F} (ht : t ∈ torusGroup .E7 F)
    {η : ModGL .E7 F} (hη : η ∈ NJ F J) : t * η * t⁻¹ ∈ NJ F J := by
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  obtain ⟨hx, hy, -⟩ := root_diagonal_conjugation .E7 F b
  induction hη using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨j, hj, c, rfl | rfl⟩ := hg
    · rw [hx]
      exact Subgroup.subset_closure ⟨j, hj, _, Or.inl rfl⟩
    · rw [hy]
      exact Subgroup.subset_closure ⟨j, hj, _, Or.inr rfl⟩
  | one => simp
  | mul g₁ g₂ _ _ h₁ h₂ =>
    have : rootDiagUnit .E7 b * (g₁ * g₂) * (rootDiagUnit .E7 b)⁻¹ =
        (rootDiagUnit .E7 b * g₁ * (rootDiagUnit .E7 b)⁻¹) *
          (rootDiagUnit .E7 b * g₂ * (rootDiagUnit .E7 b)⁻¹) := by group
    rw [this]
    exact mul_mem h₁ h₂
  | inv g _ h =>
    have : rootDiagUnit .E7 b * g⁻¹ * (rootDiagUnit .E7 b)⁻¹ =
        (rootDiagUnit .E7 b * g * (rootDiagUnit .E7 b)⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem h

theorem exists_mul_of_mem_levi {J : Set (Fin (Tag.rank .E7))} {u : ModGL .E7 F}
    (hu : u ∈ parabolicLevi .E7 F J) :
    ∃ t ∈ torusGroup .E7 F, ∃ η ∈ NJ F J, u = t * η := by
  let P : Subgroup (ModGL .E7 F) :=
    { carrier := {x | ∃ t ∈ torusGroup .E7 F, ∃ η ∈ NJ F J, x = t * η}
      mul_mem' := by
        rintro _ _ ⟨t₁, ht₁, η₁, hη₁, rfl⟩ ⟨t₂, ht₂, η₂, hη₂, rfl⟩
        refine ⟨t₁ * t₂, mul_mem ht₁ ht₂, (t₂⁻¹ * η₁ * t₂) * η₂, ?_, ?_⟩
        · have := conj_mem_NJ (J := J) (inv_mem ht₂) hη₁
          rw [inv_inv] at this
          exact mul_mem this hη₂
        · group
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      inv_mem' := by
        rintro _ ⟨t, ht, η, hη, rfl⟩
        refine ⟨t⁻¹, inv_mem ht, t * η⁻¹ * t⁻¹, ?_, ?_⟩
        · exact conj_mem_NJ ht (inv_mem hη)
        · group }
  have hle : parabolicLevi .E7 F J ≤ P := by
    rw [parabolicLevi_eq_sup]
    exact sup_le (fun t ht => ⟨t, ht, 1, one_mem _, by simp⟩)
      (fun η hη => ⟨1, one_mem _, η, hη, by simp⟩)
  exact hle hu

end Decomposition

end CFSG.ClassicalInvolution.ModelFacts.E7Model
