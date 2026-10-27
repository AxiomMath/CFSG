module

public import CFSG.LieType.Chevalley.RankOneFaithful

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial

variable (τ : Tag) (K : Type) [Field K]

@[expose] def simpleRootSL2
    (i : Fin τ.rank) : SL2 K →* ModGL τ K :=
  (exceptional_ordinary_rank_one_central_image τ K i).choose

variable {τ K}

theorem simpleRootSL2_uSL
    (i : Fin τ.rank) (c : K) :
    simpleRootSL2 τ K i (uSL c) = xUnit τ K i c :=
  (exceptional_ordinary_rank_one_central_image τ K i).choose_spec.1 c

theorem simpleRootSL2_vSL
    (i : Fin τ.rank) (c : K) :
    simpleRootSL2 τ K i (vSL c) = yUnit τ K i c :=
  (exceptional_ordinary_rank_one_central_image τ K i).choose_spec.2.1 c

theorem simpleRootSL2_HSL
    (i : Fin τ.rank) (t : Kˣ) :
    simpleRootSL2 τ K i (HSL t) = torusElt τ K i t :=
  (exceptional_ordinary_rank_one_central_image τ K i).choose_spec.2.2.1 t

theorem simpleRootSL2_WSL
    (i : Fin τ.rank) : simpleRootSL2 τ K i WSL = weylElt τ K i 1 :=
  (exceptional_ordinary_rank_one_central_image τ K i).choose_spec.2.2.2.1

theorem range_simpleRootSL2
    (i : Fin τ.rank) :
    (simpleRootSL2 τ K i).range =
      Subgroup.closure (Set.range (xUnit τ K i) ∪ Set.range (yUnit τ K i)) :=
  (exceptional_ordinary_rank_one_central_image τ K i).choose_spec.2.2.2.2.1

theorem eq_simpleRootSL2
    (i : Fin τ.rank) {ρ : SL2 K →* ModGL τ K}
    (hu : ∀ c, ρ (uSL c) = xUnit τ K i c) (hv : ∀ c, ρ (vSL c) = yUnit τ K i c) :
    ρ = simpleRootSL2 τ K i :=
  MonoidHom.eq_of_eqOn_dense sl2_closure_upper_lower fun g hg => by
    rcases hg with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · exact (hu c).trans (simpleRootSL2_uSL i c).symm
    · exact (hv c).trans (simpleRootSL2_vSL i c).symm

theorem simpleRootSL2_mem_adjointGroup
    (i : Fin τ.rank) (A : SL2 K) :
    simpleRootSL2 τ K i A ∈ adjointGroup τ K := by
  have h : (simpleRootSL2 τ K i).range ≤ adjointGroup τ K := by
    rw [range_simpleRootSL2, Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    exacts [xUnit_mem_adjointGroup i c, yUnit_mem_adjointGroup i c]
  exact h ⟨A, rfl⟩

theorem simpleRootSL2_injective
    (hK : ringChar K ≠ 2) (i : Fin τ.rank) :
    Function.Injective (simpleRootSL2 τ K i) :=
  (odd_Chevalley_simple_root_SL2_faithful τ K hK i).1 _ (simpleRootSL2_uSL i)
    (simpleRootSL2_vSL i)

variable (τ K)

@[expose] def rootSL2
    (β : Fin τ.rank → ℤ) : SL2 K →* ModGL τ K :=
  (MulAut.conj (pinnedWeyl τ K β)).toMonoidHom.comp (simpleRootSL2 τ K (pinnedData τ β).1)

@[expose] def rootRankOneGroup
    (β : Fin τ.rank → ℤ) : Subgroup (ModGL τ K) :=
  (rootSL2 τ K β).range

@[expose] def rootTorusSL2
    (β : Fin τ.rank → ℤ) (c : Kˣ) : ModGL τ K :=
  rootSL2 τ K β (HSL c)

variable {K} in
@[expose] def nSL (c : Kˣ) : SL2 K :=
  ⟨!![0, (c : K); -((c⁻¹ : Kˣ) : K), 0], by simp [Matrix.det_fin_two]⟩

@[expose] def rootWeylSL2
    (β : Fin τ.rank → ℤ) (c : Kˣ) : ModGL τ K :=
  rootSL2 τ K β (nSL c)

variable {τ K}

theorem rootSL2_apply
    (β : Fin τ.rank → ℤ) (A : SL2 K) :
    rootSL2 τ K β A =
      pinnedWeyl τ K β * simpleRootSL2 τ K (pinnedData τ β).1 A * (pinnedWeyl τ K β)⁻¹ :=
  rfl

theorem nSL_one : nSL (1 : Kˣ) = WSL := by
  ext p q
  fin_cases p <;> fin_cases q <;> simp [nSL, WSL]

theorem nSL_eq_HSL_mul (c : Kˣ) : nSL c = HSL c * WSL := by
  ext p q
  rw [Matrix.SpecialLinearGroup.coe_mul]
  fin_cases p <;> fin_cases q <;> simp [nSL, HSL, WSL, Matrix.mul_apply, Fin.sum_univ_two]

theorem exceptional_Lang_root_rank_one_data
    (τ : Tag) (K : Type) [Field K] (β : Fin τ.rank → ℤ) :
    (∀ c, simpleRootSL2 τ K (pinnedData τ β).1 (uSL c) = xUnit τ K (pinnedData τ β).1 c) ∧
    (∀ c, simpleRootSL2 τ K (pinnedData τ β).1 (vSL c) = yUnit τ K (pinnedData τ β).1 c) ∧
    (∀ ρ : SL2 K →* ModGL τ K, (∀ c, ρ (uSL c) = xUnit τ K (pinnedData τ β).1 c) →
      (∀ c, ρ (vSL c) = yUnit τ K (pinnedData τ β).1 c) →
        ρ = simpleRootSL2 τ K (pinnedData τ β).1) ∧
    pinnedWeyl τ K β ∈ adjointGroup τ K ∧
    (∀ A : SL2 K, rootSL2 τ K β A ∈ adjointGroup τ K) ∧
    rootRankOneGroup τ K β ≤ adjointGroup τ K ∧
    (∀ c : Kˣ, rootTorusSL2 τ K β c ∈ adjointGroup τ K ∧ rootWeylSL2 τ K β c ∈ adjointGroup τ K) ∧
    (ringChar K ≠ 2 → Function.Injective (rootSL2 τ K β) ∧
      ∃ e : SL2 K ≃* rootRankOneGroup τ K β, ∀ A, (e A : ModGL τ K) = rootSL2 τ K β A) ∧
    (∀ c : Kˣ, rootTorusSL2 τ K β c =
      pinnedWeyl τ K β * torusElt τ K (pinnedData τ β).1 c * (pinnedWeyl τ K β)⁻¹) ∧
    rootWeylSL2 τ K β 1 =
      pinnedWeyl τ K β * weylElt τ K (pinnedData τ β).1 1 * (pinnedWeyl τ K β)⁻¹ ∧
    ∀ c : Kˣ, rootWeylSL2 τ K β c = rootTorusSL2 τ K β c * rootWeylSL2 τ K β 1 := by
  have hW := pinnedWeyl_mem_adjointGroup (K := K) β
  have hρ : ∀ A : SL2 K, rootSL2 τ K β A ∈ adjointGroup τ K := fun A =>
    mul_mem (mul_mem hW (simpleRootSL2_mem_adjointGroup _ A)) (inv_mem hW)
  refine ⟨simpleRootSL2_uSL _, simpleRootSL2_vSL _, fun ρ hu hv => eq_simpleRootSL2 _ hu hv, hW,
    hρ, ?_, fun c => ⟨hρ _, hρ _⟩, fun hK => ?_, fun c => ?_, ?_, fun c => ?_⟩
  · rintro _ ⟨A, rfl⟩
    exact hρ A
  · have hinj : Function.Injective (rootSL2 τ K β) := fun A B h => by
      rw [rootSL2_apply, rootSL2_apply] at h
      exact simpleRootSL2_injective hK _ (by simpa using h)
    exact ⟨hinj, MonoidHom.ofInjective hinj, fun A => rfl⟩
  · rw [rootTorusSL2, rootSL2_apply, simpleRootSL2_HSL]
  · rw [rootWeylSL2, nSL_one, rootSL2_apply, simpleRootSL2_WSL]
  · rw [rootWeylSL2, rootWeylSL2, rootTorusSL2, nSL_one, nSL_eq_HSL_mul, map_mul]

end CFSG.LieType.Chevalley
