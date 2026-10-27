module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ScalarTorus
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.Normalizer

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.IrE8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

set_option linter.unusedSectionVars false


variable {τ : Tag}

namespace HeisActAux

variable {F : Type} [Field F]

private theorem Qθ_induction {P : ModGL τ F → Prop}
    (hone : P 1) (hmul : ∀ x y, x ∈ Qθ τ F → y ∈ Qθ τ F → P x → P y → P (x * y))
    (hinv : ∀ x, x ∈ Qθ τ F → P x → P x⁻¹)
    (h₁ : ∀ β ∈ Deg1 τ, ∀ t : F, P (pinnedX τ F β t))
    (h₂ : ∀ t : F, P (pinnedX τ F (highRoot τ) t)) :
    ∀ x ∈ Qθ τ F, P x := by
  let H : Subgroup (ModGL τ F) :=
    { carrier := {x | x ∈ Qθ τ F ∧ P x}
      mul_mem' := fun {x y} hx hy => ⟨mul_mem hx.1 hy.1, hmul x y hx.1 hy.1 hx.2 hy.2⟩
      one_mem' := ⟨one_mem _, hone⟩
      inv_mem' := fun {x} hx => ⟨inv_mem hx.1, hinv x hx.1 hx.2⟩ }
  have hle : Qθ τ F ≤ H := by
    show rootSpan τ F (parabolicRadicalRoots τ (Jθ τ)) ≤ H
    refine iSup₂_le fun α hα => ?_
    intro g hg
    obtain ⟨t, rfl⟩ := mem_rootSubgroup.1 hg
    rcases (CoordAux.mem_radRoots_iff α).1 hα with h | rfl
    · exact ⟨pinnedX_mem_rootSpan hα t, h₁ α h t⟩
    · exact ⟨pinnedX_mem_rootSpan hα t, h₂ t⟩
  exact fun x hx => (hle hx).2

private theorem pinnedX_mem_Qθ {β : Fin τ.rank → ℤ} (hβ : β ∈ Deg1 τ) (t : F) :
    pinnedX τ F β t ∈ Qθ τ F :=
  pinnedX_mem_rootSpan ((CoordAux.mem_radRoots_iff β).2 (Or.inl hβ)) t

private theorem pinnedX_highRoot_mem_Qθ (t : F) : pinnedX τ F (highRoot τ) t ∈ Qθ τ F :=
  pinnedX_mem_rootSpan ((CoordAux.mem_radRoots_iff (highRoot τ)).2 (Or.inr rfl)) t

private theorem conj_mem_Qθ {l q : ModGL τ F} (hl : l ∈ Lθ τ F) (hq : q ∈ Qθ τ F) :
    l * q * l⁻¹ ∈ Qθ τ F :=
  (Subgroup.mem_normalizer_iff.1 (parabolicSubgroup_le_normalizer_parabolicRadical (τ := τ)
    (K := F) (Jθ τ) (parabolicLevi_le_parabolicSubgroup (Jθ τ) hl)) q).1 hq

private theorem conj_mem_Uθ {l u : ModGL τ F} (hl : l ∈ Lθ τ F) (hu : u ∈ Uθ τ F) :
    l * u * l⁻¹ ∈ Uθ τ F :=
  (Subgroup.mem_normalizer_iff.1 (Pθ_le_normalizer_Uθ τ F
    (parabolicLevi_le_parabolicSubgroup (Jθ τ) hl)) u).1 hu

private theorem torus_conj_Qθ (c : Fˣ) {q : ModGL τ F} (hq : q ∈ Qθ τ F) :
    heisCoord τ F (rootTorusSL2 τ F (highRoot τ) c * q * (rootTorusSL2 τ F (highRoot τ) c)⁻¹) =
      (c : F) • heisCoord τ F q := by
  generalize hh : rootTorusSL2 τ F (highRoot τ) c = h
  refine (Qθ_induction (P := fun x => h * x * h⁻¹ ∈ Qθ τ F ∧
      heisCoord τ F (h * x * h⁻¹) = (c : F) • heisCoord τ F x) ?_ ?_ ?_ ?_ ?_ q hq).2
  · rw [mul_one, mul_inv_cancel, heisCoord_one, smul_zero]
    exact ⟨one_mem _, rfl⟩
  · rintro x y hx hy ⟨hxQ, hxc⟩ ⟨hyQ, hyc⟩
    have e : h * (x * y) * h⁻¹ = (h * x * h⁻¹) * (h * y * h⁻¹) := by group
    refine ⟨by rw [e]; exact mul_mem hxQ hyQ, ?_⟩
    rw [e, (heisCoord_spec τ F).mul _ hxQ _ hyQ, (heisCoord_spec τ F).mul _ hx _ hy, hxc, hyc,
      smul_add]
  · rintro x hx ⟨hxQ, hxc⟩
    have e : h * x⁻¹ * h⁻¹ = (h * x * h⁻¹)⁻¹ := by group
    refine ⟨by rw [e]; exact inv_mem hxQ, ?_⟩
    rw [e, heisCoord_inv hxQ, heisCoord_inv hx, hxc, smul_neg]
  · intro β hβ t
    have hconj := ScalarTorusAux.torus_conj_pinnedX (isRoot_highRoot τ)
      (CoordAux.mem_Deg1.1 hβ).1 c t
    rw [ScalarTorusAux.exponent_of_Deg1 hβ, zpow_one, hh] at hconj
    rw [hconj]
    refine ⟨pinnedX_mem_Qθ hβ _, ?_⟩
    rw [(heisCoord_spec τ F).pinnedX_deg1 β hβ, (heisCoord_spec τ F).pinnedX_deg1 β hβ]
    ext γ
    by_cases hγ : γ = β
    · subst hγ
      simp
    · simp [Pi.single_apply, hγ]
  · intro t
    have hconj := ScalarTorusAux.torus_conj_pinnedX (isRoot_highRoot τ) (isRoot_highRoot τ) c t
    rw [hh] at hconj
    rw [hconj]
    refine ⟨pinnedX_highRoot_mem_Qθ _, ?_⟩
    rw [(heisCoord_spec τ F).pinnedX_highRoot, (heisCoord_spec τ F).pinnedX_highRoot, smul_zero]

open CFSG.LieType.Steinberg.Adjoint in
private theorem torus_comm_pinnedX {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (h0 : α (iθ τ) = 0) (c : Fˣ) (z : F) :
    rootTorusSL2 τ F (highRoot τ) c * pinnedX τ F α z =
      pinnedX τ F α z * rootTorusSL2 τ F (highRoot τ) c := by
  have hconj := ScalarTorusAux.torus_conj_pinnedX (isRoot_highRoot τ) hα c z
  have h1 : iform (highRoot τ) α = 0 := by rw [iform_highRoot_apply, h0, mul_zero]
  rw [h1, mul_zero, Int.zero_ediv, zpow_zero, Units.val_one, one_mul] at hconj
  exact mul_inv_eq_iff_eq_mul.1 hconj

private theorem comm_torus {l : ModGL τ F} (hl : l ∈ Lθ τ F) (c : Fˣ) :
    l * rootTorusSL2 τ F (highRoot τ) c = rootTorusSL2 τ F (highRoot τ) c * l := by
  obtain ⟨-, hdH, -⟩ := exceptional_Lang_root_rank_one_torus_transport τ F (isRoot_highRoot τ)
  have hle : Lθ τ F ≤ Subgroup.centralizer {rootTorusSL2 τ F (highRoot τ) c} := by
    refine sup_le (fun t ht => ?_) ((Subgroup.closure_le _).2 ?_)
    · rw [Subgroup.mem_centralizer_iff]
      rintro _ rfl
      exact mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup (hdH c))
        (torusGroup_le_diagonalGroup ht)
    · rintro _ ⟨j, hj, s, rfl | rfl⟩
      · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        rintro _ rfl
        rw [← pinnedX_single]
        exact torus_comm_pinnedX (isRoot_single τ j)
          (Pi.single_eq_of_ne (Ne.symm (show j ≠ iθ τ from hj)) 1) c s
      · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        rintro _ rfl
        rw [← pinnedX_neg_single]
        refine torus_comm_pinnedX (isRoot_neg_single τ j) ?_ c s
        rw [Pi.neg_apply, Pi.single_eq_of_ne (Ne.symm (show j ≠ iθ τ from hj)) 1, neg_zero]
  exact ((Subgroup.mem_centralizer_iff.1 (hle hl)) _ rfl).symm

private theorem conj_pinnedX_Deg1 {l : ModGL τ F} (hl : l ∈ Lθ τ F) {β : Fin τ.rank → ℤ}
    (hβ : β ∈ Deg1 τ) (z : F) :
    heisCoord τ F (l * pinnedX τ F β z * l⁻¹) =
      z • heisCoord τ F (l * pinnedX τ F β 1 * l⁻¹) := by
  by_cases hz : z = 0
  · subst hz
    rw [pinnedX_zero, mul_one, mul_inv_cancel, heisCoord_one, zero_smul]
  · have hconj := ScalarTorusAux.torus_conj_pinnedX (isRoot_highRoot τ)
      (CoordAux.mem_Deg1.1 hβ).1 (Units.mk0 z hz) 1
    rw [ScalarTorusAux.exponent_of_Deg1 hβ, zpow_one, Units.val_mk0, mul_one] at hconj
    have hc := comm_torus hl (Units.mk0 z hz)
    have hs := torus_conj_Qθ (Units.mk0 z hz) (conj_mem_Qθ hl (pinnedX_mem_Qθ hβ (1 : F)))
    rw [Units.val_mk0] at hs
    rw [← hs, ← hconj]
    congr 1
    generalize rootTorusSL2 τ F (highRoot τ) (Units.mk0 z hz) = h at hc ⊢
    calc l * (h * pinnedX τ F β 1 * h⁻¹) * l⁻¹
        = (l * h) * pinnedX τ F β 1 * (l * h)⁻¹ := by group
      _ = (h * l) * pinnedX τ F β 1 * (h * l)⁻¹ := by rw [hc]
      _ = h * (l * pinnedX τ F β 1 * l⁻¹) * h⁻¹ := by group

end HeisActAux

open HeisActAux in
theorem exists_heisAct (F : Type) [Field F] {l : ModGL τ F} (hl : l ∈ Lθ τ F) :
    ∃ A : ((Fin τ.rank → ℤ) → F) →ₗ[F] ((Fin τ.rank → ℤ) → F),
      (∀ v ν, ν ∉ Deg1 τ → A v ν = 0) ∧
      ∀ q ∈ Qθ τ F, l * q * l⁻¹ ∈ Qθ τ F ∧
        heisCoord τ F (l * q * l⁻¹) = A (heisCoord τ F q) := by
  classical
  obtain ⟨L₁, -, hmem₁⟩ := CoordAux.exists_list_Deg1 (τ := τ)
  let c : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ) → F :=
    fun β => heisCoord τ F (l * pinnedX τ F β 1 * l⁻¹)
  let A : ((Fin τ.rank → ℤ) → F) →ₗ[F] ((Fin τ.rank → ℤ) → F) :=
    ∑ β ∈ L₁.toFinset, (LinearMap.proj β : ((Fin τ.rank → ℤ) → F) →ₗ[F] F).smulRight (c β)
  have hA : ∀ v : (Fin τ.rank → ℤ) → F, A v = ∑ β ∈ L₁.toFinset, v β • c β := by
    intro v
    simp only [A, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]
  have hsingle : ∀ β ∈ Deg1 τ, ∀ z : F, A (Pi.single β z) = z • c β := by
    intro β hβ z
    rw [hA, Finset.sum_eq_single β]
    · rw [Pi.single_eq_same]
    · intro γ _ hγ
      rw [Pi.single_eq_of_ne hγ, zero_smul]
    · intro h
      exact absurd (List.mem_toFinset.2 ((hmem₁ β).2 hβ)) h
  refine ⟨A, fun v ν hν => ?_, Qθ_induction (P := fun q => l * q * l⁻¹ ∈ Qθ τ F ∧
      heisCoord τ F (l * q * l⁻¹) = A (heisCoord τ F q)) ?_ ?_ ?_ ?_ ?_⟩
  · rw [hA, Finset.sum_apply]
    refine Finset.sum_eq_zero fun β hβ => ?_
    have hβD : β ∈ Deg1 τ := (hmem₁ β).1 (List.mem_toFinset.1 hβ)
    rw [Pi.smul_apply, show c β ν = 0 from
      (heisCoord_spec τ F).support _ (conj_mem_Qθ hl (pinnedX_mem_Qθ hβD 1)) ν hν, smul_zero]
  · refine ⟨by rw [mul_one, mul_inv_cancel]; exact one_mem _, ?_⟩
    rw [mul_one, mul_inv_cancel, heisCoord_one, map_zero]
  · rintro x y hx hy ⟨hxQ, hxc⟩ ⟨hyQ, hyc⟩
    have e : l * (x * y) * l⁻¹ = (l * x * l⁻¹) * (l * y * l⁻¹) := by group
    refine ⟨by rw [e]; exact mul_mem hxQ hyQ, ?_⟩
    rw [e, (heisCoord_spec τ F).mul _ hxQ _ hyQ, (heisCoord_spec τ F).mul _ hx _ hy, hxc, hyc,
      map_add]
  · rintro x hx ⟨hxQ, hxc⟩
    have e : l * x⁻¹ * l⁻¹ = (l * x * l⁻¹)⁻¹ := by group
    refine ⟨by rw [e]; exact inv_mem hxQ, ?_⟩
    rw [e, heisCoord_inv hxQ, heisCoord_inv hx, hxc, map_neg]
  · intro β hβ t
    refine ⟨conj_mem_Qθ hl (pinnedX_mem_Qθ hβ t), ?_⟩
    rw [conj_pinnedX_Deg1 hl hβ t, (heisCoord_spec τ F).pinnedX_deg1 β hβ, hsingle β hβ t]
  · intro t
    have hU : l * pinnedX τ F (highRoot τ) t * l⁻¹ ∈ Uθ τ F :=
      conj_mem_Uθ hl (mem_rootSubgroup.2 ⟨t, rfl⟩)
    obtain ⟨t', ht'⟩ := mem_rootSubgroup.1 hU
    rw [← ht']
    refine ⟨pinnedX_highRoot_mem_Qθ _, ?_⟩
    rw [(heisCoord_spec τ F).pinnedX_highRoot, (heisCoord_spec τ F).pinnedX_highRoot, map_zero]

theorem heisAct_inv_left {F : Type} [Field F] {l : ModGL τ F}
    {A A' : ((Fin τ.rank → ℤ) → F) →ₗ[F] ((Fin τ.rank → ℤ) → F)}
    (hA : ∀ q ∈ Qθ τ F, l * q * l⁻¹ ∈ Qθ τ F ∧ heisCoord τ F (l * q * l⁻¹) = A (heisCoord τ F q))
    (hA' : ∀ q ∈ Qθ τ F, l⁻¹ * q * l ∈ Qθ τ F ∧
      heisCoord τ F (l⁻¹ * q * l) = A' (heisCoord τ F q))
    {v : (Fin τ.rank → ℤ) → F} (hv : ∀ ν, ν ∉ Deg1 τ → v ν = 0) : A' (A v) = v := by
  obtain ⟨q, hq, rfl⟩ := (heisCoord_spec τ F).surj v hv
  obtain ⟨h1, h2⟩ := hA q hq
  rw [← h2, ← (hA' _ h1).2, show l⁻¹ * (l * q * l⁻¹) * l = q by group]

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.IrE8
