module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Step3
public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.IrredF4Aux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

set_option linter.unusedSectionVars false


variable {τ : Tag} {K L : Type} [Field K] [Field L]

theorem pinnedX_mem_Qθ_of_Deg1 {β : Fin τ.rank → ℤ} (hβ : β ∈ Deg1 τ) (t : K) :
    pinnedX τ K β t ∈ Qθ τ K :=
  pinnedX_mem_rootSpan ((CoordAux.mem_radRoots_iff β).2 (Or.inl hβ)) t

theorem pinnedX_highRoot_mem_Qθ (t : K) : pinnedX τ K (highRoot τ) t ∈ Qθ τ K :=
  pinnedX_mem_rootSpan ((CoordAux.mem_radRoots_iff (highRoot τ)).2 (Or.inr rfl)) t

theorem Qθ_induction {P : ModGL τ K → Prop}
    (hone : P 1) (hmul : ∀ x y, x ∈ Qθ τ K → y ∈ Qθ τ K → P x → P y → P (x * y))
    (hinv : ∀ x, x ∈ Qθ τ K → P x → P x⁻¹)
    (h₁ : ∀ β ∈ Deg1 τ, ∀ t : K, P (pinnedX τ K β t))
    (h₂ : ∀ t : K, P (pinnedX τ K (highRoot τ) t)) :
    ∀ x ∈ Qθ τ K, P x := by
  let H : Subgroup (ModGL τ K) :=
    { carrier := {x | x ∈ Qθ τ K ∧ P x}
      mul_mem' := fun {x y} hx hy => ⟨mul_mem hx.1 hy.1, hmul x y hx.1 hy.1 hx.2 hy.2⟩
      one_mem' := ⟨one_mem _, hone⟩
      inv_mem' := fun {x} hx => ⟨inv_mem hx.1, hinv x hx.1 hx.2⟩ }
  have hle : Qθ τ K ≤ H := by
    show rootSpan τ K (parabolicRadicalRoots τ (Jθ τ)) ≤ H
    refine iSup₂_le fun α hα => ?_
    intro g hg
    obtain ⟨t, rfl⟩ := mem_rootSubgroup.1 hg
    rcases (CoordAux.mem_radRoots_iff α).1 hα with h | rfl
    · exact ⟨pinnedX_mem_Qθ_of_Deg1 h t, h₁ α h t⟩
    · exact ⟨pinnedX_highRoot_mem_Qθ t, h₂ t⟩
  exact fun x hx => (hle hx).2

theorem coord_baseChange (f : K →+* L) {q : ModGL τ K} (hq : q ∈ Qθ τ K) :
    baseChangeGL f q ∈ Qθ τ L ∧
      heisCoord τ L (baseChangeGL f q) = fun β => f (heisCoord τ K q β) := by
  refine Qθ_induction (P := fun x => baseChangeGL f x ∈ Qθ τ L ∧
      heisCoord τ L (baseChangeGL f x) = fun β => f (heisCoord τ K x β)) ?_ ?_ ?_ ?_ ?_ q hq
  · refine ⟨by rw [map_one]; exact one_mem _, ?_⟩
    rw [map_one, heisCoord_one, heisCoord_one]
    funext β
    simp
  · rintro x y hx hy ⟨hxQ, hxc⟩ ⟨hyQ, hyc⟩
    refine ⟨by rw [map_mul]; exact mul_mem hxQ hyQ, ?_⟩
    rw [map_mul, (heisCoord_spec τ L).mul _ hxQ _ hyQ, (heisCoord_spec τ K).mul _ hx _ hy, hxc,
      hyc]
    funext β
    simp only [Pi.add_apply, map_add]
  · rintro x hx ⟨hxQ, hxc⟩
    refine ⟨by rw [map_inv]; exact inv_mem hxQ, ?_⟩
    rw [map_inv, heisCoord_inv hxQ, heisCoord_inv hx, hxc]
    funext β
    simp only [Pi.neg_apply, map_neg]
  · intro β hβ t
    rw [baseChangeGL_pinnedX]
    refine ⟨pinnedX_mem_Qθ_of_Deg1 hβ _, ?_⟩
    rw [(heisCoord_spec τ L).pinnedX_deg1 β hβ, (heisCoord_spec τ K).pinnedX_deg1 β hβ]
    funext γ
    by_cases h : γ = β
    · subst h
      simp
    · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, map_zero]
  · intro t
    rw [baseChangeGL_pinnedX]
    refine ⟨pinnedX_highRoot_mem_Qθ _, ?_⟩
    rw [(heisCoord_spec τ L).pinnedX_highRoot, (heisCoord_spec τ K).pinnedX_highRoot]
    funext γ
    simp

theorem coord_frob (Fr : L →+* L) {q : ModGL τ L} (hq : q ∈ Qθ τ L) :
    Units.map (entrywiseHom Fr) q ∈ Qθ τ L ∧
      heisCoord τ L (Units.map (entrywiseHom Fr) q) = fun β => Fr (heisCoord τ L q β) := by
  have e : Units.map (entrywiseHom Fr) q = baseChangeGL Fr q := Units.ext rfl
  rw [e]
  exact coord_baseChange Fr hq

theorem scalarTorus_conj_Qθ (c : Kˣ) {q : ModGL τ K} (hq : q ∈ Qθ τ K) :
    rootTorusSL2 τ K (highRoot τ) c * q * (rootTorusSL2 τ K (highRoot τ) c)⁻¹ ∈ Qθ τ K ∧
      heisCoord τ K (rootTorusSL2 τ K (highRoot τ) c * q * (rootTorusSL2 τ K (highRoot τ) c)⁻¹) =
        (c : K) • heisCoord τ K q := by
  set h := rootTorusSL2 τ K (highRoot τ) c
  refine Qθ_induction (P := fun x => h * x * h⁻¹ ∈ Qθ τ K ∧
      heisCoord τ K (h * x * h⁻¹) = (c : K) • heisCoord τ K x) ?_ ?_ ?_ ?_ ?_ q hq
  · rw [mul_one, mul_inv_cancel, heisCoord_one, smul_zero]
    exact ⟨one_mem _, rfl⟩
  · rintro x y hx hy ⟨hxQ, hxc⟩ ⟨hyQ, hyc⟩
    have e : h * (x * y) * h⁻¹ = (h * x * h⁻¹) * (h * y * h⁻¹) := by group
    refine ⟨by rw [e]; exact mul_mem hxQ hyQ, ?_⟩
    rw [e, (heisCoord_spec τ K).mul _ hxQ _ hyQ, (heisCoord_spec τ K).mul _ hx _ hy, hxc, hyc,
      smul_add]
  · rintro x hx ⟨hxQ, hxc⟩
    have e : h * x⁻¹ * h⁻¹ = (h * x * h⁻¹)⁻¹ := by group
    refine ⟨by rw [e]; exact inv_mem hxQ, ?_⟩
    rw [e, heisCoord_inv hxQ, heisCoord_inv hx, hxc, smul_neg]
  · intro β hβ t
    have hconj := ScalarTorusAux.torus_conj_pinnedX (isRoot_highRoot τ) (CoordAux.mem_Deg1.1 hβ).1
      c t
    rw [ScalarTorusAux.exponent_of_Deg1 hβ, zpow_one] at hconj
    rw [hconj]
    refine ⟨pinnedX_mem_Qθ_of_Deg1 hβ _, ?_⟩
    rw [(heisCoord_spec τ K).pinnedX_deg1 β hβ, (heisCoord_spec τ K).pinnedX_deg1 β hβ]
    ext γ
    by_cases hγ : γ = β
    · subst hγ
      simp
    · simp [Pi.single_apply, hγ]
  · intro t
    rw [ScalarTorusAux.torus_conj_pinnedX (isRoot_highRoot τ) (isRoot_highRoot τ) c t]
    refine ⟨pinnedX_highRoot_mem_Qθ _, ?_⟩
    rw [(heisCoord_spec τ K).pinnedX_highRoot, (heisCoord_spec τ K).pinnedX_highRoot, smul_zero]

open CFSG.LieType.Steinberg.Adjoint in
theorem scalarTorus_comm_pinnedX_of_deg_zero {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (h0 : α (iθ τ) = 0) (c : Lˣ) (z : L) :
    rootTorusSL2 τ L (highRoot τ) c * pinnedX τ L α z =
      pinnedX τ L α z * rootTorusSL2 τ L (highRoot τ) c := by
  have hconj := ScalarTorusAux.torus_conj_pinnedX (isRoot_highRoot τ) hα c z
  have h1 : iform (highRoot τ) α = 0 := by rw [iform_highRoot_apply, h0, mul_zero]
  rw [h1, mul_zero, Int.zero_ediv, zpow_zero, Units.val_one, one_mul] at hconj
  exact mul_inv_eq_iff_eq_mul.1 hconj

theorem Lθ_comm_scalarTorus {l : ModGL τ L} (hl : l ∈ Lθ τ L) (c : Lˣ) :
    l * rootTorusSL2 τ L (highRoot τ) c = rootTorusSL2 τ L (highRoot τ) c * l := by
  obtain ⟨-, hdH, -⟩ := exceptional_Lang_root_rank_one_torus_transport τ L (isRoot_highRoot τ)
  have hle : Lθ τ L ≤ Subgroup.centralizer {rootTorusSL2 τ L (highRoot τ) c} := by
    refine sup_le (fun t ht => ?_) ((Subgroup.closure_le _).2 ?_)
    · rw [Subgroup.mem_centralizer_iff]
      rintro _ rfl
      exact mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup (hdH c))
        (torusGroup_le_diagonalGroup ht)
    · rintro _ ⟨j, hj, s, rfl | rfl⟩
      · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        rintro _ rfl
        rw [← pinnedX_single]
        refine scalarTorus_comm_pinnedX_of_deg_zero (isRoot_single τ j) ?_ c s
        exact Pi.single_eq_of_ne (Ne.symm hj) 1
      · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        rintro _ rfl
        rw [← pinnedX_neg_single]
        refine scalarTorus_comm_pinnedX_of_deg_zero (isRoot_neg_single τ j) ?_ c s
        rw [Pi.neg_apply, Pi.single_eq_of_ne (Ne.symm hj) 1, neg_zero]
  exact ((Subgroup.mem_centralizer_iff.1 (hle hl)) _ rfl).symm

theorem levi_conj_pinnedX_Deg1 {l : ModGL τ L} (hl : l ∈ Lθ τ L) {β : Fin τ.rank → ℤ}
    (hβ : β ∈ Deg1 τ) (z : L) :
    l * pinnedX τ L β z * l⁻¹ ∈ Qθ τ L ∧
      heisCoord τ L (l * pinnedX τ L β z * l⁻¹) =
        z • heisCoord τ L (l * pinnedX τ L β 1 * l⁻¹) := by
  have hQ1 : l * pinnedX τ L β 1 * l⁻¹ ∈ Qθ τ L :=
    Lθ_conj_mem_Qθ hl (pinnedX_mem_Qθ_of_Deg1 hβ 1)
  by_cases hz : z = 0
  · subst hz
    rw [pinnedX_zero, mul_one, mul_inv_cancel, heisCoord_one, zero_smul]
    exact ⟨one_mem _, rfl⟩
  · set h := rootTorusSL2 τ L (highRoot τ) (Units.mk0 z hz)
    have hconj := ScalarTorusAux.torus_conj_pinnedX (isRoot_highRoot τ)
      (CoordAux.mem_Deg1.1 hβ).1 (Units.mk0 z hz) 1
    rw [ScalarTorusAux.exponent_of_Deg1 hβ, zpow_one, Units.val_mk0, mul_one] at hconj
    have hc : l * h = h * l := Lθ_comm_scalarTorus hl _
    have e : l * pinnedX τ L β z * l⁻¹ = h * (l * pinnedX τ L β 1 * l⁻¹) * h⁻¹ := by
      rw [← hconj]
      calc l * (h * pinnedX τ L β 1 * h⁻¹) * l⁻¹
          = (l * h) * pinnedX τ L β 1 * (l * h)⁻¹ := by group
        _ = (h * l) * pinnedX τ L β 1 * (h * l)⁻¹ := by rw [hc]
        _ = h * (l * pinnedX τ L β 1 * l⁻¹) * h⁻¹ := by group
    obtain ⟨hs1, hs2⟩ := scalarTorus_conj_Qθ (Units.mk0 z hz) hQ1
    rw [e]
    exact ⟨hs1, by rw [hs2, Units.val_mk0]⟩

theorem levi_action {l : ModGL τ L} (hl : l ∈ Lθ τ L) :
    ∃ f : ((Fin τ.rank → ℤ) → L) →ₗ[L] ((Fin τ.rank → ℤ) → L), ∀ q ∈ Qθ τ L,
      l * q * l⁻¹ ∈ Qθ τ L ∧ heisCoord τ L (l * q * l⁻¹) = f (heisCoord τ L q) := by
  classical
  let F : ((Fin τ.rank → ℤ) → L) →ₗ[L] ((Fin τ.rank → ℤ) → L) :=
    ∑ β ∈ rootFinset τ, (LinearMap.proj β : ((Fin τ.rank → ℤ) → L) →ₗ[L] L).smulRight
      (heisCoord τ L (l * pinnedX τ L β 1 * l⁻¹))
  have hF : ∀ v : (Fin τ.rank → ℤ) → L, F v =
      ∑ β ∈ rootFinset τ, v β • heisCoord τ L (l * pinnedX τ L β 1 * l⁻¹) := by
    intro v
    simp [F, LinearMap.sum_apply]
  have hFsingle : ∀ β ∈ Deg1 τ, ∀ z : L, F (Pi.single β z) =
      z • heisCoord τ L (l * pinnedX τ L β 1 * l⁻¹) := by
    intro β hβ z
    rw [hF, Finset.sum_eq_single β]
    · rw [Pi.single_eq_same]
    · intro γ _ hγ
      rw [Pi.single_eq_of_ne hγ, zero_smul]
    · intro h
      exact absurd (mem_rootFinset.2 (CoordAux.mem_Deg1.1 hβ).1) h
  refine ⟨F, Qθ_induction (P := fun q => l * q * l⁻¹ ∈ Qθ τ L ∧
      heisCoord τ L (l * q * l⁻¹) = F (heisCoord τ L q)) ?_ ?_ ?_ ?_ ?_⟩
  · refine ⟨by rw [mul_one, mul_inv_cancel]; exact one_mem _, ?_⟩
    rw [mul_one, mul_inv_cancel, heisCoord_one, map_zero]
  · rintro x y hx hy ⟨hxQ, hxc⟩ ⟨hyQ, hyc⟩
    have e : l * (x * y) * l⁻¹ = (l * x * l⁻¹) * (l * y * l⁻¹) := by group
    refine ⟨by rw [e]; exact mul_mem hxQ hyQ, ?_⟩
    rw [e, (heisCoord_spec τ L).mul _ hxQ _ hyQ, (heisCoord_spec τ L).mul _ hx _ hy, hxc, hyc,
      map_add]
  · rintro x hx ⟨hxQ, hxc⟩
    have e : l * x⁻¹ * l⁻¹ = (l * x * l⁻¹)⁻¹ := by group
    refine ⟨by rw [e]; exact inv_mem hxQ, ?_⟩
    rw [e, heisCoord_inv hxQ, heisCoord_inv hx, hxc, map_neg]
  · intro β hβ t
    obtain ⟨h1, h2⟩ := levi_conj_pinnedX_Deg1 hl hβ t
    refine ⟨h1, ?_⟩
    rw [h2, (heisCoord_spec τ L).pinnedX_deg1 β hβ, hFsingle β hβ t]
  · intro t
    have hU : l * pinnedX τ L (highRoot τ) t * l⁻¹ ∈ Uθ τ L :=
      Lθ_conj_mem_Uθ hl (mem_rootSubgroup.2 ⟨t, rfl⟩)
    obtain ⟨t', ht'⟩ := mem_rootSubgroup.1 hU
    rw [← ht']
    refine ⟨pinnedX_highRoot_mem_Qθ _, ?_⟩
    rw [(heisCoord_spec τ L).pinnedX_highRoot, (heisCoord_spec τ L).pinnedX_highRoot, map_zero]

theorem degθ_smul_of_fix {w : WeylGroup τ} (hw : w • highRoot τ = highRoot τ)
    (β : Fin τ.rank → ℤ) : (w • β) (iθ τ) = β (iθ τ) := by
  have h := CFSG.LieType.Chevalley.iform_smul w (highRoot τ) β
  rw [hw, iform_highRoot_apply, iform_highRoot_apply] at h
  exact mul_left_cancel₀ (cθ_ne_zero τ) h

open Classical in
theorem coord_conj_n {w : WeylGroup τ} (hw : w • highRoot τ = highRoot τ) :
    ∃ ε : (Fin τ.rank → ℤ) → L, (∀ α, IsRoot τ α → ε α * ε α = 1) ∧
      ∀ q ∈ Qθ τ L,
        (canonicalRep (coxeterSystem τ) L w)⁻¹ * q * canonicalRep (coxeterSystem τ) L w ∈ Qθ τ L ∧
        ∀ α, heisCoord τ L
            ((canonicalRep (coxeterSystem τ) L w)⁻¹ * q * canonicalRep (coxeterSystem τ) L w) α =
          if α ∈ Deg1 τ then ε α * heisCoord τ L q (w • α) else 0 := by
  have hex : ∀ β : Fin τ.rank → ℤ, ∃ e : L, IsRoot τ β → e * e = 1 ∧ ∀ c : L,
      canonicalRep (coxeterSystem τ) L w * pinnedX τ L β c *
        (canonicalRep (coxeterSystem τ) L w)⁻¹ = pinnedX τ L (w • β) (e * c) := by
    intro β
    by_cases hβ : IsRoot τ β
    · obtain ⟨e, he, hc⟩ := exists_canonicalRep_mul_pinnedX_mul_inv L w hβ
      exact ⟨e, fun _ => ⟨he, hc⟩⟩
    · exact ⟨1, fun h => absurd h hβ⟩
  choose ε hε using hex
  refine ⟨ε, fun β hβ => (hε β hβ).1, ?_⟩
  generalize canonicalRep (coxeterSystem τ) L w = n at hε ⊢
  have hw' : w⁻¹ • highRoot τ = highRoot τ := inv_smul_eq_iff.2 hw.symm
  have hconj : ∀ μ : Fin τ.rank → ℤ, IsRoot τ μ → ∀ c : L,
      n⁻¹ * pinnedX τ L μ c * n = pinnedX τ L (w⁻¹ • μ) (ε (w⁻¹ • μ) * c) := by
    intro μ hμ c
    have hα : IsRoot τ (w⁻¹ • μ) := IsRoot.smul hμ w⁻¹
    obtain ⟨hεε, hεc⟩ := hε _ hα
    have h1 := hεc (ε (w⁻¹ • μ) * c)
    rw [smul_inv_smul, ← mul_assoc, hεε, one_mul] at h1
    rw [← h1]
    group
  refine Qθ_induction ?_ ?_ ?_ ?_ ?_
  · refine ⟨by rw [mul_one, inv_mul_cancel]; exact one_mem _, fun α => ?_⟩
    rw [mul_one, inv_mul_cancel, heisCoord_one, Pi.zero_apply, Pi.zero_apply, mul_zero, ite_self]
  · rintro x y hx hy ⟨hxQ, hxc⟩ ⟨hyQ, hyc⟩
    have e : n⁻¹ * (x * y) * n = (n⁻¹ * x * n) * (n⁻¹ * y * n) := by group
    refine ⟨by rw [e]; exact mul_mem hxQ hyQ, fun α => ?_⟩
    rw [e, (heisCoord_spec τ L).mul _ hxQ _ hyQ, (heisCoord_spec τ L).mul _ hx _ hy, Pi.add_apply,
      Pi.add_apply, hxc α, hyc α]
    by_cases hα : α ∈ Deg1 τ
    · rw [if_pos hα, if_pos hα, if_pos hα, mul_add]
    · rw [if_neg hα, if_neg hα, if_neg hα, add_zero]
  · rintro x hx ⟨hxQ, hxc⟩
    have e : n⁻¹ * x⁻¹ * n = (n⁻¹ * x * n)⁻¹ := by group
    refine ⟨by rw [e]; exact inv_mem hxQ, fun α => ?_⟩
    rw [e, heisCoord_inv hxQ, heisCoord_inv hx, Pi.neg_apply, Pi.neg_apply, hxc α]
    by_cases hα : α ∈ Deg1 τ
    · rw [if_pos hα, if_pos hα, mul_neg]
    · rw [if_neg hα, if_neg hα, neg_zero]
  · intro μ hμ t
    have hμr : IsRoot τ μ := (CoordAux.mem_Deg1.1 hμ).1
    have hαD : w⁻¹ • μ ∈ Deg1 τ :=
      CoordAux.mem_Deg1.2 ⟨IsRoot.smul hμr w⁻¹, by
        rw [degθ_smul_of_fix hw' μ]; exact (CoordAux.mem_Deg1.1 hμ).2⟩
    rw [hconj μ hμr t]
    refine ⟨pinnedX_mem_Qθ_of_Deg1 hαD _, fun γ => ?_⟩
    rw [(heisCoord_spec τ L).pinnedX_deg1 _ hαD, (heisCoord_spec τ L).pinnedX_deg1 μ hμ]
    by_cases hγ : γ = w⁻¹ • μ
    · subst hγ
      rw [if_pos hαD, Pi.single_eq_same, smul_inv_smul, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hγ]
      by_cases hγD : γ ∈ Deg1 τ
      · have hne : w • γ ≠ μ := fun h => hγ (by rw [← h, inv_smul_smul])
        rw [if_pos hγD, Pi.single_eq_of_ne hne, mul_zero]
      · rw [if_neg hγD]
  · intro t
    have hθ := isRoot_highRoot τ
    rw [hconj _ hθ t, hw']
    refine ⟨pinnedX_highRoot_mem_Qθ _, fun γ => ?_⟩
    rw [(heisCoord_spec τ L).pinnedX_highRoot, (heisCoord_spec τ L).pinnedX_highRoot,
      Pi.zero_apply, Pi.zero_apply, mul_zero, ite_self]

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.IrredF4Aux
