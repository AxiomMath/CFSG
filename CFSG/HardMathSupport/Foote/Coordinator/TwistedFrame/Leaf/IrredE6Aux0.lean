module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Frame
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Step3
public import CFSG.LieType.Chevalley.GraphFixedF4GroupDescent
public import CFSG.RankThree.PartOne.KE.A2Shape

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.IrredE6Aux

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

theorem sep {E M : Type*} [Field E] [AddCommGroup M] [Module E M] (N : Submodule E M)
    (A : Finset E) (d : ℕ) (hA : d < A.card) (w : ℕ → M)
    (h : ∀ a ∈ A, ∑ k ∈ Finset.range (d + 1), a ^ k • w k ∈ N) : ∀ k ≤ d, w k ∈ N := by
  classical
  intro k hk
  have key : ∀ φ : Module.Dual E (M ⧸ N), φ (N.mkQ (w k)) = 0 := by
    intro φ
    have hpoly : ∑ j ∈ Finset.range (d + 1),
        Polynomial.C (φ (N.mkQ (w j))) * Polynomial.X ^ j = 0 := by
      refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ A (fun a ha => ?_) ?_
      · have h1 : N.mkQ (∑ j ∈ Finset.range (d + 1), a ^ j • w j) = 0 := by
          rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
          exact h a ha
        have h2 := congrArg φ h1
        simp only [map_sum, map_smul, smul_eq_mul, map_zero] at h2
        rw [Polynomial.eval_finsetSum]
        refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) h2
        rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
          mul_comm]
      · refine lt_of_le_of_lt (Polynomial.natDegree_sum_le_of_forall_le _ _ fun j hj => ?_) hA
        exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans
          (Nat.lt_add_one_iff.1 (Finset.mem_range.1 hj))
    have hk' : k < d + 1 := Nat.lt_add_one_iff.2 hk
    have := congrArg (fun p => Polynomial.coeff p k) hpoly
    simpa [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, hk'] using this
  have := (Module.forall_dual_apply_eq_zero_iff E (N.mkQ (w k))).1 key
  rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this

theorem sep_inj {E M ι : Type*} [Field E] [AddCommGroup M] [Module E M] [Fintype ι]
    (N : Submodule E M) (A : Finset E) (d : ℕ) (hA : d < A.card) (ex : ι → ℕ)
    (hex : Function.Injective ex) (hd : ∀ i, ex i ≤ d) (z : ι → M)
    (h : ∀ a ∈ A, ∑ i, a ^ ex i • z i ∈ N) : ∀ i, z i ∈ N := by
  classical
  intro i
  have hw := sep N A d hA (fun k => ∑ j, if ex j = k then z j else 0) (fun a ha => ?_) (ex i) (hd i)
  · have hzi : (∑ j, if ex j = ex i then z j else 0) = z i := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        simp [hex.eq_iff, hj]
      · simp
    simpa [hzi] using hw
  · have hsum : ∑ k ∈ Finset.range (d + 1), a ^ k • (∑ j, if ex j = k then z j else 0) =
        ∑ j, a ^ ex j • z j := by
      simp only [Finset.smul_sum, smul_ite, smul_zero]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_ite_eq]
      simp [Nat.lt_add_one_iff.2 (hd j)]
    rw [hsum]
    exact h a ha

theorem mem_of_mem_span_map {F E X : Type} [Field F] [Field E] [Algebra F E]
    (W : Submodule F (X → F)) {u : X → F}
    (h : (fun x => algebraMap F E (u x)) ∈
      Submodule.span E ((fun w : X → F => fun x => algebraMap F E (w x)) '' (W : Set (X → F)))) :
    u ∈ W := by
  obtain ⟨φ, hφ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap F E)
    (LinearMap.ker_eq_bot.2 (algebraMap F E).injective)
  have hφ1 : ∀ k : F, φ (algebraMap F E k) = k := fun k => by
    simpa using LinearMap.congr_fun hφ k
  let S : Submodule E (X → E) :=
    { carrier := {c | ∀ ψ : E →ₗ[F] F, (fun x => ψ (c x)) ∈ W}
      zero_mem' := fun ψ => by
        have e : (fun x => ψ ((0 : X → E) x)) = 0 := by
          funext x; simp
        show (fun x => ψ ((0 : X → E) x)) ∈ W
        rw [e]
        exact W.zero_mem
      add_mem' := fun {c c'} hc hc' ψ => by
        have e : (fun x => ψ ((c + c') x)) = (fun x => ψ (c x)) + (fun x => ψ (c' x)) := by
          funext x; simp
        show (fun x => ψ ((c + c') x)) ∈ W
        rw [e]
        exact W.add_mem (hc ψ) (hc' ψ)
      smul_mem' := fun s c hc ψ => by
        have := hc (ψ ∘ₗ LinearMap.mulLeft F s)
        simpa using this }
  have hS : Submodule.span E
      ((fun w : X → F => fun x => algebraMap F E (w x)) '' (W : Set (X → F))) ≤ S := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨w, hw, rfl⟩ ψ
    have e : (fun x => ψ (algebraMap F E (w x))) = (ψ 1) • w := by
      funext x
      simp [Algebra.algebraMap_eq_smul_one, mul_comm]
    show (fun x => ψ (algebraMap F E (w x))) ∈ W
    rw [e]
    exact W.smul_mem _ hw
  have := hS h φ
  simpa [hφ1] using this

theorem exists_two_indep {E : Type} [Field E] (q : ℕ) (hq : 2 ≤ q) (e : E) (he : e ≠ 0)
    (A : Finset E) (hA : q < A.card) :
    ∃ a₁ ∈ A, ∃ a₂ ∈ A, a₁ * (e * a₂ ^ q) - a₂ * (e * a₁ ^ q) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a₁, ha₁, ha₁0⟩ := Finset.exists_mem_ne (show 1 < A.card by omega) (0 : E)
  have hq1 : a₁ ^ q = a₁ * a₁ ^ (q - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hp : (Polynomial.X ^ q - Polynomial.C (a₁ ^ (q - 1)) * Polynomial.X : Polynomial E) = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ A (fun a₂ ha₂ => ?_) ?_
    · have h0 := hcon a₁ ha₁ a₂ ha₂
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_mul,
        Polynomial.eval_C]
      rw [hq1] at h0
      have h1 : (a₁ * e) * (a₂ ^ q - a₁ ^ (q - 1) * a₂) = 0 := by linear_combination h0
      exact (mul_eq_zero.1 h1).resolve_left (mul_ne_zero ha₁0 he)
    · refine lt_of_le_of_lt ((Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)) hA
      · simp
      · have h1 : (Polynomial.C (a₁ ^ (q - 1)) * Polynomial.X : Polynomial E).natDegree ≤ 1 := by
          simpa using Polynomial.natDegree_C_mul_X_pow_le (a₁ ^ (q - 1)) 1
        omega
  have h1 := congrArg (fun p => Polynomial.coeff p q) hp
  simp only [Polynomial.coeff_sub, Polynomial.coeff_X_pow_self, Polynomial.coeff_C_mul_X,
    Polynomial.coeff_zero] at h1
  rw [if_neg (by omega)] at h1
  simp at h1

theorem exists_finset_pow_eq {E : Type} [Field E] [IsAlgClosed E] (m : ℕ) (hm : 2 ≤ m)
    (hm0 : (m : E) = 0) (e : E) (he : e ≠ 0) :
    ∃ A : Finset E, m ≤ A.card ∧ ∀ a ∈ A, e * a ^ m = a := by
  classical
  set p : Polynomial E := Polynomial.C e * Polynomial.X ^ m - Polynomial.X with hp
  have hdeg : p.natDegree = m := by
    rw [hp, Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
    · exact Polynomial.natDegree_C_mul_X_pow m e he
    · rw [Polynomial.natDegree_C_mul_X_pow m e he, Polynomial.natDegree_X]
      omega
  have hp0 : p ≠ 0 := by
    intro h
    rw [h] at hdeg
    simp at hdeg
    omega
  have hder : Polynomial.derivative p = -1 := by
    rw [hp, Polynomial.derivative_sub, Polynomial.derivative_C_mul_X_pow, Polynomial.derivative_X,
      hm0, mul_zero, Polynomial.C_0, zero_mul, zero_sub]
  have hsep : p.Separable := by
    rw [Polynomial.separable_def, hder]
    exact isCoprime_one_right.neg_right
  refine ⟨p.roots.toFinset, ?_, fun a ha => ?_⟩
  · rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep)]
    rw [IsAlgClosed.card_roots_eq_natDegree, hdeg]
  · rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0, Polynomial.IsRoot.def] at ha
    simpa [hp, sub_eq_zero] using ha

theorem exists_root_pow {E : Type} [Field E] [IsAlgClosed E] (m : ℕ) (hm : 2 ≤ m) (e : E)
    (he : e ≠ 0) (κ : E) : ∃ c : E, e * c ^ m + κ = c := by
  classical
  set p : Polynomial E := Polynomial.C e * Polynomial.X ^ m - Polynomial.X + Polynomial.C κ with hp
  have hdeg : p.natDegree = m := by
    rw [hp, Polynomial.natDegree_add_C, Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
    · exact Polynomial.natDegree_C_mul_X_pow m e he
    · rw [Polynomial.natDegree_C_mul_X_pow m e he, Polynomial.natDegree_X]
      omega
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_root p (by
    rw [Polynomial.degree_eq_natDegree (p := p) (by
      intro h
      rw [h] at hdeg
      simp at hdeg
      omega), hdeg]
    exact_mod_cast (by omega : m ≠ 0))
  refine ⟨c, ?_⟩
  simp only [hp, Polynomial.IsRoot.def, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X] at hc
  linear_combination hc

theorem natCast_card_eq_zero (F : Type) [Field F] [Finite F] (E : Type) [Field E] [Algebra F E] :
    ((Nat.card F : ℕ) : E) = 0 := by
  haveI : Fintype F := Fintype.ofFinite F
  have h : ((Nat.card F : ℕ) : F) = 0 := by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero F
  rw [← map_natCast (algebraMap F E), h, map_zero]

theorem exists_radList (σ : Tag) : ∃ l : List (Fin σ.rank → ℤ), l.Nodup ∧
    ∀ α, α ∈ l ↔ α ∈ parabolicRadicalRoots σ (Jθ σ) :=
  exists_list_of_finite ((finite_setOf_isRoot σ).subset fun _ h => h.1.1)

theorem exists_rational_Qθ {F : Type} [Field F] [Finite F] {w : WeylGroup τ} (D : LangLevi τ F w)
    {y : ModGL τ D.L} (hy : y ∈ Qθ τ D.L) (hfix : Units.map (entrywiseHom D.Fr) y = y) :
    ∃ y₀ ∈ Qθ τ F, baseChangeGL (algebraMap F D.L) y₀ = y := by
  classical
  obtain ⟨l, hl, hlS⟩ := exists_radList τ
  have hpos : ∀ α ∈ l, IsRoot τ α ∧ 0 < height α := fun α hα => ((hlS α).1 hα).1
  obtain ⟨c, hc⟩ := exists_list_prod_pinnedX_eq D.L (S := parabolicRadicalRoots τ (Jθ τ))
    (fun α hα => hα.1)
    (fun α hα β hβ a b ha hb hr => add_mem_parabolicRadicalRoots hα.1 hβ ha hb hr) hl hlS hy
  have hFy : (l.map fun α => pinnedX τ D.L α (D.Fr (c α))).prod = y := by
    rw [← hfix, ← hc, map_list_prod, List.map_map]
    congr 2
    funext α
    simp [Function.comp, CFSG.RankThree.PartOne.KE.units_map_entrywiseHom_pinnedX]
  have heq := pinnedX_list_prod_injective l hl hpos (fun α => D.Fr (c α)) c (hFy.trans hc.symm)
  have hrat : ∀ α ∈ l, ∃ d : F, algebraMap F D.L d = c α := fun α hα =>
    mem_range_algebraMap_of_pow_card_eq (by rw [← D.hFr]; exact heq α hα)
  choose! d hd using hrat
  refine ⟨(l.map fun α => pinnedX τ F α (d α)).prod, ?_, ?_⟩
  · refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨α, hα, rfl⟩ := List.mem_map.1 hx
    exact pinnedX_mem_rootSpan ((hlS α).1 hα) (d α)
  · rw [map_list_prod, List.map_map, ← hc]
    congr 1
    refine List.map_congr_left fun α hα => ?_
    simp only [Function.comp, baseChangeGL_pinnedX, hd α hα]


theorem comm_Qθ_pinnedX_of {F : Type} [Field F] {γ β : Fin τ.rank → ℤ}
    (hβ : β ∈ Deg1 τ) (hsum : γ + β = highRoot τ) (N c : F)
    (hform : ∀ s : F, pinnedX τ F γ s * pinnedX τ F β c * (pinnedX τ F γ s)⁻¹ *
      (pinnedX τ F β c)⁻¹ = pinnedX τ F (highRoot τ) (N * s * c))
    {q : ModGL τ F} (hq : q ∈ Qθ τ F) :
    q * pinnedX τ F β c * q⁻¹ * (pinnedX τ F β c)⁻¹ =
      pinnedX τ F (highRoot τ) (N * c * heisCoord τ F q γ) := by
  have hs := heisCoord_spec τ F
  refine Qθ_induction (P := fun x => x * pinnedX τ F β c * x⁻¹ * (pinnedX τ F β c)⁻¹ =
      pinnedX τ F (highRoot τ) (N * c * heisCoord τ F x γ)) ?_ ?_ ?_ ?_ ?_ q hq
  · show 1 * pinnedX τ F β c * 1⁻¹ * (pinnedX τ F β c)⁻¹ =
      pinnedX τ F (highRoot τ) (N * c * heisCoord τ F 1 γ)
    rw [heisCoord_one, Pi.zero_apply, mul_zero, pinnedX_zero, one_mul, inv_one, mul_one,
      mul_inv_cancel]
  · intro x z hx hz ex ez
    have hcomm : x * pinnedX τ F (highRoot τ) (N * c * heisCoord τ F z γ) =
        pinnedX τ F (highRoot τ) (N * c * heisCoord τ F z γ) * x :=
      (CoordAux.Uθ_comm (mem_rootSubgroup.2 ⟨_, rfl⟩)
        (parabolicRadical_le_posUnipotent (Jθ τ) hx)).symm
    show x * z * pinnedX τ F β c * (x * z)⁻¹ * (pinnedX τ F β c)⁻¹ =
      pinnedX τ F (highRoot τ) (N * c * heisCoord τ F (x * z) γ)
    calc x * z * pinnedX τ F β c * (x * z)⁻¹ * (pinnedX τ F β c)⁻¹
        = x * (z * pinnedX τ F β c * z⁻¹ * (pinnedX τ F β c)⁻¹) * x⁻¹ *
            (x * pinnedX τ F β c * x⁻¹ * (pinnedX τ F β c)⁻¹) := by group
      _ = x * pinnedX τ F (highRoot τ) (N * c * heisCoord τ F z γ) * x⁻¹ *
            pinnedX τ F (highRoot τ) (N * c * heisCoord τ F x γ) := by rw [ex, ez]
      _ = pinnedX τ F (highRoot τ) (N * c * heisCoord τ F z γ) *
            pinnedX τ F (highRoot τ) (N * c * heisCoord τ F x γ) := by
          rw [hcomm, mul_inv_cancel_right]
      _ = pinnedX τ F (highRoot τ) (N * c * heisCoord τ F (x * z) γ) := by
          rw [← pinnedX_add, hs.mul _ hx _ hz, Pi.add_apply]
          congr 1
          ring
  · intro x hx ex
    have hcomm : x⁻¹ * pinnedX τ F (highRoot τ) (-(N * c * heisCoord τ F x γ)) =
        pinnedX τ F (highRoot τ) (-(N * c * heisCoord τ F x γ)) * x⁻¹ :=
      (CoordAux.Uθ_comm (mem_rootSubgroup.2 ⟨_, rfl⟩)
        (parabolicRadical_le_posUnipotent (Jθ τ) (inv_mem hx))).symm
    show x⁻¹ * pinnedX τ F β c * x⁻¹⁻¹ * (pinnedX τ F β c)⁻¹ =
      pinnedX τ F (highRoot τ) (N * c * heisCoord τ F x⁻¹ γ)
    calc x⁻¹ * pinnedX τ F β c * x⁻¹⁻¹ * (pinnedX τ F β c)⁻¹
        = x⁻¹ * (x * pinnedX τ F β c * x⁻¹ * (pinnedX τ F β c)⁻¹)⁻¹ * x := by group
      _ = x⁻¹ * pinnedX τ F (highRoot τ) (-(N * c * heisCoord τ F x γ)) * x := by
          rw [ex, pinnedX_neg]
      _ = pinnedX τ F (highRoot τ) (-(N * c * heisCoord τ F x γ)) := by
          rw [hcomm, inv_mul_cancel_right]
      _ = pinnedX τ F (highRoot τ) (N * c * heisCoord τ F x⁻¹ γ) := by
          rw [heisCoord_inv hx, Pi.neg_apply]
          congr 1
          ring
  · intro δ hδ t
    show pinnedX τ F δ t * pinnedX τ F β c * (pinnedX τ F δ t)⁻¹ * (pinnedX τ F β c)⁻¹ =
      pinnedX τ F (highRoot τ) (N * c * heisCoord τ F (pinnedX τ F δ t) γ)
    rw [hs.pinnedX_deg1 δ hδ t]
    rcases eq_or_ne δ γ with rfl | hne
    · rw [hform t, Pi.single_eq_same]
      congr 1
      ring
    · have hnot : δ + β ∉ rootFinset τ := by
        intro hr
        have h2 := CoordAux.eq_highRoot_of_two_le (mem_rootFinset.1 hr) (by
          rw [Pi.add_apply, (CoordAux.mem_Deg1.1 hδ).2, (CoordAux.mem_Deg1.1 hβ).2]
          norm_num)
        rw [← hsum] at h2
        exact hne (add_right_cancel h2)
      rw [(CoordAux.commute_pinnedX_of_not_isRoot_add hδ hβ hnot t c).eq, mul_inv_cancel_right,
        mul_inv_cancel, Pi.single_eq_of_ne hne.symm, mul_zero, pinnedX_zero]
  · intro t
    show pinnedX τ F (highRoot τ) t * pinnedX τ F β c * (pinnedX τ F (highRoot τ) t)⁻¹ *
        (pinnedX τ F β c)⁻¹ =
      pinnedX τ F (highRoot τ) (N * c * heisCoord τ F (pinnedX τ F (highRoot τ) t) γ)
    rw [CoordAux.Uθ_comm (mem_rootSubgroup.2 ⟨t, rfl⟩) (CoordAux.pinnedX_mem_pos hβ c),
      mul_inv_cancel_right, mul_inv_cancel, hs.pinnedX_highRoot, Pi.zero_apply, mul_zero,
      pinnedX_zero]

theorem Qθ_comm_highRoot {F : Type} [Field F] {q : ModGL τ F} (hq : q ∈ Qθ τ F) (s : F) :
    pinnedX τ F (highRoot τ) s * q = q * pinnedX τ F (highRoot τ) s :=
  CoordAux.Uθ_comm (mem_rootSubgroup.2 ⟨s, rfl⟩) (parabolicRadical_le_posUnipotent (Jθ τ) hq)

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.IrredE6Aux
