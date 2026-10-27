module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Defs
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.Coordinates
public import CFSG.LieType.Chevalley.GraphFixedF4GroupDescent
public import CFSG.RankThree.Lattice.SteinbergBIListMatrix

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.IrE8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

set_option linter.unusedSectionVars false


variable {τ : Tag}

namespace HeisAux1

private theorem Qθ_induction {K : Type} [Field K] {P : ModGL τ K → Prop}
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
    · exact ⟨pinnedX_mem_rootSpan hα t, h₁ α h t⟩
    · exact ⟨pinnedX_mem_rootSpan hα t, h₂ t⟩
  exact fun x hx => (hle hx).2

private theorem isRoot_highRoot_sub {β : Fin τ.rank → ℤ} (hβ : β ∈ Deg1 τ) :
    IsRoot τ (highRoot τ - β) := by
  have hθ := isRoot_highRoot τ
  have hcp : corootPair (highRoot τ) β = 1 := by
    have h := corootPair_mul hθ β
    rw [iform_highRoot_apply, iform_highRoot_apply, (CoordAux.mem_Deg1.1 hβ).2,
      CoordAux.highRoot_degree] at h
    have hne : cθ τ * 2 ≠ 0 := mul_ne_zero (cθ_ne_zero τ) two_ne_zero
    exact mul_right_cancel₀ hne (h.trans (by ring))
  have h := IsRoot.neg (IsRoot.smul (CoordAux.mem_Deg1.1 hβ).1 (rootReflection (highRoot τ)))
  rwa [rootReflection_smul hθ, hcp, one_smul, neg_sub] at h

private theorem highRoot_sub_mem_Deg1 {β : Fin τ.rank → ℤ} (hβ : β ∈ Deg1 τ) :
    highRoot τ - β ∈ Deg1 τ := by
  refine CoordAux.mem_Deg1.2 ⟨isRoot_highRoot_sub hβ, ?_⟩
  rw [Pi.sub_apply, CoordAux.highRoot_degree, (CoordAux.mem_Deg1.1 hβ).2]
  norm_num

private theorem comm_Qθ_pinnedX_of {F : Type} [Field F] {γ β : Fin τ.rank → ℤ}
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

end HeisAux1

theorem heisCoord_baseChange {K L : Type} [Field K] [Field L] (f : K →+* L) {q : ModGL τ K}
    (hq : q ∈ Qθ τ K) :
    baseChangeGL f q ∈ Qθ τ L ∧
      heisCoord τ L (baseChangeGL f q) = fun β => f (heisCoord τ K q β) := by
  refine HeisAux1.Qθ_induction (P := fun x => baseChangeGL f x ∈ Qθ τ L ∧
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
    refine ⟨pinnedX_mem_rootSpan ((CoordAux.mem_radRoots_iff β).2 (Or.inl hβ)) _, ?_⟩
    rw [(heisCoord_spec τ L).pinnedX_deg1 β hβ, (heisCoord_spec τ K).pinnedX_deg1 β hβ]
    funext γ
    by_cases h : γ = β
    · subst h
      simp
    · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, map_zero]
  · intro t
    rw [baseChangeGL_pinnedX]
    refine ⟨pinnedX_mem_rootSpan ((CoordAux.mem_radRoots_iff (highRoot τ)).2 (Or.inr rfl)) _, ?_⟩
    rw [(heisCoord_spec τ L).pinnedX_highRoot, (heisCoord_spec τ K).pinnedX_highRoot]
    funext γ
    simp

theorem fixed_Qθ_rational {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L]
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K) {q' : ModGL τ L} (hq' : q' ∈ Qθ τ L)
    (hF : Units.map (entrywiseHom Fr) q' = q') :
    ∃ q₀ ∈ Qθ τ K, baseChangeGL (algebraMap K L) q₀ = q' := by
  classical
  obtain ⟨l, hl, hlS⟩ : ∃ l : List (Fin τ.rank → ℤ), l.Nodup ∧
      ∀ α, α ∈ l ↔ α ∈ parabolicRadicalRoots τ (Jθ τ) :=
    exists_list_of_finite ((finite_setOf_isRoot τ).subset fun _ h => h.1.1)
  have hpos : ∀ α ∈ l, IsRoot τ α ∧ 0 < height α := fun α hα => ((hlS α).1 hα).1
  obtain ⟨c, hc⟩ := exists_list_prod_pinnedX_eq L (S := parabolicRadicalRoots τ (Jθ τ))
    (fun α hα => hα.1)
    (fun α hα β hβ a b ha hb hr => add_mem_parabolicRadicalRoots hα.1 hβ ha hb hr) hl hlS hq'
  have hF' : baseChangeGL Fr q' = q' := by
    have e : baseChangeGL Fr q' = Units.map (entrywiseHom Fr) q' := Units.ext rfl
    rw [e, hF]
  have hFy : (l.map fun α => pinnedX τ L α (Fr (c α))).prod = q' := by
    rw [← hF', ← hc, map_list_prod, List.map_map]
    congr 1
    refine List.map_congr_left fun α _ => ?_
    rw [Function.comp_apply, baseChangeGL_pinnedX]
  have heq := pinnedX_list_prod_injective l hl hpos (fun α => Fr (c α)) c (hFy.trans hc.symm)
  have hrat : ∀ α ∈ l, ∃ d : K, algebraMap K L d = c α := fun α hα =>
    CFSG.LieType.Chevalley.mem_range_algebraMap_of_pow_card_eq (k := K)
      (by rw [← hFr]; exact heq α hα)
  choose! d hd using hrat
  refine ⟨(l.map fun α => pinnedX τ K α (d α)).prod, ?_, ?_⟩
  · refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨α, hα, rfl⟩ := List.mem_map.1 hx
    exact pinnedX_mem_rootSpan ((hlS α).1 hα) (d α)
  · rw [map_list_prod, List.map_map, ← hc]
    congr 1
    refine List.map_congr_left fun α hα => ?_
    rw [Function.comp_apply, baseChangeGL_pinnedX, hd α hα]

theorem commutator_Qθ_pinnedX {β : Fin Tag.E8.rank → ℤ} (hβ : β ∈ Deg1 Tag.E8) :
    ∃ N : ℤ, (N = 1 ∨ N = -1) ∧ ∀ (F : Type) [Field F] (q : ModGL Tag.E8 F), q ∈ Qθ Tag.E8 F →
      ∀ c : F, q * pinnedX Tag.E8 F β c * q⁻¹ * (pinnedX Tag.E8 F β c)⁻¹ =
        pinnedX Tag.E8 F (highRoot Tag.E8)
          ((N : F) * c * heisCoord Tag.E8 F q (highRoot Tag.E8 - β)) := by
  have hγD : highRoot Tag.E8 - β ∈ Deg1 Tag.E8 := HeisAux1.highRoot_sub_mem_Deg1 hβ
  have hsum : highRoot Tag.E8 - β + β = highRoot Tag.E8 := sub_add_cancel _ _
  have hne : highRoot Tag.E8 - β ≠ β := by
    intro h
    have h1 := congrFun h 1
    have h3 : highRoot Tag.E8 1 % 2 = 1 := by decide
    rw [Pi.sub_apply] at h1
    omega
  obtain ⟨h1, -⟩ := simply_laced_root_commutator_unit.{0} Tag.E8 (Or.inr (Or.inr (Or.inr rfl)))
    (CoordAux.mem_Deg1.1 hγD).1 (CoordAux.mem_Deg1.1 hβ).1 hne (CoordAux.Deg1.ne_neg hγD hβ)
  obtain ⟨hN, hform⟩ := h1 (by rw [hsum]; exact isRoot_highRoot _)
  refine ⟨commConst Tag.E8 (highRoot Tag.E8 - β) β (1, 1), hN, fun F _ q hq c => ?_⟩
  refine HeisAux1.comm_Qθ_pinnedX_of hβ hsum _ c (fun s => ?_) hq
  have h := hform F s c
  rw [commutatorElement_def, hsum] at h
  exact h

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.IrE8
