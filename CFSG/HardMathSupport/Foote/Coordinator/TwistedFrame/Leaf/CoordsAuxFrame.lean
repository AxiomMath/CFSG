module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.CoordsAuxLang
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.CoordsAuxData
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.CoordsAuxHard
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.DegZero

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open scoped commutatorElement

set_option linter.unusedSectionVars false


namespace CoordsAux

private theorem mem_frame_iff {τ : Tag} {K : Type} [Field K] [Finite K] {w : WeylGroup τ}
    (D : LangLevi τ K w) (S : Set (Fin τ.rank → ℤ)) (x : ModGL τ K) :
    x ∈ D.frame S ↔ x ∈ adjointGroup τ K ∧
      D.g⁻¹ * baseChangeGL (algebraMap K D.L) x * D.g ∈ rootSpan τ D.L S := by
  unfold LangLevi.frame
  rw [Subgroup.mem_inf, Subgroup.mem_comap]
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, inv_inv]

private theorem frame_commute (c : TwClass) {K : Type} [Field K] [Finite K]
    (D : LangLevi c.tag K c.w) : ∀ x ∈ c.X₁ D, ∀ y ∈ c.X₂ D, x * y = y * x := by
  intro x hx y hy
  obtain ⟨-, hx'⟩ := (mem_frame_iff D _ x).1 hx
  obtain ⟨-, hy'⟩ := (mem_frame_iff D _ y).1 hy
  have h := rootSpan_commute c D.L _ hx' _ hy'
  refine baseChangeGL_injective (algebraMap K D.L) ?_
  rw [map_mul, map_mul]
  set a := baseChangeGL (algebraMap K D.L) x
  set b := baseChangeGL (algebraMap K D.L) y
  set g := D.g
  calc a * b = g * (g⁻¹ * a * g * (g⁻¹ * b * g)) * g⁻¹ := by group
    _ = g * (g⁻¹ * b * g * (g⁻¹ * a * g)) * g⁻¹ := by rw [h]
    _ = b * a := by group

private theorem exists_mul_of_mem_sup (c : TwClass) {K : Type} [Field K] [Finite K]
    (D : LangLevi c.tag K c.w) {x : ModGL c.tag K} (hx : x ∈ c.X₁ D ⊔ c.X₂ D) :
    ∃ x₁ ∈ c.X₁ D, ∃ x₂ ∈ c.X₂ D, x = x₁ * x₂ := by
  have hle : c.X₁ D ≤ Subgroup.normalizer (c.X₂ D : Set (ModGL c.tag K)) := fun y hy =>
    mem_normalizer_of_forall_mul_eq fun z hz => frame_commute c D y hy z hz
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle, Set.mem_mul] at hx
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := hx
  exact ⟨x₁, hx₁, x₂, hx₂, rfl⟩

private theorem rootSpan_S₂_le_Lθ (c : TwClass) (F : Type) [Field F] :
    rootSpan c.tag F c.S₂ ≤ Lθ c.tag F :=
  iSup₂_le fun _ hα => rootSubgroup_le_Lθ_of_deg_zero hα.1 (hα.2 _ (iθ_not_mem_J₂ c))

private theorem coord_support_of_mem_rootSpan (c : TwClass) (F : Type) [Field F]
    {y : ModGL c.tag F} (hy : y ∈ rootSpan c.tag F {α | α ∈ c.S₁ ∧ 1 ≤ α (iθ c.tag)}) :
    y ∈ Qθ c.tag F ∧ ∀ β, β ∉ Bset c → heisCoord c.tag F y β = 0 := by
  let H : Subgroup (ModGL c.tag F) :=
    { carrier := {y | y ∈ Qθ c.tag F ∧ ∀ β, β ∉ Bset c → heisCoord c.tag F y β = 0}
      mul_mem' := fun {x y} hx hy => ⟨mul_mem hx.1 hy.1, fun β hβ => by
        rw [(heisCoord_spec c.tag F).mul _ hx.1 _ hy.1, Pi.add_apply, hx.2 β hβ, hy.2 β hβ,
          add_zero]⟩
      one_mem' := ⟨one_mem _, fun β _ => by rw [heisCoord_one, Pi.zero_apply]⟩
      inv_mem' := fun {x} hx => ⟨inv_mem hx.1, fun β hβ => by
        rw [heisCoord_inv hx.1, Pi.neg_apply, hx.2 β hβ, neg_zero]⟩ }
  have hle : rootSpan c.tag F {α | α ∈ c.S₁ ∧ 1 ≤ α (iθ c.tag)} ≤ H := by
    refine iSup₂_le fun α hα => ?_
    intro g hg
    obtain ⟨t, rfl⟩ := mem_rootSubgroup.1 hg
    have hr : IsRoot c.tag α := hα.1.1
    rcases eq_or_lt_of_le hα.2 with h1 | h2
    ·
      have hD : α ∈ Deg1 c.tag := CoordAux.mem_Deg1.2 ⟨hr, h1.symm⟩
      refine ⟨pinnedX_mem_Qθ_of_mem_Deg1 hD t, fun β hβ => ?_⟩
      have hne : β ≠ α := by
        rintro rfl
        exact hβ ⟨hD, hα.1⟩
      rw [(heisCoord_spec c.tag F).pinnedX_deg1 α hD t, Pi.single_eq_of_ne hne]
    ·
      have hθ : α = highRoot c.tag := CoordAux.eq_highRoot_of_two_le hr (by omega)
      subst hθ
      refine ⟨Uθ_le_Qθ (mem_rootSubgroup.2 ⟨t, rfl⟩), fun β _ => ?_⟩
      rw [(heisCoord_spec c.tag F).pinnedX_highRoot, Pi.zero_apply]
  exact hle hy

section Class

variable (c : TwClass) {K : Type} [Field K] [Finite K] (D : LangLevi c.tag K c.w)

theorem mem_X₁_of_support {q : ModGL c.tag K} (hq : q ∈ Qθ c.tag K)
    (hs : ∀ β, κ D q β ≠ 0 → β ∈ Bset c) : q ∈ c.X₁ D := by
  obtain ⟨lB, hnd, hlB⟩ := exists_list_of_finite (S := Bset c)
    ((finite_setOf_isRoot c.tag).subset fun _ hβ => hβ.1.1)
  obtain ⟨u, hu, he⟩ := exists_prodX_of_support hnd (fun β hβ => ((hlB β).1 hβ).1)
    (Ψ_Qθ D hq) (fun ν hν => by
      by_contra h
      exact hν ((hlB ν).2 (hs ν h)))
  show q ∈ D.frame c.S₁
  refine (mem_frame_iff D c.S₁ q).2 ⟨Qθ_le_adjointGroup c.tag K hq, ?_⟩
  change Ψ D q ∈ rootSpan c.tag D.L c.S₁
  rw [he]
  exact mul_mem (rootSubgroup_le_rootSpan_of_mem (highRoot_mem_S₁ c) hu)
    (CoordAux.prodX_mem_rootSpan (fun β hβ => ((hlB β).1 hβ).2) _)

theorem support_of_mem_X {q : ModGL c.tag K} (hq : q ∈ Qθ c.tag K)
    (hX : q ∈ c.X₁ D ⊔ c.X₂ D) : ∀ β, κ D q β ≠ 0 → β ∈ Bset c := by
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := exists_mul_of_mem_sup c D hX
  have ha : Ψ D x₁ ∈ rootSpan c.tag D.L c.S₁ := ((mem_frame_iff D _ x₁).1 hx₁).2
  have hb : Ψ D x₂ ∈ Lθ c.tag D.L := rootSpan_S₂_le_Lθ c D.L ((mem_frame_iff D _ x₂).1 hx₂).2
  have hΨ : Ψ D x₁ * Ψ D x₂ ∈ Qθ c.tag D.L := by
    rw [← Ψ_mul]
    exact Ψ_Qθ D hq
  have haP : Ψ D x₁ ∈ Pθ c.tag D.L := by
    have e : Ψ D x₁ = Ψ D x₁ * Ψ D x₂ * (Ψ D x₂)⁻¹ := by group
    rw [e]
    exact mul_mem (Qθ_le_Pθ c.tag D.L hΨ) (Lθ_le_Pθ c.tag D.L (inv_mem hb))
  obtain ⟨J, v, hmin, hS⟩ := exists_levi_data c
  obtain ⟨q₁, hq₁, l, hl, hal⟩ := factor_of_mem_rootSpan_of_mem_Pθ hmin hS ha haP
  obtain ⟨hq₁Q, hq₁s⟩ := coord_support_of_mem_rootSpan c D.L hq₁
  have heq : q₁ = Ψ D x₁ * Ψ D x₂ :=
    (eq_of_mul_eq_of_parabolic hq₁Q hΨ (mul_mem hl hb) (one_mem _)
      (by rw [mul_one, hal, mul_assoc])).1
  intro β hβ
  by_contra hn
  apply hβ
  show heisCoord c.tag D.L (Ψ D (x₁ * x₂)) β = 0
  rw [Ψ_mul, ← heq]
  exact hq₁s β hn

end Class

end CoordsAux

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
