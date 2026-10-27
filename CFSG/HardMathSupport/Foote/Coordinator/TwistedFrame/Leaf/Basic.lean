module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.Opposite
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.QuasiAuxMain

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

set_option linter.unusedSectionVars false


namespace TwBasicAux

theorem gen_of_quasisimple {G : Type*} [Group G] {X U V : Subgroup G}
    (hq : CFSG.IsQuasisimple ↥X) (hU : U ≤ X) (hV : V ≤ X)
    (hnc : ∃ u ∈ U, ∃ v ∈ V, u * v ≠ v * u) :
    (⨆ x ∈ X, conjSub x U) = X := by
  have hle : (⨆ x ∈ X, conjSub x U) ≤ X := iSup₂_le fun x hx => by
    rintro _ ⟨u, hu, rfl⟩
    exact mul_mem (mul_mem hx (hU hu)) (inv_mem hx)
  have key : ∀ y ∈ X, conjSub y (⨆ x ∈ X, conjSub x U) ≤ ⨆ x ∈ X, conjSub x U := by
    intro y hy
    refine Subgroup.map_le_iff_le_comap.2 (iSup₂_le fun x hx => ?_)
    refine Subgroup.map_le_iff_le_comap.1 ?_
    show conjSub y (conjSub x U) ≤ ⨆ x ∈ X, conjSub x U
    rw [← conjSub_mul]
    exact le_iSup₂ (f := fun x (_ : x ∈ X) => conjSub x U) (y * x) (mul_mem hy hx)
  haveI hnorm : ((⨆ x ∈ X, conjSub x U).subgroupOf X).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact key g.1 g.2 (Subgroup.mem_map_of_mem _ hn)
  refine le_antisymm hle ?_
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hq
      ((⨆ x ∈ X, conjSub x U).subgroupOf X) with hc | htop
  · exfalso
    obtain ⟨u, hu, v, hv, huv⟩ := hnc
    have huN : u ∈ ⨆ x ∈ X, conjSub x U :=
      Subgroup.mem_iSup_of_mem 1 (Subgroup.mem_iSup_of_mem X.one_mem
        (by rw [conjSub_one]; exact hu))
    have hmem : (⟨u, hU hu⟩ : ↥X) ∈ (⨆ x ∈ X, conjSub x U).subgroupOf X := huN
    have h := Subgroup.mem_center_iff.1 (hc hmem) ⟨v, hV hv⟩
    exact huv (congrArg Subtype.val h).symm
  · intro x hx
    have : (⟨x, hx⟩ : ↥X) ∈ (⨆ x ∈ X, conjSub x U).subgroupOf X := by
      rw [htop]
      exact Subgroup.mem_top _
    exact this

theorem exists_not_commute_pinnedX_neg {τ : Tag} {K : Type} [Field K] {β : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) : ∃ c d : K, pinnedX τ K β c * pinnedX τ K (-β) d ≠
      pinnedX τ K (-β) d * pinnedX τ K β c := by
  obtain ⟨w, i, rfl⟩ := isRoot_iff_exists_smul_single.1 hβ
  obtain ⟨ε₁, -, hX⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K w (isRoot_single τ i)
  obtain ⟨ε₂, -, hY⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K w (isRoot_neg_single τ i)
  refine ⟨ε₁ * 1, ε₂ * 1, fun h => ?_⟩
  refine not_commute_xUnit_yUnit (τ := τ) (K := K) i ?_
  have e1 := hX 1
  have e2 := hY 1
  rw [pinnedX_single] at e1
  rw [pinnedX_neg_single, smul_neg] at e2
  set n := canonicalRep (coxeterSystem τ) K w
  have h' : (n * xUnit τ K i 1 * n⁻¹) * (n * yUnit τ K i 1 * n⁻¹) =
      (n * yUnit τ K i 1 * n⁻¹) * (n * xUnit τ K i 1 * n⁻¹) := by
    rw [e1, e2]
    exact h
  show xUnit τ K i 1 * yUnit τ K i 1 = yUnit τ K i 1 * xUnit τ K i 1
  calc xUnit τ K i 1 * yUnit τ K i 1
      = n⁻¹ * ((n * xUnit τ K i 1 * n⁻¹) * (n * yUnit τ K i 1 * n⁻¹)) * n := by group
    _ = n⁻¹ * ((n * yUnit τ K i 1 * n⁻¹) * (n * xUnit τ K i 1 * n⁻¹)) * n := by rw [h']
    _ = yUnit τ K i 1 * xUnit τ K i 1 := by group

theorem mem_frame_iff {τ : Tag} {K : Type} [Field K] [Finite K] {w : WeylGroup τ}
    (D : LangLevi τ K w) (S : Set (Fin τ.rank → ℤ)) (x : ModGL τ K) :
    x ∈ D.frame S ↔ x ∈ adjointGroup τ K ∧
      D.g⁻¹ * baseChangeGL (algebraMap K D.L) x * D.g ∈ rootSpan τ D.L S := by
  unfold LangLevi.frame
  rw [Subgroup.mem_inf, Subgroup.mem_comap]
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, inv_inv]

theorem rootSubgroup_le_frame {τ : Tag} {K : Type} [Field K] [Finite K] {w : WeylGroup τ}
    (D : LangLevi τ K w) {S : Set (Fin τ.rank → ℤ)} {β : Fin τ.rank → ℤ} (hβS : β ∈ S)
    (hg : D.g ∈ Subgroup.normalizer (rootSubgroup τ D.L β : Set (ModGL τ D.L))) :
    rootSubgroup τ K β ≤ D.frame S := by
  intro x hx
  rw [mem_frame_iff]
  refine ⟨rootSubgroup_le_adjointGroup β hx, ?_⟩
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
  rw [baseChangeGL_pinnedX]
  have h1 := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) _).1
    (mem_rootSubgroup.2 ⟨algebraMap K D.L c, rfl⟩ :
      pinnedX τ D.L β (algebraMap K D.L c) ∈ rootSubgroup τ D.L β)
  rw [inv_inv] at h1
  exact Subgroup.mem_iSup_of_mem β (Subgroup.mem_iSup_of_mem hβS h1)

theorem iθ_not_mem_J₂ (c : TwClass) : (iθ c.tag).val ∉ c.J₂ := by
  cases c <;> decide

theorem iform_highRoot_eq_zero (c : TwClass) {α : Fin c.tag.rank → ℤ} (hα : α ∈ c.S₂) :
    CFSG.LieType.Steinberg.Adjoint.iform (highRoot c.tag) α = 0 := by
  rw [iform_highRoot_apply, hα.2 _ (iθ_not_mem_J₂ c), mul_zero]

theorem highRoot_mem_S₁ (c : TwClass) : highRoot c.tag ∈ c.S₁ :=
  ⟨isRoot_highRoot _, fun _ hα => iform_highRoot_eq_zero c hα⟩

theorem neg_highRoot_mem_S₁ (c : TwClass) : -highRoot c.tag ∈ c.S₁ :=
  ⟨isRoot_neg_highRoot _, fun _ hα => by
    rw [iform_neg_left, iform_highRoot_eq_zero c hα, neg_zero]⟩

theorem f4_not_isRoot_add : ∀ α ∈ rootFinset Tag.F4,
    (∀ β ∈ rootFinset Tag.F4, (∀ i : Fin Tag.F4.rank, i.val ∉ TwClass.f4Six.J₂ → β i = 0) →
      CFSG.LieType.Steinberg.Adjoint.iform α β = 0) →
    ∀ β ∈ rootFinset Tag.F4, (∀ i : Fin Tag.F4.rank, i.val ∉ TwClass.f4Six.J₂ → β i = 0) →
      α + β ∉ rootFinset Tag.F4 := by
  decide +kernel

theorem not_isRoot_add_f4 {α β : Fin Tag.F4.rank → ℤ} (hα : α ∈ TwClass.f4Six.S₁)
    (hβ : β ∈ TwClass.f4Six.S₂) : ¬ IsRoot Tag.F4 (α + β) := fun h =>
  f4_not_isRoot_add α (mem_rootFinset.2 hα.1)
    (fun β' hβ' hs => hα.2 β' ⟨mem_rootFinset.1 hβ', hs⟩) β (mem_rootFinset.2 hβ.1) hβ.2
    (mem_rootFinset.2 h)

theorem rootSpan_commute (c : TwClass) (L : Type) [Field L] :
    ∀ x ∈ rootSpan c.tag L c.S₁, ∀ y ∈ rootSpan c.tag L c.S₂, x * y = y * x := by
  cases c with
  | f4Six =>
    refine rootSpan_commute_of_gen' fun α hα β hβ c d => ?_
    exact pinnedX_commute_of_iform_eq_zero L hα.1 hβ.1 (hα.2 β hβ) (not_isRoot_add_f4 hα hβ) c d
  | e6Six =>
    exact CFSG.RankThree.PartOne.KE.rootSpan_commute_of_orth (Or.inr (Or.inl rfl))
      (fun r hr => hr.1) (fun r hr => hr.1)
      (fun α hα β hβ => (dotProduct_mulVec_symmetrizedCartan_eq_sum α β).trans (hα.2 β hβ))
  | e8Ten =>
    exact CFSG.RankThree.PartOne.KE.rootSpan_commute_of_orth (Or.inr (Or.inr (Or.inr rfl)))
      (fun r hr => hr.1) (fun r hr => hr.1)
      (fun α hα β hβ => (dotProduct_mulVec_symmetrizedCartan_eq_sum α β).trans (hα.2 β hβ))
  | e8Twelve =>
    exact CFSG.RankThree.PartOne.KE.rootSpan_commute_of_orth (Or.inr (Or.inr (Or.inr rfl)))
      (fun r hr => hr.1) (fun r hr => hr.1)
      (fun α hα β hβ => (dotProduct_mulVec_symmetrizedCartan_eq_sum α β).trans (hα.2 β hβ))

theorem frame_commute (c : TwClass) {K : Type} [Field K] [Finite K] (D : LangLevi c.tag K c.w) :
    ∀ x ∈ c.X₁ D, ∀ y ∈ c.X₂ D, x * y = y * x := by
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

theorem twBasic_of_quasi (c : TwClass) {K : Type} [Field K] [Finite K]
    (D : LangLevi c.tag K c.w) (hq : CFSG.IsQuasisimple ↥(c.X₁ D)) :
    TwBasic (c.X₁ D) (c.X₂ D) := by
  have hUθ : Uθ c.tag K ≤ c.X₁ D :=
    rootSubgroup_le_frame D (highRoot_mem_S₁ c)
      (Pθ_le_normalizer_Uθ c.tag D.L (parabolicLevi_le_parabolicSubgroup _ D.g_mem))
  have hUneg : Heis.Uneg c.tag K ≤ c.X₁ D :=
    rootSubgroup_le_frame D (neg_highRoot_mem_S₁ c) (Lθ_le_normalizer_Uneg c.tag D.L D.g_mem)
  refine ⟨fun x hx => ((mem_frame_iff D _ x).1 hx).1, fun x hx => ((mem_frame_iff D _ x).1 hx).1,
    frame_commute c D, hUθ, hUneg, ?_⟩
  obtain ⟨a, b, hab⟩ := exists_not_commute_pinnedX_neg (K := K) (isRoot_highRoot c.tag)
  exact gen_of_quasisimple hq hUθ hUneg
    ⟨_, mem_rootSubgroup.2 ⟨a, rfl⟩, _, mem_rootSubgroup.2 ⟨b, rfl⟩, hab⟩

end TwBasicAux


theorem twBasic (c : TwClass) (K : Type) [Field K] [Finite K] (hK : c.minQ ≤ Nat.card K)
    (D : LangLevi c.tag K c.w) : TwBasic (c.X₁ D) (c.X₂ D) :=
  TwBasicAux.twBasic_of_quasi c D (twQuasi_X₁ c K hK D)

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
