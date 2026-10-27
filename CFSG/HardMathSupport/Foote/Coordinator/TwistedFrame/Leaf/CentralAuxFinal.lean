module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.CentralAuxOrbit
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.CentralAuxClasses
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.CentralAuxLevi
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Frames
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Hyp

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.CentralAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false


section BaseChange

variable {τ : Tag} {K L : Type} [Field K] [Field L] (ι : K →+* L)

theorem baseChangeGL_mem_torusGroup' {h : ModGL τ K} (hh : h ∈ torusGroup τ K) :
    baseChangeGL ι h ∈ torusGroup τ L := by
  have hle : torusGroup τ K ≤ (torusGroup τ L).comap (baseChangeGL ι) := by
    rw [torusGroup, Subgroup.closure_le]
    rintro _ ⟨⟨i, t⟩, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, baseChangeGL_torusElt]
    exact torusElt_mem_torusGroup i _
  exact hle hh

theorem baseChangeGL_mem_Lθ {x : ModGL τ K} (hx : x ∈ Lθ τ K) : baseChangeGL ι x ∈ Lθ τ L := by
  have hT : torusGroup τ L ≤ Lθ τ L := le_sup_left
  have hle : Lθ τ K ≤ (Lθ τ L).comap (baseChangeGL ι) := by
    refine sup_le (fun t ht => ?_) ((Subgroup.closure_le _).2 ?_)
    · exact Subgroup.mem_comap.2 (hT (baseChangeGL_mem_torusGroup' ι ht))
    · rintro _ ⟨j, hj, c, rfl | rfl⟩
      · rw [SetLike.mem_coe, Subgroup.mem_comap, baseChangeGL_xUnit]
        exact (le_sup_right : Subgroup.closure
          {g | ∃ j ∈ Jθ τ, ∃ c : L, g = xUnit τ L j c ∨ g = yUnit τ L j c} ≤ Lθ τ L)
          (Subgroup.subset_closure ⟨j, hj, ι c, Or.inl rfl⟩)
      · rw [SetLike.mem_coe, Subgroup.mem_comap, baseChangeGL_yUnit]
        exact (le_sup_right : Subgroup.closure
          {g | ∃ j ∈ Jθ τ, ∃ c : L, g = xUnit τ L j c ∨ g = yUnit τ L j c} ≤ Lθ τ L)
          (Subgroup.subset_closure ⟨j, hj, ι c, Or.inr rfl⟩)
  exact hle hx

end BaseChange

section Hat

variable {τ : Tag} {K : Type} [Field K] [Finite K] {w : WeylGroup τ} (D : LangLevi τ K w)

theorem hat_mem_Lθ_and_centralizes {x : ModGL τ K} (hx : x ∈ Lθ τ K)
    (hcθ : ∀ u ∈ Uθ τ K, x * u = u * x) (hcn : ∀ u ∈ Heis.Uneg τ K, x * u = u * x) :
    hat D x ∈ Lθ τ D.L ∧ (∀ u ∈ Uθ τ D.L, hat D x * u = u * hat D x) ∧
      ∀ u ∈ Heis.Uneg τ D.L, hat D x * u = u * hat D x := by
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  have hxL : baseChangeGL (algebraMap K D.L) x ∈ Lθ τ D.L := baseChangeGL_mem_Lθ _ hx
  have hgL := D.g_mem
  refine ⟨mul_mem (mul_mem (inv_mem hgL) hxL) hgL, ?_, ?_⟩
  · have h1 : baseChangeGL (algebraMap K D.L) x * pinnedX τ D.L (highRoot τ) 1 *
        (baseChangeGL (algebraMap K D.L) x)⁻¹ = pinnedX τ D.L (highRoot τ) 1 := by
      have hu : pinnedX τ K (highRoot τ) 1 ∈ Uθ τ K := mem_rootSubgroup.2 ⟨1, rfl⟩
      have := congrArg (baseChangeGL (algebraMap K D.L)) (hcθ _ hu)
      rw [map_mul, map_mul, baseChangeGL_pinnedX, map_one] at this
      rw [this]
      group
    have key := Lθ_centralizes_Uθ hxL h1
    intro u hu
    have hgu : D.g * u * D.g⁻¹ ∈ Uθ τ D.L :=
      (Subgroup.mem_normalizer_iff.1 (Pθ_le_normalizer_Uθ τ D.L (Lθ_le_Pθ τ D.L hgL)) u).1 hu
    have h2 := key _ hgu
    unfold hat
    calc D.g⁻¹ * baseChangeGL (algebraMap K D.L) x * D.g * u
        = D.g⁻¹ * (baseChangeGL (algebraMap K D.L) x * (D.g * u * D.g⁻¹)) * D.g := by group
      _ = D.g⁻¹ * ((D.g * u * D.g⁻¹) * baseChangeGL (algebraMap K D.L) x) * D.g := by rw [h2]
      _ = u * (D.g⁻¹ * baseChangeGL (algebraMap K D.L) x * D.g) := by group
  · have h1 : baseChangeGL (algebraMap K D.L) x * pinnedX τ D.L (-highRoot τ) 1 *
        (baseChangeGL (algebraMap K D.L) x)⁻¹ = pinnedX τ D.L (-highRoot τ) 1 := by
      have hu : pinnedX τ K (-highRoot τ) 1 ∈ Heis.Uneg τ K := mem_rootSubgroup.2 ⟨1, rfl⟩
      have := congrArg (baseChangeGL (algebraMap K D.L)) (hcn _ hu)
      rw [map_mul, map_mul, baseChangeGL_pinnedX, map_one] at this
      rw [this]
      group
    have key := Lθ_centralizes_Uneg hxL h1
    intro u hu
    have hgu : D.g * u * D.g⁻¹ ∈ Heis.Uneg τ D.L :=
      (Subgroup.mem_normalizer_iff.1 (Lθ_le_normalizer_Uneg τ D.L hgL) u).1 hu
    have h2 := key _ hgu
    unfold hat
    calc D.g⁻¹ * baseChangeGL (algebraMap K D.L) x * D.g * u
        = D.g⁻¹ * (baseChangeGL (algebraMap K D.L) x * (D.g * u * D.g⁻¹)) * D.g := by group
      _ = D.g⁻¹ * ((D.g * u * D.g⁻¹) * baseChangeGL (algebraMap K D.L) x) * D.g := by rw [h2]
      _ = u * (D.g⁻¹ * baseChangeGL (algebraMap K D.L) x * D.g) := by group

end Hat

section Roots

variable {τ : Tag}

theorem rootReflection_smul_formula (β : Fin τ.rank → ℤ) (hβ : IsRoot τ β)
    (v : Fin τ.rank → ℤ) :
    rootReflection β • v = v - (2 * iform β v / iform β β) • β :=
  ((exceptional_Lang_root_rank_one_torus_transport τ ℚ hβ).2.2.2.1 v).1

theorem refl_neg_deg1 {δ : Fin τ.rank → ℤ} (hδ : δ ∈ Deg1 τ) :
    rootReflection (highRoot τ) • (-δ) = highRoot τ - δ := by
  rw [rootReflection_smul_formula _ (isRoot_highRoot τ)]
  have hd : δ (iθ τ) = 1 := hδ.2
  have h1 : iform (highRoot τ) (-δ) = -(cθ τ) := by
    rw [iform_highRoot_apply, Pi.neg_apply, hd]
    ring
  have h2 : iform (highRoot τ) (highRoot τ) = cθ τ * 2 := by
    rw [iform_highRoot_apply, CoordAux.highRoot_degree]
  rw [h1, h2]
  have e : 2 * -(cθ τ) / (cθ τ * 2) = -1 := by
    rw [show 2 * -(cθ τ) = (-1) * (cθ τ * 2) by ring]
    exact Int.mul_ediv_cancel _ (mul_ne_zero (cθ_ne_zero τ) two_ne_zero)
  rw [e, neg_one_zsmul]
  abel

theorem refl_theta_sub_deg1 {δ : Fin τ.rank → ℤ} (hδ : δ ∈ Deg1 τ) :
    rootReflection (highRoot τ) • (highRoot τ - δ) = -δ := by
  rw [rootReflection_smul_formula _ (isRoot_highRoot τ)]
  have hd : δ (iθ τ) = 1 := hδ.2
  have h1 : iform (highRoot τ) (highRoot τ - δ) = cθ τ := by
    rw [iform_highRoot_apply, Pi.sub_apply, CoordAux.highRoot_degree, hd]
    ring
  have h2 : iform (highRoot τ) (highRoot τ) = cθ τ * 2 := by
    rw [iform_highRoot_apply, CoordAux.highRoot_degree]
  rw [h1, h2]
  have e : 2 * cθ τ / (cθ τ * 2) = 1 := by
    rw [show 2 * cθ τ = 1 * (cθ τ * 2) by ring]
    exact Int.mul_ediv_cancel _ (mul_ne_zero (cθ_ne_zero τ) two_ne_zero)
  rw [e, one_zsmul]
  abel

theorem isRoot_theta_sub {δ : Fin τ.rank → ℤ} (hδ : δ ∈ Deg1 τ) : IsRoot τ (highRoot τ - δ) := by
  rw [← refl_neg_deg1 hδ]
  exact IsRoot.smul (IsRoot.neg hδ.1) _

theorem theta_sub_mem_Deg1 {δ : Fin τ.rank → ℤ} (hδ : δ ∈ Deg1 τ) :
    highRoot τ - δ ∈ Deg1 τ := by
  refine ⟨isRoot_theta_sub hδ, ?_⟩
  have hd : δ (iθ τ) = 1 := hδ.2
  show (highRoot τ - δ) (iθ τ) = 1
  rw [Pi.sub_apply, CoordAux.highRoot_degree, hd]
  norm_num

theorem centralizes_neg_of_theta_sub {L : Type} [Field L] {ĝ : ModGL τ L}
    (hθ : ∀ u ∈ Uθ τ L, ĝ * u = u * ĝ) (hn : ∀ u ∈ Heis.Uneg τ L, ĝ * u = u * ĝ)
    {δ : Fin τ.rank → ℤ} (hδ : δ ∈ Deg1 τ)
    (h : ∀ c, ĝ * pinnedX τ L (highRoot τ - δ) c = pinnedX τ L (highRoot τ - δ) c * ĝ) (d : L) :
    ĝ * pinnedX τ L (-δ) d = pinnedX τ L (-δ) d * ĝ := by
  obtain ⟨hrank, -, hmono, -⟩ :=
    exceptional_Lang_root_rank_one_torus_transport τ L (isRoot_highRoot τ)
  obtain ⟨hnm, hπ⟩ := hmono 1
  have hnU : rootWeylSL2 τ L (highRoot τ) 1 ∈ Uθ τ L ⊔ Heis.Uneg τ L := by
    rw [← hrank]
    exact ⟨nSL 1, rfl⟩
  have hnc : Commute ĝ (rootWeylSL2 τ L (highRoot τ) 1) := centralizes_sup hθ hn _ hnU
  obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hnm (isRoot_theta_sub hδ)
  rw [hπ, refl_theta_sub_deg1 hδ] at hμ
  have key : ∀ c, ĝ * pinnedX τ L (-δ) (μ * c) = pinnedX τ L (-δ) (μ * c) * ĝ := by
    intro c
    rw [← hμ c]
    have hX : Commute ĝ (pinnedX τ L (highRoot τ - δ) c) := h c
    exact ((hnc.mul_right hX).mul_right hnc.inv_right).eq
  have e : (μ : L) * (((μ⁻¹ : Lˣ) : L) * d) = d := by
    rw [← mul_assoc, Units.mul_inv, one_mul]
  have := key (((μ⁻¹ : Lˣ) : L) * d)
  rwa [e] at this

end Roots

section FrameFacts

variable {τ : Tag} {K : Type} [Field K] [Finite K] {w : WeylGroup τ}

theorem rootSubgroup_le_frame' (D : LangLevi τ K w) {S : Set (Fin τ.rank → ℤ)}
    {β : Fin τ.rank → ℤ} (hβS : β ∈ S)
    (hg : D.g ∈ Subgroup.normalizer (rootSubgroup τ D.L β : Set (ModGL τ D.L))) :
    rootSubgroup τ K β ≤ D.frame S := by
  intro x hx
  rw [mem_frame_iff']
  refine ⟨rootSubgroup_le_adjointGroup β hx, ?_⟩
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
  rw [baseChangeGL_pinnedX]
  have h1 := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) _).1
    (mem_rootSubgroup.2 ⟨algebraMap K D.L c, rfl⟩ :
      pinnedX τ D.L β (algebraMap K D.L c) ∈ rootSubgroup τ D.L β)
  rw [inv_inv] at h1
  exact Subgroup.mem_iSup_of_mem β (Subgroup.mem_iSup_of_mem hβS h1)

end FrameFacts

section ClassFacts

theorem iθ_not_mem_J₂' (c : TwClass) : (iθ c.tag).val ∉ c.J₂ := by
  cases c <;> decide

theorem iform_highRoot_eq_zero' (c : TwClass) {α : Fin c.tag.rank → ℤ} (hα : α ∈ c.S₂) :
    iform (highRoot c.tag) α = 0 := by
  rw [iform_highRoot_apply, hα.2 _ (iθ_not_mem_J₂' c), mul_zero]

theorem highRoot_mem_S₁' (c : TwClass) : highRoot c.tag ∈ c.S₁ :=
  ⟨isRoot_highRoot _, fun _ hα => iform_highRoot_eq_zero' c hα⟩

theorem neg_highRoot_mem_S₁' (c : TwClass) : -highRoot c.tag ∈ c.S₁ :=
  ⟨isRoot_neg_highRoot _, fun _ hα => by
    rw [iform_neg_left, iform_highRoot_eq_zero' c hα, neg_zero]⟩

theorem f4_not_isRoot_add' : ∀ α ∈ rootFinset Tag.F4,
    (∀ β ∈ rootFinset Tag.F4, (∀ i : Fin Tag.F4.rank, i.val ∉ TwClass.f4Six.J₂ → β i = 0) →
      iform α β = 0) →
    ∀ β ∈ rootFinset Tag.F4, (∀ i : Fin Tag.F4.rank, i.val ∉ TwClass.f4Six.J₂ → β i = 0) →
      α + β ∉ rootFinset Tag.F4 := by
  decide +kernel

theorem not_isRoot_add_f4' {α β : Fin Tag.F4.rank → ℤ} (hα : α ∈ TwClass.f4Six.S₁)
    (hβ : β ∈ TwClass.f4Six.S₂) : ¬ IsRoot Tag.F4 (α + β) := fun h =>
  f4_not_isRoot_add' α (mem_rootFinset.2 hα.1)
    (fun β' hβ' hs => hα.2 β' ⟨mem_rootFinset.1 hβ', hs⟩) β (mem_rootFinset.2 hβ.1) hβ.2
    (mem_rootFinset.2 h)

theorem rootSpan_commute' (c : TwClass) (L : Type) [Field L] :
    ∀ x ∈ rootSpan c.tag L c.S₁, ∀ y ∈ rootSpan c.tag L c.S₂, x * y = y * x := by
  cases c with
  | f4Six =>
    refine rootSpan_commute_of_gen' fun α hα β hβ c d => ?_
    exact pinnedX_commute_of_iform_eq_zero L hα.1 hβ.1 (hα.2 β hβ) (not_isRoot_add_f4' hα hβ) c d
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

theorem smul_mem_S₁ (c : TwClass) (hd : TwClassData c) {β : Fin c.tag.rank → ℤ}
    (hβ : β ∈ c.S₁) : c.w • β ∈ c.S₁ := by
  refine ⟨IsRoot.smul hβ.1 c.w, fun α hα => ?_⟩
  have h0 := hβ.2 _ (hd.wS₂ α hα)
  have e := iform_smul c.w⁻¹ (c.w • β) α
  rw [inv_smul_smul] at e
  rw [← e]
  exact h0

theorem theta_sub_mem_S₁ (c : TwClass) {δ : Fin c.tag.rank → ℤ} (hδ : δ ∈ c.S₁)
    (hδ1 : δ ∈ Deg1 c.tag) : highRoot c.tag - δ ∈ c.S₁ :=
  ⟨isRoot_theta_sub hδ1, fun α hα => by
    rw [iform_sub_left, (highRoot_mem_S₁' c).2 α hα, hδ.2 α hα, sub_zero]⟩

end ClassFacts

theorem rootChar_eq_one_of_commute (c : TwClass) {L : Type} [Field L] {ĝ h y : ModGL c.tag L}
    (a : Fin c.tag.rank → Lˣ) (hh : h = rootDiagUnit c.tag a) (hxy : ĝ = h * y)
    (hy : y ∈ rootSpan c.tag L c.S₂) {δ : Fin c.tag.rank → ℤ} (hδ : δ ∈ c.S₁)
    (hcom : ĝ * pinnedX c.tag L δ 1 = pinnedX c.tag L δ 1 * ĝ) : rootChar a δ = 1 := by
  have hy' : Commute y (pinnedX c.tag L δ 1) :=
    (rootSpan_commute' c L _ (pinnedX_mem_rootSpan hδ 1) _ hy).symm
  have hcom' : Commute ĝ (pinnedX c.tag L δ 1) := hcom
  have hh' : Commute h (pinnedX c.tag L δ 1) := by
    have e : h = ĝ * y⁻¹ := by rw [hxy]; group
    rw [e]
    exact hcom'.mul_left hy'.inv_left
  have e1 := rootDiagUnit_conj_pinnedX a hδ.1 (1 : L)
  rw [← hh] at e1
  have e2 : h * pinnedX c.tag L δ 1 * h⁻¹ = pinnedX c.tag L δ 1 := by
    rw [hh'.eq]
    group
  rw [e2] at e1
  have := pinnedX_injective c.tag L δ e1
  exact Units.ext (by simpa using this.symm)

theorem central_main (c : TwClass) {K : Type} [Field K] [Finite K] (D : LangLevi c.tag K c.w)
    {x : ModGL c.tag K} (hx : x ∈ adjointGroup c.tag K)
    (hxX : ∀ y ∈ D.frame c.S₁, x * y = y * x) : x ∈ D.frame c.S₂ := by
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  have hd := twClassData c
  obtain ⟨k, ω, hlev⟩ := hd.levi
  have hUθ : Uθ c.tag K ≤ D.frame c.S₁ :=
    rootSubgroup_le_frame' D (highRoot_mem_S₁' c)
      (Pθ_le_normalizer_Uθ c.tag D.L (Lθ_le_Pθ c.tag D.L D.g_mem))
  have hUn : Heis.Uneg c.tag K ≤ D.frame c.S₁ :=
    rootSubgroup_le_frame' D (neg_highRoot_mem_S₁' c) (Lθ_le_normalizer_Uneg c.tag D.L D.g_mem)
  have hcθ : ∀ u ∈ Uθ c.tag K, x * u = u * x := fun u hu => hxX u (hUθ hu)
  have hcn : ∀ u ∈ Heis.Uneg c.tag K, x * u = u * x := fun u hu => hxX u (hUn hu)
  have hxL : x ∈ Lθ c.tag K :=
    Heis.centralizer_Uθ_inf_centralizer_Uneg_le_Lθ c.tag K hx hcθ hcn
  obtain ⟨hhL, hhθ, hhn⟩ := hat_mem_Lθ_and_centralizes D hxL hcθ hcn
  have hwθ := hd.wθ
  have hwS : ∀ β ∈ c.S₁, c.w • β ∈ c.S₁ := fun β hβ => smul_mem_S₁ c hd hβ
  have hdeg : ∀ β, β ∈ c.S₁ → β ∈ Deg1 c.tag → ∀ cc : D.L,
      hat D x * pinnedX c.tag D.L β cc = pinnedX c.tag D.L β cc * hat D x :=
    fun β hβS hβ1 cc => centralizes_deg1 D (highRoot_mem_S₁' c) hwθ hwS hxX hhθ hhn hβS hβ1 cc
  have hδ : ∀ i, ω i • highRoot c.tag ∈ c.S₁ ∧ ω i • highRoot c.tag ∈ Deg1 c.tag := fun i =>
    ⟨(hlev.mem i).1, (hlev.mem i).1.1, (hlev.mem i).2⟩
  have hnegδ : ∀ i (cc : D.L), hat D x * pinnedX c.tag D.L (-(ω i • highRoot c.tag)) cc =
      pinnedX c.tag D.L (-(ω i • highRoot c.tag)) cc * hat D x := fun i cc => by
    obtain ⟨hS, h1⟩ := hδ i
    exact centralizes_neg_of_theta_sub hhθ hhn h1
      (fun cc' => hdeg _ (theta_sub_mem_S₁ c hS h1) (theta_sub_mem_Deg1 h1) cc') cc
  have hg : hat D x ∈ adjointGroup c.tag D.L := parabolicLevi_le_adjointGroup c.tag D.L (Jθ c.tag) hhL
  have hc : ∀ i, (∀ u ∈ conjSub (canonicalRep (coxeterSystem c.tag) D.L (ω i)) (Uθ c.tag D.L),
        hat D x * u = u * hat D x) ∧
      (∀ u ∈ conjSub (canonicalRep (coxeterSystem c.tag) D.L (ω i)) (Heis.Uneg c.tag D.L),
        hat D x * u = u * hat D x) := by
    intro i
    obtain ⟨ε, -, hε⟩ :=
      exists_canonicalRep_mul_pinnedX_mul_inv D.L (ω i) (isRoot_highRoot c.tag)
    obtain ⟨ε', -, hε'⟩ :=
      exists_canonicalRep_mul_pinnedX_mul_inv D.L (ω i) (isRoot_neg_highRoot c.tag)
    refine ⟨fun u hu => ?_, fun u hu => ?_⟩
    · obtain ⟨a, ha⟩ := mem_rootSubgroup.1 (mem_conjSub_iff.1 hu)
      have hu2 : u = pinnedX c.tag D.L (ω i • highRoot c.tag) (ε * a) := by
        rw [← hε a, ha]
        group
      rw [hu2]
      exact hdeg _ (hδ i).1 (hδ i).2 _
    · obtain ⟨a, ha⟩ := mem_rootSubgroup.1 (mem_conjSub_iff.1 hu)
      have hu2 : u = pinnedX c.tag D.L (-(ω i • highRoot c.tag)) (ε' * a) := by
        rw [← smul_neg, ← hε' a, ha]
        group
      rw [hu2]
      exact hnegδ i _
  obtain ⟨h, hhT, y, hy, hxy⟩ := levi_intersection ω {i : Fin c.tag.rank | i.val ∈ c.J₂}
    hlev.min (fun β hβ => by
      rw [Ipre_k] at hβ
      exact hlev.perp β hβ.1 hβ.2) hlev.fix hg hhθ hhn hc
  have hS₂eq : parabolicRoots c.tag {i : Fin c.tag.rank | i.val ∈ c.J₂} = c.S₂ :=
    Set.ext fun _ => Iff.rfl
  have hyS₂ : y ∈ rootSpan c.tag D.L c.S₂ := by
    rw [← hS₂eq]
    exact hy
  obtain ⟨a, ha, -⟩ := (exceptional_Lang_root_rank_one_torus_transport c.tag D.L
    (isRoot_highRoot c.tag)).2.2.2.2.2.1 h hhT
  have h₀ : rootChar a (highRoot c.tag) = 1 :=
    rootChar_eq_one_of_commute c a ha hxy hyS₂ (highRoot_mem_S₁' c)
      (by simpa using hhθ _ (mem_rootSubgroup.2 ⟨1, rfl⟩))
  have hδ1 : ∀ m, rootChar a (ω m • highRoot c.tag) = 1 := fun m =>
    rootChar_eq_one_of_commute c a ha hxy hyS₂ (hδ m).1 (hdeg _ (hδ m).1 (hδ m).2 1)
  have hT := rootDiagUnit_mem_rootSpan_of_chars (L := D.L) c.J₂ (highRoot c.tag)
    (fun m => ω m • highRoot c.tag) (fun v hv => hlev.lattice v hv) a h₀ hδ1
  rw [hS₂eq, ← ha] at hT
  rw [mem_frame_iff']
  refine ⟨hx, ?_⟩
  have : hat D x ∈ rootSpan c.tag D.L c.S₂ := by
    rw [hxy]
    exact mul_mem hT hyS₂
  exact this

theorem twCentral_aux (c : TwClass) {K : Type} [Field K] [Finite K] (D : LangLevi c.tag K c.w) :
    TwCentral (c.X₁ D) (c.X₂ D) := by
  have key : ∀ x ∈ adjointGroup c.tag K, (∀ y ∈ c.X₁ D, x * y = y * x) → x ∈ c.X₂ D :=
    fun x hx hxX => central_main c D hx hxX
  refine ⟨⟨⊥, fun a ha b hb => ?_, bot_le, fun g hg hgX => ?_⟩, fun g hg hgX _ => ?_⟩
  · rw [Subgroup.mem_bot] at ha hb
    rw [ha, hb]
  · rw [bot_sup_eq]
    exact key g hg hgX
  · exact (le_sup_right : c.X₂ D ≤ c.X₁ D ⊔ c.X₂ D) (key g hg hgX)

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.CentralAux
