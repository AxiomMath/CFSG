module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialOuterQ3
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerE8FourFiveQ2Char
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryTorus
public import CFSG.CharacterTheory.SteinbergBYFieldFour
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Classical CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.ClassicalInvolution.ModelFacts.Levi CFSG.CharacterTheory.SteinbergBY
open scoped MatrixGroups commutatorElement

section Plumbing

variable {τ : Tag} {L : Type} [Field L]

private theorem simplyLacedTag_of_E6_E7_E8 {τ : Tag}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) : SimplyLacedTag τ := by
  rcases hτ with rfl | rfl | rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

private theorem commute_conj_of_scale {G : Type*} [Group G] {z u X z₀ h₀ : G}
    (hco : Commute z (z₀ * u * z₀⁻¹)) (hscale : h₀ * X * h₀⁻¹ = u) :
    Commute ((z₀ * h₀)⁻¹ * z * (z₀ * h₀)) X := by
  have hmain : Commute z ((z₀ * h₀) * X * (z₀ * h₀)⁻¹) := by
    rw [show (z₀ * h₀) * X * (z₀ * h₀)⁻¹ = z₀ * u * z₀⁻¹ by
      rw [← hscale]
      group]
    exact hco
  have h' := (Commute.conj_iff (a := z) (b := (z₀ * h₀) * X * (z₀ * h₀)⁻¹)
    (h := (z₀ * h₀)⁻¹)).2 hmain
  simpa [mul_assoc] using h'

private theorem commute_undo_pinnedX {c : Lˣ} {γ : Fin τ.rank → ℤ} {z z₀ h₀ : ModGL τ L}
    (hgen : ∀ t, Commute ((z₀ * h₀)⁻¹ * z * (z₀ * h₀)) (pinnedX τ L γ t))
    (hscale : ∀ t, h₀ * pinnedX τ L γ t * h₀⁻¹ = pinnedX τ L γ (((c⁻¹ : Lˣ) : L) * t)) :
    ∀ s, Commute z (z₀ * pinnedX τ L γ s * z₀⁻¹) := by
  intro s
  have hmain : Commute ((z₀ * h₀)⁻¹ * z * (z₀ * h₀)) (pinnedX τ L γ ((c : L) * s)) :=
    hgen ((c : L) * s)
  have h' := (Commute.conj_iff (a := (z₀ * h₀)⁻¹ * z * (z₀ * h₀))
    (b := pinnedX τ L γ ((c : L) * s)) (h := z₀ * h₀)).2 hmain
  have e1 : (z₀ * h₀) * ((z₀ * h₀)⁻¹ * z * (z₀ * h₀)) * (z₀ * h₀)⁻¹ = z := by group
  rw [e1] at h'
  have e2 : (z₀ * h₀) * pinnedX τ L γ ((c : L) * s) * (z₀ * h₀)⁻¹ =
      z₀ * pinnedX τ L γ s * z₀⁻¹ := by
    rw [show (z₀ * h₀) * pinnedX τ L γ ((c : L) * s) * (z₀ * h₀)⁻¹ =
      z₀ * (h₀ * pinnedX τ L γ ((c : L) * s) * h₀⁻¹) * z₀⁻¹ by group,
      hscale ((c : L) * s), Units.inv_mul_cancel_left c s]
  rw [e2] at h'
  exact h'

end Plumbing

section Fixed

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]

private theorem outer_two_fixed_scalars_mul_one [CharP L 2]
    {φ₁ : ModGL τ L →* ModGL τ L} {δ : Fin τ.rank → ℤ} (hδr : IsRoot τ δ) {μ μ' : L}
    (hμ : μ ≠ 0) (hμ' : μ' ≠ 0)
    (hu : ∀ t, φ₁ (pinnedX τ L δ t) = pinnedX τ L δ (μ * t ^ 2))
    (hv : ∀ t, φ₁ (pinnedX τ L (-δ) t) = pinnedX τ L (-δ) (μ' * t ^ 2)) :
    μ * μ' = 1 := by
  haveI : PerfectRing L 2 := IsAlgClosed.perfectRing L 2
  obtain ⟨a, rfl⟩ : ∃ a : Lˣ, (a : L) = μ := ⟨Units.mk0 μ hμ, rfl⟩
  obtain ⟨b, rfl⟩ : ∃ b : Lˣ, (b : L) = μ' := ⟨Units.mk0 μ' hμ', rfl⟩
  have hinj : Function.Injective (rootSL2 τ L δ) := rootSL2_injective_of_field δ
  have hQ : ∀ B : SL2 L, φ₁ (rootSL2 τ L δ B) ∈ (rootSL2 τ L δ).range := by
    intro B
    rw [range_rootSL2_of_isRoot hδr]
    have hle : (rootSubgroup τ L δ ⊔ rootSubgroup τ L (-δ)).map φ₁ ≤
        rootSubgroup τ L δ ⊔ rootSubgroup τ L (-δ) := by
      rw [Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rw [rootSubgroup, MonoidHom.map_closure, Subgroup.closure_le]
        rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
        rw [hu]
        exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨_, rfl⟩)
      · rw [rootSubgroup, MonoidHom.map_closure, Subgroup.closure_le]
        rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
        rw [hv]
        exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨_, rfl⟩)
    have hB : rootSL2 τ L δ B ∈ rootSubgroup τ L δ ⊔ rootSubgroup τ L (-δ) := by
      rw [← range_rootSL2_of_isRoot hδr]
      exact ⟨B, rfl⟩
    exact hle ⟨_, hB, rfl⟩
  let T : SL2 L →* SL2 L :=
    (MonoidHom.ofInjective hinj).symm.toMonoidHom.comp
      ((φ₁.comp (rootSL2 τ L δ)).codRestrict _ hQ)
  have hT : ∀ B, rootSL2 τ L δ (T B) = φ₁ (rootSL2 τ L δ B) := fun B => by
    have := (MonoidHom.ofInjective hinj).apply_symm_apply ⟨φ₁ (rootSL2 τ L δ B), hQ B⟩
    exact congrArg Subtype.val this
  have hTu : ∀ c : L, T (uSL c) = uSL (a * frobeniusEquiv L 2 c) := by
    intro c
    apply hinj
    rw [hT, rootSL2_uSL_two, hu, rootSL2_uSL_two, frobeniusEquiv_def]
  have hTv : ∀ c : L, T (vSL c) = vSL (b * frobeniusEquiv L 2 c) := by
    intro c
    apply hinj
    rw [hT, rootSL2_vSL_two hδr, hv, rootSL2_vSL_two hδr, frobeniusEquiv_def]
  obtain ⟨hab, -⟩ := sl2_semilinear_root_compatibility (frobeniusEquiv L 2) a b T hTu hTv
  simpa using congrArg (fun u : Lˣ => (u : L)) hab

theorem outer_two_fixed_scalar [CharP L 2] {φ₁ : ModGL τ L →* ModGL τ L}
    {f : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ} (hpin : OuterPinned φ₁ f 2)
    {Ψ : Set (Fin τ.rank → ℤ)} (hf : IsIsometry Ψ f) {δ : Fin τ.rank → ℤ} (hδ : δ ∈ Ψ)
    (hδr : IsRoot τ δ) (hfix : f δ = δ) :
    ∃ c : Lˣ, (∀ t, φ₁ (pinnedX τ L δ t) = pinnedX τ L δ ((c : L) * t ^ 2)) ∧
      ∀ t, φ₁ (pinnedX τ L (-δ) t) = pinnedX τ L (-δ) (((c⁻¹ : Lˣ) : L) * t ^ 2) := by
  obtain ⟨-, μ, hμ, hu⟩ := hpin δ hδr
  obtain ⟨-, μ', hμ', hv⟩ := hpin (-δ) (IsRoot.neg hδr)
  have hnegfix : f (-δ) = -δ := by rw [hf.neg δ hδ, hfix]
  rw [hfix] at hu
  rw [hnegfix] at hv
  have hμμ' : μ * μ' = 1 := outer_two_fixed_scalars_mul_one hδr hμ hμ' hu hv
  obtain ⟨c, rfl⟩ : ∃ c : Lˣ, (c : L) = μ := ⟨Units.mk0 μ hμ, rfl⟩
  have hc' : c * Units.mk0 μ' hμ' = 1 := by
    ext
    simpa using hμμ'
  have hb : Units.mk0 μ' hμ' = c⁻¹ := eq_inv_of_mul_eq_one_right hc'
  refine ⟨c, ?_, ?_⟩
  · intro t
    rw [hu]
  · intro t
    have hμ'inv : μ' = ((c⁻¹ : Lˣ) : L) := congrArg (fun u : Lˣ => (u : L)) hb
    rw [hv, hμ'inv]

end Fixed

section ScalePair

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]

theorem exists_torus_scale_pair (hsl : SimplyLacedTag τ) {δ δ' : Fin τ.rank → ℤ}
    (hδ : IsRoot τ δ) (hδ' : IsRoot τ δ') (h : iform δ δ' = -1) (c c' : Lˣ) :
    ∃ h₀ : ModGL τ L, ∀ t,
      h₀ * pinnedX τ L δ t * h₀⁻¹ = pinnedX τ L δ ((c : L) * t) ∧
      h₀ * pinnedX τ L (-δ) t * h₀⁻¹ = pinnedX τ L (-δ) (((c⁻¹ : Lˣ) : L) * t) ∧
      h₀ * pinnedX τ L δ' t * h₀⁻¹ = pinnedX τ L δ' ((c' : L) * t) ∧
      h₀ * pinnedX τ L (-δ') t * h₀⁻¹ = pinnedX τ L (-δ') (((c'⁻¹ : Lˣ) : L) * t) := by
  classical
  have hδn : iform δ δ = 2 := outer_iform_self_of_simplyLaced hsl hδ
  have hδ'n : iform δ' δ' = 2 := outer_iform_self_of_simplyLaced hsl hδ'
  have hpair : A2Pairing δ δ' :=
    ⟨by rw [hδn, hδ'n], by omega, by rw [h, hδn]; norm_num⟩
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq ((c' * c ^ 2 : Lˣ) : L)
    (by norm_num : 0 < 3)
  have hx0 : x ≠ 0 := by
    intro hx0
    rw [hx0, zero_pow (by norm_num : (3 : ℕ) ≠ 0)] at hx
    exact (Units.ne_zero (c' * c ^ 2)) hx.symm
  let xu : Lˣ := Units.mk0 x hx0
  have hxu : (xu : L) = x := rfl
  let y : Lˣ := xu ^ 2 * c⁻¹
  have hx3 : xu ^ 3 = c' * c ^ 2 := by
    ext
    simpa [hxu] using hx
  have hxy : xu ^ 2 * y⁻¹ = c := by
    have h1 : c * xu ^ 2 * c⁻¹ = xu ^ 2 := by
      rw [mul_comm c (xu ^ 2), mul_assoc, mul_inv_cancel, mul_one]
    have h : xu ^ 2 = c * y := by
      rw [show y = xu ^ 2 * c⁻¹ from rfl, ← mul_assoc, h1]
    nth_rewrite 1 [h]
    rw [mul_assoc, mul_inv_cancel, mul_one]
  have hx'y' : xu⁻¹ * y ^ 2 = c' := by
    have hxx : xu⁻¹ * (xu * xu ^ 3) = xu ^ 3 := by
      rw [← mul_assoc, inv_mul_cancel, one_mul]
    have e : xu⁻¹ * y ^ 2 = xu ^ 3 * (c ^ 2)⁻¹ := by
      rw [show y = xu ^ 2 * c⁻¹ from rfl, mul_pow, inv_pow,
        show (xu ^ 2) ^ 2 = xu ^ 4 by rw [← pow_mul]]
      rw [show xu ^ 4 = xu * xu ^ 3 by rw [pow_succ'], ← mul_assoc, hxx]
    rw [e, hx3, mul_assoc, mul_inv_cancel, mul_one]
  refine ⟨torusPair L δ δ' xu y, fun t => ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [torusPair_conj_theta hδ hδ' hpair xu y t, hxy]
  · rw [torusPair_conj_neg_theta hδ hδ' hpair xu y t, hxy]
  · rw [torusPair_conj_delta hδ hδ' hpair xu y t, hx'y']
  · rw [torusPair_conj_neg_delta hδ hδ' hpair xu y t, hx'y']

end ScalePair

section FixedCommute

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]

private theorem pinnedX_fixed_of_scalar [CharP L 2] {φ₁ : ModGL τ L →* ModGL τ L}
    {β : Fin τ.rank → ℤ} {c s : L}
    (hc : ∀ t, φ₁ (pinnedX τ L β t) = pinnedX τ L β (c * t ^ 2)) (hs : c * s ^ 2 = s) :
    φ₁ (pinnedX τ L β s) = pinnedX τ L β s ∧
      pinnedX τ L β s * pinnedX τ L β s = 1 := by
  constructor
  · rw [hc, hs]
  · rw [← pinnedX_add, CharTwo.add_self_eq_zero, pinnedX_zero]

private theorem outer_two_fixed_involutions [CharP L 2]
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    {f : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ} (hf : IsIsometry Ψ f)
    {φ₁ : ModGL τ L →* ModGL τ L} (hpin : OuterPinned φ₁ f 2) {z z₀ : ModGL τ L}
    (hfixc : ∀ g ∈ rootSpan τ L Ψ, φ₁ g = g → g * g = 1 → Commute z (z₀ * g * z₀⁻¹))
    {δ δ' : Fin τ.rank → ℤ} (hδ : δ ∈ Ψ) (hδ' : δ' ∈ Ψ) (hfδ : f δ = δ) (hfδ' : f δ' = δ') :
    ∃ c c' : Lˣ,
      Commute z (z₀ * pinnedX τ L δ ((c⁻¹ : Lˣ) : L) * z₀⁻¹) ∧
      Commute z (z₀ * pinnedX τ L (-δ) ((c : L)) * z₀⁻¹) ∧
      Commute z (z₀ * pinnedX τ L δ' ((c'⁻¹ : Lˣ) : L) * z₀⁻¹) ∧
      Commute z (z₀ * pinnedX τ L (-δ') ((c' : L)) * z₀⁻¹) := by
  have hδr : IsRoot τ δ := hΨ.isRoot δ hδ
  have hδ'r : IsRoot τ δ' := hΨ.isRoot δ' hδ'
  obtain ⟨c, hc, hcn⟩ := outer_two_fixed_scalar hpin hf hδ hδr hfδ
  obtain ⟨c', hc', hc'n⟩ := outer_two_fixed_scalar hpin hf hδ' hδ'r hfδ'
  refine ⟨c, c', ?_, ?_, ?_, ?_⟩
  · obtain ⟨hfix, hsq⟩ := pinnedX_fixed_of_scalar hc
      (s := ((c⁻¹ : Lˣ) : L)) (by rw [pow_two]; exact Units.mul_inv_cancel_left c _)
    exact hfixc _ (pinnedX_mem_rootSpan hδ _) hfix hsq
  · obtain ⟨hfix, hsq⟩ := pinnedX_fixed_of_scalar hcn
      (s := (c : L)) (by rw [pow_two]; exact Units.inv_mul_cancel_left c _)
    exact hfixc _ (pinnedX_mem_rootSpan (hΨ.neg_mem δ hδ) _) hfix hsq
  · obtain ⟨hfix, hsq⟩ := pinnedX_fixed_of_scalar hc'
      (s := ((c'⁻¹ : Lˣ) : L)) (by rw [pow_two]; exact Units.mul_inv_cancel_left c' _)
    exact hfixc _ (pinnedX_mem_rootSpan hδ' _) hfix hsq
  · obtain ⟨hfix, hsq⟩ := pinnedX_fixed_of_scalar hc'n
      (s := (c' : L)) (by rw [pow_two]; exact Units.inv_mul_cancel_left c' _)
    exact hfixc _ (pinnedX_mem_rootSpan (hΨ.neg_mem δ' hδ') _) hfix hsq

private theorem outer_two_fixed_conj_of_tableCheck [CharP L 2]
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hcheck : RootOps.tableCheck τ = true)
    (hsl : SimplyLacedTag τ) {δ δ' : Fin τ.rank → ℤ} (hδr : IsRoot τ δ)
    (hδ'r : IsRoot τ δ') (h : iform δ δ' = -1) {z z₀ : ModGL τ L} {c c' : Lˣ}
    (hco1 : Commute z (z₀ * pinnedX τ L δ ((c⁻¹ : Lˣ) : L) * z₀⁻¹))
    (hco2 : Commute z (z₀ * pinnedX τ L (-δ) ((c : L)) * z₀⁻¹))
    (hco3 : Commute z (z₀ * pinnedX τ L δ' ((c'⁻¹ : Lˣ) : L) * z₀⁻¹))
    (hco4 : Commute z (z₀ * pinnedX τ L (-δ') ((c' : L)) * z₀⁻¹)) :
    ∃ h₀ : ModGL τ L,
      (∀ t, Commute ((z₀ * h₀)⁻¹ * z * (z₀ * h₀)) (pinnedX τ L δ t)) ∧
      (∀ t, Commute ((z₀ * h₀)⁻¹ * z * (z₀ * h₀)) (pinnedX τ L (-δ) t)) ∧
      (∀ t, h₀ * pinnedX τ L δ t * h₀⁻¹ = pinnedX τ L δ (((c⁻¹ : Lˣ) : L) * t)) ∧
      ∀ t, h₀ * pinnedX τ L (-δ) t * h₀⁻¹ =
        pinnedX τ L (-δ) ((((c⁻¹ : Lˣ)⁻¹ : Lˣ) : L) * t) := by
  obtain ⟨h₀, hh₀⟩ := exists_torus_scale_pair hsl hδr hδ'r h c⁻¹ c'⁻¹
  have hc1 : Commute ((z₀ * h₀)⁻¹ * z * (z₀ * h₀)) (pinnedX τ L δ 1) :=
    commute_conj_of_scale (z := z) (u := pinnedX τ L δ ((c⁻¹ : Lˣ) : L))
      (X := pinnedX τ L δ 1) (z₀ := z₀) (h₀ := h₀) hco1 (by simpa using (hh₀ 1).1)
  have hc2 : Commute ((z₀ * h₀)⁻¹ * z * (z₀ * h₀)) (pinnedX τ L (-δ) 1) :=
    commute_conj_of_scale (z := z) (u := pinnedX τ L (-δ) ((c : L)))
      (X := pinnedX τ L (-δ) 1) (z₀ := z₀) (h₀ := h₀) hco2
      (by simpa [inv_inv] using (hh₀ 1).2.1)
  have hc3 : Commute ((z₀ * h₀)⁻¹ * z * (z₀ * h₀)) (pinnedX τ L δ' 1) :=
    commute_conj_of_scale (z := z) (u := pinnedX τ L δ' ((c'⁻¹ : Lˣ) : L))
      (X := pinnedX τ L δ' 1) (z₀ := z₀) (h₀ := h₀) hco3 (by simpa using (hh₀ 1).2.2.1)
  have hc4 : Commute ((z₀ * h₀)⁻¹ * z * (z₀ * h₀)) (pinnedX τ L (-δ') 1) :=
    commute_conj_of_scale (z := z) (u := pinnedX τ L (-δ') ((c' : L)))
      (X := pinnedX τ L (-δ') 1) (z₀ := z₀) (h₀ := h₀) hco4
      (by simpa [inv_inv] using (hh₀ 1).2.2.2)
  have hgenδ : ∀ t, Commute ((z₀ * h₀)⁻¹ * z * (z₀ * h₀)) (pinnedX τ L δ t) := fun t =>
    core_two_tag_of_tableCheck hτ hcheck ((z₀ * h₀)⁻¹ * z * (z₀ * h₀)) hδr hδ'r h hc1.eq hc2.eq hc3.eq hc4.eq t
  have hneg : iform (-δ) (-δ') = -1 := by
    rw [iform_neg_left, iform_neg_right, neg_neg, h]
  have hgennegδ : ∀ t, Commute ((z₀ * h₀)⁻¹ * z * (z₀ * h₀)) (pinnedX τ L (-δ) t) := fun t =>
    core_two_tag_of_tableCheck hτ hcheck ((z₀ * h₀)⁻¹ * z * (z₀ * h₀)) (IsRoot.neg hδr) (IsRoot.neg hδ'r) hneg
      hc2.eq (by simpa using hc1.eq) hc4.eq (by simpa using hc3.eq) t
  exact ⟨h₀, hgenδ, hgennegδ, fun t => (hh₀ t).1, fun t => (hh₀ t).2.1⟩

theorem outer_two_commute_fixed_of_tableCheck [CharP L 2] (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hcheck : RootOps.tableCheck τ = true)
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    {f : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ} (hf : IsIsometry Ψ f)
    {φ₁ : ModGL τ L →* ModGL τ L} (hpin : OuterPinned φ₁ f 2) {z z₀ : ModGL τ L}
    (hfixc : ∀ g ∈ rootSpan τ L Ψ, φ₁ g = g → g * g = 1 → Commute z (z₀ * g * z₀⁻¹))
    {δ δ' : Fin τ.rank → ℤ} (hδ : δ ∈ Ψ) (hδ' : δ' ∈ Ψ) (hfδ : f δ = δ) (hfδ' : f δ' = δ')
    (h : iform δ δ' = -1) :
    (∀ t, Commute z (z₀ * pinnedX τ L δ t * z₀⁻¹)) ∧
      ∀ t, Commute z (z₀ * pinnedX τ L (-δ) t * z₀⁻¹) := by
  obtain ⟨c, c', hco1, hco2, hco3, hco4⟩ :=
    outer_two_fixed_involutions hΨ hf hpin hfixc hδ hδ' hfδ hfδ'
  obtain ⟨h₀, hgenδ, hgennegδ, hsδ, hsneg⟩ := outer_two_fixed_conj_of_tableCheck hτ hcheck
    (simplyLacedTag_of_E6_E7_E8 hτ) (hΨ.isRoot δ hδ) (hΨ.isRoot δ' hδ') h
    hco1 hco2 hco3 hco4
  exact ⟨commute_undo_pinnedX (c := c) hgenδ hsδ,
    commute_undo_pinnedX (γ := -δ) (c := c⁻¹) hgennegδ hsneg⟩

end FixedCommute

section NonFixedCommute

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]

private theorem outer_two_cube_root_data [CharP L 2] {μ μ' : L} (hμ : μ ≠ 0)
    (hμ' : μ' ≠ 0) :
    ∃ t₀ ζ : L, t₀ ≠ 0 ∧ t₀ ^ 3 = (μ' * μ ^ 2)⁻¹ ∧ ζ ^ 2 = ζ + 1 ∧
      ζ ^ 2 + ζ = 1 ∧ ζ ^ 3 = 1 := by
  have hμμ : μ' * μ ^ 2 ≠ 0 := mul_ne_zero hμ' (pow_ne_zero 2 hμ)
  obtain ⟨t₀, ht₀⟩ := IsAlgClosed.exists_pow_nat_eq ((μ' * μ ^ 2)⁻¹)
    (by norm_num : 0 < 3)
  have ht₀0 : t₀ ≠ 0 := by
    intro h
    rw [h, zero_pow (by norm_num : (3 : ℕ) ≠ 0)] at ht₀
    exact inv_ne_zero hμμ ht₀.symm
  obtain ⟨ζ, hζ⟩ := FieldFour.exists_root_sq_add_self_add_one L
  have h2L : (2 : L) = 0 := CharTwo.two_eq_zero
  have hζ2 : ζ ^ 2 = ζ + 1 := by linear_combination hζ - (ζ + 1) * h2L
  have hζsum : ζ ^ 2 + ζ = 1 := by linear_combination hζ - h2L
  have hζ3 : ζ ^ 3 = 1 := by
    calc ζ ^ 3 = ζ * (ζ ^ 2) := by ring
      _ = ζ * (ζ + 1) := by rw [hζ2]
      _ = ζ * ζ + ζ := by ring
      _ = (ζ + 1) + ζ := by rw [← pow_two, hζ2]
      _ = 1 := by
        have hzz : ζ + ζ = 0 := CharTwo.add_self_eq_zero ζ
        calc ζ + 1 + ζ = (ζ + ζ) + 1 := by ring
          _ = 0 + 1 := by rw [hzz]
          _ = 1 := by rw [zero_add]
  exact ⟨t₀, ζ, ht₀0, ht₀, hζ2, hζsum, hζ3⟩

private theorem outer_two_fixed_point_scalar {μ μ' t : L} (hμμ : μ' * μ ^ 2 ≠ 0)
    (ht : t ^ 3 = (μ' * μ ^ 2)⁻¹) : μ' * (μ * t ^ 2) ^ 2 = t := by
  calc μ' * (μ * t ^ 2) ^ 2 = (μ' * μ ^ 2) * (t * t ^ 3) := by ring
    _ = (μ' * μ ^ 2) * (t * (μ' * μ ^ 2)⁻¹) := by rw [ht]
    _ = t := by
      rw [← mul_assoc, mul_comm (μ' * μ ^ 2) t, mul_assoc,
        mul_inv_cancel₀ hμμ, mul_one]

private theorem outer_two_nonfixed_fixed_element [CharP L 2]
    {φ₁ : ModGL τ L →* ModGL τ L} {γ γ' : Fin τ.rank → ℤ} {μ μ' : L}
    (hcomm : ∀ a b : L, Commute (pinnedX τ L γ a) (pinnedX τ L γ' b))
    (hu : ∀ t, φ₁ (pinnedX τ L γ t) = pinnedX τ L γ' (μ * t ^ 2))
    (hv : ∀ t, φ₁ (pinnedX τ L γ' t) = pinnedX τ L γ (μ' * t ^ 2))
    (hscalar : ∀ t : L, t ^ 3 = (μ' * μ ^ 2)⁻¹ → μ' * (μ * t ^ 2) ^ 2 = t)
    {t : L} (ht : t ^ 3 = (μ' * μ ^ 2)⁻¹) :
    φ₁ (pinnedX τ L γ t * pinnedX τ L γ' (μ * t ^ 2)) =
        pinnedX τ L γ t * pinnedX τ L γ' (μ * t ^ 2) ∧
      (pinnedX τ L γ t * pinnedX τ L γ' (μ * t ^ 2)) *
        (pinnedX τ L γ t * pinnedX τ L γ' (μ * t ^ 2)) = 1 := by
  constructor
  · rw [map_mul, hu, hv, (hcomm (μ' * (μ * t ^ 2) ^ 2) (μ * t ^ 2)).eq.symm,
      hscalar t ht]
  · have hA : pinnedX τ L γ t * pinnedX τ L γ t = 1 := by
      rw [← pinnedX_add, CharTwo.add_self_eq_zero, pinnedX_zero]
    have hB : pinnedX τ L γ' (μ * t ^ 2) * pinnedX τ L γ' (μ * t ^ 2) = 1 := by
      rw [← pinnedX_add, CharTwo.add_self_eq_zero, pinnedX_zero]
    have hAB : Commute (pinnedX τ L γ t) (pinnedX τ L γ' (μ * t ^ 2)) :=
      hcomm t (μ * t ^ 2)
    calc (pinnedX τ L γ t * pinnedX τ L γ' (μ * t ^ 2)) *
          (pinnedX τ L γ t * pinnedX τ L γ' (μ * t ^ 2))
        = pinnedX τ L γ t *
            (pinnedX τ L γ' (μ * t ^ 2) * pinnedX τ L γ t) *
              pinnedX τ L γ' (μ * t ^ 2) := by group
      _ = pinnedX τ L γ t *
            (pinnedX τ L γ t * pinnedX τ L γ' (μ * t ^ 2)) *
              pinnedX τ L γ' (μ * t ^ 2) := by rw [hAB.eq.symm]
      _ = (pinnedX τ L γ t * pinnedX τ L γ t) *
            (pinnedX τ L γ' (μ * t ^ 2) * pinnedX τ L γ' (μ * t ^ 2)) := by group
      _ = 1 := by rw [hA, hB, mul_one]

private theorem rootTorus_scales_pair {δ γ γ' : Fin τ.rank → ℤ} (hδ : IsRoot τ δ)
    (hγ : IsRoot τ γ) (hγ' : IsRoot τ γ') (hδγ : iform δ γ = -1)
    (hδγ' : iform δ γ' = -1) (hδn : iform δ δ = 2) (lam : Lˣ) :
    (∀ s, rootTorusSL2 τ L δ lam * pinnedX τ L γ s * (rootTorusSL2 τ L δ lam)⁻¹ =
        pinnedX τ L γ (((lam⁻¹ : Lˣ) : L) * s)) ∧
      ∀ s, rootTorusSL2 τ L δ lam * pinnedX τ L γ' s * (rootTorusSL2 τ L δ lam)⁻¹ =
        pinnedX τ L γ' (((lam⁻¹ : Lˣ) : L) * s) := by
  have eγ : 2 * iform δ γ / iform δ δ = -1 := by rw [hδγ, hδn]; norm_num
  have eγ' : 2 * iform δ γ' / iform δ δ = -1 := by rw [hδγ', hδn]; norm_num
  constructor
  · intro s
    rw [outer_rootTorusSL2_conj_pinnedX hδ hγ lam s, eγ]
    simp
  · intro s
    rw [outer_rootTorusSL2_conj_pinnedX hδ hγ' lam s, eγ']
    simp

private theorem outer_two_scaled_point {γ γ' δ : Fin τ.rank → ℤ} {μ : L} {z z₀ : ModGL τ L}
    {t c₀ : L} (hδ : IsRoot τ δ) (hγ : IsRoot τ γ) (hγ' : IsRoot τ γ')
    (hδγ : iform δ γ = -1) (hδγ' : iform δ γ' = -1) (hδn : iform δ δ = 2)
    (hδc : ∀ x ∈ rootRankOneGroup τ L δ, Commute z (z₀ * x * z₀⁻¹))
    (hA : Commute z (z₀ * (pinnedX τ L γ t * pinnedX τ L γ' (μ * t ^ 2)) * z₀⁻¹)) :
    Commute z (z₀ * (pinnedX τ L γ (c₀ * t) *
      pinnedX τ L γ' (c₀ * (μ * t ^ 2))) * z₀⁻¹) := by
  rcases eq_or_ne c₀ 0 with rfl | hc₀
  · simp only [zero_mul, pinnedX_zero, mul_one, mul_inv_cancel]
    exact Commute.one_right z
  · set lam : Lˣ := (Units.mk0 c₀ hc₀)⁻¹ with hlam
    have hlamc : ((lam⁻¹ : Lˣ) : L) = c₀ := by
      rw [hlam]
      simp
    have hT : Commute z (z₀ * rootTorusSL2 τ L δ lam * z₀⁻¹) := hδc _ ⟨HSL lam, rfl⟩
    have hs := rootTorus_scales_pair hδ hγ hγ' hδγ hδγ' hδn lam
    have e2 : rootTorusSL2 τ L δ lam *
        (pinnedX τ L γ t * pinnedX τ L γ' (μ * t ^ 2)) *
          (rootTorusSL2 τ L δ lam)⁻¹ =
        pinnedX τ L γ (c₀ * t) * pinnedX τ L γ' (c₀ * (μ * t ^ 2)) := by
      rw [show rootTorusSL2 τ L δ lam *
            (pinnedX τ L γ t * pinnedX τ L γ' (μ * t ^ 2)) *
              (rootTorusSL2 τ L δ lam)⁻¹ =
          (rootTorusSL2 τ L δ lam * pinnedX τ L γ t * (rootTorusSL2 τ L δ lam)⁻¹) *
            (rootTorusSL2 τ L δ lam * pinnedX τ L γ' (μ * t ^ 2) *
              (rootTorusSL2 τ L δ lam)⁻¹) by group, hs.1, hs.2, hlamc]
    have hconj : Commute z (z₀ *
        (rootTorusSL2 τ L δ lam * (pinnedX τ L γ t * pinnedX τ L γ' (μ * t ^ 2)) *
          (rootTorusSL2 τ L δ lam)⁻¹) * z₀⁻¹) := by
      have h' := (hT.mul_right hA).mul_right hT.inv_right
      have e1 : (z₀ * rootTorusSL2 τ L δ lam * z₀⁻¹) *
            (z₀ * (pinnedX τ L γ t * pinnedX τ L γ' (μ * t ^ 2)) * z₀⁻¹) *
              (z₀ * rootTorusSL2 τ L δ lam * z₀⁻¹)⁻¹ =
          z₀ * (rootTorusSL2 τ L δ lam *
            (pinnedX τ L γ t * pinnedX τ L γ' (μ * t ^ 2)) *
              (rootTorusSL2 τ L δ lam)⁻¹) * z₀⁻¹ := by group
      rw [← e1]
      exact h'
    rwa [e2] at hconj

private theorem outer_two_span_coeffs {μ u : L} {t₀ ζ : L}
    (hζsum : ζ ^ 2 + ζ = 1) (h2L : (2 : L) = 0) (ht₀0 : t₀ ≠ 0) :
    ∃ c₁ c₂ : L, c₁ * t₀ + c₂ * (ζ * t₀) = u ∧
      c₁ * (μ * t₀ ^ 2) + c₂ * (μ * (ζ * t₀) ^ 2) = 0 := by
  obtain ⟨c₂, hc₂⟩ : ∃ c₂ : L, c₂ * (ζ * t₀) = u * ζ := by
    refine ⟨u / t₀, ?_⟩
    field_simp
  set c₁ : L := c₂ * ζ ^ 2 with hc₁def
  have hc₁t : c₁ * t₀ = u * ζ ^ 2 := by
    rw [hc₁def]
    calc c₂ * ζ ^ 2 * t₀ = (c₂ * (ζ * t₀)) * ζ := by ring
      _ = (u * ζ) * ζ := by rw [hc₂]
      _ = u * ζ ^ 2 := by ring
  have hc₁sum : c₁ + c₂ * ζ ^ 2 = 0 := by
    rw [hc₁def]
    have e : c₂ * ζ ^ 2 + c₂ * ζ ^ 2 = (2 : L) * (c₂ * ζ ^ 2) := by ring
    rw [e, h2L, zero_mul]
  have hsum1 : c₁ * t₀ + c₂ * (ζ * t₀) = u := by
    rw [hc₁t, hc₂, ← mul_add, hζsum, mul_one]
  have hsum2 : c₁ * (μ * t₀ ^ 2) + c₂ * (μ * (ζ * t₀) ^ 2) = 0 := by
    have e : c₁ * (μ * t₀ ^ 2) + c₂ * (μ * (ζ * t₀) ^ 2) =
        μ * t₀ ^ 2 * (c₁ + c₂ * ζ ^ 2) := by ring
    rw [e, hc₁sum, mul_zero]
  exact ⟨c₁, c₂, hsum1, hsum2⟩

private theorem outer_two_pair_product {γ γ' : Fin τ.rank → ℤ} {μ u c₁ c₂ t₀ ζ : L}
    (hcomm : ∀ a b : L, Commute (pinnedX τ L γ a) (pinnedX τ L γ' b))
    (hsum1 : c₁ * t₀ + c₂ * (ζ * t₀) = u)
    (hsum2 : c₁ * (μ * t₀ ^ 2) + c₂ * (μ * (ζ * t₀) ^ 2) = 0) :
    (pinnedX τ L γ (c₁ * t₀) * pinnedX τ L γ' (c₁ * (μ * t₀ ^ 2))) *
        (pinnedX τ L γ (c₂ * (ζ * t₀)) *
          pinnedX τ L γ' (c₂ * (μ * (ζ * t₀) ^ 2))) = pinnedX τ L γ u := by
  have hBC : Commute (pinnedX τ L γ' (c₁ * (μ * t₀ ^ 2)))
      (pinnedX τ L γ (c₂ * (ζ * t₀))) :=
    (hcomm (c₂ * (ζ * t₀)) (c₁ * (μ * t₀ ^ 2))).symm
  calc (pinnedX τ L γ (c₁ * t₀) * pinnedX τ L γ' (c₁ * (μ * t₀ ^ 2))) *
        (pinnedX τ L γ (c₂ * (ζ * t₀)) *
          pinnedX τ L γ' (c₂ * (μ * (ζ * t₀) ^ 2)))
      = pinnedX τ L γ (c₁ * t₀) *
          (pinnedX τ L γ' (c₁ * (μ * t₀ ^ 2)) *
            pinnedX τ L γ (c₂ * (ζ * t₀))) *
              pinnedX τ L γ' (c₂ * (μ * (ζ * t₀) ^ 2)) := by group
    _ = pinnedX τ L γ (c₁ * t₀) *
          (pinnedX τ L γ (c₂ * (ζ * t₀)) *
            pinnedX τ L γ' (c₁ * (μ * t₀ ^ 2))) *
              pinnedX τ L γ' (c₂ * (μ * (ζ * t₀) ^ 2)) := by
      rw [hBC.eq.symm]
    _ = (pinnedX τ L γ (c₁ * t₀) * pinnedX τ L γ (c₂ * (ζ * t₀))) *
          (pinnedX τ L γ' (c₁ * (μ * t₀ ^ 2)) *
            pinnedX τ L γ' (c₂ * (μ * (ζ * t₀) ^ 2))) := by group
    _ = pinnedX τ L γ (c₁ * t₀ + c₂ * (ζ * t₀)) *
          pinnedX τ L γ' (c₁ * (μ * t₀ ^ 2) + c₂ * (μ * (ζ * t₀) ^ 2)) := by
      rw [← pinnedX_add, ← pinnedX_add]
    _ = pinnedX τ L γ u := by
      rw [hsum1, hsum2, pinnedX_zero, mul_one]

private theorem outer_two_nonfixed_span {γ γ' : Fin τ.rank → ℤ} {μ μ' : L} {z z₀ : ModGL τ L}
    (hcomm : ∀ a b : L, Commute (pinnedX τ L γ a) (pinnedX τ L γ' b))
    (hpoint : ∀ t : L, t ^ 3 = (μ' * μ ^ 2)⁻¹ → ∀ c₀ : L,
      Commute z (z₀ * (pinnedX τ L γ (c₀ * t) *
        pinnedX τ L γ' (c₀ * (μ * t ^ 2))) * z₀⁻¹))
    {t₀ ζ : L} (ht₀ : t₀ ^ 3 = (μ' * μ ^ 2)⁻¹) (hζ3 : ζ ^ 3 = 1)
    (hζsum : ζ ^ 2 + ζ = 1) (h2L : (2 : L) = 0) (ht₀0 : t₀ ≠ 0) :
    ∀ u, Commute z (z₀ * pinnedX τ L γ u * z₀⁻¹) := by
  have hζt₀ : (ζ * t₀) ^ 3 = (μ' * μ ^ 2)⁻¹ := by
    rw [mul_pow, hζ3, one_mul, ht₀]
  intro u
  obtain ⟨c₁, c₂, hsum1, hsum2⟩ := outer_two_span_coeffs hζsum h2L ht₀0
  have hprod : Commute z
      ((z₀ * (pinnedX τ L γ (c₁ * t₀) *
          pinnedX τ L γ' (c₁ * (μ * t₀ ^ 2))) * z₀⁻¹) *
        (z₀ * (pinnedX τ L γ (c₂ * (ζ * t₀)) *
          pinnedX τ L γ' (c₂ * (μ * (ζ * t₀) ^ 2))) * z₀⁻¹)) :=
    (hpoint t₀ ht₀ c₁).mul_right (hpoint (ζ * t₀) hζt₀ c₂)
  have hprod_eq := outer_two_pair_product hcomm hsum1 hsum2
  have eE : (z₀ * (pinnedX τ L γ (c₁ * t₀) *
        pinnedX τ L γ' (c₁ * (μ * t₀ ^ 2))) * z₀⁻¹) *
        (z₀ * (pinnedX τ L γ (c₂ * (ζ * t₀)) *
          pinnedX τ L γ' (c₂ * (μ * (ζ * t₀) ^ 2))) * z₀⁻¹) =
      z₀ * pinnedX τ L γ u * z₀⁻¹ := by
    rw [show (z₀ * (pinnedX τ L γ (c₁ * t₀) *
            pinnedX τ L γ' (c₁ * (μ * t₀ ^ 2))) * z₀⁻¹) *
          (z₀ * (pinnedX τ L γ (c₂ * (ζ * t₀)) *
            pinnedX τ L γ' (c₂ * (μ * (ζ * t₀) ^ 2))) * z₀⁻¹) =
        z₀ * ((pinnedX τ L γ (c₁ * t₀) *
            pinnedX τ L γ' (c₁ * (μ * t₀ ^ 2))) *
          (pinnedX τ L γ (c₂ * (ζ * t₀)) *
            pinnedX τ L γ' (c₂ * (μ * (ζ * t₀) ^ 2)))) * z₀⁻¹ by group,
      hprod_eq]
  rwa [eE] at hprod

theorem outer_two_commute_nonfixed [CharP L 2] (hsl : SimplyLacedTag τ)
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    {f : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ} (hf : IsIsometry Ψ f)
    {φ₁ : ModGL τ L →* ModGL τ L} (hpin : OuterPinned φ₁ f 2) {z z₀ : ModGL τ L}
    (hfixc : ∀ g ∈ rootSpan τ L Ψ, φ₁ g = g → g * g = 1 → Commute z (z₀ * g * z₀⁻¹))
    {γ δ : Fin τ.rank → ℤ} (hγ : γ ∈ Ψ) (hfγ : f γ ≠ γ) (hinv : f (f γ) = γ)
    (horth : iform γ (f γ) = 0) (hδ : δ ∈ Ψ) (hfδ : f δ = δ) (hγδ : iform γ δ = -1)
    (hδc : ∀ x ∈ rootRankOneGroup τ L δ, Commute z (z₀ * x * z₀⁻¹)) :
    ∀ u, Commute z (z₀ * pinnedX τ L γ u * z₀⁻¹) := by
  have hγr : IsRoot τ γ := hΨ.isRoot γ hγ
  have hfγmem : f γ ∈ Ψ := hf.bijOn.mapsTo hγ
  have hfγr : IsRoot τ (f γ) := hΨ.isRoot (f γ) hfγmem
  have hδr : IsRoot τ δ := hΨ.isRoot δ hδ
  have hnormγ : iform γ γ = 2 := outer_iform_self_of_simplyLaced hsl hγr
  have hnormfγ : iform (f γ) (f γ) = 2 := outer_iform_self_of_simplyLaced hsl hfγr
  have hnormδ : iform δ δ = 2 := outer_iform_self_of_simplyLaced hsl hδr
  have hadd : ¬ IsRoot τ (γ + f γ) := by
    intro hr
    have h4 : iform (γ + f γ) (γ + f γ) = 4 := by
      rw [iform_add_left, iform_add_right, iform_add_right, hnormγ, horth,
        iform_comm (f γ) γ, horth, hnormfγ]
      norm_num
    have h2 := outer_iform_self_of_simplyLaced hsl hr
    omega
  have hcommγ : ∀ a b : L, Commute (pinnedX τ L γ a) (pinnedX τ L (f γ) b) :=
    fun a b => outer_commute_pinnedX hγr hfγr horth hadd a b
  obtain ⟨-, μ, hμ, hu⟩ := hpin γ hγr
  obtain ⟨-, μ', hμ', hv⟩ := hpin (f γ) hfγr
  rw [hinv] at hv
  have hμμ : μ' * μ ^ 2 ≠ 0 := mul_ne_zero hμ' (pow_ne_zero 2 hμ)
  obtain ⟨t₀, ζ, ht₀0, ht₀, -, hζsum, hζ3⟩ := outer_two_cube_root_data hμ hμ'
  have hmem : ∀ t : L,
      pinnedX τ L γ t * pinnedX τ L (f γ) (μ * t ^ 2) ∈ rootSpan τ L Ψ :=
    fun t => mul_mem (pinnedX_mem_rootSpan hγ _) (pinnedX_mem_rootSpan hfγmem _)
  have hAt : ∀ t : L, t ^ 3 = (μ' * μ ^ 2)⁻¹ →
      Commute z (z₀ * (pinnedX τ L γ t * pinnedX τ L (f γ) (μ * t ^ 2)) * z₀⁻¹) := by
    intro t ht
    obtain ⟨hfix, hsq⟩ := outer_two_nonfixed_fixed_element hcommγ hu hv
      (fun s hs => outer_two_fixed_point_scalar hμμ hs) ht
    exact hfixc _ (hmem t) hfix hsq
  have hδγ : iform δ γ = -1 := by rw [iform_comm, hγδ]
  have hδfγ : iform δ (f γ) = -1 := by
    rw [iform_comm, ← hfδ, hf.iform_eq γ hγ δ hδ, hγδ]
  have hpoint : ∀ t : L, t ^ 3 = (μ' * μ ^ 2)⁻¹ → ∀ c₀ : L,
      Commute z (z₀ * (pinnedX τ L γ (c₀ * t) *
        pinnedX τ L (f γ) (c₀ * (μ * t ^ 2))) * z₀⁻¹) := by
    intro t ht c₀
    exact outer_two_scaled_point hδr hγr hfγr hδγ hδfγ hnormδ hδc (hAt t ht)
  exact outer_two_nonfixed_span hcommγ hpoint ht₀ hζ3 hζsum (CharTwo.two_eq_zero) ht₀0

end NonFixedCommute

section Assembly

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)

theorem outer_two_fixed_central {a : Fin τ.rank → Lˣ}
    (i : KernelComponent (rootCharHom a))
    (hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1)
    {z₀ : ModGL τ L} {φ₁ : ModGL τ L →* ModGL τ L}
    (hz₀n : ∀ g, g ∈ rootSpan τ L (componentRoots (rootCharHom a) i) ↔
      z₀ * g * z₀⁻¹ ∈ rootSpan τ L (componentRoots (rootCharHom a) i))
    (hφ₁ : ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      iterHom S.D.step (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
        (z₀ * g * z₀⁻¹) = z₀ * φ₁ g * z₀⁻¹)
    (hmem : ∀ g ∈ rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i), g ∈ S.D.model →
      (∃ n : ℕ, g ^ 2 ^ n = 1) → g ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i)
    {z : ModGL τ L}
    (hcomm : ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i, Commute z x) :
    ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i), φ₁ g = g → g * g = 1 →
      Commute z (z₀ * g * z₀⁻¹) := by
  intro g hg hfix hsq
  have hg' : z₀ * g * z₀⁻¹ ∈ rootSpan τ L (componentRoots (rootCharHom a) i) := (hz₀n g).1 hg
  have hmodel : z₀ * g * z₀⁻¹ ∈ S.D.model :=
    outer_conj_mem_model S i hs1 (fun h hh => (hz₀n h).1 hh) hφ₁ hg hfix
  have hrat : z₀ * g * z₀⁻¹ ∈
      rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i) :=
    rootSpan_mono (fun γ hγ =>
      (⟨0, γ, hγ, rfl⟩ : γ ∈ rationalRoots S.ρ (rootCharHom a) i)) hg'
  have h2pow : ∃ n : ℕ, (z₀ * g * z₀⁻¹) ^ 2 ^ n = 1 := by
    refine ⟨1, ?_⟩
    have hc : (z₀ * g * z₀⁻¹) * (z₀ * g * z₀⁻¹) = 1 := by
      calc (z₀ * g * z₀⁻¹) * (z₀ * g * z₀⁻¹) = z₀ * (g * g) * z₀⁻¹ := by group
        _ = 1 := by rw [hsq]; group
    show (z₀ * g * z₀⁻¹) ^ 2 = 1
    rw [pow_two]
    exact hc
  exact hcomm _ (hmem _ hrat hmodel h2pow)

private theorem outer_two_rootSpan_completion {Ψ : Set (Fin τ.rank → ℤ)} {z₀ z : ModGL τ L}
    (hz₀n : ∀ g, g ∈ rootSpan τ L Ψ ↔ z₀ * g * z₀⁻¹ ∈ rootSpan τ L Ψ)
    (hall : ∀ β ∈ Ψ, ∀ t, Commute z (z₀ * pinnedX τ L β t * z₀⁻¹)) :
    ∀ g ∈ rootSpan τ L Ψ, Commute z g := by
  have hmap : (rootSpan τ L Ψ).map (MulAut.conj z₀).toMonoidHom ≤
      Subgroup.centralizer {z} := by
    simp only [rootSpan, Subgroup.map_iSup]
    refine iSup₂_le fun γ hγ => ?_
    rw [rootSubgroup, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 (hall γ hγ t).symm.eq
  intro g hg
  have hg' : z₀⁻¹ * g * z₀ ∈ rootSpan τ L Ψ := by
    refine (hz₀n _).2 ?_
    have : z₀ * (z₀⁻¹ * g * z₀) * z₀⁻¹ = g := by group
    rw [this]
    exact hg
  have hcalc : (MulAut.conj z₀).toMonoidHom (z₀⁻¹ * g * z₀) = g := by
    show z₀ * (z₀⁻¹ * g * z₀) * z₀⁻¹ = g
    group
  have hmem' : g ∈ Subgroup.centralizer {z} := hmap (Subgroup.mem_map.2 ⟨_, hg', hcalc⟩)
  exact Commute.symm (Subgroup.mem_centralizer_singleton_iff.1 hmem')

private theorem outer_two_assembly_of_tableCheck
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hcheck : RootOps.tableCheck τ = true) [CharP L 2] {a : Fin τ.rank → Lˣ}
    (i : KernelComponent (rootCharHom a))
    (hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1)
    {f : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ} {z₀ : ModGL τ L}
    {φ₁ : ModGL τ L →* ModGL τ L}
    (hf : IsIsometry (componentRoots (rootCharHom a) i) f) (hpin : OuterPinned φ₁ f 2)
    (hz₀n : ∀ g, g ∈ rootSpan τ L (componentRoots (rootCharHom a) i) ↔
      z₀ * g * z₀⁻¹ ∈ rootSpan τ L (componentRoots (rootCharHom a) i))
    (hφ₁ : ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      iterHom S.D.step (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
        (z₀ * g * z₀⁻¹) = z₀ * φ₁ g * z₀⁻¹)
    (hinv : ∀ γ ∈ componentRoots (rootCharHom a) i, f (f γ) = γ)
    (horth : ∀ γ ∈ componentRoots (rootCharHom a) i, f γ ≠ γ → iform γ (f γ) = 0)
    (hR2 : ∀ δ ∈ componentRoots (rootCharHom a) i, f δ = δ →
      ∃ δ' ∈ componentRoots (rootCharHom a) i, f δ' = δ' ∧ iform δ δ' = -1)
    (hR3 : ∀ γ ∈ componentRoots (rootCharHom a) i, f γ ≠ γ →
      ∃ δ ∈ componentRoots (rootCharHom a) i, f δ = δ ∧ iform γ δ = -1)
    (hmem : ∀ g ∈ rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i), g ∈ S.D.model →
      (∃ n : ℕ, g ^ 2 ^ n = 1) → g ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i)
    (z : ModGL τ L) (hcomm : ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i, Commute z x) :
    ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i), Commute z g := by
  have hΨ : IsRootComponent (componentRoots (rootCharHom a) i) :=
    isRootComponent_componentRoots i
  have hfixc := outer_two_fixed_central S i hs1 hz₀n hφ₁ hmem hcomm
  have hfixed : ∀ δ ∈ componentRoots (rootCharHom a) i, f δ = δ →
      (∀ t, Commute z (z₀ * pinnedX τ L δ t * z₀⁻¹)) ∧
        ∀ t, Commute z (z₀ * pinnedX τ L (-δ) t * z₀⁻¹) := by
    intro δ hδ hfδ
    obtain ⟨δ', hδ', hfδ', hδδ'⟩ := hR2 δ hδ hfδ
    exact outer_two_commute_fixed_of_tableCheck hτ hcheck hΨ hf hpin hfixc hδ hδ' hfδ hfδ' hδδ'
  have hrankOne : ∀ δ ∈ componentRoots (rootCharHom a) i, f δ = δ →
      ∀ x ∈ rootRankOneGroup τ L δ, Commute z (z₀ * x * z₀⁻¹) := by
    intro δ hδ hfδ
    exact outer_commute_rankOne_of_pm (hΨ.isRoot δ hδ)
      (hfixed δ hδ hfδ).1 (hfixed δ hδ hfδ).2
  have hnonfixed : ∀ γ ∈ componentRoots (rootCharHom a) i, f γ ≠ γ →
      ∀ t, Commute z (z₀ * pinnedX τ L γ t * z₀⁻¹) := by
    intro γ hγ hfγ
    obtain ⟨δ, hδ, hfδ, hγδ⟩ := hR3 γ hγ hfγ
    exact outer_two_commute_nonfixed (simplyLacedTag_of_E6_E7_E8 hτ) hΨ hf hpin
      hfixc hγ hfγ (hinv γ hγ) (horth γ hγ hfγ) hδ hfδ hγδ (hrankOne δ hδ hfδ)
  have hall : ∀ β ∈ componentRoots (rootCharHom a) i, ∀ t,
      Commute z (z₀ * pinnedX τ L β t * z₀⁻¹) := by
    intro β hβ t
    by_cases hfβ : f β = β
    · exact (hfixed β hβ hfβ).1 t
    · exact hnonfixed β hβ hfβ t
  exact outer_two_rootSpan_completion hz₀n hall

theorem commute_rootSpan_of_commute_component_outer_two_of_tableCheck
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hcheck : RootOps.tableCheck τ = true) [CharP L 2] {a : Fin τ.rank → Lˣ}
    (i : KernelComponent (rootCharHom a))
    (hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1)
    {f : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ} {z₀ : ModGL τ L}
    {φ₁ : ModGL τ L →* ModGL τ L}
    (hf : IsIsometry (componentRoots (rootCharHom a) i) f) (hpin : OuterPinned φ₁ f 2)
    (hz₀n : ∀ g, g ∈ rootSpan τ L (componentRoots (rootCharHom a) i) ↔
      z₀ * g * z₀⁻¹ ∈ rootSpan τ L (componentRoots (rootCharHom a) i))
    (hφ₁ : ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      iterHom S.D.step (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
        (z₀ * g * z₀⁻¹) = z₀ * φ₁ g * z₀⁻¹)
    (hinv : ∀ γ ∈ componentRoots (rootCharHom a) i, f (f γ) = γ)
    (horth : ∀ γ ∈ componentRoots (rootCharHom a) i, f γ ≠ γ → iform γ (f γ) = 0)
    (hR2 : ∀ δ ∈ componentRoots (rootCharHom a) i, f δ = δ →
      ∃ δ' ∈ componentRoots (rootCharHom a) i, f δ' = δ' ∧ iform δ δ' = -1)
    (hR3 : ∀ γ ∈ componentRoots (rootCharHom a) i, f γ ≠ γ →
      ∃ δ ∈ componentRoots (rootCharHom a) i, f δ = δ ∧ iform γ δ = -1)
    (hmem : ∀ g ∈ rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i), g ∈ S.D.model →
      (∃ n : ℕ, g ^ 2 ^ n = 1) → g ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i)
    (z : ModGL τ L) (hcomm : ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i, Commute z x) :
    ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i), Commute z g :=
  outer_two_assembly_of_tableCheck S hτ hcheck i hs1 hf hpin hz₀n hφ₁ hinv horth hR2 hR3 hmem z hcomm

end Assembly

end CFSG.HardMathSupport.Timmesfeld.LangTorus
