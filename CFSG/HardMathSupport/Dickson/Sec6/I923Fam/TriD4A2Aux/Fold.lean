module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4A2Aux.TitsSimple
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4A2Aux.Residual

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

namespace CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4A2

theorem isSimpleGroup_of_dichotomy {G : Type*} [Group G] (S : Subgroup G) (hS : S ≠ ⊥)
    (h : ∀ A : Subgroup G, A ≤ S → (∀ s ∈ S, ∀ a ∈ A, s * a * s⁻¹ ∈ A) → A = ⊥ ∨ A = S) :
    IsSimpleGroup ↥S := by
  haveI : Nontrivial ↥S := (Subgroup.nontrivial_iff_ne_bot S).2 hS
  refine ⟨fun N hN => ?_⟩
  have hle : N.map S.subtype ≤ S := Subgroup.map_subtype_le N
  have hcl : ∀ s ∈ S, ∀ a ∈ N.map S.subtype, s * a * s⁻¹ ∈ N.map S.subtype := by
    intro s hs a ha
    obtain ⟨n, hn, rfl⟩ := ha
    refine ⟨⟨s, hs⟩ * n * ⟨s, hs⟩⁻¹, hN.conj_mem n hn ⟨s, hs⟩, ?_⟩
    simp
  rcases h _ hle hcl with h1 | h1
  · left
    exact (Subgroup.map_eq_bot_iff_of_injective N S.subtype_injective).1 h1
  · right
    apply Subgroup.map_injective S.subtype_injective
    rw [h1, Subgroup.map_top, Subgroup.range_subtype]

theorem conjBy_le_of_normal {X : Type*} [Group X] {S A : Subgroup X} [S.Normal] (hA : A ≤ S)
    (m : X) : conjBy m A ≤ S := by
  intro x hx
  rw [mem_conjBy_iff] at hx
  have := (inferInstance : S.Normal).conj_mem _ (hA hx) m⁻¹
  simpa [mul_assoc] using this

variable {X : Type*} [Group X] [Finite X] {H : Subgroup X} {r₁ r₂ : X} {U : Subgroup X}
  {root : ℤ → Subgroup X} {R : RGD2 6 H r₁ r₂ U root} {φ : X ≃* X}

theorem fold_residual_simple (hf : FoldData R φ) (hgen : (H ⊔ U) ⊔ R.N = ⊤)
    (hZ : ∀ g ∈ H, (∀ i, IsRoot 6 i → ∀ x ∈ root i, g * x = x * g) → g = 1)
    (hz : ∀ h ∈ H, φ ((r₁ * r₂) ^ 3 * h) ≠ (r₁ * r₂) ^ 3 * h)
    (hC : ∀ t ∈ H ⊓ foldFix φ, (∀ u ∈ U ⊓ foldFix φ, t * u = u * t) → t = 1)
    (E : Subgroup ↥(foldFix φ)) (hE : ⁅E, E⁆ = E)
    (hE1 : ∀ x ∈ foldRoot φ root 1, ∃ hx : x ∈ foldFix φ, (⟨x, hx⟩ : ↥(foldFix φ)) ∈ E) :
    ∃ S : Subgroup ↥(foldFix φ), ∃ _ : S.Normal, Group.IsSolvable (↥(foldFix φ) ⧸ S) ∧
      ⁅S, S⁆ = S ∧ IsSimpleGroup ↥S ∧
      ∀ u ∈ U ⊓ foldFix φ, ∃ hu : u ∈ foldFix φ, (⟨u, hu⟩ : ↥(foldFix φ)) ∈ S := by
  obtain ⟨S, hSn, hSperf, hSsolv⟩ := exists_residual ↥(foldFix φ)
  have hES : E ≤ S := perfect_le_of_solvable_quotient hE S hSsolv
  obtain ⟨r₁', r₂', h1, h2, h1H, h2H, R'⟩ := hf.exists_rgd2
  have hr₁ : r₁' ∈ foldFix φ := h1
  have hr₂ : r₂' ∈ foldFix φ := h2
  have hroot : ∀ i, IsRoot 3 i → foldRoot φ root i ≤ foldFix φ := fun i _ => inf_le_right
  have hgen' := R'.restrict_gen (foldFix φ) inf_le_right hr₁ hr₂ inf_le_right hroot
    (fun x hx => hf.generation hgen hZ hz h1 h1H h2 h2H hx)
  have RG := R'.restrict (foldFix φ) inf_le_right hr₁ hr₂ inf_le_right hroot
  haveI := RG.cartan_normal
  have hCG : ∀ t ∈ (H ⊓ foldFix φ).subgroupOf (foldFix φ),
      (∀ u ∈ (U ⊓ foldFix φ).subgroupOf (foldFix φ), t * u = u * t) → t = 1 := by
    intro t ht htc
    apply Subtype.ext
    exact hC t.1 ⟨(Subgroup.mem_subgroupOf.1 ht).1, t.2⟩ (fun u hu => by
      have := htc ⟨u, hu.2⟩ hu
      exact congrArg Subtype.val this)
  have hrootS : ∀ i, IsRoot 3 i → (fun i => (foldRoot φ root i).subgroupOf (foldFix φ)) i ≤ S := by
    obtain ⟨a1, a2, a3⟩ := RG.act₁
    obtain ⟨b1, b2, b3⟩ := RG.act₂
    have p1 : (foldRoot φ root 1).subgroupOf (foldFix φ) ≤ S := by
      intro x hx
      obtain ⟨hx', hxE⟩ := hE1 x.1 hx
      exact hES hxE
    have p2 : (foldRoot φ root 2).subgroupOf (foldFix φ) ≤ S := by
      obtain ⟨e, -⟩ := b3 1 le_rfl (by norm_num)
      have e' : conjBy (⟨r₂', hr₂⟩ : ↥(foldFix φ))⁻¹
          ((foldRoot φ root 1).subgroupOf (foldFix φ)) =
          (foldRoot φ root 2).subgroupOf (foldFix φ) := by
        simpa using e
      rw [← e']
      exact conjBy_le_of_normal p1 _
    have p3 : (foldRoot φ root 3).subgroupOf (foldFix φ) ≤ S := by
      obtain ⟨e, -⟩ := a3 2 (by norm_num) (by norm_num)
      have e' : conjBy (⟨r₁', hr₁⟩ : ↥(foldFix φ))⁻¹
          ((foldRoot φ root 2).subgroupOf (foldFix φ)) =
          (foldRoot φ root 3).subgroupOf (foldFix φ) := by
        simpa using e
      rw [← e']
      exact conjBy_le_of_normal p2 _
    have m1 : (foldRoot φ root (-1)).subgroupOf (foldFix φ) ≤ S := by
      rw [← a1]
      exact conjBy_le_of_normal p1 _
    have m3 : (foldRoot φ root (-3)).subgroupOf (foldFix φ) ≤ S := by
      have e' : conjBy (⟨r₂', hr₂⟩ : ↥(foldFix φ))⁻¹
          ((foldRoot φ root 3).subgroupOf (foldFix φ)) =
          (foldRoot φ root (-3)).subgroupOf (foldFix φ) := by
        simpa using b1
      rw [← e']
      exact conjBy_le_of_normal p3 _
    have m2 : (foldRoot φ root (-2)).subgroupOf (foldFix φ) ≤ S := by
      obtain ⟨-, e⟩ := a3 3 (by norm_num) (by norm_num)
      have e' : conjBy (⟨r₁', hr₁⟩ : ↥(foldFix φ))⁻¹
          ((foldRoot φ root (-3)).subgroupOf (foldFix φ)) =
          (foldRoot φ root (-2)).subgroupOf (foldFix φ) := by
        simpa using e
      rw [← e']
      exact conjBy_le_of_normal m3 _
    intro i hi
    have hi' : i = -3 ∨ i = -2 ∨ i = -1 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
      obtain ⟨h0, h3⟩ := hi
      omega
    rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [m3, m2, m1, p1, p2, p3]
  have hUS := U_le_of_root_le RG hrootS
  refine ⟨S, hSn, hSsolv, hSperf, ?_, ?_⟩
  · refine isSimpleGroup_of_dichotomy S ?_ ?_
    · intro hbot
      have hne := RG.ne_bot 1 (isRoot_pos le_rfl (by norm_num))
      apply hne
      rw [eq_bot_iff]
      exact (hrootS 1 (isRoot_pos le_rfl (by norm_num))).trans (by rw [hbot])
    · intro A hAS hAn
      exact rgd2_simple_normal RG hgen' hCG S hSperf hrootS A hAS hAn
  · intro u hu
    exact ⟨hu.2, hUS hu⟩

end CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4A2
