module

public import CFSG.ClassicalInvolution.RouteD.ExoticD4Local

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.LieType.Universal
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.Exotic
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

@[expose] def D4FrameRigid (p f : ℕ) [Fact p.Prime] (t : StatedLieTag) (n e : ℕ) : Prop :=
  ∀ (X : Type) [Group X] (φ : (modelUniv t n p e Fact.out).K →* X),
    φ.ker ≤ Subgroup.center _ → φ.range.Normal → ∀ (α : X ≃* X)
    (R : Fin 4 → Subgroup (modelUniv t n p e Fact.out).K),
    (∀ i, R i ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D) → Function.Injective R →
    (∀ i j, i ≠ j → Commutes (R i) (R j)) → (∀ i, ∀ a ∈ (R i).map φ, α a = a) →
    ∀ R₅ ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D,
      (∃ W, LinearBlockStandardPair (GaloisField p f) W ((R 0).map φ) (R₅.map φ)) →
      (∃ W, LinearBlockStandardPair (GaloisField p f) W ((R 2).map φ) (R₅.map φ)) →
      (R₅.map φ).map (α : X →* X) = R₅.map φ

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem range_normal_of_lieSystem {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (D : LieSystemData p f X Φ) (i : Fin D.card) : (D.hom i).range.Normal := by
  have key : ∀ g ∈ (⨆ k, (D.hom k).range : Subgroup X), ∀ n ∈ (D.hom i).range,
      g * n * g⁻¹ ∈ (D.hom i).range := by
    intro g hg
    induction hg using Subgroup.iSup_induction' with
    | hp k y hy =>
      intro n hn
      by_cases hki : k = i
      · subst hki
        exact (D.hom k).range.mul_mem ((D.hom k).range.mul_mem hy hn)
          ((D.hom k).range.inv_mem hy)
      · have := range_commute_of_ne D hki y hy n hn
        rw [this, mul_assoc, mul_inv_cancel, mul_one]
        exact hn
    | h1 => intro n hn; simpa using hn
    | hmul x y _ _ hx hy =>
      intro n hn
      have e : x * y * n * (x * y)⁻¹ = x * (y * n * y⁻¹) * x⁻¹ := by group
      rw [e]
      exact hx _ (hy n hn)
  refine ⟨fun n hn g => key g ?_ n hn⟩
  rw [D.generate]
  trivial

section Frame

variable [Finite G] {Ω : Set (Subgroup G)} {x : G}

theorem exists_fourth_member (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) (hP1 : LocalOddCentral Ω {x})
    (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)) {c : Fin D.card}
    (htag : D.tag c = .POmegaPlus) (hrank : D.rank c = 4) (hexp : D.exp c = f)
    {N₁ N₂ N₃ : Subgroup G} (h1 : N₁ ∈ compMembers Ω x D c) (h2 : N₂ ∈ compMembers Ω x D c)
    (h3 : N₃ ∈ compMembers Ω x D c) (h12 : N₁ ≠ N₂) (h13 : N₁ ≠ N₃) (h23 : N₂ ≠ N₃)
    (c12 : Commutes N₁ N₂) (c13 : Commutes N₁ N₃) (c23 : Commutes N₂ N₃) :
    ∃ N₄ ∈ compMembers Ω x D c, N₄ ≠ N₁ ∧ N₄ ≠ N₂ ∧ N₄ ≠ N₃ ∧ Commutes N₁ N₄ ∧
      Commutes N₂ N₄ ∧ Commutes N₃ N₄ := by
  have hperf := fundPerfect_modelUniv hp2 (D.isFundTag c) (D.admissible c)
    (by rw [hexp]; omega)
  have hsc := fundamentalSingleClass_of_ne D c (by rw [htag]; decide) (by rw [htag]; decide)
  have hclique := cliqueFour_fund_of_eq (p := p) (f := f) hp2 hq (t := D.tag c)
    (n := D.rank c) (e := D.exp c) htag hrank hexp (D.admissible c)
  obtain ⟨R₁, hR₁⟩ := exists_corr_left hΩ hex D h1
  obtain ⟨R₂, hR₂⟩ := exists_corr_left hΩ hex D h2
  obtain ⟨R₃, hR₃⟩ := exists_corr_left hΩ hex D h3
  have hne : ∀ {A B : Subgroup G} {RA RB}, Corr Ω x D c A RA → Corr Ω x D c B RB → A ≠ B →
      RA ≠ RB := fun hA hB hAB hR => hAB (corr_unique_right hΩ hP1 hA (hR ▸ hB))
  obtain ⟨F₄, d1, d2, d3, k1, k2, k3, -⟩ := hclique ⟨R₁, hR₁.2.1⟩ ⟨R₂, hR₂.2.1⟩ ⟨R₃, hR₃.2.1⟩
    (fun h => hne hR₁ hR₂ h12 (congrArg Subtype.val h))
    (fun h => hne hR₁ hR₃ h13 (congrArg Subtype.val h))
    (fun h => hne hR₂ hR₃ h23 (congrArg Subtype.val h))
    ((corr_commutes hΩ hP1 hperf hR₁ hR₂).mp c12) ((corr_commutes hΩ hP1 hperf hR₁ hR₃).mp c13)
    ((corr_commutes hΩ hP1 hperf hR₂ hR₃).mp c23)
  obtain ⟨N₄, hN₄⟩ := exists_corr_right hΩ D hsc F₄.2
  refine ⟨N₄, ⟨hN₄.1, hN₄.2.2 ▸ Subgroup.map_le_range _ _⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    subst h
    exact d1 (Subtype.ext (corr_unique_left hperf hN₄ hR₁))
  · intro h
    subst h
    exact d2 (Subtype.ext (corr_unique_left hperf hN₄ hR₂))
  · intro h
    subst h
    exact d3 (Subtype.ext (corr_unique_left hperf hN₄ hR₃))
  · exact (corr_commutes hΩ hP1 hperf hR₁ hN₄).mpr k1
  · exact (corr_commutes hΩ hP1 hperf hR₂ hN₄).mpr k2
  · exact (corr_commutes hΩ hP1 hperf hR₃ hN₄).mpr k3


theorem conjSub_eq_of_frame (hb : D4FrameRigid p f .POmegaPlus 4 f) (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) (hP1 : LocalOddCentral Ω {x}) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)) {c : Fin D.card}
    (htag : D.tag c = .POmegaPlus) (hrank : D.rank c = 4) (hexp : D.exp c = f) {t : G}
    (htx : t * x * t⁻¹ = x) {N : Fin 4 → Subgroup G} (hN : ∀ i, N i ∈ compMembers Ω x D c)
    (hinj : Function.Injective N) (hcomm : ∀ i j, i ≠ j → Commutes (N i) (N j))
    (hfix : ∀ i, N i ≤ Subgroup.centralizer ({t} : Set G)) {N₅ : Subgroup G}
    (h5 : N₅ ∈ compMembers Ω x D c)
    (hs₀ : ∃ W, LinearBlockStandardPair (GaloisField p f) W (N 0) N₅)
    (hs₂ : ∃ W, LinearBlockStandardPair (GaloisField p f) W (N 2) N₅) :
    conjSub t N₅ = N₅ := by
  have hperf := fundPerfect_modelUniv hp2 (D.isFundTag c) (D.admissible c)
    (by rw [hexp]; omega)
  have hbD : D4FrameRigid p f (D.tag c) (D.rank c) (D.exp c) := by
    rw [htag, hrank, hexp]
    exact hb
  choose R hR using fun i => exists_corr_left hΩ hex D (hN i)
  obtain ⟨R₅, hR₅⟩ := exists_corr_left hΩ hex D h5
  have hstd : ∀ (i : Fin 4) (W : Subgroup G),
      LinearBlockStandardPair (GaloisField p f) W (N i) N₅ →
      ∃ W', LinearBlockStandardPair (GaloisField p f) W' ((R i).map (D.hom c))
        (R₅.map (D.hom c)) := by
    intro i W hW
    obtain ⟨W', hW'⟩ := linearBlockStandardPair_locImg_of_members hP1 (hN i).1 h5.1 hW
    rw [(hR i).2.2, hR₅.2.2] at hW'
    exact ⟨W', hW'⟩
  have key := hbD (locQuot Ω x) (D.hom c) (D.ker_le_center c) (range_normal_of_lieSystem D c)
    (Gaps.locAut hΩ.conjInvariant htx) R (fun i => (hR i).2.1)
    (fun i j h => hinj (corr_unique_right hΩ hP1 (hR i) (h ▸ hR j)))
    (fun i j hij => (corr_commutes hΩ hP1 hperf (hR i) (hR j)).mp (hcomm i j hij))
    (fun i a ha => (locAut_fixed_iff hΩ hP1 htx (hR i).1).mp (hfix i) a (by
      rw [(hR i).2.2]; exact ha))
    R₅ hR₅.2.1 (hstd 0 _ hs₀.choose_spec) (hstd 2 _ hs₂.choose_spec)
  have himg : locImg Ω x (conjSub t N₅) = locImg Ω x N₅ := by
    rw [← locAut_locImg hΩ.conjInvariant htx N₅, hR₅.2.2]
    exact key
  have hmem : conjSub t N₅ ∈ centralizingMembers Ω {x} := by
    have := centralizingMembers_conj hΩ.conjInvariant t x
    rw [htx] at this
    rw [this]
    exact ⟨N₅, h5.1, rfl⟩
  exact locImg_injOn hΩ hP1 hmem h5.1 himg

end Frame

end CFSG.ClassicalInvolution.RouteD
