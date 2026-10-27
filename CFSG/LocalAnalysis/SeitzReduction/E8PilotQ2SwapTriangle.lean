module

public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2SwapUniquePair

public section

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_perfect)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.SeitzQ2 (SwapParam AgreeOn FlipOn)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section Twist

variable {G : Type*} [Group G] {t : G} {D : Subgroup G}

theorem swapParam_flip_injective (P : SwapParam t D) (hinj : Function.Injective P.Ψ) :
    Function.Injective P.flip.Ψ :=
  hinj.comp (MulEquiv.prodComm : D × D ≃* D × D).injective

theorem swapParam_flip_range (P : SwapParam t D) : P.flip.Ψ.range = P.Ψ.range := by
  ext x
  constructor
  · rintro ⟨⟨a, b⟩, rfl⟩
    exact ⟨(b, a), rfl⟩
  · rintro ⟨⟨a, b⟩, rfl⟩
    exact ⟨(b, a), rfl⟩

theorem swapParam_twist_one (P : SwapParam t D) : P.twist 1 = P := by
  rw [SeitzQ2.SwapParam.twist, ite_eq_left rfl]

theorem swapParam_twist_neg_one (P : SwapParam t D) : P.twist (-1) = P.flip := by
  rw [SeitzQ2.SwapParam.twist, ite_eq_right (by decide)]

theorem swapParam_twist_injective (P : SwapParam t D) (hinj : Function.Injective P.Ψ)
    (s : ℤˣ) : Function.Injective (P.twist s).Ψ := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · rw [swapParam_twist_one]
    exact hinj
  · rw [swapParam_twist_neg_one]
    exact swapParam_flip_injective P hinj

theorem swapParam_twist_range (P : SwapParam t D) (s : ℤˣ) : (P.twist s).Ψ.range = P.Ψ.range := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · rw [swapParam_twist_one]
  · rw [swapParam_twist_neg_one, swapParam_flip_range]

theorem swapParam_le_centralizer (P : SwapParam t D) {X : Subgroup G}
    (hrange : P.Ψ.range = centralizerPerfectCore X) : D ≤ centralizer (X : Set G) := by
  intro d hd
  have h1 : d ∈ P.Ψ.range := ⟨(⟨d, hd⟩, ⟨d, hd⟩), P.diag ⟨d, hd⟩⟩
  rw [hrange] at h1
  exact perfectCore_le _ h1

end Twist

section Coherent

variable {G : Type*} [Group G] {t : G}

theorem exists_twist_agreeOn_triangle (ht2 : t * t = 1) {D₁ D₂ D₃ : Subgroup G}
    (P₁ : SwapParam t D₁) (P₂ : SwapParam t D₂) (P₃ : SwapParam t D₃) {O₁₂ O₁₃ O₂₃ : Subgroup G}
    (h₁₂ : AgreeOn P₁ P₂ O₁₂ ∨ FlipOn P₁ P₂ O₁₂) (h₁₃ : AgreeOn P₁ P₃ O₁₃ ∨ FlipOn P₁ P₃ O₁₃)
    (h₂₃ : AgreeOn P₂ P₃ O₂₃ ∨ FlipOn P₂ P₃ O₂₃) {q : G} (hq₁₂ : q ∈ O₁₂) (hq₁₃ : q ∈ O₁₃)
    (hq₂₃ : q ∈ O₂₃) (hdet : P₁.lft q ≠ t * P₁.lft q * t⁻¹) :
    ∃ s₂ s₃ : ℤˣ, AgreeOn P₁ (P₂.twist s₂) O₁₂ ∧ AgreeOn P₁ (P₃.twist s₃) O₁₃ ∧
      AgreeOn (P₂.twist s₂) (P₃.twist s₃) O₂₃ := by
  have t₁₂ := SeitzQ2.twistOn_agreeSign h₁₂
  have t₁₃ := SeitzQ2.twistOn_agreeSign h₁₃
  have t₂₃ := SeitzQ2.twistOn_agreeSign h₂₃
  have htri := SeitzQ2.sign_mul_of_triangle ht2 t₁₂ t₂₃ t₁₃ hq₁₂ hq₂₃ hq₁₃ hdet
  refine ⟨SeitzQ2.agreeSign P₁ P₂ O₁₂, SeitzQ2.agreeSign P₁ P₃ O₁₃, fun x hx => ?_,
    fun x hx => ?_, fun x hx => ?_⟩
  · rw [SeitzQ2.SwapParam.lft_twist, t₁₂ x hx, ← SeitzQ2.signConj_mul ht2, Int.units_mul_self,
      SeitzQ2.signConj_one]
  · rw [SeitzQ2.SwapParam.lft_twist, t₁₃ x hx, ← SeitzQ2.signConj_mul ht2, Int.units_mul_self,
      SeitzQ2.signConj_one]
  · rw [SeitzQ2.SwapParam.lft_twist, SeitzQ2.SwapParam.lft_twist, t₂₃ x hx,
      ← SeitzQ2.signConj_mul ht2, htri, mul_assoc, Int.units_mul_self, mul_one]

end Coherent

section FinThree

variable {G : Type*} [Group G]

theorem iSup_fin_three_subgroup (f : Fin 3 → Subgroup G) : ⨆ k, f k = f 0 ⊔ f 1 ⊔ f 2 := by
  apply le_antisymm
  · refine iSup_le fun k => ?_
    fin_cases k
    · exact le_sup_left.trans le_sup_left
    · exact le_sup_right.trans le_sup_left
    · exact le_sup_right
  · exact sup_le (sup_le (le_iSup f 0) (le_iSup f 1)) (le_iSup f 2)

theorem sup_three_sup_three_subgroup (a b c a' b' c' : Subgroup G) :
    a ⊔ b ⊔ c ⊔ (a' ⊔ b' ⊔ c') = a ⊔ a' ⊔ (b ⊔ b') ⊔ (c ⊔ c') := by
  rw [sup_sup_sup_comm, sup_sup_sup_comm a b]

end FinThree

section Triangle

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G}

omit [Finite G] in
theorem map_conj_le_centralizer_of_eq_fst {D : Subgroup G} (Q : SwapParam t D)
    {A B Fa Fb : Subgroup G} (ha : Fa = Q.fst A) (hb : Fb = Q.fst B) :
    Fb.map (MulAut.conj t).toMonoidHom ≤ centralizer (Fa : Set G) := by
  rw [ha, hb]
  exact Q.map_conj_fst_le_centralizer A B

theorem exists_swapFactors_of_swapParam_triangle (hL : IsSimpleGroup L) (ht2 : t * t = 1)
    {X₁ X₂ X₃ D₁ D₂ D₃ : Subgroup G} (P₁ : SwapParam t D₁) (P₂ : SwapParam t D₂)
    (P₃ : SwapParam t D₃) (hinj₁ : Function.Injective P₁.Ψ) (hinj₂ : Function.Injective P₂.Ψ)
    (hinj₃ : Function.Injective P₃.Ψ) (hrange₁ : P₁.Ψ.range = centralizerPerfectCore X₁)
    (hrange₂ : P₂.Ψ.range = centralizerPerfectCore X₂)
    (hrange₃ : P₃.Ψ.range = centralizerPerfectCore X₃)
    (h₂₁ : X₂ ≤ D₁) (h₃₁ : X₃ ≤ D₁) (h₁₂ : X₁ ≤ D₂) (h₃₂ : X₃ ≤ D₂) (h₁₃ : X₁ ≤ D₃)
    (h₂₃ : X₂ ≤ D₃)
    (hS₁₂ : IsSimpleGroup (perfectCore (D₁ ⊓ centralizer (X₂ : Set G))))
    (hS₁₃ : IsSimpleGroup (perfectCore (D₁ ⊓ centralizer (X₃ : Set G))))
    (hS₂₃ : IsSimpleGroup (perfectCore (D₂ ⊓ centralizer (X₃ : Set G))))
    (hZ₁₂ : center (perfectCore (D₁ ⊓ centralizer (X₂ : Set G))) = ⊥)
    (hZ₁₃ : center (perfectCore (D₁ ⊓ centralizer (X₃ : Set G))) = ⊥)
    (hZ₂₃ : center (perfectCore (D₂ ⊓ centralizer (X₃ : Set G))) = ⊥)
    {q : G} (hq₁₂ : q ∈ perfectCore (D₁ ⊓ centralizer (X₂ : Set G)))
    (hq₁₃ : q ∈ perfectCore (D₁ ⊓ centralizer (X₃ : Set G)))
    (hq₂₃ : q ∈ perfectCore (D₂ ⊓ centralizer (X₃ : Set G))) (hq : q ≠ 1)
    (hgen : perfectCore (D₁ ⊓ centralizer (X₂ : Set G)) ⊔
      perfectCore (D₁ ⊓ centralizer (X₃ : Set G)) ⊔
        perfectCore (D₂ ⊓ centralizer (X₃ : Set G)) = L) :
    ∃ G₁ : Subgroup G, CFSG.Open.IsQuasisimple G₁ ∧
      G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G) ∧
      (∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L) ∧ (∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y) ∧
      G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom =
        centralizerPerfectCore (X₁ ⊔ X₂) ⊔ centralizerPerfectCore (X₁ ⊔ X₃) ⊔
          centralizerPerfectCore (X₂ ⊔ X₃) := by
  obtain ⟨e₂₁, d₁₂⟩ := by
    haveI := hS₁₂
    exact SeitzQ2.agreeOn_or_flipOn_of_neighbours P₁ P₂ hinj₁ hinj₂ hrange₁ hrange₂ h₂₁ h₁₂ hZ₁₂
  obtain ⟨e₃₁, d₁₃⟩ := by
    haveI := hS₁₃
    exact SeitzQ2.agreeOn_or_flipOn_of_neighbours P₁ P₃ hinj₁ hinj₃ hrange₁ hrange₃ h₃₁ h₁₃ hZ₁₃
  obtain ⟨e₃₂, d₂₃⟩ := by
    haveI := hS₂₃
    exact SeitzQ2.agreeOn_or_flipOn_of_neighbours P₂ P₃ hinj₂ hinj₃ hrange₂ hrange₃ h₃₂ h₂₃ hZ₂₃
  set O₁₂ := perfectCore (D₁ ⊓ centralizer (X₂ : Set G)) with hO₁₂
  set O₁₃ := perfectCore (D₁ ⊓ centralizer (X₃ : Set G)) with hO₁₃
  set O₂₃ := perfectCore (D₂ ⊓ centralizer (X₃ : Set G)) with hO₂₃
  have hO₁₂D₁ : O₁₂ ≤ D₁ := (perfectCore_le _).trans inf_le_left
  have hO₁₃D₁ : O₁₃ ≤ D₁ := (perfectCore_le _).trans inf_le_left
  have hO₂₃D₂ : O₂₃ ≤ D₂ := (perfectCore_le _).trans inf_le_left
  have hO₁₂D₂ : O₁₂ ≤ D₂ := by
    rw [← e₂₁]
    exact (perfectCore_le _).trans inf_le_left
  have hO₁₃D₃ : O₁₃ ≤ D₃ := by
    rw [← e₃₁]
    exact (perfectCore_le _).trans inf_le_left
  have hO₂₃D₃ : O₂₃ ≤ D₃ := by
    rw [← e₃₂]
    exact (perfectCore_le _).trans inf_le_left
  have hdet : P₁.lft q ≠ t * P₁.lft q * t⁻¹ := by
    refine P₁.lft_ne_conj_lft (hO₁₂D₁ hq₁₂) fun hc => hq ?_
    have hc' : (⟨q, hq₁₂⟩ : O₁₂) ∈ center O₁₂ := by
      rw [mem_center_iff]
      intro g
      apply Subtype.ext
      have h1 := congrArg Subtype.val (mem_center_iff.1 hc ⟨g, hO₁₂D₁ g.2⟩)
      exact h1
    rw [hZ₁₂, mem_bot] at hc'
    exact congrArg Subtype.val hc'
  obtain ⟨s₂, s₃, a₁₂, a₁₃, a₂₃⟩ :=
    exists_twist_agreeOn_triangle ht2 P₁ P₂ P₃ d₁₂ d₁₃ d₂₃ hq₁₂ hq₁₃ hq₂₃ hdet
  set Q₂ := P₂.twist s₂ with hQ₂
  set Q₃ := P₃.twist s₃ with hQ₃
  have e₁₂ : P₁.fst O₁₂ = Q₂.fst O₁₂ := (P₁.fst_eq_of_lft_eq hO₁₂D₁ hO₁₂D₂ a₁₂).symm
  have e₁₃ : P₁.fst O₁₃ = Q₃.fst O₁₃ := (P₁.fst_eq_of_lft_eq hO₁₃D₁ hO₁₃D₃ a₁₃).symm
  have e₂₃ : Q₂.fst O₂₃ = Q₃.fst O₂₃ := (Q₂.fst_eq_of_lft_eq hO₂₃D₂ hO₂₃D₃ a₂₃).symm
  set F : Fin 3 → Subgroup G := ![P₁.fst O₁₂, P₁.fst O₁₃, Q₂.fst O₂₃] with hF
  set O : Fin 3 → Subgroup G := ![O₁₂, O₁₃, O₂₃] with hO
  have hcomm : ∀ k l, (F l).map (MulAut.conj t).toMonoidHom ≤ centralizer (F k : Set G) := by
    intro k l
    fin_cases k <;> fin_cases l
    · exact map_conj_le_centralizer_of_eq_fst P₁ rfl rfl
    · exact map_conj_le_centralizer_of_eq_fst P₁ rfl rfl
    · exact map_conj_le_centralizer_of_eq_fst Q₂ e₁₂ rfl
    · exact map_conj_le_centralizer_of_eq_fst P₁ rfl rfl
    · exact map_conj_le_centralizer_of_eq_fst P₁ rfl rfl
    · exact map_conj_le_centralizer_of_eq_fst Q₃ e₁₃ e₂₃
    · exact map_conj_le_centralizer_of_eq_fst Q₂ rfl e₁₂
    · exact map_conj_le_centralizer_of_eq_fst Q₃ e₂₃ e₁₃
    · exact map_conj_le_centralizer_of_eq_fst Q₂ rfl rfl
  have hperf : ∀ k, ⁅F k, F k⁆ = F k := by
    intro k
    fin_cases k
    · exact P₁.commutator_fst hO₁₂D₁ (perfectCore_perfect _)
    · exact P₁.commutator_fst hO₁₃D₁ (perfectCore_perfect _)
    · exact Q₂.commutator_fst hO₂₃D₂ (perfectCore_perfect _)
  have hδ : ∀ k, ∀ x ∈ F k, x * (t * x * t⁻¹) ∈ O k := by
    intro k
    fin_cases k
    · exact fun x hx => P₁.mul_conj_mem_of_mem_fst hx
    · exact fun x hx => P₁.mul_conj_mem_of_mem_fst hx
    · exact fun x hx => Q₂.mul_conj_mem_of_mem_fst hx
  have hsurjP : ∀ k, ∀ y ∈ O k, ∃ x ∈ F k, x * (t * x * t⁻¹) = y := by
    intro k
    fin_cases k
    · exact fun y hy => P₁.exists_mem_fst_mul_conj_eq hO₁₂D₁ hy
    · exact fun y hy => P₁.exists_mem_fst_mul_conj_eq hO₁₃D₁ hy
    · exact fun y hy => Q₂.exists_mem_fst_mul_conj_eq hO₂₃D₂ hy
  have hgen' : ⨆ k, O k = L := by
    rw [iSup_fin_three_subgroup]
    exact hgen
  obtain ⟨hq', h₁₂', hδL, hsurjL⟩ :=
    SeitzQ2.isQuasisimple_iSup_of_diag hL F O hcomm hperf hδ hsurjP hgen'
  refine ⟨⨆ k, F k, hq', h₁₂', hδL, hsurjL, ?_⟩
  have hE₁₂ : centralizerPerfectCore (X₁ ⊔ X₂) =
      P₁.fst O₁₂ ⊔ (P₁.fst O₁₂).map (MulAut.conj t).toMonoidHom := by
    rw [P₁.centralizerPerfectCore_sup_eq hinj₁ hrange₁ h₂₁, P₁.map_prod_eq_fst_sup]
  have hE₁₃ : centralizerPerfectCore (X₁ ⊔ X₃) =
      P₁.fst O₁₃ ⊔ (P₁.fst O₁₃).map (MulAut.conj t).toMonoidHom := by
    rw [P₁.centralizerPerfectCore_sup_eq hinj₁ hrange₁ h₃₁, P₁.map_prod_eq_fst_sup]
  have hE₂₃ : centralizerPerfectCore (X₂ ⊔ X₃) =
      Q₂.fst O₂₃ ⊔ (Q₂.fst O₂₃).map (MulAut.conj t).toMonoidHom := by
    rw [Q₂.centralizerPerfectCore_sup_eq (swapParam_twist_injective P₂ hinj₂ s₂)
      ((swapParam_twist_range P₂ s₂).trans hrange₂) h₃₂, Q₂.map_prod_eq_fst_sup]
  rw [iSup_fin_three_subgroup, Subgroup.map_sup, Subgroup.map_sup, hE₁₂, hE₁₃, hE₂₃]
  exact sup_three_sup_three_subgroup _ _ _ _ _ _

theorem exists_swapFactors_unique_of_swapParam_triangle {P : Type} [Group P] [Finite P]
    (hset : SeitzSetting G L) (hOut : Group.IsSolvable (Outer L)) (e : L ≃* P)
    (hP : SeitzQ2.SwapPairExclusion P) (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {X₁ X₂ X₃ D₁ D₂ D₃ : Subgroup G} (P₁ : SwapParam t D₁) (P₂ : SwapParam t D₂)
    (P₃ : SwapParam t D₃) (hinj₁ : Function.Injective P₁.Ψ) (hinj₂ : Function.Injective P₂.Ψ)
    (hinj₃ : Function.Injective P₃.Ψ) (hrange₁ : P₁.Ψ.range = centralizerPerfectCore X₁)
    (hrange₂ : P₂.Ψ.range = centralizerPerfectCore X₂)
    (hrange₃ : P₃.Ψ.range = centralizerPerfectCore X₃)
    (hX₁L : X₁ ≤ L) (hX₂L : X₂ ≤ L) (hX₃L : X₃ ≤ L)
    (h₂₁ : X₂ ≤ D₁) (h₃₁ : X₃ ≤ D₁) (h₁₂ : X₁ ≤ D₂) (h₃₂ : X₃ ≤ D₂) (h₁₃ : X₁ ≤ D₃)
    (h₂₃ : X₂ ≤ D₃)
    (hS₁₂ : IsSimpleGroup (perfectCore (D₁ ⊓ centralizer (X₂ : Set G))))
    (hS₁₃ : IsSimpleGroup (perfectCore (D₁ ⊓ centralizer (X₃ : Set G))))
    (hS₂₃ : IsSimpleGroup (perfectCore (D₂ ⊓ centralizer (X₃ : Set G))))
    (hZ₁₂ : center (perfectCore (D₁ ⊓ centralizer (X₂ : Set G))) = ⊥)
    (hZ₁₃ : center (perfectCore (D₁ ⊓ centralizer (X₃ : Set G))) = ⊥)
    (hZ₂₃ : center (perfectCore (D₂ ⊓ centralizer (X₃ : Set G))) = ⊥)
    {q : G} (hq₁₂ : q ∈ perfectCore (D₁ ⊓ centralizer (X₂ : Set G)))
    (hq₁₃ : q ∈ perfectCore (D₁ ⊓ centralizer (X₃ : Set G)))
    (hq₂₃ : q ∈ perfectCore (D₂ ⊓ centralizer (X₃ : Set G))) (hq : q ≠ 1)
    (hgen : perfectCore (D₁ ⊓ centralizer (X₂ : Set G)) ⊔
      perfectCore (D₁ ⊓ centralizer (X₃ : Set G)) ⊔
        perfectCore (D₂ ⊓ centralizer (X₃ : Set G)) = L) :
    ∃ G₁ : Subgroup G, CFSG.Open.IsQuasisimple G₁ ∧
      G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G) ∧
      (∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L) ∧ (∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y) ∧
      G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom =
        centralizerPerfectCore (X₁ ⊔ X₂) ⊔ centralizerPerfectCore (X₁ ⊔ X₃) ⊔
          centralizerPerfectCore (X₂ ⊔ X₃) ∧
      ∀ g : G, g⁻¹ * t * g ∈
          normalizer ((G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) →
        g ∈ normalizer ((G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hL := SeitzQ2.isSimpleGroup_of_seitzSetting hset
  obtain ⟨G₁, hq', h₁₂', hδ, hsurj, hspan⟩ := exists_swapFactors_of_swapParam_triangle hL htt
    P₁ P₂ P₃ hinj₁ hinj₂ hinj₃ hrange₁ hrange₂ hrange₃ h₂₁ h₃₁ h₁₂ h₃₂ h₁₃ h₂₃ hS₁₂ hS₁₃ hS₂₃
    hZ₁₂ hZ₁₃ hZ₂₃ hq₁₂ hq₁₃ hq₂₃ hq hgen
  have hD₁ := swapParam_le_centralizer P₁ hrange₁
  have hD₂ := swapParam_le_centralizer P₂ hrange₂
  have hcen : ∀ {O A B : Subgroup G}, O ≤ centralizer (A : Set G) →
      O ≤ centralizer (B : Set G) → O ≤ centralizer ((A ⊔ B : Subgroup G) : Set G) :=
    fun hA hB => le_centralizer_iff.2 (sup_le (le_centralizer_iff.1 hA) (le_centralizer_iff.1 hB))
  refine ⟨G₁, hq', h₁₂', hδ, hsurj, hspan,
    SeitzQ2.unique_of_swapFactors_of_neighbours_of_swapPairExclusion hset hOut e hP ht hKt hq' h₁₂'
      hδ hsurj ![X₁ ⊔ X₂, X₁ ⊔ X₃, X₂ ⊔ X₃]
      ![perfectCore (D₁ ⊓ centralizer (X₂ : Set G)), perfectCore (D₁ ⊓ centralizer (X₃ : Set G)),
        perfectCore (D₂ ⊓ centralizer (X₃ : Set G))] (fun k => ?_) (fun k => ?_) (fun k => ?_) ?_
      (fun k => ?_)⟩
  · fin_cases k
    · exact sup_le hX₁L hX₂L
    · exact sup_le hX₁L hX₃L
    · exact sup_le hX₂L hX₃L
  · fin_cases k
    · exact hcen (((perfectCore_le _).trans inf_le_left).trans hD₁)
        ((perfectCore_le _).trans inf_le_right)
    · exact hcen (((perfectCore_le _).trans inf_le_left).trans hD₁)
        ((perfectCore_le _).trans inf_le_right)
    · exact hcen (((perfectCore_le _).trans inf_le_left).trans hD₂)
        ((perfectCore_le _).trans inf_le_right)
  · fin_cases k <;> exact perfectCore_perfect _
  · rw [iSup_fin_three_subgroup]
    exact hgen
  · rw [hspan]
    fin_cases k
    · exact le_sup_left.trans le_sup_left
    · exact le_sup_right.trans le_sup_left
    · exact le_sup_right

theorem false_of_swapParam_triangle {P : Type} [Group P] [Finite P] (hset : SeitzSetting G L)
    (hOut : Group.IsSolvable (Outer L)) (e : L ≃* P) (hP : SeitzQ2.SwapPairExclusion P)
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {X₁ X₂ X₃ D₁ D₂ D₃ : Subgroup G} (P₁ : SwapParam t D₁) (P₂ : SwapParam t D₂)
    (P₃ : SwapParam t D₃) (hinj₁ : Function.Injective P₁.Ψ) (hinj₂ : Function.Injective P₂.Ψ)
    (hinj₃ : Function.Injective P₃.Ψ) (hrange₁ : P₁.Ψ.range = centralizerPerfectCore X₁)
    (hrange₂ : P₂.Ψ.range = centralizerPerfectCore X₂)
    (hrange₃ : P₃.Ψ.range = centralizerPerfectCore X₃)
    (hX₁L : X₁ ≤ L) (hX₂L : X₂ ≤ L) (hX₃L : X₃ ≤ L)
    (h₂₁ : X₂ ≤ D₁) (h₃₁ : X₃ ≤ D₁) (h₁₂ : X₁ ≤ D₂) (h₃₂ : X₃ ≤ D₂) (h₁₃ : X₁ ≤ D₃)
    (h₂₃ : X₂ ≤ D₃)
    (hS₁₂ : IsSimpleGroup (perfectCore (D₁ ⊓ centralizer (X₂ : Set G))))
    (hS₁₃ : IsSimpleGroup (perfectCore (D₁ ⊓ centralizer (X₃ : Set G))))
    (hS₂₃ : IsSimpleGroup (perfectCore (D₂ ⊓ centralizer (X₃ : Set G))))
    (hZ₁₂ : center (perfectCore (D₁ ⊓ centralizer (X₂ : Set G))) = ⊥)
    (hZ₁₃ : center (perfectCore (D₁ ⊓ centralizer (X₃ : Set G))) = ⊥)
    (hZ₂₃ : center (perfectCore (D₂ ⊓ centralizer (X₃ : Set G))) = ⊥)
    {q : G} (hq₁₂ : q ∈ perfectCore (D₁ ⊓ centralizer (X₂ : Set G)))
    (hq₁₃ : q ∈ perfectCore (D₁ ⊓ centralizer (X₃ : Set G)))
    (hq₂₃ : q ∈ perfectCore (D₂ ⊓ centralizer (X₃ : Set G))) (hq : q ≠ 1)
    (hgen : perfectCore (D₁ ⊓ centralizer (X₂ : Set G)) ⊔
      perfectCore (D₁ ⊓ centralizer (X₃ : Set G)) ⊔
        perfectCore (D₂ ⊓ centralizer (X₃ : Set G)) = L) : False := by
  obtain ⟨G₁, hq', h₁₂', -, -, -, huniq⟩ := exists_swapFactors_unique_of_swapParam_triangle hset
    hOut e hP ht hKt P₁ P₂ P₃ hinj₁ hinj₂ hinj₃ hrange₁ hrange₂ hrange₃ hX₁L hX₂L hX₃L h₂₁ h₃₁
    h₁₂ h₃₂ h₁₃ h₂₃ hS₁₂ hS₁₃ hS₂₃ hZ₁₂ hZ₁₃ hZ₂₃ hq₁₂ hq₁₃ hq₂₃ hq hgen
  have : IsSimpleGroup G := hset.1
  exact F4Pilot.false_of_simple_of_swap_of_isQuasisimple ht hq' h₁₂' rfl huniq

end Triangle

end CFSG.SeitzReduction.E8Pilot
