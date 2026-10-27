module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5.RowsBasic
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.Ident
public import Certificates.Data.S7SocQ8

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Ident.SocQ8

open CFSG.ClassicalInvolution.Generic Certificates.S5Rows Certificates.S7SocQ8

section Checks

variable {M : Type*} [Group M] [DecidableEq M]

theorem refCheck_sound {L : List M} {refs : List (List M)} (h : refCheck L refs = true)
    {i j : M} (hi : i ∈ L) (hj : j ∈ L) (hij : S5.Q8Rel i j) :
    ∃ R ∈ refs, ∀ x ∈ q8Span i j, x ∈ R := by
  have h1 : (!q8RelB i j || inRefB refs i j) = true :=
    List.all_eq_true.1 (List.all_eq_true.1 h i hi) j hj
  rw [S5.q8RelB_eq_true_iff.2 hij, Bool.not_true, Bool.false_or] at h1
  obtain ⟨R, hR, hR'⟩ := List.any_eq_true.1 h1
  exact ⟨R, hR, fun x hx => of_decide_eq_true (List.all_eq_true.1 hR' x hx)⟩

theorem sigmaCheck_sound {σ : M} {refs : List (List M)} (h : sigmaCheck σ refs = true)
    {R : List M} (hR : R ∈ refs) : ∃ R' ∈ refs, ∀ r ∈ R, σ * r * σ⁻¹ ∈ R' := by
  obtain ⟨R', hR', h1⟩ := List.any_eq_true.1 (List.all_eq_true.1 h R hR)
  exact ⟨R', hR', fun r hr => of_decide_eq_true (List.all_eq_true.1 h1 r hr)⟩

end Checks

section Model

variable {M : Type*} [Group M] [DecidableEq M]

theorem card_eq_eight {G : Type*} [Group G] {T : Subgroup G}
    (h : Nonempty (↥T ≃* QuaternionGroup 2)) : Nat.card T = 8 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem exists_conj_ref {A P S : Subgroup M} [Finite A] (hP2 : (P.subgroupOf A).index = 2)
    (hS2 : IsPGroup 2 (S.subgroupOf A))
    (hSi : ¬ 2 ∣ (S.subgroupOf A).index) {σ : M} (hσA : σ ∈ A) (hσP : σ ∉ P)
    {L : List M} (hL : ∀ x ∈ S, x ∈ L) {refs : List (List M)} (h1 : refCheck L refs = true)
    (h2 : sigmaCheck σ refs = true) {T : Subgroup M} (hTA : T ≤ A)
    (e : ↥T ≃* QuaternionGroup 2) : ∃ c ∈ P, ∃ R ∈ refs, ∀ t ∈ T, c⁻¹ * t * c ∈ R := by
  have hT8 : Nat.card (T.subgroupOf A) = 2 ^ 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTA).toEquiv, card_eq_eight ⟨e⟩]
    norm_num
  obtain ⟨g, hg⟩ := S5.exists_conj_mem_of_isPGroup hS2 hSi (IsPGroup.of_card hT8)
  obtain ⟨i, hi, j, hj, hij, hspan⟩ := S5.exists_q8Pair e
  set a : M := (g : M) with ha
  have haA : a ∈ A := g.2
  have hconjS : ∀ t ∈ T, a⁻¹ * t * a ∈ S := by
    intro t ht
    have h3 := hg ⟨t, hTA ht⟩ (Subgroup.mem_subgroupOf.2 ht)
    rw [Subgroup.mem_subgroupOf] at h3
    simpa [ha] using h3
  set f : M →* M := (MulAut.conj a⁻¹).toMonoidHom with hf
  have hfx : ∀ x, f x = a⁻¹ * x * a := fun x => by simp [hf, MulAut.conj_apply]
  have hfinj : Function.Injective f := (MulAut.conj a⁻¹).injective
  have hij' : S5.Q8Rel (f i) (f j) :=
    hij.map f fun h0 => hij.2.1 (hfinj (by rw [h0, map_one]))
  obtain ⟨R, hR, hRs⟩ := refCheck_sound h1 (hL _ (by rw [hfx]; exact hconjS i hi))
    (hL _ (by rw [hfx]; exact hconjS j hj)) hij'
  have hTR : ∀ t ∈ T, a⁻¹ * t * a ∈ R := fun t ht => by
    rw [← hfx]
    exact hRs _ (S5.mem_q8Span_map f (hspan t ht))
  by_cases haP : a ∈ P
  · exact ⟨a, haP, R, hR, hTR⟩
  · obtain ⟨R', hR', hσR⟩ := sigmaCheck_sound h2 hR
    have hcP : a * σ⁻¹ ∈ P := by
      have key := Subgroup.mul_mem_iff_of_index_two hP2 (a := ⟨a, haA⟩)
        (b := ⟨σ⁻¹, A.inv_mem hσA⟩)
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] at key
      refine key.2 (iff_of_false haP fun h0 => hσP ?_)
      simpa using P.inv_mem h0
    refine ⟨a * σ⁻¹, hcP, R', hR', fun t ht => ?_⟩
    rw [show (a * σ⁻¹)⁻¹ * t * (a * σ⁻¹) = σ * (a⁻¹ * t * a) * σ⁻¹ by group]
    exact hσR _ (hTR t ht)

theorem exists_conj_ref_of_embed {G : Type*} [Group G] {N : Subgroup G} {A P : Subgroup M}
    {refs : List (List M)} (θ : G →* M) (hθ : Function.Injective θ) (hθA : ∀ x, θ x ∈ A)
    (hθP : ∀ p ∈ P, ∃ l ∈ N, θ l = p)
    (hconj : ∀ T : Subgroup M, T ≤ A → (↥T ≃* QuaternionGroup 2) →
      ∃ c ∈ P, ∃ R ∈ refs, ∀ t ∈ T, c⁻¹ * t * c ∈ R)
    {T : Subgroup G} (hT : Nonempty (↥T ≃* QuaternionGroup 2)) :
    ∃ l ∈ N, ∃ R ∈ refs, ∀ t ∈ T, θ (l⁻¹ * t * l) ∈ R := by
  obtain ⟨e⟩ := hT
  have hle : T.map θ ≤ A := by
    rintro _ ⟨t, -, rfl⟩
    exact hθA t
  obtain ⟨c, hc, R, hR, hcR⟩ :=
    hconj (T.map θ) hle ((T.equivMapOfInjective θ hθ).symm.trans e)
  obtain ⟨l, hl, rfl⟩ := hθP c hc
  refine ⟨l, hl, R, hR, fun t ht => ?_⟩
  rw [map_mul, map_mul, map_inv]
  exact hcR _ (Subgroup.mem_map_of_mem θ ht)

theorem coe_eq_of_le_list {U : Subgroup M} {R : List M} (hR : R.length ≤ 8)
    (hU : Nat.card U = 8) (h : ∀ u ∈ U, u ∈ R) : (U : Set M) = {x | x ∈ R} := by
  have hsub : (U : Set M) ⊆ (R.toFinset : Set M) := fun u hu => List.mem_toFinset.2 (h u hu)
  have key := Set.eq_of_subset_of_ncard_le hsub (by
    rw [Set.ncard_coe_finset]
    have h1 : (U : Set M).ncard = 8 := by
      rw [← Nat.card_coe_set_eq]
      exact hU
    rw [h1]
    exact (List.toFinset_card_le R).trans hR) (Finset.finite_toSet _)
  rw [key]
  ext x
  simp

theorem coe_map_conjSub_eq {G : Type*} [Group G] (θ : G →* M) (hθ : Function.Injective θ)
    {R : List M} (hR : R.length ≤ 8) {T : Subgroup G} (hT : Nat.card T = 8) {l : G}
    (hl : ∀ t ∈ T, θ (l⁻¹ * t * l) ∈ R) :
    (((conjSub l⁻¹ T).map θ : Subgroup M) : Set M) = {x | x ∈ R} := by
  refine coe_eq_of_le_list hR ?_ ?_
  · rw [Subgroup.card_map_of_injective hθ, conjSub,
      Subgroup.card_map_of_injective (MulAut.conj l⁻¹).injective, hT]
  · rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, mem_conjSub_iff, inv_inv] at hx
    have h1 := hl _ hx
    rwa [show l⁻¹ * (l * x * l⁻¹) * l = x by group] at h1

theorem exists_mem_of_ref {G : Type*} [Group G] (θ : G →* M) (hθ : Function.Injective θ)
    {R : List M} (hR : R.length ≤ 8) {T : Subgroup G} (hT : Nat.card T = 8) {l : G}
    (hl : ∀ t ∈ T, θ (l⁻¹ * t * l) ∈ R) {r : M} (hr : r ∈ R) :
    ∃ t ∈ T, θ (l⁻¹ * t * l) = r := by
  have h1 : r ∈ (((conjSub l⁻¹ T).map θ : Subgroup M) : Set M) := by
    rw [coe_map_conjSub_eq θ hθ hR hT hl]
    exact hr
  obtain ⟨x, hx, rfl⟩ := h1
  rw [SetLike.mem_coe, mem_conjSub_iff, inv_inv] at hx
  exact ⟨_, hx, by rw [show l⁻¹ * (l * x * l⁻¹) * l = x by group]⟩

theorem conjSub_eq_of_ref {G : Type*} [Group G] (θ : G →* M) (hθ : Function.Injective θ)
    {R : List M} (hR : R.length ≤ 8) {T₁ T₂ : Subgroup G} (h₁ : Nat.card T₁ = 8)
    (h₂ : Nat.card T₂ = 8) {l₁ l₂ : G} (hl₁ : ∀ t ∈ T₁, θ (l₁⁻¹ * t * l₁) ∈ R)
    (hl₂ : ∀ t ∈ T₂, θ (l₂⁻¹ * t * l₂) ∈ R) : conjSub (l₂ * l₁⁻¹) T₁ = T₂ := by
  have heq : conjSub l₁⁻¹ T₁ = conjSub l₂⁻¹ T₂ :=
    Subgroup.map_injective hθ (SetLike.coe_injective
      ((coe_map_conjSub_eq θ hθ hR h₁ hl₁).trans (coe_map_conjSub_eq θ hθ hR h₂ hl₂).symm))
  rw [conjSub_mul, heq, conjSub_conjSub_inv]

theorem mem_lOrbit_of_ref {G : Type} [Group G] (N : Subgroup G) (θ : G →* M)
    (hθ : Function.Injective θ) {R : List M} (hR : R.length ≤ 8) {T₁ T₂ : Subgroup G}
    (h₁ : Nat.card T₁ = 8) (h₂ : Nat.card T₂ = 8) {l₁ l₂ : G} (hl₁N : l₁ ∈ N) (hl₂N : l₂ ∈ N)
    (hl₁ : ∀ t ∈ T₁, θ (l₁⁻¹ * t * l₁) ∈ R) (hl₂ : ∀ t ∈ T₂, θ (l₂⁻¹ * t * l₂) ∈ R) :
    T₂ ∈ lOrbit N T₁ :=
  ⟨l₂ * l₁⁻¹, N.mul_mem hl₂N (N.inv_mem hl₁N), conjSub_eq_of_ref θ hθ hR h₁ h₂ hl₁ hl₂⟩

theorem eq_or_eq_of_pair {α : Type*} {a b x y z : α} (hx : x = a ∨ x = b) (hy : y = a ∨ y = b)
    (hz : z = a ∨ z = b) (hxy : x ≠ y) : z = x ∨ z = y := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;>
    simp_all

end Model

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Ident.SocQ8
