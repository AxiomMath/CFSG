module

public import CFSG.LargeExtraspecial.S4OmegaQ
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalMcLConfig

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Module Subgroup QuadraticMap CFSG.LargeExtraspecial.OrthoF2

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {β : LinearMap.BilinForm (ZMod 2) V}

theorem card_le_of_fix (hnd : β.Nondegenerate) {a : V} (ha : a ≠ 0)
    {E : Subgroup (V ≃ₗ[ZMod 2] V)} (hEU : E ≤ spPointRadical β a) {B : Set V}
    (hBa : ∀ q ∈ B, β a q = 0) (hfix : ∀ e ∈ E, ∀ q ∈ B, e q = q) :
    Nat.card E ≤ 2 ^ (finrank (ZMod 2) V - finrank (ZMod 2)
      (Submodule.span (ZMod 2) (insert a B))) := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  obtain ⟨b₀, hb₀⟩ : ∃ b, β a b ≠ 0 := by
    by_contra! h
    exact ha (hnd.1 a h)
  have hb₁ : β a b₀ = 1 := zmod2_eq_one_of_ne_zero hb₀
  set P := Submodule.span (ZMod 2) (insert a B) with hP
  set W := LinearMap.BilinForm.orthogonal β P with hW
  let φ : E → W := fun e => ⟨(e : V ≃ₗ[ZMod 2] V) b₀ - b₀, by
    rw [hW, LinearMap.BilinForm.mem_orthogonal_iff]
    intro p hp
    change β p _ = 0
    induction hp using Submodule.span_induction with
    | mem p hp =>
      rcases hp with rfl | hq
      · exact (hEU e.2).2.2.2 b₀
      · have h1 := spPointRadical_apply_of_orthogonal hb₁ (hEU e.2) (hBa p hq)
        rw [hfix e e.2 p hq] at h1
        have h2 : β p ((e : V ≃ₗ[ZMod 2] V) b₀ - b₀) • a = 0 := by
          have := congrArg (· - p) h1
          simpa using this.symm
        rcases smul_eq_zero.mp h2 with h | h
        · exact h
        · exact absurd h ha
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
    | smul c x _ hx => rw [map_smul, LinearMap.smul_apply, hx, smul_zero]⟩
  have hinj : Function.Injective φ := by
    intro s t hst
    have h1 : (s : V ≃ₗ[ZMod 2] V) b₀ - b₀ = (t : V ≃ₗ[ZMod 2] V) b₀ - b₀ :=
      congrArg Subtype.val hst
    exact Subtype.ext (spPointRadical_ext hb₁ (hEU s.2) (hEU t.2) (sub_left_inj.mp h1))
  calc Nat.card E ≤ Nat.card W := Nat.card_le_card_of_injective φ hinj
    _ = 2 ^ finrank (ZMod 2) W := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    _ = 2 ^ (finrank (ZMod 2) V - finrank (ZMod 2) P) := by
        rw [hW, LinearMap.BilinForm.finrank_orthogonal hnd]

theorem finrank_sup_span_of_not_mem {P : Submodule (ZMod 2) V} {c : V} (hc : c ∉ P) :
    finrank (ZMod 2) (P ⊔ Submodule.span (ZMod 2) {c} : Submodule (ZMod 2) V) =
      finrank (ZMod 2) P + 1 := by
  have hc0 : c ≠ 0 := fun h => hc (h ▸ P.zero_mem)
  have hinf : P ⊓ Submodule.span (ZMod 2) {c} = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hvP, hvc⟩
    rcases mem_span_singleton_iff.mp hvc with h | h
    · exact h ▸ Submodule.zero_mem _
    · exact absurd (h ▸ hvP) hc
  have h := Submodule.finrank_sup_add_finrank_inf_eq P (Submodule.span (ZMod 2) {c})
  rw [hinf, finrank_bot, add_zero, finrank_span_singleton hc0] at h
  exact h

theorem false_of_split (hβ : β.IsAlt) (hnd : β.Nondegenerate) {X : Subgroup (V ≃ₗ[ZMod 2] V)}
    {a : V} (ha : a ≠ 0) (hspan : Submodule.span (ZMod 2) (orbitOf X a) = ⊤)
    {E : Subgroup (V ≃ₗ[ZMod 2] V)} (hEX : E ≤ X) (hEU : E ≤ spPointRadical β a)
    (hcard : Nat.card (spPointRadical β a) ≤ 2 * Nat.card E) {A B : Set V}
    (hA : A ⊆ orbitOf X a) (hB : B ⊆ orbitOf X a)
    (hcover : ∀ t ∈ orbitOf X a, t ∈ A ∨ t ∈ B)
    (horth : ∀ p ∈ A, ∀ q ∈ B, β p q = 0) (haA : a ∈ A) (hBne : B.Nonempty) : False := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have hT0 : ∀ t ∈ orbitOf X a, t ≠ 0 := by
    rintro t ⟨x, -, rfl⟩ h
    exact ha (x.map_eq_zero_iff.mp h)
  have hpair : ∀ v : V, v ≠ 0 → ∃ y ∈ orbitOf X a, β v y = 1 := by
    intro v hv
    by_contra h
    push Not at h
    apply hv
    refine hnd.1 v fun y => ?_
    have hy : y ∈ Submodule.span (ZMod 2) (orbitOf X a) := by rw [hspan]; trivial
    induction hy using Submodule.span_induction with
    | mem y hy => exact (zmod2_eq_zero_or_eq_one _).resolve_right (h y hy)
    | zero => simp
    | add u w _ _ hu hw => rw [map_add, hu, hw, add_zero]
    | smul c u _ hu => rw [map_smul, hu, smul_zero]
  obtain ⟨y, hyT, hay⟩ := hpair a ha
  have hyA : y ∈ A := by
    rcases hcover y hyT with h | h
    · exact h
    · exact absurd (horth a haA y h) (by rw [hay]; decide)
  obtain ⟨q, hqB⟩ := hBne
  obtain ⟨q', hq'T, hqq'⟩ := hpair q (hT0 q (hB hqB))
  have hq'B : q' ∈ B := by
    rcases hcover q' hq'T with h | h
    · exact absurd ((isAlt_symm hβ q q').trans (horth q' h q hqB)) (by rw [hqq']; decide)
    · exact h
  have hfix : ∀ e ∈ E, ∀ w ∈ B, e w = w := by
    intro e he w hwB
    have hwa : β a w = 0 := horth a haA w hwB
    rcases mem_span_singleton_iff.mp ((hEU he).2.2.1 w hwa) with h | h
    · exact sub_eq_zero.mp h
    · exfalso
      obtain ⟨r, hrT, hwr⟩ := hpair w (hT0 w (hB hwB))
      have hrB : r ∈ B := by
        rcases hcover r hrT with h' | h'
        · exact absurd ((isAlt_symm hβ w r).trans (horth r h' w hwB)) (by rw [hwr]; decide)
        · exact h'
      have heq : e w = w + a := by rw [← h]; abel
      have hmem : w + a ∈ orbitOf X a := by
        rw [← heq]
        exact apply_mem_orbitOf (hEX he) (hB hwB)
      rcases hcover _ hmem with h1 | h1
      · have := horth _ h1 r hrB
        rw [map_add, LinearMap.add_apply, hwr, horth a haA r hrB, add_zero] at this
        exact one_ne_zero this
      · have := horth y hyA _ h1
        rw [map_add, horth y hyA w hwB, zero_add, isAlt_symm hβ, hay] at this
        exact one_ne_zero this
  have hBa : ∀ q ∈ B, β a q = 0 := fun q hq => horth a haA q hq
  have h1 := card_le_of_fix hnd ha hEU hBa hfix
  have hdim : 3 ≤ finrank (ZMod 2) (Submodule.span (ZMod 2) (insert a B)) := by
    set P1 := Submodule.span (ZMod 2) ({q} : Set V) with hP1
    have hq0 := hT0 q (hB hqB)
    have hq'P1 : q' ∉ P1 := by
      intro hmem
      rcases mem_span_singleton_iff.mp hmem with h | h
      · rw [h, map_zero] at hqq'
        exact zero_ne_one hqq'
      · rw [h, hβ.self_eq_zero] at hqq'
        exact zero_ne_one hqq'
    set P2 := P1 ⊔ Submodule.span (ZMod 2) {q'} with hP2
    have haP2 : a ∉ P2 := by
      intro hmem
      obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp hmem
      obtain ⟨k, rfl⟩ := Submodule.mem_span_singleton.mp hu
      obtain ⟨k', rfl⟩ := Submodule.mem_span_singleton.mp hw
      have e1 : β a q = 0 := hBa q hqB
      have e2 : β a q' = 0 := hBa q' hq'B
      rw [← huw] at e1 e2
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        hβ.self_eq_zero, mul_zero, zero_add, add_zero] at e1 e2
      rw [isAlt_symm hβ q' q, hqq', mul_one] at e1
      rw [hqq', mul_one] at e2
      rw [e1, e2, zero_smul, zero_smul, add_zero] at huw
      exact ha huw.symm
    have h2 : finrank (ZMod 2) P2 = 2 := by
      rw [hP2, finrank_sup_span_of_not_mem hq'P1, hP1, finrank_span_singleton hq0]
    have h3 : finrank (ZMod 2) (P2 ⊔ Submodule.span (ZMod 2) {a} : Submodule (ZMod 2) V) = 3 := by
      rw [finrank_sup_span_of_not_mem haP2, h2]
    have hle : P2 ⊔ Submodule.span (ZMod 2) {a} ≤ Submodule.span (ZMod 2) (insert a B) := by
      refine sup_le (sup_le ?_ ?_) ?_ <;> rw [Submodule.span_le] <;> intro v hv <;>
        rw [Set.mem_singleton_iff] at hv <;> subst hv <;> apply Submodule.subset_span
      · exact Set.mem_insert_of_mem _ hqB
      · exact Set.mem_insert_of_mem _ hq'B
      · exact Set.mem_insert _ _
    have := Submodule.finrank_mono hle
    omega
  have h2 := card_spPointRadical hβ hnd ha
  rw [h2] at hcard
  have h3 := Submodule.finrank_le (Submodule.span (ZMod 2) (insert a B))
  have h4 : 2 ^ (finrank (ZMod 2) V - 1) ≤ 2 * 2 ^ (finrank (ZMod 2) V -
      finrank (ZMod 2) (Submodule.span (ZMod 2) (insert a B))) := hcard.trans
    (Nat.mul_le_mul_left 2 h1)
  rw [← pow_succ'] at h4
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h4
  omega

theorem eq_of_closed_orbit (hβ : β.IsAlt) (hnd : β.Nondegenerate)
    {X : Subgroup (V ≃ₗ[ZMod 2] V)} {a : V} (ha : a ≠ 0)
    (hspan : Submodule.span (ZMod 2) (orbitOf X a) = ⊤) {E : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hEX : E ≤ X) (hEU : E ≤ spPointRadical β a)
    (hcard : Nat.card (spPointRadical β a) ≤ 2 * Nat.card E) (ℓ : Set V)
    (hℓT : ℓ ⊆ orbitOf X a) (hne : ℓ.Nonempty)
    (hcl : ∀ d ∈ orbitOf X a, ∀ p ∈ ℓ, p + β p d • d ∈ ℓ) : ℓ = orbitOf X a := by
  classical
  by_contra hneq
  set N := orbitOf X a \ ℓ with hN
  have hNne : N.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at h
    exact hneq (le_antisymm hℓT h)
  have horth : ∀ p ∈ ℓ, ∀ q ∈ N, β p q = 0 := by
    intro p hp q hq
    by_contra h
    have h1 : β p q = 1 := zmod2_eq_one_of_ne_zero h
    have hpq : p + q ∈ ℓ := by
      have := hcl q hq.1 p hp
      rwa [h1, one_smul] at this
    have := hcl (p + q) (hℓT hpq) p hp
    rw [map_add, hβ.self_eq_zero, zero_add, h1, one_smul, ← add_assoc, vec_add_self,
      zero_add] at this
    exact hq.2 this
  have hcover : ∀ t ∈ orbitOf X a, t ∈ ℓ ∨ t ∈ N := by
    intro t ht
    by_cases h : t ∈ ℓ
    · exact Or.inl h
    · exact Or.inr ⟨ht, h⟩
  by_cases haℓ : a ∈ ℓ
  · exact false_of_split hβ hnd ha hspan hEX hEU hcard hℓT (fun t ht => ht.1) hcover horth haℓ
      hNne
  · refine false_of_split hβ hnd ha hspan hEX hEU hcard (fun t ht => ht.1) hℓT
      (fun t ht => (hcover t ht).symm) (fun p hp q hq => ?_) ⟨⟨1, one_mem _, rfl⟩, haℓ⟩ hne
    rw [isAlt_symm hβ]
    exact horth q hq p hp

theorem spTransvection_not_mem_of_not_transitive (hβ : β.IsAlt) (hnd : β.Nondegenerate)
    (h4 : 4 ≤ finrank (ZMod 2) V) {X : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hX : X ≤ TauCeti.BilinForm.isometryGroup β) {a : V} (ha : a ≠ 0)
    (hspan : Submodule.span (ZMod 2) (orbitOf X a) = ⊤) {E : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hEX : E ≤ X) (hEU : E ≤ spPointRadical β a)
    (hcard : Nat.card (spPointRadical β a) ≤ 2 * Nat.card E)
    (hntr : ∃ v : V, v ≠ 0 ∧ v ∉ orbitOf X a) : spTransvection β hβ a ∉ E := by
  intro hτ
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have hτX : ∀ b ∈ orbitOf X a, spTransvection β hβ b ∈ X := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← conj_spTransvection hβ a (hX hx)]
    exact mul_mem (mul_mem hx (hEX hτ)) (inv_mem hx)
  have hT0 : (0 : V) ∉ orbitOf X a := by
    rintro ⟨x, -, hx⟩
    exact ha (x.map_eq_zero_iff.mp hx)
  let P : CFSG.ComponentClassification.OutcomeLocal.PreConfig V :=
    { b := β
      D := orbitOf X a
      self_eq_zero := hβ.self_eq_zero
      comm := isAlt_symm hβ
      nondeg := fun u hu => hnd.1 u hu
      zero_notMem := hT0
      span_eq := hspan
      add_mem := fun u hu v hv huv => by
        have := apply_mem_orbitOf (hτX v hv) hu
        rwa [spTransvection_apply, huv, one_smul] at this
      eq_of_closed := fun ℓ hℓ hne hcl =>
        eq_of_closed_orbit hβ hnd ha hspan hEX hEU hcard ℓ hℓ hne hcl }
  set C := P.toSympConfig with hC
  have hno : ∀ x ∈ orbitOf X a, ∀ y ∈ orbitOf X a, x ≠ y → β x y = 0 →
      x + y ∉ orbitOf X a := by
    intro x hx y hy hxy hb hxyT
    have hall := C.all_of_exists (x := x) (y := y) hx hy hxy hb hxyT
    obtain ⟨v, hv0, hvT⟩ := hntr
    exact hvT ((C.mem_iff_ne_zero_of_all hall v).mpr hv0)
  have hfixT : ∀ e ∈ E, ∀ c ∈ orbitOf X a, β c a = 0 → e c = c := by
    intro e he c hc hca
    have hac : β a c = 0 := by rw [isAlt_symm hβ, hca]
    rcases mem_span_singleton_iff.mp ((hEU he).2.2.1 c hac) with h | h
    · exact sub_eq_zero.mp h
    · exfalso
      have heq : e c = c + a := by rw [← h]; abel
      by_cases hca' : c = a
      · rw [hca', (hEU he).2.1] at heq
        apply ha
        have := congrArg (· + a) heq
        simpa [add_assoc, vec_add_self] using this.symm
      · apply hno c hc a ⟨1, one_mem _, rfl⟩ hca' hca
        rw [← heq]
        exact apply_mem_orbitOf (hEX he) hc
  have hfix : ∀ e ∈ E, ∀ x ∈ {x : V | β a x = 0}, e x = x := by
    intro e he x hx
    have hx' : β x a = 0 := by rw [isAlt_symm hβ]; exact hx
    have key : ∀ y ∈ Submodule.span (ZMod 2) {p | p ∈ C.D ∧ C.b p a = 0}, e y = y := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem p hp => exact hfixT e he p hp.1 hp.2
      | zero => exact map_zero _
      | add u w _ _ hu hw => rw [map_add, hu, hw]
      | smul c u _ hu => rw [map_smul, hu]
    exact key x (C.mem_span_perp ha (t := x) hx')
  have h1 := card_le_of_fix hnd ha hEU (B := {x : V | β a x = 0}) (fun q hq => hq) hfix
  have hspan' : Submodule.span (ZMod 2) (insert a {x : V | β a x = 0}) =
      LinearMap.ker (β a) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro v hv
      rcases hv with rfl | hv
      · exact LinearMap.mem_ker.mpr (hβ.self_eq_zero v)
      · exact LinearMap.mem_ker.mpr hv
    · intro v hv
      exact Submodule.subset_span (Set.mem_insert_of_mem _ (LinearMap.mem_ker.mp hv))
  have hker : finrank (ZMod 2) (LinearMap.ker (β a)) + 1 = finrank (ZMod 2) V := by
    have h2 := LinearMap.finrank_range_add_finrank_ker (β a)
    have hr : LinearMap.range (β a) = ⊤ := by
      obtain ⟨b, hb⟩ : ∃ b, β a b ≠ 0 := by
        by_contra! h
        exact ha (hnd.1 a h)
      have hb1 := zmod2_eq_one_of_ne_zero hb
      rw [LinearMap.range_eq_top]
      intro c
      exact ⟨c • b, by rw [map_smul, hb1, smul_eq_mul, mul_one]⟩
    rw [hr, finrank_top, finrank_self] at h2
    omega
  rw [hspan'] at h1
  have h3 := card_spPointRadical hβ hnd ha
  rw [h3] at hcard
  have h5 : 2 ^ (finrank (ZMod 2) V - 1) ≤ 2 * 2 ^ (finrank (ZMod 2) V -
      finrank (ZMod 2) (LinearMap.ker (β a))) := hcard.trans (Nat.mul_le_mul_left 2 h1)
  rw [← pow_succ'] at h5
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h5
  omega

end CFSG.LargeExtraspecial.S4
