module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Input31

public section

open scoped IsMulCommutative

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open

section Linear

variable {p : ℕ} [Fact p.Prime]

theorem gl3_ray {F : Type*} [Field F] {x0 x : F × F} (hx0 : x0 ≠ 0)
    (h : x.1 * x0.2 = x0.1 * x.2) : ∃ t : F, x.1 = t * x0.1 ∧ x.2 = t * x0.2 := by
  by_cases h1 : x0.1 = 0
  · have h2 : x0.2 ≠ 0 := by
      intro h2
      exact hx0 (Prod.ext h1 h2)
    have hx1 : x.1 = 0 := by
      have h3 : x.1 * x0.2 = 0 := by rw [h, h1, zero_mul]
      exact (mul_eq_zero.1 h3).resolve_right h2
    refine ⟨x.2 / x0.2, ?_, ?_⟩
    · rw [hx1, h1, mul_zero]
    · field_simp
  · refine ⟨x.1 / x0.1, ?_, ?_⟩
    · field_simp
    · field_simp
      linear_combination (-1 : F) * h

abbrev gl3QuotAction {A V : Type*} [Group A] [AddCommGroup V] [Module (ZMod p) V]
    (ρ : A →* Module.End (ZMod p) V) (W : Submodule (ZMod p) V)
    (hW : ∀ a : A, ∀ w ∈ W, ρ a w ∈ W) : MulAction A (V ⧸ W) where
  smul a q := W.mapQ W (ρ a) (fun w hw => hW a w hw) q
  one_smul q := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective W q
    change W.mapQ W (ρ 1) (fun w hw => hW 1 w hw) (Submodule.Quotient.mk x) = Submodule.Quotient.mk x
    simp [Submodule.mapQ_apply]
  mul_smul a b q := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective W q
    change W.mapQ W (ρ (a * b)) (fun w hw => hW (a * b) w hw) (Submodule.Quotient.mk x) =
      W.mapQ W (ρ a) (fun w hw => hW a w hw) (W.mapQ W (ρ b) (fun w hw => hW b w hw)
        (Submodule.Quotient.mk x))
    simp [Submodule.mapQ_apply, Module.End.mul_apply]

theorem gl3_exists_fixed_mod {A V : Type*} [Group A] [AddCommGroup V] [Module (ZMod p) V]
    [FiniteDimensional (ZMod p) V] (hA : IsPGroup p A) (ρ : A →* Module.End (ZMod p) V)
    (W : Submodule (ZMod p) V) (hW : ∀ a : A, ∀ w ∈ W, ρ a w ∈ W) (hWtop : W ≠ ⊤) :
    ∃ v : V, v ∉ W ∧ ∀ a : A, ρ a v - v ∈ W := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI := gl3QuotAction ρ W hW
  haveI : Finite (V ⧸ W) := Module.finite_of_finite (ZMod p)
  have hfin := Submodule.finrank_quotient_add_finrank W
  have hlt := Submodule.finrank_lt hWtop
  have hpos : 0 < Module.finrank (ZMod p) (V ⧸ W) := by omega
  have hcard : p ∣ Nat.card (V ⧸ W) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
    exact dvd_pow_self p hpos.ne'
  have h0 : (0 : V ⧸ W) ∈ MulAction.fixedPoints A (V ⧸ W) := by
    rw [MulAction.mem_fixedPoints]
    intro a
    change W.mapQ W (ρ a) (fun w hw => hW a w hw) 0 = 0
    exact map_zero _
  obtain ⟨b, hb, hne⟩ :=
    IsPGroup.exists_fixed_point_of_prime_dvd_card_of_fixed_point hA (V ⧸ W) hcard h0
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective W b
  refine ⟨v, fun hv => hne ((Submodule.Quotient.mk_eq_zero W).2 hv).symm, fun a => ?_⟩
  have hfa := MulAction.mem_fixedPoints.1 hb a
  change W.mapQ W (ρ a) (fun w hw => hW a w hw) (Submodule.Quotient.mk v) =
    Submodule.Quotient.mk v at hfa
  rw [Submodule.mapQ_apply, Submodule.Quotient.eq] at hfa
  exact hfa

theorem gl3_core {A V : Type*} [Group A] [AddCommGroup V] [Module (ZMod p) V]
    [FiniteDimensional (ZMod p) V] (hV : Module.finrank (ZMod p) V = 3) (hA : IsPGroup p A)
    (hcomm : ∀ a b : A, a * b = b * a) (ρ : A →* Module.End (ZMod p) V) :
    Nat.card (A ⧸ ρ.ker) ≤ p ^ 2 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hbot : (⊥ : Submodule (ZMod p) V) ≠ ⊤ := by
    intro h
    have h1 : Module.finrank (ZMod p) (⊥ : Submodule (ZMod p) V) =
        Module.finrank (ZMod p) (⊤ : Submodule (ZMod p) V) := by rw [h]
    rw [finrank_bot, finrank_top, hV] at h1
    exact absurd h1 (by norm_num)
  obtain ⟨v1, hv1, hfix1⟩ : ∃ v1 : V, v1 ≠ 0 ∧ ∀ a : A, ρ a v1 = v1 := by
    obtain ⟨v, hv, h⟩ := gl3_exists_fixed_mod hA ρ ⊥
      (fun a w hw => by
        rw [Submodule.mem_bot] at hw
        rw [hw, map_zero]
        exact Submodule.zero_mem _) hbot
    refine ⟨v, fun h0 => hv (h0 ▸ Submodule.zero_mem _), fun a => ?_⟩
    have ha := h a
    rw [Submodule.mem_bot, sub_eq_zero] at ha
    exact ha
  have hW1top : Submodule.span (ZMod p) {v1} ≠ ⊤ := by
    intro h
    have h1 : Module.finrank (ZMod p) (Submodule.span (ZMod p) {v1}) =
        Module.finrank (ZMod p) (⊤ : Submodule (ZMod p) V) := by rw [h]
    rw [finrank_span_singleton hv1, finrank_top, hV] at h1
    exact absurd h1 (by norm_num)
  have hW1 : ∀ a : A, ∀ w ∈ Submodule.span (ZMod p) {v1},
      ρ a w ∈ Submodule.span (ZMod p) {v1} := by
    intro a w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
    rw [map_smul, hfix1 a]
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self v1)
  obtain ⟨v2, hv2, hfix2⟩ := gl3_exists_fixed_mod hA ρ _ hW1 hW1top
  have hsub1 : Submodule.span (ZMod p) {v1} ≤ Submodule.span (ZMod p) {v1, v2} :=
    Submodule.span_mono (Set.singleton_subset_iff.2 (Set.mem_insert _ _))
  have hmem2 : ∀ c d : ZMod p, c • v1 + d • v2 ∈ Submodule.span (ZMod p) {v1, v2} := fun c d =>
    Submodule.add_mem _ (Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_insert _ _)))
      (Submodule.smul_mem _ d (Submodule.subset_span (Set.mem_insert_of_mem _
        (Set.mem_singleton _))))
  have hW2 : ∀ a : A, ∀ w ∈ Submodule.span (ZMod p) {v1, v2},
      ρ a w ∈ Submodule.span (ZMod p) {v1, v2} := by
    intro a w hw
    obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.1 hw
    rw [map_add, map_smul, map_smul, hfix1 a]
    have h2' : ρ a v2 ∈ Submodule.span (ZMod p) {v1, v2} := by
      have := Submodule.add_mem _ (hsub1 (hfix2 a))
        (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)) :
          v2 ∈ Submodule.span (ZMod p) {v1, v2})
      simpa using this
    exact Submodule.add_mem _ (Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_insert _ _)))
      (Submodule.smul_mem _ d h2')
  have hW2top : Submodule.span (ZMod p) {v1, v2} ≠ ⊤ := by
    classical
    intro h
    have h1 : Module.finrank (ZMod p) (Submodule.span (ZMod p) {v1, v2}) =
        Module.finrank (ZMod p) (⊤ : Submodule (ZMod p) V) := by rw [h]
    rw [finrank_top, hV] at h1
    have h2 := finrank_span_finset_le_card (R := ZMod p) ({v1, v2} : Finset V)
    have h3 : (({v1, v2} : Finset V) : Set V) = {v1, v2} := by simp
    have h4 := Finset.card_le_two (a := v1) (b := v2)
    unfold Set.finrank at h2
    rw [h3] at h2
    omega
  obtain ⟨v3, hv3, hfix3⟩ := gl3_exists_fixed_mod hA ρ _ hW2 hW2top
  have hli : LinearIndependent (ZMod p) ![v1, v2, v3] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_three] at hg
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at hg
    have hmem1 : ∀ c : ZMod p, c • v1 ∈ Submodule.span (ZMod p) {v1} := fun c =>
      Submodule.smul_mem _ c (Submodule.mem_span_singleton_self v1)
    have g2 : g 2 = 0 := by
      by_contra hne
      apply hv3
      have h' : g 2 • v3 = -(g 0 • v1 + g 1 • v2) := by
        linear_combination (norm := module) hg
      have h'' : g 2 • v3 ∈ Submodule.span (ZMod p) {v1, v2} := by
        rw [h']
        exact Submodule.neg_mem _ (hmem2 _ _)
      have := Submodule.smul_mem _ (g 2)⁻¹ h''
      rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
    have g1 : g 1 = 0 := by
      by_contra hne
      apply hv2
      have h' : g 1 • v2 = -(g 0 • v1) := by
        rw [g2, zero_smul, add_zero] at hg
        linear_combination (norm := module) hg
      have h'' : g 1 • v2 ∈ Submodule.span (ZMod p) {v1} := by
        rw [h']
        exact Submodule.neg_mem _ (hmem1 _)
      have := Submodule.smul_mem _ (g 1)⁻¹ h''
      rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
    have g0 : g 0 = 0 := by
      rw [g1, g2, zero_smul, zero_smul, add_zero, add_zero] at hg
      exact (smul_eq_zero.1 hg).resolve_right hv1
    intro i
    fin_cases i <;> simp [g0, g1, g2]
  have hspan : Submodule.span (ZMod p) (Set.range ![v1, v2, v3]) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_fin, hV])
  have hcoord2 : ∀ a : A, ∃ α : ZMod p, ρ a v2 = v2 + α • v1 := by
    intro a
    obtain ⟨α, hα⟩ := Submodule.mem_span_singleton.1 (hfix2 a)
    exact ⟨α, by rw [hα]; abel⟩
  have hcoord3 : ∀ a : A, ∃ β γ : ZMod p, ρ a v3 = v3 + β • v2 + γ • v1 := by
    intro a
    obtain ⟨γ, β, hγβ⟩ := Submodule.mem_span_pair.1 (hfix3 a)
    refine ⟨β, γ, ?_⟩
    have h' : ρ a v3 = γ • v1 + β • v2 + v3 := by
      rw [hγβ, sub_add_cancel]
    rw [h']
    abel
  choose α hα using hcoord2
  choose β γ hβγ using hcoord3
  have hcomm2 : ∀ a b : A, (β b * α a - β a * α b) • v1 = 0 := by
    intro a b
    have hab : ρ (a * b) = ρ (b * a) := by rw [hcomm a b]
    have h1 : ρ a (ρ b v3) = ρ b (ρ a v3) := by
      have := congrArg (fun f : Module.End (ZMod p) V => f v3) hab
      simpa [map_mul, Module.End.mul_apply] using this
    simp only [hβγ, hα, hfix1, map_add, map_smul] at h1
    linear_combination (norm := module) h1
  have hαβ : ∀ a b : A, β b * α a = β a * α b := by
    intro a b
    have h := hcomm2 a b
    rw [smul_eq_zero] at h
    rcases h with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hv1
  have hinj : ∀ a b : A, α a = α b → β a = β b → γ a = γ b → ρ a = ρ b := by
    intro a b h1 h2 h3
    refine LinearMap.ext_on_range hspan ?_
    intro i
    fin_cases i
    · simp [hfix1]
    · simp [hα, h1]
    · simp [hβγ, h1, h2, h3]
  obtain ⟨x0, hx0⟩ : ∃ x0 : ZMod p × ZMod p, ∀ a : A,
      ∃ t : ZMod p, α a = t * x0.1 ∧ β a = t * x0.2 := by
    by_cases h : ∃ a0 : A, (α a0 ≠ 0 ∨ β a0 ≠ 0)
    · obtain ⟨a0, ha0⟩ := h
      have hx : ((α a0, β a0) : ZMod p × ZMod p) ≠ 0 := by
        intro h0
        rcases ha0 with h' | h'
        · exact h' (congrArg Prod.fst h0)
        · exact h' (congrArg Prod.snd h0)
      refine ⟨(α a0, β a0), fun a => ?_⟩
      obtain ⟨t, ht1, ht2⟩ := gl3_ray (x := (α a, β a)) hx (by
        have h := hαβ a0 a
        show α a * β a0 = α a0 * β a
        rw [mul_comm (α a) (β a0), mul_comm (α a0) (β a)]
        exact h.symm)
      exact ⟨t, ht1, ht2⟩
    · simp only [not_exists, not_or, ne_eq, not_not] at h
      refine ⟨(1, 0), fun a => ⟨0, ?_⟩⟩
      obtain ⟨h1, h2⟩ := h a
      simp [h1, h2]
  choose t ht using hx0
  have hker : ∀ a1 a2 : A, α a1 = α a2 → β a1 = β a2 → γ a1 = γ a2 → a1⁻¹ * a2 ∈ ρ.ker := by
    intro a1 a2 h1 h2 h3
    rw [MonoidHom.mem_ker, map_mul]
    have hr : ρ a2 = ρ a1 := (hinj a1 a2 h1 h2 h3).symm
    rw [hr, ← map_mul, inv_mul_cancel, map_one]
  let f : A ⧸ ρ.ker → ZMod p × ZMod p := fun q => (t q.out, γ q.out)
  have hf : Function.Injective f := by
    intro q1 q2 h
    simp only [f, Prod.mk.injEq] at h
    obtain ⟨h1, h3⟩ := h
    rw [← QuotientGroup.out_eq' q1, ← QuotientGroup.out_eq' q2, QuotientGroup.eq]
    apply hker
    · rw [(ht q1.out).1, (ht q2.out).1, h1]
    · rw [(ht q1.out).2, (ht q2.out).2, h1]
    · exact h3
  have hcard := Nat.card_le_card_of_injective f hf
  simpa [Nat.card_prod, Nat.card_zmod, sq] using hcard

end Linear

theorem input31_GL3Rank_body :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → ∀ A N : Subgroup G,
      IsElemAbelian p A → IsElemAbelian p N → Nat.card N = p ^ 3 →
        A ≤ Subgroup.normalizer (N : Set G) →
          Nat.card A ≤ p ^ 2 * Nat.card (A ⊓ Subgroup.centralizer (N : Set G) : Subgroup G) := by
  intro G _ _ p hp A N hA hN hNcard hAN
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : IsMulCommutative ↥N := hN.1
  haveI : IsMulCommutative ↥A := hA.1
  have hexp : ∀ x : Additive ↥N, p • x = 0 := by
    intro x
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    apply Subtype.ext
    simpa using hN.2 (x.toMul : G) x.toMul.2
  haveI : Module (ZMod p) (Additive ↥N) := AddCommGroup.zmodModule hexp
  haveI : Finite (Additive ↥N) := Finite.of_equiv ↥N Additive.ofMul
  haveI : Module.Finite (ZMod p) (Additive ↥N) := Module.Finite.of_finite
  have hrank : Module.finrank (ZMod p) (Additive ↥N) = 3 := by
    have h1 : Nat.card (Additive ↥N) = Nat.card (ZMod p) ^ Module.finrank (ZMod p) (Additive ↥N) :=
      @Module.natCard_eq_pow_finrank (ZMod p) (Additive ↥N) _ _ _ _
    rw [Nat.card_zmod, ← Nat.card_congr Additive.ofMul, hNcard] at h1
    exact (Nat.pow_right_injective hp.two_le h1).symm
  have hconj : ∀ (a : A) (y : ↥N), (a : G) * (y : G) * (a : G)⁻¹ ∈ N := fun a y =>
    (Subgroup.mem_normalizer_iff.1 (hAN a.2) (y : G)).1 y.2
  let cjH : A → (↥N →* ↥N) := fun a =>
    { toFun := fun y => ⟨(a : G) * (y : G) * (a : G)⁻¹, hconj a y⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun y z => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  let ρ : A →* Module.End (ZMod p) (Additive ↥N) :=
    { toFun := fun a => AddMonoidHom.toZModLinearMap p (MonoidHom.toAdditive (cjH a))
      map_one' := LinearMap.ext fun y =>
        Additive.toMul.injective (Subtype.ext (by simp [cjH] <;> rfl))
      map_mul' := fun a b => LinearMap.ext fun y =>
        Additive.toMul.injective (Subtype.ext (by
          simp [cjH, Module.End.mul_apply, mul_assoc] <;> group)) }
  have hcore := gl3_core hrank (IsElemAbelian.isPGroup hA) (fun a b => mul_comm a b) ρ
  have hker : Subgroup.map A.subtype ρ.ker = A ⊓ Subgroup.centralizer (N : Set G) := by
    ext x
    simp only [Subgroup.mem_map, MonoidHom.mem_ker, Subgroup.mem_inf]
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨a.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      have h5 : ρ a (Additive.ofMul ⟨n, hn⟩) = Additive.ofMul ⟨n, hn⟩ := by
        have := LinearMap.congr_fun ha (Additive.ofMul ⟨n, hn⟩)
        simpa using this
      have h3 : (a : G) * n * (a : G)⁻¹ = n := by
        have := congrArg (fun z : Additive ↥N => (Additive.toMul z).1) h5
        simpa [ρ, cjH] using this
      have h4 : (a : G) * n = n * a := mul_inv_eq_iff_eq_mul.1 h3
      exact h4.symm
    · rintro ⟨hxA, hxC⟩
      refine ⟨⟨x, hxA⟩, ?_, rfl⟩
      refine LinearMap.ext fun y => ?_
      have hy := Subgroup.mem_centralizer_iff.1 hxC (Additive.toMul y).1 (Additive.toMul y).2
      have key : x * (Additive.toMul y).1 * x⁻¹ = (Additive.toMul y).1 := by
        rw [← hy, mul_inv_cancel_right]
      rw [Module.End.one_apply]
      exact Additive.toMul.injective (Subtype.ext (by simpa [ρ, cjH] using key))
  have hkc : Nat.card ρ.ker = Nat.card (A ⊓ Subgroup.centralizer (N : Set G) : Subgroup G) := by
    rw [← hker, Subgroup.card_map_of_injective (f := A.subtype) Subtype.val_injective]
  calc Nat.card A = Nat.card (A ⧸ ρ.ker) * Nat.card ρ.ker :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker
    _ ≤ p ^ 2 * Nat.card ρ.ker := Nat.mul_le_mul_right _ hcore
    _ = p ^ 2 * Nat.card (A ⊓ Subgroup.centralizer (N : Set G) : Subgroup G) := by rw [hkc]

theorem input31_GL3Rank_holds : Input31_GL3Rank := input31_GL3Rank_body

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

end
