module

public import CFSG.ClassicalGroups.Alternating.PointRadicalFixedCard
public import CFSG.ClassicalGroups.Symplectic.StandardForm

public section

namespace CFSG.ClassicalGroups.Alternating

open LinearMap (BilinForm)
open CFSG.ClassicalGroups.Symplectic

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {B : BilinForm K V}

theorem mem_span_of_forall_orthogonal [FiniteDimensional K V] (hBn : B.Nondegenerate)
    {ι : Type*} [Finite ι] (v : ι → V) (x : V)
    (h : ∀ y, (∀ i, B (v i) y = 0) → B x y = 0) : x ∈ Submodule.span K (Set.range v) := by
  have _ := Fintype.ofFinite ι
  have hker : ⨅ i, LinearMap.ker (B (v i)) ≤ LinearMap.ker (B x) := fun y hy => by
    rw [Submodule.mem_iInf] at hy
    exact h y fun i => LinearMap.mem_ker.mp (hy i)
  have hspan := mem_span_of_iInf_ker_le_ker hker
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hspan
  have h0 : ∀ y, B (x - ∑ i, c i • v i) y = 0 := by
    intro y
    have h1 := congrArg (fun f : V →ₗ[K] K => f y) hc
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at h1
    simp only [map_sub, map_sum, map_smul, LinearMap.sub_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul]
    rw [h1]
    ring
  have : x = ∑ i, c i • v i := sub_eq_zero.mp (hBn.1 _ h0)
  rw [this]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem Ssp_mul_Ssp (hB : B.IsAlt) {v w w' : V} (hw : B v w = 0) (hw' : B v w' = 0) (c c' : K) :
    Ssp hB v w c * Ssp hB v w' c' = Ssp hB v (w + w') (c + c' + B w' w) :=
  Subtype.ext (siegel_mul hB hw hw' c c')

theorem Ssp_conj (hB : B.IsAlt) (g : Gsp B) (v w : V) (c : K) :
    g * Ssp hB v w c * g⁻¹ = Ssp hB (g.app v) (g.app w) c :=
  Subtype.ext (siegel_conj hB g.2 v w c)

theorem Ssp_zero (hB : B.IsAlt) (v : V) (c : K) : Ssp hB v 0 c = Tsp hB v c :=
  Subtype.ext (siegel_zero_eq hB v c)

theorem Ssp_smul_left (hB : B.IsAlt) {v w : V} (hw : B v w = 0) (s c : K) :
    Ssp hB (s • v) w c = Ssp hB v (s • w) (s ^ 2 * c) :=
  Subtype.ext (siegel_smul_left hB hw s c)

theorem Tsp_zero (hB : B.IsAlt) (v : V) : Tsp hB v 0 = 1 :=
  Subtype.ext (symplecticTransvection_zero hB v)

private theorem two_smul_eq_zero [CharP K 2] (x : V) : x + x = 0 := by
  rw [← two_smul K x, CharTwo.two_eq_zero, zero_smul]

theorem eq_Lsp_of_normalized [FiniteDimensional K V] [Finite K] [CharP K 2] (hB : B.IsAlt)
    (hBn : B.Nondegenerate) (hK : 2 < Nat.card K) {u : V} (hu : u ≠ 0)
    (S : Subgroup (Gsp B)) (hSL : S ≤ Lsp B hB u)
    (hSn : ∀ g : Gsp B, (∃ c : K, g.app u = c • u) → ∀ s ∈ S, g * s * g⁻¹ ∈ S)
    (hnT : ∃ s ∈ S, ∀ c : K, s ≠ Tsp hB u c) : S = Lsp B hB u := by
  classical
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hflip : ∀ x y : V, B x y = 0 → B y x = 0 := fun x y h => by
    rw [← hB.neg_eq x y, h, neg_zero]
  obtain ⟨s₀, hs₀S, hs₀T⟩ := hnT
  obtain ⟨w₀, c₀, hw₀, hs₀eq⟩ : ∃ w c, B u w = 0 ∧ s₀ = Ssp hB u w c := by
    obtain ⟨w, c, hw, hxw⟩ := mem_Lsp.mp (hSL hs₀S)
    exact ⟨w, c, hw, Subtype.ext hxw.symm⟩
  have hw₀u : ∀ a : K, w₀ ≠ a • u := by
    intro a ha
    apply hs₀T c₀
    rw [hs₀eq, ha, Ssp_smul_self]
  obtain ⟨z₁, hz₁u, hz₁⟩ : ∃ z, B u z = 0 ∧ B w₀ z ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hmem := mem_span_of_forall_orthogonal hBn (fun _ : Unit => u) w₀
      (fun y hy => hcon y (hy ()))
    rw [Set.range_const, Submodule.mem_span_singleton] at hmem
    obtain ⟨a, ha⟩ := hmem
    exact hw₀u a ha.symm
  have hBflip : ∀ x : V, B x x = 0 := hB.self_eq_zero
  have hE : ∀ z, B u z = 0 → B w₀ z ≠ 0 → Ssp hB u z (B w₀ z) ∈ S := by
    intro z hz hβ
    set β := B w₀ z with hβdef
    let g : Gsp B := Tsp hB z β⁻¹
    have hgu : g.app u = (1 : K) • u := by
      show (Tsp hB z β⁻¹).app u = _
      rw [Tsp_app, hz, mul_zero, zero_smul, add_zero, one_smul]
    have hgw : g.app w₀ = w₀ + z := by
      show (Tsp hB z β⁻¹).app w₀ = _
      rw [Tsp_app, ← hβdef, inv_mul_cancel₀ hβ, one_smul]
    have h1 := hSn g ⟨1, hgu⟩ s₀ hs₀S
    rw [hs₀eq, Ssp_conj, hgu, hgw, one_smul] at h1
    have hwz : B u (w₀ + z) = 0 := by rw [map_add, hw₀, hz, add_zero]
    have h3 := S.mul_mem h1 hs₀S
    rw [hs₀eq, Ssp_mul_Ssp hB hwz hw₀] at h3
    have e1 : w₀ + z + w₀ = z := by
      rw [add_comm w₀ z, add_assoc, two_smul_eq_zero (K := K) w₀, add_zero]
    have e2 : c₀ + c₀ + B w₀ (w₀ + z) = β := by
      rw [CharTwo.add_self_eq_zero, zero_add, map_add, hBflip, zero_add]
    rw [e1, e2] at h3
    exact h3
  have hX : ∀ w, B u w = 0 → ∃ c, Ssp hB u w c ∈ S := by
    intro w hw
    by_cases hβw : B w₀ w = 0
    · have hwz : B u (w + z₁) = 0 := by rw [map_add, hw, hz₁u, add_zero]
      have hβ' : B w₀ (w + z₁) ≠ 0 := by rw [map_add, hβw, zero_add]; exact hz₁
      have h3 := S.mul_mem (hE (w + z₁) hwz hβ') (hE z₁ hz₁u hz₁)
      rw [Ssp_mul_Ssp hB hwz hz₁u] at h3
      have e1 : w + z₁ + z₁ = w := by
        rw [add_assoc, two_smul_eq_zero (K := K) z₁, add_zero]
      rw [e1] at h3
      exact ⟨_, h3⟩
    · exact ⟨_, hE w hw hβw⟩
  obtain ⟨a, ha0, ha1⟩ : ∃ a : K, a ≠ 0 ∧ a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : (Set.univ : Set K) ⊆ {0, 1} := fun x _ => by
      by_cases hx : x = 0
      · simp [hx]
      · simp [hcon x hx]
    have : Nat.card K ≤ 2 := by
      calc Nat.card K = (Set.univ : Set K).ncard := (Set.ncard_univ K).symm
        _ ≤ ({0, 1} : Set K).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ 2 := by
          refine (Set.ncard_insert_le _ _).trans ?_
          rw [Set.ncard_singleton]
    omega
  obtain ⟨z₁', hz₁'u, hz₁'1⟩ : ∃ z, B u z = 0 ∧ B w₀ z = 1 :=
    ⟨(B w₀ z₁)⁻¹ • z₁, by rw [map_smul, hz₁u, smul_zero],
      by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hz₁]⟩
  obtain ⟨y, hyu, hyw, hyz⟩ : ∃ y, B u y = 0 ∧ B w₀ y = 0 ∧ B z₁' y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hmem := mem_span_of_forall_orthogonal hBn (![u, w₀] : Fin 2 → V) z₁'
      (fun y hy => hcon y (hy 0) (hy 1))
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hmem
    rw [Fin.sum_univ_two] at hc
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hc
    have h0 : B w₀ z₁' = 0 := by
      rw [← hc, map_add, map_smul, map_smul, hflip u w₀ hw₀, hBflip, smul_zero, smul_zero,
        add_zero]
    rw [hz₁'1] at h0
    exact one_ne_zero h0
  obtain ⟨z₂, hz₂u, hz₂w, hne⟩ : ∃ z₂, B u z₂ = 0 ∧ B w₀ z₂ = a ∧ B z₂ z₁' ≠ 0 := by
    refine ⟨a • z₁' + y, ?_, ?_, ?_⟩
    · rw [map_add, map_smul, hz₁'u, hyu, smul_zero, add_zero]
    · rw [map_add, map_smul, hz₁'1, hyw, smul_eq_mul, mul_one, add_zero]
    · rw [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, hBflip, smul_zero,
        zero_add]
      intro h
      exact hyz (hflip y z₁' h)
  have hz₃u : B u (z₁' + z₂) = 0 := by rw [map_add, hz₁'u, hz₂u, add_zero]
  have hz₃w : B w₀ (z₁' + z₂) = 1 + a := by rw [map_add, hz₁'1, hz₂w]
  have h1a : (1 + a : K) ≠ 0 := by
    intro h
    apply ha1
    have := eq_neg_of_add_eq_zero_right h
    rw [this, CharTwo.neg_eq]
  have e₁ := hE z₁' hz₁'u (by rw [hz₁'1]; exact one_ne_zero)
  have e₂ := hE z₂ hz₂u (by rw [hz₂w]; exact ha0)
  have e₃ := hE (z₁' + z₂) hz₃u (by rw [hz₃w]; exact h1a)
  rw [hz₁'1] at e₁
  rw [hz₂w] at e₂
  rw [hz₃w] at e₃
  have hprod := S.mul_mem (S.mul_mem e₁ e₂) e₃
  rw [Ssp_mul_Ssp hB hz₁'u hz₂u,
    Ssp_mul_Ssp hB (by rw [map_add, hz₁'u, hz₂u, add_zero]) hz₃u] at hprod
  have e4 : z₁' + z₂ + (z₁' + z₂) = 0 := two_smul_eq_zero (K := K) _
  have e5 : 1 + a + B z₂ z₁' + (1 + a) + B (z₁' + z₂) (z₁' + z₂) = B z₂ z₁' := by
    rw [hBflip]
    have : (1 + a + B z₂ z₁' + (1 + a) + 0 : K) = B z₂ z₁' + ((1 + a) + (1 + a)) := by ring
    rw [this, CharTwo.add_self_eq_zero, add_zero]
  rw [e4, e5, Ssp_zero] at hprod
  have hTall : ∀ c, Tsp hB u c ∈ S := by
    intro c
    by_cases hc : c = 0
    · rw [hc, Tsp_zero]; exact S.one_mem
    · obtain ⟨l, hl⟩ : ∃ l : K, l ^ 2 = c / B z₂ z₁' := by
        obtain ⟨l, hl⟩ : IsSquare (c / B z₂ z₁') :=
          FiniteField.isSquare_of_char_two (ringChar.eq K 2) _
        exact ⟨l, by rw [sq]; exact hl.symm⟩
      have hl0 : l ≠ 0 := by
        rintro rfl
        rw [zero_pow two_ne_zero] at hl
        exact div_ne_zero hc hne hl.symm
      obtain ⟨g, hg⟩ := exists_gsp_apply_eq hB hBn hu (smul_ne_zero hl0 hu)
      have h1 := hSn g ⟨l, hg⟩ _ hprod
      rw [← Ssp_zero hB u (B z₂ z₁'), Ssp_conj, hg, Gsp.map_zero',
        Ssp_smul_left hB (map_zero (B u)) l, smul_zero, Ssp_zero] at h1
      have e6 : l ^ 2 * B z₂ z₁' = c := by rw [hl]; field_simp
      rw [e6] at h1
      exact h1
  refine le_antisymm hSL (fun x hx => ?_)
  obtain ⟨w, c, hw, hxw⟩ := mem_Lsp.mp hx
  have hx' : x = Ssp hB u w c := Subtype.ext hxw.symm
  obtain ⟨c', hc'⟩ := hX w hw
  have h3 := S.mul_mem hc' (hTall (c - c'))
  rw [← Ssp_zero hB u (c - c'), Ssp_mul_Ssp hB hw (map_zero (B u)), add_zero, map_zero,
    LinearMap.zero_apply, add_zero, add_sub_cancel] at h3
  rw [hx']
  exact h3

end CFSG.ClassicalGroups.Alternating

namespace CFSG.ClassicalGroups.Symplectic

open CFSG.Open CFSG.ClassicalGroups.Alternating
open Matrix

variable {m : ℕ} {K : Type} [Field K]

theorem eq_LspGL_of_normalized [Finite K] [CharP K 2] (hK : 2 < Nat.card K)
    {u : Fin m ⊕ Fin m → K} (hu : u ≠ 0) (S : Subgroup (GL (Fin m ⊕ Fin m) K))
    (hSL : S ≤ LspGL m K u)
    (hSn : ∀ g ∈ StatedSp m K,
      (∃ c : K, (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u = c • u) →
        ∀ s ∈ S, g * s * g⁻¹ ∈ S)
    (hnT : ∃ s ∈ S, ∀ c : K, ∃ x : Fin m ⊕ Fin m → K,
      (s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x ≠ x + (c * spForm m K x u) • u) :
    S = LspGL m K u := by
  classical
  let e : StatedSp m K ≃* Gsp (spForm m K) := spEquiv
  let S' : Subgroup (Gsp (spForm m K)) :=
    (S.comap (StatedSp m K).subtype).map e.toMonoidHom
  have hS'mem : ∀ g : Gsp (spForm m K), g ∈ S' ↔ (e.symm g : GL (Fin m ⊕ Fin m) K) ∈ S := by
    intro g
    constructor
    · rintro ⟨s, hs, rfl⟩
      show ((e.symm (e s) : StatedSp m K) : GL (Fin m ⊕ Fin m) K) ∈ S
      rw [MulEquiv.symm_apply_apply]
      exact hs
    · intro h
      exact ⟨e.symm g, h, by simp⟩
  have hS'L : S' ≤ Lsp (spForm m K) spForm_isAlt u := by
    intro g hg
    have h1 := (mem_LspGL_iff.mp (hSL ((hS'mem g).mp hg))).2
    have h2 : spEquiv (m := m) (K := K) (e.symm g) = g := e.apply_symm_apply g
    rw [show (⟨((e.symm g : StatedSp m K) : GL (Fin m ⊕ Fin m) K), (e.symm g).2⟩ :
      StatedSp m K) = e.symm g from rfl, h2] at h1
    exact h1
  have hS'n : ∀ g : Gsp (spForm m K), (∃ c : K, g.app u = c • u) → ∀ s ∈ S', g * s * g⁻¹ ∈ S' := by
    intro g ⟨c, hc⟩ s hs
    rw [hS'mem] at hs ⊢
    have hgS := (e.symm g).2
    have h1 := hSn (e.symm g : GL (Fin m ⊕ Fin m) K) hgS ⟨c, ?_⟩ _ hs
    · simpa using h1
    · have := spEquiv_app (e.symm g) u
      rw [MulEquiv.apply_symm_apply] at this
      rw [← this]
      exact hc
  have hS'T : ∃ s ∈ S', ∀ c : K, s ≠ Tsp spForm_isAlt u c := by
    obtain ⟨s, hsS, hsT⟩ := hnT
    refine ⟨e ⟨s, hSL.trans (LspGL_le_statedSp u) hsS⟩, (hS'mem _).mpr (by simpa using hsS), ?_⟩
    intro c hc
    obtain ⟨x, hx⟩ := hsT c
    apply hx
    have h1 := congrArg (fun t : Gsp (spForm m K) => t.app x) hc
    simp only [Tsp_app] at h1
    rw [← h1]
    exact (spEquiv_app ⟨s, hSL.trans (LspGL_le_statedSp u) hsS⟩ x).symm
  have hmain := eq_Lsp_of_normalized spForm_isAlt spForm_nondegenerate hK hu S' hS'L hS'n hS'T
  refine le_antisymm hSL (fun x hx => ?_)
  have hxSp : x ∈ StatedSp m K := LspGL_le_statedSp u hx
  have h1 : e ⟨x, hxSp⟩ ∈ S' := by
    rw [hmain]
    exact (mem_LspGL_iff.mp hx).2
  simpa using (hS'mem _).mp h1

end CFSG.ClassicalGroups.Symplectic
