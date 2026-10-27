module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.GroupTheory.PGroup
public import Mathlib.FieldTheory.Finiteness
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.HardMathSupport.Foote.E27.OrthSyl

open LinearMap Module Submodule

@[expose] def bnd (m : ℕ) : ℕ := (m - 1) ^ 2 / 4

theorem bnd_mono {m : ℕ} (hm : m ≤ 7) : bnd (m - 1) ≤ bnd m := by
  unfold bnd; interval_cases m <;> decide

theorem bnd_two {m : ℕ} (hm : m ≤ 7) (h2 : 2 ≤ m) : (m - 2) + bnd (m - 2) ≤ bnd m := by
  unfold bnd; interval_cases m <;> decide

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [Module.Finite K V]

section Lemmas

variable {B : LinearMap.BilinForm K V}

theorem orth_inf_orth (hB : B.Nondegenerate) (hs : B.IsSymm) {X : Submodule K V}
    (hX : X ⊓ B.orthogonal X = ⊥) : B.orthogonal X ⊓ B.orthogonal (B.orthogonal X) = ⊥ := by
  have h := LinearMap.BilinForm.orthogonal_orthogonal hB hs.isRefl X
  rw [h, inf_comm, hX]

theorem sup_nondeg (hs : B.IsSymm) {X Y : Submodule K V} (hY : Y ≤ B.orthogonal X)
    (hX : X ⊓ B.orthogonal X = ⊥) (hYn : Y ⊓ B.orthogonal Y = ⊥) :
    (X ⊔ Y) ⊓ B.orthogonal (X ⊔ Y) = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hz, hzo⟩
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hz
  replace hzo := LinearMap.BilinForm.mem_orthogonal_iff.1 hzo
  have hxo : x ∈ B.orthogonal X := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro x' hx'
    have h1 := hzo x' (Submodule.mem_sup_left hx')
    have h2 : B x' y = 0 := by
      have := hY hy
      rw [LinearMap.BilinForm.mem_orthogonal_iff] at this
      exact this x' hx'
    rw [map_add, h2, add_zero] at h1
    exact h1
  have hx0 : x = 0 := by
    have : x ∈ X ⊓ B.orthogonal X := ⟨hx, hxo⟩
    rw [hX] at this
    exact (Submodule.mem_bot K).1 this
  subst hx0
  have hyo : y ∈ B.orthogonal Y := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y' hy'
    have h1 := hzo y' (Submodule.mem_sup_right hy')
    simpa using h1
  have : y ∈ Y ⊓ B.orthogonal Y := ⟨hy, hyo⟩
  rw [hYn] at this
  have hy0 : y = 0 := (Submodule.mem_bot K).1 this
  simp [hy0]

theorem line_nondeg {v : V} (hv : B v v ≠ 0) : Submodule.span K {v} ⊓ B.orthogonal (Submodule.span K {v}) = ⊥ :=
  LinearMap.BilinForm.span_singleton_inf_orthogonal_eq_bot hv

theorem plane_nondeg (hs : B.IsSymm) {u v : V} (huv : B u v = 1) (hvv : B v v = 0) :
    Submodule.span K {u, v} ⊓ B.orthogonal (Submodule.span K {u, v}) = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hz, hzo⟩
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hz
  replace hzo := LinearMap.BilinForm.mem_orthogonal_iff.1 hzo
  have h1 := hzo v (Submodule.subset_span (by simp))
  have h2 := hzo u (Submodule.subset_span (by simp))
  have hvu : B v u = 1 := by rw [hs.eq]; exact huv
  simp only [map_add, map_smul, smul_eq_mul, hvu, hvv] at h1
  simp only [map_add, map_smul, smul_eq_mul, huv] at h2
  have ha : a = 0 := by simpa using h1
  have hb : b = 0 := by simpa [ha] using h2
  simp [ha, hb]

theorem finrank_sup_of_le_orth {X Y : Submodule K V} (hX : X ⊓ B.orthogonal X = ⊥)
    (hY : Y ≤ B.orthogonal X) : finrank K ↥(X ⊔ Y) = finrank K X + finrank K Y := by
  have hd : X ⊓ Y = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have : z ∈ X ⊓ B.orthogonal X := ⟨hz.1, hY hz.2⟩
    rw [hX] at this
    exact this
  have := Submodule.finrank_sup_add_finrank_inf_eq X Y
  rw [hd, finrank_bot] at this
  omega

@[expose] def proj (B : LinearMap.BilinForm K V) (u v x : V) : V :=
  x - B x v • u - (B x u - B x v * B u u) • v

theorem proj_mem_orth (hs : B.IsSymm) {X : Submodule K V} {u v x : V} (hu : u ∈ B.orthogonal X)
    (hv : v ∈ B.orthogonal X) (hx : x ∈ B.orthogonal X) (huv : B u v = 1) (hvv : B v v = 0) :
    proj B u v x ∈ B.orthogonal (X ⊔ Submodule.span K {u, v}) := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
  obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.1 hb
  have hvu : B v u = 1 := by rw [hs.eq]; exact huv
  have hxu : B x u = B u x := hs.eq _ _
  have hxv : B x v = B v x := hs.eq _ _
  have h1 : B a x = 0 := (LinearMap.BilinForm.mem_orthogonal_iff.1 hx) a ha
  have h2 : B a u = 0 := (LinearMap.BilinForm.mem_orthogonal_iff.1 hu) a ha
  have h3 : B a v = 0 := (LinearMap.BilinForm.mem_orthogonal_iff.1 hv) a ha
  unfold proj
  simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, h1, h2, h3, huv, hvu, hvv, hxu, hxv]
  ring

theorem proj_injOn (hs : B.IsSymm) (h2 : (2 : K) ≠ 0) {u v x₁ x₂ : V} (hvv : B v v = 0)
    (hx₁v : B x₁ v = 1) (hx₂v : B x₂ v = 1) (hx₁ : B x₁ x₁ = B u u)
    (hx₂ : B x₂ x₂ = B u u) (h : proj B u v x₁ = proj B u v x₂) : x₁ = x₂ := by
  unfold proj at h
  rw [hx₁v, hx₂v] at h
  simp only [one_smul, one_mul] at h
  obtain ⟨c, hcdef⟩ : ∃ c, c = B x₁ u - B x₂ u := ⟨_, rfl⟩
  have hc : x₁ = x₂ + c • v := by
    have key : x₁ - (x₂ + c • v) = (x₁ - u - (B x₁ u - B u u) • v) -
        (x₂ - u - (B x₂ u - B u u) • v) := by
      rw [hcdef]; module
    rw [h, sub_self, sub_eq_zero] at key
    exact key
  have hxv : B v x₂ = 1 := by rw [hs.eq]; exact hx₂v
  have e : B x₁ x₁ = B x₂ x₂ + 2 * c := by
    rw [hc]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hvv,
      hx₂v, hxv]
    ring
  have h2c : 2 * c = 0 := by
    have : B x₂ x₂ + 2 * c = B x₂ x₂ := by rw [← e, hx₁, hx₂]
    linear_combination this
  have : c = 0 := by
    rcases mul_eq_zero.1 h2c with h | h
    · exact absurd h h2
    · exact h
  rw [hc, this, zero_smul, add_zero]

theorem exists_fixed_vector (hK : Nat.card K = 3) {G : Type} [Group G] [Finite G]
    (hp : IsPGroup 3 G) (φ : G →* (V ≃ₗ[K] V)) {W : Submodule K V}
    (hW : ∀ g : G, ∀ w ∈ W, φ g w ∈ W) (hpos : 0 < finrank K W) :
    ∃ w ∈ W, w ≠ 0 ∧ ∀ g : G, φ g w = w := by
  classical
  letI : MulAction G W :=
    { smul := fun g w => ⟨φ g w.1, hW g w.1 w.2⟩
      one_smul := fun w => Subtype.ext (by change φ 1 w.1 = w.1; simp)
      mul_smul := fun g h w => Subtype.ext (by change φ (g * h) w.1 = φ g (φ h w.1); simp) }
  have : Fintype K := Fintype.ofFinite K
  have : Finite W := Module.finite_of_finite K
  have : Fintype W := Fintype.ofFinite W
  have hcard : Nat.card W = 3 ^ finrank K W := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := K) (V := W),
      ← Nat.card_eq_fintype_card (α := K), hK]
  have hdvd : 3 ∣ Nat.card W := by
    rw [hcard]; exact dvd_pow_self 3 (Nat.pos_iff_ne_zero.1 hpos)
  have h0 : (0 : W) ∈ MulAction.fixedPoints G W := fun g => Subtype.ext (by change φ g 0 = 0; simp)
  obtain ⟨b, hb, hne⟩ := hp.exists_fixed_point_of_prime_dvd_card_of_fixed_point W hdvd h0
  refine ⟨b.1, b.2, fun h => hne ?_, fun g => ?_⟩
  · exact (Subtype.ext h.symm)
  · exact congrArg Subtype.val (hb g)

end Lemmas

variable {B : LinearMap.BilinForm K V}

theorem pair_finrank (hs : B.IsSymm) {u v : V} (huv : B u v = 1) (hvv : B v v = 0) :
    finrank K (Submodule.span K {u, v}) = 2 := by
  have hli : LinearIndependent K ![u, v] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have h1 := congrArg (fun z => B z v) hab
    have h2 := congrArg (fun z => B z u) hab
    have hvu : B v u = 1 := by rw [hs.eq]; exact huv
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, huv,
      hvv, hvu, map_zero, LinearMap.zero_apply] at h1 h2
    have ha : a = 0 := by simpa using h1
    refine ⟨ha, ?_⟩
    simpa [ha] using h2
  have := finrank_span_eq_card hli
  have hr : Set.range ![u, v] = {u, v} := by
    ext z; simp [eq_comm]; exact or_comm
  rw [hr] at this
  simpa using this

theorem bound_aux (hK : Nat.card K = 3) (h2 : (2 : K) ≠ 0) (hB : B.Nondegenerate)
    (hs : B.IsSymm) (hd : finrank K V ≤ 7) :
    ∀ m : ℕ, ∀ X : Submodule K V, X ⊓ B.orthogonal X = ⊥ → finrank K (B.orthogonal X) = m →
    ∀ (G : Type) [Group G] [Finite G] (φ : G →* (V ≃ₗ[K] V)), Function.Injective φ →
      (∀ g x y, B (φ g x) (φ g y) = B x y) → IsPGroup 3 G → (∀ g, ∀ x ∈ X, φ g x = x) →
      Nat.card G ≤ 3 ^ bnd m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro X hX hm G _ _ φ hφ hiso hp hfix
  have : Finite V := Module.finite_of_finite K
  have hm7 : m ≤ 7 := by rw [← hm]; exact (Submodule.finrank_le _).trans hd
  have hWdim : m + finrank K X = finrank K V := by
    have := LinearMap.BilinForm.finrank_orthogonal hB X
    have hle := Submodule.finrank_le X
    have hle2 : finrank K X ≤ finrank K V := Submodule.finrank_le X
    omega
  have hWpres : ∀ g : G, ∀ w ∈ B.orthogonal X, φ g w ∈ B.orthogonal X := by
    intro g w hw
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hw ⊢
    intro x hx
    have := hiso g x w
    rw [hfix g x hx] at this
    rw [this]
    exact hw x hx
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  · have hWbot : B.orthogonal X = ⊥ := Submodule.finrank_eq_zero.1 hm
    have hXtop : X = ⊤ := by
      have : B.orthogonal (B.orthogonal X) = X :=
        LinearMap.BilinForm.orthogonal_orthogonal hB hs.isRefl X
      rw [← this, hWbot, LinearMap.BilinForm.orthogonal_bot]
    have hsub : Subsingleton G := by
      refine ⟨fun a b => hφ (LinearEquiv.ext fun x => ?_)⟩
      rw [hfix a x (by rw [hXtop]; trivial), hfix b x (by rw [hXtop]; trivial)]
    have : Nat.card G = 1 := Nat.card_eq_one_iff_unique.2 ⟨hsub, ⟨1⟩⟩
    rw [this]; simp [bnd]
  obtain ⟨v, hvW, hv0, hvfix⟩ := exists_fixed_vector hK hp φ hWpres (by rw [hm]; exact hmpos)
  by_cases hvv : B v v = 0
  · have hWWn := orth_inf_orth hB hs hX
    have hex : ∃ u ∈ B.orthogonal X, B u v = 1 := by
      by_contra hno
      push Not at hno
      have hvo : v ∈ B.orthogonal (B.orthogonal X) := by
        rw [LinearMap.BilinForm.mem_orthogonal_iff]
        intro u hu
        by_contra hne
        refine hno ((B u v)⁻¹ • u) (Submodule.smul_mem _ _ hu) ?_
        rw [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hne]
      have : v ∈ B.orthogonal X ⊓ B.orthogonal (B.orthogonal X) := ⟨hvW, hvo⟩
      rw [hWWn] at this
      exact hv0 ((Submodule.mem_bot K).1 this)
    obtain ⟨u, huW, huv⟩ := hex
    have hYX : Submodule.span K {u, v} ≤ B.orthogonal X := by
      rw [Submodule.span_le]
      intro z hz
      rcases hz with rfl | rfl
      · exact huW
      · exact hvW
    have hX'' : (X ⊔ Submodule.span K {u, v}) ⊓ B.orthogonal (X ⊔ Submodule.span K {u, v}) = ⊥ :=
      sup_nondeg hs hYX hX (plane_nondeg hs huv hvv)
    have hdimX'' : finrank K ↥(X ⊔ Submodule.span K {u, v}) = finrank K X + 2 := by
      rw [finrank_sup_of_le_orth hX hYX, pair_finrank hs huv hvv]
    have hle := Submodule.finrank_le (X ⊔ Submodule.span K {u, v})
    have hm2 : 2 ≤ m := by omega
    have hdimW'' : finrank K (B.orthogonal (X ⊔ Submodule.span K {u, v})) = m - 2 := by
      rw [LinearMap.BilinForm.finrank_orthogonal hB, hdimX'']
      omega
    let A : Set V := {x | x ∈ B.orthogonal X ∧ B x v = 1 ∧ B x x = B u u}
    have hAcard : Nat.card A ≤ 3 ^ (m - 2) := by
      let f : A → B.orthogonal (X ⊔ Submodule.span K {u, v}) := fun x =>
        ⟨proj B u v x.1, proj_mem_orth hs huW hvW x.2.1 huv hvv⟩
      have hf : Function.Injective f := by
        intro x y hxy
        apply Subtype.ext
        exact proj_injOn hs h2 hvv x.2.2.1 y.2.2.1 x.2.2.2 y.2.2.2 (congrArg Subtype.val hxy)
      have : Fintype K := Fintype.ofFinite K
      have : Finite (B.orthogonal (X ⊔ Submodule.span K {u, v})) := Module.finite_of_finite K
      have : Fintype (B.orthogonal (X ⊔ Submodule.span K {u, v})) := Fintype.ofFinite _
      refine (Nat.card_le_card_of_injective f hf).trans ?_
      rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := K), hdimW'',
        ← Nat.card_eq_fintype_card (α := K), hK]
    letI : MulAction G V := MulAction.compHom V φ
    have hsm : ∀ (g : G) (x : V), g • x = φ g x := fun _ _ => rfl
    have horb : Nat.card (MulAction.orbit G u) ≤ 3 ^ (m - 2) := by
      refine le_trans (Nat.card_mono (Set.toFinite A) ?_) hAcard
      rintro _ ⟨g, rfl⟩
      show φ g u ∈ A
      refine ⟨hWpres g u huW, ?_, ?_⟩
      · have := hiso g u v
        rwa [hvfix g, huv] at this
      · exact hiso g u u
    have hstab : Nat.card (MulAction.stabilizer G u) ≤ 3 ^ bnd (m - 2) := by
      have hfixS : ∀ g : MulAction.stabilizer G u, ∀ x ∈ X ⊔ Submodule.span K {u, v},
          (φ.comp (MulAction.stabilizer G u).subtype) g x = x := by
        intro g x hx
        obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
        obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.1 hb
        have hgu : φ g.1 u = u := g.2
        simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, map_add, map_smul]
        rw [hfix g.1 a ha, hgu, hvfix g.1]
      have hinjS : Function.Injective (φ.comp (MulAction.stabilizer G u).subtype) :=
        hφ.comp (Subgroup.subtype_injective _)
      have hisoS : ∀ g : MulAction.stabilizer G u, ∀ x y,
          B ((φ.comp (MulAction.stabilizer G u).subtype) g x)
            ((φ.comp (MulAction.stabilizer G u).subtype) g y) = B x y := fun g x y => hiso g.1 x y
      exact ih (m - 2) (by omega) _ hX'' hdimW'' _ _ hinjS hisoS (hp.to_subgroup _) hfixS
    have hos : Nat.card (MulAction.orbit G u) * Nat.card (MulAction.stabilizer G u) =
        Nat.card G := by
      classical
      have : Fintype G := Fintype.ofFinite G
      have : Fintype (MulAction.orbit G u) := Fintype.ofFinite _
      have : Fintype (MulAction.stabilizer G u) := Fintype.ofFinite _
      have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group G u
      simpa [Nat.card_eq_fintype_card] using h
    calc Nat.card G = Nat.card (MulAction.orbit G u) * Nat.card (MulAction.stabilizer G u) :=
          hos.symm
      _ ≤ 3 ^ (m - 2) * 3 ^ bnd (m - 2) := Nat.mul_le_mul horb hstab
      _ = 3 ^ ((m - 2) + bnd (m - 2)) := (pow_add _ _ _).symm
      _ ≤ 3 ^ bnd m := Nat.pow_le_pow_right (by norm_num) (bnd_two hm7 hm2)
  · have hYX : Submodule.span K {v} ≤ B.orthogonal X :=
      (Submodule.span_singleton_le_iff_mem v _).2 hvW
    have hX' : (X ⊔ Submodule.span K {v}) ⊓ B.orthogonal (X ⊔ Submodule.span K {v}) = ⊥ :=
      sup_nondeg hs hYX hX (line_nondeg hvv)
    have hdimX' : finrank K ↥(X ⊔ Submodule.span K {v}) = finrank K X + 1 := by
      rw [finrank_sup_of_le_orth hX hYX, finrank_span_singleton hv0]
    have hdimW' : finrank K (B.orthogonal (X ⊔ Submodule.span K {v})) = m - 1 := by
      rw [LinearMap.BilinForm.finrank_orthogonal hB, hdimX']
      have := Submodule.finrank_le (X ⊔ Submodule.span K {v})
      omega
    have hfix' : ∀ g : G, ∀ x ∈ X ⊔ Submodule.span K {v}, φ g x = x := by
      intro g x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hb
      rw [map_add, map_smul, hfix g a ha, hvfix g]
    have := ih (m - 1) (by omega) (X ⊔ Submodule.span K {v}) hX' hdimW' G φ hφ hiso hp hfix'
    exact this.trans (Nat.pow_le_pow_right (by norm_num) (bnd_mono hm7))

theorem card_le_of_isPGroup (hK : Nat.card K = 3) (h2 : (2 : K) ≠ 0) (hB : B.Nondegenerate)
    (hs : B.IsSymm) (hd : finrank K V ≤ 7) {G : Type} [Group G] [Finite G]
    (φ : G →* (V ≃ₗ[K] V)) (hφ : Function.Injective φ) (hiso : ∀ g x y, B (φ g x) (φ g y) = B x y)
    (hp : IsPGroup 3 G) : Nat.card G ≤ 3 ^ bnd (finrank K V) := by
  have h := bound_aux hK h2 hB hs hd (finrank K V) ⊥ (bot_inf_eq _)
    (by rw [LinearMap.BilinForm.orthogonal_bot, finrank_top]) G φ hφ hiso hp
    (fun g x hx => by rw [(Submodule.mem_bot K).1 hx, map_zero])
  exact h

end CFSG.HardMathSupport.Foote.E27.OrthSyl
