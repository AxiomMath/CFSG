module

public import CFSG.LocalAnalysis.QuasithinUnique.ONanCount

public section

namespace CFSG.QuasithinUnique.ONan

open Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {X R : Subgroup (V ≃ₗ[ZMod 2] V)} {A C : Submodule (ZMod 2) V}

omit [Finite V] in
theorem span_invariant {Δ : Set V} (hΔ : ∀ x ∈ X, ∀ d ∈ Δ, x d ∈ Δ) :
    ∀ x ∈ X, ∀ v ∈ Submodule.span (ZMod 2) Δ, x v ∈ Submodule.span (ZMod 2) Δ := by
  intro x hx v hv
  induction hv using Submodule.span_induction with
  | mem d hd => exact Submodule.subset_span (hΔ x hx d hd)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add u w _ _ hu hw => rw [map_add]; exact Submodule.add_mem _ hu hw
  | smul c u _ hu => rw [map_smul]; exact Submodule.smul_mem _ c hu

def fibre (A C : Submodule (ZMod 2) V) (Δ : Set V) : Set C :=
  {e | ∃ a : A, a ≠ 0 ∧ (a : V) + (e : V) ∈ Δ}

omit [Finite V] in
theorem fibre_nonempty (S : Setting X R A C)
    (hX : ∀ W : Submodule (ZMod 2) V, (∀ x ∈ X, ∀ v ∈ W, x v ∈ W) → W = ⊥ ∨ W = ⊤)
    (hCA : finrank (ZMod 2) C < finrank (ZMod 2) A) {Δ : Set V}
    (hΔx : ∀ x ∈ X, ∀ d ∈ Δ, x d ∈ Δ) (hΔne : ∃ d ∈ Δ, d ≠ 0) : (fibre A C Δ).Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have hΔC : Δ ⊆ C := by
    intro d hd
    obtain ⟨a, ha, e, he, rfl⟩ := S.decomp d
    by_cases ha0 : a = 0
    · rw [ha0, zero_add]; exact he
    · exfalso
      have : (⟨e, he⟩ : C) ∈ fibre A C Δ := ⟨⟨a, ha⟩, fun h => ha0 (congrArg Subtype.val h), hd⟩
      rw [hne] at this
      exact this
  have hW := hX (Submodule.span (ZMod 2) Δ) (span_invariant hΔx)
  obtain ⟨d, hd, hd0⟩ := hΔne
  rcases hW with h | h
  · have : d ∈ (⊥ : Submodule (ZMod 2) V) := h ▸ Submodule.subset_span hd
    exact hd0 ((Submodule.mem_bot _).mp this)
  · have hCtop : C = ⊤ := by
      rw [eq_top_iff, ← h, Submodule.span_le]
      exact hΔC
    have hAbot : A = ⊥ := by
      rw [eq_bot_iff]
      intro a ha
      exact (Submodule.mem_bot _).mpr (S.eq_zero_of_mem ha (hCtop ▸ Submodule.mem_top))
    rw [hAbot, finrank_bot] at hCA
    omega

theorem key_contradiction (S : Setting X R A C)
    (hX : ∀ W : Submodule (ZMod 2) V, (∀ x ∈ X, ∀ v ∈ W, x v ∈ W) → W = ⊥ ∨ W = ⊤)
    (hC : 2 ≤ finrank (ZMod 2) C) (hCA : finrank (ZMod 2) C < finrank (ZMod 2) A)
    {Δ : Set V} (hΔx : ∀ x ∈ X, ∀ d ∈ Δ, x d ∈ Δ) (hΔ0 : (0 : V) ∉ Δ)
    (hk : 1 ≤ (fibre A C Δ).ncard) (hks : 2 * (fibre A C Δ).ncard ≤ Nat.card C) : False := by
  classical
  let φ : A × C → V := fun p => (p.1 : V) + (p.2 : V)
  have hφadd : ∀ p p' : A × C, φ (p + p') = φ p + φ p' := by
    intro p p'
    show ((p.1 + p'.1 : A) : V) + ((p.2 + p'.2 : C) : V) = _
    push_cast
    exact add_add_add_comm _ _ _ _
  have hφinj : Function.Injective φ := by
    rintro ⟨a, e⟩ ⟨a', e'⟩ h
    obtain ⟨h1, h2⟩ := S.add_inj a.2 a'.2 e.2 e'.2 h
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  have hφsurj : Function.Surjective φ := by
    intro v
    obtain ⟨a, ha, e, he, rfl⟩ := S.decomp v
    exact ⟨(⟨a, ha⟩, ⟨e, he⟩), rfl⟩
  let Q : Set (A × C) := φ ⁻¹' Δ
  let D : Set C := fibre A C Δ
  let F : Set C := {e | ((0 : A), e) ∈ Q}
  have hQ : ∀ a e, (a, e) ∈ Q ↔ (a ≠ 0 ∧ e ∈ D) ∨ (a = 0 ∧ e ∈ F) := by
    intro a e
    constructor
    · intro h
      by_cases ha : a = 0
      · subst ha; exact Or.inr ⟨rfl, h⟩
      · exact Or.inl ⟨ha, ⟨a, ha, h⟩⟩
    · rintro (⟨ha, a', ha', h'⟩ | ⟨rfl, h⟩)
      · have ha0 : (a : V) ≠ 0 := fun h => ha (Subtype.ext h)
        have ha'0 : (a' : V) ≠ 0 := fun h => ha' (Subtype.ext h)
        obtain ⟨r, hr, hra⟩ := S.trans a' a'.2 a a.2 ha'0 ha0
        have := hΔx r (S.le hr) _ h'
        rw [map_add, hra, S.fixes r hr e e.2] at this
        exact this
      · exact h
  have hF0 : (0 : C) ∉ F := by
    intro h
    have h' : φ ((0 : A), (0 : C)) ∈ Δ := h
    have h0 : φ ((0 : A), (0 : C)) = 0 := by simp [φ]
    rw [h0] at h'
    exact hΔ0 h'
  have hsC : 4 ≤ Nat.card C := by
    rw [natCard_submodule]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ finrank (ZMod 2) C := Nat.pow_le_pow_right (by norm_num) hC
  have hqs : 2 * Nat.card C ≤ Nat.card A := by
    rw [natCard_submodule, natCard_submodule]
    calc 2 * 2 ^ finrank (ZMod 2) C = 2 ^ (finrank (ZMod 2) C + 1) := by ring
      _ ≤ 2 ^ finrank (ZMod 2) A := Nat.pow_le_pow_right (by norm_num) hCA
  have hkD : 1 ≤ D.ncard := hk
  have hksD : 2 * D.ncard ≤ Nat.card C := hks
  have hcount := corr_dichotomy hQ hF0 hkD hksD hsC hqs
  let n : V → ℕ := fun x => {v : V | v ∈ Δ ∧ v + x ∈ Δ}.ncard
  have hn : ∀ (b : A) (t : C), n ((b : V) + (t : V)) =
      {p : A × C | p ∈ Q ∧ p + (b, t) ∈ Q}.ncard := by
    intro b t
    have himg : {v : V | v ∈ Δ ∧ v + ((b : V) + (t : V)) ∈ Δ} =
        φ '' {p : A × C | p ∈ Q ∧ p + (b, t) ∈ Q} := by
      ext v
      constructor
      · rintro ⟨h1, h2⟩
        obtain ⟨p, rfl⟩ := hφsurj v
        refine ⟨p, ⟨h1, ?_⟩, rfl⟩
        show φ (p + (b, t)) ∈ Δ
        rw [hφadd]
        exact h2
      · rintro ⟨p, ⟨h1, h2⟩, rfl⟩
        refine ⟨h1, ?_⟩
        have h2' : φ (p + (b, t)) ∈ Δ := h2
        rwa [hφadd] at h2'
    show {v : V | v ∈ Δ ∧ v + ((b : V) + (t : V)) ∈ Δ}.ncard = _
    rw [himg, Set.ncard_image_of_injective _ hφinj]
  have hnmono : ∀ x ∈ X, ∀ y : V, n y ≤ n (x y) := by
    intro x hx y
    apply Set.ncard_le_ncard_of_injOn (fun v => x v)
    · rintro v ⟨h1, h2⟩
      refine ⟨hΔx x hx v h1, ?_⟩
      have := hΔx x hx _ h2
      rwa [map_add] at this
    · intro v _ w _ h
      exact x.injective h
  let Pc : C → Prop := fun t => ∀ e ∈ D, e + t ∈ D
  let Us : Set V := {v | ∃ (b : A) (t : C), Pc t ∧ (b : V) + (t : V) = v}
  have hUs0 : (0 : V) ∈ Us := ⟨0, 0, fun e he => by simpa using he, by simp⟩
  have hUsadd : ∀ x ∈ Us, ∀ y ∈ Us, x + y ∈ Us := by
    rintro _ ⟨b, t, ht, rfl⟩ _ ⟨b', t', ht', rfl⟩
    refine ⟨b + b', t + t', fun e he => ?_, ?_⟩
    · rw [← add_assoc]
      exact ht' _ (ht e he)
    · push_cast
      exact add_add_add_comm _ _ _ _
  let U : Submodule (ZMod 2) V := submoduleOfAdd Us hUs0 hUsadd
  have hUmem : ∀ v, v ∈ U ↔ v ∈ Us := fun v => mem_submoduleOfAdd Us hUs0 hUsadd v
  have hUchar : ∀ (b : A) (t : C), ((b : V) + (t : V) ∈ U) ↔ Pc t := by
    intro b t
    rw [hUmem]
    constructor
    · rintro ⟨b', t', ht', h⟩
      obtain ⟨-, h2⟩ := S.add_inj b'.2 b.2 t'.2 t.2 h
      have : t' = t := Subtype.ext h2
      exact this ▸ ht'
    · intro ht
      exact ⟨b, t, ht, rfl⟩
  have hdec : ∀ v : V, ∃ (b : A) (t : C), (b : V) + (t : V) = v := by
    intro v
    obtain ⟨a, ha, e, he, rfl⟩ := S.decomp v
    exact ⟨⟨a, ha⟩, ⟨e, he⟩, rfl⟩
  have hU1 : ∀ v ∈ U, (Nat.card A - 2) * D.ncard ≤ n v := by
    intro v hv
    obtain ⟨b, t, rfl⟩ := hdec v
    rw [hn]
    exact (hcount b t).1 ((hUchar b t).mp hv)
  have hU2 : ∀ v, v ∉ U → n v < (Nat.card A - 2) * D.ncard := by
    intro v hv
    obtain ⟨b, t, rfl⟩ := hdec v
    rw [hn]
    refine (hcount b t).2 ?_
    by_contra hcon
    apply hv
    rw [hUchar]
    intro e he
    by_contra hne
    exact hcon ⟨e, he, hne⟩
  have hUinv : ∀ x ∈ X, ∀ v ∈ U, x v ∈ U := by
    intro x hx v hv
    by_contra h
    have h1 := hU2 _ h
    have h2 := hnmono x hx v
    have h3 := hU1 v hv
    omega
  rcases hX U hUinv with h | h
  · obtain ⟨a, haA, ha0, -⟩ := exists_mem_ne_two A (by omega) 0 0
    have : a ∈ U := by
      rw [hUmem]
      exact ⟨⟨a, haA⟩, 0, fun e he => by simpa using he, by simp⟩
    rw [h] at this
    exact ha0 ((Submodule.mem_bot _).mp this)
  · have hex : ∃ t₀ : C, ¬ Pc t₀ := by
      by_contra hall
      have hall' : ∀ t : C, Pc t := fun t => by
        by_contra ht
        exact hall ⟨t, ht⟩
      obtain ⟨e₀, he₀⟩ : D.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
      have hDuniv : D = Set.univ := by
        refine Set.eq_univ_of_forall fun e => ?_
        have := hall' (e₀ + e) e₀ he₀
        rwa [add_self_add] at this
      rw [hDuniv, Set.ncard_univ] at hksD
      omega
    obtain ⟨t₀, ht₀⟩ := hex
    have : ((0 : A) : V) + (t₀ : V) ∈ U := by
      rw [h]; exact Submodule.mem_top
    exact ht₀ ((hUchar 0 t₀).mp this)

theorem larger_complement_transitive (S : Setting X R A C)
    (hX : ∀ W : Submodule (ZMod 2) V, (∀ x ∈ X, ∀ v ∈ W, x v ∈ W) → W = ⊥ ∨ W = ⊤)
    (hC : 2 ≤ finrank (ZMod 2) C) (hCA : finrank (ZMod 2) C < finrank (ZMod 2) A) :
    ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃ x ∈ X, x v = w := by
  classical
  intro v w hv hw
  by_contra hno
  have hno' : ∀ x ∈ X, x v ≠ w := fun x hx h => hno ⟨x, hx, h⟩
  let Δ₁ : Set V := {d | ∃ x ∈ X, x v = d}
  let Δ₂ : Set V := {d | ∃ x ∈ X, x w = d}
  have hΔ₁x : ∀ x ∈ X, ∀ d ∈ Δ₁, x d ∈ Δ₁ := by
    rintro x hx _ ⟨y, hy, rfl⟩
    exact ⟨x * y, X.mul_mem hx hy, rfl⟩
  have hΔ₂x : ∀ x ∈ X, ∀ d ∈ Δ₂, x d ∈ Δ₂ := by
    rintro x hx _ ⟨y, hy, rfl⟩
    exact ⟨x * y, X.mul_mem hx hy, rfl⟩
  have hΔ₁0 : (0 : V) ∉ Δ₁ := by
    rintro ⟨y, hy, h⟩
    exact hv ((map_eq_zero_iff y y.injective).mp h)
  have hΔ₂0 : (0 : V) ∉ Δ₂ := by
    rintro ⟨y, hy, h⟩
    exact hw ((map_eq_zero_iff y y.injective).mp h)
  have hdisj : ∀ d, d ∈ Δ₁ → d ∉ Δ₂ := by
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    refine hno' (y⁻¹ * x) (X.mul_mem (X.inv_mem hy) hx) ?_
    show y⁻¹ (x v) = w
    rw [← hxy]
    simp
  have hne₁ : (fibre A C Δ₁).Nonempty :=
    fibre_nonempty S hX hCA hΔ₁x ⟨v, ⟨1, X.one_mem, rfl⟩, hv⟩
  have hne₂ : (fibre A C Δ₂).Nonempty :=
    fibre_nonempty S hX hCA hΔ₂x ⟨w, ⟨1, X.one_mem, rfl⟩, hw⟩
  have hfdisj : Disjoint (fibre A C Δ₁) (fibre A C Δ₂) := by
    rw [Set.disjoint_left]
    rintro e ⟨a₁, ha₁, h₁⟩ ⟨a₂, ha₂, h₂⟩
    have ha₁0 : (a₁ : V) ≠ 0 := fun h => ha₁ (Subtype.ext h)
    have ha₂0 : (a₂ : V) ≠ 0 := fun h => ha₂ (Subtype.ext h)
    obtain ⟨r, hr, hra⟩ := S.trans a₁ a₁.2 a₂ a₂.2 ha₁0 ha₂0
    have := hΔ₁x r (S.le hr) _ h₁
    rw [map_add, hra, S.fixes r hr e e.2] at this
    exact hdisj _ this h₂
  have hsum : (fibre A C Δ₁).ncard + (fibre A C Δ₂).ncard ≤ Nat.card C := by
    rw [← Set.ncard_union_eq hfdisj]
    exact Set.ncard_le_card _
  have hk₁ : 1 ≤ (fibre A C Δ₁).ncard := by
    have := (Set.ncard_pos (Set.toFinite _)).mpr hne₁
    omega
  have hk₂ : 1 ≤ (fibre A C Δ₂).ncard := by
    have := (Set.ncard_pos (Set.toFinite _)).mpr hne₂
    omega
  by_cases hle : 2 * (fibre A C Δ₁).ncard ≤ Nat.card C
  · exact key_contradiction S hX hC hCA hΔ₁x hΔ₁0 hk₁ hle
  · exact key_contradiction S hX hC hCA hΔ₂x hΔ₂0 hk₂ (by omega)

end CFSG.QuasithinUnique.ONan
