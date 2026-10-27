module

public import CFSG.Fischer.Classification.Symplectic.Config

public section

namespace CFSG.Fischer.Classification.Symplectic

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace SympConfig

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (C : SympConfig V)

@[expose] def TN : Prop :=
  ∀ x ∈ C.D, ∀ y ∈ C.D, ∀ z ∈ C.D, x ≠ y → C.b x y = 0 → C.b z x = 0 → C.b z y = 0 →
    z ≠ x → z ≠ y → x + y + z ∉ C.D

@[expose] def star (d e : V) : Set V :=
  {f | f ∈ C.D ∧ (f = d ∨ f = e ∨ (C.b f d = 1 ∧ C.b f e = 1 ∧ f ≠ d + e))}

@[expose] def IsStar (S : Set V) : Prop :=
  ∃ d ∈ C.D, ∃ e ∈ C.D, C.b d e = 1 ∧ S = C.star d e

abbrev Stars : Type _ := {S : Set V // C.IsStar S}

variable {C}

section Clique

variable {d e : V}

theorem mem_star_left (hd : d ∈ C.D) : d ∈ C.star d e :=
  ⟨hd, Or.inl rfl⟩

theorem mem_star_right (he : e ∈ C.D) : e ∈ C.star d e :=
  ⟨he, Or.inr (Or.inl rfl)⟩

theorem star_comm (d e : V) : C.star d e = C.star e d := by
  ext f
  simp only [star, Set.mem_ofPred_eq]
  constructor <;> rintro ⟨hf, h | h | ⟨h1, h2, h3⟩⟩
  · exact ⟨hf, Or.inr (Or.inl h)⟩
  · exact ⟨hf, Or.inl h⟩
  · exact ⟨hf, Or.inr (Or.inr ⟨h2, h1, by rwa [add_comm]⟩)⟩
  · exact ⟨hf, Or.inr (Or.inl h)⟩
  · exact ⟨hf, Or.inl h⟩
  · exact ⟨hf, Or.inr (Or.inr ⟨h2, h1, by rwa [add_comm]⟩)⟩

theorem ne_of_b_eq_one {u v : V} (h : C.b u v = 1) : u ≠ v := by
  rintro rfl
  rw [C.self_eq_zero] at h
  exact zero_ne_one h

theorem isStar_star (hd : d ∈ C.D) (he : e ∈ C.D) (hde : C.b d e = 1) : C.IsStar (C.star d e) :=
  ⟨d, hd, e, he, hde, rfl⟩

theorem b_add_right_eq_one (hde : C.b d e = 1) : C.b d (d + e) = 1 := by
  rw [C.b_add_right, C.self_eq_zero, zero_add, hde]

theorem b_eq_one_of_mem_star (hTN : C.TN) (hd : d ∈ C.D) (he : e ∈ C.D) (hde : C.b d e = 1)
    {f g : V} (hf : f ∈ C.star d e) (hg : g ∈ C.star d e) (hfg : f ≠ g) : C.b f g = 1 := by
  obtain ⟨hfD, hf⟩ := hf
  obtain ⟨hgD, hg⟩ := hg
  have hed : C.b e d = 1 := by rw [C.comm]; exact hde
  rcases hf with hf | hf | ⟨hfd, hfe, hfde⟩ <;> rcases hg with hg | hg | ⟨hgd, hge, hgde⟩
  · exact absurd (hf.trans hg.symm) hfg
  · rw [hf, hg]; exact hde
  · rw [hf, C.comm]; exact hgd
  · rw [hf, hg]; exact hed
  · exact absurd (hf.trans hg.symm) hfg
  · rw [hf, C.comm]; exact hge
  · rw [hg]; exact hfd
  · rw [hg]; exact hfe
  · by_contra h0
    have h0' : C.b f g = 0 := zmod_two_eq_zero_of_ne_one h0
    refine hTN f hfD g hgD (d + e) (C.add_mem d hd e he hde) hfg h0' ?_ ?_ (Ne.symm hfde)
      (Ne.symm hgde) ?_
    · rw [C.b_add_left, C.comm d f, hfd, C.comm e f, hfe, zmod_two_one_add_one]
    · rw [C.b_add_left, C.comm d g, hgd, C.comm e g, hge, zmod_two_one_add_one]
    · have h1 : f + d ∈ C.D := C.add_mem f hfD d hd hfd
      have h2 : g + e ∈ C.D := C.add_mem g hgD e he hge
      have hb : C.b (f + d) (g + e) = 1 := by
        rw [C.b_add_left, C.b_add_right, C.b_add_right, h0', hfe, C.comm d g, hgd, hde]
        rfl
      have := C.add_mem _ h1 _ h2 hb
      rwa [show f + d + (g + e) = f + g + (d + e) by zmod_two_abel] at this

theorem star_subset_star (hTN : C.TN) (hd : d ∈ C.D) (he : e ∈ C.D) (hde : C.b d e = 1)
    {f : V} (hf : f ∈ C.star d e) (hfd : f ≠ d) : C.star d e ⊆ C.star d f := by
  intro g hg
  refine ⟨hg.1, ?_⟩
  by_cases hgd : g = d
  · exact Or.inl hgd
  by_cases hgf : g = f
  · exact Or.inr (Or.inl hgf)
  right
  right
  refine ⟨?_, b_eq_one_of_mem_star hTN hd he hde hg hf hgf, ?_⟩
  · rw [C.comm]
    exact b_eq_one_of_mem_star hTN hd he hde (mem_star_left hd) hg (Ne.symm hgd)
  · intro hg'
    by_cases hge : g = e
    ·
      have hfde : f = d + e := by rw [← hge, hg']; zmod_two_abel
      rcases hf.2 with h | h | ⟨-, -, h⟩
      · exact hfd h
      · exact hgf (hge.trans h.symm)
      · exact h hfde
    by_cases hfe : f = e
    · rcases hg.2 with h | h | ⟨-, -, h⟩
      · exact hgd h
      · exact hge h
      · exact h (by rw [hg', hfe])
    · have h1 : C.b g e = 1 := b_eq_one_of_mem_star hTN hd he hde hg (mem_star_right he) hge
      have h2 : C.b f e = 1 := b_eq_one_of_mem_star hTN hd he hde hf (mem_star_right he) hfe
      rw [hg', C.b_add_left, hde, h2, zmod_two_one_add_one] at h1
      exact zero_ne_one h1

theorem star_eq_of_mem (hTN : C.TN) (hd : d ∈ C.D) (he : e ∈ C.D) (hde : C.b d e = 1) {f : V}
    (hf : f ∈ C.star d e) (hfd : f ≠ d) : C.star d f = C.star d e := by
  have hdf : C.b d f = 1 := b_eq_one_of_mem_star hTN hd he hde (mem_star_left hd) hf (Ne.symm hfd)
  have hed : e ≠ d := (ne_of_b_eq_one hde).symm
  have hef : e ∈ C.star d f := by
    refine ⟨he, ?_⟩
    by_cases hef : e = f
    · exact Or.inr (Or.inl hef)
    right
    right
    refine ⟨by rw [C.comm]; exact hde, b_eq_one_of_mem_star hTN hd he hde (mem_star_right he)
      hf hef, fun h => ?_⟩
    rcases hf.2 with h' | h' | ⟨-, -, h'⟩
    · exact hfd h'
    · exact hef h'.symm
    · exact h' (by rw [h]; zmod_two_abel)
  exact Set.Subset.antisymm (star_subset_star hTN hd hf.1 hdf hef hed)
    (star_subset_star hTN hd he hde hf hfd)

theorem star_eq_star (hTN : C.TN) (hd : d ∈ C.D) (he : e ∈ C.D) (hde : C.b d e = 1) {f g : V}
    (hf : f ∈ C.star d e) (hg : g ∈ C.star d e) (hfg : f ≠ g) : C.star f g = C.star d e := by
  by_cases hfd : f = d
  · subst hfd
    exact star_eq_of_mem hTN hd he hde hg (Ne.symm hfg)
  · have h1 : C.star d f = C.star d e := star_eq_of_mem hTN hd he hde hf hfd
    have hdf : C.b d f = 1 :=
      b_eq_one_of_mem_star hTN hd he hde (mem_star_left hd) hf (Ne.symm hfd)
    have hfd' : C.b f d = 1 := by rw [C.comm]; exact hdf
    have hg' : g ∈ C.star f d := by rw [star_comm, h1]; exact hg
    rw [star_eq_of_mem hTN hf.1 hd hfd' hg' (Ne.symm hfg), star_comm, h1]

end Clique

section Outside

variable {d e : V}

theorem exists_eq_add_of_b_eq_one (hTN : C.TN) (hd : d ∈ C.D) (he : e ∈ C.D)
    (hde : C.b d e = 1) {a f : V} (ha : a ∈ C.star d e) (hfD : f ∈ C.D)
    (hf : f ∉ C.star d e) (hfa : C.b f a = 1) : ∃ c ∈ C.star d e, a ≠ c ∧ f = a + c := by
  obtain ⟨e', he'S, he'a, hS⟩ : ∃ e' ∈ C.star d e, e' ≠ a ∧ C.star a e' = C.star d e := by
    by_cases had : a = d
    · subst had
      exact ⟨e, mem_star_right he, (ne_of_b_eq_one hde).symm, rfl⟩
    · exact ⟨d, mem_star_left hd, Ne.symm had,
        star_eq_star hTN hd he hde ha (mem_star_left hd) had⟩
  have hae' : C.b a e' = 1 := b_eq_one_of_mem_star hTN hd he hde ha he'S (Ne.symm he'a)
  rw [← hS] at hf ⊢
  have haf : C.b a f = 1 := by rw [C.comm]; exact hfa
  rcases C.b_cases f e' with h | h
  ·
    refine ⟨a + f, ⟨C.add_mem a ha.1 f hfD haf, Or.inr (Or.inr ⟨?_, ?_, ?_⟩)⟩, ?_, by zmod_two_abel⟩
    · rw [C.b_add_left, C.self_eq_zero, zero_add, hfa]
    · rw [C.b_add_left, hae', h, add_zero]
    · intro h'
      apply hf
      have : f = e' := by
        have := congrArg (a + ·) h'
        simpa only [zmod_two_add_add_self] using this
      rw [this]
      exact mem_star_right he'S.1
    · intro h'
      have : f = 0 := by
        have := congrArg (a + ·) h'
        simpa only [zmod_two_add_self, zmod_two_add_add_self] using this.symm
      exact C.zero_notMem (this ▸ hfD)
  ·
    refine ⟨e', mem_star_right he'S.1, Ne.symm he'a, ?_⟩
    by_contra hne
    exact hf ⟨hfD, Or.inr (Or.inr ⟨hfa, h, hne⟩)⟩

theorem exists_eq_add_of_notMem (hTN : C.TN) (hd : d ∈ C.D) (he : e ∈ C.D) (hde : C.b d e = 1)
    {f : V} (hfD : f ∈ C.D) (hf : f ∉ C.star d e) :
    ∃ a ∈ C.star d e, ∃ c ∈ C.star d e, a ≠ c ∧ f = a + c := by
  obtain ⟨a, ha, hfa⟩ : ∃ a ∈ C.star d e, C.b f a = 1 := by
    by_contra h
    push Not at h
    have h0 : ∀ a ∈ C.star d e, C.b f a = 0 := fun a ha => zmod_two_eq_zero_of_ne_one (h a ha)
    have hfd : d ≠ f := fun h' => hf (h' ▸ mem_star_left hd)
    obtain ⟨u, hu, hud, huf⟩ := C.exists_common hd hfD hfd
      (by rw [C.comm]; exact h0 d (mem_star_left hd))
    have huS : u ∉ C.star d e := fun h' => by
      rw [C.comm, h0 u h'] at huf
      exact zero_ne_one huf
    obtain ⟨c, hc, -, hu'⟩ := exists_eq_add_of_b_eq_one hTN hd he hde (mem_star_left hd) hu huS hud
    rw [hu', C.comm, C.b_add_right, h0 d (mem_star_left hd), h0 c hc, add_zero] at huf
    exact zero_ne_one huf
  obtain ⟨c, hc, hac, hfac⟩ := exists_eq_add_of_b_eq_one hTN hd he hde ha hfD hf hfa
  exact ⟨a, ha, c, hc, hac, hfac⟩

end Outside

section Through

variable {d e : V}

theorem add_mem_star_two (hd : d ∈ C.D) (he : e ∈ C.D) (hde : C.b d e = 1) :
    d + e ∈ C.star d (d + e) :=
  mem_star_right (C.add_mem d hd e he hde)

theorem add_notMem_star (hd : d ∈ C.D) (he : e ∈ C.D) : d + e ∉ C.star d e := by
  rintro ⟨-, h | h | ⟨-, -, h⟩⟩
  · apply C.ne_zero_of_mem he
    simpa using congrArg (d + ·) h
  · apply C.ne_zero_of_mem hd
    simpa using congrArg (· + e) h
  · exact h rfl

theorem star_ne_star (hd : d ∈ C.D) (he : e ∈ C.D) (hde : C.b d e = 1) :
    C.star d e ≠ C.star d (d + e) := fun h =>
  add_notMem_star hd he (h ▸ add_mem_star_two hd he hde)

theorem eq_or_eq_of_mem (hTN : C.TN) (hd : d ∈ C.D) (he : e ∈ C.D) (hde : C.b d e = 1)
    {S : Set V} (hS : C.IsStar S) (hdS : d ∈ S) : S = C.star d e ∨ S = C.star d (d + e) := by
  obtain ⟨a, ha, c, hc, hac, rfl⟩ := hS
  obtain ⟨f, hfS, hfd⟩ : ∃ f ∈ C.star a c, f ≠ d := by
    by_cases had : a = d
    · exact ⟨c, mem_star_right hc, fun h => ne_of_b_eq_one hac (had.trans h.symm)⟩
    · exact ⟨a, mem_star_left ha, had⟩
  have hSf : C.star d f = C.star a c := star_eq_star hTN ha hc hac hdS hfS (Ne.symm hfd)
  have hdf : C.b d f = 1 := b_eq_one_of_mem_star hTN ha hc hac hdS hfS (Ne.symm hfd)
  rw [← hSf]
  by_cases hfe : f ∈ C.star d e
  · exact Or.inl (star_eq_of_mem hTN hd he hde hfe hfd)
  · right
    have hde' : C.b d (d + e) = 1 := b_add_right_eq_one hde
    refine star_eq_of_mem hTN hd (C.add_mem d hd e he hde) hde' ⟨hfS.1, ?_⟩ hfd
    have hfd' : C.b f d = 1 := by rw [C.comm]; exact hdf
    by_cases hf1 : f = d + e
    · exact Or.inr (Or.inl hf1)
    right
    right
    have hfe' : f ≠ e := fun h => hfe (by rw [h]; exact mem_star_right he)
    have hbfe : C.b f e = 0 := by
      rcases C.b_cases f e with h | h
      · exact h
      · exact absurd ⟨hfS.1, Or.inr (Or.inr ⟨hfd', h, hf1⟩)⟩ hfe
    refine ⟨hfd', by rw [C.b_add_right, hfd', hbfe, add_zero], ?_⟩
    rw [zmod_two_add_add_self]
    exact hfe'

theorem eq_or_eq_of_mem_of_mem (hTN : C.TN) {x : V} (hx : x ∈ C.D) {S₁ S₂ S : Set V}
    (h₁ : C.IsStar S₁) (h₂ : C.IsStar S₂) (hS : C.IsStar S) (hne : S₁ ≠ S₂) (hx₁ : x ∈ S₁)
    (hx₂ : x ∈ S₂) (hxS : x ∈ S) : S = S₁ ∨ S = S₂ := by
  obtain ⟨e, he, hxe⟩ := C.exists_mem_b_eq_one (C.ne_zero_of_mem hx)
  have hxe' : C.b x e = 1 := by rw [C.comm]; exact hxe
  rcases eq_or_eq_of_mem hTN hx he hxe' h₁ hx₁ with r₁ | r₁ <;>
    rcases eq_or_eq_of_mem hTN hx he hxe' h₂ hx₂ with r₂ | r₂ <;>
    rcases eq_or_eq_of_mem hTN hx he hxe' hS hxS with r | r
  all_goals first
    | exact absurd (r₁.trans r₂.symm) hne
    | exact Or.inl (r.trans r₁.symm)
    | exact Or.inr (r.trans r₂.symm)

theorem eq_of_mem_of_mem (hTN : C.TN) {S S' : Set V} (hS : C.IsStar S) (hS' : C.IsStar S')
    (hne : S ≠ S') {f g : V} (hf : f ∈ S) (hf' : f ∈ S') (hg : g ∈ S) (hg' : g ∈ S') :
    f = g := by
  by_contra hfg
  obtain ⟨d, hd, e, he, hde, rfl⟩ := hS
  obtain ⟨d', hd', e', he', hde', rfl⟩ := hS'
  exact hne ((star_eq_star hTN hd he hde hf hg hfg).symm.trans
    (star_eq_star hTN hd' he' hde' hf' hg' hfg))

theorem exists_mem_inter (hTN : C.TN) {S S' : Set V} (hS : C.IsStar S) (hS' : C.IsStar S')
    (hne : S ≠ S') : ∃ f, f ∈ S ∧ f ∈ S' := by
  obtain ⟨d, hd, e, he, hde, rfl⟩ := hS
  obtain ⟨d', hd', e', he', hde', rfl⟩ := hS'
  obtain ⟨f, hfS', hfS⟩ : ∃ f ∈ C.star d' e', f ∉ C.star d e := by
    by_contra h
    push Not at h
    exact hne (star_eq_star hTN hd he hde (h d' (mem_star_left hd')) (h e' (mem_star_right he'))
      (ne_of_b_eq_one hde')).symm
  obtain ⟨a, ha, c, hc, hac, rfl⟩ := exists_eq_add_of_notMem hTN hd he hde hfS'.1 hfS
  have hca : C.b c a = 1 := b_eq_one_of_mem_star hTN hd he hde hc ha (Ne.symm hac)
  have hfa : C.b (a + c) a = 1 := by rw [C.b_add_left, C.self_eq_zero, zero_add, hca]
  rcases eq_or_eq_of_mem hTN hfS'.1 ha.1 hfa ⟨d', hd', e', he', hde', rfl⟩ hfS' with h | h
  · exact ⟨a, ha, h ▸ mem_star_right ha.1⟩
  · refine ⟨c, hc, ?_⟩
    rw [h, show a + c + a = c by zmod_two_abel]
    exact mem_star_right hc.1

end Through

section Action

theorem image_star (f : V ≃ₗ[ZMod 2] V) (hf : ∀ u v, C.b (f u) (f v) = C.b u v)
    (hD : ∀ u, f u ∈ C.D ↔ u ∈ C.D) (d e : V) : f '' C.star d e = C.star (f d) (f e) := by
  ext g
  constructor
  · rintro ⟨g₀, ⟨hg₀, h⟩, rfl⟩
    refine ⟨(hD g₀).2 hg₀, ?_⟩
    rcases h with rfl | rfl | ⟨h1, h2, h3⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · refine Or.inr (Or.inr ⟨by rw [hf, h1], by rw [hf, h2], fun h => h3 ?_⟩)
      rw [← map_add] at h
      exact f.injective h
  · rintro ⟨hg, h⟩
    refine ⟨f.symm g, ⟨(hD _).1 (by rw [LinearEquiv.apply_symm_apply]; exact hg), ?_⟩,
      LinearEquiv.apply_symm_apply f g⟩
    rcases h with rfl | rfl | ⟨h1, h2, h3⟩
    · exact Or.inl (LinearEquiv.symm_apply_apply f d)
    · exact Or.inr (Or.inl (LinearEquiv.symm_apply_apply f e))
    · refine Or.inr (Or.inr ⟨?_, ?_, fun h => h3 ?_⟩)
      · rw [← hf, LinearEquiv.apply_symm_apply, h1]
      · rw [← hf, LinearEquiv.apply_symm_apply, h2]
      · rw [← map_add, ← h, LinearEquiv.apply_symm_apply]

theorem isStar_image (f : V ≃ₗ[ZMod 2] V) (hf : ∀ u v, C.b (f u) (f v) = C.b u v)
    (hD : ∀ u, f u ∈ C.D ↔ u ∈ C.D) {S : Set V} (hS : C.IsStar S) : C.IsStar (f '' S) := by
  obtain ⟨d, hd, e, he, hde, rfl⟩ := hS
  exact ⟨f d, (hD d).2 hd, f e, (hD e).2 he, by rw [hf, hde], image_star f hf hD d e⟩

theorem transvection_isometry {t : V ≃ₗ[ZMod 2] V} {d : V} (ht : ∀ v, t v = v + C.b v d • d)
    (u v : V) : C.b (t u) (t v) = C.b u v := by
  rw [ht, ht]
  have e1 : C.b (u + C.b u d • d) (v + C.b v d • d) = C.b u v + C.b v d * C.b u d +
      C.b u d * C.b d v + C.b u d * (C.b v d * C.b d d) := by
    simp only [C.b_add_left, C.b_add_right, map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  rw [e1, C.self_eq_zero, C.comm d v]
  generalize C.b u v = a
  generalize C.b u d = x
  generalize C.b v d = y
  revert a x y
  decide

theorem transvection_mem_iff {t : V ≃ₗ[ZMod 2] V} {d : V} (hdD : d ∈ C.D)
    (ht : ∀ v, t v = v + C.b v d • d) (u : V) : t u ∈ C.D ↔ u ∈ C.D := by
  rw [ht]
  rcases C.b_cases u d with h | h
  · rw [h, zero_smul, add_zero]
  · rw [h, one_smul]
    constructor
    · intro hu
      have := C.add_mem _ hu d hdD (by rw [C.b_add_left, h, C.self_eq_zero, add_zero])
      rwa [add_assoc, zmod_two_add_self, add_zero] at this
    · intro hu
      exact C.add_mem u hu d hdD h

variable {d e : V}

theorem image_star_left {t : V ≃ₗ[ZMod 2] V} (hd : d ∈ C.D) (ht : ∀ v, t v = v + C.b v d • d)
    (hde : C.b d e = 1) : t '' C.star d e = C.star d (d + e) := by
  rw [image_star t (transvection_isometry ht) (transvection_mem_iff hd ht), ht, ht,
    C.self_eq_zero, zero_smul, add_zero, C.comm e d, hde, one_smul, add_comm e d]

theorem image_star_right {t : V ≃ₗ[ZMod 2] V} (hd : d ∈ C.D) (ht : ∀ v, t v = v + C.b v d • d)
    (hde : C.b d e = 1) : t '' C.star d (d + e) = C.star d e := by
  rw [image_star t (transvection_isometry ht) (transvection_mem_iff hd ht), ht, ht,
    C.self_eq_zero, zero_smul, add_zero, C.b_add_left, C.self_eq_zero, zero_add, C.comm e d,
    hde, one_smul, show d + e + d = e by zmod_two_abel]

theorem image_star_of_notMem (hTN : C.TN) {t : V ≃ₗ[ZMod 2] V} (hd : d ∈ C.D)
    (ht : ∀ v, t v = v + C.b v d • d) {S : Set V} (hS : C.IsStar S) (hdS : d ∉ S) : t '' S = S := by
  obtain ⟨a₀, ha₀, c₀, hc₀, hac₀, rfl⟩ := hS
  obtain ⟨a, ha, c, hc, hac, rfl⟩ := exists_eq_add_of_notMem hTN ha₀ hc₀ hac₀ hd hdS
  have hb : C.b a c = 1 := b_eq_one_of_mem_star hTN ha₀ hc₀ hac₀ ha hc hac
  rw [← star_eq_star hTN ha₀ hc₀ hac₀ ha hc hac,
    image_star t (transvection_isometry ht) (transvection_mem_iff hd ht), ht, ht,
    C.b_add_right, C.self_eq_zero, zero_add, hb, one_smul, C.b_add_right, C.comm c a, hb,
    C.self_eq_zero, add_zero, one_smul, zmod_two_add_add_self,
    show c + (a + c) = a by zmod_two_abel, star_comm]

end Action

section Card

theorem three_le_card [Fintype C.Stars] {d e : V} (hd : d ∈ C.D) (he : e ∈ C.D)
    (hde : C.b d e = 1) : 3 ≤ Fintype.card C.Stars := by
  classical
  have hde' := b_add_right_eq_one hde
  have hed : C.b e (d + e) = 1 := by
    rw [C.b_add_right, C.comm e d, hde, C.self_eq_zero, add_zero]
  have hdeD : d + e ∈ C.D := C.add_mem d hd e he hde
  let S₁ : C.Stars := ⟨_, isStar_star hd he hde⟩
  let S₂ : C.Stars := ⟨_, isStar_star hd hdeD hde'⟩
  let S₃ : C.Stars := ⟨_, isStar_star he hdeD hed⟩
  have h12 : S₁ ≠ S₂ := fun h => star_ne_star hd he hde (congrArg Subtype.val h)
  have h13 : S₁ ≠ S₃ := by
    intro h
    have h' : C.star d e = C.star e (d + e) := congrArg Subtype.val h
    exact add_notMem_star hd he (h' ▸ mem_star_right hdeD)
  have h23 : S₂ ≠ S₃ := by
    intro h
    have h' : C.star d (d + e) = C.star e (d + e) := congrArg Subtype.val h
    have : e ∈ C.star d (d + e) := h' ▸ mem_star_left he
    rcases this.2 with h' | h' | ⟨-, -, h'⟩
    · exact ne_of_b_eq_one hde h'.symm
    · apply C.ne_zero_of_mem hd
      simpa using congrArg (· + e) h'.symm
    · exact h' (by zmod_two_abel)
  have hcard : ({S₁, S₂, S₃} : Finset C.Stars).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [h12, h13]), Finset.card_pair h23]
  rw [← hcard]
  exact Finset.card_le_univ _

theorem card_ne_four [Fintype C.Stars] (hTN : C.TN) : Fintype.card C.Stars ≠ 4 := by
  classical
  intro h4
  let T : Fin 4 → C.Stars := (Fintype.equivFinOfCardEq h4).symm
  have hT : ∀ S : C.Stars, ∃ i, S = T i := fun S =>
    ⟨Fintype.equivFinOfCardEq h4 S, ((Fintype.equivFinOfCardEq h4).symm_apply_apply S).symm⟩
  have hTinj : Function.Injective T := (Fintype.equivFinOfCardEq h4).symm.injective
  have hTne : ∀ i j, i ≠ j → (T i).1 ≠ (T j).1 := fun i j hij h =>
    hij (hTinj (Subtype.ext h))
  obtain ⟨x, hx₀, hx₁⟩ := exists_mem_inter hTN (T 0).2 (T 1).2 (hTne 0 1 (by decide))
  obtain ⟨y, hy₂, hy₃⟩ := exists_mem_inter hTN (T 2).2 (T 3).2 (hTne 2 3 (by decide))
  have hxD : x ∈ C.D := (T 0).2.choose_spec.2.choose_spec.2.2 ▸ hx₀ |>.1
  have hyD : y ∈ C.D := (T 2).2.choose_spec.2.choose_spec.2.2 ▸ hy₂ |>.1
  have hxS : ∀ i, x ∈ (T i).1 → i = 0 ∨ i = 1 := by
    intro i hi
    rcases eq_or_eq_of_mem_of_mem hTN hxD (T 0).2 (T 1).2 (T i).2 (hTne 0 1 (by decide)) hx₀ hx₁
      hi with h | h
    · exact Or.inl (hTinj (Subtype.ext h))
    · exact Or.inr (hTinj (Subtype.ext h))
  have hyS : ∀ i, y ∈ (T i).1 → i = 2 ∨ i = 3 := by
    intro i hi
    rcases eq_or_eq_of_mem_of_mem hTN hyD (T 2).2 (T 3).2 (T i).2 (hTne 2 3 (by decide)) hy₂ hy₃
      hi with h | h
    · exact Or.inl (hTinj (Subtype.ext h))
    · exact Or.inr (hTinj (Subtype.ext h))
  have horth : ∀ u ∈ C.D, ∀ v ∈ C.D, C.b u v = 1 → ∃ i, u ∈ (T i).1 ∧ v ∈ (T i).1 := by
    intro u hu v hv huv
    obtain ⟨i, hi⟩ := hT ⟨_, isStar_star hu hv huv⟩
    exact ⟨i, hi ▸ mem_star_left hu, hi ▸ mem_star_right hv⟩
  have hxy : C.b x y = 0 := by
    rcases C.b_cases x y with h | h
    · exact h
    · obtain ⟨i, hxi, hyi⟩ := horth x hxD y hyD h
      rcases hxS i hxi with rfl | rfl <;> rcases hyS _ hyi with h' | h' <;>
        exact absurd h' (by decide)
  have hshare : ∀ f ∈ C.D, f ≠ x → f ≠ y → C.b f x = 1 ∧ C.b f y = 1 := by
    intro f hf hfx hfy
    obtain ⟨e, he, hfe⟩ := C.exists_mem_b_eq_one (C.ne_zero_of_mem hf)
    have hfe' : C.b f e = 1 := by rw [C.comm]; exact hfe
    obtain ⟨i, hi⟩ := hT ⟨_, isStar_star hf he hfe'⟩
    obtain ⟨j, hj⟩ := hT ⟨_, isStar_star hf (C.add_mem f hf e he hfe') (b_add_right_eq_one hfe')⟩
    have hfi : f ∈ (T i).1 := hi ▸ mem_star_left hf
    have hfj : f ∈ (T j).1 := hj ▸ mem_star_left hf
    have hij : i ≠ j := fun h => star_ne_star hf he hfe'
      ((congrArg Subtype.val hi).trans ((congrArg (fun k => (T k).1) h).trans
        (congrArg Subtype.val hj).symm))
    have hpair : ∀ k, f ∈ (T k).1 → ∀ z ∈ (T k).1, z ≠ f → C.b f z = 1 := by
      intro k hk z hz hzf
      obtain ⟨a, ha, c, hc, hac, hS⟩ := (T k).2
      rw [hS] at hk hz
      exact b_eq_one_of_mem_star hTN ha hc hac hk hz (Ne.symm hzf)
    have hx01 : ∀ k, k = 0 ∨ k = 1 → x ∈ (T k).1 := by
      rintro k (rfl | rfl)
      · exact hx₀
      · exact hx₁
    have hy23 : ∀ k, k = 2 ∨ k = 3 → y ∈ (T k).1 := by
      rintro k (rfl | rfl)
      · exact hy₂
      · exact hy₃
    have hnx : ¬ ((i = 0 ∨ i = 1) ∧ (j = 0 ∨ j = 1)) := by
      rintro ⟨hi', hj'⟩
      apply hfx
      have h01 : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by omega
      rcases h01 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact eq_of_mem_of_mem hTN (T 0).2 (T 1).2 (hTne 0 1 (by decide)) hfi hfj hx₀ hx₁
      · exact eq_of_mem_of_mem hTN (T 0).2 (T 1).2 (hTne 0 1 (by decide)) hfj hfi hx₀ hx₁
    have hny : ¬ ((i = 2 ∨ i = 3) ∧ (j = 2 ∨ j = 3)) := by
      rintro ⟨hi', hj'⟩
      apply hfy
      have h23 : (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) := by omega
      rcases h23 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact eq_of_mem_of_mem hTN (T 2).2 (T 3).2 (hTne 2 3 (by decide)) hfi hfj hy₂ hy₃
      · exact eq_of_mem_of_mem hTN (T 2).2 (T 3).2 (hTne 2 3 (by decide)) hfj hfi hy₂ hy₃
    have hcases : ((i = 0 ∨ i = 1) ∧ (j = 2 ∨ j = 3)) ∨ ((i = 2 ∨ i = 3) ∧ (j = 0 ∨ j = 1)) := by
      omega
    rcases hcases with ⟨hi', hj'⟩ | ⟨hi', hj'⟩
    · exact ⟨hpair i hfi x (hx01 i hi') (Ne.symm hfx), hpair j hfj y (hy23 j hj') (Ne.symm hfy)⟩
    · exact ⟨hpair j hfj x (hx01 j hj') (Ne.symm hfx), hpair i hfi y (hy23 i hi') (Ne.symm hfy)⟩
  have hzero : x + y = 0 := C.eq_zero_of_forall_mem fun f hf => by
    by_cases hfx : f = x
    · rw [hfx, C.b_add_right, C.self_eq_zero, zero_add, hxy]
    by_cases hfy : f = y
    · rw [hfy, C.b_add_right, C.self_eq_zero, add_zero, C.comm, hxy]
    obtain ⟨h1, h2⟩ := hshare f hf hfx hfy
    rw [C.b_add_right, h1, h2, zmod_two_one_add_one]
  have hxy' : x = y := zmod_two_eq_of_add_eq_zero hzero
  rcases hxS 2 (hxy' ▸ hy₂) with h | h <;> exact absurd h (by decide)

end Card

section Perm

variable {G : Type*} [Group G]

theorem inv_apply_apply (τ : G →* V ≃ₗ[ZMod 2] V) (g : G) (x : V) : τ g⁻¹ (τ g x) = x := by
  rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

theorem apply_inv_apply (τ : G →* V ≃ₗ[ZMod 2] V) (g : G) (x : V) : τ g (τ g⁻¹ x) = x := by
  rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

@[expose] noncomputable def starPerm (τ : G →* V ≃ₗ[ZMod 2] V)
    (hiso : ∀ g u v, C.b (τ g u) (τ g v) = C.b u v) (hD : ∀ g u, τ g u ∈ C.D ↔ u ∈ C.D) :
    G →* Equiv.Perm C.Stars where
  toFun g :=
    { toFun := fun S => ⟨τ g '' S.1, isStar_image (τ g) (hiso g) (hD g) S.2⟩
      invFun := fun S => ⟨τ g⁻¹ '' S.1, isStar_image (τ g⁻¹) (hiso g⁻¹) (hD g⁻¹) S.2⟩
      left_inv := fun S => Subtype.ext (by
        simp only [Set.image_image, inv_apply_apply, Set.image_id'])
      right_inv := fun S => Subtype.ext (by
        simp only [Set.image_image, apply_inv_apply, Set.image_id']) }
  map_one' := Equiv.ext fun S => Subtype.ext (by
    show τ 1 '' S.1 = S.1
    rw [map_one]
    exact Set.image_id S.1)
  map_mul' g h := Equiv.ext fun S => Subtype.ext (by
    show τ (g * h) '' S.1 = τ g '' (τ h '' S.1)
    rw [map_mul, Set.image_image]
    rfl)

theorem starPerm_apply (τ : G →* V ≃ₗ[ZMod 2] V) (hiso : ∀ g u v, C.b (τ g u) (τ g v) = C.b u v)
    (hD : ∀ g u, τ g u ∈ C.D ↔ u ∈ C.D) (g : G) (S : C.Stars) :
    (starPerm τ hiso hD g S).1 = τ g '' S.1 :=
  rfl

theorem starPerm_eq_swap (hTN : C.TN) (τ : G →* V ≃ₗ[ZMod 2] V)
    (hiso : ∀ g u v, C.b (τ g u) (τ g v) = C.b u v) (hD : ∀ g u, τ g u ∈ C.D ↔ u ∈ C.D) {g : G}
    {d : V} (hdD : d ∈ C.D) (hg : ∀ v, τ g v = v + C.b v d • d) {S S' : C.Stars} (hne : S ≠ S')
    (hdS : d ∈ S.1) (hdS' : d ∈ S'.1) : starPerm τ hiso hD g = Equiv.swap S S' := by
  classical
  obtain ⟨f, hf, hdf, hSf, hS'f⟩ : ∃ f ∈ C.D, C.b d f = 1 ∧ S.1 = C.star d f ∧
      S'.1 = C.star d (d + f) := by
    obtain ⟨a, ha, c, hc, hac, hS⟩ := S.2
    obtain ⟨f, hfS, hfd⟩ : ∃ f ∈ S.1, f ≠ d := by
      by_cases had : a = d
      · exact ⟨c, hS ▸ mem_star_right hc, fun h => ne_of_b_eq_one hac (had.trans h.symm)⟩
      · exact ⟨a, hS ▸ mem_star_left ha, had⟩
    rw [hS] at hfS hdS
    have hSf : C.star d f = C.star a c := star_eq_star hTN ha hc hac hdS hfS (Ne.symm hfd)
    have hdf : C.b d f = 1 := b_eq_one_of_mem_star hTN ha hc hac hdS hfS (Ne.symm hfd)
    refine ⟨f, hfS.1, hdf, hS.trans hSf.symm, ?_⟩
    rcases eq_or_eq_of_mem hTN hdD hfS.1 hdf S'.2 hdS' with h | h
    · exact absurd (Subtype.ext (h.trans (hSf.trans hS.symm))).symm hne
    · exact h
  refine Equiv.ext fun T => Subtype.ext ?_
  rw [starPerm_apply]
  by_cases hTS : T = S
  · rw [hTS, Equiv.swap_apply_left, hSf, hS'f, image_star_left hdD hg hdf]
  by_cases hTS' : T = S'
  · rw [hTS', Equiv.swap_apply_right, hSf, hS'f, image_star_right hdD hg hdf]
  rw [Equiv.swap_apply_of_ne_of_ne hTS hTS']
  refine image_star_of_notMem hTN hdD hg T.2 fun hdT => ?_
  rcases eq_or_eq_of_mem_of_mem hTN hdD S.2 S'.2 T.2 (fun h => hne (Subtype.ext h)) hdS hdS'
    hdT with h | h
  · exact hTS (Subtype.ext h)
  · exact hTS' (Subtype.ext h)

theorem isSwap_permCongr_iff {α β : Type*} [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (σ : Equiv.Perm α) : (e.permCongr σ).IsSwap ↔ σ.IsSwap := by
  constructor
  · rintro ⟨x, y, hxy, h⟩
    refine ⟨e.symm x, e.symm y, fun h' => hxy (e.symm.injective h'), ?_⟩
    have : σ = e.symm.permCongr (e.permCongr σ) := by
      ext a
      simp [Equiv.permCongr_apply]
    rw [this, h, Equiv.permCongr_def, Equiv.symm_trans_swap_trans]
  · rintro ⟨x, y, hxy, rfl⟩
    exact ⟨e x, e y, fun h' => hxy (e.injective h'), by
      rw [Equiv.permCongr_def, Equiv.symm_trans_swap_trans]⟩

theorem exists_mulEquiv_perm [Finite V] (hTN : C.TN) (τ : G →* V ≃ₗ[ZMod 2] V)
    (hinj : Function.Injective τ) (hiso : ∀ g u v, C.b (τ g u) (τ g v) = C.b u v)
    (hD : ∀ g u, τ g u ∈ C.D ↔ u ∈ C.D) (E' : Set G) (δ : E' → V) (hδD : ∀ d, δ d ∈ C.D)
    (hδ : ∀ (d : E') v, τ d v = v + C.b v (δ d) • δ d) (hδs : ∀ v ∈ C.D, ∃ d, δ d = v)
    (hDne : C.D.Nonempty) :
    ∃ m : ℕ, (m = 3 ∨ 5 ≤ m) ∧ ∃ φ : G ≃* Equiv.Perm (Fin m), ∀ g, g ∈ E' ↔ (φ g).IsSwap := by
  classical
  have : Fintype C.Stars := Fintype.ofFinite _
  set π := starPerm τ hiso hD
  have htwo : ∀ v ∈ C.D, ∃ S S' : C.Stars, S ≠ S' ∧ v ∈ S.1 ∧ v ∈ S'.1 := by
    intro v hv
    obtain ⟨e, he, hve⟩ := C.exists_mem_b_eq_one (C.ne_zero_of_mem hv)
    have hve' : C.b v e = 1 := by rw [C.comm]; exact hve
    exact ⟨⟨_, isStar_star hv he hve'⟩, ⟨_, isStar_star hv (C.add_mem v hv e he hve')
      (b_add_right_eq_one hve')⟩, fun h => star_ne_star hv he hve' (congrArg Subtype.val h),
      mem_star_left hv, mem_star_left hv⟩
  have hπinj : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    rw [Subgroup.mem_bot]
    apply hinj
    rw [map_one]
    have hfix : ∀ v ∈ C.D, τ g v = v := by
      intro v hv
      obtain ⟨S, S', hne, hvS, hvS'⟩ := htwo v hv
      have h1 : τ g v ∈ S.1 := by
        have := congrArg Subtype.val (Equiv.ext_iff.1 hg S)
        rw [starPerm_apply] at this
        exact this ▸ ⟨v, hvS, rfl⟩
      have h2 : τ g v ∈ S'.1 := by
        have := congrArg Subtype.val (Equiv.ext_iff.1 hg S')
        rw [starPerm_apply] at this
        exact this ▸ ⟨v, hvS', rfl⟩
      exact eq_of_mem_of_mem hTN S.2 S'.2 (fun h => hne (Subtype.ext h)) h1 h2 hvS hvS'
    have hlin : (τ g : V →ₗ[ZMod 2] V) = LinearMap.id :=
      LinearMap.ext_on C.span_eq fun v hv => hfix v hv
    exact LinearEquiv.ext fun v => LinearMap.congr_fun hlin v
  have hswap : ∀ S S' : C.Stars, S ≠ S' → ∃ d : E', π d = Equiv.swap S S' := by
    intro S S' hne
    obtain ⟨v, hvS, hvS'⟩ := exists_mem_inter hTN S.2 S'.2 fun h => hne (Subtype.ext h)
    have hvD : v ∈ C.D := by
      obtain ⟨a, ha, c, hc, hac, hS⟩ := S.2
      exact (hS ▸ hvS).1
    obtain ⟨d, rfl⟩ := hδs v hvD
    exact ⟨d, starPerm_eq_swap hTN τ hiso hD hvD (hδ d) hne hvS hvS'⟩
  have hπsurj : Function.Surjective π := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← Equiv.Perm.closure_isSwap, Subgroup.closure_le]
    rintro σ ⟨S, S', hne, rfl⟩
    obtain ⟨d, hd⟩ := hswap S S' hne
    exact ⟨d, hd⟩
  have hE : ∀ g, g ∈ E' ↔ (π g).IsSwap := by
    intro g
    constructor
    · intro hg
      obtain ⟨S, S', hne, hS, hS'⟩ := htwo (δ ⟨g, hg⟩) (hδD _)
      exact ⟨S, S', hne, starPerm_eq_swap hTN τ hiso hD (hδD _) (hδ ⟨g, hg⟩) hne hS hS'⟩
    · rintro ⟨S, S', hne, h⟩
      obtain ⟨d, hd⟩ := hswap S S' hne
      rw [← hd] at h
      rw [hπinj h]
      exact d.2
  obtain ⟨d₀, hd₀⟩ := hDne
  obtain ⟨e₀, he₀, he₀d⟩ := C.exists_mem_b_eq_one (C.ne_zero_of_mem hd₀)
  have h3 := three_le_card hd₀ he₀ (by rw [C.comm]; exact he₀d)
  have h4 := card_ne_four (C := C) hTN
  refine ⟨Fintype.card C.Stars, by omega,
    (MulEquiv.ofBijective π ⟨hπinj, hπsurj⟩).trans
      (Equiv.permCongrHom (Fintype.equivFin C.Stars)), fun g => ?_⟩
  rw [hE g]
  exact (isSwap_permCongr_iff _ _).symm

end Perm

end SympConfig

end CFSG.Fischer.Classification.Symplectic
