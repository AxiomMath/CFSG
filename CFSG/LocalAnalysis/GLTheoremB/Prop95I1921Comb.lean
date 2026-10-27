module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1921Star

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95I1921

open Equiv Equiv.Perm

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem pai (g : Perm Ω) (x : Ω) : g (g⁻¹ x) = x := by simp

theorem fixF_subset_of_card_lt {p : ℕ} (hp : p.Prime) {a b : Perm Ω} (hab : Commute a b)
    (hb : b ^ p = 1) (hcard : (fixF a).card < p) : fixF a ⊆ fixF b := by
  have hcx : ∀ x, a (b x) = b (a x) := fun x => congrArg (fun f : Perm Ω => f x) hab.eq
  have hpres : ∀ x, b x ∈ fixF a ↔ x ∈ fixF a := by
    intro x
    simp only [mem_fixF]
    constructor
    · intro hx
      apply b.injective
      rw [← hcx, hx]
    · intro hx
      rw [hcx, hx]
  let τ' : Perm ↥(fixF a) := b.subtypePerm hpres
  have h' : τ' ^ p = 1 := by
    ext ⟨x, hx⟩
    have := congrArg (fun f : Perm Ω => f x) hb
    simp only [Perm.coe_one, id_eq] at this
    have h2 : ((τ' ^ p) ⟨x, hx⟩ : Ω) = (b ^ p) x := by
      rw [Perm.subtypePerm_pow]
      rfl
    simpa [h2] using this
  have hord : orderOf τ' ∣ (fixF a).card.factorial := by
    have := orderOf_dvd_natCard τ'
    rwa [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_coe] at this
  have hτ1 : orderOf τ' = 1 := by
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one h') with h | h
    · exact h
    · exfalso
      rw [h] at hord
      have := (Nat.Prime.dvd_factorial hp).1 hord
      omega
  have hτ : τ' = 1 := orderOf_eq_one_iff.1 hτ1
  intro x hx
  rw [mem_fixF]
  have := congrArg (fun f : Perm ↥(fixF a) => ((f ⟨x, hx⟩ : ↥(fixF a)) : Ω)) hτ
  simpa [τ'] using this

theorem fixF_eq_of_card_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {a b : Perm Ω}
    (ha : a ^ p = 1) (hb : b ^ p = 1) (hab : Commute a b) (h2 : (fixF a).card = 2)
    (hb' : (fixF b).card = 2 ∨ (fixF b).card = 4) : fixF b = fixF a := by
  have hp3 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
  have hsub : fixF a ⊆ fixF b := fixF_subset_of_card_lt hp hab hb (by omega)
  have hmod := card_fixF_modEq_inter hp hab.symm ha
  rw [Finset.inter_eq_right.2 hsub, h2] at hmod
  have hcard : (fixF b).card = 2 := by
    rcases hb' with h | h
    · exact h
    · exfalso
      rw [h] at hmod
      have h4 := (Nat.modEq_iff_dvd' (by norm_num : (2 : ℕ) ≤ 4)).1 hmod.symm
      have h5 : p ∣ 2 := by simpa using h4
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h5)
  exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm

theorem fixF_inter_of_card_four {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {a b : Perm Ω}
    (ha : a ^ p = 1) (hb : b ^ p = 1) (hab : Commute a b) (ha4 : (fixF a).card = 4)
    (hb4 : (fixF b).card = 4) : fixF a = fixF b ∨ (p = 3 ∧ (fixF a ∩ fixF b).card = 1) := by
  by_cases hp5 : 5 ≤ p
  · left
    have hsub : fixF a ⊆ fixF b := fixF_subset_of_card_lt hp hab hb (by omega)
    exact Finset.eq_of_subset_of_card_le hsub (by omega)
  · have hp4 : p ≠ 4 := by
      rintro rfl
      exact absurd hp (by decide)
    have hp3 : p = 3 := by
      have := hp.two_le
      omega
    subst hp3
    have hmod := card_fixF_modEq_inter hp hab hb
    have hle : (fixF a ∩ fixF b).card ≤ 4 := ha4 ▸ Finset.card_le_card Finset.inter_subset_left
    have h1 : (fixF a ∩ fixF b).card ≡ 4 [MOD 3] := hmod.symm.trans (by rw [ha4])
    have hcases : (fixF a ∩ fixF b).card = 1 ∨ (fixF a ∩ fixF b).card = 4 := by
      unfold Nat.ModEq at h1
      omega
    rcases hcases with h | h
    · right; exact ⟨rfl, h⟩
    · left
      have h1' : fixF a ∩ fixF b = fixF a := Finset.eq_of_subset_of_card_le
        Finset.inter_subset_left (by omega)
      have h2' : fixF a ∩ fixF b = fixF b := Finset.eq_of_subset_of_card_le
        Finset.inter_subset_right (by omega)
      rw [← h1', h2']

theorem exists_restrictDT {F : Finset Ω} {s : Perm Ω} (hs : IsDT F s) :
    ∃ r : Perm ↥F, Perm.ofSubtype r = s ∧ IsDT (Finset.univ : Finset ↥F) r := by
  let r : Perm ↥F := s.subtypePerm (fun x => (isDT_preserves hs x).symm)
  have hr : Perm.ofSubtype r = s :=
    Perm.ofSubtype_subtypePerm _ (fun x hx => by
      by_contra hxF; exact hx (hs.1 x hxF))
  refine ⟨r, hr, ⟨fun x hx => absurd (Finset.mem_univ x) hx, ?_, fun x _ => ?_⟩⟩
  · apply Perm.ofSubtype_injective
    rw [map_mul, map_one, hr]
    exact hs.2.1
  · intro hx
    apply hs.2.2 x.1 x.2
    exact congrArg Subtype.val hx

theorem fin4_dt_mul : ∀ s s' : Perm (Fin 4), IsDT (Finset.univ : Finset (Fin 4)) s →
    IsDT (Finset.univ : Finset (Fin 4)) s' →
      s * s' = 1 ∨ IsDT (Finset.univ : Finset (Fin 4)) (s * s') := by
  decide +kernel

theorem fin4_dt_three : ∀ e s₁ s : Perm (Fin 4), e ^ 3 = 1 →
    (∃ z, e z = z ∧ ∀ x, e x = x → x = z) →
      IsDT (Finset.univ : Finset (Fin 4)) s₁ → IsDT (Finset.univ : Finset (Fin 4)) s →
        s = s₁ ∨ s = e * s₁ * e⁻¹ ∨ s = e⁻¹ * s₁ * e := by
  decide +kernel

theorem isDT_mul_aux {G : Type*} [Fintype G] [DecidableEq G] (hG : Fintype.card G = 4)
    {s s' : Perm G} (hs : IsDT (Finset.univ : Finset G) s) (hs' : IsDT (Finset.univ : Finset G) s') :
    s * s' = 1 ∨ IsDT (Finset.univ : Finset G) (s * s') := by
  let e : G ≃ Fin 4 := Fintype.equivFinOfCardEq hG
  let φ : Perm G ≃* Perm (Fin 4) := e.permCongrHom
  have hφ : ∀ x, φ x = e.permCongr x := fun x => congrFun (Equiv.permCongrHom_coe e) x
  have h1 : IsDT (Finset.univ : Finset (Fin 4)) (φ s) := by
    rw [hφ]; exact (isDT_univ_permCongr e s).2 hs
  have h2 : IsDT (Finset.univ : Finset (Fin 4)) (φ s') := by
    rw [hφ]; exact (isDT_univ_permCongr e s').2 hs'
  rcases fin4_dt_mul _ _ h1 h2 with h | h
  · left
    apply φ.injective
    rw [map_mul, map_one]
    exact h
  · right
    rw [← map_mul, hφ] at h
    exact (isDT_univ_permCongr e _).1 h

theorem isDT_mul {F : Finset Ω} (hF : F.card = 4) {s s' : Perm Ω} (hs : IsDT F s)
    (hs' : IsDT F s') : s * s' = 1 ∨ IsDT F (s * s') := by
  have hcard : Fintype.card ↥F = 4 := by rw [Fintype.card_coe]; exact hF
  obtain ⟨r, hr, hrd⟩ := exists_restrictDT hs
  obtain ⟨r', hr', hrd'⟩ := exists_restrictDT hs'
  rcases isDT_mul_aux hcard hrd hrd' with h | h
  · left
    rw [← hr, ← hr', ← map_mul, h, map_one]
  · right
    rw [← hr, ← hr', ← map_mul]
    exact isDT_of_ofSubtype h

@[expose] def V4 (F : Finset Ω) (hF : F.card = 4) : Subgroup (Perm Ω) where
  carrier := {s | s = 1 ∨ IsDT F s}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro s s' (rfl | hs) (rfl | hs')
    · left; simp
    · right; simpa using hs'
    · right; simpa using hs
    · exact (isDT_mul hF hs hs')
  inv_mem' := by
    rintro s (rfl | hs)
    · left; simp
    · right
      have : s⁻¹ = s := by
        have h2 := hs.2.1
        exact inv_eq_of_mul_eq_one_left h2
      rw [this]; exact hs

theorem mem_V4 {F : Finset Ω} (hF : F.card = 4) {s : Perm Ω} : s ∈ V4 F hF ↔ s = 1 ∨ IsDT F s :=
  Iff.rfl

theorem conj_ofSubtype {F : Finset Ω} {g : Perm Ω} {gr : Perm ↥F}
    (hg : ∀ x : ↥F, ((gr x : ↥F) : Ω) = g x) (hpres : ∀ x, x ∈ F ↔ g x ∈ F) (r : Perm ↥F) :
    g * Perm.ofSubtype r * g⁻¹ = Perm.ofSubtype (gr * r * gr⁻¹) := by
  ext x
  by_cases hx : x ∈ F
  · have hy : g⁻¹ x ∈ F := by
      rw [hpres, pai]; exact hx
    have hgr : gr ⟨g⁻¹ x, hy⟩ = ⟨x, hx⟩ := Subtype.ext (by rw [hg]; simp)
    have hgri : gr⁻¹ ⟨x, hx⟩ = ⟨g⁻¹ x, hy⟩ := by
      rw [Perm.inv_eq_iff_eq]; exact hgr.symm
    have hL : (g * Perm.ofSubtype r * g⁻¹) x = g (((r ⟨g⁻¹ x, hy⟩ : ↥F)) : Ω) := by
      simp only [Perm.mul_apply]
      rw [Perm.ofSubtype_apply_of_mem r hy]
    have hR : (Perm.ofSubtype (gr * r * gr⁻¹)) x = ((gr (r ⟨g⁻¹ x, hy⟩) : ↥F) : Ω) := by
      rw [Perm.ofSubtype_apply_of_mem _ hx]
      simp only [Perm.mul_apply]
      rw [hgri]
    rw [hL, hR, hg]
  · have hy : g⁻¹ x ∉ F := by
      intro h
      apply hx
      have := (hpres _).1 h
      rwa [pai] at this
    rw [Perm.mul_apply, Perm.mul_apply, Perm.ofSubtype_apply_of_not_mem _ hy,
      pai, Perm.ofSubtype_apply_of_not_mem _ hx]

theorem dt_upgrade_aux {G : Type*} [Fintype G] [DecidableEq G] (hG : Fintype.card G = 4)
    {e s₁ s : Perm G} (he : e ^ 3 = 1) (hfix : ∃ z, e z = z ∧ ∀ x, e x = x → x = z)
    (h1 : IsDT (Finset.univ : Finset G) s₁) (hs : IsDT (Finset.univ : Finset G) s) :
    s = s₁ ∨ s = e * s₁ * e⁻¹ ∨ s = e⁻¹ * s₁ * e := by
  let e₀ : G ≃ Fin 4 := Fintype.equivFinOfCardEq hG
  let φ : Perm G ≃* Perm (Fin 4) := e₀.permCongrHom
  have hφ : ∀ x, φ x = e₀.permCongr x := fun x => congrFun (Equiv.permCongrHom_coe e₀) x
  have hfix' : ∃ z, φ e z = z ∧ ∀ x, φ e x = x → x = z := by
    obtain ⟨z, hz, hz2⟩ := hfix
    refine ⟨e₀ z, ?_, ?_⟩
    · rw [hφ, Equiv.permCongr_apply]; simp [hz]
    · intro y hy
      rw [hφ, Equiv.permCongr_apply] at hy
      have h3 : e (e₀.symm y) = e₀.symm y := by
        apply e₀.injective; simpa using hy
      have := hz2 _ h3
      rw [← this]; simp
  have := fin4_dt_three (φ e) (φ s₁) (φ s) (by rw [← map_pow, he, map_one]) hfix'
    (by rw [hφ]; exact (isDT_univ_permCongr e₀ s₁).2 h1)
    (by rw [hφ]; exact (isDT_univ_permCongr e₀ s).2 hs)
  rcases this with h | h | h
  · left; exact φ.injective h
  · right; left; apply φ.injective; rw [h, map_mul, map_mul, map_inv]
  · right; right; apply φ.injective; rw [h, map_mul, map_mul, map_inv]

theorem dt_upgrade {F : Finset Ω} (hF : F.card = 4) {e : Perm Ω} (he : e ^ 3 = 1)
    (hpres : ∀ x, x ∈ F ↔ e x ∈ F) (hfix : (F ∩ fixF e).card = 1) {s₁ s : Perm Ω}
    (h1 : IsDT F s₁) (hs : IsDT F s) :
    s = s₁ ∨ s = e * s₁ * e⁻¹ ∨ s = e⁻¹ * s₁ * e := by
  have hcard : Fintype.card ↥F = 4 := by rw [Fintype.card_coe]; exact hF
  obtain ⟨r₁, hr₁, hd₁⟩ := exists_restrictDT h1
  obtain ⟨r, hr, hd⟩ := exists_restrictDT hs
  let er : Perm ↥F := e.subtypePerm (fun x => (hpres x).symm)
  have her : ∀ x : ↥F, ((er x : ↥F) : Ω) = e x := fun x => rfl
  have he3 : er ^ 3 = 1 := by
    ext ⟨x, hx⟩
    have := congrArg (fun f : Perm Ω => f x) he
    simp only [Perm.coe_one, id_eq] at this
    have h2 : ((er ^ 3) ⟨x, hx⟩ : Ω) = (e ^ 3) x := by
      rw [Perm.subtypePerm_pow]
      rfl
    simpa [h2] using this
  have hfx : ∃ z, er z = z ∧ ∀ x, er x = x → x = z := by
    obtain ⟨z, hz⟩ := Finset.card_eq_one.1 hfix
    have hzm : z ∈ F ∩ fixF e := by rw [hz]; exact Finset.mem_singleton_self z
    obtain ⟨hzF, hzfix⟩ := Finset.mem_inter.1 hzm
    refine ⟨⟨z, hzF⟩, Subtype.ext (mem_fixF.1 hzfix), fun x hx => ?_⟩
    have hxm : (x : Ω) ∈ F ∩ fixF e := by
      refine Finset.mem_inter.2 ⟨x.2, mem_fixF.2 ?_⟩
      have := congrArg Subtype.val hx
      exact this
    rw [hz, Finset.mem_singleton] at hxm
    exact Subtype.ext hxm
  rcases dt_upgrade_aux hcard he3 hfx hd₁ hd with h | h | h
  · left; rw [← hr, ← hr₁, h]
  · right; left
    rw [← hr, ← hr₁, h]
    exact (conj_ofSubtype her hpres r₁).symm
  · right; right
    rw [← hr, ← hr₁, h]
    have hpres' : ∀ x, x ∈ F ↔ e⁻¹ x ∈ F := fun x => by
      rw [hpres (e⁻¹ x), pai]
    have her' : ∀ x : ↥F, ((er⁻¹ x : ↥F) : Ω) = e⁻¹ x := by
      intro x
      have : er (er⁻¹ x) = x := pai er x
      apply e.injective
      rw [pai]
      exact congrArg Subtype.val this
    have := conj_ofSubtype her' hpres' r₁
    simpa using this.symm

theorem trivial_of_alt_normalized {U : Finset Ω} (hU : 5 ≤ U.card) {R : Subgroup (Perm Ω)}
    (hR2 : ∀ r ∈ R, ∃ n : ℕ, r ^ (2 ^ n) = 1) (hRev : ∀ r ∈ R, sign r = 1)
    (hRU : ∀ r ∈ R, ∀ x, x ∉ U → r x = x)
    (hRn : ∀ g : Perm Ω, sign g = 1 → (∀ x, x ∉ U → g x = x) → ∀ r ∈ R, g * r * g⁻¹ ∈ R) :
    R = ⊥ := by
  let N' : Subgroup (Perm ↥U) := R.comap (Perm.ofSubtype : Perm ↥U →* Perm Ω)
  have hN'exp : ∀ g ∈ N', ∃ n : ℕ, g ^ (2 ^ n) = 1 := by
    intro g hg
    obtain ⟨n, hn⟩ := hR2 (Perm.ofSubtype g) hg
    refine ⟨n, Perm.ofSubtype_injective ?_⟩
    rw [map_pow, hn, map_one]
  have hev : ∀ g ∈ N', sign g = 1 := by
    intro g hg
    have := hRev (Perm.ofSubtype g) hg
    rwa [Perm.sign_ofSubtype] at this
  have hnorm : ∀ h : Perm ↥U, sign h = 1 → ∀ g ∈ N', h * g * h⁻¹ ∈ N' := by
    intro h hh g hg
    show Perm.ofSubtype (h * g * h⁻¹) ∈ R
    rw [map_mul, map_mul, map_inv]
    refine hRn _ (by rw [Perm.sign_ofSubtype]; exact hh) (fun x hx => ?_) _ hg
    exact Perm.ofSubtype_apply_of_not_mem h hx
  have hcard : Fintype.card ↥U ≠ 4 := by rw [Fintype.card_coe]; omega
  rw [eq_bot_iff]
  intro r hr
  rw [Subgroup.mem_bot]
  have hpres : ∀ x, x ∈ U ↔ r x ∈ U := by
    intro x
    constructor
    · intro hx
      by_contra hrx
      have h1 := hRU r hr _ hrx
      have : r x = x := r.injective h1
      exact hrx (by rw [this]; exact hx)
    · intro hrx
      by_contra hx
      have h2 := hRU r hr x hx
      exact hx (by rw [← h2]; exact hrx)
  let r' : Perm ↥U := r.subtypePerm (fun x => (hpres x).symm)
  have hr' : Perm.ofSubtype r' = r :=
    Perm.ofSubtype_subtypePerm _ (fun x hx => by
      by_contra hxU; exact hx (hRU r hr x hxU))
  have hr'N : r' ∈ N' := by
    show Perm.ofSubtype r' ∈ R
    rw [hr']; exact hr
  rcases pcore_alt hN'exp hev hnorm r' hr'N with h | ⟨h4, -⟩
  · rw [← hr', h, map_one]
  · exact absurd h4 hcard

theorem fin4_dt_even : ∀ s : Perm (Fin 4), IsDT (Finset.univ : Finset (Fin 4)) s → sign s = 1 := by
  decide +kernel

theorem sign_isDT {F : Finset Ω} (hF : F.card = 4) {s : Perm Ω} (hs : IsDT F s) : sign s = 1 := by
  have hcard : Fintype.card ↥F = 4 := by rw [Fintype.card_coe]; exact hF
  obtain ⟨r, hr, hd⟩ := exists_restrictDT hs
  rw [← hr, Perm.sign_ofSubtype]
  let e : ↥F ≃ Fin 4 := Fintype.equivFinOfCardEq hcard
  have := fin4_dt_even (e.permCongr r) ((isDT_univ_permCongr e r).2 hd)
  rwa [sign_permCongr] at this

theorem mem_zpowers_swap_of_supported {x y : Ω} (hxy : x ≠ y) {s : Perm Ω}
    (hs : ∀ z, z ≠ x → z ≠ y → s z = z) : s ∈ Subgroup.zpowers (swap x y) := by
  have hx : s x = x ∨ s x = y := by
    by_contra h
    push Not at h
    have := hs (s x) h.1 h.2
    exact h.1 (s.injective this)
  have hy : s y = y ∨ s y = x := by
    by_contra h
    push Not at h
    have := hs (s y) h.2 h.1
    exact h.1 (s.injective this)
  rcases hx with hx | hx
  · rcases hy with hy | hy
    · have : s = 1 := by
        ext z
        by_cases hzx : z = x
        · subst hzx; simpa using hx
        · by_cases hzy : z = y
          · subst hzy; simpa using hy
          · simpa using hs z hzx hzy
      rw [this]; exact Subgroup.one_mem _
    · exfalso
      have : s y = s x := by rw [hx, hy]
      exact hxy (s.injective this).symm
  · rcases hy with hy | hy
    · exfalso
      have : s x = s y := by rw [hx, hy]
      exact hxy (s.injective this)
    · have : s = swap x y := by
        ext z
        by_cases hzx : z = x
        · subst hzx; simpa using hx
        · by_cases hzy : z = y
          · subst hzy; simp [hy]
          · rw [swap_apply_of_ne_of_ne hzx hzy]; exact hs z hzx hzy
      rw [this]; exact Subgroup.mem_zpowers _

theorem mem_zpowers_swap_cases {x y : Ω} {r : Perm Ω} (hr : r ∈ Subgroup.zpowers (swap x y)) :
    r = 1 ∨ r = swap x y := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hr
  have h2 : (swap x y) ^ (2 : ℤ) = 1 := by
    rw [zpow_two]; exact swap_mul_self x y
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    have : k = 2 * (k / 2) := by omega
    rw [this, zpow_mul, h2, one_zpow]
  · right
    have : k = 2 * (k / 2) + 1 := by omega
    rw [this, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem comb {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Δ : Subgroup (Perm Ω)} (hΔc : ∀ a ∈ Δ, ∀ b ∈ Δ, a * b = b * a) (hΔe : ∀ a ∈ Δ, a ^ p = 1)
    {Sg : Perm Ω → Subgroup (Perm Ω)}
    (hloc : ∀ a ∈ Δ, a ≠ 1 → ∀ s ∈ Sg a, (∀ x, a x ≠ x → s x = x) ∧
        (s = 1 ∨ (fixF a).card = 2 ∨ ((fixF a).card = 4 ∧ IsDT (fixF a) s)))
    (hinv : ∀ a ∈ Δ, a ≠ 1 → ∀ e ∈ Δ, ∀ s ∈ Sg a, e * s * e⁻¹ ∈ Sg a)
    {R : Subgroup (Perm Ω)} (hR2 : ∀ r ∈ R, ∃ n : ℕ, r ^ (2 ^ n) = 1)
    (hRS : R ≤ ⨆ (a : Perm Ω) (_ : a ∈ Δ) (_ : a ≠ 1), Sg a)
    (hRn : ∀ s ∈ (⨆ (a : Perm Ω) (_ : a ∈ Δ) (_ : a ≠ 1), Sg a), ∀ r ∈ R, s * r * s⁻¹ ∈ R) :
    R = ⊥ ∨ (∃ x y : Ω, x ≠ y ∧ R = Subgroup.zpowers (swap x y) ∧
        Fintype.card Ω ≡ 2 [MOD p]) ∨
      (Fintype.card Ω ≡ 4 [MOD p] ∧ ∃ F : Finset Ω, F.card = 4 ∧ ∀ r ∈ R, r = 1 ∨ IsDT F r) := by
  classical
  set S : Subgroup (Perm Ω) := ⨆ (a : Perm Ω) (_ : a ∈ Δ) (_ : a ≠ 1), Sg a with hS
  have hSg_le : ∀ a ∈ Δ, a ≠ 1 → Sg a ≤ S := fun a ha ha1 =>
    le_iSup₂_of_le a ha (le_iSup_of_le ha1 le_rfl)
  have hSle : ∀ H : Subgroup (Perm Ω), (∀ a ∈ Δ, a ≠ 1 → Sg a ≤ H) → S ≤ H := fun H h =>
    iSup₂_le fun a ha => iSup_le fun ha1 => h a ha ha1
  by_cases hD : ∃ a ∈ Δ, a ≠ 1 ∧ Sg a ≠ ⊥
  swap
  · left
    push Not at hD
    have : S ≤ ⊥ := hSle ⊥ (fun a ha ha1 => (hD a ha ha1).le)
    exact eq_bot_iff.2 (hRS.trans this)
  obtain ⟨a₁, ha₁Δ, ha₁1, ha₁ne⟩ := hD
  have hcard24 : ∀ a ∈ Δ, a ≠ 1 → Sg a ≠ ⊥ → (fixF a).card = 2 ∨ (fixF a).card = 4 := by
    intro a ha ha1 hne
    obtain ⟨s, hs1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
    have hs1' : (s : Perm Ω) ≠ 1 := fun h => hs1 (Subtype.ext h)
    rcases (hloc a ha ha1 s s.2).2 with h | h | ⟨h4, -⟩
    · exact absurd h hs1'
    · exact Or.inl h
    · exact Or.inr h4
  by_cases hI : ∃ a₀ ∈ Δ, a₀ ≠ 1 ∧ Sg a₀ ≠ ⊥ ∧ (fixF a₀).card = 2
  ·
    obtain ⟨a₀, ha₀Δ, ha₀1, ha₀ne, ha₀2⟩ := hI
    obtain ⟨x, y, hxy, hFxy⟩ := Finset.card_eq_two.1 ha₀2
    have hall : ∀ a ∈ Δ, a ≠ 1 → Sg a ≤ Subgroup.zpowers (swap x y) := by
      intro a ha ha1
      by_cases hne : Sg a = ⊥
      · rw [hne]; exact bot_le
      · have hfix : fixF a = fixF a₀ := fixF_eq_of_card_two hp hp2 (hΔe a₀ ha₀Δ) (hΔe a ha)
          (hΔc a₀ ha₀Δ a ha) ha₀2 (hcard24 a ha ha1 hne)
        intro s hs
        refine mem_zpowers_swap_of_supported hxy (fun z hzx hzy => ?_)
        have hz : z ∉ fixF a := by
          rw [hfix, hFxy]; simp [hzx, hzy]
        exact (hloc a ha ha1 s hs).1 z (fun h => hz (mem_fixF.2 h))
    have hSz : S ≤ Subgroup.zpowers (swap x y) := hSle _ hall
    have hRz : R ≤ Subgroup.zpowers (swap x y) := hRS.trans hSz
    by_cases hτ : swap x y ∈ R
    · right; left
      refine ⟨x, y, hxy, le_antisymm hRz ((Subgroup.zpowers_le).2 hτ), ?_⟩
      have := card_modEq_fixF hp (hΔe a₀ ha₀Δ)
      rwa [ha₀2] at this
    · left
      rw [eq_bot_iff]
      intro r hr
      rw [Subgroup.mem_bot]
      rcases mem_zpowers_swap_cases (hRz hr) with h | h
      · exact h
      · exact absurd (h ▸ hr) hτ
  ·
    have h4 : ∀ a ∈ Δ, a ≠ 1 → Sg a ≠ ⊥ → (fixF a).card = 4 := by
      intro a ha ha1 hne
      rcases hcard24 a ha ha1 hne with h | h
      · exact absurd ⟨a, ha, ha1, hne, h⟩ hI
      · exact h
    have ha₁4 := h4 a₁ ha₁Δ ha₁1 ha₁ne
    have hcardΩ : Fintype.card Ω ≡ 4 [MOD p] := by
      have := card_modEq_fixF hp (hΔe a₁ ha₁Δ)
      rwa [ha₁4] at this
    by_cases hE : ∀ a ∈ Δ, a ≠ 1 → Sg a ≠ ⊥ → fixF a = fixF a₁
    ·
      right; right
      refine ⟨hcardΩ, fixF a₁, ha₁4, ?_⟩
      have hSV : S ≤ V4 (fixF a₁) ha₁4 := by
        refine hSle _ (fun a ha ha1 => ?_)
        by_cases hne : Sg a = ⊥
        · rw [hne]; exact bot_le
        · intro s hs
          have hfa := hE a ha ha1 hne
          rcases (hloc a ha ha1 s hs).2 with h | h | ⟨-, h⟩
          · exact (mem_V4 ha₁4).2 (Or.inl h)
          · exfalso
            have := h4 a ha ha1 hne
            omega
          · exact (mem_V4 ha₁4).2 (Or.inr (by rw [← hfa]; exact h))
      intro r hr
      exact (mem_V4 ha₁4).1 (hSV (hRS hr))
    ·
      left
      push Not at hE
      obtain ⟨b, hbΔ, hb1, hbne, hbF⟩ := hE
      have hb4 := h4 b hbΔ hb1 hbne
      have hcomm : ∀ a ∈ Δ, ∀ b ∈ Δ, Commute a b := fun a ha b hb => hΔc a ha b hb
      have h3 : p = 3 :=
        ((fixF_inter_of_card_four hp hp2 (hΔe a₁ ha₁Δ) (hΔe b hbΔ) (hcomm a₁ ha₁Δ b hbΔ) ha₁4
          hb4).resolve_left (fun h => hbF h.symm)).1
      have hup : ∀ c ∈ Δ, c ≠ 1 → Sg c ≠ ⊥ → ∀ s, IsDT (fixF c) s → s ∈ Sg c := by
        intro c hc hc1 hcne s hs
        have hc4 := h4 c hc hc1 hcne
        obtain ⟨c', hc'Δ, hc'1, hc'ne, hc'F⟩ : ∃ c' ∈ Δ, c' ≠ 1 ∧ Sg c' ≠ ⊥ ∧
            fixF c' ≠ fixF c := by
          by_cases h : fixF c = fixF a₁
          · exact ⟨b, hbΔ, hb1, hbne, by rw [h]; exact hbF⟩
          · exact ⟨a₁, ha₁Δ, ha₁1, ha₁ne, fun h' => h h'.symm⟩
        have hc'4 := h4 c' hc'Δ hc'1 hc'ne
        have hint := (fixF_inter_of_card_four hp hp2 (hΔe c hc) (hΔe c' hc'Δ) (hcomm c hc c' hc'Δ)
          hc4 hc'4).resolve_left (fun h => hc'F h.symm)
        have hpres : ∀ x, x ∈ fixF c ↔ c' x ∈ fixF c := by
          intro x
          simp only [mem_fixF]
          have hcx : c (c' x) = c' (c x) := congrArg (fun f : Perm Ω => f x)
            (hcomm c hc c' hc'Δ).eq
          constructor
          · intro hx; rw [hcx, hx]
          · intro hx; apply c'.injective; rw [← hcx]; exact hx
        obtain ⟨t, ht⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hcne
        have ht1 : (t : Perm Ω) ≠ 1 := fun h => ht (Subtype.ext h)
        have htdt : IsDT (fixF c) (t : Perm Ω) := by
          rcases (hloc c hc hc1 t t.2).2 with h | h | ⟨-, h⟩
          · exact absurd h ht1
          · omega
          · exact h
        have hc'3 : c' ^ 3 = 1 := by rw [← h3]; exact hΔe c' hc'Δ
        rcases dt_upgrade hc4 hc'3 hpres hint.2 htdt hs with h | h | h
        · rw [h]; exact t.2
        · rw [h]; exact hinv c hc hc1 c' hc'Δ t t.2
        · have := hinv c hc hc1 c'⁻¹ (Δ.inv_mem hc'Δ) t t.2
          rw [inv_inv] at this
          rw [h]; exact this
      let D' : Finset (Perm Ω) := Finset.univ.filter
        (fun c => c ∈ Δ ∧ c ≠ 1 ∧ Sg c ≠ ⊥ ∧ fixF c ≠ fixF a₁)
      have hD'mem : ∀ c, c ∈ D' ↔ c ∈ Δ ∧ c ≠ 1 ∧ Sg c ≠ ⊥ ∧ fixF c ≠ fixF a₁ := by
        intro c; simp [D']
      haveI : Nonempty ↥D' := ⟨⟨b, (hD'mem b).2 ⟨hbΔ, hb1, hbne, hbF⟩⟩⟩
      let G : ↥D' → Finset Ω := fun c => fixF c.1
      have hG4 : ∀ c : ↥D', (G c).card = 4 := fun c => by
        obtain ⟨hc, hc1, hcne, -⟩ := (hD'mem c.1).1 c.2
        exact h4 c.1 hc hc1 hcne
      have hGint : ∀ c : ↥D', (fixF a₁ ∩ G c).card = 1 := by
        intro c
        obtain ⟨hc, hc1, hcne, hcF⟩ := (hD'mem c.1).1 c.2
        exact ((fixF_inter_of_card_four hp hp2 (hΔe a₁ ha₁Δ) (hΔe c.1 hc)
          (hcomm a₁ ha₁Δ c.1 hc) ha₁4 (h4 c.1 hc hc1 hcne)).resolve_left
          (fun h => hcF h.symm)).2
      have hA0 : ∀ s, IsDT (fixF a₁) s → s ∈ S := fun s hs =>
        hSg_le a₁ ha₁Δ ha₁1 (hup a₁ ha₁Δ ha₁1 ha₁ne s hs)
      have hAG : ∀ (c : ↥D') s, IsDT (G c) s → s ∈ S := by
        intro c s hs
        obtain ⟨hc, hc1, hcne, -⟩ := (hD'mem c.1).1 c.2
        exact hSg_le c.1 hc hc1 (hup c.1 hc hc1 hcne s hs)
      have hgen := star_gen (fixF a₁) G ha₁4 hG4 hGint hA0 hAG
      set U : Finset Ω := fixF a₁ ∪ Finset.univ.biUnion G with hU
      have hfixF_sub : ∀ c ∈ Δ, c ≠ 1 → Sg c ≠ ⊥ → fixF c ⊆ U := by
        intro c hc hc1 hcne x hx
        by_cases hcF : fixF c = fixF a₁
        · rw [hU]; exact Finset.mem_union_left _ (hcF ▸ hx)
        · rw [hU]
          exact Finset.mem_union_right _ (Finset.mem_biUnion.2
            ⟨⟨c, (hD'mem c).2 ⟨hc, hc1, hcne, hcF⟩⟩, Finset.mem_univ _, hx⟩)
      let Gs : Subgroup (Perm Ω) :=
        { carrier := {g | sign g = 1 ∧ ∀ x, x ∉ U → g x = x}
          one_mem' := ⟨by simp, fun x _ => rfl⟩
          mul_mem' := by
            rintro g g' ⟨h1, h2⟩ ⟨h1', h2'⟩
            exact ⟨by rw [map_mul, h1, h1']; rfl, fun x hx => by
              rw [Perm.mul_apply, h2' x hx, h2 x hx]⟩
          inv_mem' := by
            rintro g ⟨h1, h2⟩
            refine ⟨by rw [map_inv, h1]; rfl, fun x hx => ?_⟩
            exact Perm.inv_eq_iff_eq.2 (h2 x hx).symm }
      have hSGs : S ≤ Gs := by
        refine hSle _ (fun c hc hc1 => ?_)
        by_cases hcne : Sg c = ⊥
        · rw [hcne]; exact bot_le
        · intro s hs
          have hc4 := h4 c hc hc1 hcne
          rcases (hloc c hc hc1 s hs).2 with h | h | ⟨-, h⟩
          · rw [h]; exact Gs.one_mem
          · omega
          · exact ⟨sign_isDT hc4 h, fun x hx =>
              h.1 x (fun hxF => hx (hfixF_sub c hc hc1 hcne hxF))⟩
      have hint_ab := ((fixF_inter_of_card_four hp hp2 (hΔe a₁ ha₁Δ) (hΔe b hbΔ)
        (hcomm a₁ ha₁Δ b hbΔ) ha₁4 hb4).resolve_left (fun h => hbF h.symm)).2
      have hU5 : 5 ≤ U.card := by
        have h1 : (fixF a₁ ∪ fixF b).card = 7 := by
          have := Finset.card_union_add_card_inter (fixF a₁) (fixF b)
          rw [ha₁4, hb4, hint_ab] at this
          omega
        have hsub : fixF a₁ ∪ fixF b ⊆ U :=
          Finset.union_subset (Finset.subset_union_left)
            (hfixF_sub b hbΔ hb1 hbne)
        have := Finset.card_le_card hsub
        omega
      exact trivial_of_alt_normalized hU5 hR2 (fun r hr => (hSGs (hRS hr)).1)
        (fun r hr x hx => (hSGs (hRS hr)).2 x hx)
        (fun g hg1 hgU r hr => hRn g (hgen g hg1 hgU) r hr)

section Seven

@[expose] def c₁ : Perm (Fin 7) := swap 0 2 * swap 0 1

@[expose] def c₂ : Perm (Fin 7) := c₁ * (swap 3 5 * swap 3 4)

@[expose] def c₃ : Perm (Fin 7) := swap 3 5 * swap 3 4

theorem c₁_cycleType : c₁.cycleType = {3} :=
  (isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide) :
    (swap (0 : Fin 7) 2 * swap 0 1).IsThreeCycle)

theorem c₃_cycleType : c₃.cycleType = {3} :=
  (isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide) :
    (swap (3 : Fin 7) 5 * swap 3 4).IsThreeCycle)

theorem c₂_cycleType : c₂.cycleType = {3, 3} := by
  have hd : Perm.Disjoint c₁ c₃ := by
    show ∀ x, c₁ x = x ∨ c₃ x = x
    unfold c₁ c₃; decide
  unfold c₂
  rw [show c₁ * (swap 3 5 * swap 3 4) = c₁ * c₃ from rfl, hd.cycleType_mul, c₁_cycleType,
    c₃_cycleType]
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem locB7_std₁ : ∀ g : Perm (Fin 7), g * c₁ = c₁ * g → sign g = 1 → g ^ 4 = 1 →
    (∀ x, c₁ x ≠ x → g x = x) ∧ (g = 1 ∨ ((fixF c₁).card = 4 ∧ IsDT (fixF c₁) g)) := by
  unfold c₁; decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem locB7_std₂ : ∀ g : Perm (Fin 7), g * c₂ = c₂ * g → sign g = 1 → g ^ 4 = 1 →
    (∀ x, c₂ x ≠ x → g x = x) ∧ (g = 1 ∨ ((fixF c₂).card = 4 ∧ IsDT (fixF c₂) g)) := by
  unfold c₂ c₁; decide

theorem locB7_conj {α : Type*} [Fintype α] [DecidableEq α] {σ₀ σ : Perm α}
    (hstd : ∀ g : Perm α, g * σ₀ = σ₀ * g → sign g = 1 → g ^ 4 = 1 →
      (∀ x, σ₀ x ≠ x → g x = x) ∧ (g = 1 ∨ ((fixF σ₀).card = 4 ∧ IsDT (fixF σ₀) g)))
    (hσ : IsConj σ₀ σ) {g : Perm α} (hg : g * σ = σ * g) (hev : sign g = 1) (h4 : g ^ 4 = 1) :
    (∀ x, σ x ≠ x → g x = x) ∧ (g = 1 ∨ ((fixF σ).card = 4 ∧ IsDT (fixF σ) g)) := by
  obtain ⟨h, rfl⟩ := isConj_iff.1 hσ
  set g₀ : Perm α := h⁻¹ * g * h with hg₀
  have hcomm : g₀ * σ₀ = σ₀ * g₀ := by
    have : g * (h * σ₀ * h⁻¹) = (h * σ₀ * h⁻¹) * g := hg
    calc g₀ * σ₀ = h⁻¹ * (g * (h * σ₀ * h⁻¹)) * h := by rw [hg₀]; group
      _ = h⁻¹ * ((h * σ₀ * h⁻¹) * g) * h := by rw [this]
      _ = σ₀ * g₀ := by rw [hg₀]; group
  have hsg : sign g₀ = 1 := by
    rw [hg₀, map_mul, map_mul, map_inv, hev]
    rcases Int.units_eq_one_or (sign h) with h1 | h1 <;> simp [h1]
  have h4' : g₀ ^ 4 = 1 := by
    have : g₀ ^ 4 = h⁻¹ * g ^ 4 * h := by
      rw [hg₀]
      have := conj_pow (a := h⁻¹) (b := g) (i := 4)
      simpa using this
    rw [this, h4]; group
  obtain ⟨hmv, hcase⟩ := hstd g₀ hcomm hsg h4'
  have hconjx : ∀ x, g x = h (g₀ (h⁻¹ x)) := by
    intro x; rw [hg₀]; simp
  have hfix : ∀ x, (h * σ₀ * h⁻¹) x = x ↔ σ₀ (h⁻¹ x) = h⁻¹ x := by
    intro x
    simp only [Perm.mul_apply]
    constructor
    · intro hx
      apply h.injective
      rw [hx]; simp
    · intro hx
      rw [hx]; simp
  refine ⟨fun x hx => ?_, ?_⟩
  · have hy : σ₀ (h⁻¹ x) ≠ h⁻¹ x := fun hh => hx ((hfix x).2 hh)
    have := hmv (h⁻¹ x) hy
    rw [hconjx, this]; simp
  · rcases hcase with h0 | ⟨hc4, hdt⟩
    · left
      have : g = h * g₀ * h⁻¹ := by rw [hg₀]; group
      rw [this, h0]; group
    · right
      have hF : fixF (h * σ₀ * h⁻¹) = (fixF σ₀).map h.toEmbedding := by
        ext x
        rw [mem_fixF, hfix, Finset.mem_map_equiv, mem_fixF]
        simp
      refine ⟨by rw [hF, Finset.card_map, hc4], ?_, ?_, ?_⟩
      · intro x hx
        have hx' : h⁻¹ x ∉ fixF σ₀ := by
          intro hh; apply hx
          rw [hF, Finset.mem_map_equiv]; simpa using hh
        have := hdt.1 _ hx'
        rw [hconjx, this]; simp
      · have : g = h * g₀ * h⁻¹ := by rw [hg₀]; group
        have h2 := hdt.2.1
        calc g * g = h * (g₀ * g₀) * h⁻¹ := by rw [this]; group
          _ = 1 := by rw [h2]; group
      · intro x hx hgx
        have hx' : h⁻¹ x ∈ fixF σ₀ := by
          rw [hF, Finset.mem_map_equiv] at hx; simpa using hx
        apply hdt.2.2 _ hx'
        have := hconjx x
        rw [hgx] at this
        have h5 : h⁻¹ x = g₀ (h⁻¹ x) := by
          apply h.injective
          rw [← this]; simp
        exact h5.symm

theorem locB7 {σ g : Perm (Fin 7)} (hσ : σ ^ 3 = 1) (hσ1 : σ ≠ 1) (hg : g * σ = σ * g)
    (hev : sign g = 1) (h4 : g ^ 4 = 1) :
    (∀ x, σ x ≠ x → g x = x) ∧ (g = 1 ∨ ((fixF σ).card = 4 ∧ IsDT (fixF σ) g)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hct := cycleType_of_pow_prime_eq_one hσ
  have hcard_pos : σ.cycleType.card ≠ 0 := by
    intro h0
    apply hσ1
    rw [← cycleType_eq_zero]
    exact Multiset.card_eq_zero.1 h0
  have hsum : σ.cycleType.sum = σ.support.card := sum_cycleType σ
  have hsupp : σ.support.card ≤ 7 := by simpa using σ.support.card_le_univ
  have hk : σ.cycleType.card = 1 ∨ σ.cycleType.card = 2 := by
    rw [hct] at hsum
    simp only [Multiset.sum_replicate, smul_eq_mul, Multiset.card_replicate] at hsum
    omega
  rcases hk with hk | hk
  · have hty : σ.cycleType = {3} := by rw [hct, hk]; rfl
    have hconj : IsConj c₁ σ := isConj_iff_cycleType_eq.2 (by rw [hty, c₁_cycleType])
    exact locB7_conj locB7_std₁ hconj hg hev h4
  · have hty : σ.cycleType = {3, 3} := by rw [hct, hk]; rfl
    have hconj : IsConj c₂ σ := isConj_iff_cycleType_eq.2 (by rw [hty, c₂_cycleType])
    exact locB7_conj locB7_std₂ hconj hg hev h4

end Seven

end CFSG.LocalAnalysis.GLTheoremB.Prop95I1921
