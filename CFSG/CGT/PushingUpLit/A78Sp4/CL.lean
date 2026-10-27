module

public import CFSG.CGT.PushingUpLit.A78Sp4.Coord
public import Mathlib.FieldTheory.Perfect

public section

namespace CFSG.CGT.PushingUpLit.A78Sp4

variable {K : Type*} [Field K]

@[expose] def IsDiagForm (gb : K × K →+ K × K) : Prop :=
  ∃ (a b : K) (σ : K →+* K), a ≠ 0 ∧ b ≠ 0 ∧ ∀ r s, gb (r, s) = (a * σ r, b * σ s)

@[expose] def IsSwapForm (gb : K × K →+ K × K) : Prop :=
  ∃ (a b : K) (σ : K →+* K), a ≠ 0 ∧ b ≠ 0 ∧ ∀ r s, gb (r, s) = (b * σ s, a ^ 2 * σ r ^ 2)

omit [Field K] in
theorem exists_avoid [Finite K] (s : Finset K) (h : s.card < Nat.card K) : ∃ d : K, d ∉ s := by
  have := Fintype.ofFinite K
  by_contra hcon
  push Not at hcon
  have : (Finset.univ : Finset K) ⊆ s := fun d _ => hcon d
  have h2 := Finset.card_le_card this
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at h2
  omega

section Lines

variable {f g : K →+ K} {Γ : K × K →+ K × K}

theorem gamma_line (hE : ∀ r s, Γ (r * s, r ^ 2 * s) = (f r * g s, f r ^ 2 * g s)) {r x : K}
    (hr : r ≠ 0) : Γ (x, r * x) = (f r * g (x / r), f r ^ 2 * g (x / r)) := by
  have h := hE r (x / r)
  rwa [mul_div_cancel₀ _ hr, show r ^ 2 * (x / r) = r * x by field_simp] at h

theorem lines_relation [CharP K 2] (hE : ∀ r s, Γ (r * s, r ^ 2 * s) = (f r * g s, f r ^ 2 * g s))
    {r r' r'' x y z : K} (hr : r ≠ 0) (hr' : r' ≠ 0) (hr'' : r'' ≠ 0) (h1 : x + y = z)
    (h2 : r * x + r' * y = r'' * z) :
    f r * g (x / r) * (f r + f r'') = f r' * g (y / r') * (f r' + f r'') := by
  have hsum : (x, r * x) + (y, r' * y) = (z, r'' * z) := by
    ext
    · exact h1
    · exact h2
  have h := congrArg Γ hsum
  rw [map_add, gamma_line hE hr, gamma_line hE hr', gamma_line hE hr''] at h
  have e1 := congrArg Prod.fst h
  have e2 := congrArg Prod.snd h
  simp only [Prod.fst_add, Prod.snd_add] at e1 e2
  have h2' : (2 : K) = 0 := charTwo_two_eq_zero
  linear_combination e2 - f r'' * e1 + (f r * g (x / r) * f r'' - f r' * g (y / r') * f r') * h2'

end Lines

section LemmaC

variable [CharP K 2] {f g : K →+ K} {Γ : K × K →+ K × K}

theorem g_mul_of_lines (hf : Function.Injective f)
    (hE : ∀ r s, Γ (r * s, r ^ 2 * s) = (f r * g s, f r ^ 2 * g s))
    {κ ν : K} (hκ0 : κ ≠ 0) (hκ1 : κ ≠ 1) (hν : ν ≠ 0) (h1 : κ * ν ≠ 1) (h2 : κ ^ 2 * ν ≠ 1)
    (u : K) : g (ν * u) * g 1 = g ν * g u := by
  have h2' : (2 : K) = 0 := charTwo_two_eq_zero
  have hden : (1 : K) + κ * ν ≠ 0 := fun h => h1 (by linear_combination h - h2')
  have hnum : κ ^ 2 * ν + 1 ≠ 0 := fun h => h2 (by linear_combination h - h2')
  set ρ₀ : K := (κ ^ 2 * ν + 1) / (1 + κ * ν) with hρ₀
  have hkey : ρ₀ * (1 + κ * ν) = κ ^ 2 * ν + 1 := div_mul_cancel₀ _ hden
  have hρ0 : ρ₀ ≠ 0 := div_ne_zero hnum hden
  have hrel : ∀ w : K, f 1 * (f 1 + f ρ₀) * g w = f κ * (f κ + f ρ₀) * g (ν * w) := by
    intro w
    have hr := lines_relation hE (r := 1) (r' := κ) (r'' := ρ₀) (x := w) (y := κ * ν * w)
      (z := w + κ * ν * w) one_ne_zero hκ0 hρ0 rfl
      (by linear_combination (-w) * hkey)
    rw [div_one, show κ * ν * w / κ = ν * w by field_simp] at hr
    linear_combination hr
  have hf0 : ∀ a : K, f a = 0 → a = 0 := (injective_iff_map_eq_zero f).1 hf
  have hfκ : f κ ≠ 0 := fun h => hκ0 (hf0 κ h)
  have hρκ : ρ₀ ≠ κ := by
    intro h
    rw [h] at hkey
    exact hκ1 (by linear_combination hkey)
  have hfκρ : f κ + f ρ₀ ≠ 0 := by
    rw [← map_add]
    intro h
    exact hρκ (by linear_combination hf0 _ h - κ * h2')
  have hB : f κ * (f κ + f ρ₀) ≠ 0 := mul_ne_zero hfκ hfκρ
  have := hrel u
  have h1' := hrel 1
  rw [mul_one] at h1'
  apply mul_left_cancel₀ hB
  linear_combination (-(g 1)) * this + (g u) * h1'

theorem exists_ringHom_of_lines [Finite K] (hq : 8 ≤ Nat.card K) (hf : Function.Injective f)
    (hg : Function.Injective g) (hE : ∀ r s, Γ (r * s, r ^ 2 * s) = (f r * g s, f r ^ 2 * g s)) :
    ∃ σ : K →+* K, ∀ z, g z = g 1 * σ z := by
  classical
  have hg0 : ∀ a : K, g a = 0 → a = 0 := (injective_iff_map_eq_zero g).1 hg
  have hg1 : g 1 ≠ 0 := fun h => one_ne_zero (hg0 1 h)
  obtain ⟨κ, hκ⟩ := exists_avoid ({0, 1} : Finset K) (by
    have := Finset.card_le_two (a := (0 : K)) (b := 1)
    omega)
  have hκ0 : κ ≠ 0 := fun h => hκ (by simp [h])
  have hκ1 : κ ≠ 1 := fun h => hκ (by simp [h])
  set σz : K → K := fun z => g z / g 1 with hσz
  have hσ1 : σz 1 = 1 := div_self hg1
  have hbig : ∀ ν : K, κ * ν ≠ 1 → κ ^ 2 * ν ≠ 1 → ∀ u, σz (ν * u) = σz ν * σz u := by
    intro ν h1 h2 u
    by_cases hν : ν = 0
    · simp [hσz, hν]
    · have := g_mul_of_lines hf hE hκ0 hκ1 hν h1 h2 u
      simp only [hσz]
      field_simp
      linear_combination this
  have hclos : ∀ ν₁ ν₂ : K, (∀ u, σz (ν₁ * u) = σz ν₁ * σz u) →
      (∀ u, σz (ν₂ * u) = σz ν₂ * σz u) → ∀ u, σz (ν₁ * ν₂ * u) = σz (ν₁ * ν₂) * σz u := by
    intro ν₁ ν₂ h₁ h₂ u
    have e1 : σz (ν₁ * ν₂) = σz ν₁ * σz ν₂ := by simpa [hσ1] using h₁ ν₂
    rw [mul_assoc, h₁, h₂, e1, mul_assoc]
  have hall : ∀ ν u, σz (ν * u) = σz ν * σz u := by
    intro ν u
    by_cases hν : κ * ν ≠ 1 ∧ κ ^ 2 * ν ≠ 1
    · exact hbig ν hν.1 hν.2 u
    · obtain ⟨ν₁, hν₁⟩ := exists_avoid
        ({0, κ⁻¹, (κ ^ 2)⁻¹, κ * ν, κ ^ 2 * ν} : Finset K) (by
          have := Finset.card_le_five (a := (0 : K)) (b := κ⁻¹) (c := (κ ^ 2)⁻¹)
            (d := κ * ν) (e := κ ^ 2 * ν)
          omega)
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hν₁
      obtain ⟨h0, h1, h2, h3, h4⟩ := hν₁
      have hκ2 : κ ^ 2 ≠ 0 := pow_ne_zero 2 hκ0
      have hν₁' : κ * ν₁ ≠ 1 := fun h => h1 (by field_simp; linear_combination h)
      have hν₁'' : κ ^ 2 * ν₁ ≠ 1 := fun h => h2 (by field_simp; linear_combination h)
      have hν₂ : κ * (ν / ν₁) ≠ 1 := fun h => h3 (by field_simp at h; linear_combination -h)
      have hν₂' : κ ^ 2 * (ν / ν₁) ≠ 1 := fun h => h4 (by field_simp at h; linear_combination -h)
      have := hclos ν₁ (ν / ν₁) (hbig ν₁ hν₁' hν₁'') (hbig _ hν₂ hν₂') u
      rwa [mul_div_cancel₀ _ h0] at this
  let σ : K →+* K :=
    { toFun := σz
      map_one' := hσ1
      map_mul' := fun a b => hall a b
      map_zero' := by simp [hσz]
      map_add' := fun a b => by simp [hσz, add_div] }
  refine ⟨σ, fun z => ?_⟩
  show g z = g 1 * (g z / g 1)
  field_simp

end LemmaC

section Rho

variable [Finite K] [CharP K 2]

@[expose] noncomputable def rhoEquiv (K : Type*) [Field K] [Finite K] [CharP K 2] :
    K × K ≃+ K × K where
  toFun p := (p.2, p.1 ^ 2)
  invFun p := ((frobeniusEquiv K 2).symm p.2, p.1)
  left_inv p := by
    refine Prod.ext ?_ rfl
    exact (frobeniusEquiv K 2).symm_apply_apply p.1
  right_inv p := by
    refine Prod.ext rfl ?_
    exact (frobeniusEquiv K 2).apply_symm_apply p.2
  map_add' p q := by
    refine Prod.ext rfl ?_
    exact CharTwo.add_sq p.1 q.1

theorem rhoEquiv_apply (p : K × K) : rhoEquiv K p = (p.2, p.1 ^ 2) := rfl

theorem rhoEquiv_beta (x y : K × K) :
    rhoEquiv K (beta x y) = beta (rhoEquiv K x) (rhoEquiv K y) := by
  simp only [rhoEquiv_apply, beta]
  refine Prod.ext ?_ ?_
  · simp only
    ring
  · simp only
    rw [CharTwo.add_sq]
    ring

theorem rhoEquiv_symm_beta (x y : K × K) :
    (rhoEquiv K).symm (beta x y) = beta ((rhoEquiv K).symm x) ((rhoEquiv K).symm y) := by
  apply (rhoEquiv K).injective
  rw [AddEquiv.apply_symm_apply, rhoEquiv_beta, AddEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply]

theorem exists_ringHom_of_lines' {f g : K →+ K} {Γ : K × K →+ K × K} (hq : 8 ≤ Nat.card K)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hE : ∀ r s, Γ (r * s, r ^ 2 * s) = (f r * g s, f r ^ 2 * g s)) :
    ∃ τ : K →+* K, ∀ r, f r = f 1 * τ r := by
  set Φ := frobeniusEquiv K 2 with hΦ
  have hΦapp : ∀ x : K, Φ x = x ^ 2 := fun x => rfl
  let g' : K →+ K := Φ.toRingHom.toAddMonoidHom.comp (f.comp Φ.symm.toRingHom.toAddMonoidHom)
  let Γ' : K × K →+ K × K :=
    (rhoEquiv K).toAddMonoidHom.comp (Γ.comp (rhoEquiv K).symm.toAddMonoidHom)
  have hg'inj : Function.Injective g' := Φ.injective.comp (hf.comp Φ.symm.injective)
  have hg'app : ∀ s₀ : K, g' (s₀ ^ 2) = f s₀ ^ 2 := fun s₀ => by
    show Φ (f (Φ.symm (s₀ ^ 2))) = f s₀ ^ 2
    rw [← hΦapp s₀, Φ.symm_apply_apply]
    rfl
  have hE' : ∀ r s, Γ' (r * s, r ^ 2 * s) = (g r * g' s, g r ^ 2 * g' s) := by
    intro r s
    obtain ⟨s₀, rfl⟩ := Φ.surjective s
    rw [hΦapp s₀, hg'app s₀]
    have h1 : (rhoEquiv K).symm (r * s₀ ^ 2, r ^ 2 * s₀ ^ 2) = (s₀ * r, s₀ ^ 2 * r) := by
      refine Prod.ext ?_ ?_
      · show Φ.symm (r ^ 2 * s₀ ^ 2) = s₀ * r
        have : r ^ 2 * s₀ ^ 2 = Φ (s₀ * r) := by rw [hΦapp]; ring
        rw [this, Φ.symm_apply_apply]
      · show r * s₀ ^ 2 = s₀ ^ 2 * r
        ring
    show (rhoEquiv K) (Γ ((rhoEquiv K).symm (r * s₀ ^ 2, r ^ 2 * s₀ ^ 2))) = _
    rw [h1, hE s₀ r, rhoEquiv_apply]
    refine Prod.ext ?_ ?_
    · show f s₀ ^ 2 * g r = g r * f s₀ ^ 2
      ring
    · show (f s₀ * g r) ^ 2 = g r ^ 2 * f s₀ ^ 2
      ring
  obtain ⟨σ', hσ'⟩ := exists_ringHom_of_lines hq hg hg'inj hE'
  refine ⟨σ', fun r => ?_⟩
  have h := hσ' (r ^ 2)
  have e2 : g' 1 = f 1 ^ 2 := by
    have := hg'app 1
    rwa [one_pow] at this
  rw [hg'app r, e2, map_pow] at h
  have h' : f r ^ 2 = (f 1 * σ' r) ^ 2 := by rw [mul_pow]; exact h
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h' with h3 | h3
  · exact h3
  · rw [h3, CharTwo.neg_eq]

end Rho

section Twist

variable [CharP K 2] [Finite K]

theorem twist_eq {f g : K →+ K} {Γ : K × K →+ K × K} (hq : 8 ≤ Nat.card K)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hE : ∀ r s, Γ (r * s, r ^ 2 * s) = (f r * g s, f r ^ 2 * g s)) {τ σ : K →+* K}
    (hτ : ∀ r, f r = f 1 * τ r) (hσ : ∀ s, g s = g 1 * σ s) : τ = σ := by
  classical
  have h2' : (2 : K) = 0 := charTwo_two_eq_zero
  have hf0 : ∀ a : K, f a = 0 → a = 0 := (injective_iff_map_eq_zero f).1 hf
  have hg0 : ∀ a : K, g a = 0 → a = 0 := (injective_iff_map_eq_zero g).1 hg
  have hf1 : f 1 ≠ 0 := fun h => one_ne_zero (hf0 1 h)
  have hg1 : g 1 ≠ 0 := fun h => one_ne_zero (hg0 1 h)
  obtain ⟨κ, hκ⟩ := exists_avoid ({0, 1} : Finset K) (by
    have := Finset.card_le_two (a := (0 : K)) (b := 1)
    omega)
  have hκ0 : κ ≠ 0 := fun h => hκ (by simp [h])
  have hκ1 : κ ≠ 1 := fun h => hκ (by simp [h])
  have hσκ : σ κ ≠ 0 := (map_ne_zero σ).2 hκ0
  have hrel : ∀ z : K, z ≠ 0 →
      σ (κ + z) * σ κ * τ (1 + z) = τ κ * σ (1 + z) * τ (κ + z) := by
    intro z hz
    have h := lines_relation hE (r := 1) (r' := κ) (r'' := z) (x := κ + z) (y := 1 + z)
      (z := 1 + κ) one_ne_zero hκ0 hz (by linear_combination z * h2')
      (by linear_combination κ * h2')
    rw [div_one, hτ z, hτ κ, hσ (κ + z), hσ ((1 + z) / κ), map_div₀] at h
    have e1 : f 1 + f 1 * τ z = f 1 * τ (1 + z) := by rw [τ.map_add, τ.map_one]; ring
    have e2 : f 1 * τ κ + f 1 * τ z = f 1 * τ (κ + z) := by rw [τ.map_add]; ring
    rw [e1, e2] at h
    have hc : f 1 ^ 2 * g 1 ≠ 0 := mul_ne_zero (pow_ne_zero 2 hf1) hg1
    apply mul_left_cancel₀ hc
    field_simp at h ⊢
    linear_combination h
  let Λ : K →+ K := AddMonoidHom.mk' (fun c => τ c * σ κ - τ κ * σ c) (by
    intro a b
    simp only [map_add]
    ring)
  have hΛapp : ∀ c, Λ c = τ c * σ κ - τ κ * σ c := fun c => rfl
  have hΛ : ∀ c : K, c ≠ 0 → c ≠ 1 → κ * c ≠ 1 → Λ c = 0 := by
    intro c hc0 hc1 hκc
    have hc1' : c + 1 ≠ 0 := fun h => hc1 (by linear_combination h - h2')
    have hκc' : κ * c + 1 ≠ 0 := fun h => hκc (by linear_combination h - h2')
    set z : K := (κ * c + 1) / (c + 1) with hz
    have hzdef : z * (c + 1) = κ * c + 1 := div_mul_cancel₀ _ hc1'
    have hz0 : z ≠ 0 := div_ne_zero hκc' hc1'
    have hκz : κ + z ≠ 0 := by
      intro h
      have hzκ : z = κ := by linear_combination h - κ * h2'
      rw [hzκ] at hzdef
      exact hκ1 (by linear_combination hzdef)
    have h1z : 1 + z = c * (κ + z) := by
      apply mul_left_cancel₀ hc1'
      linear_combination (1 - c) * hzdef + (1 - κ * c ^ 2) * h2'
    have := hrel z hz0
    rw [h1z, map_mul, map_mul] at this
    rw [hΛapp]
    have hne : σ (κ + z) * τ (κ + z) ≠ 0 :=
      mul_ne_zero ((map_ne_zero σ).2 hκz) ((map_ne_zero τ).2 hκz)
    apply mul_left_cancel₀ hne
    linear_combination this
  have hgood : ∀ d : K, d ≠ 1 → κ * d ≠ 1 → Λ d = 0 := by
    intro d hd1 hκd
    by_cases hd0 : d = 0
    · rw [hd0, map_zero]
    · exact hΛ d hd0 hd1 hκd
  have hall : ∀ c : K, Λ c = 0 := by
    intro c
    obtain ⟨d, hd⟩ := exists_avoid ({1, κ⁻¹, c + 1, c + κ⁻¹} : Finset K) (by
      have := Finset.card_le_four (a := (1 : K)) (b := κ⁻¹) (c := c + 1) (d := c + κ⁻¹)
      omega)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd
    obtain ⟨hd1, hd2, hd3, hd4⟩ := hd
    have hs : κ * κ⁻¹ = 1 := mul_inv_cancel₀ hκ0
    have hκd : κ * d ≠ 1 := fun h => hd2 (mul_left_cancel₀ hκ0 (h.trans hs.symm))
    have hcd1 : c + d ≠ 1 := fun h => hd3 (by linear_combination h - c * h2')
    have hκcd : κ * (c + d) ≠ 1 := fun h => hd4 (by
      have := mul_left_cancel₀ hκ0 (h.trans hs.symm)
      linear_combination this - c * h2')
    have e : Λ c = Λ (c + d) - Λ d := by rw [← map_sub, add_sub_cancel_right]
    rw [e, hgood _ hcd1 hκcd, hgood d hd1 hκd, sub_zero]
  have h1 : σ κ = τ κ := by
    have := hall 1
    rw [hΛapp, τ.map_one, σ.map_one] at this
    linear_combination this
  ext c
  have hc := hall c
  rw [hΛapp, ← h1] at hc
  apply mul_right_cancel₀ hσκ
  linear_combination hc

end Twist

section CL

variable [CharP K 2] [Finite K]

theorem cl_diag_W (hq : 8 ≤ Nat.card K) {gb Γ : K × K →+ K × K}
    (hcomp : ∀ x y, Γ (beta x y) = beta (gb x) (gb y))
    (hax : (∀ r, (gb (r, 0)).2 = 0) ∧ ∀ s, (gb (0, s)).1 = 0)
    (hbij : Function.Bijective gb) : IsDiagForm gb := by
  let f : K →+ K := (AddMonoidHom.fst K K).comp (gb.comp (AddMonoidHom.inl K K))
  let g : K →+ K := (AddMonoidHom.snd K K).comp (gb.comp (AddMonoidHom.inr K K))
  have hfapp : ∀ r, f r = (gb (r, 0)).1 := fun r => rfl
  have hgapp : ∀ s, g s = (gb (0, s)).2 := fun s => rfl
  have hgb : ∀ r s, gb (r, s) = (f r, g s) := by
    intro r s
    have e : (r, s) = (r, 0) + (0, s) := by simp
    rw [e, map_add]
    refine Prod.ext ?_ ?_
    · show (gb (r, 0)).1 + (gb (0, s)).1 = f r
      rw [hax.2 s, add_zero, hfapp]
    · show (gb (r, 0)).2 + (gb (0, s)).2 = g s
      rw [hax.1 r, zero_add, hgapp]
  have hf : Function.Injective f := by
    intro r r' h
    have : gb (r, 0) = gb (r', 0) := by
      rw [hgb, hgb, h]
    have := hbij.1 this
    exact (Prod.mk.inj this).1
  have hg : Function.Injective g := by
    intro s s' h
    have : gb (0, s) = gb (0, s') := by
      rw [hgb, hgb, h]
    have := hbij.1 this
    exact (Prod.mk.inj this).2
  have hE : ∀ r s, Γ (r * s, r ^ 2 * s) = (f r * g s, f r ^ 2 * g s) := by
    intro r s
    have h := hcomp (r, 0) (0, s)
    rw [beta_fst_zero, hgb r 0, hgb 0 s, map_zero, map_zero, beta_fst_zero] at h
    exact h
  obtain ⟨σ, hσ⟩ := exists_ringHom_of_lines hq hf hg hE
  obtain ⟨τ, hτ⟩ := exists_ringHom_of_lines' hq hf hg hE
  have hτσ := twist_eq hq hf hg hE hτ hσ
  have hf0 : ∀ a : K, f a = 0 → a = 0 := (injective_iff_map_eq_zero f).1 hf
  have hg0 : ∀ a : K, g a = 0 → a = 0 := (injective_iff_map_eq_zero g).1 hg
  refine ⟨f 1, g 1, σ, fun h => one_ne_zero (hf0 1 h), fun h => one_ne_zero (hg0 1 h),
    fun r s => ?_⟩
  rw [hgb, hτ r, hσ s, hτσ]

theorem cl_swap_W (hq : 8 ≤ Nat.card K) {gb Γ : K × K →+ K × K}
    (hcomp : ∀ x y, Γ (beta x y) = beta (gb x) (gb y))
    (hax : (∀ r, (gb (r, 0)).1 = 0) ∧ ∀ s, (gb (0, s)).2 = 0)
    (hbij : Function.Bijective gb) : IsSwapForm gb := by
  let gb' : K × K →+ K × K := (rhoEquiv K).symm.toAddMonoidHom.comp gb
  let Γ' : K × K →+ K × K := (rhoEquiv K).symm.toAddMonoidHom.comp Γ
  have hcomp' : ∀ x y, Γ' (beta x y) = beta (gb' x) (gb' y) := by
    intro x y
    show (rhoEquiv K).symm (Γ (beta x y)) = beta ((rhoEquiv K).symm (gb x))
      ((rhoEquiv K).symm (gb y))
    rw [hcomp, rhoEquiv_symm_beta]
  have hax' : (∀ r, (gb' (r, 0)).2 = 0) ∧ ∀ s, (gb' (0, s)).1 = 0 := by
    refine ⟨fun r => ?_, fun s => ?_⟩
    · show ((rhoEquiv K).symm (gb (r, 0))).2 = 0
      exact hax.1 r
    · show (frobeniusEquiv K 2).symm (gb (0, s)).2 = 0
      rw [hax.2 s, map_zero]
  have hbij' : Function.Bijective gb' := (rhoEquiv K).symm.bijective.comp hbij
  obtain ⟨a, b, σ, ha, hb, h⟩ := cl_diag_W hq hcomp' hax' hbij'
  refine ⟨a, b, σ, ha, hb, fun r s => ?_⟩
  have e : gb (r, s) = rhoEquiv K (gb' (r, s)) := by
    show gb (r, s) = rhoEquiv K ((rhoEquiv K).symm (gb (r, s)))
    rw [AddEquiv.apply_symm_apply]
  rw [e, h, rhoEquiv_apply, mul_pow]

end CL

section Image

variable [CharP K 2] [Finite K]

@[expose] def uMap (a : K) (σ : K →+* K) : K →+ K :=
  AddMonoidHom.mk' (fun r => a * σ r + r) (by
    intro x y
    simp only [map_add]
    ring)

omit [CharP K 2] in
theorem card_fixed_sq_le {σ : K →+* K} (hσ : σ ≠ RingHom.id K) :
    Nat.card {e : K | σ e = e} ^ 2 ≤ Nat.card K := by
  obtain ⟨x, hx⟩ : ∃ x : K, σ x ≠ x := by
    by_contra h
    push Not at h
    exact hσ (RingHom.ext h)
  have hinj : Function.Injective
      (fun p : {e : K | σ e = e} × {e : K | σ e = e} => (p.1 : K) + x * p.2) := by
    rintro ⟨⟨e₁, h₁⟩, ⟨e₂, h₂⟩⟩ ⟨⟨e₁', h₁'⟩, ⟨e₂', h₂'⟩⟩ h
    simp only at h
    have h₂₂ : e₂ = e₂' := by
      by_contra hne
      have hne' : e₂ - e₂' ≠ 0 := sub_ne_zero.2 hne
      apply hx
      have hxe : x = (e₁' - e₁) / (e₂ - e₂') := by
        field_simp
        linear_combination h
      rw [hxe, map_div₀, map_sub, map_sub, h₁, h₂, h₁', h₂']
    subst h₂₂
    have : e₁ = e₁' := by linear_combination h
    subst this
    rfl
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_prod, ← sq] at this

theorem card_ker_uMap_le {σ : K →+* K} {a : K} :
    Nat.card (uMap a σ).ker ≤ Nat.card {e : K | σ e = e} := by
  by_cases hex : ∃ r₁ ∈ (uMap a σ).ker, r₁ ≠ 0
  · obtain ⟨r₁, hr₁, hr₁0⟩ := hex
    have h2' : (2 : K) = 0 := charTwo_two_eq_zero
    have hker : ∀ r ∈ (uMap a σ).ker, a * σ r = r := by
      intro r hr
      have : a * σ r + r = 0 := hr
      linear_combination this - r * h2'
    have hσr₁ : σ r₁ ≠ 0 := (map_ne_zero σ).2 hr₁0
    refine Nat.card_le_card_of_injective (fun r => ⟨(r : K) / r₁, ?_⟩) ?_
    · show σ ((r : K) / r₁) = (r : K) / r₁
      have e1 := hker r r.2
      have e2 := hker r₁ hr₁
      rw [map_div₀]
      field_simp
      linear_combination σ r₁ * e1 - σ ↑r * e2
    · intro r r' h
      have h' : (r : K) / r₁ = (r' : K) / r₁ := congrArg Subtype.val h
      exact Subtype.ext ((div_left_inj' hr₁0).1 h')
  · push Not at hex
    have : Nat.card (uMap a σ).ker = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun x y => Subtype.ext ?_⟩, ⟨⟨0, (uMap a σ).ker.zero_mem⟩⟩⟩
      rw [hex x x.2, hex y y.2]
    rw [this]
    have : Nonempty {e : K | σ e = e} := ⟨⟨0, by simp⟩⟩
    exact Nat.card_pos

omit [Finite K] in
theorem card_ker_uMap_id {a : K} :
    (a = 1 → Nat.card (uMap a (RingHom.id K)).ker = Nat.card K) ∧
      (a ≠ 1 → Nat.card (uMap a (RingHom.id K)).ker = 1) := by
  have h2' : (2 : K) = 0 := charTwo_two_eq_zero
  constructor
  · intro ha
    have : (uMap a (RingHom.id K)).ker = ⊤ := by
      refine (AddSubgroup.eq_top_iff' _).2 fun r => ?_
      show a * r + r = 0
      rw [ha]
      linear_combination r * h2'
    rw [this, AddSubgroup.card_top]
  · intro ha
    have hne : a + 1 ≠ 0 := fun h => ha (by linear_combination h - h2')
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y => Subtype.ext ?_⟩, ⟨⟨0, (uMap a (RingHom.id K)).ker.zero_mem⟩⟩⟩
    have hz : ∀ r : K, a * r + r = 0 → r = 0 := by
      intro r hr
      have : (a + 1) * r = 0 := by linear_combination hr
      exact (mul_eq_zero.1 this).resolve_left hne
    exact (hz x x.2).trans (hz y y.2).symm

theorem card_ker_mul_le {a b : K} {σ : K →+* K}
    (hne : ¬ (a = 1 ∧ b = 1 ∧ σ = RingHom.id K)) :
    Nat.card (uMap a σ).ker * Nat.card (uMap b σ).ker ≤ Nat.card K := by
  by_cases hσ : σ = RingHom.id K
  · subst hσ
    have hle : ∀ c : K, Nat.card (uMap c (RingHom.id K)).ker ≤ Nat.card K := fun c =>
      Nat.card_le_card_of_injective _ Subtype.val_injective
    by_cases ha1 : a = 1
    · have hb1 : b ≠ 1 := fun h => hne ⟨ha1, h, rfl⟩
      rw [card_ker_uMap_id.1 ha1, card_ker_uMap_id.2 hb1, mul_one]
    · rw [card_ker_uMap_id.2 ha1, one_mul]
      exact hle b
  · have h1 := card_fixed_sq_le hσ
    have h2 : Nat.card (uMap a σ).ker ^ 2 ≤ Nat.card K :=
      (Nat.pow_le_pow_left card_ker_uMap_le 2).trans h1
    have h3 : Nat.card (uMap b σ).ker ^ 2 ≤ Nat.card K :=
      (Nat.pow_le_pow_left card_ker_uMap_le 2).trans h1
    have h4 : (Nat.card (uMap a σ).ker * Nat.card (uMap b σ).ker) ^ 2 ≤ Nat.card K ^ 2 := by
      rw [mul_pow, sq (Nat.card K)]
      exact Nat.mul_le_mul h2 h3
    exact (Nat.pow_le_pow_iff_left (by norm_num)).1 h4

theorem card_image_ge (hq : 8 ≤ Nat.card K) {gb : K × K →+ K × K}
    (hform : IsDiagForm gb ∨ IsSwapForm gb) (hne : gb ≠ AddMonoidHom.id (K × K)) :
    4 < (Set.range (gb + AddMonoidHom.id (K × K))).ncard := by
  have hfin : (Set.range (gb + AddMonoidHom.id (K × K))).Finite := Set.finite_range _
  rcases hform with ⟨a, b, σ, ha, hb, h⟩ | ⟨a, b, σ, ha, hb, h⟩
  ·
    have hrange : Set.range (gb + AddMonoidHom.id (K × K)) =
        Set.range (uMap a σ) ×ˢ Set.range (uMap b σ) := by
      ext ⟨x, y⟩
      constructor
      · rintro ⟨⟨r, s⟩, hrs⟩
        have h1 : (a * σ r + r, b * σ s + s) = (x, y) := by
          rw [← hrs, AddMonoidHom.add_apply, h]
          rfl
        exact ⟨⟨r, congrArg Prod.fst h1⟩, ⟨s, congrArg Prod.snd h1⟩⟩
      · rintro ⟨⟨r, hr⟩, ⟨s, hs⟩⟩
        refine ⟨(r, s), ?_⟩
        rw [AddMonoidHom.add_apply, h]
        exact Prod.ext hr hs
    have hne' : ¬ (a = 1 ∧ b = 1 ∧ σ = RingHom.id K) := by
      rintro ⟨rfl, rfl, rfl⟩
      apply hne
      ext p
      · simp [h]
      · simp [h]
    have hker := card_ker_mul_le hne'
    have hu := AddSubgroup.card_ker_mul_card_range (uMap a σ)
    have hv := AddSubgroup.card_ker_mul_card_range (uMap b σ)
    rw [hrange, Set.ncard_prod]
    have e1 : (Set.range (uMap a σ)).ncard = Nat.card (uMap a σ).range := by
      rw [← Nat.card_coe_set_eq]; rfl
    have e2 : (Set.range (uMap b σ)).ncard = Nat.card (uMap b σ).range := by
      rw [← Nat.card_coe_set_eq]; rfl
    rw [e1, e2]
    set ku := Nat.card (uMap a σ).ker
    set kv := Nat.card (uMap b σ).ker
    set ru := Nat.card (uMap a σ).range
    set rv := Nat.card (uMap b σ).range
    have hq0 : 0 < Nat.card K := Nat.card_pos
    have : ru * rv * (ku * kv) = Nat.card K * Nat.card K := by
      calc ru * rv * (ku * kv) = (ku * ru) * (kv * rv) := by ring
        _ = Nat.card K * Nat.card K := by rw [hu, hv]
    have h5 : Nat.card K * Nat.card K ≤ ru * rv * Nat.card K := by
      rw [← this]
      exact Nat.mul_le_mul_left _ hker
    have h6 : Nat.card K ≤ ru * rv := Nat.le_of_mul_le_mul_right h5 hq0
    omega
  ·
    have hsub : Set.range (fun r : K => (gb + AddMonoidHom.id (K × K)) (r, 0)) ⊆
        Set.range (gb + AddMonoidHom.id (K × K)) := fun _ ⟨r, hr⟩ => ⟨(r, 0), hr⟩
    have hinj : Function.Injective (fun r : K => (gb + AddMonoidHom.id (K × K)) (r, 0)) := by
      intro r r' hrr
      have := congrArg Prod.fst hrr
      simp only [AddMonoidHom.add_apply, h, AddMonoidHom.id_apply, map_zero, mul_zero,
        Prod.fst_add, zero_add] at this
      exact this
    have h1 := Set.ncard_le_ncard hsub hfin
    have h2 : (Set.range (fun r : K => (gb + AddMonoidHom.id (K × K)) (r, 0))).ncard =
        Nat.card K := by
      rw [← Nat.card_coe_set_eq, Nat.card_range_of_injective hinj]
    omega

end Image

end CFSG.CGT.PushingUpLit.A78Sp4
