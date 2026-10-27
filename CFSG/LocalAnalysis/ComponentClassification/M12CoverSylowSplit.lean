module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverSylow

public section

namespace CFSG.ComponentClassification.M12Cover

@[expose] def InvolutionCocyclesSplit (Q : Type*) [Group Q] : Prop :=
  ∀ f : Q → Q → ZMod 2, (∀ b, f 1 b = 0) → (∀ a, f a 1 = 0) →
    (∀ a b c, f a b + f (a * b) c = f b c + f a (b * c)) → (∀ q, orderOf q = 2 → f q q = 0) →
    ∃ μ : Q → ZMod 2, ∀ a b, f a b = μ a + μ b + μ (a * b)

theorem involutionCocyclesSplit_S : InvolutionCocyclesSplit S :=
  fun f hl hr hc hd => exists_coboundary f hl hr hc hd

theorem InvolutionCocyclesSplit.of_mulEquiv {Q Q' : Type*} [Group Q] [Group Q'] (e : Q ≃* Q')
    (h : InvolutionCocyclesSplit Q') : InvolutionCocyclesSplit Q := by
  intro f hl hr hc hd
  obtain ⟨μ, hμ⟩ := h (fun a b => f (e.symm a) (e.symm b)) (fun b => by simpa using hl _)
    (fun a => by simpa using hr _) (fun a b c => by simpa using hc _ _ _)
    (fun q hq => hd _ (by rwa [MulEquiv.orderOf_eq]))
  refine ⟨fun a => μ (e a), fun a b => ?_⟩
  simpa using hμ (e a) (e b)

section Splitting

variable {Q E : Type*} [Group Q] [Group E] {t : E}

theorem eq_one_or_eq_of_mem_zpowers (ht : orderOf t = 2) {x : E}
    (hx : x ∈ Subgroup.zpowers t) : x = 1 ∨ x = t := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  rw [← zpow_mod_orderOf, ht]
  rcases Int.emod_two_eq_zero_or_one k with h | h <;> rw [Nat.cast_ofNat, h] <;> simp

theorem exists_section_of_cocycles (hQ : InvolutionCocyclesSplit Q) (ρ : E →* Q)
    (hρ : Function.Surjective ρ) (ht : orderOf t = 2) (htZ : t ∈ Subgroup.center E)
    (hker : ρ.ker = Subgroup.zpowers t) (hinv : ∀ e : E, orderOf (ρ e) = 2 → orderOf e = 2) :
    ∃ σ : Q →* E, ∀ q, ρ (σ q) = q := by
  classical
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    exact absurd ht (by norm_num)
  let τ : ZMod 2 → E := fun z => t ^ z.val
  have τ_add : ∀ z w, τ (z + w) = τ z * τ w := by
    intro z w
    have h := pow_mod_orderOf t (z.val + w.val)
    rw [ht] at h
    simp only [τ, ZMod.val_add, ← pow_add, h]
  have τ_zero : τ 0 = 1 := by simp [τ]
  have τ_one : τ 1 = t := by simp [τ, ZMod.val_one]
  have τ_inj : ∀ z w, τ z = τ w → z = w := by
    intro z w h
    fin_cases z <;> fin_cases w
    · rfl
    · exact absurd (τ_zero.symm.trans (h.trans τ_one)) ht1.symm
    · exact absurd (τ_one.symm.trans (h.trans τ_zero)) ht1
    · rfl
  have τ_mem : ∀ z, τ z ∈ Subgroup.zpowers t := fun z => pow_mem (Subgroup.mem_zpowers t) _
  have τ_ker : ∀ z, ρ (τ z) = 1 := fun z => by
    rw [← MonoidHom.mem_ker, hker]
    exact τ_mem z
  have τ_comm : ∀ z x, x * τ z = τ z * x := fun z x =>
    Subgroup.mem_center_iff.1 (pow_mem htZ _) x
  let u : Q → E := fun q => if q = 1 then 1 else Function.surjInv hρ q
  have hu : ∀ q, ρ (u q) = q := by
    intro q
    by_cases h : q = 1
    · simp [u, h]
    · simp only [u, h, ↓reduceIte]
      exact Function.surjInv_eq hρ q
  have hu1 : u 1 = 1 := by simp [u]
  let f : Q → Q → ZMod 2 := fun a b => if u a * u b = u (a * b) then 0 else 1
  have hf : ∀ a b, u a * u b = τ (f a b) * u (a * b) := by
    intro a b
    by_cases h : u a * u b = u (a * b)
    · simp [f, h, τ_zero]
    · have hmem : u a * u b * (u (a * b))⁻¹ ∈ Subgroup.zpowers t := by
        rw [← hker, MonoidHom.mem_ker]
        simp [hu]
      rcases eq_one_or_eq_of_mem_zpowers ht hmem with h1 | h1
      · exact absurd (mul_inv_eq_one.1 h1) h
      · simp only [f, h, ↓reduceIte, τ_one]
        rw [← h1, inv_mul_cancel_right]
  have hl : ∀ b, f 1 b = 0 := fun b => by simp [f, hu1]
  have hr : ∀ a, f a 1 = 0 := fun a => by simp [f, hu1]
  have hc : ∀ a b c, f a b + f (a * b) c = f b c + f a (b * c) := by
    intro a b c
    apply τ_inj
    have h1 : u a * u b * u c = τ (f a b + f (a * b) c) * u (a * b * c) := by
      rw [hf a b, mul_assoc, hf (a * b) c, ← mul_assoc, τ_add]
    have h2 : u a * u b * u c = τ (f b c + f a (b * c)) * u (a * (b * c)) := by
      rw [mul_assoc, hf b c, ← mul_assoc, τ_comm, mul_assoc, hf a (b * c), ← mul_assoc, τ_add]
    rw [mul_assoc a b c] at h1
    exact mul_right_cancel (h1.symm.trans h2)
  have hd : ∀ q, orderOf q = 2 → f q q = 0 := by
    intro q hq
    have hq2 : q * q = 1 := by rw [← pow_two, ← hq, pow_orderOf_eq_one]
    have huq : u q * u q = 1 := by
      rw [← pow_two, ← hinv (u q) (by rw [hu]; exact hq), pow_orderOf_eq_one]
    simp [f, huq, hq2, hu1]
  obtain ⟨μ, hμ⟩ := hQ f hl hr hc hd
  let σf : Q → E := fun q => τ (μ q) * u q
  have hσ : ∀ a b, σf (a * b) = σf a * σf b := by
    intro a b
    have hμ' : μ (a * b) = μ a + μ b + f a b := by
      rw [hμ a b]
      grind
    show τ (μ (a * b)) * u (a * b) = τ (μ a) * u a * (τ (μ b) * u b)
    calc τ (μ (a * b)) * u (a * b) = τ (μ a) * τ (μ b) * (τ (f a b) * u (a * b)) := by
          rw [hμ', τ_add, τ_add, mul_assoc]
      _ = τ (μ a) * τ (μ b) * (u a * u b) := by rw [hf a b]
      _ = τ (μ a) * (τ (μ b) * u a) * u b := by simp only [mul_assoc]
      _ = τ (μ a) * u a * (τ (μ b) * u b) := by
          rw [← τ_comm (μ b) (u a)]
          simp only [mul_assoc]
  refine ⟨MonoidHom.mk' σf hσ, fun q => ?_⟩
  simp [σf, τ_ker, hu]

theorem exists_mulEquiv_prod_of_section (ρ : E →* Q) (htZ : t ∈ Subgroup.center E)
    (hker : ρ.ker = Subgroup.zpowers t) (σ : Q →* E) (hσ : ∀ q, ρ (σ q) = q) :
    ∃ φ : Subgroup.zpowers t × Q ≃* E, ∀ z q, φ (z, q) = z * σ q := by
  have hcen : ∀ (z : Subgroup.zpowers t) (x : E), x * z = z * x := fun z x =>
    Subgroup.mem_center_iff.1 (Subgroup.zpowers_le.2 htZ z.2) x
  have hρz : ∀ z : Subgroup.zpowers t, ρ z = 1 := fun z => by
    rw [← MonoidHom.mem_ker, hker]
    exact z.2
  let φ : Subgroup.zpowers t × Q →* E :=
    MonoidHom.mk' (fun p => (p.1 : E) * σ p.2) fun p p' => by
      simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, map_mul, mul_assoc]
      rw [← mul_assoc (p'.1 : E) (σ p.2), ← hcen p'.1 (σ p.2), mul_assoc]
  have hinj : Function.Injective φ := by
    rintro ⟨z, q⟩ ⟨z', q'⟩ h
    have h' : (z : E) * σ q = z' * σ q' := h
    have hq : q = q' := by
      have := congrArg ρ h'
      rwa [map_mul, map_mul, hρz, hρz, hσ, hσ, one_mul, one_mul] at this
    subst hq
    exact Prod.ext (Subtype.ext (mul_right_cancel h')) rfl
  have hsurj : Function.Surjective φ := by
    intro x
    have hmem : x * (σ (ρ x))⁻¹ ∈ Subgroup.zpowers t := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hσ, mul_inv_cancel]
    exact ⟨(⟨_, hmem⟩, ρ x), by simp [φ]⟩
  exact ⟨MulEquiv.ofBijective φ ⟨hinj, hsurj⟩, fun z q => rfl⟩

end Splitting

theorem splits_of_involution_lifts {E : Type*} [Group E] [Finite E] (ρ : E →* ↥S)
    (hρ : Function.Surjective ρ) {t : E} (ht : orderOf t = 2) (htZ : t ∈ Subgroup.center E)
    (hker : ρ.ker = Subgroup.zpowers t)
    (hinv : ∀ e : E, orderOf (ρ e) = 2 → orderOf e = 2) :
    ∃ σ : ↥S →* E, ∀ s, ρ (σ s) = s :=
  exists_section_of_cocycles involutionCocyclesSplit_S ρ hρ ht htZ hker hinv

theorem exists_section_mulEquiv_prod {E : Type*} [Group E] [Finite E] (ρ : E →* ↥S)
    (hρ : Function.Surjective ρ) {t : E} (ht : orderOf t = 2) (htZ : t ∈ Subgroup.center E)
    (hker : ρ.ker = Subgroup.zpowers t)
    (hinv : ∀ e : E, orderOf (ρ e) = 2 → orderOf e = 2) :
    ∃ σ : ↥S →* E, (∀ s, ρ (σ s) = s) ∧
      ∃ φ : Subgroup.zpowers t × ↥S ≃* E, ∀ z s, φ (z, s) = z * σ s := by
  obtain ⟨σ, hσ⟩ := splits_of_involution_lifts ρ hρ ht htZ hker hinv
  exact ⟨σ, hσ, exists_mulEquiv_prod_of_section ρ htZ hker σ hσ⟩

theorem splits_of_involution_lifts_of_mulEquiv {Q E : Type*} [Group Q] [Group E] [Finite E]
    (eQ : Q ≃* ↥S) (ρ : E →* Q) (hρ : Function.Surjective ρ) {t : E} (ht : orderOf t = 2)
    (htZ : t ∈ Subgroup.center E) (hker : ρ.ker = Subgroup.zpowers t)
    (hinv : ∀ e : E, orderOf (ρ e) = 2 → orderOf e = 2) :
    ∃ σ : Q →* E, ∀ q, ρ (σ q) = q :=
  exists_section_of_cocycles (involutionCocyclesSplit_S.of_mulEquiv eQ) ρ hρ ht htZ hker hinv

theorem exists_section_mulEquiv_prod_of_mulEquiv {Q E : Type*} [Group Q] [Group E] [Finite E]
    (eQ : Q ≃* ↥S) (ρ : E →* Q) (hρ : Function.Surjective ρ) {t : E} (ht : orderOf t = 2)
    (htZ : t ∈ Subgroup.center E) (hker : ρ.ker = Subgroup.zpowers t)
    (hinv : ∀ e : E, orderOf (ρ e) = 2 → orderOf e = 2) :
    ∃ σ : Q →* E, (∀ q, ρ (σ q) = q) ∧
      ∃ φ : Subgroup.zpowers t × Q ≃* E, ∀ z q, φ (z, q) = z * σ q := by
  obtain ⟨σ, hσ⟩ := splits_of_involution_lifts_of_mulEquiv eQ ρ hρ ht htZ hker hinv
  exact ⟨σ, hσ, exists_mulEquiv_prod_of_section ρ htZ hker σ hσ⟩

end CFSG.ComponentClassification.M12Cover
