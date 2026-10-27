module

public import CFSG.CGT.PushingUpLit.J42.S5ExtChain

public section

open CFSG.CGT.PushingUpLit.SolK

namespace CFSG.Certificates.Kernel.S5K

theorem perm_apply_inv (s : Equiv.Perm (Fin 32)) (x : Fin 32) : s (s⁻¹ x) = x :=
  s.apply_symm_apply x

@[expose] def autP0 : Subgroup (Equiv.Perm (Fin 32)) where
  carrier := {σ | ∀ i j, σ (extraMulFin i j) = extraMulFin (σ i) (σ j)}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {a b} ha hb i j => by
    simp only [Set.mem_setOf_eq, Equiv.Perm.coe_mul, Function.comp_apply] at *
    rw [hb, ha]
  inv_mem' := fun {a} ha i j => by
    apply a.injective
    rw [ha]
    simp only [perm_apply_inv]

theorem mem_autP0 {σ : Equiv.Perm (Fin 32)} :
    σ ∈ autP0 ↔ ∀ i j, σ (extraMulFin i j) = extraMulFin (σ i) (σ j) :=
  Iff.rfl

@[expose] def IsConjP (i : Fin 32) (σ : Fin 32 → Fin 32) : Prop :=
  ∀ x, extraMulFin (σ x) i = extraMulFin i x

theorem mul_mul_cube : ∀ a i : Fin 32,
    extraMulFin (extraMulFin a i) (extraMulFin i (extraMulFin i i)) = a := by
  decide +kernel

theorem mul_right_cancel {a b i : Fin 32} (h : extraMulFin a i = extraMulFin b i) : a = b := by
  rw [← mul_mul_cube a i, h, mul_mul_cube]

theorem isConjP_unique {i : Fin 32} {σ τ : Fin 32 → Fin 32} (hσ : IsConjP i σ)
    (hτ : IsConjP i τ) : σ = τ :=
  funext fun x => mul_right_cancel ((hσ x).trans (hτ x).symm)

theorem isConjP_conj {s : Equiv.Perm (Fin 32)} (hs : s ∈ autP0) {i : Fin 32}
    {σ : Equiv.Perm (Fin 32)} (h : IsConjP i σ) : IsConjP (s i) ⇑(s * σ * s⁻¹) := by
  intro x
  simp only [Equiv.Perm.coe_mul, Function.comp_apply]
  rw [← hs, h, hs, perm_apply_inv]

theorem card_autP0 {N : ℕ} {tab : ℕ → Fin 32 → Fin 32}
    (hom : ∀ e < N, ∀ i j, tab e (extraMulFin i j) = extraMulFin (tab e i) (tab e j))
    (inj : ∀ e < N, Function.Injective (tab e))
    (complete : ∀ f : Fin 32 → Fin 32, (∀ i j, f (extraMulFin i j) = extraMulFin (f i) (f j)) →
      Function.Injective f → ∃ e, e < N ∧ tab e = f)
    (tab_inj : ∀ e e', e < N → e' < N → tab e = tab e' → e = e') :
    Nat.card autP0 = N := by
  let F : Fin N → autP0 := fun e =>
    ⟨Equiv.ofBijective (tab e) (Finite.injective_iff_bijective.1 (inj e e.2)), hom e e.2⟩
  have hF : Function.Bijective F := by
    refine ⟨fun e e' h => Fin.ext (tab_inj e e' e.2 e'.2 ?_), fun σ => ?_⟩
    · funext x
      exact congrArg (fun τ : autP0 => (τ : Equiv.Perm (Fin 32)) x) h
    · obtain ⟨e, he, hfe⟩ := complete σ σ.2 (σ : Equiv.Perm (Fin 32)).injective
      refine ⟨⟨e, he⟩, Subtype.ext (Equiv.ext fun x => ?_)⟩
      exact congrFun hfe x
  rw [← Nat.card_eq_of_bijective F hF, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem exists_conj_le {G : Type*} [Group G] [Finite G] {U S A : Subgroup G} {a m : ℕ}
    (hU : Nat.card U = 2 ^ a * m) (hm : ¬ 2 ∣ m) (hSU : S ≤ U) (hS : Nat.card S = 2 ^ a)
    (hAU : A ≤ U) (hA : IsPGroup 2 A) : ∃ s ∈ U, ∀ x ∈ A, s⁻¹ * x * s ∈ S := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero 2)
  have hfac : (Nat.card U).factorization 2 = a := by
    rw [hU, Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hm0, Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd hm]
    simp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS' : Nat.card (S.subgroupOf U) = 2 ^ (Nat.card U).factorization 2 := by
    rw [hfac, ← hS]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSU).toEquiv
  let P : Sylow 2 U := Sylow.ofCard (S.subgroupOf U) hS'
  have hA' : IsPGroup 2 (A.subgroupOf U) := hA.of_equiv (Subgroup.subgroupOfEquivOfLe hAU).symm
  obtain ⟨Q, hQ⟩ := hA'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq U P Q
  refine ⟨g, g.2, fun x hx => ?_⟩
  have hxQ : (⟨x, hAU hx⟩ : U) ∈ (Q : Subgroup U) := hQ (Subgroup.mem_subgroupOf.2 hx)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxQ
  obtain ⟨y, hy, hyx⟩ := hxQ
  have hyS : ((y : U) : G) ∈ S := Subgroup.mem_subgroupOf.1 hy
  have hyx' : (g : G) * y * (g : G)⁻¹ = x := congrArg Subtype.val hyx
  rw [← hyx']
  simpa [mul_assoc] using hyS

theorem cat_complete {G : Type*} [Group G] [Finite G] (S0 : Subgroup G) (hS0 : IsPGroup 2 S0)
    (K : ℕ) (cat : ℕ → Set G) (h1 : ∃ k < K, cat k = {1})
    (hstep : ∀ k < K, ∀ B : Subgroup G, (B : Set G) = cat k → ∀ g ∈ S0, g ∉ B → g * g ∈ B →
      (∀ c ∈ B, g * c * g⁻¹ ∈ B) → ∃ k' < K, ∀ x, x ∈ cat k' ↔ x ∈ B ∨ ∃ b ∈ B, x = g * b)
    (R : Subgroup G) (hR : R ≤ S0) : ∃ k < K, (R : Set G) = cat k := by
  have hRp : IsPGroup 2 R := hS0.to_le hR
  suffices H : ∀ n : ℕ, ∀ B : Subgroup G, B ≤ R → Nat.card R - Nat.card B = n →
      (∃ k < K, (B : Set G) = cat k) → ∃ k < K, (R : Set G) = cat k by
    obtain ⟨k, hk, hk1⟩ := h1
    exact H _ ⊥ bot_le rfl ⟨k, hk, by rw [hk1, Subgroup.coe_bot]⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro B hBR hn ⟨k, hk, hBk⟩
    rcases eq_or_lt_of_le hBR with rfl | hlt
    · exact ⟨k, hk, hBk⟩
    obtain ⟨g, hgR, hgB, hgg, hgN⟩ := s5ext_exists_step hRp hlt
    obtain ⟨B', hB'⟩ := s5ext_exists_adjoin hgg hgN
    obtain ⟨k', hk', hk'B⟩ := hstep k hk B hBk g (hR hgR) hgB hgg
      (fun c hc => (Subgroup.mem_normalizer_iff.1 hgN c).1 hc)
    have hBB' : B ≤ B' := fun x hx => (hB' x).2 (Or.inl hx)
    have hB'R : B' ≤ R := fun x hx => by
      rcases (hB' x).1 hx with hx | ⟨b, hb, rfl⟩
      · exact hBR hx
      · exact R.mul_mem hgR (hBR hb)
    have hgB' : g ∈ B' := (hB' g).2 (Or.inr ⟨1, B.one_mem, (mul_one g).symm⟩)
    have hcard : Nat.card B < Nat.card B' :=
      Subgroup.card_lt_of_lt (lt_of_le_of_ne hBB' fun h => hgB (by rw [h]; exact hgB'))
    have hcard' : Nat.card B' ≤ Nat.card R := Subgroup.card_le_of_le hB'R
    refine ih (Nat.card R - Nat.card B') (by omega) B' hB'R rfl ⟨k', hk', ?_⟩
    ext x
    rw [SetLike.mem_coe, hB', hk'B]

@[expose] def PWit (C : Set (Equiv.Perm (Fin 32))) (as : List (Equiv.Perm (Fin 32))) (ts : List (Fin 32)) :
    Prop :=
  as.length + ts.length ≤ 4 ∧ (∀ a ∈ as, a ∈ C) ∧ (∀ t ∈ ts, ∃ σ ∈ C, IsConjP t σ) ∧
    (∀ P : Equiv.Perm (Fin 32) → Prop, (∀ σ ∈ C, ∀ i, IsConjP i σ → P σ) →
      (∀ a ∈ as, ∀ x ∈ autP0, P x → P (a * x)) → ∀ α ∈ C, P α) ∧
    (∀ Q : Fin 32 → Prop, (∀ α ∈ C, ∀ t ∈ ts, Q (α t)) →
      (∀ x y, Q x → Q y → Q (extraMulFin x y)) → ∀ i, (∃ σ ∈ C, IsConjP i σ) → Q i)

theorem pwit_conj {C : Set (Equiv.Perm (Fin 32))} {as : List (Equiv.Perm (Fin 32))}
    {ts : List (Fin 32)} (h : PWit C as ts) {s : Equiv.Perm (Fin 32)} (hs : s ∈ autP0) :
    PWit {x | s⁻¹ * x * s ∈ C} (as.map fun a => s * a * s⁻¹) (ts.map s) := by
  obtain ⟨hlen, has, hts, hP, hQ⟩ := h
  have hs' : s⁻¹ ∈ autP0 := autP0.inv_mem hs
  have hconj : ∀ σ ∈ C, s⁻¹ * (s * σ * s⁻¹) * s ∈ C := fun σ hσ => by
    simpa [mul_assoc] using hσ
  refine ⟨by simpa using hlen, ?_, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨a', ha', rfl⟩ := List.mem_map.1 ha
    exact hconj a' (has a' ha')
  · intro t ht
    obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht
    obtain ⟨σ, hσ, hσt⟩ := hts t' ht'
    exact ⟨s * σ * s⁻¹, hconj σ hσ, isConjP_conj hs hσt⟩
  · intro P hP1 hP2 α hα
    have := hP (fun σ => P (s * σ * s⁻¹))
      (fun σ hσ i hi => hP1 _ (hconj σ hσ) (s i) (isConjP_conj hs hi))
      (fun a ha x hx hPx => by
        have h2 := hP2 (s * a * s⁻¹) (List.mem_map_of_mem ha) (s * x * s⁻¹)
          (autP0.mul_mem (autP0.mul_mem hs hx) hs') hPx
        simpa [mul_assoc] using h2)
      _ hα
    simpa [mul_assoc] using this
  · intro Q hQ1 hQ2 i ⟨σ, hσ, hσi⟩
    have := hQ (fun j => Q (s j))
      (fun α hα t ht => by
        have h2 := hQ1 (s * α * s⁻¹) (hconj α hα) (s t) (List.mem_map_of_mem ht)
        simpa using h2)
      (fun x y hx hy => by rw [hs]; exact hQ2 _ _ hx hy)
      (s⁻¹ i) ⟨s⁻¹ * σ * s, hσ, by simpa using isConjP_conj hs' hσi⟩
    simpa using this

end CFSG.Certificates.Kernel.S5K
