module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Cocode24Bound
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Cocode24Fix
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.EvenSporadicStandard.Induction.Balance.Cocode24

open Equiv Subgroup

theorem act_act_inv {g : Perm (Fin 24)} (hg : g ∈ aut) (s : Syn) : act g (act g⁻¹ s) = s := by
  have h : (act g).comp (act g⁻¹) = LinearMap.id := by
    rw [← act_mul hg (inv_mem hg), mul_inv_cancel, act_one]
  have h3 := LinearMap.congr_fun h s
  rwa [LinearMap.comp_apply, LinearMap.id_apply] at h3

theorem act_inv_act {g : Perm (Fin 24)} (hg : g ∈ aut) (s : Syn) : act g⁻¹ (act g s) = s := by
  have := act_act_inv (inv_mem hg) s
  simpa using this

theorem act_conj {g b : Perm (Fin 24)} (hg : g ∈ aut) (hb : b ∈ aut) (s : Syn) :
    act (g * b * g⁻¹) (act g s) = act g (act b s) := by
  have h1 := act_mul (mul_mem hg hb) (inv_mem hg)
  have h2 := act_mul hg hb
  rw [h1, LinearMap.comp_apply, act_inv_act hg, h2, LinearMap.comp_apply]

theorem factorization_two_card_aut : (244823040 : ℕ).factorization 2 = 10 := by
  rw [show (244823040 : ℕ) = 2 ^ 10 * 239085 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

theorem exists_conj_le {S : Subgroup (Perm (Fin 24))} (hSa : S ≤ aut) (hSc : Nat.card S = 2 ^ 10)
    (haut : Nat.card aut = 244823040) {B : Subgroup (Perm (Fin 24))} (hBa : B ≤ aut)
    (hB2 : ∀ b ∈ B, b * b = 1) : ∃ g ∈ aut, ∀ b ∈ B, g * b * g⁻¹ ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S' : Subgroup aut := S.subgroupOf aut
  let B' : Subgroup aut := B.subgroupOf aut
  have hS'c : Nat.card S' = 2 ^ 10 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSa).toEquiv).trans hSc
  let S₀ : Sylow 2 aut := Sylow.ofCard S' (by rw [hS'c, haut, factorization_two_card_aut])
  have hB'p : IsPGroup 2 B' := by
    intro b
    refine ⟨1, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    have := hB2 _ b.2
    simpa [pow_two] using this
  obtain ⟨P, hP⟩ := hB'p.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq aut S₀ P
  refine ⟨((g⁻¹ : aut) : Perm (Fin 24)), (g⁻¹).2, fun b hb => ?_⟩
  have h1 : (⟨b, hBa hb⟩ : aut) ∈ (P : Subgroup aut) :=
    hP (show (⟨b, hBa hb⟩ : aut) ∈ B' from hb)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at h1
  obtain ⟨s, hs, hsb⟩ := h1
  have hsb' : g * s * g⁻¹ = ⟨b, hBa hb⟩ := by
    simpa [MulAut.smul_def, MulAut.conj_apply] using hsb
  have : s = g⁻¹ * ⟨b, hBa hb⟩ * g := by
    rw [← hsb']
    group
  have hs' : (s : Perm (Fin 24)) ∈ S := hs
  rw [this] at hs'
  simpa using hs'

theorem offender_of_conj {S : Subgroup (Perm (Fin 24))} (hS : OffenderBound S)
    {B : Subgroup (Perm (Fin 24))} (hBa : B ≤ aut) (hB2 : ∀ b ∈ B, b * b = 1)
    (hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) (hB0 : B ≠ ⊥) {g : Perm (Fin 24)} (hg : g ∈ aut)
    (hgS : ∀ b ∈ B, g * b * g⁻¹ ∈ S) : Nat.card B * Nat.card (fixSyn B) ≤ 2 ^ 11 := by
  set B' : Subgroup (Perm (Fin 24)) := B.map (MulAut.conj g).toMonoidHom with hB'
  have hmem : ∀ x, x ∈ B' ↔ ∃ b ∈ B, g * b * g⁻¹ = x := by
    intro x
    simp [hB', Subgroup.mem_map]
  have hle : B' ≤ S := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := (hmem x).1 hx
    exact hgS b hb
  have h2 : ∀ b ∈ B', b * b = 1 := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := (hmem x).1 hx
    calc g * b * g⁻¹ * (g * b * g⁻¹) = g * (b * b) * g⁻¹ := by group
      _ = 1 := by rw [hB2 b hb]; group
  have hc : ∀ b ∈ B', ∀ b' ∈ B', b * b' = b' * b := by
    intro x hx y hy
    obtain ⟨b, hb, rfl⟩ := (hmem x).1 hx
    obtain ⟨b', hb', rfl⟩ := (hmem y).1 hy
    calc g * b * g⁻¹ * (g * b' * g⁻¹) = g * (b * b') * g⁻¹ := by group
      _ = g * (b' * b) * g⁻¹ := by rw [hBc b hb b' hb']
      _ = g * b' * g⁻¹ * (g * b * g⁻¹) := by group
  have h0 : B' ≠ ⊥ := by
    obtain ⟨b, hb, hb1⟩ : ∃ b ∈ B, b ≠ 1 := by
      by_contra hcon
      apply hB0
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      by_contra hx1
      exact hcon ⟨x, hx, hx1⟩
    intro h
    have h1 := (Subgroup.eq_bot_iff_forall _).1 h (g * b * g⁻¹) ((hmem _).2 ⟨b, hb, rfl⟩)
    apply hb1
    have h2 : b = g⁻¹ * (g * b * g⁻¹) * g := by group
    rw [h2, h1]
    group
  have hcard : Nat.card B' = Nat.card B :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hfix : Nat.card (fixSyn B) ≤ Nat.card (fixSyn B') := by
    refine Nat.card_le_card_of_injective (fun s => ⟨act g s.1, ?_⟩) ?_
    · intro x hx
      obtain ⟨b, hb, rfl⟩ := (hmem x).1 hx
      rw [act_conj hg (hBa hb), s.2 b hb]
    · intro s s' h
      apply Subtype.ext
      have h' := congrArg Subtype.val h
      have := congrArg (act g⁻¹) h'
      simpa [act_inv_act hg] using this
  calc Nat.card B * Nat.card (fixSyn B) ≤ Nat.card B' * Nat.card (fixSyn B') := by
        rw [hcard]
        exact Nat.mul_le_mul_left _ hfix
    _ ≤ 2 ^ 11 := hS B' hle h2 hc h0

section Group

variable {Γ : Type*} [Group Γ] (E : Subgroup Γ) [E.Normal]

omit [E.Normal] in
theorem comm_of_iso (ψ : Additive E ≃+ Syn) (x y : E) : x * y = y * x := by
  apply Additive.ofMul.injective
  apply ψ.injective
  rw [ofMul_mul, ofMul_mul, map_add, map_add, add_comm]

theorem exists_hom (ψ : Additive E ≃+ Syn)
    (hact : ∀ g : Γ, ∃ σ ∈ aut, ∀ x : E,
      ψ (Additive.ofMul (MulAut.conjNormal g x)) = act σ (ψ (Additive.ofMul x))) :
    ∃ ρ : Γ →* Perm (Fin 24), (∀ g, ρ g ∈ aut) ∧ ∀ (g : Γ) (x : E),
      ψ (Additive.ofMul (MulAut.conjNormal g x)) = act (ρ g) (ψ (Additive.ofMul x)) := by
  choose σ hσ hσψ using hact
  have hsurj : ∀ s : Syn, ∃ x : E, ψ (Additive.ofMul x) = s := fun s =>
    ⟨(ψ.symm s).toMul, by simp⟩
  have hmul : ∀ g h : Γ, σ (g * h) = σ g * σ h := by
    intro g h
    have key : (⟨σ (g * h), hσ _⟩ : aut) = ⟨σ g, hσ g⟩ * ⟨σ h, hσ h⟩ := by
      apply actHom_injective
      refine LinearEquiv.ext fun s => ?_
      obtain ⟨x, rfl⟩ := hsurj s
      rw [map_mul, LinearEquiv.mul_apply, actHom_apply, actHom_apply, actHom_apply,
        ← hσψ (g * h) x, ← hσψ h x, ← hσψ g, map_mul, MulAut.mul_apply]
    exact congrArg Subtype.val key
  have hone : σ 1 = 1 := by
    have key : (⟨σ 1, hσ 1⟩ : aut) = 1 := by
      apply actHom_injective
      refine LinearEquiv.ext fun s => ?_
      obtain ⟨x, rfl⟩ := hsurj s
      rw [map_one, actHom_apply]
      show act (σ 1) _ = _
      rw [← hσψ 1 x, map_one]
      rfl
    exact congrArg Subtype.val key
  exact ⟨⟨⟨σ, hone⟩, hmul⟩, hσ, hσψ⟩

variable {E}

theorem ker_eq {ψ : Additive E ≃+ Syn} {ρ : Γ →* Perm (Fin 24)} (hρaut : ∀ g, ρ g ∈ aut)
    (hρ : ∀ (g : Γ) (x : E),
      ψ (Additive.ofMul (MulAut.conjNormal g x)) = act (ρ g) (ψ (Additive.ofMul x)))
    (hcent : ∀ g : Γ, (∀ x ∈ E, g * x = x * g) → g ∈ E) : ρ.ker = E := by
  ext g
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    apply hcent
    intro x hx
    have h1 := hρ g ⟨x, hx⟩
    rw [h, act_one] at h1
    have h2 := Subtype.ext_iff.1 (Additive.ofMul.injective (ψ.injective h1))
    simp only [MulAut.conjNormal_apply] at h2
    exact mul_inv_eq_iff_eq_mul.1 h2
  · intro hg
    have key : (⟨ρ g, hρaut g⟩ : aut) = 1 := by
      apply actHom_injective
      refine LinearEquiv.ext fun s => ?_
      obtain ⟨y, rfl⟩ := ψ.surjective s
      obtain ⟨x, rfl⟩ : ∃ x : E, Additive.ofMul x = y := ⟨y.toMul, rfl⟩
      rw [map_one, actHom_apply]
      show act (ρ g) _ = _
      rw [← hρ g x]
      show ψ (Additive.ofMul (MulAut.conjNormal g x)) = ψ (Additive.ofMul x)
      have hx : MulAut.conjNormal g x = x := by
        apply Subtype.ext
        have := congrArg Subtype.val (comm_of_iso E ψ ⟨g, hg⟩ x)
        simp only [MulAut.conjNormal_apply]
        exact mul_inv_eq_iff_eq_mul.2 this
      rw [hx]
    exact congrArg Subtype.val key

variable [Finite Γ]

theorem eq_of_elemAb (hS : SylowFacts) (ψ : Additive E ≃+ Syn)
    (hact : ∀ g : Γ, ∃ σ ∈ aut, ∀ x : E,
      ψ (Additive.ofMul (MulAut.conjNormal g x)) = act σ (ψ (Additive.ofMul x)))
    (hcent : ∀ g : Γ, (∀ x ∈ E, g * x = x * g) → g ∈ E)
    (hcard : Nat.card (Γ ⧸ E) = 244823040)
    (A : Subgroup Γ) (hA2 : ∀ a ∈ A, a * a = 1) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hAcard : Nat.card A = 2 ^ 12) : A = E := by
  obtain ⟨S, hSa, hSc, hSoff⟩ := hS
  obtain ⟨ρ, hρaut, hρ⟩ := exists_hom E ψ hact
  have hker : ρ.ker = E := ker_eq hρaut hρ hcent
  have hEcard : Nat.card E = 2 ^ 12 := by
    rw [Nat.card_congr (Additive.ofMul : E ≃ Additive E), Nat.card_congr ψ.toEquiv, card_syn]
  have hrange : Nat.card ρ.range = 244823040 := by
    have h1 := Subgroup.card_ker_mul_card_range ρ
    have h2 := Subgroup.card_mul_index E
    rw [hker] at h1
    have h3 : E.index = 244823040 := hcard
    rw [h3] at h2
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans h2.symm)
  have hrange_le : ρ.range ≤ aut := by
    rintro _ ⟨g, rfl⟩
    exact hρaut g
  have haut : Nat.card aut = 244823040 :=
    le_antisymm card_aut_le (hrange ▸ Subgroup.card_le_of_le hrange_le)
  by_contra hne
  have hAE : ∃ a ∈ A, a ∉ E := by
    by_contra hcon
    apply hne
    refine Subgroup.eq_of_le_of_card_ge (fun a ha => ?_) (by rw [hAcard, hEcard])
    by_contra haE
    exact hcon ⟨a, ha, haE⟩
  obtain ⟨a₀, ha₀, ha₀E⟩ := hAE
  let f : A →* Perm (Fin 24) := ρ.comp A.subtype
  have hf : ∀ a : A, f a = ρ (a : Γ) := fun a => rfl
  have hcardA : Nat.card f.ker * Nat.card f.range = 2 ^ 12 :=
    (Subgroup.card_ker_mul_card_range f).trans hAcard
  have hBaut : f.range ≤ aut := by
    rintro _ ⟨a, rfl⟩
    rw [hf]
    exact hρaut a
  have hBsq : ∀ b ∈ f.range, b * b = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [hf, ← map_mul, show (a : Γ) * a = 1 from hA2 a a.2, map_one]
  have hBcomm : ∀ b ∈ f.range, ∀ b' ∈ f.range, b * b' = b' * b := by
    rintro _ ⟨a, rfl⟩ _ ⟨a', rfl⟩
    rw [hf, hf, ← map_mul, ← map_mul, hAc a a.2 a' a'.2]
  have hB0 : f.range ≠ ⊥ := by
    intro h
    have hmem : ρ a₀ ∈ f.range := ⟨⟨a₀, ha₀⟩, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    apply ha₀E
    rw [← hker]
    exact hmem
  have hfix : Nat.card f.ker ≤ Nat.card (fixSyn f.range) := by
    have hmemE : ∀ a : f.ker, (a : A).1 ∈ E := by
      intro a
      rw [← hker]
      exact a.2
    refine Nat.card_le_card_of_injective
      (fun a => ⟨ψ (Additive.ofMul ⟨(a : A).1, hmemE a⟩), ?_⟩) ?_
    · rintro _ ⟨a', rfl⟩
      rw [hf a', ← hρ]
      congr 2
      apply Subtype.ext
      have h1 := hAc a' a'.2 (a : A).1 (a : A).2
      simp only [MulAut.conjNormal_apply]
      exact mul_inv_eq_iff_eq_mul.2 h1
    · intro a₁ a₂ h
      have h1 := congrArg Subtype.val h
      have h2 := Subtype.ext_iff.1 (Additive.ofMul.injective (ψ.injective h1))
      exact Subtype.ext (Subtype.ext h2)
  obtain ⟨g, hg, hgS⟩ := exists_conj_le hSa hSc haut hBaut hBsq
  have hoff := offender_of_conj hSoff hBaut hBsq hBcomm hB0 hg hgS
  have h3 : Nat.card f.ker * Nat.card f.range ≤ Nat.card (fixSyn f.range) * Nat.card f.range :=
    Nat.mul_le_mul_right _ hfix
  rw [hcardA] at h3
  have h4 : Nat.card (fixSyn f.range) * Nat.card f.range ≤ 2 ^ 11 := by
    rw [mul_comm]
    exact hoff
  omega

end Group

end CFSG.EvenSporadicStandard.Induction.Balance.Cocode24
