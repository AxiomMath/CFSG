module

public import CFSG.LargeExtraspecial.S8A5E0

public section

namespace CFSG.LargeExtraspecial.S8

open Subgroup CFSG.CGT.Timmesfeld75

universe u

variable {Γ : Type u} [Group Γ]

abbrev Epair (A : Subgroup Γ) (x : Γ) : Subgroup Γ :=
  (A ⊓ normalizer (conjSubgroup x A : Set Γ)) ⊔ (conjSubgroup x A ⊓ normalizer (A : Set Γ))

theorem conjSubgroup_normalizer (g : Γ) (T : Subgroup Γ) :
    conjSubgroup g (normalizer (T : Set Γ)) = normalizer (conjSubgroup g T : Set Γ) := by
  ext y
  rw [mem_conjSubgroup]
  have h := mem_normalizer_conj_iff (T := T) (g := g) (y := g⁻¹ * y * g)
  rw [show g * (g⁻¹ * y * g) * g⁻¹ = y by group] at h
  exact h.symm

theorem conjSubgroup_inv_Epair (A : Subgroup Γ) (x : Γ) :
    conjSubgroup x⁻¹ (Epair A x) = Epair A x⁻¹ := by
  rw [Epair, Epair, conjSubgroup_sup, conjSubgroup_inf, conjSubgroup_inf,
    conjSubgroup_normalizer, conjSubgroup_normalizer, conjSubgroup_inv_conj, sup_comm]

theorem conj_mem_Epair_inv {A : Subgroup Γ} {x e : Γ} (he : e ∈ Epair A x) :
    x⁻¹ * e * x ∈ Epair A x⁻¹ := by
  rw [← conjSubgroup_inv_Epair, mem_conjSubgroup, inv_inv]
  rwa [show x * (x⁻¹ * e * x) * x⁻¹ = e by group]

theorem comm_of_hP1E {M B B₁ : Subgroup Γ} {T : Set Γ} {u : Γ} (huu : u * u = 1)
    (hP1u : ∀ y ∈ M, y * u * y⁻¹ * u = u * (y * u * y⁻¹) → y * u * y⁻¹ ≠ u →
      y * u * y⁻¹ ∈ T → B ⊓ conjSubgroup y B = ⊥)
    (hT : ∀ e ∈ B₁, u * e = e * u → e * u ∈ T)
    (hB₁M : B₁ ≤ M) (hsq₁ : ∀ b ∈ B₁, b * b = 1) (huB₁ : u ∈ normalizer (B₁ : Set Γ))
    {f : Γ} (hfB : f ∈ B) (hff : f * f = 1) (hfB₁ : f ∈ normalizer (B₁ : Set Γ)) {b : Γ}
    (hb : b ∈ B₁) : (f * b * f⁻¹ * b⁻¹) * u = u * (f * b * f⁻¹ * b⁻¹) := by
  obtain ⟨c, hc⟩ : ∃ c, c = f * b * f⁻¹ * b⁻¹ := ⟨_, rfl⟩
  rw [← hc]
  have hinv₁ : ∀ e ∈ B₁, e⁻¹ = e := fun e he => inv_eq_of_mul_eq_one_right (hsq₁ e he)
  have hb' : f * b * f⁻¹ ∈ B₁ := (mem_normalizer_iff.mp hfB₁ b).mp hb
  have hcB₁ : c ∈ B₁ := by rw [hc]; exact mul_mem hb' (inv_mem hb)
  have hfc : f * c = c * f := by
    have h1 : f * (f * b * f⁻¹) * f⁻¹ = b := by
      rw [show f * (f * b * f⁻¹) * f⁻¹ = (f * f) * b * (f * f)⁻¹ by group, hff]
      group
    have h2 : f * c * f⁻¹ = c := by
      calc f * c * f⁻¹ = (f * (f * b * f⁻¹) * f⁻¹) * (f * b * f⁻¹)⁻¹ := by rw [hc]; group
        _ = b * (f * b * f⁻¹) := by rw [h1, hinv₁ _ hb']
        _ = (f * b * f⁻¹) * b := S9.TIX.comm_of_sq hsq₁ hb hb'
        _ = c := by rw [hc, hinv₁ b hb]
    calc f * c = f * c * f⁻¹ * f := by group
      _ = c * f := by rw [h2]
  have hd : u * c * u⁻¹ ∈ B₁ := (mem_normalizer_iff.mp huB₁ c).mp hcB₁
  obtain ⟨e, he⟩ : ∃ e, e = c * (u * c * u⁻¹)⁻¹ := ⟨_, rfl⟩
  have heB₁ : e ∈ B₁ := by rw [he]; exact mul_mem hcB₁ (inv_mem hd)
  have h3 : c * u * c⁻¹ = e * u := by rw [he]; group
  have h4 : u * e * u⁻¹ = e := by
    calc u * e * u⁻¹ = (u * c * u⁻¹) * ((u * u) * c⁻¹ * (u * u)⁻¹) := by rw [he]; group
      _ = (u * c * u⁻¹) * c⁻¹ := by rw [huu]; group
      _ = e⁻¹ := by rw [he]; group
      _ = e := hinv₁ e heB₁
  have hue : u * e = e * u := by
    calc u * e = u * e * u⁻¹ * u := by group
      _ = e * u := by rw [h4]
  have hcu : (c * u * c⁻¹) * u = u * (c * u * c⁻¹) := by
    rw [h3]
    calc e * u * u = e * (u * u) := by group
      _ = (u * u) * e := by rw [huu, mul_one, one_mul]
      _ = u * (u * e) := by group
      _ = u * (e * u) := by rw [hue]
  by_contra hne
  have hcuc : c * u * c⁻¹ ≠ u := by
    intro h
    apply hne
    calc c * u = c * u * c⁻¹ * c := by group
      _ = u * c := by rw [h]
  have hbot := hP1u c (hB₁M hcB₁) hcu hcuc (by rw [h3]; exact hT e heB₁ hue)
  have hf1 : f = 1 := by
    have hmem : f ∈ B ⊓ conjSubgroup c B := by
      refine ⟨hfB, mem_conjSubgroup.mpr ?_⟩
      rw [show c⁻¹ * f * c = c⁻¹ * (f * c) by group, hfc, inv_mul_cancel_left]
      exact hfB
    rw [hbot] at hmem
    exact hmem
  apply hcuc
  rw [hc, hf1]
  group

structure PairDataE (M A N : Subgroup Γ) (t x : Γ) : Prop where
  hAM : A ≤ M
  hAN : A ≤ N
  hsq : ∀ a ∈ A, a * a = 1
  htA : t ∈ A
  ht1 : t ≠ 1
  hNc : ∀ a ∈ N, ∀ b ∈ N, a * b * a⁻¹ * b⁻¹ ∈ zpowers t
  htN : ∀ n ∈ N, n * t = t * n
  hNorm : ∀ y ∈ M, y * t = t * y → ∀ n ∈ N, y * n * y⁻¹ ∈ N
  hP1 : ∀ y ∈ M, y * t * y⁻¹ * t = t * (y * t * y⁻¹) → y * t * y⁻¹ ≠ t →
    (y * t * y⁻¹ ∈ Epair A x ∨ y * t * y⁻¹ ∈ Epair A x⁻¹) → A ⊓ conjSubgroup y A = ⊥
  hK : ∀ y ∈ M, y * t = t * y → ∀ a ∈ A ⊓ conjSubgroup y A,
    a ∉ zpowers t → conjSubgroup y A = A
  hxM : x ∈ M
  hσt : x * t * x⁻¹ * t = t * (x * t * x⁻¹)
  hσ1 : x * t * x⁻¹ ≠ t
  hF : ∀ a ∈ A, a ∈ normalizer (conjSubgroup x A : Set Γ) ↔
    a * (x * t * x⁻¹) = x * t * x⁻¹ * a
  hF' : ∀ a ∈ A, a ∈ normalizer (conjSubgroup x⁻¹ A : Set Γ) ↔
    a * (x⁻¹ * t * x⁻¹⁻¹) = x⁻¹ * t * x⁻¹⁻¹ * a
  h4 : 4 * Nat.card (A ⊓ normalizer (conjSubgroup x A : Set Γ) : Subgroup Γ) ≤ Nat.card A
  h4' : 4 * Nat.card (A ⊓ normalizer (conjSubgroup x⁻¹ A : Set Γ) : Subgroup Γ) ≤ Nat.card A
  h2 : 2 < Nat.card (A ⊓ normalizer (conjSubgroup x A : Set Γ) : Subgroup Γ)
  h2' : 2 < Nat.card (A ⊓ normalizer (conjSubgroup x⁻¹ A : Set Γ) : Subgroup Γ)

namespace PairDataE

variable {M A N : Subgroup Γ} {t x : Γ} (P : PairDataE M A N t x)
include P

theorem htt : t * t = 1 := P.hsq t P.htA

theorem symm : PairDataE M A N t x⁻¹ where
  hAM := P.hAM
  hAN := P.hAN
  hsq := P.hsq
  htA := P.htA
  ht1 := P.ht1
  hNc := P.hNc
  htN := P.htN
  hNorm := P.hNorm
  hP1 := fun y hy hc hne hE => P.hP1 y hy hc hne (by rw [inv_inv] at hE; exact hE.symm)
  hK := P.hK
  hxM := inv_mem P.hxM
  hσt := by
    have h := P.hσt
    rw [inv_inv]
    calc x⁻¹ * t * x * t = x⁻¹ * (t * (x * t * x⁻¹)) * x := by group
      _ = x⁻¹ * (x * t * x⁻¹ * t) * x := by rw [h]
      _ = t * (x⁻¹ * t * x) := by group
  hσ1 := by
    rw [inv_inv]
    intro h
    apply P.hσ1
    calc x * t * x⁻¹ = x * (x⁻¹ * t * x) * x⁻¹ := by rw [h]
      _ = t := by group
  hF := P.hF'
  hF' := by simpa only [inv_inv] using P.hF
  h4 := P.h4'
  h4' := by simpa only [inv_inv] using P.h4
  h2 := P.h2'
  h2' := by simpa only [inv_inv] using P.h2

theorem hA₁M : conjSubgroup x A ≤ M := by
  intro b hb
  have h := P.hAM (mem_conjSubgroup.mp hb)
  have e : b = x * (x⁻¹ * b * x) * x⁻¹ := by group
  rw [e]
  exact M.mul_mem (M.mul_mem P.hxM h) (inv_mem P.hxM)

theorem hsq₁ : ∀ b ∈ conjSubgroup x A, b * b = 1 := by
  intro b hb
  have h := P.hsq _ (mem_conjSubgroup.mp hb)
  calc b * b = x * ((x⁻¹ * b * x) * (x⁻¹ * b * x)) * x⁻¹ := by group
    _ = 1 := by rw [h]; group

theorem mem_normalizer_iff_comm {b : Γ} (hb : b ∈ conjSubgroup x A) :
    b ∈ normalizer (A : Set Γ) ↔ b * t = t * b := by
  have ha := mem_conjSubgroup.mp hb
  have e : b = x * (x⁻¹ * b * x) * x⁻¹ := by group
  have hN : b ∈ normalizer (A : Set Γ) ↔
      x⁻¹ * b * x ∈ normalizer (conjSubgroup x⁻¹ A : Set Γ) := by
    have key := mem_normalizer_conj_iff (T := conjSubgroup x⁻¹ A) (g := x) (y := x⁻¹ * b * x)
    rwa [conjSubgroup_conj_inv, ← e] at key
  rw [hN, P.hF' _ ha, inv_inv]
  constructor
  · intro h
    calc b * t = x * ((x⁻¹ * b * x) * (x⁻¹ * t * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * t * x) * (x⁻¹ * b * x)) * x⁻¹ := by rw [h]
      _ = t * b := by group
  · intro h
    calc x⁻¹ * b * x * (x⁻¹ * t * x) = x⁻¹ * (b * t) * x := by group
      _ = x⁻¹ * (t * b) * x := by rw [h]
      _ = x⁻¹ * t * x * (x⁻¹ * b * x) := by group

theorem t_mem_F : t ∈ A ⊓ normalizer (conjSubgroup x A : Set Γ) :=
  ⟨P.htA, (P.hF t P.htA).mpr P.hσt.symm⟩

theorem σ_mem : x * t * x⁻¹ ∈ conjSubgroup x A := by
  rw [mem_conjSubgroup, show x⁻¹ * (x * t * x⁻¹) * x = t by group]
  exact P.htA

theorem σ_mem_F₁ : x * t * x⁻¹ ∈ conjSubgroup x A ⊓ normalizer (A : Set Γ) :=
  ⟨P.σ_mem, (P.mem_normalizer_iff_comm P.σ_mem).mpr P.hσt⟩

theorem mul_t_mem_Epair {e : Γ} (he : e ∈ conjSubgroup x A) (het : t * e = e * t) :
    e * t ∈ Epair A x :=
  mul_mem (mem_sup_right ⟨he, (P.mem_normalizer_iff_comm he).mpr het.symm⟩)
    (mem_sup_left P.t_mem_F)

theorem mul_σ_mem_Epair {e : Γ} (he : e ∈ A) (het : x * t * x⁻¹ * e = e * (x * t * x⁻¹)) :
    e * (x * t * x⁻¹) ∈ Epair A x :=
  mul_mem (mem_sup_left ⟨he, (P.hF e he).mpr het.symm⟩) (mem_sup_right P.σ_mem_F₁)

theorem hP1σ : ∀ y ∈ M, y * (x * t * x⁻¹) * y⁻¹ * (x * t * x⁻¹) =
    (x * t * x⁻¹) * (y * (x * t * x⁻¹) * y⁻¹) → y * (x * t * x⁻¹) * y⁻¹ ≠ x * t * x⁻¹ →
    y * (x * t * x⁻¹) * y⁻¹ ∈ Epair A x →
    conjSubgroup x A ⊓ conjSubgroup y (conjSubgroup x A) = ⊥ := by
  intro y hyM hcomm hne hE
  have hy'M : x⁻¹ * y * x ∈ M := M.mul_mem (M.mul_mem (inv_mem P.hxM) hyM) P.hxM
  have e1 : x⁻¹ * y * x * t * (x⁻¹ * y * x)⁻¹ = x⁻¹ * (y * (x * t * x⁻¹) * y⁻¹) * x := by
    group
  have h1 := P.hP1 (x⁻¹ * y * x) hy'M (by
    calc x⁻¹ * y * x * t * (x⁻¹ * y * x)⁻¹ * t =
        x⁻¹ * (y * (x * t * x⁻¹) * y⁻¹ * (x * t * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * t * x⁻¹) * (y * (x * t * x⁻¹) * y⁻¹)) * x := by rw [hcomm]
      _ = t * (x⁻¹ * y * x * t * (x⁻¹ * y * x)⁻¹) := by group) (by
    intro h
    apply hne
    calc y * (x * t * x⁻¹) * y⁻¹ = x * (x⁻¹ * y * x * t * (x⁻¹ * y * x)⁻¹) * x⁻¹ := by group
      _ = x * t * x⁻¹ := by rw [h]) (Or.inr (by rw [e1]; exact conj_mem_Epair_inv hE))
  have h2 := congrArg (conjSubgroup x) h1
  rw [conjSubgroup_inf, ← S9.TIX.conjSubgroup_mul, show x * (x⁻¹ * y * x) = y * x by group,
    S9.TIX.conjSubgroup_mul] at h2
  rw [h2]
  exact conjSubgroup_eq_bot_iff.mpr rfl

theorem inf_eq_bot : A ⊓ conjSubgroup x A = ⊥ :=
  P.hP1 x P.hxM P.hσt P.hσ1 (Or.inl (mem_sup_right P.σ_mem_F₁))

end PairDataE

end CFSG.LargeExtraspecial.S8
