module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FTwoR
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FFiber

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

universe u

theorem sec4F_block_disjoint {Ω : Type u} {R : Ω → Ω → Prop} {a a' c c' b b' e e' : Ω}
    (hb : Sec4FBlock R a a' c c') (hb' : Sec4FBlock R b b' e e') (hba : b ≠ a) (hba' : b ≠ a') :
    b' ≠ a ∧ b' ≠ a' := by
  obtain ⟨-, -, hc, hc', ha, ha'⟩ := hb
  obtain ⟨-, -, he, -, -, -⟩ := hb'
  have hbe : R b e := (he b).mpr (Or.inl rfl)
  have hfalse : (e = c ∨ e = c') → False := by
    rintro (h | h)
    · rw [h] at hbe
      rcases (hc b).mp hbe with h' | h'
      · exact hba h'
      · exact hba' h'
    · rw [h] at hbe
      rcases (hc' b).mp hbe with h' | h'
      · exact hba h'
      · exact hba' h'
  constructor
  · intro hb'a
    exact hfalse ((ha e).mp (hb'a ▸ (he b').mpr (Or.inr rfl)))
  · intro hb'a'
    exact hfalse ((ha' e).mp (hb'a' ▸ (he b').mpr (Or.inr rfl)))

theorem sec4F_block_pair {Ω : Type u} {R : Ω → Ω → Prop} {a a' c c' p q : Ω}
    (hb : Sec4FBlock R a a' c c') (hp : p = a ∨ p = a') (hpq : q ≠ p)
    (hnb : ∀ e, R p e ↔ R q e) : q = a ∨ q = a' := by
  obtain ⟨-, -, hc, -, ha, ha'⟩ := hb
  have hpc : R p c := by
    rcases hp with hp | hp
    · rw [hp]
      exact (ha c).mpr (Or.inl rfl)
    · rw [hp]
      exact (ha' c).mpr (Or.inl rfl)
  exact (hc q).mp ((hnb c).mp hpc)

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B P : Subgroup G}
  {x : G} {φ : (Fin 7 → ZMod 2) → G}

theorem Sec4FSetup.block_realizes (h : Sec4FSetup t L S z A B φ) (hT : Sec4FTwo A P x)
    {a a' c c' : Option (Fin 7)} (hb : Sec4FBlock (sec4FR t φ x) a a' c c') :
    Sec4MRealizes t φ (sec4FD t φ x c) (Equiv.swap a a') ∧
      Sec4MRealizes t φ (sec4FD t φ x c') (Equiv.swap a a') := by
  obtain ⟨haa', -, hc, hc', -, -⟩ := hb
  obtain ⟨u, v, huv, hR, hr⟩ := h.R_left hT c
  obtain ⟨u', v', huv', hR', hr'⟩ := h.R_left hT c'
  have hswap : Equiv.swap u v = Equiv.swap a a' :=
    sec4F_swap_eq_of_iff huv haa' (fun g => (hR g).symm.trans (hc g))
  have hswap' : Equiv.swap u' v' = Equiv.swap a a' :=
    sec4F_swap_eq_of_iff huv' haa' (fun g => (hR' g).symm.trans (hc' g))
  refine ⟨?_, ?_⟩
  · rw [hswap] at hr
    exact hr
  · rw [hswap'] at hr'
    exact hr'

theorem Sec4FSetup.block_act (h : Sec4FSetup t L S z A B φ) (hT : Sec4FTwo A P x)
    {a a' c c' : Option (Fin 7)} (hb : Sec4FBlock (sec4FR t φ x) a a' c c') :
    (∀ e, sec4MPt t φ a * sec4FD t φ x e * (sec4MPt t φ a)⁻¹ =
        sec4FD t φ x (Equiv.swap c c' e)) ∧
      ∀ e, sec4MPt t φ a' * sec4FD t φ x e * (sec4MPt t φ a')⁻¹ =
        sec4FD t φ x (Equiv.swap c c' e) := by
  obtain ⟨-, hcc', -, -, ha, ha'⟩ := hb
  obtain ⟨u, v, huv, hR, hr⟩ := h.R_right hT a
  obtain ⟨u', v', huv', hR', hr'⟩ := h.R_right hT a'
  have hswap : Equiv.swap u v = Equiv.swap c c' :=
    sec4F_swap_eq_of_iff huv hcc' (fun e => (hR e).symm.trans (ha e))
  have hswap' : Equiv.swap u' v' = Equiv.swap c c' :=
    sec4F_swap_eq_of_iff huv' hcc' (fun e => (hR' e).symm.trans (ha' e))
  exact ⟨fun e => by rw [hr e, hswap], fun e => by rw [hr' e, hswap']⟩

theorem Sec4FSetup.block_kappa (h : Sec4FSetup t L S z A B φ) (hT : Sec4FTwo A P x)
    {a a' c c' : Option (Fin 7)} (hb : Sec4FBlock (sec4FR t φ x) a a' c c') :
    sec4MPt t φ a * sec4MPt t φ a' = sec4FD t φ x c * sec4FD t φ x c' := by
  obtain ⟨hreal_c, hreal_c'⟩ := h.block_realizes hT hb
  obtain ⟨haa', hcc', -, -, -, -⟩ := hb
  have hdN_c : sec4FD t φ x c ∈ normalizer (A : Set G) := hT.PM (h.d_mem_P hT c)
  have hdN_c' : sec4FD t φ x c' ∈ normalizer (A : Set G) := hT.PM (h.d_mem_P hT c')
  have hmem : (sec4FD t φ x c)⁻¹ * sec4FD t φ x c' ∈ P :=
    mul_mem (inv_mem (h.d_mem_P hT c)) (h.d_mem_P hT c')
  obtain ⟨n, hn⟩ := hT.P2 ⟨(sec4FD t φ x c)⁻¹ * sec4FD t φ x c', hmem⟩
  have hn' : ((sec4FD t φ x c)⁻¹ * sec4FD t φ x c') ^ 2 ^ n = 1 := by
    have h := congrArg Subtype.val hn
    simpa using h
  rcases h.fiber_two (h.d_conj c) (h.d_conj c') hdN_c hdN_c' haa' hreal_c hreal_c'
    ⟨n, hn'⟩ with heq | heq
  · exact absurd (h.d_inj heq) (Ne.symm hcc')
  · have hsq : sec4FD t φ x c * sec4FD t φ x c = 1 := h.d_sq c
    have hprod : sec4FD t φ x c * sec4FD t φ x c' = sec4MPt t φ a * sec4MPt t φ a' := by
      rw [heq, ← mul_assoc, hsq, one_mul]
    exact hprod.symm

theorem Sec4FSetup.kappa_nbr (h : Sec4FSetup t L S z A B φ) (hT : Sec4FTwo A P x)
    {p q e₁ e₂ : Option (Fin 7)} (hpq : p ≠ q) (he : e₁ ≠ e₂)
    (hprod : sec4MPt t φ p * sec4MPt t φ q = sec4FD t φ x e₁ * sec4FD t φ x e₂) :
    ∀ e, sec4FR t φ x p e ↔ sec4FR t φ x q e := by
  obtain ⟨u, v, huv, hRp, hrp⟩ := h.R_right hT p
  obtain ⟨u', v', huv', hRq, hrq⟩ := h.R_right hT q
  have hcomm : ∀ e, (sec4MPt t φ p * sec4MPt t φ q) * sec4FD t φ x e =
      sec4FD t φ x e * (sec4MPt t φ p * sec4MPt t φ q) := by
    intro e
    rw [hprod]
    calc (sec4FD t φ x e₁ * sec4FD t φ x e₂) * sec4FD t φ x e
        = sec4FD t φ x e₁ * (sec4FD t φ x e₂ * sec4FD t φ x e) := by rw [mul_assoc]
      _ = sec4FD t φ x e₁ * (sec4FD t φ x e * sec4FD t φ x e₂) := by rw [h.d_comm e₂ e]
      _ = (sec4FD t φ x e₁ * sec4FD t φ x e) * sec4FD t φ x e₂ := by rw [← mul_assoc]
      _ = (sec4FD t φ x e * sec4FD t φ x e₁) * sec4FD t φ x e₂ := by rw [h.d_comm e₁ e]
      _ = sec4FD t φ x e * (sec4FD t φ x e₁ * sec4FD t φ x e₂) := by rw [mul_assoc]
  have hconj : ∀ e, (sec4MPt t φ p * sec4MPt t φ q) * sec4FD t φ x e *
      (sec4MPt t φ p * sec4MPt t φ q)⁻¹ =
      sec4FD t φ x (Equiv.swap u v (Equiv.swap u' v' e)) := by
    intro e
    calc (sec4MPt t φ p * sec4MPt t φ q) * sec4FD t φ x e *
          (sec4MPt t φ p * sec4MPt t φ q)⁻¹
        = sec4MPt t φ p * (sec4MPt t φ q * sec4FD t φ x e * (sec4MPt t φ q)⁻¹) *
            (sec4MPt t φ p)⁻¹ := by group
      _ = sec4MPt t φ p * sec4FD t φ x (Equiv.swap u' v' e) * (sec4MPt t φ p)⁻¹ := by
            rw [hrq e]
      _ = sec4FD t φ x (Equiv.swap u v (Equiv.swap u' v' e)) := hrp (Equiv.swap u' v' e)
  have hfix : ∀ e, Equiv.swap u v (Equiv.swap u' v' e) = e := by
    intro e
    refine (h.d_inj (x := x)) ?_
    rw [← hconj e, hcomm e, mul_assoc, mul_inv_cancel, mul_one]
  have hmul : Equiv.swap u v * Equiv.swap u' v' = 1 := by
    apply Equiv.ext
    intro e
    rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    exact hfix e
  have hswap : Equiv.swap u v = Equiv.swap u' v' := by
    calc Equiv.swap u v = Equiv.swap u v * 1 := by rw [mul_one]
      _ = Equiv.swap u v * (Equiv.swap u' v' * Equiv.swap u' v') := by
            rw [Equiv.swap_mul_self]
      _ = (Equiv.swap u v * Equiv.swap u' v') * Equiv.swap u' v' := by rw [← mul_assoc]
      _ = 1 * Equiv.swap u' v' := by rw [hmul]
      _ = Equiv.swap u' v' := by rw [one_mul]
  intro e
  rw [hRp e, hRq e]
  have h1 : (e = u ∨ e = v) ↔ Equiv.swap u v e ≠ e :=
    ⟨fun hh => Equiv.swap_apply_ne_self_iff.mpr ⟨huv, hh⟩,
      fun hh => (Equiv.swap_apply_ne_self_iff.mp hh).2⟩
  have h2 : (e = u' ∨ e = v') ↔ Equiv.swap u' v' e ≠ e :=
    ⟨fun hh => Equiv.swap_apply_ne_self_iff.mpr ⟨huv', hh⟩,
      fun hh => (Equiv.swap_apply_ne_self_iff.mp hh).2⟩
  rw [h1, h2, hswap]

end CFSG.OddStandard.SmallF3.Omega
