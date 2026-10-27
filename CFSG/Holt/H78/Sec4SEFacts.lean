module

public import CFSG.Holt.H78.Sec4Prop49S4
public import CFSG.Holt.H78.Sec4SEAut

public section

namespace CFSG.Holt.H78

open MulAction CFSG.GH74.Uniqueness.Bender Equiv
open scoped Pointwise


section Chain

namespace IsBenderAction

variable {X : Type*} [Group X] [Finite X] {Ω : Type*} [MulAction X Ω] {n e : ℕ}

omit [Finite X] in
theorem two_le_of_unitary (hA : IsBenderAction X Ω n 3 e) : 2 ≤ e := by
  rcases hA.benderType.cases' with ⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨-, rfl, -⟩
  · omega
  · omega
  · have hm : 5 ≤ 2 ^ n + 1 := by have := hA.four_le_q; omega
    have hg : Nat.gcd 3 (2 ^ n + 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
    have hdiv := Nat.div_mul_cancel (Nat.gcd_dvd_right 3 (2 ^ n + 1))
    by_contra h
    have hle : (2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1) * Nat.gcd 3 (2 ^ n + 1) ≤ 1 * 3 :=
      Nat.mul_le_mul (by omega) hg
    omega

theorem exists_mem_rootCenter_smul_eq_of_unitary (hA : IsBenderAction X Ω n 3 e) {a b : Ω}
    (hab : a ≠ b) {Q : Sylow 2 X} (hQ : (Q : Subgroup X) ≤ stabilizer X a) {δ : Ω}
    (hδ : δ ∈ holtDelta X Ω a b) : ∃ p ∈ rootCenter (Q : Subgroup X), p ≠ 1 ∧ p • b = δ := by
  set H := stabilizer X a ⊓ stabilizer X b with hH
  have hmul := (stabilizer H δ).card_mul_index
  rw [MulAction.index_stabilizer, ← hA.holtDelta_eq_orbit_of_mem hab hδ, hA.ncard_holtDelta hab,
    hA.card_stabilizer_inf hab] at hmul
  have hq : 0 < 2 ^ n - 1 := by have := hA.four_le_q; omega
  have hstab : Nat.card (stabilizer H δ) = e :=
    Nat.eq_of_mul_eq_mul_left hq (by rw [mul_comm]; exact hmul)
  have he := hA.two_le_of_unitary
  have hne : stabilizer H δ ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hstab
    omega
  obtain ⟨k, hk1⟩ := (stabilizer H δ).ne_bot_iff_exists_ne_one.mp hne
  set d : X := ((k : H) : X) with hd
  have hdH : d ∈ H := (k : H).2
  have hd1 : d ≠ 1 := fun h => hk1 (Subtype.ext (Subtype.ext h))
  have hdδ : d • δ = δ := k.2
  have hδa : δ ≠ a := fun h => left_notMem_holtDelta hab (h ▸ hδ)
  have hδb : δ ≠ b := fun h => right_notMem_holtDelta hab (h ▸ hδ)
  obtain ⟨p, hp, hpb⟩ := hA.exists_mem_smul_eq hQ hab.symm hδa
  have hdB : d ∈ borel (Q : Subgroup X) := (hA.mem_borel_iff hQ).mpr hdH.1
  have hdp : d * p * d⁻¹ ∈ (Q : Subgroup X) := (Subgroup.mem_normalizer_iff.mp hdB p).mp hp
  have hdb' : d⁻¹ • b = b := by rw [inv_smul_eq_iff, hdH.2]
  have hfix : (p⁻¹ * (d * p * d⁻¹)) • b = b := by
    rw [mul_smul, mul_smul, mul_smul, hdb', hpb, hdδ, ← hpb, inv_smul_smul]
  have h1 := hA.eq_one_of_smul_eq hQ (mul_mem (inv_mem hp) hdp) hab.symm hfix
  have hdpd : d * p * d⁻¹ = p := (inv_mul_eq_one.mp h1).symm
  have hcomm : d * p * d⁻¹ * p⁻¹ ∈ rootCenter (Q : Subgroup X) := by
    rw [hdpd, mul_inv_cancel]
    exact one_mem _
  refine ⟨p, hA.mem_rootCenter_of_commutator_mem hQ hab hdH hd1 hp hcomm, ?_, hpb⟩
  rintro rfl
  rw [one_smul] at hpb
  exact hδb hpb.symm

theorem holtDelta_subset_holtDelta'_of_unitary (hA : IsBenderAction X Ω n 3 e) {a b : Ω}
    (hab : a ≠ b) : holtDelta X Ω a b ⊆ holtDelta' X Ω a b := by
  intro δ hδ
  obtain ⟨Q, hQ⟩ := hA.exists_sylow_le_stabilizer a
  obtain ⟨p, hpZ, hp1, hpb⟩ := hA.exists_mem_rootCenter_smul_eq_of_unitary hab hQ hδ
  exact ⟨p, (hA.mem_longInvAt_iff hQ).mpr ⟨hpZ, hp1⟩, hpb⟩

end IsBenderAction

theorem seChainUnitary : SEChainUnitary := fun _ _ _ _ _ _ hA _ _ hab =>
  hA.holtDelta_subset_holtDelta'_of_unitary hab

end Chain

section Count

variable {Ψ : Type} [Finite Ψ]

theorem ncard_add_one_sq_le_of_conj {H Z : Subgroup (Perm Ψ)}
    (hHc : ∀ d ∈ H, ∀ d' ∈ H, d * d' = d' * d) (hHZ : ∀ d ∈ H, ∀ z ∈ Z, d * z * d⁻¹ ∈ Z)
    (htr : ∀ z ∈ Z, z ≠ 1 → ∀ z' ∈ Z, z' ≠ 1 → ∃ d ∈ H, d * z * d⁻¹ = z')
    {x : Perm Ψ} (hxH : ∀ d ∈ H, x * d * x⁻¹ ∈ H) (hxZ : ∀ z ∈ Z, x⁻¹ * z * x ∈ Z)
    {Δ : Set Ψ} {γ₀ : Ψ} (hγ₀ : x γ₀ = γ₀) (hΔ : ∀ δ ∈ Δ, ∃ d ∈ H, d γ₀ = δ)
    {z₀ : Perm Ψ} (hz₀ : z₀ ∈ Z) (hz₀1 : z₀ ≠ 1) (hKE : ∀ d ∈ H, d γ₀ = γ₀ ↔ d * z₀ = z₀ * d)
    {δ₁ : Ψ} (hδ₁ : δ₁ ∈ Δ) (hxδ₁ : x δ₁ ≠ δ₁) :
    ((Δ ∩ {δ | x δ = δ}).ncard + 1) ^ 2 ≤ Nat.card Z := by
  classical
  have hz₀' : x⁻¹ * z₀ * x ≠ 1 := fun h => hz₀1 (by
    calc z₀ = x * (x⁻¹ * z₀ * x) * x⁻¹ := by group
      _ = 1 := by rw [h]; group)
  obtain ⟨h₂, hh₂, hh₂z⟩ := htr z₀ hz₀ hz₀1 _ (hxZ z₀ hz₀) hz₀'
  have hkey : ∀ d ∈ H, (x * h₂) * (d * z₀ * d⁻¹) * (x * h₂)⁻¹ =
      (x * d * x⁻¹) * z₀ * (x * d * x⁻¹)⁻¹ := by
    intro d hd
    have hc := hHc h₂ hh₂ d hd
    calc (x * h₂) * (d * z₀ * d⁻¹) * (x * h₂)⁻¹ = x * (h₂ * d) * z₀ * (h₂ * d)⁻¹ * x⁻¹ := by
          group
      _ = x * d * (h₂ * z₀ * h₂⁻¹) * d⁻¹ * x⁻¹ := by rw [hc]; group
      _ = (x * d * x⁻¹) * z₀ * (x * d * x⁻¹)⁻¹ := by rw [hh₂z]; group
  have hyz₀ : (x * h₂) * z₀ * (x * h₂)⁻¹ = z₀ := by
    calc (x * h₂) * z₀ * (x * h₂)⁻¹ = x * (h₂ * z₀ * h₂⁻¹) * x⁻¹ := by group
      _ = z₀ := by rw [hh₂z]; group
  have hx' : x⁻¹ γ₀ = γ₀ := by rw [Perm.inv_eq_iff_eq, hγ₀]
  have hT : ∀ d ∈ H, ((x * h₂) * (d * z₀ * d⁻¹) * (x * h₂)⁻¹ = d * z₀ * d⁻¹ ↔
      x (d γ₀) = d γ₀) := by
    intro d hd
    have hg : d⁻¹ * (x * d * x⁻¹) ∈ H := H.mul_mem (H.inv_mem hd) (hxH d hd)
    rw [hkey d hd]
    have e1 : (x * d * x⁻¹) * z₀ * (x * d * x⁻¹)⁻¹ = d * z₀ * d⁻¹ ↔
        (d⁻¹ * (x * d * x⁻¹)) * z₀ = z₀ * (d⁻¹ * (x * d * x⁻¹)) := by
      constructor
      · intro h
        calc (d⁻¹ * (x * d * x⁻¹)) * z₀ =
            d⁻¹ * ((x * d * x⁻¹) * z₀ * (x * d * x⁻¹)⁻¹) * (x * d * x⁻¹) := by group
          _ = d⁻¹ * (d * z₀ * d⁻¹) * (x * d * x⁻¹) := by rw [h]
          _ = z₀ * (d⁻¹ * (x * d * x⁻¹)) := by group
      · intro h
        calc (x * d * x⁻¹) * z₀ * (x * d * x⁻¹)⁻¹ =
            d * ((d⁻¹ * (x * d * x⁻¹)) * z₀) * (x * d * x⁻¹)⁻¹ := by group
          _ = d * (z₀ * (d⁻¹ * (x * d * x⁻¹))) * (x * d * x⁻¹)⁻¹ := by rw [h]
          _ = d * z₀ * d⁻¹ := by group
    rw [e1, ← hKE _ hg, Perm.mul_apply, Perm.mul_apply, Perm.mul_apply, hx',
      Perm.inv_eq_iff_eq]
  set A : Set (Perm Ψ) := {z | z ∈ Z ∧ (x * h₂) * z * (x * h₂)⁻¹ = z} with hAdef
  have h1A : (1 : Perm Ψ) ∈ A := ⟨Z.one_mem, by group⟩
  have hAinv : ∀ u ∈ A, u⁻¹ ∈ A := by
    rintro u ⟨huZ, hu⟩
    refine ⟨Z.inv_mem huZ, ?_⟩
    calc (x * h₂) * u⁻¹ * (x * h₂)⁻¹ = ((x * h₂) * u * (x * h₂)⁻¹)⁻¹ := by group
      _ = u⁻¹ := by rw [hu]
  have hAmul : ∀ u ∈ A, ∀ w ∈ A, u * w ∈ A := by
    rintro u ⟨huZ, hu⟩ w ⟨hwZ, hw⟩
    refine ⟨Z.mul_mem huZ hwZ, ?_⟩
    calc (x * h₂) * (u * w) * (x * h₂)⁻¹ =
        ((x * h₂) * u * (x * h₂)⁻¹) * ((x * h₂) * w * (x * h₂)⁻¹) := by group
      _ = u * w := by rw [hu, hw]
  have hF : (Δ ∩ {δ | x δ = δ}).ncard ≤ (A \ {1}).ncard := by
    choose! f hfH hf using hΔ
    refine Set.ncard_le_ncard_of_injOn (fun δ => f δ * z₀ * (f δ)⁻¹) ?_ ?_
    · rintro δ ⟨hδ, hxδ⟩
      refine ⟨⟨hHZ _ (hfH δ hδ) z₀ hz₀, (hT _ (hfH δ hδ)).mpr ?_⟩, fun h => hz₀1 ?_⟩
      · rw [hf δ hδ]
        exact hxδ
      · calc z₀ = (f δ)⁻¹ * (f δ * z₀ * (f δ)⁻¹) * f δ := by group
          _ = 1 := by rw [Set.mem_singleton_iff.mp h]; group
    · rintro δ ⟨hδ, -⟩ δ' ⟨hδ', -⟩ h
      have hg : (f δ')⁻¹ * f δ ∈ H := H.mul_mem (H.inv_mem (hfH δ' hδ')) (hfH δ hδ)
      have hc : ((f δ')⁻¹ * f δ) * z₀ = z₀ * ((f δ')⁻¹ * f δ) := by
        calc ((f δ')⁻¹ * f δ) * z₀ = (f δ')⁻¹ * (f δ * z₀ * (f δ)⁻¹) * f δ := by group
          _ = (f δ')⁻¹ * (f δ' * z₀ * (f δ')⁻¹) * f δ := by rw [show f δ * z₀ * (f δ)⁻¹ =
                f δ' * z₀ * (f δ')⁻¹ from h]
          _ = z₀ * ((f δ')⁻¹ * f δ) := by group
      have h1 := (hKE _ hg).mpr hc
      rw [Perm.mul_apply, Perm.inv_eq_iff_eq, hf δ hδ, hf δ' hδ'] at h1
      exact h1
  obtain ⟨d₁, hd₁, hd₁γ⟩ := hΔ δ₁ hδ₁
  have hz₁A : ¬ ((x * h₂) * (d₁ * z₀ * d₁⁻¹) * (x * h₂)⁻¹ = d₁ * z₀ * d₁⁻¹) := fun h =>
    hxδ₁ (by rw [← hd₁γ]; exact (hT d₁ hd₁).mp h)
  have hyH : ∀ d ∈ H, (x * h₂) * d * (x * h₂)⁻¹ ∈ H := by
    intro d hd
    have h1 := hxH _ (H.mul_mem (H.mul_mem hh₂ hd) (H.inv_mem hh₂))
    rw [show (x * h₂) * d * (x * h₂)⁻¹ = x * (h₂ * d * h₂⁻¹) * x⁻¹ by group]
    exact h1
  have hS6 : ∀ w ∈ A, d₁ * w * d₁⁻¹ ∈ A → w = 1 := by
    rintro w ⟨hwZ, hwy⟩ ⟨-, hw'y⟩
    by_contra hw1
    have hgH : d₁⁻¹ * ((x * h₂) * d₁ * (x * h₂)⁻¹) ∈ H :=
      H.mul_mem (H.inv_mem hd₁) (hyH d₁ hd₁)
    have hwy' : (x * h₂)⁻¹ * w * (x * h₂) = w := by
      calc (x * h₂)⁻¹ * w * (x * h₂) =
          (x * h₂)⁻¹ * ((x * h₂) * w * (x * h₂)⁻¹) * (x * h₂) := by rw [hwy]
        _ = w := by group
    have hgw : (d₁⁻¹ * ((x * h₂) * d₁ * (x * h₂)⁻¹)) * w *
        (d₁⁻¹ * ((x * h₂) * d₁ * (x * h₂)⁻¹))⁻¹ = w := by
      calc (d₁⁻¹ * ((x * h₂) * d₁ * (x * h₂)⁻¹)) * w *
          (d₁⁻¹ * ((x * h₂) * d₁ * (x * h₂)⁻¹))⁻¹ =
          d₁⁻¹ * ((x * h₂) * (d₁ * ((x * h₂)⁻¹ * w * (x * h₂)) * d₁⁻¹) * (x * h₂)⁻¹) * d₁ := by
            group
        _ = d₁⁻¹ * ((x * h₂) * (d₁ * w * d₁⁻¹) * (x * h₂)⁻¹) * d₁ := by rw [hwy']
        _ = d₁⁻¹ * (d₁ * w * d₁⁻¹) * d₁ := by rw [hw'y]
        _ = w := by group
    obtain ⟨k, hk, hkw⟩ := htr w hwZ hw1 z₀ hz₀ hz₀1
    have hc := hHc _ hgH k hk
    have hgz : (d₁⁻¹ * ((x * h₂) * d₁ * (x * h₂)⁻¹)) * z₀ *
        (d₁⁻¹ * ((x * h₂) * d₁ * (x * h₂)⁻¹))⁻¹ = z₀ := by
      rw [← hkw]
      calc (d₁⁻¹ * ((x * h₂) * d₁ * (x * h₂)⁻¹)) * (k * w * k⁻¹) *
          (d₁⁻¹ * ((x * h₂) * d₁ * (x * h₂)⁻¹))⁻¹ =
          ((d₁⁻¹ * ((x * h₂) * d₁ * (x * h₂)⁻¹)) * k) * w *
            ((d₁⁻¹ * ((x * h₂) * d₁ * (x * h₂)⁻¹)) * k)⁻¹ := by group
        _ = (k * (d₁⁻¹ * ((x * h₂) * d₁ * (x * h₂)⁻¹))) * w *
            (k * (d₁⁻¹ * ((x * h₂) * d₁ * (x * h₂)⁻¹)))⁻¹ := by rw [hc]
        _ = k * ((d₁⁻¹ * ((x * h₂) * d₁ * (x * h₂)⁻¹)) * w *
            (d₁⁻¹ * ((x * h₂) * d₁ * (x * h₂)⁻¹))⁻¹) * k⁻¹ := by group
        _ = k * w * k⁻¹ := by rw [hgw]
    apply hz₁A
    calc (x * h₂) * (d₁ * z₀ * d₁⁻¹) * (x * h₂)⁻¹ =
        d₁ * ((d₁⁻¹ * ((x * h₂) * d₁ * (x * h₂)⁻¹)) *
          ((x * h₂) * z₀ * (x * h₂)⁻¹) * (d₁⁻¹ * ((x * h₂) * d₁ * (x * h₂)⁻¹))⁻¹) * d₁⁻¹ := by
          group
      _ = d₁ * z₀ * d₁⁻¹ := by rw [hyz₀, hgz]
  have hS7 : A.ncard * A.ncard ≤ Nat.card Z := by
    rw [← Set.ncard_prod]
    show (A ×ˢ A).ncard ≤ (Z : Set (Perm Ψ)).ncard
    refine Set.ncard_le_ncard_of_injOn (fun p : Perm Ψ × Perm Ψ => p.1 * (d₁ * p.2 * d₁⁻¹))
      ?_ ?_
    · rintro ⟨u, w⟩ ⟨⟨huZ, -⟩, ⟨hwZ, -⟩⟩
      exact Z.mul_mem huZ (hHZ d₁ hd₁ w hwZ)
    · rintro ⟨u, w⟩ ⟨hu, hw⟩ ⟨u', w'⟩ ⟨hu', hw'⟩ h
      have h' : u * (d₁ * w * d₁⁻¹) = u' * (d₁ * w' * d₁⁻¹) := h
      have hv : d₁ * (w' * w⁻¹) * d₁⁻¹ = u'⁻¹ * u := by
        calc d₁ * (w' * w⁻¹) * d₁⁻¹ = u'⁻¹ * (u' * (d₁ * w' * d₁⁻¹)) * (d₁ * w * d₁⁻¹)⁻¹ := by
              group
          _ = u'⁻¹ * (u * (d₁ * w * d₁⁻¹)) * (d₁ * w * d₁⁻¹)⁻¹ := by rw [h']
          _ = u'⁻¹ * u := by group
      have hww := hS6 _ (hAmul _ hw' _ (hAinv _ hw)) (by rw [hv]; exact hAmul _ (hAinv _ hu') _ hu)
      have hw'w : w' = w := mul_inv_eq_one.mp hww
      subst hw'w
      rw [mul_right_cancel h']
  have hA1 : (A \ {1}).ncard + 1 = A.ncard := Set.ncard_sdiff_singleton_add_one h1A
  have hFA : (Δ ∩ {δ | x δ = δ}).ncard + 1 ≤ A.ncard := by omega
  calc ((Δ ∩ {δ | x δ = δ}).ncard + 1) ^ 2 ≤ A.ncard ^ 2 := Nat.pow_le_pow_left hFA 2
    _ = A.ncard * A.ncard := sq _
    _ ≤ Nat.card Z := hS7

end Count

section FieldFix

variable {Ψ : Type} [Finite Ψ] {M : Subgroup (Perm Ψ)} {n i e : ℕ}

omit [Finite Ψ] in
private theorem mem_torus_iff {a b : Ψ} {d : Perm Ψ} :
    d ∈ M ⊓ stabilizer (Perm Ψ) a ⊓ stabilizer (Perm Ψ) b ↔ d ∈ M ∧ d a = a ∧ d b = b := by
  simp only [Subgroup.mem_inf, mem_stabilizer_iff, Perm.smul_def, and_assoc]

theorem IsBenderAction.exists_forall_apply_eq_iff_commute (hA : IsBenderAction ↥M Ψ n i e)
    {a b : Ψ} (hab : a ≠ b) {γ₀ : Ψ} (hγ₀ : γ₀ ∈ holtDelta M Ψ a b) :
    ∃ z₀ ∈ rootCenter (seRadical M a), z₀ ≠ 1 ∧
      ∀ d ∈ M, d a = a → d b = b → (d γ₀ = γ₀ ↔ d * z₀ = z₀ * d) := by
  have hM : IsNaturalSE M := isNaturalSE_iff.mpr ⟨n, i, e, hA⟩
  have hγa : γ₀ ≠ a := fun h => left_notMem_holtDelta hab (h ▸ hγ₀)
  have hγb : γ₀ ≠ b := fun h => right_notMem_holtDelta hab (h ▸ hγ₀)
  by_cases hi : i = 3
  · subst hi
    obtain ⟨Q, hQ⟩ := hA.exists_sylow_le_stabilizer a
    obtain ⟨p, hpZ, hp1, hpb⟩ := hA.exists_mem_rootCenter_smul_eq_of_unitary hab hQ hγ₀
    have hpb' : (p : Perm Ψ) b = γ₀ := hpb
    have hpR : (p : Perm Ψ) ∈ seRadical M a := by
      rw [hA.seRadical_eq_map hQ]
      exact ⟨p, rootCenter_le _ hpZ, rfl⟩
    refine ⟨(p : Perm Ψ), ?_, fun h => hp1 (Subtype.ext h), fun d hdM hda hdb => ⟨?_, ?_⟩⟩
    · rw [hA.rootCenter_seRadical_eq_map hQ]
      exact ⟨p, hpZ, rfl⟩
    · intro hdγ
      have hr : (p : Perm Ψ)⁻¹ * (d * p * d⁻¹) ∈ seRadical M a :=
        mul_mem (inv_mem hpR) (conj_mem_seRadical (M.le_normalizer hdM) hda hpR)
      have hdb' : d⁻¹ b = b := by rw [Perm.inv_eq_iff_eq, hdb]
      have hrb : ((p : Perm Ψ)⁻¹ * (d * p * d⁻¹)) b = b := by
        rw [Perm.mul_apply, Perm.mul_apply, Perm.mul_apply, hdb', hpb', hdγ, Perm.inv_eq_iff_eq,
          hpb']
      have h2 : d * p * d⁻¹ = p :=
        (inv_mul_eq_one.mp (hM.eq_one_of_mem_seRadical hr hab.symm hrb)).symm
      calc d * p = d * p * d⁻¹ * d := by group
        _ = p * d := by rw [h2]
    · intro hdp
      calc d γ₀ = (d * p) b := by rw [Perm.mul_apply, hpb']
        _ = (p * d) b := by rw [hdp]
        _ = γ₀ := by rw [Perm.mul_apply, hdb, hpb']
  · have hreg : ∀ d ∈ M, d a = a → d b = b → ∀ γ, γ ≠ a → γ ≠ b → d γ = γ → d = 1 := by
      intro d hdM hda hdb γ hγa hγb hdγ
      exact congrArg Subtype.val (hA.eq_one_of_mem_stabilizer_inf_of_smul_eq hi hab
        (d := ⟨d, hdM⟩) ⟨hda, hdb⟩ hγa hγb hdγ)
    have hZ : rootCenter (seRadical M a) ≠ ⊥ := by
      intro h
      have h1 := hA.card_rootCenter_seRadical a
      rw [h, Subgroup.card_bot] at h1
      have := hA.four_le_q
      omega
    obtain ⟨⟨z₀, hz₀⟩, hz₀1⟩ := (rootCenter (seRadical M a)).ne_bot_iff_exists_ne_one.mp hZ
    have hz₀1' : z₀ ≠ 1 := fun h => hz₀1 (Subtype.ext h)
    refine ⟨z₀, hz₀, hz₀1', fun d hdM hda hdb => ⟨fun hdγ => ?_, fun hdz => ?_⟩⟩
    · rw [hreg d hdM hda hdb γ₀ hγa hγb hdγ, one_mul, mul_one]
    · have hz₀R := rootCenter_le _ hz₀
      have hz₀a : z₀ a = a := apply_eq_of_mem_seRadical hz₀R
      have hzb : z₀ b ≠ b := fun h => hz₀1' (hM.eq_one_of_mem_seRadical hz₀R hab.symm h)
      have hza : z₀ b ≠ a := fun h => hab (z₀.injective (h.trans hz₀a.symm)).symm
      have hdzb : d (z₀ b) = z₀ b := by
        rw [← Perm.mul_apply, hdz, Perm.mul_apply, hdb]
      rw [hreg d hdM hda hdb (z₀ b) hza hzb hdzb, Perm.one_apply]

end FieldFix

theorem seFieldFixBound : SEFieldFixBound := by
  intro Ψ _ _ M hM a b hab x hx hxa hxb hmove
  obtain ⟨n, i, e, hA⟩ := hM.exists_isBenderAction
  have hΔcard := hA.ncard_holtDelta hab
  have hZcard := hA.card_rootCenter_seRadical a
  have hq := hA.four_le_q
  rcases (holtDelta M Ψ a b ∩ {δ | x δ = δ}).eq_empty_or_nonempty with hF | ⟨γ₀, hγ₀Δ, hγ₀x⟩
  · rw [hF, Set.ncard_empty]
    omega
  obtain ⟨δ₁, hδ₁, hxδ₁⟩ := hmove
  obtain ⟨z₀, hz₀, hz₀1, hKE⟩ := hA.exists_forall_apply_eq_iff_commute hab hγ₀Δ
  have hxa' : x⁻¹ a = a := by rw [Perm.inv_eq_iff_eq, hxa]
  have hxb' : x⁻¹ b = b := by rw [Perm.inv_eq_iff_eq, hxb]
  have hcyc := hA.isCyclic_stabilizer_inf hab
  refine (ncard_add_one_sq_le_of_conj (H := M ⊓ stabilizer (Perm Ψ) a ⊓ stabilizer (Perm Ψ) b)
    (Z := rootCenter (seRadical M a)) ?_ ?_ ?_ (x := x) ?_ ?_ hγ₀x ?_ hz₀ hz₀1 ?_ hδ₁
    hxδ₁).trans ?_
  · intro d hd d' hd'
    rw [mem_torus_iff] at hd hd'
    exact congrArg (fun g : ↥(stabilizer ↥M a ⊓ stabilizer ↥M b) => ((g : ↥M) : Perm Ψ))
      (IsCyclic.commGroup.mul_comm (⟨⟨d, hd.1⟩, hd.2.1, hd.2.2⟩ :
        ↥(stabilizer ↥M a ⊓ stabilizer ↥M b)) ⟨⟨d', hd'.1⟩, hd'.2.1, hd'.2.2⟩)
  · intro d hd z hz
    rw [mem_torus_iff] at hd
    exact conj_mem_rootCenter_seRadical (M.le_normalizer hd.1) hd.2.1 hz
  · intro z hz hz1 z' hz' hz'1
    obtain ⟨d, hdM, hda, hdb, hdz⟩ := hM.exists_conj_eq hab hz hz1 hz' hz'1
    exact ⟨d, mem_torus_iff.mpr ⟨hdM, hda, hdb⟩, hdz⟩
  · intro d hd
    rw [mem_torus_iff] at hd ⊢
    refine ⟨(Subgroup.mem_normalizer_iff.mp hx d).mp hd.1, ?_, ?_⟩
    · rw [Perm.mul_apply, Perm.mul_apply, hxa', hd.2.1, hxa]
    · rw [Perm.mul_apply, Perm.mul_apply, hxb', hd.2.2, hxb]
  · intro z hz
    simpa using conj_mem_rootCenter_seRadical (inv_mem hx) hxa' hz
  · intro δ hδ
    rw [hA.holtDelta_eq_orbit_of_mem hab hγ₀Δ] at hδ
    obtain ⟨k, rfl⟩ := hδ
    exact ⟨((k : ↥M) : Perm Ψ), mem_torus_iff.mpr ⟨(k : ↥M).2, k.2.1, k.2.2⟩, rfl⟩
  · intro d hd
    rw [mem_torus_iff] at hd
    exact hKE d hd.1 hd.2.1 hd.2.2
  · rw [hZcard, hΔcard]
    omega

end CFSG.Holt.H78
