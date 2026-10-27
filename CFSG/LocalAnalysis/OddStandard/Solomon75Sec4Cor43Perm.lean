module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4Conj

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup

namespace AhatData

theorem eq_one_of_forall_comm_altFixOf {n : ℕ} {σ g : Perm (Fin n)}
    (hm : 4 ≤ (σ.support)ᶜ.card) (hg : g ∈ altFixOf σ)
    (hcomm : ∀ t ∈ altFixOf σ, t * g = g * t) : g = 1 := by
  by_contra hg1
  obtain ⟨a, ha⟩ : ∃ a, g a ≠ a := by
    by_contra hcon
    push Not at hcon
    exact hg1 (Equiv.ext hcon)
  have hσa : σ a = a := by
    by_contra hne
    exact ha (hg.1 a hne)
  have hσb : σ (g a) = g a := by
    by_contra hne
    exact ha (g.injective (hg.1 _ hne))
  have hfix : ∀ x, σ x = x → x ∈ (σ.support)ᶜ := fun x hx => by
    simp [Perm.mem_support, hx]
  have hfix' : ∀ x ∈ (σ.support)ᶜ, σ x = x := fun x hx => by
    simpa [Perm.mem_support] using hx
  have hcard : 1 < ((σ.support)ᶜ \ {a, g a}).card := by
    have h1 := Finset.le_card_sdiff ({a, g a} : Finset (Fin n)) ((σ.support)ᶜ)
    have h2 : ({a, g a} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.1 hcard
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hc hd
  have hσc := hfix' c hc.1
  have hσd := hfix' d hd.1
  have hac : a ≠ c := fun e => hc.2.1 e.symm
  have hbc : g a ≠ c := fun e => hc.2.2 e.symm
  have had : a ≠ d := fun e => hd.2.1 e.symm
  have hbd : g a ≠ d := fun e => hd.2.2 e.symm
  have ht : swap a c * swap c d ∈ altFixOf σ := by
    refine ⟨fun x hx => ?_, ?_⟩
    · have hxa : x ≠ a := fun e => hx (by rw [e]; exact hσa)
      have hxc : x ≠ c := fun e => hx (by rw [e]; exact hσc)
      have hxd : x ≠ d := fun e => hx (by rw [e]; exact hσd)
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne hxc hxd, swap_apply_of_ne_of_ne hxa hxc]
    · rw [Perm.sign_mul, Perm.sign_swap hac, Perm.sign_swap hcd]
      decide
  have h1 := congrArg (fun f : Perm (Fin n) => f a) (hcomm _ ht)
  simp only [Perm.mul_apply] at h1
  have hta : swap a c (swap c d a) = c := by
    rw [swap_apply_of_ne_of_ne hac had, swap_apply_left]
  have htb : swap a c (swap c d (g a)) = g a := by
    rw [swap_apply_of_ne_of_ne hbc hbd, swap_apply_of_ne_of_ne ha hbc]
  rw [htb, hta] at h1
  exact hac (g.injective h1)

theorem apply_mem_of_commute_threeCycle {Ω : Type*} [DecidableEq Ω] {n : Perm Ω}
    {x u v : Ω} (hxv : x ≠ v) (huv : u ≠ v)
    (hcomm : n * (swap x u * swap x v) = (swap x u * swap x v) * n) :
    n x = x ∨ n x = u ∨ n x = v := by
  by_contra hcon
  have h1 : n x ≠ x := fun h => hcon (Or.inl h)
  have h2 : n x ≠ u := fun h => hcon (Or.inr (Or.inl h))
  have h3 : n x ≠ v := fun h => hcon (Or.inr (Or.inr h))
  have hc : (swap x u * swap x v) (n x) = n x := by
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne h1 h3, swap_apply_of_ne_of_ne h1 h2]
  have hx : (swap x u * swap x v) x = v := by
    rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hxv.symm huv.symm]
  have h4 : n ((swap x u * swap x v) x) = (swap x u * swap x v) (n x) :=
    congrArg (fun f : Perm Ω => f x) hcomm
  rw [hx, hc] at h4
  exact hxv (n.injective h4).symm

theorem eq_one_of_forall_comm_alternatingGroup {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (h5 : 5 ≤ Nat.card Ω) {n : Perm Ω}
    (hcomm : ∀ a ∈ alternatingGroup Ω, n * a = a * n) : n = 1 := by
  ext x
  have hcard : 2 < ((Finset.univ : Finset Ω).erase x).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ← Nat.card_eq_fintype_card]
    omega
  obtain ⟨b, hb, d, hd, e, he, hbd, hbe, hde⟩ := Finset.two_lt_card.1 hcard
  have hxb : x ≠ b := fun h => by simp [h] at hb
  have hxd : x ≠ d := fun h => by simp [h] at hd
  have hxe : x ≠ e := fun h => by simp [h] at he
  have hsgn : ∀ {u v : Ω}, x ≠ u → x ≠ v → u ≠ v →
      n * (swap x u * swap x v) = (swap x u * swap x v) * n := fun hxu hxv huv =>
    hcomm _ (isThreeCycle_swap_mul_swap_same hxu hxv huv).mem_alternatingGroup
  have h1 := apply_mem_of_commute_threeCycle hxd hbd (hsgn hxb hxd hbd)
  have h2 := apply_mem_of_commute_threeCycle hxe hbe (hsgn hxb hxe hbe)
  have h3 := apply_mem_of_commute_threeCycle hxe hde (hsgn hxd hxe hde)
  show n x = x
  grind

theorem eq_bot_of_normal_of_not_alt_le {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (h5 : 5 ≤ Nat.card Ω) {T N' : Subgroup (Perm Ω)} (hAT : alternatingGroup Ω ≤ T)
    (hN'T : N' ≤ T) (hn : (N'.subgroupOf T).Normal) (hnot : ¬ alternatingGroup Ω ≤ N') :
    N' = ⊥ := by
  have hsimple : IsSimpleGroup (alternatingGroup Ω) := alternatingGroup.isSimpleGroup h5
  have hn' : ∀ h k, h ∈ N' → k ∈ T → k * h * k⁻¹ ∈ N' :=
    (Subgroup.normal_subgroupOf_iff hN'T).1 hn
  have : (N'.subgroupOf (alternatingGroup Ω)).Normal := by
    refine ⟨fun m hm g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hm ⊢
    simpa using hn' _ _ hm (hAT g.2)
  have hbot : N'.subgroupOf (alternatingGroup Ω) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N'.subgroupOf (alternatingGroup Ω))
      with h | h
    · exact h
    · exfalso
      apply hnot
      intro a ha
      have : (⟨a, ha⟩ : alternatingGroup Ω) ∈ N'.subgroupOf (alternatingGroup Ω) := by
        rw [h]
        exact Subgroup.mem_top _
      exact this
  have hcomm : ∀ n ∈ N', ∀ a ∈ alternatingGroup Ω, n * a = a * n := by
    intro n hn a ha
    have h1 : n * a * n⁻¹ * a⁻¹ ∈ N' := by
      have := mul_mem hn (hn' n⁻¹ a (inv_mem hn) (hAT ha))
      simpa [mul_assoc] using this
    have h2 : n * a * n⁻¹ * a⁻¹ ∈ alternatingGroup Ω :=
      mul_mem ((inferInstance : (alternatingGroup Ω).Normal).conj_mem a ha n) (inv_mem ha)
    have h3 : (⟨n * a * n⁻¹ * a⁻¹, h2⟩ : alternatingGroup Ω) ∈
        N'.subgroupOf (alternatingGroup Ω) := h1
    rw [hbot, Subgroup.mem_bot] at h3
    have h4 : n * a * n⁻¹ * a⁻¹ = 1 := congrArg Subtype.val h3
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h4
    exact h4
  rw [eq_bot_iff]
  intro n hn
  exact (Subgroup.mem_bot).2 (eq_one_of_forall_comm_alternatingGroup h5 (hcomm n hn))

end AhatData

end CFSG.OddStandard.Solomon75
