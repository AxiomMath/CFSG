module

public import CFSG.GH74.GLS.Basic

public section

namespace CFSG.GH74.GLS.TwoThin

open Subgroup
open scoped commutatorElement

theorem exists_fixedPoint_of_involutive_of_odd {α : Type*} [Finite α] (hodd : Odd (Nat.card α))
    (f : α → α) (hf : Function.Involutive f) : ∃ a, f a = a := by
  classical
  have : Fintype α := Fintype.ofFinite α
  by_contra hne
  push Not at hne
  set σ : Equiv.Perm α := hf.toPerm f with hσdef
  have hσ : σ ^ 2 = 1 := by
    ext a
    simp [hσdef, pow_two, Equiv.Perm.mul_apply, hf a]
  have hsupp : σ.support = Finset.univ := by
    ext a
    simp [Equiv.Perm.mem_support, hσdef, hne a]
  have h2 := Equiv.Perm.two_dvd_card_support hσ
  rw [hsupp, Finset.card_univ, ← Nat.card_eq_fintype_card] at h2
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

theorem exists_commute_mul_mem_of_odd {G : Type*} [Group G] {K O : Subgroup G} {t : G}
    (hO : Odd (Nat.card O)) (hOK : O ≤ K) (ht2 : t * t = 1)
    (htO : ∀ o ∈ O, t * o * t⁻¹ ∈ O) (hcomm : ∀ k ∈ K, ⁅k, t⁆ ∈ O) :
    ∀ k ∈ K, ∃ c ∈ K, t * c = c * t ∧ ∃ o ∈ O, k = c * o := by
  intro k hk
  have h1 : t * t = 1 := ht2
  have h2 : t⁻¹ * t⁻¹ = 1 := by rw [← mul_inv_rev, ht2, inv_one]
  have : Finite O := Nat.finite_of_card_ne_zero hO.pos.ne'
  set a : G := k⁻¹ * t * k * t⁻¹ with ha
  have haO : a ∈ O := by
    have := hcomm k⁻¹ (K.inv_mem hk)
    simpa [commutatorElement_def, ha, mul_assoc] using this
  have haa : a * (t * a * t⁻¹) = 1 := by
    calc a * (t * a * t⁻¹) = k⁻¹ * (t * t) * k * (t⁻¹ * t⁻¹) := by simp only [ha]; group
      _ = 1 := by rw [h1, h2]; group
  let f : O → O := fun o => ⟨a * (t * o * t⁻¹), O.mul_mem haO (htO o o.2)⟩
  have hf : Function.Involutive f := by
    intro o
    apply Subtype.ext
    change a * (t * (a * (t * (o : G) * t⁻¹)) * t⁻¹) = o
    calc a * (t * (a * (t * (o : G) * t⁻¹)) * t⁻¹)
        = (a * (t * a * t⁻¹)) * ((t * t) * (o : G) * (t⁻¹ * t⁻¹)) := by group
      _ = o := by rw [haa, h1, h2]; group
  obtain ⟨o₀, ho₀⟩ := exists_fixedPoint_of_involutive_of_odd hO f hf
  have ho₀' : a * (t * (o₀ : G) * t⁻¹) = o₀ := congrArg Subtype.val ho₀
  refine ⟨k * o₀, K.mul_mem hk (hOK o₀.2), ?_, (o₀⁻¹ : O), (o₀⁻¹ : O).2, by simp⟩
  calc t * (k * (o₀ : G)) = (k * a) * (t * (o₀ : G) * t⁻¹) * t := by simp only [ha]; group
    _ = k * (a * (t * (o₀ : G) * t⁻¹)) * t := by group
    _ = k * (o₀ : G) * t := by rw [ho₀']

theorem exists_centralizer_mul_pPrimeCore {G : Type} [Group G] [Finite G] {K : Subgroup G} {t : G}
    (ht : t ∈ centralizerSection K (pPrimeCoreOf 2 K)) (ht2 : orderOf t = 2) :
    ∀ k ∈ K, ∃ c ∈ K ⊓ centralizer ({t} : Set G), ∃ o ∈ pPrimeCoreOf 2 K, k = c * o := by
  obtain ⟨-, htn, hcomm⟩ := ht
  have hodd : Odd (Nat.card (pPrimeCoreOf 2 K)) := by
    unfold pPrimeCoreOf
    rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hsq : t * t = 1 := by rw [← pow_two]; exact ht2 ▸ pow_orderOf_eq_one t
  have hOK : pPrimeCoreOf 2 K ≤ K := by
    rintro _ ⟨o, -, rfl⟩
    exact o.2
  intro k hk
  obtain ⟨c, hc, hct, o, ho, rfl⟩ :=
    exists_commute_mul_mem_of_odd hodd hOK hsq (fun o ho => ((mem_normalizer_iff.mp htn) o).mp ho)
      hcomm k hk
  exact ⟨c, ⟨hc, mem_centralizer_singleton_iff.mpr hct.symm⟩, o, ho, rfl⟩

end CFSG.GH74.GLS.TwoThin
