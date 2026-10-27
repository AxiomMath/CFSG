module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.F10

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu
open CFSG.Quasithin (pairVec)

private lemma even_orderOf_of_swap {α : Type*} {i j : α} {τ : Equiv.Perm α}
    (hi : τ i = j) (hj : τ j = i) (hij : i ≠ j) {m : ℕ} (hm : τ ^ m = 1) : Even m := by
  by_contra hne
  rw [Nat.not_even_iff_odd] at hne
  obtain ⟨a, rfl⟩ := hne
  have hfix : (τ ^ 2) j = j := by
    rw [pow_two, Equiv.Perm.mul_apply, hj, hi]
  have hpow : ∀ b : ℕ, ((τ ^ 2) ^ b) j = j := by
    intro b
    induction b with
    | zero => rfl
    | succ k ih => rw [pow_succ, Equiv.Perm.mul_apply, hfix, ih]
  have hsplit : τ ^ (2 * a + 1) = (τ ^ 2) ^ a * τ := by
    rw [← pow_mul, ← pow_succ]
  rw [hsplit] at hm
  have h5 : ((τ ^ 2) ^ a) j = i := by
    have h6 := congrArg (fun f : Equiv.Perm α => f i) hm
    rw [Equiv.Perm.mul_apply, hi, Equiv.Perm.one_apply] at h6
    exact h6
  rw [hpow a] at h5
  exact hij h5.symm

namespace CocodeExtension

variable {N : Type*} [Group N] {E : Subgroup N} {e : ↥E ≃* W11} (h : CocodeExtension N E e)

theorem conj_eq_iff_mem_Bhat {i j : Fin 24} (hij : i ≠ j)
    {x : ↥E} (hx : e x = cocodeCoords.κ (pairVec i j)) (n : N) :
    n * (x : N) * n⁻¹ = x ↔ n ∈ h.Bhat i j := by
  refine ⟨fun hn => ?_, fun hn => h.conj_eq_of_mem_Bhat hx hn⟩
  rw [h.mem_Bhat_iff]
  have hfix : h.conjE n x = x := Subtype.ext ((h.coe_conjE n x).trans hn)
  have h1 := h.π_apply_e n x
  rw [hfix, hx, rho11_kappa_pairVec] at h1
  rcases kappa11_pairVec_inj (((h.π n : ↥AutPerm) : Equiv.Perm (Fin 24)).injective.ne hij)
      hij h1 with
    ⟨h0, h1⟩ | ⟨h0, h1⟩
  · exact Or.inl ⟨h0, h1⟩
  · exact Or.inr ⟨h0, h1⟩

theorem mem_Bduad_of_mem_Bhat_of_odd {i j : Fin 24} (hij : i ≠ j)
    {n : N} (hn : n ∈ h.Bhat i j) (hodd : Odd (orderOf n)) : n ∈ h.Bduad i j := by
  rcases h.mem_Bhat_iff.1 hn with ⟨hi, hj⟩ | ⟨hi, hj⟩
  · exact h.mem_Bduad_iff.2 ⟨hi, hj⟩
  · exfalso
    have hσpow : (((h.π n : ↥AutPerm) : Equiv.Perm (Fin 24))) ^ orderOf n = 1 := by
      have h1 : h.π n ^ orderOf n = (1 : ↥AutPerm) := by
        rw [← map_pow, pow_orderOf_eq_one, map_one]
      have h2 := congrArg (fun g : ↥AutPerm => (g : Equiv.Perm (Fin 24))) h1
      simpa [Subgroup.coe_pow] using h2
    exact (Nat.not_even_iff_odd.2 hodd)
      (even_orderOf_of_swap hi hj hij hσpow)

theorem exists_mem_Bhat_not_mem_Bduad
    {i j : Fin 24} (hij : i ≠ j) :
    ∃ n ∈ h.Bhat i j, n ∉ h.Bduad i j := by
  obtain ⟨p, hp, hp0, hp1⟩ := CFSG.Monster.B.TwoA.autPerm_maps_two i j hij
  obtain ⟨q, hq, hq0, hq1⟩ := CFSG.Monster.B.TwoA.autPerm_maps_two j i hij.symm
  have hpi : p⁻¹ i = 0 := by rw [Equiv.Perm.inv_eq_iff_eq]; exact hp0.symm
  have hpj : p⁻¹ j = 1 := by rw [Equiv.Perm.inv_eq_iff_eq]; exact hp1.symm
  obtain ⟨n, hn⟩ := h.π_surjective (⟨q * p⁻¹, mul_mem hq (inv_mem hp)⟩ : ↥AutPerm)
  refine ⟨n, ?_, ?_⟩
  · rw [h.mem_Bhat_iff]
    right
    rw [hn]
    change (q * p⁻¹) i = j ∧ (q * p⁻¹) j = i
    constructor
    · rw [Equiv.Perm.mul_apply, hpi, hq0]
    · rw [Equiv.Perm.mul_apply, hpj, hq1]
  · intro hnB
    rw [h.mem_Bduad_iff] at hnB
    rw [hn] at hnB
    have h1 := hnB.1
    change (q * p⁻¹) i = i at h1
    rw [Equiv.Perm.mul_apply, hpi, hq0] at h1
    exact hij h1.symm

theorem card_Bduad (i j : Fin 24) :
    Nat.card ↥(h.Bduad i j) = Nat.card ↥E * Nat.card ↥(duadStab i j) := by
  let f : ↥(h.Bduad i j) →* ↥(duadStab i j) :=
    (h.π.comp (h.Bduad i j).subtype).codRestrict (duadStab i j) fun b => b.2
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨n, hn⟩ := h.π_surjective y
    refine ⟨⟨n, ?_⟩, ?_⟩
    · rw [Bduad, Subgroup.mem_comap, hn]; exact y.2
    · exact Subtype.ext hn
  have hker : f.ker = E.subgroupOf (h.Bduad i j) := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf,
      show (f b = 1) ↔ h.π (↑b : N) = 1 from Subtype.ext_iff, h.π_eq_one_iff]
  have h1 := Subgroup.card_ker_mul_card_of_surjective (f := f) hf
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (h.le_Bduad i j)).toEquiv] at h1
  exact h1.symm

end CocodeExtension

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
