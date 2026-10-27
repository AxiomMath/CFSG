module

public import CFSG.HardMathSupport.Foote.E27.Defs
public import CFSG.HardMathSupport.Foote.E27.LocalBound
public import CFSG.HardMathSupport.Foote.E27.PermCent
public import CFSG.Quasithin.H13.KG14726COrd
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.HardMathSupport.Foote.E27

open Equiv Subgroup Nat

theorem e27AltSlice_of_bound
    (hD3 : ∀ (X : Type) [Group X] [Finite X] (K R T : Subgroup X) (z : X),
      E27Config X K R T z → 3 ^ 5 ∣ Nat.card (MulAut ↥K)) : E27AltSlice := by
  intro X _ _ K R T z hc n hn ⟨e⟩
  have hD := hD3 X K R T z hc
  have := hc.normal
  have hcard : Nat.card (MulAut ↥K) = Nat.card (MulAut (alternatingGroup (Fin n))) :=
    Nat.card_congr (MulAut.congr e).toEquiv
  by_cases h6 : n = 6
  · subst h6
    have h1 := CFSG.Quasithin.H13.KG14726.card_mulAut_alternatingGroup_six_dvd
    rw [hcard] at hD
    have := dvd_trans (dvd_trans (by norm_num : 243 ∣ 3 ^ 5) hD) h1
    omega
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn h6
  have hperm : Nat.card (MulAut (alternatingGroup (Fin n))) = n ! := by
    rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_perm, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have hn12 : 12 ≤ n := by
    by_contra hlt
    rw [hcard, hperm] at hD
    have : n < 12 := by omega
    interval_cases n <;> first | omega | (revert hD; decide)
  let ψ : X →* MulAut ↥K := MulAut.conjNormal
  let ρ' : MulAut (alternatingGroup (Fin n)) := MulAut.congr e (ψ z)
  obtain ⟨σ, hσ⟩ := hbij.2 ρ'
  have hz3 : z ^ 3 = 1 := hc.elem.2 z hc.z_mem
  have hz1 : z ≠ 1 := fun h => hc.z_not_mem (h ▸ T.one_mem)
  have hψz : ψ z ≠ 1 := by
    intro h
    apply hz1
    have : z ∈ Subgroup.centralizer (K : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h1 := congrArg (fun f : MulAut ↥K => Subtype.val (f ⟨k, hk⟩)) h
      simp only [ψ, MulAut.conjNormal_apply, MulAut.one_apply] at h1
      calc k * z = (z * k * z⁻¹) * z := by rw [h1]
        _ = z * k := by group
    rw [hc.faithful] at this
    exact this
  have hρ1 : ρ' ≠ 1 := by
    intro h
    apply hψz
    exact (MulAut.congr e).injective (h.trans (map_one _).symm)
  have hσ3 : σ ^ 3 = 1 := by
    apply hbij.1
    rw [map_pow, hσ, map_one]
    simp only [ρ', ← map_pow, ψ, ← map_pow, hz3, map_one]
  have hσ1 : σ ≠ 1 := by
    intro h
    apply hρ1
    rw [← hσ, h, map_one]
  have hord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  have hcomm : ∀ k : ↥K, z * (k : X) = k * z ↔
      σ * ((e k : alternatingGroup (Fin n)) : Perm (Fin n)) = (e k : Perm (Fin n)) * σ := by
    intro k
    set a : alternatingGroup (Fin n) := e k with ha
    have h1 : ((ρ' a : alternatingGroup (Fin n)) : Perm (Fin n)) = σ * a * σ⁻¹ := by
      rw [← hσ, MulAut.conjNormal_apply]
    have h2 : ρ' a = e (ψ z k) := by
      simp [ρ', ha, MulAut.congr_apply]
    have h3 : ((ψ z k : ↥K) : X) = z * k * z⁻¹ := MulAut.conjNormal_apply z k
    calc z * (k : X) = k * z
        ↔ z * k * z⁻¹ = k := (mul_inv_eq_iff_eq_mul).symm
      _ ↔ ψ z k = k := by rw [← h3, Subtype.coe_inj]
      _ ↔ ρ' a = a := by rw [h2, ha, e.apply_eq_iff_eq]
      _ ↔ σ * a * σ⁻¹ = a := by rw [← h1, Subtype.coe_inj]
      _ ↔ σ * a = a * σ := mul_inv_eq_iff_eq_mul
  have h81 := dvd81_card_alt_commuting hn12 hord
  have hS : Nat.card {a : alternatingGroup (Fin n) // σ * (a : Perm (Fin n)) = a * σ} =
      Nat.card {k : ↥K // z * (k : X) = k * z} :=
    (Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun k => hcomm k)).symm
  rw [hS] at h81
  let C := Subgroup.centralizer ({z} : Set X)
  let H : Subgroup ↥C := K.subgroupOf C
  have e2 : H ≃ {k : ↥K // z * (k : X) = k * z} :=
    { toFun := fun h => ⟨⟨h.1.1, h.2⟩, (mem_centralizer_singleton_iff.mp h.1.2).symm⟩
      invFun := fun k => ⟨⟨k.1.1, mem_centralizer_singleton_iff.mpr k.2.symm⟩, k.1.2⟩
      left_inv := fun h => rfl
      right_inv := fun k => rfl }
  have hHC : 81 ∣ Nat.card ↥C := by
    have h81' : 81 ∣ Nat.card H := by rw [Nat.card_congr e2]; exact h81
    exact dvd_trans h81' (Subgroup.card_subgroup_dvd_card H)
  obtain ⟨S, hS27⟩ := hc.sylow
  have hSR : Nat.card (S : Subgroup ↥C) = 27 := by
    rw [← hc.card_R, ← hS27]
    exact (Subgroup.card_map_of_injective (Subgroup.subtype_injective C)).symm
  have hfac := Sylow.card_eq_multiplicity S
  rw [hSR] at hfac
  have h3 : 3 ^ 4 ∣ Nat.card ↥C := by simpa using hHC
  rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne'] at h3
  have : (27 : ℕ) = 3 ^ (Nat.card ↥C).factorization 3 := hfac
  have h27 : (27 : ℕ) = 3 ^ 3 := by norm_num
  rw [h27] at this
  have := Nat.pow_right_injective (by norm_num : 2 ≤ 3) this
  omega

theorem e27AltSlice : E27AltSlice :=
  e27AltSlice_of_bound fun _ _ _ K R T z hc =>
    have := hc.normal
    three_pow_five_dvd_card_mulAut K hc.faithful R T z hc.elem hc.card_R hc.T_le_R hc.card_T
      hc.z_mem hc.z_not_mem hc.fus hc.sylow hc.central hc.dvd81

end CFSG.HardMathSupport.Foote.E27
