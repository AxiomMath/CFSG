module

public import CFSG.Quasithin.Vol2.Ch1Sec3A5Gen

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin

theorem exists_inner_sec_of_odd_order {X : Type*} [Group X] {A N : Subgroup X}
    [hN : (N.subgroupOf A).Normal]
    (e : (↥A ⧸ N.subgroupOf A) ≃* ↥(alternatingGroup (Fin 5)))
    (hNA : N ≤ A) {β : MulAut X} (hβ : β ∈ L139A5.stb A N)
    (hodd : Odd (orderOf β)) :
    ∃ ℓ ∈ A, ∀ x ∈ A, (β x)⁻¹ * (ℓ * x * ℓ⁻¹) ∈ N := by
  have heven : ∀ σ : Equiv.Perm (Fin 5), Equiv.Perm.sign σ = 1 →
      ∃ (y : X) (hy : y ∈ A), L139A5.secPi e ⟨MulAut.conj y, L139A5.conj_mem_stb hNA hy⟩ = σ := by
    intro σ hσ
    obtain ⟨b, hb⟩ := QuotientGroup.mk_surjective (e.symm ⟨σ, hσ⟩)
    refine ⟨b, b.2, ?_⟩
    rw [L139A5.secPi_conj e hNA b b.2]
    have : ((⟨(b : X), b.2⟩ : ↥A) : ↥A ⧸ N.subgroupOf A) = e.symm ⟨σ, hσ⟩ := hb
    rw [this, MulEquiv.apply_symm_apply]
  have hsign : Equiv.Perm.sign (L139A5.secPi e ⟨β, hβ⟩) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (L139A5.secPi e ⟨β, hβ⟩)) with h | h
    · exact h
    · exfalso
      have h2 : orderOf (Equiv.Perm.sign (L139A5.secPi e ⟨β, hβ⟩)) = 2 := by
        rw [h]
        exact orderOf_eq_prime (by norm_num) (by norm_num)
      have hdvd1 : orderOf (Equiv.Perm.sign (L139A5.secPi e ⟨β, hβ⟩)) ∣
          orderOf (L139A5.secPi e ⟨β, hβ⟩) := orderOf_map_dvd _ _
      have hdvd2 : orderOf (L139A5.secPi e ⟨β, hβ⟩) ∣ orderOf β := by
        have h1 := orderOf_map_dvd (L139A5.secPi e) ⟨β, hβ⟩
        have hβord : orderOf (⟨β, hβ⟩ : L139A5.stb A N) = orderOf β := by
          rw [← Subgroup.orderOf_coe ⟨β, hβ⟩]
        rwa [hβord] at h1
      have h2dvd : 2 ∣ orderOf β := by
        rw [← h2]
        exact hdvd1.trans hdvd2
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2dvd)
  obtain ⟨ℓ, hℓ, hℓπ⟩ := heven (L139A5.secPi e ⟨β, hβ⟩) hsign
  refine ⟨ℓ, hℓ, fun x hx => ?_⟩
  set w : L139A5.stb A N := ⟨MulAut.conj ℓ, L139A5.conj_mem_stb hNA hℓ⟩⁻¹ * ⟨β, hβ⟩ with hw
  have hk : L139A5.secPi e w = 1 := by
    rw [hw, map_mul, map_inv, hℓπ, inv_mul_cancel]
  have hc := L139A5.mem_of_secPi_eq_one e hk x hx
  have hwx : (w : MulAut X) x = ℓ⁻¹ * β x * ℓ := by
    rw [hw]
    simp
  rw [hwx] at hc
  have hcN := ((L139A5.conj_mem_stb hNA hℓ).2 _).mpr hc
  have e1 : MulAut.conj ℓ ((ℓ⁻¹ * β x * ℓ)⁻¹ * x) = (β x)⁻¹ * (ℓ * x * ℓ⁻¹) := by
    rw [MulAut.conj_apply]
    group
  rwa [e1] at hcN

end CFSG.GroupTheory
