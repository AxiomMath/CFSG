module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GC1N
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GC1U
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GC1SN

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {A : Type} [Group A] [Finite A] {H : Subgroup A} {𝒮 : Set (Subgroup A)} {x : A}

theorem l34g_act (hO3 : Asc82FactO3Cent) (hC3 : Asc82FactCent3) (hF : L34GFac H 𝒮 x)
    {C0 P : Subgroup A} (hC0F : C0 ≤ H ⊓ centralizer ({x} : Set A))
    (hC0n : ∀ f ∈ H ⊓ centralizer ({x} : Set A), ∀ c ∈ C0, f * c * f⁻¹ ∈ C0)
    (hodd : ∀ f ∈ H ⊓ centralizer ({x} : Set A), Odd (orderOf f) → f ∈ C0)
    (hfix : ∀ S ∈ 𝒮, CFSG.conjugate S x = S → ∃ c ∈ C0, c ∈ S ∧ c ≠ 1)
    (hswap : ∀ S ∈ 𝒮, CFSG.conjugate S x ≠ S → ∀ d ∈ S, d * (x * d * x⁻¹) ∈ C0)
    (hP : IsPGroup 3 ↥P) (hPx : ∀ p ∈ P, p * x = x * p)
    (hPperm : ∀ p ∈ P, ∀ S ∈ 𝒮, CFSG.conjugate S p ∈ 𝒮)
    (hPC0 : ∀ p ∈ P, ∀ c ∈ C0, p * c * p⁻¹ ∈ C0)
    (hPsub : (P.subgroupOf (P ⊔ C0)).IsSubnormal) : P = ⊥ := by
  obtain ⟨R, hPR, hRB, hR3, hRn⟩ := l34g_exists_normal_pGroup (le_sup_left : P ≤ P ⊔ C0) hP hPsub
  obtain ⟨R0, hR0C, hR03, hR0F, hR0max⟩ := l34g_exists_O3 hC0F hC0n
  have hR0 : R0 = ⊥ := l34g_propN hO3 hC3 hF hR03 (hR0C.trans hC0F) hR0F
  have hcomm : ∀ p ∈ P, ∀ c ∈ C0, p * c = c * p := by
    intro p hp c hc
    have hcB : c ∈ P ⊔ C0 := Subgroup.mem_sup_right hc
    have h1 : p * c * p⁻¹ * c⁻¹ ∈ R := by
      have := R.mul_mem (hPR hp) (hRn c hcB p⁻¹ (R.inv_mem (hPR hp)))
      simpa [mul_assoc] using this
    have h2 : p * c * p⁻¹ * c⁻¹ ∈ C0 := C0.mul_mem (hPC0 p hp c hc) (C0.inv_mem hc)
    have hN' : R ⊓ C0 ≤ R0 := by
      refine hR0max (R ⊓ C0) inf_le_right ?_ ?_
      · exact IsPGroup.to_le hR3 inf_le_left
      · intro c' hc' n hn
        exact ⟨hRn c' (Subgroup.mem_sup_right hc') n hn.1, C0.mul_mem (C0.mul_mem hc' hn.2)
          (C0.inv_mem hc')⟩
    have h3 : p * c * p⁻¹ * c⁻¹ = 1 := by
      have := hN' ⟨h1, h2⟩
      rw [hR0] at this
      exact this
    calc p * c = (p * c * p⁻¹ * c⁻¹) * (c * p) := by group
      _ = c * p := by rw [h3, one_mul]
  rw [eq_bot_iff]
  intro p hp
  obtain ⟨m, hm⟩ := hP ⟨p, hp⟩
  have hpm : p ^ 3 ^ m = 1 := by
    have := congrArg Subtype.val hm
    simpa using this
  have := l34g_propU hC3 hF hodd hfix hswap hpm (hPx p hp) (hPperm p hp) (hcomm p hp)
  exact (Subgroup.mem_bot).mpr this

end CFSG.OddStandard.SmallF3.Omega
