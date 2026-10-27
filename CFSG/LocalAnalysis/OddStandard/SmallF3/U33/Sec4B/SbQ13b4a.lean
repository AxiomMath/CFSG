module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13b3a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13b2a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13b1
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem q13b_F_le_U (h : Q13Om t L S x₁ x₂ lam rho tau om) {𝒮 F : Subgroup G}
    (h𝒮 : IsPGroup 2 𝒮) (hU : ctxU t tau x₁ x₂ lam ≤ 𝒮) (hF : NormalIn F 𝒮)
    (hFe : CFSG.Open.IsElemAbelian 2 F) (hFc : Nat.card F = 4) :
    F ≤ ctxU t tau x₁ x₂ lam := by
  intro f hfF
  have hFne : F ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card F = 1 := by rw [hbot, Subgroup.card_bot]
    omega
  have hzF : (x₁ * x₂) ^ 2 ∈ F := q13b_z_mem_of_normal h h𝒮 hU hF hFne
  obtain ⟨hz1, hz2⟩ := q13b_z_facts h
  have ht𝒮 : t ∈ 𝒮 := hU (q13b_O_le_U h (q13b_t_mem_O h))
  have hz_comm_t : t * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * t :=
    q13b_z_central h h𝒮 hU t ht𝒮
  have hF0c : zpowers ((x₁ * x₂) ^ 2) ≤ centralizer ({t} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hz_comm_t.symm)
  have hF0_le : zpowers ((x₁ * x₂) ^ 2) ≤ F := Subgroup.zpowers_le.mpr hzF
  have hcard0 : Nat.card (zpowers ((x₁ * x₂) ^ 2)) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (p := 2) (by simpa [pow_two] using hz2) hz1
  have hcard : Nat.card F = 2 * Nat.card (zpowers ((x₁ * x₂) ^ 2)) := by
    rw [hFc, hcard0]
  have hcomm := q13b_comm_mem_of_index_two (F₀ := zpowers ((x₁ * x₂) ^ 2)) hF0_le hcard
    (g := t) (fun x hx => hF.2 t ht𝒮 x hx)
    (fun x hx => by
      have htx : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp (hF0c hx)
      have hx' : t * x * t⁻¹ = x := by rw [← htx]; group
      rw [hx']; exact hx)
    (fun x hx => by
      have htx : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp (hF0c hx)
      have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (q13a_t_mul_self h)
      rw [htinv]
      have hx' : t * x * t = x := by rw [← htx, mul_assoc, q13a_t_mul_self h, mul_one]
      rw [hx']; exact hx)
  have hmem := hcomm f hfF
  rcases q13b_mem_zpowers_sq hz2 hmem with h1 | h1
  ·
    have htf : t * f = f * t := by
      have hconj : t * f * t⁻¹ = f := by
        calc t * f * t⁻¹ = t * f * t⁻¹ * f⁻¹ * f := by group
          _ = 1 * f := by rw [h1]
          _ = f := by group
      calc t * f = (t * f * t⁻¹) * t := by group
        _ = f * t := by rw [hconj]
    have hfS : f ∈ S := by
      have hthis : f ∈ 𝒮 ⊓ centralizer ({t} : Set G) :=
        ⟨hF.1 hfF, Subgroup.mem_centralizer_singleton_iff.mpr htf.symm⟩
      rwa [q13b_cent_t h h𝒮 hU] at hthis
    exact h.c11.S_le_U hfS
  ·
    have hff : f * f = 1 := CFSG.Open.IsElemAbelian.mul_self_eq_one hFe hfF
    have hzf : f * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * f :=
      q13b_z_central h h𝒮 hU f (hF.1 hfF)
    have hzf_inv : f⁻¹ * (x₁ * x₂) ^ 2 * f = (x₁ * x₂) ^ 2 := by
      calc f⁻¹ * (x₁ * x₂) ^ 2 * f = f⁻¹ * ((x₁ * x₂) ^ 2 * f) := by group
        _ = f⁻¹ * (f * (x₁ * x₂) ^ 2) := by rw [← hzf]
        _ = (x₁ * x₂) ^ 2 := by group
    have hfzf : f * (x₁ * x₂) ^ 2 * f = (x₁ * x₂) ^ 2 := by
      calc f * (x₁ * x₂) ^ 2 * f = (f * (x₁ * x₂) ^ 2) * f := rfl
        _ = ((x₁ * x₂) ^ 2 * f) * f := by rw [hzf]
        _ = (x₁ * x₂) ^ 2 * (f * f) := by group
        _ = (x₁ * x₂) ^ 2 := by rw [hff, mul_one]
    have hftz : t * f * t⁻¹ = (x₁ * x₂) ^ 2 * f := by
      calc t * f * t⁻¹ = t * f * t⁻¹ * f⁻¹ * f := by group
        _ = (x₁ * x₂) ^ 2 * f := by rw [h1]
    have htf : t * f = (x₁ * x₂) ^ 2 * f * t := by
      calc t * f = (t * f * t⁻¹) * t := by group
        _ = ((x₁ * x₂) ^ 2 * f) * t := by rw [hftz]
    have hleft : f⁻¹ * t * f = (x₁ * x₂) ^ 2 * t := by
      calc f⁻¹ * t * f = f⁻¹ * (t * f) := by group
        _ = f⁻¹ * ((x₁ * x₂) ^ 2 * f * t) := by rw [htf]
        _ = (f⁻¹ * (x₁ * x₂) ^ 2 * f) * t := by group
        _ = (x₁ * x₂) ^ 2 * t := by rw [hzf_inv]
    have hft' : f * t * f⁻¹ = (x₁ * x₂) ^ 2 * t := by
      have hfinv : f⁻¹ = f := inv_eq_of_mul_eq_one_right hff
      calc f * t * f⁻¹ = f * (t * f) := by rw [hfinv]; group
        _ = f * ((x₁ * x₂) ^ 2 * f * t) := by rw [htf]
        _ = (f * (x₁ * x₂) ^ 2 * f) * t := by group
        _ = (x₁ * x₂) ^ 2 * t := by rw [hfzf]
    have hS_cent : S ≤ centralizer ({t} : Set G) := by
      rw [← q13b_cent_t h h𝒮 hU]; exact inf_le_right
    have hXS_mem : ∀ s ∈ S, f⁻¹ * s * f ∈ S := by
      intro s hs
      have hs𝒮 : s ∈ 𝒮 := hU (h.c11.S_le_U hs)
      have hst : s * t = t * s :=
        Subgroup.mem_centralizer_singleton_iff.mp (hS_cent hs)
      have hsz : s * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * s := q13b_z_central h h𝒮 hU s hs𝒮
      have hX𝒮 : f⁻¹ * s * f ∈ 𝒮 :=
        𝒮.mul_mem (𝒮.mul_mem (𝒮.inv_mem (hF.1 hfF)) hs𝒮) (hF.1 hfF)
      have hXcent : f⁻¹ * s * f ∈ centralizer ({t} : Set G) := by
        refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
        have hszt : s * ((x₁ * x₂) ^ 2 * t) * s⁻¹ = (x₁ * x₂) ^ 2 * t := by
          calc s * ((x₁ * x₂) ^ 2 * t) * s⁻¹
              = (s * (x₁ * x₂) ^ 2 * s⁻¹) * (s * t * s⁻¹) := by group
            _ = (x₁ * x₂) ^ 2 * t := by
                  rw [show s * (x₁ * x₂) ^ 2 * s⁻¹ = (x₁ * x₂) ^ 2 by
                        rw [hsz]; group,
                      show s * t * s⁻¹ = t by rw [hst]; group]
        have hconj : (f⁻¹ * s * f) * t * (f⁻¹ * s * f)⁻¹ = t := by
          calc (f⁻¹ * s * f) * t * (f⁻¹ * s * f)⁻¹
              = f⁻¹ * (s * (f * t * f⁻¹) * s⁻¹) * f := by group
            _ = f⁻¹ * (s * ((x₁ * x₂) ^ 2 * t) * s⁻¹) * f := by rw [hft']
            _ = f⁻¹ * ((x₁ * x₂) ^ 2 * t) * f := by rw [hszt]
            _ = t := by
                  calc f⁻¹ * ((x₁ * x₂) ^ 2 * t) * f
                      = (f⁻¹ * (x₁ * x₂) ^ 2 * f) * (f⁻¹ * t * f) := by group
                    _ = (x₁ * x₂) ^ 2 * ((x₁ * x₂) ^ 2 * t) := by rw [hzf_inv, hleft]
                    _ = t := by rw [← mul_assoc, hz2, one_mul]
        calc (f⁻¹ * s * f) * t
            = ((f⁻¹ * s * f) * t * (f⁻¹ * s * f)⁻¹) * (f⁻¹ * s * f) := by group
          _ = t * (f⁻¹ * s * f) := by rw [hconj]
      have hmem : f⁻¹ * s * f ∈ 𝒮 ⊓ centralizer ({t} : Set G) := ⟨hX𝒮, hXcent⟩
      rwa [q13b_cent_t h h𝒮 hU] at hmem
    have hfinv_norm : f⁻¹ ∈ normalizer (S : Set G) :=
      Subgroup.mem_normalizer_fintype (fun s hs => by
        have : f⁻¹ * s * (f⁻¹)⁻¹ = f⁻¹ * s * f := by group
        rw [this]
        exact hXS_mem s hs)
    have hf_norm : f ∈ normalizer (S : Set G) := by
      have := Subgroup.inv_mem (Subgroup.normalizer (S : Set G)) hfinv_norm
      simpa using this
    exact q13b_N_S_le_U h h𝒮 hU ⟨hf_norm, hF.1 hfF⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
