module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GC1Pk1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GC1Pk2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PBase
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GC1NDiag

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {A : Type} [Group A] [Finite A] {H : Subgroup A} {𝒮 : Set (Subgroup A)} {x : A}

private theorem l34g_centralizes_of_fixed (hO3 : Asc82FactO3Cent) (hC3 : Asc82FactCent3)
    (hF : L34GFac H 𝒮 x) {N : Subgroup A} (hN : IsPGroup 3 ↥N)
    (hNF : N ≤ H ⊓ centralizer ({x} : Set A))
    (hNn : ∀ f ∈ H ⊓ centralizer ({x} : Set A), ∀ n ∈ N, f * n * f⁻¹ ∈ N)
    {n : A} (hn : n ∈ N) (hnH : n ∈ H) (hnx : n * x = x * n)
    {S : Subgroup A} (hS : S ∈ 𝒮) (hconjS : CFSG.conjugate S n = S)
    (hxS : CFSG.conjugate S x = S) : ∀ s ∈ S, n * s = s * n := by
  let N' : Subgroup A := N ⊓ S
  have hN'3 : IsPGroup 3 ↥N' := hN.to_inf_left
  have hN'le : N' ≤ S ⊓ centralizer ({x} : Set A) := fun a ha => ⟨ha.2, (hNF ha.1).2⟩
  have hN'n : ∀ c ∈ S ⊓ centralizer ({x} : Set A), ∀ m ∈ N', c * m * c⁻¹ ∈ N' := by
    intro c hc m hm
    have hcF : c ∈ H ⊓ centralizer ({x} : Set A) := ⟨hF.le S hS hc.1, hc.2⟩
    exact ⟨hNn c hcF m hm.1, S.mul_mem (S.mul_mem hc.1 hm.2) (S.inv_mem hc.1)⟩
  have hN'bot : N' = ⊥ :=
    l34g_pk1 hO3 (hF.simple S hS) hF.invol hxS hN'3 hN'le hN'n
  have hcommF : ∀ c ∈ S ⊓ centralizer ({x} : Set A), n * c = c * n := by
    intro c hc
    have hcF : c ∈ H ⊓ centralizer ({x} : Set A) := ⟨hF.le S hS hc.1, hc.2⟩
    have hwN : n * c * n⁻¹ * c⁻¹ ∈ N := by
      have h1 : c * n⁻¹ * c⁻¹ ∈ N := hNn c hcF n⁻¹ (N.inv_mem hn)
      have h2 : n * (c * n⁻¹ * c⁻¹) ∈ N := N.mul_mem hn h1
      rw [show n * c * n⁻¹ * c⁻¹ = n * (c * n⁻¹ * c⁻¹) by group]
      exact h2
    have hwS : n * c * n⁻¹ * c⁻¹ ∈ S :=
      S.mul_mem (hF.normal S hS n hnH c hc.1) (S.inv_mem hc.1)
    have hw : n * c * n⁻¹ * c⁻¹ = 1 := by
      have hmem : n * c * n⁻¹ * c⁻¹ ∈ N' := ⟨hwN, hwS⟩
      rw [hN'bot] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hc' : n * c * n⁻¹ = c := mul_inv_eq_one.mp hw
    calc n * c = n * c * n⁻¹ * n := by group
      _ = c * n := by rw [hc']
  obtain ⟨m, hm⟩ := hN ⟨n, hn⟩
  have hn3 : n ^ 3 ^ m = 1 := by
    have h := congrArg Subtype.val hm
    simpa using h
  intro s hs
  exact l34g_pk2 hC3 (hF.simple S hS) hF.invol hxS hn3 hconjS hnx
    (fun c hc _ => hcommF c hc) s hs

private theorem l34g_centralizes_of_swap (hF : L34GFac H 𝒮 x) {N : Subgroup A}
    (hN : IsPGroup 3 ↥N)
    (hNn : ∀ f ∈ H ⊓ centralizer ({x} : Set A), ∀ n ∈ N, f * n * f⁻¹ ∈ N)
    {n : A} (hn : n ∈ N) (hnH : n ∈ H) (hnx : n * x = x * n)
    {S : Subgroup A} (hS : S ∈ 𝒮) (hxS : CFSG.conjugate S x ≠ S) :
    ∀ s ∈ S, n * s = s * n := by
  have hnorm : ∀ a ∈ S, n * a * n⁻¹ ∈ S := fun a ha => hF.normal S hS n hnH a ha
  have hNSbot : l34gNS hF hS hxS N = ⊥ := l34gNS_eq_bot hF hS hxS hN hNn
  intro d hd
  have hndS : n * d * n⁻¹ ∈ S := hnorm d hd
  have hwS : n * d * n⁻¹ * d⁻¹ ∈ S := S.mul_mem hndS (S.inv_mem hd)
  have hwN : l34gDiag x (n * d * n⁻¹ * d⁻¹) ∈ N := by
    rw [l34gDiag_mul hF hS hxS hndS (S.inv_mem hd),
        l34gDiag_conj_n hnx (d := d), l34gDiag_inv hF hS hxS hd]
    have h1 : l34gDiag x d * n⁻¹ * (l34gDiag x d)⁻¹ ∈ N :=
      hNn (l34gDiag x d) (l34gDiag_mem hF hS hxS hd) n⁻¹ (N.inv_mem hn)
    rw [show n * l34gDiag x d * n⁻¹ * (l34gDiag x d)⁻¹
          = n * (l34gDiag x d * n⁻¹ * (l34gDiag x d)⁻¹) by group]
    exact N.mul_mem hn h1
  have hwNS : n * d * n⁻¹ * d⁻¹ ∈ l34gNS hF hS hxS N :=
    show n * d * n⁻¹ * d⁻¹ ∈ S ∧ l34gDiag x (n * d * n⁻¹ * d⁻¹) ∈ N from ⟨hwS, hwN⟩
  have hw1 : n * d * n⁻¹ * d⁻¹ = 1 := by
    have hw_bot : n * d * n⁻¹ * d⁻¹ ∈ (⊥ : Subgroup A) := by
      rw [← hNSbot]
      exact hwNS
    exact Subgroup.mem_bot.mp hw_bot
  have hnd : n * d * n⁻¹ = d := mul_inv_eq_one.mp hw1
  calc n * d = n * d * n⁻¹ * n := by group
    _ = d * n := by rw [hnd]

theorem l34g_propN (hO3 : Asc82FactO3Cent) (hC3 : Asc82FactCent3) (hF : L34GFac H 𝒮 x)
    {N : Subgroup A} (hN : IsPGroup 3 ↥N) (hNF : N ≤ H ⊓ centralizer ({x} : Set A))
    (hNn : ∀ f ∈ H ⊓ centralizer ({x} : Set A), ∀ n ∈ N, f * n * f⁻¹ ∈ N) : N = ⊥ := by
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  have hnF : n ∈ H ⊓ centralizer ({x} : Set A) := hNF hn
  have hnH : n ∈ H := hnF.1
  have hnx : n * x = x * n :=
    ((Subgroup.mem_centralizer_iff.mp hnF.2) x (Set.mem_singleton x)).symm
  apply hF.eq_one_of_centralizes
  intro S hS s hs
  have hconjS : CFSG.conjugate S n = S := by
    rw [sec63P_conjugate_eq_iff, Subgroup.mem_normalizer_iff]
    intro a
    exact ⟨fun ha => hF.normal S hS n hnH a ha, fun ha => by
      have h := hF.normal S hS n⁻¹ (H.inv_mem hnH) (n * a * n⁻¹) ha
      rwa [show n⁻¹ * (n * a * n⁻¹) * (n⁻¹)⁻¹ = a by group] at h⟩
  by_cases hxS : CFSG.conjugate S x = S
  · exact l34g_centralizes_of_fixed hO3 hC3 hF hN hNF hNn hn hnH hnx hS hconjS hxS s hs
  · exact l34g_centralizes_of_swap hF hN hNn hn hnH hnx hS hxS s hs

end CFSG.OddStandard.SmallF3.Omega
