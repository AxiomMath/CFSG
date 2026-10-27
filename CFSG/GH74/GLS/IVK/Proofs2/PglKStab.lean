module

public import CFSG.GH74.GLS.IVK.Proofs2.C3PglK

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter

section Stab

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem mem_innAut_of_maps_gamma (e : K ≃* L2 F) (hD4 : HasD4Centralizers K)
    (hQ8 : ∀ u : K, orderOf u = 2 → Nonempty (↥(centralizer ({MulAut.conj u} : Set (MulAut K)) ⊓
      innDiagSub e) ≃* DihedralGroup 8))
    {V₀ : Subgroup K} {u₁ u₂ : K} (hV₀4 : Nat.card ↥V₀ = 4)
    (hV₀comm : ∀ a ∈ V₀, ∀ b ∈ V₀, a * b = b * a) (hu₁ : u₁ ∈ V₀) (hu₂ : u₂ ∈ V₀)
    (h₁ : orderOf u₁ = 2) (h₂ : orderOf u₂ = 2) (hu₁₂ : u₁ ≠ u₂) (hcomm12 : u₁ * u₂ = u₂ * u₁)
    {Γ : Subgroup K} (hΓ1 : centralizer ({u₁} : Set K) ≤ Γ) (hΓ2 : centralizer ({u₂} : Set K) ≤ Γ)
    (hΓN : Γ ≤ normalizer (V₀ : Set K)) (hΓ24 : Nat.card ↥Γ = 24) {φ : MulAut K}
    (hφX : φ ∈ innDiagSub e) (hφ : ∀ k ∈ Γ, φ k ∈ Γ) : φ ∈ innAut K := by
  have hinj := conj_injective_of_L2 e
  set V : Subgroup (MulAut K) := V₀.map (MulAut.conj : K →* MulAut K) with hV
  have hV4 : Nat.card ↥V = 4 := by
    rw [hV, Subgroup.card_map_of_injective hinj]
    exact hV₀4
  have hmemV : ∀ u ∈ V₀, MulAut.conj u ∈ V := fun u hu => Subgroup.mem_map_of_mem _ hu
  set S : Subgroup (MulAut K) := stabSub (innDiagSub e) Γ with hS
  have hφS : φ ∈ S := ⟨hφX, hφ, inv_mem_of_forall_mem Γ φ hφ⟩
  have hV₀Γ : V₀ ≤ Γ := (le_centralizer_normalizer_of_d4 hD4 hV₀4 hV₀comm hu₁ h₁).1.trans hΓ1
  have hconjS : ∀ γ ∈ Γ, MulAut.conj γ ∈ S := fun γ hγ =>
    ⟨innAut_le_innDiagSub e ⟨γ, rfl⟩,
      fun k hk => by
        rw [MulAut.conj_apply]
        exact Γ.mul_mem (Γ.mul_mem hγ hk) (Γ.inv_mem hγ),
      fun k hk => by
        rw [← map_inv, MulAut.conj_apply]
        simpa using Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hγ) hk) hγ⟩
  have hVS : V ≤ S := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ : v ∈ V₀.map (MulAut.conj : K →* MulAut K) := hv
    exact hconjS u (hV₀Γ hu)
  have hS24 : Nat.card ↥S ≤ 24 := by
    have hF4 : Nat.card ↥(V.subgroupOf S) = 4 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVS).toEquiv]
      exact hV4
    have hFn : (V.subgroupOf S).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨u, hu, hun⟩ : (n : MulAut K) ∈ V₀.map (MulAut.conj : K →* MulAut K) := hn
      have hgu : (g : MulAut K) u ∈ V₀ :=
        map_mem_of_d4 hD4 hV₀4 hV₀comm hu₁ hu₂ h₁ h₂ hu₁₂ hΓ1 hΓ2 hΓN hΓ24
          (mem_stabSub.1 g.2).2.1 u hu
      have hE : ((g * n * g⁻¹ : ↥S) : MulAut K) = MulAut.conj ((g : MulAut K) u) := by
        show (g : MulAut K) * (n : MulAut K) * (g : MulAut K)⁻¹ = _
        rw [← hun]
        exact mul_conj_mul_inv _ u
      rw [hE]
      exact Subgroup.mem_map_of_mem _ hgu⟩
    refine CFSG.QuasithinUnique.Unc25Small.card_le_24_of_klein (V.subgroupOf S) hF4 ?_
    intro g hg
    have hf1 : (⟨MulAut.conj u₁, hVS (hmemV u₁ hu₁)⟩ : ↥S) ∈ V.subgroupOf S := hmemV u₁ hu₁
    have hf2 : (⟨MulAut.conj u₂, hVS (hmemV u₂ hu₂)⟩ : ↥S) ∈ V.subgroupOf S := hmemV u₂ hu₂
    have hg1 : (g : MulAut K) * MulAut.conj u₁ = MulAut.conj u₁ * g :=
      congrArg Subtype.val (hg _ hf1)
    have hg2 : (g : MulAut K) * MulAut.conj u₂ = MulAut.conj u₂ * g :=
      congrArg Subtype.val (hg _ hf2)
    show (g : MulAut K) ∈ V
    rcases eq_of_commute_of_d8 e hQ8 h₁ h₂ hu₁₂ hcomm12 (mem_stabSub.1 g.2).1 hg1 hg2 with
      h | h | h | h
    · rw [h]; exact V.one_mem
    · rw [h]; exact hmemV u₁ hu₁
    · rw [h]; exact hmemV u₂ hu₂
    · rw [h]; exact V.mul_mem (hmemV u₂ hu₂) (hmemV u₁ hu₁)
  have hconjle : Γ.map (MulAut.conj : K →* MulAut K) ≤ S := by
    rintro _ ⟨γ, hγ, rfl⟩
    exact hconjS γ hγ
  have hcardconj : Nat.card ↥(Γ.map (MulAut.conj : K →* MulAut K)) = 24 := by
    rw [Subgroup.card_map_of_injective hinj]
    exact hΓ24
  have hSeq : Γ.map (MulAut.conj : K →* MulAut K) = S :=
    Subgroup.eq_of_le_of_card_ge hconjle (by rw [hcardconj]; exact hS24)
  have hφc : φ ∈ Γ.map (MulAut.conj : K →* MulAut K) := by
    rw [hSeq]
    exact hφS
  obtain ⟨γ, -, rfl⟩ := hφc
  exact ⟨γ, rfl⟩

end Stab

end CFSG.GH74.GLS.IVK.Proofs2
