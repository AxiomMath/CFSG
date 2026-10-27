module

public import CFSG.GH74.Uniqueness.SU.KI1r4EData
public import CFSG.GH74.Uniqueness.SU.KI1r4ECount

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4

open Subgroup CFSG CFSG.LocalCores CFSG.GH74.Uniqueness.SU CFSG.GH74.Uniqueness.SU.K.R3
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H]

theorem commute_of_components {K L : Subgroup H} (hK : IsComponent K) (hL : IsComponent L)
    (hne : K ≠ L) (s : H) (hs : s ∈ K) (t : H) (ht : t ∈ L) : s * t = t * s := by
  rcases distinct_components_commute hK hL with h | h
  · exact absurd h hne
  · have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hs
    exact (Subgroup.mem_centralizer_iff.mp this t ht).symm

theorem L85Data.false_of_three {T : Sylow 2 H} {x y : H} {A R : Subgroup H}
    (d : L85Data T x y A R) {K₁ K₂ K₃ : Subgroup H} (h₁ : IsComponent K₁) (h₂ : IsComponent K₂)
    (h₃ : IsComponent K₃) (h12 : K₁ ≠ K₂) (h13 : K₁ ≠ K₃) (h23 : K₂ ≠ K₃) : False := by
  classical
  have hnab : ∀ K : Subgroup H, IsComponent K →
      ∃ a ∈ R ⊓ K, ∃ b ∈ R ⊓ K, a * b ≠ b * a := by
    intro K hK
    obtain ⟨z, hzK, hzc, hz1, hz2⟩ := d.hKinv K hK
    obtain ⟨a, ha, b, hb, hab⟩ := exists_noncomm_inf_of_component T hK hzK hzc hz1 hz2
    exact ⟨a, ⟨d.hLT ⟨ha.1.1, ha.1.2⟩, ha.2⟩, b, ⟨d.hLT ⟨hb.1.1, hb.1.2⟩, hb.2⟩, hab⟩
  have hindep : ∀ {K L M : Subgroup H}, IsComponent K → IsComponent L → IsComponent M →
      K ≠ L → K ≠ M → ∀ s ∈ K, ∀ t ∈ L, ∀ u ∈ M, s * t * u ∈ A → s ∈ A := by
    intro K L M hK hL hM hKL hKM s hs t ht u hu hA
    have hsc : ∀ k ∈ K, s * k = k * s := by
      intro k hk
      have hka : Commute k (s * t * u) := ((d.hAE _ hA).2 k (component_le_layer hK hk)).symm
      have hkt : Commute k t := commute_of_components hK hL hKL k hk t ht
      have hku : Commute k u := commute_of_components hK hM hKM k hk u hu
      have h1 : Commute k ((s * t * u) * u⁻¹ * t⁻¹) :=
        (hka.mul_right hku.inv_right).mul_right hkt.inv_right
      have e : (s * t * u) * u⁻¹ * t⁻¹ = s := by group
      rw [e] at h1
      exact h1.symm.eq
    exact d.hZEA s (component_le_layer hK hs) (center_of_component_central hK hs hsc)
  have c12 := commute_of_components h₁ h₂ h12
  have c13 := commute_of_components h₁ h₃ h13
  have c23 := commute_of_components h₂ h₃ h23
  have hRK : ∀ K : Subgroup H, R ⊓ K ≤ K := fun K => inf_le_right
  have hcard := card_ge_of_three_commuting R A (R ⊓ K₁) (R ⊓ K₂) (R ⊓ K₃) inf_le_left inf_le_left
    inf_le_left (d.rdata.A_le) d.hAc
    (fun s hs t ht => c12 s hs.2 t ht.2) (fun s hs t ht => c13 s hs.2 t ht.2)
    (fun s hs t ht => c23 s hs.2 t ht.2) (hnab K₁ h₁) (hnab K₂ h₂) (hnab K₃ h₃)
    (fun s₁ hs₁ s₂ hs₂ s₃ hs₃ h => hindep h₁ h₂ h₃ h12 h13 s₁ hs₁.2 s₂ hs₂.2 s₃ hs₃.2 h)
    (fun s₁ hs₁ s₂ hs₂ s₃ hs₃ h => by
      refine hindep h₂ h₁ h₃ h12.symm h23 s₂ hs₂.2 s₁ hs₁.2 s₃ hs₃.2 ?_
      have : s₂ * s₁ = s₁ * s₂ := (c12 s₁ hs₁.2 s₂ hs₂.2).symm
      rw [this]; exact h)
    (fun s₁ hs₁ s₂ hs₂ s₃ hs₃ h => by
      refine hindep h₃ h₁ h₂ h13.symm h23.symm s₃ hs₃.2 s₁ hs₁.2 s₂ hs₂.2 ?_
      have e1 : s₃ * s₁ = s₁ * s₃ := (c13 s₁ hs₁.2 s₃ hs₃.2).symm
      have e2 : s₃ * s₁ * s₂ = s₁ * s₂ * s₃ := by
        calc s₃ * s₁ * s₂ = s₁ * s₃ * s₂ := by rw [e1]
          _ = s₁ * (s₃ * s₂) := by group
          _ = s₁ * (s₂ * s₃) := by rw [(c23 s₂ hs₂.2 s₃ hs₃.2).symm]
          _ = s₁ * s₂ * s₃ := by group
      rw [e2]; exact h)
  rw [d.rdata.A_card, d.h64] at hcard
  omega

theorem L85Data.false_of_moved {T : Sylow 2 H} {x y : H} {A R : Subgroup H}
    (d : L85Data T x y A R) (hy3 : IsPGroup 3 (zpowers y))
    (hmoved : ∀ K : Subgroup H, IsComponent K → ¬ ∀ k ∈ K, y * k * y⁻¹ ∈ K)
    (hcomp : ∃ K : Subgroup H, IsComponent K) : False := by
  classical
  obtain ⟨K₁, hK₁⟩ := hcomp
  set K₂ : Subgroup H := K₁.map (MulAut.conj y).toMonoidHom with hK₂def
  set K₃ : Subgroup H := K₂.map (MulAut.conj y).toMonoidHom with hK₃def
  have hK₂ : IsComponent K₂ := isComponent_map_mulEquiv (MulAut.conj y) hK₁
  have hK₃ : IsComponent K₃ := isComponent_map_mulEquiv (MulAut.conj y) hK₂
  have hinj : Function.Injective (Subgroup.map (MulAut.conj y).toMonoidHom) :=
    Subgroup.map_injective (MulAut.conj y).injective
  have hy1 : ¬ ∀ k ∈ K₁, y * k * y⁻¹ ∈ K₁ := hmoved K₁ hK₁
  have hmem2 : ∀ k ∈ K₁, y * k * y⁻¹ ∈ K₂ := fun k hk => ⟨k, hk, by simp [MulAut.conj_apply]⟩
  have h12 : K₁ ≠ K₂ := by
    intro h
    apply hy1
    intro k hk
    rw [h]
    exact hmem2 k hk
  have h23 : K₂ ≠ K₃ := fun h => h12 (hinj h)
  have h13 : K₁ ≠ K₃ := by
    intro h
    have hy2 : ∀ k ∈ K₁, y ^ 2 * k * (y ^ 2)⁻¹ ∈ K₁ := by
      intro k hk
      have : y * (y * k * y⁻¹) * y⁻¹ ∈ K₃ := ⟨y * k * y⁻¹, hmem2 k hk, by simp [MulAut.conj_apply]⟩
      rw [← h] at this
      have e : y ^ 2 * k * (y ^ 2)⁻¹ = y * (y * k * y⁻¹) * y⁻¹ := by rw [pow_two]; group
      rwa [e]
    have hy2N : y ^ 2 ∈ normalizer (K₁ : Set H) :=
      CFSG.GH74.Uniqueness.SU.K.R3.Pow.mem_normalizer_of_forall_mem K₁ hy2
    obtain ⟨n, hn⟩ := hy3 ⟨y, Subgroup.mem_zpowers y⟩
    have hyn : y ^ 3 ^ n = 1 := congrArg Subtype.val hn
    obtain ⟨m, hm⟩ : Odd (3 ^ n) := Odd.pow (by decide)
    have hyinv : y⁻¹ = (y ^ 2) ^ m := by
      have h1 : y * y ^ (2 * m) = 1 := by rw [← pow_succ', ← hm]; exact hyn
      rw [← pow_mul]
      exact inv_eq_of_mul_eq_one_right h1
    have hyN : y ∈ normalizer (K₁ : Set H) := by
      have : y⁻¹ ∈ normalizer (K₁ : Set H) := hyinv ▸ Subgroup.pow_mem _ hy2N m
      simpa using Subgroup.inv_mem _ this
    apply hy1
    intro k hk
    exact (Subgroup.mem_normalizer_iff.mp hyN k).mp hk
  exact d.false_of_three hK₁ hK₂ hK₃ h12 h13 h23

end CFSG.GH74.Uniqueness.SU.K.R4
