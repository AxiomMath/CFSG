module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup
open scoped Pointwise

theorem exists_conj_mem_sylow_big_cent {Γ : Type*} [Group Γ] [Finite Γ] {P : Subgroup Γ}
    (hP : IsPGroup 2 P) (hPmax : ∀ Q : Subgroup Γ, IsPGroup 2 Q → P ≤ Q → Q = P)
    {ψ : Γ} (hψ : ψ * ψ = 1) {k : ℕ}
    (hk : 2 ^ k ∣ Nat.card ↥(Subgroup.centralizer ({ψ} : Set Γ))) :
    ∃ g : Γ, g * ψ * g⁻¹ ∈ P ∧
      2 ^ k ≤ Nat.card ↥(P ⊓ Subgroup.centralizer ({g * ψ * g⁻¹} : Set Γ)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨H, hH⟩ : ∃ H : Subgroup ↥(Subgroup.centralizer ({ψ} : Set Γ)),
      Nat.card H = 2 ^ k :=
    Sylow.exists_subgroup_card_pow_prime 2 hk
  have hC2 : IsPGroup 2 (H.map (Subgroup.centralizer ({ψ} : Set Γ)).subtype) :=
    (IsPGroup.of_card hH).map _
  have hCK : H.map (Subgroup.centralizer ({ψ} : Set Γ)).subtype ≤
      Subgroup.centralizer ({ψ} : Set Γ) := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hCcard : Nat.card (H.map (Subgroup.centralizer ({ψ} : Set Γ)).subtype) = 2 ^ k := by
    rw [Subgroup.card_map_of_injective Subtype.val_injective, hH]
  set C : Subgroup Γ := H.map (Subgroup.centralizer ({ψ} : Set Γ)).subtype with hC
  have hψ2 : IsPGroup 2 (zpowers ψ : Subgroup Γ) := by
    have hord : orderOf ψ ∣ 2 ^ 1 := by
      rw [pow_one]
      exact orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hψ)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hCN : C ≤ Subgroup.normalizer ((zpowers ψ : Subgroup Γ) : Set Γ) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro x hx
    have hxψ : Commute ψ x := (mem_centralizer_singleton_iff.1 (hCK hx)).symm
    refine mem_centralizer_iff.2 ?_
    intro h hh
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact (Commute.zpow_left hxψ m).eq
  have hD2 : IsPGroup 2 (C ⊔ zpowers ψ : Subgroup Γ) := hC2.to_sup_of_normal_right' hψ2 hCN
  obtain ⟨P', hP'⟩ := IsPGroup.exists_le_sylow hD2
  have hψP' : ψ ∈ (P' : Subgroup Γ) := hP' (mem_sup_right (mem_zpowers ψ))
  have hCP' : C ≤ (P' : Subgroup Γ) := le_sup_left.trans hP'
  let Pz : Sylow 2 Γ :=
    { toSubgroup := P, isPGroup' := hP, is_maximal' := fun {Q} hQ hle => hPmax Q hQ hle }
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ P' Pz
  have hgP' : MulAut.conj g • (P' : Subgroup Γ) = P := by
    rw [← Sylow.coe_subgroup_smul]
    exact congrArg (fun Q : Sylow 2 Γ => (Q : Subgroup Γ)) hg
  have hgP : ∀ x ∈ (P' : Subgroup Γ), g * x * g⁻¹ ∈ P := by
    intro x hx
    have h1 := Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) (P' : Subgroup Γ) hx
    rw [hgP'] at h1
    simpa [MulAut.smul_def, MulAut.conj_apply] using h1
  refine ⟨g, hgP ψ hψP', ?_⟩
  have hsub : C.map (MulAut.conj g).toMonoidHom ≤
      P ⊓ Subgroup.centralizer ({g * ψ * g⁻¹} : Set Γ) := by
    rintro _ ⟨x, hx, rfl⟩
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have := hgP x (hCP' hx)
      simpa [MulAut.conj_apply] using this
    · refine mem_centralizer_singleton_iff.2 ?_
      have hxψ : x * ψ = ψ * x := mem_centralizer_singleton_iff.1 (hCK hx)
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc g * x * g⁻¹ * (g * ψ * g⁻¹) = g * (x * ψ) * g⁻¹ := by group
        _ = g * (ψ * x) * g⁻¹ := by rw [hxψ]
        _ = g * ψ * g⁻¹ * (g * x * g⁻¹) := by group
  have hcardC : Nat.card (C.map (MulAut.conj g).toMonoidHom) = 2 ^ k := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hCcard]
  rw [← hcardC]
  exact Subgroup.card_le_of_le hsub

end CFSG.EvenSporadicStandard.Fin76b
