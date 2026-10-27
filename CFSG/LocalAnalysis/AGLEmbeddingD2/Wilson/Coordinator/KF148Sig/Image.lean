module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.Action

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig

open Subgroup CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory

variable {Γ : Type*} [Group Γ] {L K : Subgroup Γ} (hKL : K ≤ L) {X : Type*} [Group X]
  (ψ : L ⧸ aschbacherSolvableCore 3 L ≃* X)

@[expose] noncomputable def kappa : K →* X := (toX ψ).comp (inclusion hKL)

theorem kappa_apply (k : K) : kappa hKL ψ k = toX ψ (inclusion hKL k) := rfl

theorem kappa_eq_one_iff (k : K) :
    kappa hKL ψ k = 1 ↔ inclusion hKL k ∈ aschbacherSolvableCore 3 L :=
  toX_eq_one_iff ψ _

@[expose] noncomputable def kerKappaToTheta :
    (kappa hKL ψ).ker →* aschbacherSolvableCore 3 L where
  toFun k := ⟨inclusion hKL k, (kappa_eq_one_iff hKL ψ k).1 k.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem kerKappaToTheta_injective : Function.Injective (kerKappaToTheta hKL ψ) := by
  intro k k' h
  have h' := congrArg (fun z : aschbacherSolvableCore 3 L => ((z : L) : Γ)) h
  exact Subtype.ext (Subtype.ext h')

variable [Finite Γ]

theorem isSolvable_ker_kappa : Group.IsSolvable (kappa hKL ψ).ker := by
  have h := (solvable_prime_complement_core_characterization (H := L) Nat.prime_three).1
  exact Group.isSolvable_of_isSolvable_injective (kerKappaToTheta_injective hKL ψ)

theorem coprime_card_ker_kappa : Nat.Coprime 3 (Nat.card (kappa hKL ψ).ker) := by
  have h := (solvable_prime_complement_core_characterization (H := L) Nat.prime_three).2.2.1
  have hd := Subgroup.card_dvd_of_injective _ (kerKappaToTheta_injective hKL ψ)
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 fun h3 => h (h3.trans hd)

variable {A : Subgroup Γ} (hAL : A ≤ normalizer (L : Set Γ)) (hAK : A ≤ normalizer (K : Set Γ))
  (hc : center X = ⊥) (hodd : ∀ α : MulAut X, Odd (orderOf α) → ∃ g : X, α = MulAut.conj g)
  (hA3 : ∀ a ∈ A, a ^ 3 = 1)

omit [Finite Γ] in
theorem kappa_conj (a : A) (k : K) :
    kappa hKL ψ ⟨a * k * (a : Γ)⁻¹, (hAK a.2 k).mp k.2⟩ =
      innerHom hAL ψ hc hodd hA3 a * kappa hKL ψ k * (innerHom hAL ψ hc hodd hA3 a)⁻¹ := by
  rw [kappa_apply, kappa_apply, ← toX_conj hAL ψ hc hodd hA3 a]
  rfl

omit [Finite Γ] in
include hAK in
theorem range_innerHom_le_normalizer :
    (innerHom hAL ψ hc hodd hA3).range ≤ normalizer ((kappa hKL ψ).range : Set X) := by
  rintro _ ⟨a, rfl⟩
  rw [mem_normalizer_iff]
  intro z
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨_, kappa_conj hKL ψ hAL hAK hc hodd hA3 a k⟩
  · rintro ⟨k, hk⟩
    refine ⟨⟨(a : Γ)⁻¹ * k * a, by simpa using (hAK (inv_mem a.2) k).mp k.2⟩, ?_⟩
    have h := kappa_conj hKL ψ hAL hAK hc hodd hA3 a⁻¹ k
    rw [map_inv] at h
    have e : (⟨((a⁻¹ : A) : Γ) * k * ((a⁻¹ : A) : Γ)⁻¹, (hAK (a⁻¹ : A).2 k).mp k.2⟩ : K) =
        ⟨(a : Γ)⁻¹ * k * a, by simpa using (hAK (inv_mem a.2) k).mp k.2⟩ :=
      Subtype.ext (by simp)
    rw [e] at h
    rw [h, hk]
    group

end CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig
