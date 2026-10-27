module

public import CFSG.LargeExtraspecial.S2Basic

public section

namespace CFSG.LargeExtraspecial.S14

open Module Polynomial CFSG.RankThree.OrthogonalInvolutions

variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

@[expose] def normKer (t : M ≃ₗ[ZMod 2] M) : Submodule (ZMod 2) M where
  carrier := {v | v + t v + t (t v) = 0}
  add_mem' {u v} hu hv := by
    change u + t u + t (t u) = 0 at hu
    change v + t v + t (t v) = 0 at hv
    change u + v + t (u + v) + t (t (u + v)) = 0
    simp only [map_add]
    calc u + v + (t u + t v) + (t (t u) + t (t v)) = (u + t u + t (t u)) + (v + t v + t (t v)) :=
          by abel
      _ = 0 := by rw [hu, hv, add_zero]
  zero_mem' := by simp
  smul_mem' c v hv := by
    change v + t v + t (t v) = 0 at hv
    change c • v + t (c • v) + t (t (c • v)) = 0
    simp only [map_smul]
    rw [← smul_add, ← smul_add, hv, smul_zero]

theorem mem_normKer {t : M ≃ₗ[ZMod 2] M} {v : M} : v ∈ normKer t ↔ v + t v + t (t v) = 0 :=
  Iff.rfl

variable {t : M ≃ₗ[ZMod 2] M}

theorem normKer_mapsTo {v : M} (hv : v ∈ normKer t) : t v ∈ normKer t := by
  rw [mem_normKer] at hv ⊢
  rw [← map_add, ← map_add, hv, map_zero]

theorem ord3_mem_fixSpace (ht : ∀ v, t (t (t v)) = v) (v : M) :
    v + t v + t (t v) ∈ fixSpace t := by
  rw [mem_fixSpace, map_add, map_add, ht]
  abel

theorem ord3_mem_normKer (ht : ∀ v, t (t (t v)) = v) (v : M) :
    t v + t (t v) ∈ normKer t := by
  rw [mem_normKer]
  simp only [map_add, ht]
  calc t v + t (t v) + (t (t v) + v) + (v + t v) = (t v + t v) + (t (t v) + t (t v)) + (v + v) :=
        by abel
    _ = 0 := by simp only [ZModModule.add_self]

theorem ord3_decomp (v : M) : v = (v + t v + t (t v)) + (t v + t (t v)) := by
  calc v = v + (t v + t v) + (t (t v) + t (t v)) := by
        rw [ZModModule.add_self, ZModModule.add_self, add_zero, add_zero]
    _ = (v + t v + t (t v)) + (t v + t (t v)) := by abel

theorem ord3_eq_zero {v : M} (h1 : v ∈ fixSpace t) (h2 : v ∈ normKer t) : v = 0 := by
  rw [mem_fixSpace] at h1
  rw [mem_normKer, h1, h1] at h2
  rwa [ZModModule.add_self, zero_add] at h2

theorem ord3_sup_eq (ht : ∀ v, t (t (t v)) = v) {S : Submodule (ZMod 2) M}
    (hS : ∀ v ∈ S, t v ∈ S) : S ⊓ normKer t ⊔ S ⊓ fixSpace t = S := by
  refine le_antisymm (sup_le inf_le_left inf_le_left) fun v hv => ?_
  rw [ord3_decomp (t := t) v, add_comm]
  have h1 : t v ∈ S := hS v hv
  have h2 : t (t v) ∈ S := hS _ h1
  exact Submodule.add_mem_sup ⟨add_mem h1 h2, ord3_mem_normKer ht v⟩
    ⟨add_mem (add_mem hv h1) h2, ord3_mem_fixSpace ht v⟩

theorem ord3_inf_eq_bot (S : Submodule (ZMod 2) M) :
    S ⊓ normKer t ⊓ (S ⊓ fixSpace t) = ⊥ := by
  rw [eq_bot_iff]
  rintro v ⟨⟨-, h2⟩, -, h1⟩
  exact (Submodule.mem_bot _).mpr (ord3_eq_zero h1 h2)

theorem irreducible_X_sq_add_X_add_one :
    Irreducible (X ^ 2 + X + 1 : (ZMod 2)[X]) := by
  have hdeg : (X ^ 2 + X + 1 : (ZMod 2)[X]).natDegree = 2 := by compute_degree!
  refine irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; decide) fun x hx => ?_
  rw [IsRoot, eval_add, eval_add, eval_pow, eval_X, eval_one] at hx
  revert x hx
  decide

variable [FiniteDimensional (ZMod 2) M]

theorem two_dvd_finrank_of_le_normKer {S : Submodule (ZMod 2) M} (hS : ∀ v ∈ S, t v ∈ S)
    (hSN : S ≤ normKer t) : 2 ∣ finrank (ZMod 2) S := by
  let T : Module.End (ZMod 2) S := (t : M →ₗ[ZMod 2] M).restrict hS
  have hT : aeval T (X ^ 2 + X + 1 : (ZMod 2)[X]) = 0 := by
    rw [map_add, map_add, map_pow, aeval_X, map_one]
    refine LinearMap.ext fun w => Subtype.ext ?_
    have h := hSN w.2
    rw [mem_normKer] at h
    rw [LinearMap.add_apply, LinearMap.add_apply, pow_two, Module.End.mul_apply,
      Module.End.one_apply]
    simp only [Submodule.coe_add, LinearMap.zero_apply, Submodule.coe_zero, T,
      LinearMap.restrict_apply, LinearEquiv.coe_coe]
    rw [← h]
    abel
  have := S2.natDegree_dvd_finrank_of_aeval_eq_zero irreducible_X_sq_add_X_add_one hT
  have hdeg : (X ^ 2 + X + 1 : (ZMod 2)[X]).natDegree = 2 := by compute_degree!
  rwa [hdeg] at this

theorem ord3_finrank (ht : ∀ v, t (t (t v)) = v) {S : Submodule (ZMod 2) M}
    (hS : ∀ v ∈ S, t v ∈ S) :
    finrank (ZMod 2) (S ⊓ normKer t : Submodule (ZMod 2) M) +
      finrank (ZMod 2) (S ⊓ fixSpace t : Submodule (ZMod 2) M) = finrank (ZMod 2) S := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (S ⊓ normKer t) (S ⊓ fixSpace t)
  rw [ord3_sup_eq ht hS, ord3_inf_eq_bot, finrank_bot, add_zero] at h
  exact h.symm

theorem finrank_inf_fixSpace_eq_two {A R₁ R₂ : Submodule (ZMod 2) M}
    {Z Ta Ta' Tb : M ≃ₗ[ZMod 2] M} (hA : finrank (ZMod 2) A = 4) (hZ : Z = Ta * Ta')
    (hZ3 : ∀ v, Z (Z (Z v)) = v) (hAZ : ∀ v ∈ A, Z v ∈ A) (hAa : ∀ v ∈ A, Ta v ∈ A)
    (hAa' : ∀ v ∈ A, Ta' v ∈ A) (ha2 : Ta * Ta = 1) (ha'2 : Ta' * Ta' = 1)
    (hR₁ : finrank (ZMod 2) R₁ = 2) (hR₂ : finrank (ZMod 2) R₂ = 2)
    (h1 : R₁ ≤ A ⊓ fixSpace Ta) (h2 : R₁ ≤ fixSpace Tb) (h3 : R₂ ≤ A ⊓ fixSpace Ta')
    (h4 : R₂ ≤ fixSpace Tb) (hz1 : ¬ A ≤ fixSpace Z) (hb1 : ¬ A ≤ fixSpace Tb) :
    finrank (ZMod 2) (A ⊓ fixSpace Z : Submodule (ZMod 2) M) = 2 := by
  have hsum := ord3_finrank hZ3 hAZ
  obtain ⟨k, hk⟩ := two_dvd_finrank_of_le_normKer (S := A ⊓ normKer Z)
    (fun v hv => ⟨hAZ v hv.1, normKer_mapsTo hv.2⟩) inf_le_right
  have hk2 : k ≤ 2 := by omega
  interval_cases k
  · exfalso
    apply hz1
    have hfix : A ⊓ fixSpace Z = A := Submodule.eq_of_le_of_finrank_eq inf_le_left (by omega)
    exact fun v hv => (hfix.ge hv).2
  · omega
  · exfalso
    apply hb1
    have hfix0 : A ⊓ fixSpace Z = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
    have hCa := S2.finrank_le_two_mul_inf_fixSpace ha2 hAa
    have hCa' := S2.finrank_le_two_mul_inf_fixSpace ha'2 hAa'
    have hle : (A ⊓ fixSpace Ta) ⊓ (A ⊓ fixSpace Ta') ≤ A ⊓ fixSpace Z := by
      intro v hv
      rw [Submodule.mem_inf, Submodule.mem_inf, Submodule.mem_inf, mem_fixSpace,
        mem_fixSpace] at hv
      rw [Submodule.mem_inf, mem_fixSpace, hZ, LinearEquiv.mul_apply, hv.2.2, hv.1.2]
      exact ⟨hv.1.1, rfl⟩
    have hinf : (A ⊓ fixSpace Ta) ⊓ (A ⊓ fixSpace Ta') = ⊥ :=
      eq_bot_iff.mpr (hle.trans hfix0.le)
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq (A ⊓ fixSpace Ta) (A ⊓ fixSpace Ta')
    rw [hinf, finrank_bot, add_zero] at hsup
    have hsupA : (A ⊓ fixSpace Ta) ⊔ (A ⊓ fixSpace Ta') ≤ A := sup_le inf_le_left inf_le_left
    have hsupdim := Submodule.finrank_mono hsupA
    have hsupeq : (A ⊓ fixSpace Ta) ⊔ (A ⊓ fixSpace Ta') = A :=
      Submodule.eq_of_le_of_finrank_eq hsupA (by omega)
    have hm1 := Submodule.finrank_mono h1
    have hm3 := Submodule.finrank_mono h3
    have e1 : R₁ = A ⊓ fixSpace Ta := Submodule.eq_of_le_of_finrank_eq h1 (by omega)
    have e3 : R₂ = A ⊓ fixSpace Ta' := Submodule.eq_of_le_of_finrank_eq h3 (by omega)
    rw [← hsupeq, ← e1, ← e3]
    exact sup_le h2 h4

end CFSG.LargeExtraspecial.S14
