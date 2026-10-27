module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Balance
public import CFSG.HardMathSupport.Solomon.LocalBalance.Defs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.HardMathSupport.Solomon.LocalBalance (innerAut)

@[expose] def SylowCentreInn (M : Type*) [Group M] : Prop :=
  ∀ S : Subgroup (MulAut M), IsPGroup 3 S →
    (∀ P : Subgroup (MulAut M), P ≤ innerAut M → IsPGroup 3 P → S ⊓ innerAut M ≤ P →
      P = S ⊓ innerAut M) →
    ∀ σ ∈ S, (∀ s ∈ S, σ * s = s * σ) → σ ∈ innerAut M

theorem mulAut_mul_conj_mul_inv {M : Type*} [Group M] (α : MulAut M) (y : M) :
    α * MulAut.conj y * α⁻¹ = MulAut.conj (α y) := by
  ext m
  simp [MulAut.mul_apply, map_mul, map_inv]

theorem pow_eq_one_of_isPGroup {A : Type*} [Group A] {S : Subgroup A} (hS : IsPGroup 3 S)
    {σ : A} (hσ : σ ∈ S) : ∃ k : ℕ, σ ^ (3 ^ k) = 1 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hS) ⟨σ, hσ⟩
  refine ⟨k, ?_⟩
  rw [← hk, Subgroup.orderOf_mk]
  exact pow_orderOf_eq_one σ

theorem sylowCentreInn_of_data {M : Type*} [Group M] [Finite M] (D : Subgroup (MulAut M))
    (hND : innerAut M ≤ D) (E : Subgroup M) (hE : IsPGroup 3 E)
    (h1 : ∀ (σ : MulAut M) (k : ℕ), σ ^ (3 ^ k) = 1 → σ ∈ D)
    (h2 : ∀ d ∈ D, (∀ q ∈ E, d q * q⁻¹ ∈ Subgroup.center M) → d ∈ innerAut M) :
    SylowCentreInn M := by
  intro S hS hmax σ hσS hσc
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N : Subgroup (MulAut M) := innerAut M with hN
  let f : M →* ↥N := (MulAut.conj : M →* MulAut M).rangeRestrict
  have hf : Function.Surjective f := (MulAut.conj : M →* MulAut M).rangeRestrict_surjective
  obtain ⟨Qh, hEQ⟩ := hE.exists_le_sylow
  let Qn : Sylow 3 ↥N := Qh.mapSurjective hf
  have hT'p : IsPGroup 3 ((S ⊓ N).subgroupOf N) :=
    (hS.to_le (inf_le_left : S ⊓ N ≤ S)).comap_subtype
  obtain ⟨Tsyl, hTsyl⟩ := hT'p.exists_le_sylow
  have hTeq : (Tsyl : Subgroup ↥N).map N.subtype = S ⊓ N := by
    refine hmax _ (Subgroup.map_subtype_le _) (Tsyl.isPGroup'.map _) ?_
    intro x hx
    exact ⟨⟨x, hx.2⟩, hTsyl ((Subgroup.mem_subgroupOf).2 hx), rfl⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥N Qn Tsyl
  have hconj : ∀ x ∈ (Qn : Subgroup ↥N), g * x * g⁻¹ ∈ (Tsyl : Subgroup ↥N) := by
    intro x hx
    subst hg
    have key : (MulAut.conj g • x) ∈ ((g • Qn : Sylow 3 ↥N) : Set ↥N) := by
      rw [Sylow.coe_smul]
      exact Set.smul_mem_smul_set hx
    have k2 : g * x * g⁻¹ ∈ ((g • Qn : Sylow 3 ↥N) : Set ↥N) := by simpa using key
    exact k2
  have hσD : σ ∈ D := by
    obtain ⟨k, hk⟩ := pow_eq_one_of_isPGroup hS hσS
    exact h1 σ k hk
  set n : MulAut M := (g : MulAut M) with hn
  have hnD : n ∈ D := hND g.2
  set τ : MulAut M := n⁻¹ * σ * n with hτ
  have hτD : τ ∈ D := D.mul_mem (D.mul_mem (D.inv_mem hnD) hσD) hnD
  have hcent : ∀ q ∈ E, τ q * q⁻¹ ∈ Subgroup.center M := by
    intro q hq
    have hqn : f q ∈ (Qn : Subgroup ↥N) := Subgroup.mem_map_of_mem f (hEQ hq)
    have hy := hconj _ hqn
    have hyT : ((g * f q * g⁻¹ : ↥N) : MulAut M) ∈ S ⊓ N := by
      rw [← hTeq]
      exact ⟨_, hy, rfl⟩
    have hcomm := hσc _ hyT.1
    have hyeq : ((g * f q * g⁻¹ : ↥N) : MulAut M) = n * MulAut.conj q * n⁻¹ := rfl
    rw [hyeq] at hcomm
    have h3 : τ * MulAut.conj q = MulAut.conj q * τ := by
      calc τ * MulAut.conj q = n⁻¹ * (σ * (n * MulAut.conj q * n⁻¹)) * n := by rw [hτ]; group
        _ = n⁻¹ * ((n * MulAut.conj q * n⁻¹) * σ) * n := by rw [hcomm]
        _ = MulAut.conj q * τ := by rw [hτ]; group
    have h4 : MulAut.conj (τ q) = MulAut.conj q := by
      rw [← mulAut_mul_conj_mul_inv, h3]
      group
    have h5 : MulAut.conj (τ q * q⁻¹) = 1 := by
      rw [map_mul, map_inv, h4, mul_inv_cancel]
    rw [Subgroup.mem_center_iff]
    intro x
    have h6 := congrArg (fun φ : MulAut M => φ x) h5
    simp only [MulAut.conj_apply, MulAut.one_apply] at h6
    exact (mul_inv_eq_iff_eq_mul.1 h6).symm
  have hτN : τ ∈ innerAut M := h2 τ hτD hcent
  have hσ : σ = n * τ * n⁻¹ := by rw [hτ]; group
  rw [hσ]
  exact N.mul_mem (N.mul_mem g.2 hτN) (N.inv_mem g.2)

theorem map_innerAut_congr {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (innerAut A).map (MulAut.congr e).toMonoidHom = innerAut B := by
  ext τ
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    refine ⟨e y, ?_⟩
    ext m
    simp [MulAut.congr_apply, map_mul, map_inv]
  · rintro ⟨m, rfl⟩
    refine ⟨MulAut.conj (e.symm m), ⟨e.symm m, rfl⟩, ?_⟩
    ext x
    simp [MulAut.congr_apply, map_mul, map_inv]

theorem sylowCentreInn_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hB : SylowCentreInn B) : SylowCentreInn A := by
  intro S hS hmax σ hσS hσc
  set φ : MulAut A ≃* MulAut B := MulAut.congr e with hφ
  have hI : (innerAut A).map φ.toMonoidHom = innerAut B := map_innerAut_congr e
  have hinj : Function.Injective φ.toMonoidHom := φ.injective
  have hmapinf : (S ⊓ innerAut A).map φ.toMonoidHom = S.map φ.toMonoidHom ⊓ innerAut B := by
    rw [Subgroup.map_inf _ _ _ hinj, hI]
  have key := hB (S.map φ.toMonoidHom) (hS.map _) ?_ (φ σ) ⟨σ, hσS, rfl⟩ ?_
  · rw [← hI] at key
    obtain ⟨y, hy, hyσ⟩ := key
    have : y = σ := hinj hyσ
    exact this ▸ hy
  · intro P' hP'I hP'p hle
    set P : Subgroup (MulAut A) := P'.comap φ.toMonoidHom with hP
    have hPI : P ≤ innerAut A := by
      intro x hx
      have : φ x ∈ (innerAut A).map φ.toMonoidHom := by rw [hI]; exact hP'I hx
      obtain ⟨y, hy, hyx⟩ := this
      exact (hinj hyx) ▸ hy
    have hPp : IsPGroup 3 P := hP'p.comap_of_injective _ hinj
    have hSP : S ⊓ innerAut A ≤ P := by
      intro x hx
      apply hle
      rw [← hmapinf]
      exact ⟨x, hx, rfl⟩
    have := hmax P hPI hPp hSP
    have h2 : P.map φ.toMonoidHom = P' := Subgroup.map_comap_eq_self_of_surjective φ.surjective _
    rw [← h2, this, hmapinf]
  · rintro _ ⟨s, hs, rfl⟩
    show φ σ * φ s = φ s * φ σ
    rw [← map_mul, ← map_mul, hσc s hs]

end CFSG.HardMathSupport.Solomon.Coordinator
