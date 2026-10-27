module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieOffCharDetCover
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzNonNormal.Generic

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower

open CFSG.AGLEmbedding

@[expose] def OuterComm (K : Type*) [Group K] : Prop :=
  ∀ γ α : MulAut K, γ * α * γ⁻¹ * α⁻¹ ∈ (MulAut.conj : K →* MulAut K).range

theorem OuterComm.of_mulEquiv {K L : Type} [Group K] [Group L] (e : K ≃* L)
    (h : OuterComm L) : OuterComm K := by
  intro γ α
  obtain ⟨g, hg⟩ := h (MulAut.congr e γ) (MulAut.congr e α)
  refine ⟨e.symm g, (CFSG.RankThree.PartOne.CTP.eq_conj_of_congr_eq_conj e ?_).symm⟩
  simpa only [map_mul, map_inv] using hg.symm

theorem outerComm_of_hom {K : Type*} [Group K] {A : Type*} [Group A]
    (hA : ∀ a b : A, a * b = b * a) (Θ : MulAut K →* A)
    (hker : Θ.ker ≤ (MulAut.conj : K →* MulAut K).range) : OuterComm K := by
  intro γ α
  refine hker ?_
  rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hA (Θ γ) (Θ α)]
  group

theorem outerComm_of_normalForm {K : Type*} [Group K] (Θ : Set (MulAut K))
    (hΘ : ∀ θ ∈ Θ, ∀ θ' ∈ Θ, θ * θ' = θ' * θ)
    (hnf : ∀ α : MulAut K, ∃ g : K, ∃ θ ∈ Θ, α = MulAut.conj g * θ) : OuterComm K := by
  intro γ α
  obtain ⟨g, θ, hθ, rfl⟩ := hnf γ
  obtain ⟨h, θ', hθ', rfl⟩ := hnf α
  have hc : ∀ (φ : MulAut K) (x : K), φ * MulAut.conj x * φ⁻¹ = MulAut.conj (φ x) := by
    intro φ x
    ext y
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply, map_mul, map_inv,
      MulEquiv.apply_symm_apply]
  have h1 : θ * MulAut.conj h * θ⁻¹ = MulAut.conj (θ h) := hc θ h
  have h2 : θ' * (MulAut.conj g)⁻¹ * θ'⁻¹ = (MulAut.conj (θ' g))⁻¹ := by
    rw [← map_inv, hc θ' g⁻¹, map_inv, map_inv]
  have h3 : θ * θ' * θ⁻¹ = θ' := by rw [hΘ θ hθ θ' hθ']; group
  refine ⟨g * θ h * (θ' g)⁻¹ * h⁻¹, ?_⟩
  symm
  calc MulAut.conj g * θ * (MulAut.conj h * θ') * (MulAut.conj g * θ)⁻¹ *
        (MulAut.conj h * θ')⁻¹
      = MulAut.conj g * (θ * MulAut.conj h * θ⁻¹) * (θ * θ' * θ⁻¹) * (MulAut.conj g)⁻¹ *
          θ'⁻¹ * (MulAut.conj h)⁻¹ := by group
    _ = MulAut.conj g * MulAut.conj (θ h) * (θ' * (MulAut.conj g)⁻¹ * θ'⁻¹) *
          (MulAut.conj h)⁻¹ := by rw [h1, h3]; group
    _ = MulAut.conj g * MulAut.conj (θ h) * (MulAut.conj (θ' g))⁻¹ * (MulAut.conj h)⁻¹ := by
          rw [h2]
    _ = MulAut.conj (g * θ h * (θ' g)⁻¹ * h⁻¹) := by
          simp only [map_mul, map_inv]

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner inner_normal) in
theorem outerComm_of_outer_comm {K : Type*} [Group K] (h : ∀ a b : Outer K, a * b = b * a) :
    OuterComm K :=
  outerComm_of_hom h (QuotientGroup.mk' (inner K)) (QuotientGroup.ker_mk' (inner K)).le

open CFSG.ComponentClassification.OuterAutomorphisms (Outer) in
theorem outerComm_of_isCyclic_outer {K : Type*} [Group K] (h : IsCyclic (Outer K)) :
    OuterComm K := by
  letI := IsCyclic.commGroup (α := Outer K)
  exact outerComm_of_outer_comm fun a b => mul_comm a b

open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal) in
theorem outTowerAt_of_mem_inner {K : Type*} [Group K] {p : ℕ}
    (h : ∀ α : MulAut K, (∃ k : ℕ, α ^ (p ^ k) = 1) → α ∈ (MulAut.conj : K →* MulAut K).range) :
    OutTowerAt K p := by
  refine ⟨inner K, fun γ α hα => ?_, fun α _ δ hδ => ?_⟩
  · have hαi : α ∈ inner K := h α hα
    exact (inner K).mul_mem ((inner_normal K).conj_mem α hαi γ) ((inner K).inv_mem hαi)
  · exact (inner K).mul_mem ((inner_normal K).conj_mem δ hδ α) ((inner K).inv_mem hδ)

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner) in
theorem outTowerAt_of_isPGroup_outer {K : Type*} [Group K] {r p : ℕ} (hr : r.Prime)
    (hp : p.Prime) (hrp : r ≠ p) (h : IsPGroup r (Outer K)) : OutTowerAt K p := by
  refine outTowerAt_of_mem_inner fun α ⟨k, hk⟩ => ?_
  obtain ⟨n, hn⟩ := h (QuotientGroup.mk α)
  have h1 : (QuotientGroup.mk α : Outer K) ^ (p ^ k) = 1 := by
    rw [← QuotientGroup.mk_pow, hk, QuotientGroup.mk_one]
  have hcop : Nat.Coprime (r ^ n) (p ^ k) :=
    Nat.Coprime.pow n k ((Nat.coprime_primes hr hp).2 hrp)
  have hord : orderOf (QuotientGroup.mk α : Outer K) = 1 :=
    (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hn) hcop).eq_one_of_dvd
      (orderOf_dvd_of_pow_eq_one h1)
  exact (QuotientGroup.eq_one_iff α).1 (orderOf_eq_one_iff.1 hord)

theorem p1OffCharAlmostSimpleNonNormalAt_of_outerComm {d : TauCeti.ValidLieTypeIndex}
    (h : OuterComm (TauCeti.CFSGIndex.lie d).Group) : P1OffCharAlmostSimpleNonNormalAt d :=
  p1OffCharAlmostSimpleNonNormalAt_of_towerOrCover fun _ _ _ _ _ =>
    Or.inl (SeitzNonNormal.outTowerAt_of_commutator_mem_inner h)

end CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower
