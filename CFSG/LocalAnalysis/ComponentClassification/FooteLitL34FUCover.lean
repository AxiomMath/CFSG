module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitL34FUUniq

public section

namespace CFSG.ComponentClassification.TBLit.L34FU

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.ComponentClassification.Sol76
  CFSG.ComponentClassification.UnbalancedLayer

variable {X : Type} [Group X]

theorem conjugate_eq_of_mem_normalizer {K : Subgroup X} {x : X}
    (hx : x ∈ normalizer (K : Set X)) : conjugate K x = K := by
  ext y
  constructor
  · rintro ⟨k, hk, rfl⟩
    have h := (mem_normalizer_iff.mp (inv_mem hx) k).mp hk
    simpa using h
  · intro hy
    refine ⟨x * y * x⁻¹, (mem_normalizer_iff.mp hx y).mp hy, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group

theorem centralizer_zpowers (c : X) :
    centralizer ((zpowers c : Subgroup X) : Set X) = centralizer ({c} : Set X) := by
  rw [zpowers_eq_closure, centralizer_closure]

variable [Finite X]

theorem isQuasisimple_coreQuot {K Y : Subgroup X} (hK : IsTwoComponentIn K Y) :
    IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 K Y hK.1).mp hK.2).2.2

theorem cover_twoLayerIn {K Y : Subgroup X} (hK : IsTwoComponentIn K Y) {c : X}
    (hc : IsPGroup 2 (zpowers c)) (hcK : c ∈ coreActionKernel K) :
    IsTwoComponentIn (twoLayerIn (K ⊓ centralizer ({c} : Set X))) (K ⊓ centralizer ({c} : Set X)) ∧
      twoLayerIn (K ⊓ centralizer ({c} : Set X)) ⊔ oddCoreIn K = K ∧
      Nonempty (↥(twoLayerIn (K ⊓ centralizer ({c} : Set X))) ⧸
          pPrimeCore 2 ↥(twoLayerIn (K ⊓ centralizer ({c} : Set X))) ≃* ↥K ⧸ pPrimeCore 2 ↥K) ∧
      twoLayerIn (K ⊓ centralizer ({c} : Set X)) =
        oddResidualIn (K ⊓ centralizer ({c} : Set X)) := by
  have hS : (K ⊓ centralizer ((zpowers c : Subgroup X) : Set X)) ⊔ oddCoreIn K = K :=
    inf_centralizer_sup_oddCoreIn_eq hc (zpowers_le.mpr hcK)
  rw [centralizer_zpowers] at hS
  obtain ⟨h1, h2, h3, h4⟩ := cover_facts (isQuasisimple_coreQuot hK) inf_le_left hS
  rw [← h2] at h1 h3 h4
  exact ⟨h1, h3, h4, h2⟩

theorem mem_twoLayerIn_of_pow {K Y : Subgroup X} (hK : IsTwoComponentIn K Y) {c : X}
    (hc : IsPGroup 2 (zpowers c)) (hcK : c ∈ coreActionKernel K) {g : X} (hgK : g ∈ K)
    (hgc : g * c = c * g) {k : ℕ} (hg : orderOf g = 2 ^ k) :
    g ∈ twoLayerIn (K ⊓ centralizer ({c} : Set X)) := by
  rw [(cover_twoLayerIn hK hc hcK).2.2.2]
  exact subset_closure ⟨mem_inf.mpr ⟨hgK, mem_centralizer_singleton_iff.mpr hgc⟩, k, hg⟩

theorem sup_oddCoreIn_eq_of_le {K Y : Subgroup X} (hK : IsTwoComponentIn K Y) {c : X}
    (hc : IsPGroup 2 (zpowers c)) (hcK : c ∈ coreActionKernel K) {M CM : Subgroup X}
    (hM : IsTwoComponentIn M CM) (hle : twoLayerIn (K ⊓ centralizer ({c} : Set X)) ≤ M)
    (hinv : ∃ t ∈ twoLayerIn (K ⊓ centralizer ({c} : Set X)), orderOf t = 2)
    (eMK : Nonempty (↥M ⧸ Open.fusionZStar ↥M ≃* ↥K ⧸ Open.fusionZStar ↥K)) :
    twoLayerIn (K ⊓ centralizer ({c} : Set X)) ⊔ oddCoreIn M = M := by
  obtain ⟨h1, -, ⟨e₀⟩, -⟩ := cover_twoLayerIn hK hc hcK
  obtain ⟨e₁⟩ := FooteLit.nonempty_fusionZStar_equiv_of_quotient_equiv e₀
  obtain ⟨e₂⟩ := eMK
  exact sup_oddCoreIn_eq_of_fusionZStar h1 hM hle hinv (e₂.trans e₁.symm)

theorem mem_normalizer_twoLayerIn {K : Subgroup X} {c x : X}
    (hxK : x ∈ normalizer (K : Set X)) (hxc : x * c = c * x) :
    x ∈ normalizer (twoLayerIn (K ⊓ centralizer ({c} : Set X)) : Set X) := by
  apply L34FU.mem_normalizer_of_conjugate_eq
  have hC : conjugate (centralizer ({c} : Set X)) x = centralizer ({c} : Set X) := by
    rw [conjugate_centralizer]
    congr 2
    rw [mul_assoc, ← hxc, inv_mul_cancel_left]
  have hY : conjugate (K ⊓ centralizer ({c} : Set X)) x = K ⊓ centralizer ({c} : Set X) := by
    rw [conjugate, Subgroup.map_inf _ _ _ (MulAut.conj x⁻¹).injective]
    rw [show K.map (MulAut.conj x⁻¹).toMonoidHom = conjugate K x from rfl,
      show (centralizer ({c} : Set X)).map (MulAut.conj x⁻¹).toMonoidHom =
        conjugate (centralizer ({c} : Set X)) x from rfl, conjugate_eq_of_mem_normalizer hxK, hC]
  rw [conjugate, map_twoLayerIn (MulAut.conj x⁻¹)]
  rw [show (K ⊓ centralizer ({c} : Set X)).map (MulAut.conj x⁻¹).toMonoidHom =
    conjugate (K ⊓ centralizer ({c} : Set X)) x from rfl, hY]

end CFSG.ComponentClassification.TBLit.L34FU
