module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Defs

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

section Equiv

variable {X : Type} [Group X]

theorem pPrimeCoreOf_map_mulEquiv (φ : X ≃* X) (K : Subgroup X) :
    pPrimeCoreOf 2 (K.map φ.toMonoidHom) = (pPrimeCoreOf 2 K).map φ.toMonoidHom := by
  let ψ : ↥K ≃* ↥(K.map φ.toMonoidHom) :=
    Subgroup.equivMapOfInjective K φ.toMonoidHom φ.injective
  have h1 : (pPrimeCore 2 ↥K).map ψ.toMonoidHom = pPrimeCore 2 ↥(K.map φ.toMonoidHom) :=
    pPrimeCore_map_iso 2 ψ
  have h2 : (K.map φ.toMonoidHom).subtype.comp ψ.toMonoidHom = φ.toMonoidHom.comp K.subtype := by
    ext g; rfl
  unfold pPrimeCoreOf
  rw [← h1, Subgroup.map_map, h2, ← Subgroup.map_map]

theorem oPrimeResidualOf_two_map_mulEquiv (φ : X ≃* X) (K : Subgroup X) :
    oPrimeResidualOf 2 (K.map φ.toMonoidHom) = (oPrimeResidualOf 2 K).map φ.toMonoidHom := by
  rw [oPrimeResidualOf_two_eq_oTwoPrimeOf, oPrimeResidualOf_two_eq_oTwoPrimeOf]
  unfold oTwoPrimeOf
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, k, hk⟩
    refine ⟨x, ⟨hx, k, ?_⟩, rfl⟩
    apply φ.injective
    simpa [map_pow] using hk
  · rintro ⟨x, ⟨hx, k, hk⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, k, by simp [← map_pow, hk]⟩

theorem centralizer_singleton_map_mulEquiv (φ : X ≃* X) (t : X) :
    centralizer ({φ t} : Set X) = (centralizer ({t} : Set X)).map φ.toMonoidHom := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · intro hy
    refine ⟨φ.symm y, ?_, by simp⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    apply φ.injective
    simp [hy]
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    simpa using congrArg φ hx

theorem isDoubleCoverOfAlt_congr' {K K' : Type} [Group K] [Group K'] {n : ℕ} (e : K ≃* K')
    (h : IsDoubleCoverOfAlt K n) : IsDoubleCoverOfAlt K' n := by
  obtain ⟨hq, hc, ⟨e'⟩⟩ := h
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq, ?_, ?_⟩
  · rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact hc
  · exact ⟨(QuotientGroup.congr (center K) (center K') e (Subgroup.map_center_eq e)).symm.trans
      e'⟩

theorem IsAhatIntr.map_mulEquiv (φ : X ≃* X) {t : X} {L : Subgroup X} (h : IsAhatIntr X t L) :
    IsAhatIntr X (φ t) (L.map φ.toMonoidHom) := by
  obtain ⟨hLC, htL, hpc, n, hn, hcov⟩ := h
  have hC := centralizer_singleton_map_mulEquiv φ t
  refine ⟨?_, ⟨t, htL, rfl⟩, ?_, n, hn, ?_⟩
  · rw [hC]
    exact Subgroup.map_mono hLC
  · rw [hC]
    exact (isPComponent_subgroupOf_map_iff 2 φ.toMonoidHom φ.injective hLC).2 hpc
  · let ψ : ↥L ≃* ↥(L.map φ.toMonoidHom) := Subgroup.equivMapOfInjective L _ φ.injective
    obtain ⟨f⟩ := nonempty_quotPPrimeCore_equiv ψ
    exact isDoubleCoverOfAlt_congr' f hcov

theorem IsIntrinsicIn.map_mulEquiv (φ : X ≃* X) {H L : Subgroup X} {u : X}
    (h : IsIntrinsicIn X H L u) :
    IsIntrinsicIn X (H.map φ.toMonoidHom) (L.map φ.toMonoidHom) (φ u) := by
  obtain ⟨hu, huL, ⟨hLH, hpc⟩, heq, Lu, hLu, hLueq⟩ := h
  have hLC : L.map φ.toMonoidHom ⊓ centralizer ({φ u} : Set X) =
      (L ⊓ centralizer ({u} : Set X)).map φ.toMonoidHom := by
    rw [centralizer_singleton_map_mulEquiv, ← Subgroup.map_inf_eq _ _ _ φ.injective]
  refine ⟨by rw [MulEquiv.orderOf_eq]; exact hu, ⟨u, huL, rfl⟩,
    ⟨Subgroup.map_mono hLH,
      (isPComponent_subgroupOf_map_iff 2 φ.toMonoidHom φ.injective hLH).2 hpc⟩,
    ?_, Lu.map φ.toMonoidHom, hLu.map_mulEquiv φ, ?_⟩
  · rw [hLC, pPrimeCoreOf_map_mulEquiv, oPrimeResidualOf_two_map_mulEquiv, ← Subgroup.map_sup,
      ← heq]
  · rw [hLC, pPrimeCoreOf_map_mulEquiv, oPrimeResidualOf_two_map_mulEquiv, ← Subgroup.map_sup,
      ← hLueq]

theorem K0_le (n : ℕ) (H : Subgroup X) : K0 X n H ≤ H :=
  sSup_le fun _ hL => by
    obtain ⟨u, hu⟩ := hL.1
    exact hu.2.2.1.1

theorem K0_map_le (n : ℕ) (φ : X ≃* X) (H : Subgroup X) :
    (K0 X n H).map φ.toMonoidHom ≤ K0 X n (H.map φ.toMonoidHom) := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun L hL => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  refine le_sSup ⟨?_, ?_⟩
  · obtain ⟨u, hu⟩ := hL.1
    exact ⟨φ u, hu.map_mulEquiv φ⟩
  · let ψ : ↥L ≃* ↥(L.map φ.toMonoidHom) := Subgroup.equivMapOfInjective L _ φ.injective
    obtain ⟨f⟩ := nonempty_quotPPrimeCore_equiv ψ
    exact isDoubleCoverOfAlt_congr' f hL.2

theorem K0_map (n : ℕ) (φ : X ≃* X) (H : Subgroup X) :
    (K0 X n H).map φ.toMonoidHom = K0 X n (H.map φ.toMonoidHom) := by
  refine le_antisymm (K0_map_le n φ H) ?_
  have h := Subgroup.map_mono (f := φ.toMonoidHom) (K0_map_le n φ.symm (H.map φ.toMonoidHom))
  have h1 : ∀ K : Subgroup X, (K.map φ.symm.toMonoidHom).map φ.toMonoidHom = K := fun K => by
    rw [Subgroup.map_map]
    have : φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id X := by ext x; simp
    rw [this, Subgroup.map_id]
  have h2 : (H.map φ.toMonoidHom).map φ.symm.toMonoidHom = H := by
    rw [Subgroup.map_map]
    have : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id X := by ext x; simp
    rw [this, Subgroup.map_id]
  rw [h1, h2] at h
  exact h

theorem map_conj_K0 (n : ℕ) {H : Subgroup X} {c : X} (hc : c ∈ normalizer (H : Set X)) :
    (K0 X n H).map (MulAut.conj c).toMonoidHom = K0 X n H := by
  rw [K0_map, map_conj_eq_of_mem_normalizer hc]

theorem conj_mem_K0 (n : ℕ) {H : Subgroup X} {c : X} (hc : c ∈ normalizer (H : Set X)) {k : X}
    (hk : k ∈ K0 X n H) : c * k * c⁻¹ ∈ K0 X n H := by
  rw [← map_conj_K0 n hc]
  exact ⟨k, hk, by simp [MulAut.conj_apply]⟩

end Equiv

end CFSG.OddStandard.Solomon75
