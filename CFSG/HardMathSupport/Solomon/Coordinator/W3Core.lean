module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19_10Red
public import CFSG.HardMathSupport.Timmesfeld.Balance.Reduction

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Timmesfeld.Balance

section Delta

variable {M : Type*} [Group M]

theorem w3_mem_core_of_mem_localDeltaIn {p : ℕ} {H D : Subgroup M} {d : M} (hd : d ∈ D)
    (hd1 : d ≠ 1) {x : M} (hx : x ∈ localDeltaIn p H D) :
    x ∈ GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({d} : Set M)) := by
  simp only [localDeltaIn, Subgroup.mem_iInf] at hx
  exact hx d hd hd1

theorem w3_commute_of_mem_localDeltaIn {p : ℕ} {H D : Subgroup M} {d : M} (hd : d ∈ D)
    (hd1 : d ≠ 1) {x : M} (hx : x ∈ localDeltaIn p H D) : x * d = d * x :=
  Subgroup.mem_centralizer_singleton_iff.1
    (GLAPPrimeCoreOf_le _ (w3_mem_core_of_mem_localDeltaIn hd hd1 hx)).2

theorem w3_coprime_orderOf_of_mem_localDeltaIn [Finite M] {p : ℕ} (hp : p.Prime)
    {H D : Subgroup M} {d : M} (hd : d ∈ D) (hd1 : d ≠ 1) {x : M}
    (hx : x ∈ localDeltaIn p H D) : Nat.Coprime p (orderOf x) :=
  (coprime_card_GLAPPrimeCoreOf hp _).coprime_dvd_right
    (Subgroup.orderOf_dvd_natCard _ (w3_mem_core_of_mem_localDeltaIn hd hd1 hx))

theorem w3_conj_mem_localDeltaIn [Finite M] {p : ℕ} (hp : p.Prime) {H D : Subgroup M} {y : M}
    (hyH : y ∈ Subgroup.normalizer (H : Set M)) (hyD : ∀ d ∈ D, y * d = d * y) {x : M}
    (hx : x ∈ localDeltaIn p H D) : y * x * y⁻¹ ∈ localDeltaIn p H D := by
  simp only [localDeltaIn, Subgroup.mem_iInf] at hx ⊢
  intro d hd hd1
  have hxd := hx d hd hd1
  set C := H ⊓ Subgroup.centralizer ({d} : Set M) with hC
  have hyd : Commute y d := hyD d hd
  have hyH' : y⁻¹ ∈ Subgroup.normalizer (H : Set M) := Subgroup.inv_mem _ hyH
  have hyC : ∀ c ∈ C, y * c * y⁻¹ ∈ C := by
    intro c hc
    refine ⟨(Subgroup.mem_normalizer_iff.1 hyH c).1 hc.1, ?_⟩
    have hcd : Commute c d := Subgroup.mem_centralizer_singleton_iff.1 hc.2
    exact Subgroup.mem_centralizer_singleton_iff.2 ((hyd.mul_left hcd).mul_left hyd.inv_left)
  have hyC' : ∀ c ∈ C, y⁻¹ * c * y ∈ C := by
    intro c hc
    have h1 : y⁻¹ * c * y⁻¹⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.1 hyH' c).1 hc.1
    rw [inv_inv] at h1
    refine ⟨h1, ?_⟩
    have hcd : Commute c d := Subgroup.mem_centralizer_singleton_iff.1 hc.2
    exact Subgroup.mem_centralizer_singleton_iff.2 ((hyd.inv_left.mul_left hcd).mul_left hyd)
  set S := (GLAPPrimeCoreOf p C).map (MulAut.conj y).toMonoidHom with hS
  have hSC : S ≤ C := by
    rintro _ ⟨z, hz, rfl⟩
    exact hyC z (GLAPPrimeCoreOf_le C hz)
  have hSn : ∀ g ∈ C, ∀ s ∈ S, g * s * g⁻¹ ∈ S := by
    rintro g hg _ ⟨z, hz, rfl⟩
    refine ⟨(y⁻¹ * g * y) * z * (y⁻¹ * g * y)⁻¹,
      GLAPPrimeCoreOf_conj_mem _ (hyC' g hg) z hz, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hcop : Nat.Coprime p (Nat.card S) := by
    rw [hS, Subgroup.card_map_of_injective (MulAut.conj y).injective]
    exact coprime_card_GLAPPrimeCoreOf hp C
  exact le_GLAPPrimeCoreOf_of_normal hSC hSn hcop ⟨x, hxd, rfl⟩

end Delta

section Transport

variable {K K' : Type*} [Group K] [Group K']

theorem isWeaklyLocallyBalancedAbs_of_mulEquiv {p k : ℕ} (e : K ≃* K')
    (h : IsWeaklyLocallyBalancedAbs p k K') : IsWeaklyLocallyBalancedAbs p k K := by
  intro A hA D hD H hH hAH
  set φ : MulAut K ≃* MulAut K' := MulAut.congr e with hφ
  have hA' : IsElemAbelian p (A.map φ.toMonoidHom) := i1910_isElemAbelian_map _ hA
  have hD' : IsEkIn p k (A.map φ.toMonoidHom) (D.map φ.toMonoidHom) :=
    isEkIn_map_mulEquiv p k φ hD
  have hH' : innerAut K' ≤ H.map φ.toMonoidHom := by
    rintro _ ⟨k', rfl⟩
    refine ⟨MulAut.conj (e.symm k'), hH ⟨e.symm k', rfl⟩, ?_⟩
    ext z
    simp [hφ, MulAut.congr_apply, MulAut.conj_apply]
  have hAH' : A.map φ.toMonoidHom ≤
      Subgroup.normalizer ((H.map φ.toMonoidHom : Subgroup (MulAut K')) : Set (MulAut K')) :=
    (Subgroup.map_mono hAH).trans (Subgroup.le_normalizer_map _)
  have key := h _ hA' _ hD' _ hH' hAH'
  rw [localDeltaIn_map_mulEquiv, ← Subgroup.map_commutator] at key
  exact (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).1 key

end Transport

end CFSG.HardMathSupport.Solomon.Coordinator
