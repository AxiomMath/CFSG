module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.Defs

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig

open Subgroup CFSG.GH74.GLS

variable {X Y : Type*} [Group X] [Group Y]

@[expose] def SigHyp (E K : Subgroup X) : Prop :=
  Nat.card E = 9 ∧ (∀ x ∈ E, x ^ 3 = 1) ∧ E ≤ normalizer (K : Set X) ∧ Group.IsPerfect K ∧
    K ≠ ⊥ ∧
    K ≤ ⨆ (x : X) (_ : x ∈ E) (_ : x ≠ 1), pPrimeCoreOf 3 (K ⊓ centralizer ({x} : Set X))

theorem inspectSig148_iff {X : Type} [Group X] {P : Subgroup X → Prop} :
    InspectSig148 X P ↔ ∀ E K : Subgroup X, SigHyp E K → P K :=
  ⟨fun h E K hEK => h E K hEK.1 hEK.2.1 hEK.2.2.1 hEK.2.2.2.1 hEK.2.2.2.2.1 hEK.2.2.2.2.2,
    fun h E K h1 h2 h3 h4 h5 h6 => h E K ⟨h1, h2, h3, h4, h5, h6⟩⟩

theorem pPrimeCoreOf_map_mulEquiv (φ : X ≃* Y) (p : ℕ) (H : Subgroup X) :
    pPrimeCoreOf p (H.map φ.toMonoidHom) = (pPrimeCoreOf p H).map φ.toMonoidHom := by
  let e : H ≃* H.map φ.toMonoidHom := H.equivMapOfInjective φ.toMonoidHom φ.injective
  have h1 := CFSG.pPrimeCore_map_iso p e
  unfold pPrimeCoreOf
  rw [← h1, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem map_centralizer_singleton (φ : X ≃* Y) (x : X) :
    (centralizer ({x} : Set X)).map φ.toMonoidHom = centralizer ({φ x} : Set Y) := by
  ext y
  simp only [mem_map, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [← map_mul, ← map_mul, hz]
  · intro hy
    refine ⟨φ.symm y, φ.injective ?_, φ.apply_symm_apply y⟩
    rw [map_mul, map_mul, φ.apply_symm_apply, hy]

theorem SigHyp.map {E K : Subgroup X} (h : SigHyp E K) (φ : X ≃* Y) :
    SigHyp (E.map φ.toMonoidHom) (K.map φ.toMonoidHom) := by
  obtain ⟨h9, h3, hN, hp, h1, hgen⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [card_map_of_injective φ.injective, h9]
  · rintro _ ⟨x, hx, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_pow, h3 x hx, map_one]
  · rw [← map_equiv_normalizer_eq]
    exact map_mono hN
  · exact Group.IsPerfect.map _
  · intro h0
    apply h1
    rw [eq_bot_iff]
    intro k hk
    have hk' : φ k ∈ K.map φ.toMonoidHom := ⟨k, hk, rfl⟩
    rw [h0, mem_bot] at hk'
    rw [mem_bot]
    exact φ.injective (hk'.trans (map_one φ).symm)
  · refine (map_mono hgen).trans ?_
    simp only [Subgroup.map_iSup]
    refine iSup_le fun x => iSup_le fun hx => iSup_le fun hx1 => ?_
    have hφx : φ x ≠ 1 := fun h => hx1 (φ.injective (h.trans (map_one φ).symm))
    refine le_iSup_of_le (φ x) (le_iSup_of_le ⟨x, hx, rfl⟩ (le_iSup_of_le hφx ?_))
    rw [← pPrimeCoreOf_map_mulEquiv, Subgroup.map_inf_eq _ _ _ φ.injective,
      map_centralizer_singleton]

theorem inspectSig148_of_mulEquiv {X Y : Type} [Group X] [Group Y] (φ : X ≃* Y)
    {P : Subgroup Y → Prop} (h : InspectSig148 Y P) :
    InspectSig148 X (fun K => P (K.map φ.toMonoidHom)) := by
  rw [inspectSig148_iff] at h ⊢
  exact fun E K hEK => h _ _ (hEK.map φ)

end CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig
