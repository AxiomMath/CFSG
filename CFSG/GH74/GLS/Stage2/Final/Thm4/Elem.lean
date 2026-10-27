module

public import CFSG.GH74.GLS.Stage2.Final.Thm4.Bridge
public import CFSG.ClassicalInvolution.LBalance.Proof.Tools

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm4

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg

theorem oResidual_normal_aux (p : ℕ) (X : Type) [Group X] : (oResidual p X).Normal where
  conj_mem n hn g := by
    induction hn using Subgroup.closure_induction with
    | mem x hx =>
      apply Subgroup.subset_closure
      change Nat.Coprime (orderOf (g * x * g⁻¹)) p
      have h : orderOf (g * x * g⁻¹) = orderOf x := by
        have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
        simpa using this
      rw [h]
      exact hx
    | one => simp
    | mul x y _ _ hx hy =>
      have h : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [h]
      exact Subgroup.mul_mem _ hx hy
    | inv x _ hx =>
      have h : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [h]
      exact Subgroup.inv_mem _ hx

theorem pPrimePCore_eq_pCore_of_bot {X : Type} [Group X] (p : ℕ) (h : pPrimeCore p X = ⊥) :
    pPrimePCore p X = pCore p X := by
  have hker : (QuotientGroup.mk' (pPrimeCore p X)).ker = ⊥ := by rw [QuotientGroup.ker_mk', h]
  let e : X ≃* (X ⧸ pPrimeCore p X) := MulEquiv.ofBijective (QuotientGroup.mk' (pPrimeCore p X))
    ⟨(MonoidHom.ker_eq_bot_iff _).mp hker, QuotientGroup.mk'_surjective _⟩
  have h1 := pCore_map_iso p e
  have he : e.toMonoidHom = QuotientGroup.mk' (pPrimeCore p X) := MonoidHom.ext fun _ => rfl
  rw [he] at h1
  unfold pPrimePCore
  rw [← h1]
  exact Subgroup.comap_map_eq_self_of_injective ((MonoidHom.ker_eq_bot_iff _).mp hker) _

section Amb0

variable {G : Type} [Group G]

theorem pPrimeCoreOf_eq_bot_iff (M : Subgroup G) : pPrimeCoreOf 2 M = ⊥ ↔ pPrimeCore 2 ↥M = ⊥ :=
  Subgroup.map_eq_bot_iff_of_injective (pPrimeCore 2 ↥M) M.subtype_injective

end Amb0

section Amb

variable {G : Type} [Group G] [Finite G]

theorem pPrimeCore_O2Of_eq_bot (M : Subgroup G) (hO : pPrimeCore 2 ↥M = ⊥) :
    pPrimeCore 2 ↥(O2Of M) = ⊥ := by
  set Y := oResidual 2 ↥M with hY
  have hYn : Y.Normal := oResidual_normal_aux 2 ↥M
  have hnormal : ((pPrimeCore 2 ↥Y).map Y.subtype).Normal := inferInstance
  have hle : (pPrimeCore 2 ↥Y).map Y.subtype ≤ pPrimeCore 2 ↥M := by
    refine le_sSup ⟨hnormal, ?_⟩
    rw [Subgroup.card_map_of_injective Y.subtype_injective]
    exact pPrimeCore_coprime_card
  rw [hO, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ Y.subtype_injective] at hle
  have e := Subgroup.equivMapOfInjective Y M.subtype M.subtype_injective
  have := pPrimeCore_map_iso 2 e
  rw [hle, Subgroup.map_bot] at this
  exact this.symm

theorem thm4a_of_oddCore_bot {M : Subgroup G} (hO : pPrimeCore 2 ↥M = ⊥) : Thm4a M := by
  show pLayerOf 2 M = Em M
  rw [pLayerOf_eq_map, CFSG.ClassicalInvolution.LBalanceProof.pLayer_eq_layer_of_pPrimeCore_eq_bot hO,
    Em_eq]

theorem thm4c_of_oddCore_bot {z : G} {M : Subgroup G} (hO : pPrimeCore 2 ↥M = ⊥) : Thm4c z M := by
  intro _
  have h1 : pPrimeCoreOf 2 M = ⊥ := (pPrimeCoreOf_eq_bot_iff M).mpr hO
  have h2 : O22Of (O2Of M) = O2coreOf (O2Of M) := by
    unfold O22Of O2coreOf
    rw [pPrimePCore_eq_pCore_of_bot 2 (pPrimeCore_O2Of_eq_bot M hO)]
  rw [h1, h2]
  refine ⟨bot_sup_eq _, fun a ha b _ => ?_, bot_inf_eq _⟩
  rw [Subgroup.mem_bot.mp ha]
  simp

end Amb

end CFSG.GH74.GLS.Stage2.Final.Thm4
