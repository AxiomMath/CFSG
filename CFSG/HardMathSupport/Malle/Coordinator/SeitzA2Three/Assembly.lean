module

public import CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three.Defs
public import CFSG.HardMathSupport.Foote.ModuleExclusions.FieldCube.Generation
public import CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three.Transport

public section

namespace CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.HardMathSupport.Foote.ModuleExclusions

theorem modelHyperGen_of_map_conj {M : Type*} [Group M] {p : ℕ} {B : Subgroup (MulAut M)}
    (α : MulAut M) (h : ModelHyperGen p (B.map (MulAut.conj α).toMonoidHom)) :
    ModelHyperGen p B := by
  unfold ModelHyperGen at h ⊢
  rw [eq_top_iff] at h ⊢
  have hsub : (α⁻¹ : MulAut M).toMonoidHom '' {x : M | ∃ H : Subgroup (MulAut M),
      H ≤ B.map (MulAut.conj α).toMonoidHom ∧
      H.relIndex (B.map (MulAut.conj α).toMonoidHom) = p ∧ ∀ b ∈ H, b x = x} ⊆
      {x : M | ∃ H : Subgroup (MulAut M), H ≤ B ∧ H.relIndex B = p ∧ ∀ b ∈ H, b x = x} := by
    rintro _ ⟨x, ⟨H, hHB, hHi, hHx⟩, rfl⟩
    refine ⟨H.map (MulAut.conj α⁻¹).toMonoidHom, ?_, ?_, ?_⟩
    · rintro _ ⟨b', hb', rfl⟩
      obtain ⟨b, hb, rfl⟩ := hHB hb'
      change (MulAut.conj α⁻¹) ((MulAut.conj α) b) ∈ B
      rw [MulAut.conj_apply, MulAut.conj_apply]
      have he : α⁻¹ * (α * b * α⁻¹) * α⁻¹⁻¹ = b := by group
      rw [he]
      exact hb
    · have hcomp : (MulAut.conj α⁻¹).toMonoidHom.comp (MulAut.conj α).toMonoidHom =
          MonoidHom.id (MulAut M) := by
        refine MonoidHom.ext fun b => ?_
        change (MulAut.conj α⁻¹) ((MulAut.conj α) b) = b
        rw [MulAut.conj_apply, MulAut.conj_apply]
        group
      have hmap : (B.map (MulAut.conj α).toMonoidHom).map (MulAut.conj α⁻¹).toMonoidHom = B := by
        rw [Subgroup.map_map, hcomp, Subgroup.map_id]
      rw [← hmap, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj α⁻¹).injective, hHi]
    · rintro _ ⟨b', hb', rfl⟩
      have := hHx b' hb'
      change (MulAut.conj α⁻¹ b') ((α⁻¹ : MulAut M) x) = (α⁻¹ : MulAut M) x
      rw [MulAut.conj_apply, MulAut.mul_apply, MulAut.mul_apply, inv_inv, MulAut.apply_inv_self,
        this]
  intro y _
  have hy : α y ∈ Subgroup.closure {x : M | ∃ H : Subgroup (MulAut M),
      H ≤ B.map (MulAut.conj α).toMonoidHom ∧
      H.relIndex (B.map (MulAut.conj α).toMonoidHom) = p ∧ ∀ b ∈ H, b x = x} :=
    h (Subgroup.mem_top _)
  have hmap := Subgroup.closure_mono hsub
  rw [← MonoidHom.map_closure] at hmap
  have := hmap ⟨α y, hy, rfl⟩
  simpa using this

theorem modelHyperGen_of_splitData {F : Type} [Field F] [Finite F] {σ : F ≃+* F}
    (hσ : orderOf σ = 3) (h3 : 3 ∣ Nat.card F - 1) {A B : Subgroup (MulAut (projectiveSL 3 F))}
    (hd : SplitData σ A B) (hBc : Nat.card B = 3 ^ 3) : ModelHyperGen 3 B := by
  have h := closure_hyperplane_fixed_eq_top hσ h3 hd (s := 3) (by norm_num) hBc
  unfold ModelHyperGen
  rw [eq_top_iff, ← h]
  exact Subgroup.closure_mono fun x hx => hx.2

@[expose] def A2ThreeNormalForm : Prop :=
  ∀ (F : Type) [Field F] [Finite F], 3 ∣ Nat.card F - 1 →
    ∀ B : Subgroup (MulAut (projectiveSL 3 F)), IsElemAbelian 3 B → Nat.card B = 3 ^ 3 →
      ∃ (α : MulAut (projectiveSL 3 F)) (σ : F ≃+* F), orderOf σ = 3 ∧
        ((∃ A : Subgroup (MulAut (projectiveSL 3 F)),
            SplitData σ A (B.map (MulAut.conj α).toMonoidHom)) ∨
         (∃ lam ω : Fˣ, σ lam = lam ∧ IsPrimitiveRoot (ω : F) 3 ∧
            B.map (MulAut.conj α).toMonoidHom = heisCube σ lam ω))

@[expose] def A2ThreeHeisGen : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (σ : F ≃+* F), orderOf σ = 3 → 3 ∣ Nat.card F - 1 →
    4 < Nat.card (fixF σ) → ∀ lam ω : Fˣ, σ lam = lam → IsPrimitiveRoot (ω : F) 3 →
      ModelHyperGen 3 (heisCube σ lam ω)

@[expose] def A2ThreeSixtyFour : Prop :=
  ∀ (F : Type) [Field F] [Finite F], Nat.card F = 64 →
    ∀ B : Subgroup (MulAut (projectiveSL 3 F)), IsElemAbelian 3 B → Nat.card B = 3 ^ 3 →
      ModelHyperGen 3 B

theorem a2ThreeModelGen_of (hNF : A2ThreeNormalForm) (hH : A2ThreeHeisGen)
    (h64 : A2ThreeSixtyFour) : A2ThreeModelGen := by
  intro F _ _ h3 B hB hBc
  by_cases hF : Nat.card F = 64
  · exact h64 F hF B hB hBc
  obtain ⟨α, σ, hσ, hcase⟩ := hNF F h3 B hB hBc
  refine modelHyperGen_of_map_conj α ?_
  have hc' : Nat.card (B.map (MulAut.conj α).toMonoidHom) = 3 ^ 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj α).injective, hBc]
  rcases hcase with ⟨A, hd⟩ | ⟨lam, ω, hlam, hω, heq⟩
  · exact modelHyperGen_of_splitData hσ h3 hd hc'
  · rw [heq]
    have hq := natCard_eq_pow_three hσ
    have hq₀ : 1 ≤ Nat.card (fixF σ) := Nat.one_le_iff_ne_zero.2 Nat.card_pos.ne'
    have h3₀ : 3 ∣ Nat.card (fixF σ) - 1 := three_dvd_sub_one_of_pow_three hq₀ (hq ▸ h3)
    have h2 : 2 ≤ Nat.card (fixF σ) := by
      have := Finite.one_lt_card (α := fixF σ)
      omega
    have h4 : Nat.card (fixF σ) ≠ 4 := by
      intro h4
      apply hF
      rw [hq, h4]
      norm_num
    exact hH F σ hσ h3 (by omega) lam ω hlam hω

theorem kFactSeitzOuterCubeRankTwoAtPrime_A2_three_of_pieces {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A 2 q).Valid) (h3 : 3 ∣ q.card - 1) (hNF : A2ThreeNormalForm)
    (hH : A2ThreeHeisGen) (h64 : A2ThreeSixtyFour) :
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    CFSG.AGLEmbedding.KFactSeitzOuterCubeRankTwoAtPrime ⟨.A 2 q, hv⟩ 3 :=
  kFactSeitzOuterCubeRankTwoAtPrime_A2_three_of_model hv h3 (a2ThreeModelGen_of hNF hH h64)

end CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three
