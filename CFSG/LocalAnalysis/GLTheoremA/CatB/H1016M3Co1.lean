module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1016M3Defs
import CFSG.LocalAnalysis.GLTheoremA.CatB.H1016M3Co1Rank
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Assembly.Defs
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1ThreeDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017.H1016M3

open CFSG.Open CFSG.Sporadic.Co1Schreier CFSG.HardMathSupport.Timmesfeld.SporadicBalance
open scoped Matrix

private theorem exists_conj_le_full {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Q R : Subgroup G} (hQ : Nat.card Q = p ^ (Nat.card G).factorization p) (hR : IsPGroup p R) :
    ∃ g : G, ∀ r ∈ R, g⁻¹ * r * g ∈ Q := by
  obtain ⟨S, hS⟩ := hR.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (Sylow.ofCard Q hQ) S
  refine ⟨g, fun r hr => ?_⟩
  have hmem : r ∈ ((g • Sylow.ofCard Q hQ : Sylow p G) : Subgroup G) := by
    rw [hg]
    exact hS hr
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
    MulAut.smul_def, MulAut.conj_apply, inv_inv, Sylow.coe_ofCard] at hmem
  exact hmem

private theorem conjInv_apply (g x : ↥GA) : (MulAut.conj g⁻¹).toMonoidHom x = g⁻¹ * x * g := by
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]

private theorem eq_zero_of_mulVec_conj (g k : GL24)
    (hk : ∀ v : Fin 24 → ZMod 2, (k : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v → v = 0)
    (v : Fin 24 → ZMod 2)
    (hv : ((g * k * g⁻¹ : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v) : v = 0 := by
  have h1 : (k : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ
      (((g⁻¹ : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v) =
      ((g⁻¹ : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v := by
    have h := congrArg (fun w => ((g⁻¹ : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ w) hv
    simp only [Units.val_mul, Matrix.mulVec_mulVec, ← mul_assoc, Units.inv_mul, one_mul] at h
    rw [Matrix.mulVec_mulVec]
    exact h
  have h2 := hk _ h1
  calc v = ((g : Matrix (Fin 24) (Fin 24) (ZMod 2)) *
        ((g⁻¹ : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2))) *ᵥ v := by
        rw [Units.mul_inv, Matrix.one_mulVec]
    _ = 0 := by rw [← Matrix.mulVec_mulVec, h2, Matrix.mulVec_zero]


private theorem card_Qg_full : Nat.card Co1T.Qg = 3 ^ (Nat.card ↥GA).factorization 3 := by
  rw [Co1T.card_Qg, ← Subgroup.card_top (G := ↥GA), Co1T.factorization_card_GA]

private theorem exists_conj_le_Qg {F : Subgroup ↥GA} (hF : IsElemAbelian 3 F) :
    ∃ g : ↥GA, F.map (MulAut.conj g⁻¹).toMonoidHom ≤ Co1T.Qg := by
  haveI : Finite ↥GA := Co1T.finite_GA
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_conj_le_full card_Qg_full hF.isPGroup
  refine ⟨g, ?_⟩
  rintro _ ⟨r, hr, rfl⟩
  rw [conjInv_apply]
  exact hg r hr

theorem co1ThreeRankFact_holds : Co1ThreeRankFact := by
  intro F hF
  obtain ⟨g, hg⟩ := exists_conj_le_Qg hF
  have hcard : Nat.card (F.map (MulAut.conj g⁻¹).toMonoidHom) = Nat.card F :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  rw [← hcard]
  rcases Co1Sylow.card_le_or_eq_of_le_Qg hg (hF.map _) with h | h
  · exact h.trans (by norm_num)
  · exact le_of_eq (by rw [h, Co1Sylow.card_EG])

theorem co1ThreeSixFixFact_holds : Co1ThreeSixFixFact := by
  intro F hF hF6
  obtain ⟨g, hg⟩ := exists_conj_le_Qg hF
  have hcard : Nat.card (F.map (MulAut.conj g⁻¹).toMonoidHom) = Nat.card F :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hEq : F.map (MulAut.conj g⁻¹).toMonoidHom = ElemThree.E.subgroupOf GA :=
    (Co1Sylow.card_le_or_eq_of_le_Qg hg (hF.map _)).resolve_left (by rw [hcard, hF6]; norm_num)
  have ha : (⟨ElemThree.a 0, Co1Sylow.E_le_GA (a_mem_E 0)⟩ : ↥GA) ∈
      F.map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [hEq]
    exact Subgroup.mem_subgroupOf.2 (a_mem_E 0)
  obtain ⟨e, he, hea⟩ := Subgroup.mem_map.1 ha
  refine ⟨e, he, fun v hv => ?_⟩
  rw [conjInv_apply] at hea
  have he' : e = g * ⟨ElemThree.a 0, Co1Sylow.E_le_GA (a_mem_E 0)⟩ * g⁻¹ := by
    rw [← hea]
    group
  rw [he', Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at hv
  refine eq_zero_of_mulVec_conj _ (ElemThree.a 0) (fun w hw => ?_) v hv
  by_contra h0
  rw [CFSG.Sporadic.Co1Schreier.a_zero] at hw
  exact CFSG.Sporadic.Co1Schreier.zM_mulVec_ne_self h0 hw

end CFSG.LocalAnalysis.GLTheoremA.H1017.H1016M3
