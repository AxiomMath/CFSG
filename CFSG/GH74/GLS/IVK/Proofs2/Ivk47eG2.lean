module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47eOmega
public import CFSG.LieType.Chevalley.SylowOpposition
public import CFSG.LieType.Chevalley.AdjointCenter

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk47

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem sylow_G2 {K : Type} [Group K] [Finite K] {p n : ℕ} (hp : p.Prime)
    (hmodel : UntwistedChevalleyModel K .G2 (p ^ n)) (P : Sylow p K) :
    OmegaGen p (P : Subgroup K) ∧ Nat.card (P : Subgroup K) = (p ^ n) ^ 6 := by
  obtain ⟨F, hFfield, hFfin, hFcard, ⟨e⟩⟩ := hmodel
  have : Fact p.Prime := ⟨hp⟩
  have hchar : CharP F p := charP_of_natCard_eq_pow hp hFcard
  have hZ : Subgroup.center ↥(adjointGroup .G2 F) = ⊥ := center_adjointGroup_eq_bot
  let θ : K ≃* ↥(adjointGroup .G2 F) :=
    e.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)
  have hUC : posUnipotent .G2 F ≤ adjointGroup .G2 F := posUnipotent_le_adjointGroup' .G2 F
  have hcardU : Nat.card (posUnipotent .G2 F) = Nat.card F ^ 6 := by
    rw [card_posUnipotent, ncard_posRoots_G2]
  obtain ⟨hUp, hUi⟩ := isPGroup_and_not_dvd_index p hUC (by rw [hcardU, ncard_posRoots_G2])
  let PU : Sylow p ↥(adjointGroup .G2 F) := hUp.toSylow hUi
  have hPU : (PU : Subgroup ↥(adjointGroup .G2 F)) =
      (posUnipotent .G2 F).subgroupOf (adjointGroup .G2 F) := IsPGroup.toSylow_coe hUp hUi
  let Q : Sylow p K := Sylow.mapSurjective (f := θ.symm.toMonoidHom) θ.symm.surjective PU
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K Q P
  have hP : (P : Subgroup K) =
      ((posUnipotent .G2 F).subgroupOf (adjointGroup .G2 F)).map
        (θ.symm.trans (MulAut.conj g)).toMonoidHom := by
    have h1 : (P : Subgroup K) =
        ((PU : Subgroup ↥(adjointGroup .G2 F)).map θ.symm.toMonoidHom).map
          (MulAut.conj g).toMonoidHom := by
      rw [← hg]
      rfl
    rw [h1, hPU, Subgroup.map_map]
    rfl
  have hinj : Function.Injective (θ.symm.trans (MulAut.conj g)).toMonoidHom :=
    (θ.symm.trans (MulAut.conj g)).injective
  refine ⟨?_, ?_⟩
  · rw [hP, omegaGen_map_iff _ hinj]
    rw [← omegaGen_map_iff (adjointGroup .G2 F).subtype (adjointGroup .G2 F).subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hUC]
    exact omegaGen_posUnipotent
  · rw [hP, Subgroup.card_map_of_injective hinj, card_subgroupOf_of_le hUC, hcardU, hFcard]

end CFSG.GH74.GLS.IVK.Proofs2.Ivk47
