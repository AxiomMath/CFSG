module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47fCenter
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47e
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3Heis

public noncomputable section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk47

open Subgroup

@[expose] def centerEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    ↥(Subgroup.center A) ≃* ↥(Subgroup.center B) :=
  (Subgroup.equivMapOfInjective (Subgroup.center A) e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3.map_center_mulEquiv e))

theorem center_transfer {A B : Type*} [Group A] [Group B] [Finite A] (e : A ≃* B) {p m : ℕ}
    (hcard : Nat.card ↥(Subgroup.center B) = m) (hexp : ∀ z ∈ Subgroup.center B, z ^ p = 1) :
    Nat.card ↥(Subgroup.center A) = m ∧ IsElementaryAbelian p ↥(Subgroup.center A) := by
  refine ⟨?_, ?_⟩
  · rw [← hcard]
    exact Nat.card_congr (centerEquiv e).toEquiv
  · refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
    refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun g => ?_
    apply (centerEquiv e).injective
    apply Subtype.ext
    rw [map_pow, map_one]
    have h1 := hexp (centerEquiv e g : B) (centerEquiv e g).2
    simpa using h1

end CFSG.GH74.GLS.IVK.Proofs2.Ivk47

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk47

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem exists_mulEquiv_sylow_G2 {K : Type} [Group K] [Finite K] {p n : ℕ} (hp : p.Prime)
    (hmodel : UntwistedChevalleyModel K .G2 (p ^ n)) (P : Sylow p K) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ n ∧
      Nonempty (↥(P : Subgroup K) ≃* ↥(posUnipotent .G2 F)) := by
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
  exact ⟨F, hFfield, hFfin, hFcard, ⟨(MulEquiv.subgroupCongr hP).trans
    ((Subgroup.equivMapOfInjective ((posUnipotent .G2 F).subgroupOf (adjointGroup .G2 F))
      (θ.symm.trans (MulAut.conj g)).toMonoidHom hinj).symm.trans
      (Subgroup.subgroupOfEquivOfLe hUC))⟩⟩

theorem center_sylow_G2_three {K : Type} [Group K] [Finite K] {n : ℕ}
    (hmodel : UntwistedChevalleyModel K .G2 (3 ^ n)) (P : Sylow 3 K) :
    IsElementaryAbelian 3 ↥(Subgroup.center ↥(P : Subgroup K)) ∧
      Nat.card ↥(Subgroup.center ↥(P : Subgroup K)) = (3 ^ n) ^ 2 := by
  obtain ⟨F, hFfield, hFfin, hF, ⟨e⟩⟩ := exists_mulEquiv_sylow_G2 Nat.prime_three hmodel P
  have hchar : CharP F 3 := charP_of_natCard_eq_pow Nat.prime_three hF
  have h3 : (3 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 3
  have hcard := card_center (K := F) h3
  have hexp : ∀ z ∈ Subgroup.center ↥(posUnipotent .G2 F), z ^ 3 = 1 := fun z hz =>
    pow_three_center h3 z hz
  have := center_transfer e (by rw [hcard, hF]) hexp
  rw [hF] at hcard
  exact ⟨this.2, this.1⟩

end CFSG.GH74.GLS.IVK.Proofs2.Ivk47

namespace CFSG.GH74.GLS.IVK.Proofs2

open CFSG.GH74.GLS.IVK Ivk47

theorem ivk_4_7f : IVK_4_7f := by
  intro K _ _ n hK P
  exact center_sylow_G2_three (untwisted_of_lieModel_G2 hK) P

theorem ivk_4_7ef : IVK_4_7ef := ⟨ivk_4_7e, ivk_4_7f⟩

end CFSG.GH74.GLS.IVK.Proofs2
