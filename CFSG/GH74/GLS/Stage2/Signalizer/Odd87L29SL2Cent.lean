module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29TwoNilp
public import CFSG.GH74.GLS.IVK.Lifted.SL2Aut
public import CFSG.GH74.GLS.IVK.L2.FieldProj
import CFSG.GH74.GLS.IVK.Proofs2.Lemma13d

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Lifted CFSG.GorensteinWalter CFSG.ABGLocalTools
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo

namespace L29SL2Cent

variable {F : Type} [Field F] [Finite F]

theorem thetaEquiv_eq_semilinear (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F) :
    thetaEquiv hodd h3 = semilinearEquivAut F := by
  apply MulEquiv.ext
  intro x
  exact (congrArg (fun f => f x)
    (semilinearAction_eq_native F (isOddPrimePower_card_of_odd hodd) h3)).symm

omit [Finite F] in
theorem toPSL_symm_equivPSL : toPSL ((L2.equivPSL F).symm) = MulEquiv.refl (PSL2 F) := by
  ext x
  simp [toPSL]

theorem fieldProj_symm_equivPSL (u : MulAut (PSL2 F)) :
    fieldProj ((L2.equivPSL F).symm) u = ((semilinearEquivAut F).symm u).right := by
  rw [fieldProj_apply]
  show ((semilinearEquivAut F).symm (MulAut.congr (toPSL _) u)).right = _
  rw [toPSL_symm_equivPSL]
  rfl

end L29SL2Cent

theorem twoNilp_centralizer_innDiag {F : Type} [Field F] [Finite F] (hF : IVK.L2Field F)
    {K : Type} [Group K] [Finite K] (e : K ≃* L2 F) {u : MulAut K} (hu : u ∈ innDiagSub e)
    (hu2 : orderOf u = 2) : TwoNilp ↥(centralizer ({u} : Set (MulAut K))) := by
  obtain ⟨Y, hYC, hYn, hYodd, ⟨k, hk⟩, -⟩ := Proofs2.ivk_1_3d F hF K e u hu hu2
  set C : Subgroup (MulAut K) := centralizer ({u} : Set (MulAut K)) with hC
  have hcard : Nat.card ↥(Y.subgroupOf C) = Nat.card ↥Y :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYC).toEquiv
  refine ⟨Y.subgroupOf C, ⟨fun n hn g => ?_⟩, by rw [hcard]; exact hYodd, k, ?_⟩
  · show ((g : MulAut K) * (n : MulAut K) * (g : MulAut K)⁻¹) ∈ Y
    exact hYn g g.2 n hn
  · have h1 := Subgroup.card_mul_index (Y.subgroupOf C)
    rw [hcard, ← hk] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1

theorem twoNilp_centralizer_sl2 {F : Type} [Field F] [Finite F] (hF : IVK.L2Field F)
    {Q : Type} [Group Q] (e : Q ≃* Matrix.SpecialLinearGroup (Fin 2) F) (φ : MulAut Q)
    (hφ2 : φ * φ = 1) (hφ1 : φ ≠ 1) (hnf : ¬ IVK.Lifted.FixedCond Q φ) :
    TwoNilp ↥(Subgroup.centralizer ({φ} : Set (MulAut Q))) := by
  have hodd : Odd (Nat.card F) := hF.1
  have h3 : 3 < Nat.card F := hF.2
  set α : MulAut (Matrix.SpecialLinearGroup (Fin 2) F) := MulAut.congr e φ with hα
  have hα2 : α * α = 1 := by rw [hα, ← map_mul, hφ2, map_one]
  have hα1 : α ≠ 1 := fun h => hφ1 ((MulAut.congr e).injective (h.trans (map_one _).symm))
  have hσ : (gammaOf hodd h3 α).right = 1 := by
    by_contra hne
    exact hnf (fixedCond_of_congr e (fixedCond_of_field_part hodd h3 α hα2 hne))
  set u : MulAut (PSL2 F) := psl2AutHom α with hu
  have hu2 : u * u = 1 := by rw [hu, ← map_mul, hα2, map_one]
  have hu1 : u ≠ 1 := fun h => hα1 (psl2AutHom_injective hodd h3 (h.trans (map_one _).symm))
  have hu_ord : orderOf u = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1
  have hu_mem : u ∈ innDiagSub ((L2.equivPSL F).symm) := by
    rw [mem_innDiagSub_iff, L29SL2Cent.fieldProj_symm_equivPSL,
      ← L29SL2Cent.thetaEquiv_eq_semilinear hodd h3]
    exact hσ
  have hTN : TwoNilp ↥(centralizer ({u} : Set (MulAut (PSL2 F)))) :=
    twoNilp_centralizer_innDiag hF ((L2.equivPSL F).symm) hu_mem hu_ord
  let ψ : MulAut Q →* MulAut (PSL2 F) := psl2AutHom.comp (MulAut.congr e).toMonoidHom
  have hψinj : Function.Injective ψ :=
    (psl2AutHom_injective hodd h3).comp (MulAut.congr e).injective
  have hψφ : ψ φ = u := rfl
  have hmaps : ∀ c ∈ centralizer ({φ} : Set (MulAut Q)),
      ψ c ∈ centralizer ({u} : Set (MulAut (PSL2 F))) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have := congrArg ψ (hc φ (Set.mem_singleton φ))
    rwa [map_mul, map_mul, hψφ] at this
  let f : ↥(centralizer ({φ} : Set (MulAut Q))) →* ↥(centralizer ({u} : Set (MulAut (PSL2 F)))) :=
    (ψ.comp (centralizer ({φ} : Set (MulAut Q))).subtype).codRestrict _ (fun c => hmaps c c.2)
  have hf : Function.Injective f := fun a b h => Subtype.ext (hψinj (congrArg Subtype.val h))
  exact twoNilp_of_injective f hf hTN

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
