module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCat81E6A8Gen4
public import CFSG.LocalAnalysis.OddStandard.ThmCTWr
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.GH312.AlmostSimpleLocal
import CFSG.GH74.GLS.IVK.Proofs2.Ivk94G4Layer
import CFSG.Goldschmidt.Steps.Sec82e
import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyGHCent
import CFSG.Sporadic.Schreier.J4SSylowBase
import Certificates.Data.A5

public section

open Subgroup

namespace CFSG.EvenSporadicStandard.TwoHS.GH312

theorem exists_injective_hom_perm_fin_eight :
    ∃ f : RegularWreathProduct (DihedralGroup 4) (Multiplicative (ZMod 2)) →*
      Equiv.Perm (Fin 8), Function.Injective f := by
  classical
  let _ : MulAction (DihedralGroup 4) (ZMod 4) :=
    { smul := CFSG.OddStandard.ThmC.T.D8smul
      one_smul := CFSG.OddStandard.ThmC.T.D8smul_one
      mul_smul := CFSG.OddStandard.ThmC.T.D8smul_mul }
  have : FaithfulSMul (DihedralGroup 4) (ZMod 4) :=
    ⟨fun {a b} h => CFSG.OddStandard.ThmC.T.D8smul_faithful a b h⟩
  have hinj := RegularWreathProduct.toPermInj (DihedralGroup 4) (Multiplicative (ZMod 2)) (ZMod 4)
  have hcard : Nat.card (ZMod 4 × Multiplicative (ZMod 2)) = 8 := by
    rw [Nat.card_prod]
    have h1 : Nat.card (ZMod 4) = 4 := Nat.card_zmod 4
    have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := Nat.card_zmod 2
    rw [h1, h2]
  let enc : ZMod 4 × Multiplicative (ZMod 2) ≃ Fin 8 :=
    (Finite.equivFin _).trans (finCongr hcard)
  exact ⟨enc.permCongrHom.toMonoidHom.comp
    (RegularWreathProduct.toPerm (DihedralGroup 4) (Multiplicative (ZMod 2)) (ZMod 4)),
    enc.permCongrHom.injective.comp hinj⟩

theorem sectionalTwoRankLE_four_regularWreathProduct :
    CFSG.GH74.SectionalTwoRankLE
      (RegularWreathProduct (DihedralGroup 4) (Multiplicative (ZMod 2))) 4 := by
  obtain ⟨f, hf⟩ := exists_injective_hom_perm_fin_eight
  exact CFSG.GH74.SectionalTwoRankLE.of_injective f hf
    CFSG.ComponentClassification.GSThmB.Cat81A8.gen4_perm8

theorem sectionalTwoRankLE_four_of_sylow_mulEquiv {X : Type*}
    [Group X] [Finite X] (P : Sylow 2 X)
    (ι : ↥(P : Subgroup X) ≃* RegularWreathProduct (DihedralGroup 4) (Multiplicative (ZMod 2))) :
    CFSG.GH74.SectionalTwoRankLE X 4 :=
  CFSG.CGT.PushingUpLit.SolK.SectionalTwoRankLE.of_sylow P
    (CFSG.GH74.SectionalTwoRankLE.of_mulEquiv ι.symm
      sectionalTwoRankLE_four_regularWreathProduct)

theorem sectionalTwoRankLE_four_subgroup_of_sylow_mulEquiv
    {X : Type*} [Group X] [Finite X] (P : Sylow 2 X)
    (ι : ↥(P : Subgroup X) ≃* RegularWreathProduct (DihedralGroup 4) (Multiplicative (ZMod 2)))
    (T : Subgroup X) : CFSG.GH74.SectionalTwoRankLE ↥T 4 :=
  (sectionalTwoRankLE_four_of_sylow_mulEquiv P ι).subgroup T

theorem AlmostSimpleLocal.three_le_twoRank {T : Type*} [Group T] [Finite T] {u : T}
    (h : AlmostSimpleLocal T u) : 3 ≤ CFSG.Open.twoRank T := by
  classical
  obtain ⟨K, hKC, ⟨φ⟩⟩ := h.exists_alt
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  have hnab : ∃ a b : alternatingGroup (Fin 5), a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have : IsMulCommutative (alternatingGroup (Fin 5)) := ⟨⟨fun a b => hcon a b⟩⟩
    have h3 := alternatingGroup.isMulCommutative_iff_card_le_three.1 this
    simp at h3
  obtain ⟨V₀, hV₀c, hV₀2, hV₀4⟩ :=
    CFSG.GH74.GLS.IVK.Proofs2.Ivk94.exists_four_group_of_simple hnab
  let ψ : alternatingGroup (Fin 5) →* T := K.subtype.comp φ.symm.toMonoidHom
  have hψ : Function.Injective ψ := K.subtype_injective.comp φ.symm.injective
  have hψC : ∀ a, ψ a ∈ centralizer ({u} : Set T) := fun a => hKC (φ.symm a).2
  have hu_not : ∀ a, ψ a ≠ u := by
    intro a ha
    have ha1 : a = 1 := CFSG.EvenSporadicStandard.TwoHS.SAFyGH.center_A5 a (fun c => by
      apply hψ
      rw [map_mul, map_mul, ha]
      exact mem_centralizer_singleton_iff.1 (hψC c))
    rw [ha1, map_one] at ha
    have := h.orderOf_eq
    rw [← ha, orderOf_one] at this
    omega
  have hu2 : u ^ 2 = 1 := by rw [← h.orderOf_eq]; exact pow_orderOf_eq_one u
  obtain ⟨hel, hcard⟩ := CFSG.Goldschmidt.Sec82.isElemAbelian_sup_zpowers (q := 2) Nat.prime_two
    (E := V₀.map ψ)
    (by rw [Subgroup.card_map_of_injective hψ, hV₀4]; norm_num)
    (by
      rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hV₀2 a ha, map_one])
    hu2
    (by
      rintro ⟨a, -, ha⟩
      exact hu_not a ha)
    (by
      rintro _ ⟨a, -, rfl⟩
      exact mem_centralizer_singleton_iff.1 (hψC a))
  refine le_csSup ⟨Nat.card T, ?_⟩ ⟨V₀.map ψ ⊔ zpowers u, le_top, hel, hcard⟩
  rintro k ⟨E, -, -, hk⟩
  calc k ≤ 2 ^ k := Nat.lt_two_pow_self.le
    _ = Nat.card E := hk.symm
    _ ≤ Nat.card T := Subgroup.card_le_card_group E

end CFSG.EvenSporadicStandard.TwoHS.GH312
