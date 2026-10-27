module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitL24VA7
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitAut5L2Base
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourMapInjective

public section

namespace CFSG.ComponentClassification.FooteLit.L24V

open CFSG GorensteinWalter Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.Foote5
open CFSG.ComponentClassification.AutL2Facts

theorem l24V_l2 {F : Type} [Field F]
    [Finite F] (hodd : IsOddPrimePower (Nat.card F)) {𝕊 : Type} [Group 𝕊] [Finite 𝕊]
    (e : 𝕊 ≃* PSL2 F)
    {V : Subgroup (MulAut 𝕊)} (hV : IsKleinFour V) (hVI : V ≤ innAut5 𝕊)
    {P : Subgroup (MulAut 𝕊)} (hP : IsSylowOf 2 P (centralizer (V : Set (MulAut 𝕊)))) :
    ∃ f ∈ P, P = zpowers f ⊔ V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hconj : Function.Injective (MulAut.conj : 𝕊 →* MulAut 𝕊) := fun y y' h => by
    have h1 := congrArg (autEquiv e) h
    rw [autEquiv_conj, autEquiv_conj] at h1
    exact e.injective (incl_injective F h1)
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb => by
    have := hV
    exact congrArg Subtype.val
      ((IsKleinFour.isMulCommutative (G := V)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hV.card_four]; norm_num)
  obtain ⟨hPC, -⟩ := le_and_isPGroup_of_isSylowOf hP
  have := isCyclic_ringAut F
  refine exists_eq_zpowers_sup (SemidirectProduct.rightHom.comp (autEquiv e).toMonoidHom)
    (le_of_isSylowOf_centralizer hVc hV2 hP) fun x hxP hx1 => ?_
  have hxl := Aut5L2.eq_inl_of_right_eq_one (x := autEquiv e x) hx1
  have hW := isKleinFour_comap_conj hconj hV hVI
  set ι : 𝕊 →* PGL2 F :=
    (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).comp e.toMonoidHom with hιdef
  have hι : Function.Injective ι :=
    Matrix.ProjectiveSpecialLinearGroup.toPGL_injective.comp e.injective
  have hW' := isKleinFour_map_of_injective _ hW ι hι
  have hc : (autEquiv e x).left ∈ centralizer
      (((V.comap (MulAut.conj : 𝕊 →* MulAut 𝕊)).map ι : Subgroup (PGL2 F)) : Set (PGL2 F)) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨w, hw, rfl⟩
    have h1 : x * MulAut.conj w = MulAut.conj w * x :=
      (mem_centralizer_iff.mp (hPC hxP) _ hw).symm
    have h2 := congrArg (autEquiv e) h1
    rw [map_mul, map_mul, autEquiv_conj, hxl, incl_apply, ← map_mul, ← map_mul] at h2
    exact (SemidirectProduct.inl_injective h2).symm
  rw [pgl2_kleinFour_centralizer_eq_self F hodd _ hW'] at hc
  obtain ⟨w, hw, hwx⟩ := hc
  have hxw : x = MulAut.conj w := (autEquiv e).injective (by
    rw [hxl, ← hwx, autEquiv_conj, incl_apply]
    rfl)
  rw [hxw]
  exact hw

end CFSG.ComponentClassification.FooteLit.L24V
