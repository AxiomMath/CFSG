module

public import CFSG.GF2Type.Smith1979W3.Dispatch
public import CFSG.GF2Type.Smith1979W3.CaseD.SettingNine
public import CFSG.GF2Type.Smith1979W3.CaseD.Equivariant
public import CFSG.GF2Type.Smith1979W3.CaseD.Stab
public import CFSG.LargeExtraspecial.S3bElevenThree

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979W3

open CFSG.LargeExtraspecial CFSG.GF2Type.Smith1979W3.CaseD Module

theorem irreducibleNoA2WidthThree_of_TI
    (hTI : CFSG.LargeExtraspecial.WeaklyClosedTITransitive.{0}) :
    CFSG.GF2Type.Smith1979W3.IrreducibleNoA2WidthThree := by
  intro G _ _ _ S hw hnwc hirr hno
  obtain ⟨g, haQ, hne⟩ := hnwc
  have hno' : ¬ S.HasTypeAInL g := hno g haQ hne
  obtain ⟨hL, -, hWts, hW3, -⟩ :=
    (S.lemma_3_11_two hTI (by omega) haQ hne hno').resolve_left hirr
  have hL4 : Nat.card (S.Lbar g) = 4 := by
    rw [hL, hw]
    norm_num
  haveI : Nontrivial (S.Lbar g) := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    have h1 : Nat.card (S.Lbar g) = 1 := Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
    omega
  obtain ⟨s, hs1⟩ := exists_ne (1 : S.Lbar g)
  have hsC := S.isTypeC_of_mem_Lbar_of_width_eq_three hTI hw haQ hne hno' hirr s.2
    (fun h => hs1 (Subtype.ext h))
  have hsM : (s : S.O) ∈ S.Mbar := S.Lbar_le_Mbar g s.2
  have hx0 : S.cl (g * S.z * g⁻¹) ≠ 0 := S.cl_conj_z_ne_zero haQ hne
  have hxq : S.q (S.cl (g * S.z * g⁻¹)) = 0 := S.q_cl_conj_z haQ
  obtain ⟨P, hPle, hPcard, hPfix⟩ :=
    exists_nine_le_stab S hw hWts (by rw [hW3, hw]) hirr hsM hsC hx0 hxq
  let P' : Subgroup (S.Qt ≃ₗ[ZMod 2] S.Qt) := P.map S.O.subtype
  have hP'card : Nat.card P' = 9 := by
    dsimp only [P']
    rw [Subgroup.card_map_of_injective S.O.subtype_injective, hPcard]
  have hPq : ∀ p' ∈ P', ∀ v, S.q (p' v) = S.q v := by
    intro p' hp' v
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hp'
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp p.2 v
  have hPW' : ∀ p' ∈ P', (S.clSub (S.QG ⊓ S.Qa g)).map (p' : S.Qt →ₗ[ZMod 2] S.Qt) =
      S.clSub (S.QG ⊓ S.Qa g) := by
    intro p' hp'
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hp'
    have hpM : p ∈ S.Mbar := hPle hp
    obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp hpM
    rw [← hm]
    exact map_clSub_eq_of_fix S haQ hne m (by rw [hm]; exact hPfix p hp)
  haveI : FiniteDimensional (ZMod 2) S.Qt := Module.Finite.of_finite
  exact (card_ne_nine_of_stab S.q S.q_nondegenerate
    (by rw [S.finrank_Qt_eq_two_mul_width, hw])
    (S.clSub (S.QG ⊓ S.Qa g)) hWts (by rw [hW3, hw]) P' hPq hPW') hP'card

end CFSG.GF2Type.Smith1979W3
