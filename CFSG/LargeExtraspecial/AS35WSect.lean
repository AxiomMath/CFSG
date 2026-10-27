module

public import CFSG.LargeExtraspecial.AS35WLocal
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCGWidthTwoFourGenerated
public import CFSG.GH74.SectionalRank

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.GH74

namespace AS35W

variable {F : Type} [Group F]

theorem fourGen_of_le_subgroup {K : Subgroup F} (hK : SectionalTwoRankLE K 4) {P : Subgroup F}
    (hPK : P ≤ K) (hP : IsPGroup 2 P) :
    ∃ s : Finset F, s.card ≤ 4 ∧ closure (s : Set F) = P := by
  classical
  have hP' : IsPGroup 2 (P.subgroupOf K) :=
    hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPK).symm
  obtain ⟨s, hs, hcl⟩ := hK _ hP'
  refine ⟨s.map ⟨K.subtype, K.subtype_injective⟩, by rw [Finset.card_map]; exact hs, ?_⟩
  rw [Finset.coe_map, Function.Embedding.coeFn_mk, ← MonoidHom.map_closure, hcl,
    Subgroup.map_subgroupOf_eq_of_le hPK]

theorem fourGen_of_sylow [Finite F] (S : Sylow 2 F)
    (h : ∀ P : Subgroup F, P ≤ (S : Subgroup F) →
      ∃ s : Finset F, s.card ≤ 4 ∧ Subgroup.closure (s : Set F) = P) :
    SectionalTwoRankLE F 4 := by
  classical
  intro P hP
  obtain ⟨T, hPT⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq F S T
  have hT : (T : Subgroup F) = (S : Subgroup F).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  have hP'S : P.map (MulAut.conj g⁻¹).toMonoidHom ≤ (S : Subgroup F) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hyT : y ∈ (S : Subgroup F).map (MulAut.conj g).toMonoidHom := hT ▸ hPT hy
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hyT
    have e : (MulAut.conj g⁻¹).toMonoidHom ((MulAut.conj g).toMonoidHom s) = s := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e]
    exact hs
  obtain ⟨X, hX4, hXcl⟩ := h _ hP'S
  refine ⟨X.image (fun x => g * x * g⁻¹), Finset.card_image_le.trans hX4, ?_⟩
  have hcoe : ((X.image (fun x => g * x * g⁻¹) : Finset F) : Set F) =
      (MulAut.conj g).toMonoidHom '' (X : Set F) := by
    rw [Finset.coe_image]
    rfl
  rw [hcoe, ← MonoidHom.map_closure, hXcl, Subgroup.map_map]
  ext x
  simp only [Subgroup.mem_map, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro hx
    exact ⟨x, hx, by group⟩

end AS35W

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem gen4_M (hw : S.width = 2) : SectionalTwoRankLE S.M 4 := by
  have hchar : CFSG.IsCharacteristicP 2 S.M := by
    change centralizer (CFSG.pCore 2 S.M : Set S.M) ≤ CFSG.pCore 2 S.M
    rw [← S.Q_eq_pCore]
    exact S.centralizer_le
  have hQ : IsExtraspecialPGroup 2 (CFSG.pCore 2 S.M) := by
    rw [← S.Q_eq_pCore]
    exact S.extraspecial
  have hQ32 : Nat.card (CFSG.pCore 2 S.M) = 32 := by
    rw [← S.Q_eq_pCore, S.card_Q_eq, hw]
    norm_num
  exact (CFSG.LocalAnalysis.GorensteinLyons.extraspecial_width_two_subgroups_four_generated
    hchar hQ hQ32).1

variable {L : Subgroup G} [hLn : L.Normal] (hzL : S.z ∈ L)
include hzL

theorem gen4_of_normal (hw : S.width = 2)
    (hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z)
    (hO : ∀ t ∈ S.QG, orderOf t = 2 → S.ZInOTwo t) (hC : centralizer (L : Set G) = ⊥) :
    SectionalTwoRankLE L 4 := by
  have hD := S.w2Data_of_normal hzL hw hW hO hC
  obtain ⟨P, hP⟩ := hD.sylow_le
  set K := centralizer ({(⟨S.z, hzL⟩ : L)} : Set L)
  have hKM : ∀ x : K, ((x : L) : G) ∈ S.M := fun x => by
    rw [S.mem_M_iff]
    exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.2)
  let f : K →* S.M := (L.subtype.comp K.subtype).codRestrict S.M hKM
  have hf : Function.Injective f := by
    intro x y hxy
    have := congrArg (fun m : S.M => (m : G)) hxy
    exact Subtype.ext (Subtype.ext this)
  have hK : SectionalTwoRankLE K 4 := SectionalTwoRankLE.of_injective f hf (S.gen4_M hw)
  refine AS35W.fourGen_of_sylow P fun Q hQ => ?_
  exact AS35W.fourGen_of_le_subgroup hK (hQ.trans hP) (P.isPGroup'.to_le hQ)

end Setting

end CFSG.LargeExtraspecial
