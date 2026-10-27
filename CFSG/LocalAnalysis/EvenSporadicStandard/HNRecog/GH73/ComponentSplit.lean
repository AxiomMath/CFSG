module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Comp
public import CFSG.LocalAnalysis.ComponentInitial.KProperPumpUpStatement

public section

namespace CFSG.EvenSporadicStandard.HNRecog.GH73

open CFSG.LocalAnalysis.ComponentInitial

theorem component_splits {X : Type} [Group X] [Finite X] [Group.IsPerfect X]
    (hK : CFSG.SectionRank.IsKGroupCat X) (hS : SchreierFor CFSG.Blueprint.Catalog)
    (hG : CFSG.GH74.Gen4 X) (hZ : Subgroup.center X = ⊥)
    (L : Subgroup X) (hL : CFSG.IsComponent L) :
    L.Normal ∧ IsSimpleGroup ↥L ∧ ∃ C : Subgroup X, C.Normal ∧ Disjoint L C ∧ L ⊔ C = ⊤ ∧
      ∀ l ∈ L, ∀ c ∈ C, l * c = c * l := by
  classical
  have hcard : Nat.card (CFSG.LocalCores.ComponentIndex X) ≤ 2 :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.card_componentIndex_le_two hG
  let P : X →* Equiv.Perm (CFSG.LocalCores.ComponentIndex X) :=
    MulAction.toPermHom X (CFSG.LocalCores.ComponentIndex X)
  have hPermComm : IsMulCommutative (Equiv.Perm (CFSG.LocalCores.ComponentIndex X)) :=
    Equiv.Perm.isMulCommutative_iff_card_le_two.mpr hcard
  have hker : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ ≤ P.ker := by
    rw [Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hPermComm.is_comm.comm _ _)
  have htop : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = (⊤ : Subgroup X) :=
    Group.IsPerfect.commutator_eq_top (G := X)
  have hker_top : P.ker = ⊤ := le_antisymm le_top (htop ▸ hker)
  have hPone : ∀ x : X, P x = 1 := by
    intro x
    exact MonoidHom.mem_ker.mp (hker_top.symm ▸ Subgroup.mem_top x)
  have hLmap : ∀ x : X, L.map (MulAut.conj x).toMonoidHom = L := by
    intro x
    have hfix : x • (⟨L, hL⟩ : CFSG.LocalCores.ComponentIndex X) = ⟨L, hL⟩ := by
      have h := DFunLike.congr_fun (hPone x) (⟨L, hL⟩ : CFSG.LocalCores.ComponentIndex X)
      simpa [P] using h
    have hfix' : (x • (⟨L, hL⟩ : CFSG.LocalCores.ComponentIndex X)).1 = L :=
      congrArg Subtype.val hfix
    simpa [CFSG.GH74.GLS.Stage2.Bender.Thm1.smul_component_val] using hfix'
  have hLnorm : L.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hmem : g * n * g⁻¹ ∈ L.map (MulAut.conj g).toMonoidHom :=
      ⟨n, hn, by simp [MulAut.conj_apply]⟩
    rwa [hLmap g] at hmem
  haveI : L.Normal := hLnorm
  haveI hPerfectL : Group.IsPerfect ↥L := hL.1.1
  haveI hSimpleQuot : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.1.2.1
  have hCatalog : CFSG.Blueprint.Catalog (↥L ⧸ Subgroup.center ↥L) :=
    CFSG.SectionRank.catalog_of_isKGroupCat_of_surjective hK L
      (QuotientGroup.mk' (Subgroup.center ↥L)) (QuotientGroup.mk'_surjective _)
  haveI hOuterQuot : Group.IsSolvable
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer (↥L ⧸ Subgroup.center ↥L)) :=
    hS (↥L ⧸ Subgroup.center ↥L) hL.1.2.2 hCatalog
  haveI : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥L) :=
    CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_centerQuotient ↥L
  have hsup : L ⊔ Subgroup.centralizer (L : Set X) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hnormalizes : (⊤ : Subgroup X) ≤ Subgroup.normalizer (L : Set X) :=
      le_of_eq (Subgroup.normalizer_eq_top L).symm
    obtain ⟨implementer, himpl, haction⟩ :=
      CFSG.ComponentClassification.ComponentInnerActions.perfect_normalizer_action_inner
        (G := X) (⊤ : Subgroup X) L hnormalizes (⟨x, trivial⟩ : (⊤ : Subgroup X))
    have haction' : ∀ member ∈ L,
        x * member * x⁻¹ = implementer * member * implementer⁻¹ := haction
    refine Subgroup.mem_sup_of_normal_left.mpr
      ⟨implementer, himpl, implementer⁻¹ * x, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro member hmemb
      have key : implementer⁻¹ * x * member = member * implementer⁻¹ * x := by
        calc implementer⁻¹ * x * member
            = implementer⁻¹ * (x * member * x⁻¹) * x := by group
          _ = implementer⁻¹ * (implementer * member * implementer⁻¹) * x := by
                rw [haction' member hmemb]
          _ = member * implementer⁻¹ * x := by group
      simpa only [mul_assoc] using key.symm
    · group
  have hcenterL : Subgroup.center ↥L = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    apply Subtype.ext
    have hzX : (z : X) ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro x
      have hx : x ∈ L ⊔ Subgroup.centralizer (L : Set X) := by rw [hsup]; trivial
      obtain ⟨l, hl, c, hc, hlc⟩ := Subgroup.mem_sup_of_normal_left.mp hx
      have hzl : l * (z : X) = (z : X) * l := by
        simpa using congrArg Subtype.val (Subgroup.mem_center_iff.mp hz (⟨l, hl⟩ : ↥L))
      have hzc : (z : X) * c = c * (z : X) :=
        Subgroup.mem_centralizer_iff.mp hc (z : X) z.property
      rw [← hlc]
      calc (l * c) * (z : X) = l * (c * (z : X)) := by group
        _ = l * ((z : X) * c) := by rw [hzc]
        _ = (l * (z : X)) * c := by group
        _ = ((z : X) * l) * c := by rw [hzl]
        _ = (z : X) * (l * c) := by group
    have hz1 : (z : X) = 1 := by
      rw [hZ] at hzX
      simpa using hzX
    simpa using hz1
  have hsimpleL : IsSimpleGroup ↥L := by
    have e : (↥L ⧸ Subgroup.center ↥L) ≃* ↥L :=
      (QuotientGroup.quotientMulEquivOfEq hcenterL).trans QuotientGroup.quotientBot
    exact e.symm.isSimpleGroup
  refine ⟨hLnorm, hsimpleL, Subgroup.centralizer (L : Set X), ?_, ?_, hsup, ?_⟩
  · exact Subgroup.normal_centralizer
  · rw [disjoint_iff, Subgroup.eq_bot_iff_forall]
    intro g hg
    rw [Subgroup.mem_inf] at hg
    obtain ⟨hgL, hgC⟩ := hg
    have hz : (⟨g, hgL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      have hyc : (y : X) * g = g * (y : X) :=
        Subgroup.mem_centralizer_iff.mp hgC (y : X) y.property
      simpa using hyc
    rw [hcenterL] at hz
    have hg1 : (⟨g, hgL⟩ : ↥L) = 1 := Subgroup.mem_bot.mp hz
    simpa using congrArg Subtype.val hg1
  · intro l hl c hc
    exact Subgroup.mem_centralizer_iff.mp hc l hl

end CFSG.EvenSporadicStandard.HNRecog.GH73
