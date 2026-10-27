module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Frame
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.ClassicalInvolution.QuaternionStructure
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Lemma32
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Conj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Struct
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.ComponentClassification.CatFactsSmall.PSp43

local notation "P45" => Equiv.Perm (Fin 45)

namespace PspFrame

variable {G : Type} [Group G] {L : Subgroup G} (F : PspFrame L)

@[expose] def img (X : Subgroup G) : Subgroup P45 := (X.subgroupOf L).map F.ψ

@[expose] def pre (K : Subgroup P45) : Subgroup G := (K.comap F.ψ).map L.subtype

variable {F} {X Y : Subgroup G} {K K' : Subgroup P45}

theorem mem_img {p : P45} : p ∈ F.img X ↔ ∃ l : ↥L, (l : G) ∈ X ∧ F.ψ l = p := by
  simp [img, Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem psi_mem_img {l : ↥L} : F.ψ l ∈ F.img X ↔ (l : G) ∈ X := by
  rw [mem_img]
  constructor
  · rintro ⟨l', hl', h⟩
    have : l' = l := F.ψ_injective h
    rwa [this] at hl'
  · intro h
    exact ⟨l, h, rfl⟩

theorem mem_pre {g : G} : g ∈ F.pre K ↔ ∃ h : g ∈ L, F.ψ ⟨g, h⟩ ∈ K := by
  simp only [pre, Subgroup.mem_map, Subgroup.mem_comap]
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l.2, hl⟩
  · rintro ⟨h, hg⟩
    exact ⟨⟨g, h⟩, hg, rfl⟩

theorem img_le_P (X : Subgroup G) : F.img X ≤ QP45.originalSubgroup := by
  intro p hp
  obtain ⟨l, -, rfl⟩ := mem_img.1 hp
  exact F.ψ_mem l

theorem pre_le (K : Subgroup P45) : F.pre K ≤ L := fun g hg => (mem_pre.1 hg).1

theorem img_mono (h : X ≤ Y) : F.img X ≤ F.img Y := by
  intro p hp
  obtain ⟨l, hl, rfl⟩ := mem_img.1 hp
  exact mem_img.2 ⟨l, h hl, rfl⟩

theorem pre_mono (h : K ≤ K') : F.pre K ≤ F.pre K' := by
  intro g hg
  obtain ⟨hL, hK⟩ := mem_pre.1 hg
  exact mem_pre.2 ⟨hL, h hK⟩

theorem img_pre (hK : K ≤ QP45.originalSubgroup) : F.img (F.pre K) = K := by
  apply le_antisymm
  · intro p hp
    obtain ⟨l, hl, rfl⟩ := mem_img.1 hp
    exact (mem_pre.1 hl).2
  · intro p hp
    obtain ⟨l, rfl⟩ := F.ψ_surj (hK hp)
    exact mem_img.2 ⟨l, mem_pre.2 ⟨l.2, hp⟩, rfl⟩

theorem pre_img (hX : X ≤ L) : F.pre (F.img X) = X := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hL, hmem⟩ := mem_pre.1 hg
    obtain ⟨l, hl, hψ⟩ := mem_img.1 hmem
    have : l = ⟨g, hL⟩ := F.ψ_injective hψ
    rw [this] at hl
    exact hl
  · intro g hg
    exact mem_pre.2 ⟨hX hg, mem_img.2 ⟨⟨g, hX hg⟩, hg, rfl⟩⟩

theorem img_le_img_iff (hX : X ≤ L) (hY : Y ≤ L) : F.img X ≤ F.img Y ↔ X ≤ Y := by
  refine ⟨fun h => ?_, img_mono⟩
  rw [← pre_img hX, ← pre_img hY]
  exact pre_mono h

theorem img_inj (hX : X ≤ L) (hY : Y ≤ L) : F.img X = F.img Y ↔ X = Y := by
  refine ⟨fun h => le_antisymm ?_ ?_, fun h => h ▸ rfl⟩
  · exact (img_le_img_iff hX hY).1 h.le
  · exact (img_le_img_iff hY hX).1 h.ge

theorem img_L : F.img L = QP45.originalSubgroup := by
  apply le_antisymm (img_le_P L)
  intro p hp
  obtain ⟨l, rfl⟩ := F.ψ_surj hp
  exact mem_img.2 ⟨l, l.2, rfl⟩

theorem img_bot : F.img (⊥ : Subgroup G) = ⊥ := by
  apply le_antisymm
  · intro p hp
    obtain ⟨l, hl, rfl⟩ := mem_img.1 hp
    have : l = 1 := Subtype.ext (by simpa using hl)
    rw [this, map_one]
    exact Subgroup.one_mem _
  · exact bot_le

theorem img_sup (hX : X ≤ L) (hY : Y ≤ L) : F.img (X ⊔ Y) = F.img X ⊔ F.img Y := by
  apply le_antisymm
  · have hZ : F.img X ⊔ F.img Y ≤ QP45.originalSubgroup := sup_le (img_le_P X) (img_le_P Y)
    have h1 : X ⊔ Y ≤ F.pre (F.img X ⊔ F.img Y) :=
      sup_le ((pre_img hX).ge.trans (pre_mono le_sup_left))
        ((pre_img hY).ge.trans (pre_mono le_sup_right))
    calc F.img (X ⊔ Y) ≤ F.img (F.pre (F.img X ⊔ F.img Y)) := img_mono h1
      _ = F.img X ⊔ F.img Y := img_pre hZ
  · exact sup_le (img_mono le_sup_left) (img_mono le_sup_right)

theorem card_img (hX : X ≤ L) : Nat.card (F.img X) = Nat.card X := by
  rw [img, Subgroup.card_map_of_injective F.ψ_injective]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv

@[expose] noncomputable def imgEquiv (hX : X ≤ L) : ↥X ≃* ↥(F.img X) :=
  (Subgroup.subgroupOfEquivOfLe hX).symm.trans
    (Subgroup.equivMapOfInjective (X.subgroupOf L) F.ψ F.ψ_injective)

theorem imgEquiv_apply (hX : X ≤ L) (x : ↥X) :
    ((F.imgEquiv hX x : ↥(F.img X)) : P45) = F.ψ ⟨(x : G), hX x.2⟩ := rfl

theorem relIndex_img (hXY : X ≤ Y) (hY : Y ≤ L) :
    (F.img X).relIndex (F.img Y) = X.relIndex Y := by
  rw [img, img, Subgroup.relIndex_map_map_of_injective _ _ F.ψ_injective,
    Subgroup.relIndex_subgroupOf hY]

theorem img_commutator (hX : X ≤ L) (hY : Y ≤ L) : F.img ⁅X, Y⁆ = ⁅F.img X, F.img Y⁆ := by
  have hXY : ⁅X, Y⁆ ≤ L := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    show a * b * a⁻¹ * b⁻¹ ∈ L
    exact L.mul_mem (L.mul_mem (L.mul_mem (hX ha) (hY hb)) (L.inv_mem (hX ha)))
      (L.inv_mem (hY hb))
  have h : ⁅X, Y⁆.subgroupOf L = ⁅X.subgroupOf L, Y.subgroupOf L⁆ := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hXY,
      Subgroup.map_subgroupOf_eq_of_le hX, Subgroup.map_subgroupOf_eq_of_le hY]
  rw [img, h, Subgroup.map_commutator]
  rfl

end PspFrame

end CFSG.OddStandard.SmallF3.Omega
