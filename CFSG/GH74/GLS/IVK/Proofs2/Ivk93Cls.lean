module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Pair
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93ModelJ
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Sections
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47abG2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Sylow

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Local.P34 CFSG.ComponentClassification CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}

theorem ghList_J (hctx : Stage2Ctx G z k S) {H : Subgroup G} (hne : H ≠ ⊤)
    (hs : IsSimpleGroup ↥(generalizedFitting (HBar H)))
    (hn : ∃ a b : ↥(generalizedFitting (HBar H)), a * b ≠ b * a) :
    GHList ↥(generalizedFitting (HBar H)) :=
  ghList_of_subgroup_of_quotient hctx.std.kgh hne (mkH H) (QuotientGroup.mk'_surjective _) _ hs hn

theorem jm_apply (hctx : Stage2Ctx G z k S) {H : Subgroup G} (hCH : Cen z ≤ H)
    (hzJ : mkH H ⟨z, hCH (mem_Cen_self z)⟩ ∈ generalizedFitting (HBar H)) {q : ℕ} (hq : Odd q)
    (h5 : 5 ≤ q) (hK : IVK.IsSp4L4U4 ↥(generalizedFitting (HBar H)) q)
    (T : Sylow 2 (HBar H)) (hT : (T : Subgroup (HBar H)) = barIn H S) :
    ∃ (y : ↥(generalizedFitting (HBar H))) (b : ℕ), orderOf y = 2 ∧
      ¬ IsConj (⟨mkH H ⟨z, hCH (mem_Cen_self z)⟩, hzJ⟩ : ↥(generalizedFitting (HBar H))) y ∧
      (∀ u : ↥(generalizedFitting (HBar H)), orderOf u = 2 →
        IsConj (⟨mkH H ⟨z, hCH (mem_Cen_self z)⟩, hzJ⟩ : ↥(generalizedFitting (HBar H))) u ∨
          IsConj y u) ∧
      (b = 2 ∨ b = 4) ∧ (b = 2 ↔ IVK.IsPSp4 ↥(generalizedFitting (HBar H)) q) ∧
      Nat.card ↥((T : Subgroup (HBar H)) ⊓ generalizedFitting (HBar H)) = 2 ^ Ivk93Adapt.nuQ q * b := by
  have : (generalizedFitting (HBar H)).Normal := LocalCores.generalized_fitting_characteristic.2
  obtain ⟨P, hP⟩ := Glauberman.sylow_inf_normal T (N := generalizedFitting (HBar H))
  have hz2 : orderOf z = 2 := hctx.orderOf_z
  have hx2 := (isCentralInvolution_zbar hctx hCH hzJ).1
  have hzP : (⟨mkH H ⟨z, hCH (mem_Cen_self z)⟩, hzJ⟩ : ↥(generalizedFitting (HBar H))) ∈
      (P : Subgroup ↥(generalizedFitting (HBar H))) := by
    rw [hP, Subgroup.mem_subgroupOf]
    exact ⟨by rw [hT]; exact zbar_mem_barIn hctx hCH, hzJ⟩
  have hzc : ∀ s ∈ (P : Subgroup ↥(generalizedFitting (HBar H))),
      s * (⟨mkH H ⟨z, hCH (mem_Cen_self z)⟩, hzJ⟩ : ↥(generalizedFitting (HBar H))) =
        ⟨mkH H ⟨z, hCH (mem_Cen_self z)⟩, hzJ⟩ * s := by
    intro s hs
    rw [hP, Subgroup.mem_subgroupOf] at hs
    exact Subtype.ext (zbar_comm_barIn hctx hCH (hT ▸ hs.1))
  obtain ⟨y, b, h1, h2, h3, h4, h5', h6⟩ := jm_card_classes hq h5 hK P hzP hx2 hzc
  refine ⟨y, b, h1, h2, h3, h4, h5', ?_⟩
  rw [← h6, hP]
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : (T : Subgroup (HBar H)) ⊓ generalizedFitting (HBar H) ≤ generalizedFitting (HBar H))).toEquiv]


theorem fus_of_J_two_classes {H : Subgroup G} {z x : G} (hzH : z ∈ H) (hxH : x ∈ H)
    (hz2 : orderOf z = 2) (hx2 : orderOf x = 2) (hzx : ¬ IsConj z x)
    (hcl : ∀ u : G, orderOf u = 2 → IsConj z u ∨ IsConj x u)
    (T : Sylow 2 (HBar H)) (hTJ : (T : Subgroup (HBar H)) ≤ generalizedFitting (HBar H))
    (hzJ : mkH H ⟨z, hzH⟩ ∈ generalizedFitting (HBar H))
    {y : ↥(generalizedFitting (HBar H))}
    (hJcl : ∀ u : ↥(generalizedFitting (HBar H)), orderOf u = 2 →
        IsConj (⟨mkH H ⟨z, hzH⟩, hzJ⟩ : ↥(generalizedFitting (HBar H))) u ∨ IsConj y u) :
    FUS H := by
  have : (generalizedFitting (HBar H)).Normal := LocalCores.generalized_fitting_characteristic.2
  have hodd := index_odd_of_sylow_le T hTJ
  have hinv : ∀ u : HBar H, orderOf u = 2 → u ∈ generalizedFitting (HBar H) := fun u hu =>
    involution_mem_of_odd_index hodd hu
  have hzH2 : orderOf (⟨z, hzH⟩ : ↥H) = 2 := by rw [← Subgroup.orderOf_coe]; exact hz2
  have hxH2 : orderOf (⟨x, hxH⟩ : ↥H) = 2 := by rw [← Subgroup.orderOf_coe]; exact hx2
  have hxb2 : orderOf (mkH H ⟨x, hxH⟩) = 2 := orderOf_mk_eq_two H hxH2
  have hxbJ : mkH H ⟨x, hxH⟩ ∈ generalizedFitting (HBar H) := hinv _ hxb2
  have toX : ∀ {a b : ↥(generalizedFitting (HBar H))}, IsConj a b → IsConj (a : HBar H) (b : HBar H) :=
    fun {a b} h => MonoidHom.map_isConj (generalizedFitting (HBar H)).subtype h
  have hxy : IsConj y (⟨mkH H ⟨x, hxH⟩, hxbJ⟩ : ↥(generalizedFitting (HBar H))) := by
    rcases hJcl ⟨mkH H ⟨x, hxH⟩, hxbJ⟩ (by rw [← Subgroup.orderOf_coe]; exact hxb2) with h | h
    · exfalso
      have h1 : IsConj (mkH H ⟨z, hzH⟩) (mkH H ⟨x, hxH⟩) := toX h
      have h2 : IsConj (⟨z, hzH⟩ : ↥H) ⟨x, hxH⟩ := isConj_of_mk_isConj H hzH2 hxH2 h1
      exact hzx (MonoidHom.map_isConj H.subtype h2)
    · exact h
  refine fus_of_classes hzH hxH hz2 hx2 hzx hcl ?_
  intro ū hū
  have hūJ := hinv ū hū
  rcases hJcl ⟨ū, hūJ⟩ (by rw [← Subgroup.orderOf_coe]; exact hū) with h | h
  · left
    exact (toX h).symm
  · right
    exact (toX (h.symm.trans hxy))

theorem g2_one_class {M : Type} [Group M] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hM : LieModel M .G2 0 p f) : ∀ a b : M, orderOf a = 2 → orderOf b = 2 → IsConj a b := by
  obtain ⟨F, hF, hFin, hcard, ⟨φ⟩⟩ := Ivk47ab.exists_equiv_of_lieModel hM
  have hodd : Odd (Nat.card F) := Ivk47ab.odd_card_of_model hp hp2 hcard
  have hchar : ringChar F ≠ 2 := CFSG.ABGLocalTools.ringChar_ne_two_of_odd_card hodd
  intro a b ha hb
  exact Ivk47ab.isConj_of_equiv φ
    (CFSG.LieType.HighestRoot.g2_involutions_isConj hchar (φ a) (φ b)
      (by rw [MulEquiv.orderOf_eq]; exact ha) (by rw [MulEquiv.orderOf_eq]; exact hb))

end CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt
