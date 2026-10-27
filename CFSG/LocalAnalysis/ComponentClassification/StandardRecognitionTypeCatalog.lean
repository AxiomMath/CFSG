module

public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.ComponentClassification.StandardRecognition

theorem exists_mul_ne_mul_of_isQuasisimple {L : Type*} [Group L] (hL : Assembly.IsQuasisimple L) :
    ∃ a b : L ⧸ Subgroup.center L, a * b ≠ b * a := by
  have : Group.IsPerfect L := ⟨hL.1⟩
  have : IsSimpleGroup (L ⧸ Subgroup.center L) := hL.2
  simpa only [isMulCommutative_iff, not_forall] using
    Group.IsPerfect.not_isMulCommutative (L ⧸ Subgroup.center L)

theorem inCatalog_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : Assembly.InCatalog Y) : Assembly.InCatalog X :=
  CFSG.Assembly.inCatalog_isoInvariant e h

theorem quasisimple_quotient_inCatalog (G : Type) [Group G]
    (hK : Assembly.KProper Assembly.InCatalog G) (L : Subgroup G) (hLG : L < ⊤)
    (hL : Assembly.IsQuasisimple L) : Assembly.InCatalog (L ⧸ Subgroup.center L) := by
  have hNc : ((Subgroup.center L).map L.subtype).subgroupOf L = Subgroup.center L :=
    Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  have : (((Subgroup.center L).map L.subtype).subgroupOf L).Normal := by
    rw [hNc]
    infer_instance
  let e : (L ⧸ Subgroup.center L) ≃* (L ⧸ ((Subgroup.center L).map L.subtype).subgroupOf L) :=
    QuotientGroup.quotientMulEquivOfEq hNc.symm
  have : IsSimpleGroup (L ⧸ Subgroup.center L) := hL.2
  obtain ⟨a, b, hab⟩ := exists_mul_ne_mul_of_isQuasisimple hL
  refine inCatalog_of_mulEquiv e (hK L _ hLG.ne (Subgroup.map_subtype_le _) e.symm.isSimpleGroup
    ⟨e a, e b, ?_⟩)
  rwa [← map_mul, ← map_mul, ne_eq, e.injective.eq_iff]

theorem center_eq_bot_of_isSimpleGroup {G : Type*} [Group G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) : Subgroup.center G = ⊥ := by
  refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G)).resolve_right
    fun htop => ?_
  obtain ⟨a, b, hab⟩ := hnonab
  have ha : a ∈ Subgroup.center G := htop ▸ Subgroup.mem_top a
  exact hab (Subgroup.mem_center_iff.1 ha b).symm

theorem standard_quotient_inCatalog (G : Type) [Group G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : Assembly.KProper Assembly.InCatalog G)
    (L : Subgroup G) (hL : Assembly.ComponentType.IsStandardSubgroup L) :
    L < ⊤ ∧ Assembly.InCatalog (L ⧸ Subgroup.center L) := by
  have hLG : L < ⊤ := by
    refine lt_top_iff_ne_top.2 fun htop => ?_
    have heven : Even (Nat.card (Subgroup.centralizer (L : Set G))) := hL.2.1
    rw [htop, Subgroup.coe_top, Subgroup.centralizer_univ, center_eq_bot_of_isSimpleGroup hnonab,
      Subgroup.card_bot] at heven
    exact Nat.not_even_one heven
  exact ⟨hLG, quasisimple_quotient_inCatalog G hK L hLG hL.1⟩

end CFSG.ComponentClassification.StandardRecognition
