module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.Statement

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

theorem range_eq_zpowers_sup_map {Q G : Type*} [Group Q] [Group G] (φ : Q →* G)
    {J : Subgroup Q} {q : Q} (hJ : J ⊔ Subgroup.zpowers q = ⊤) :
    φ.range = Subgroup.zpowers (φ q) ⊔ J.map φ := by
  rw [MonoidHom.range_eq_map, ← hJ, Subgroup.map_sup, MonoidHom.map_zpowers, sup_comm]

theorem index_ne_two_of_four_dvd {G : Type*} [Group G] [IsSimpleGroup G]
    (h4 : 4 ∣ Nat.card G) (H : Subgroup G) : H.index ≠ 2 := by
  intro hH
  have : H.Normal := Subgroup.normal_of_index_eq_two hH
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H with rfl | rfl
  · rw [Subgroup.index_bot] at hH
    omega
  · rw [Subgroup.index_top] at hH
    omega

theorem hasAbelianSylowTwo_of_comm {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hS : ∀ a ∈ (S : Subgroup G), ∀ b ∈ (S : Subgroup G), a * b = b * a) :
    CFSG.Walter.HasAbelianSylowTwo G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsMulCommutative (S : Subgroup G) := ⟨⟨fun a b => Subtype.ext (hS a a.2 b b.2)⟩⟩
  intro P
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G S P
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
  exact Subgroup.map_isMulCommutative _ _

section Lift

variable {G : Type} [Group G] {z : G}

def escapingLift (hO : pPrimeCore 2 (Subgroup.centralizer ({z} : Set G)) = ⊥) :
    EscapingQuotient z →* G :=
  QuotientGroup.lift _ (Subgroup.centralizer ({z} : Set G)).subtype (by rw [hO]; exact bot_le)

variable (hO : pPrimeCore 2 (Subgroup.centralizer ({z} : Set G)) = ⊥)

theorem escapingLift_mk (c : Subgroup.centralizer ({z} : Set G)) :
    escapingLift hO (escapingMk z c) = c :=
  QuotientGroup.lift_mk _ _ c

theorem escapingLift_bar : escapingLift hO (escapingBar z) = z :=
  escapingLift_mk hO _

theorem escapingLift_injective : Function.Injective (escapingLift hO) := by
  rw [← MonoidHom.ker_eq_bot_iff, escapingLift, QuotientGroup.ker_lift, Subgroup.ker_subtype,
    Subgroup.map_bot]

theorem range_escapingLift :
    (escapingLift hO).range = Subgroup.centralizer ({z} : Set G) := by
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective _ q
    exact c.2
  · intro hx
    exact ⟨escapingMk z ⟨x, hx⟩, rfl⟩

end Lift

theorem jankoConfigurationJanko : JankoConfigurationJanko := by
  intro G _ _ S z _ hz hconf hO
  obtain ⟨J, -, ⟨e⟩, hzJ, hJ⟩ := hconf.quotient
  have h4 : 4 ∣ Nat.card G :=
    (by rw [hconf.card]; norm_num : 4 ∣ Nat.card (S : Subgroup G)).trans
      (Subgroup.card_subgroup_dvd_card _)
  have hinj := escapingLift_injective hO
  have hnot : z ∉ J.map (escapingLift hO) := fun h => by
    apply hzJ
    rwa [← Subgroup.mem_map_iff_mem hinj, escapingLift_bar]
  have hC : Subgroup.centralizer ({z} : Set G) =
      Subgroup.zpowers z ⊔ J.map (escapingLift hO) := by
    refine (range_escapingLift hO).symm.trans ?_
    rw [range_eq_zpowers_sup_map _ hJ, escapingLift_bar]
  exact ⟨{
    index_ne_two := index_ne_two_of_four_dvd h4
    abelian_sylow := hasAbelianSylowTwo_of_comm S hconf.abelian
    t := z
    orderOf_t := hz.2.1
    F := J.map (escapingLift hO)
    le_centralizer := (Subgroup.map_le_range _ J).trans (range_escapingLift hO).le
    t_not_mem := hnot
    centralizer_eq := hC
    iso := (Subgroup.equivMapOfInjective J _ hinj).symm.trans e }⟩

end CFSG.ProperTwoGeneratedCore.Lemma37
