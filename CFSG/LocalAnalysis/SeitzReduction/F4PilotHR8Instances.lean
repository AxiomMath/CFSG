module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR8
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotOuterFusion
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR7Nonsplit

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

section General

variable {G : Type*} [Group G]

theorem centralizer_ne_top_of_ne_bot (hG : IsSimpleGroup G) (hnonab : ∃ a b : G, a * b ≠ b * a)
    {X : Subgroup G} (hX : X ≠ ⊥) : centralizer (X : Set G) ≠ ⊤ := by
  intro htop
  obtain ⟨a, b, hab⟩ := hnonab
  apply hX
  rcases hG.eq_bot_or_eq_top_of_normal (center G) with hZ | hZ
  · rw [eq_bot_iff, ← hZ]
    intro x hx
    rw [mem_center_iff]
    intro g
    exact (mem_centralizer_iff.mp (htop ▸ mem_top g) x hx).symm
  · exact absurd (mem_center_iff.mp (hZ ▸ mem_top b) a) hab

variable {C : Type*} [Group C] {L : Subgroup G}

theorem map_map_symm_ne_bot (e : L ≃* C) {A : Subgroup C} (hA : A ≠ ⊥) :
    (A.map e.symm.toMonoidHom).map L.subtype ≠ ⊥ := by
  rw [Ne, map_eq_bot_iff_of_injective _ L.subtype_injective,
    map_eq_bot_iff_of_injective _ e.symm.injective]
  exact hA

theorem map_map_symm_le_centralizer (e : L ≃* C) {A B : Subgroup C}
    (h : A ≤ centralizer (B : Set C)) :
    (B.map e.symm.toMonoidHom).map L.subtype ≤
      centralizer (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G) :=
  le_centralizer_iff.mp (map_le_centralizer_map _ (map_le_centralizer_map _ h))

end General

section F4

variable {K : Type} [Field K]

theorem rootDiagUnit_rDiag_ne_one [CharP K 2] {c : Kˣ} (hc : c ≠ 1) :
    (⟨rootDiagUnit .F4 (rDiag c), f4RootDiagUnit_mem_adjointGroup _⟩ : adjointGroup .F4 K) ≠ 1 := by
  intro h
  have h1 : rootDiagUnit .F4 (rDiag c) = 1 := congrArg Subtype.val h
  exact hc (eq_one_of_commute_pinnedX_rootR (ringChar.eq K 2)
    (by rw [h1]; exact Commute.one_left _))

theorem lieModel_map_map_C3Levi {G : Type} [Group G] {L : Subgroup G} {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .F4 K) :
    CFSG.Blueprint.LieModel (((C3Levi K).map e.symm.toMonoidHom).map L.subtype) .PSp 3 2 f :=
  LieType.CurtisTits.lieModel_of_mulEquiv
    (((C3Levi K).equivMapOfInjective e.symm.toMonoidHom e.symm.injective).trans
      (((C3Levi K).map e.symm.toMonoidHom).equivMapOfInjective L.subtype L.subtype_injective))
    (lieModel_C3Levi hK)

theorem neighbour_overgroup_nonsplit_of_not_normal (hcat : Sp6CatalogueClauses) {G : Type}
    [Group G] [Finite G] {L : Subgroup G} (hset : StandardSetting G L) {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .F4 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ₀ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X₀)
    (hX₀ : Nat.card X₀ = Nat.card K + 1)
    {X : Subgroup G} (hX : X = (X₀.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((C3Levi K).map e.symm.toMonoidHom).map L.subtype)
    (hnn : ¬ ((D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal) :
    NeighbourOvergroup (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) f := by
  have := finite_of_natCard_eq_two_pow hK
  have := charP_two_of_natCard_eq_two_pow hK
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  obtain ⟨hcomp, hsyl, hstd⟩ :=
    neighbour_standard_nonsplit hset.standard htK.1 ht hKt hK e hXJ₀ hcyc hX₀ hX htX hDe
  obtain ⟨-, -, hXD⟩ := centralizer_nonsplit hXJ₀ hcyc hX₀
  have hDX : D ≤ centralizer (X : Set G) := by
    rw [hX, hDe]
    exact map_map_symm_le_centralizer e hXD
  have hX₀ne : X₀ ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hX₀
    have : 0 < Nat.card K := by rw [hK]; positivity
    omega
  have hXG : centralizer (X : Set G) ≠ ⊤ :=
    centralizer_ne_top_of_ne_bot hset.simple hset.nonab (hX ▸ map_map_symm_ne_bot e hX₀ne)
  exact neighbour_overgroup hcat hset.kProper hXG htX ht hDX (hDe ▸ lieModel_map_map_C3Levi hK e)
    hcomp hsyl hstd hnn

theorem neighbour_overgroup_torusLineR (hcat : Sp6CatalogueClauses) {G : Type} [Group G]
    [Finite G] {L : Subgroup G} (hset : StandardSetting G L) {f : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .F4 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {X : Subgroup G} (hX : X = (((torusLineR K).subgroupOf (adjointGroup .F4 K)).map
      e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((C3Levi K).map e.symm.toMonoidHom).map L.subtype) :
    NeighbourOvergroup (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) f := by
  have := finite_of_natCard_eq_two_pow hK
  have := charP_two_of_natCard_eq_two_pow hK
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  obtain ⟨hcomp, hsyl, hstd⟩ :=
    neighbour_standard_torusLineR hset.standard htK.1 ht hKt hf hK e hX htX hDe
  have hnn := not_normal_map_oddCore_torusLineR_of_two_le hset hf hK e ht hKt hX hDe
  have hDX : D ≤ centralizer (X : Set G) := by
    rw [hX, hDe]
    exact map_map_symm_le_centralizer e torusLineR_subgroupOf_le_centralizer
  have hq : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨c, hc⟩ := exists_three_le_orderOf hq
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hc
    omega
  have hTne : (torusLineR K).subgroupOf (adjointGroup .F4 K) ≠ ⊥ := by
    intro h
    have hmem : (⟨rootDiagUnit .F4 (rDiag c), f4RootDiagUnit_mem_adjointGroup _⟩ :
        adjointGroup .F4 K) ∈ (torusLineR K).subgroupOf (adjointGroup .F4 K) :=
      mem_subgroupOf.2 ⟨c, rfl⟩
    rw [h, mem_bot] at hmem
    exact rootDiagUnit_rDiag_ne_one hc1 hmem
  have hXG : centralizer (X : Set G) ≠ ⊤ :=
    centralizer_ne_top_of_ne_bot hset.simple hset.nonab (hX ▸ map_map_symm_ne_bot e hTne)
  exact neighbour_overgroup hcat hset.kProper hXG htX ht hDX (hDe ▸ lieModel_map_map_C3Levi hK e)
    hcomp hsyl hstd hnn

end F4

end CFSG.SeitzReduction.F4Pilot
