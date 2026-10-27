module

public import CFSG.LocalAnalysis.ComponentInitial.KProperPumpUpStatement
public import CFSG.LocalAnalysis.ComponentInitial.GroupCentralQuotient
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBLocalB
public import CFSG.LocalAnalysis.ComponentInitial.KProperSubgroup
public import CFSG.LocalAnalysis.ComponentInitial.EscapingBlockQuotient

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification

variable {G : Type} [Group G]

theorem isComponentOf_subgroupOf_centralizer {H J : Subgroup G} (hJH : J ≤ H) (a : H)
    (hJ : CFSG.Assembly.IsComponentOf J (centralizer ({(a : G)} : Set G))) :
    CFSG.Assembly.IsComponentOf (J.subgroupOf H) (centralizer ({a} : Set H)) := by
  rw [← isComponentOf_map_iff H.subtype_injective, map_subgroupOf_eq_of_le hJH,
    map_subtype_centralizer_singleton]
  exact isComponentOf_of_le hJ (le_inf hJH hJ.1) inf_le_right

theorem isComponentOf_map_subtype_top {H : Subgroup G} {L : Subgroup H}
    (hL : CFSG.Assembly.IsComponentOf L ⊤) : CFSG.Assembly.IsComponentOf (L.map H.subtype) H := by
  have h := (isComponentOf_map_iff H.subtype_injective).2 hL
  rwa [← MonoidHom.range_eq_map, range_subtype] at h

theorem isComponentOf_of_subgroupOf_top {H J : Subgroup G} (hJH : J ≤ H)
    (hJ : CFSG.Assembly.IsComponentOf (J.subgroupOf H) ⊤) : CFSG.Assembly.IsComponentOf J H := by
  have h := isComponentOf_map_subtype_top hJ
  rwa [map_subgroupOf_eq_of_le hJH] at h

theorem conjSub_eq_self_of_mem_centralizer {g : G} {K : Subgroup G}
    (hg : g ∈ centralizer (K : Set G)) : conjSub g K = K :=
  conjSub_eq_of_mem_normalizer (centralizer_le_normalizer K hg)

theorem isElementaryAbelian_subgroupOf {H U : Subgroup G}
    (hU : CFSG.Assembly.IsElemAbelian 2 U) : CFSG.IsElementaryAbelian 2 (U.subgroupOf H) := by
  have hc : ∀ u ∈ U, ∀ w ∈ U, u * w = w * u := fun u hu w hw =>
    congrArg Subtype.val (hU.1.is_comm.comm ⟨u, hu⟩ ⟨w, hw⟩)
  exact { toIsMulCommutative := ⟨⟨fun x y => Subtype.ext (Subtype.ext (hc _ x.2 _ y.2))⟩⟩
          exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
            Subtype.ext (Subtype.ext (hU.2 _ x.2)) }

theorem known_four_group_eliminates_diagonal_pump {C : CFSG.Assembly.GroupProp}
    (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X)
    (hpump : KProperOrdinaryLocalBPumpUp C) [Finite G] (hK : CFSG.Assembly.KProper C G)
    (hB : CFSG.Assembly.ComponentType.LocalBProperty G) {J U : Subgroup G}
    (hUJ : U ≤ centralizer (J : Set G)) (hU : CFSG.Assembly.IsElemAbelian 2 U)
    (hUcard : Nat.card U = 4)
    (hJU : ∀ u ∈ U, u ≠ 1 → CFSG.Assembly.IsComponentOf J (centralizer ({u} : Set G)))
    (hmax : ∀ s : G, orderOf s = 2 → ∀ Q : Subgroup G,
      CFSG.Assembly.IsComponentOf Q (centralizer ({s} : Set G)) →
        (center Q).index ≤ (center J).index)
    {t : G} (htJ : t ∈ centralizer (J : Set G)) (ht : orderOf t = 2)
    (htU : U ≤ centralizer ({t} : Set G)) :
    CFSG.Assembly.IsComponentOf J (centralizer ({t} : Set G)) := by
  obtain ⟨a, haU, ha1⟩ : ∃ a ∈ U, a ≠ 1 := by
    rcases U.bot_or_exists_ne_one with hbot | h
    · rw [hbot, card_bot] at hUcard
      norm_num at hUcard
    · exact h
  have ha2 : orderOf a = 2 := orderOf_eq_prime (hU.2 a haU) ha1
  set H := centralizer ({t} : Set G) with hHdef
  have hJH : J ≤ H := fun x hx => by
    rw [mem_centralizer_singleton_iff]
    exact mem_centralizer_iff.1 htJ x hx
  let a' : H := ⟨a, htU haU⟩
  have ha'2 : orderOf a' = 2 := by rw [← Subgroup.orderOf_coe]; exact ha2
  have hKH : CFSG.Assembly.KProper C H := kProper_subgroup hC hK H
  have hBH : ∀ Q : Subgroup H, CFSG.Assembly.ComponentType.IsTwoPComponent Q →
      CFSG.Assembly.IsComponentOf Q ⊤ :=
    fun Q hQ => AssemblyBLocalB.ordinary_at_involution hB t ht Q hQ
  have hJa' := isComponentOf_subgroupOf_centralizer hJH a' (hJU a haU ha1)
  obtain ⟨-, L, hL, hcase⟩ := hpump H hKH hBH a' ha'2 (J.subgroupOf H) hJa'
  have hLtop : CFSG.Assembly.IsComponentOf L ⊤ :=
    (AssemblyBPredicates.isComponentOf_top_iff_native L).2 hL
  rcases hcase with ⟨-, hJL⟩ | ⟨hLa, hJset, -, -⟩
  ·
    have hJ'L : J.subgroupOf H ≤ L := hJL.1.trans inf_le_left
    rcases eq_or_lt_of_le hJ'L with heq | hlt
    · apply isComponentOf_of_subgroupOf_top hJH
      rw [heq]
      exact hLtop
    · exfalso
      have : Group.IsPerfect L := hL.1.1
      have hlt' := index_center_lt_of_lt hlt
      have hle := hmax t ht (L.map H.subtype) (isComponentOf_map_subtype_top hLtop)
      rw [index_center_eq_of_mulEquiv (subgroupOfEquivOfLe hJH),
        index_center_eq_of_mulEquiv (L.equivMapOfInjective H.subtype H.subtype_injective)] at hlt'
      omega
  ·
    exfalso
    obtain ⟨hJdiag, -, -, ⟨haCJ, -, -, -⟩, -, -, -, -, -, -, -, hA⟩ :=
      diagonal_component_centralizer_index_two hL hLa ha'2
    set hAB := commutator_conjSub_eq_bot hL hLa
    have hJeq : J.subgroupOf H = (swapDiag hAB).range := SetLike.ext' (hJset.trans hJdiag.symm)
    set U' : Subgroup H := U.subgroupOf H with hU'def
    have hU'card : Nat.card U' = 4 := by
      rw [← hUcard]
      exact Nat.card_congr (subgroupOfEquivOfLe htU).toEquiv
    have hU'CJ : U' ≤ centralizer (((swapDiag hAB).range : Subgroup H) : Set H) := by
      rw [← hJeq]
      intro u hu
      rw [mem_centralizer_iff]
      intro x hx
      exact Subtype.ext (mem_centralizer_iff.1 (hUJ hu) x hx)
    have ha'U' : a' ∈ U' := haU
    obtain ⟨hindex, -⟩ := hA U' hU'CJ (isElementaryAbelian_subgroupOf hU) ha'U'
    set CM := centralizer ((L ⊔ conjSub a'⁻¹ L : Subgroup H) : Set H)
    have hcard2 : Nat.card ↥(U' ⊓ CM) = 2 := by
      have h := relIndex_mul_card (U' ⊓ CM) U'
      rw [hindex, inf_right_comm, inf_idem, hU'card] at h
      omega
    obtain ⟨v, hv, hv1⟩ := (U' ⊓ CM).bot_or_exists_ne_one.resolve_left fun hbot => by
      rw [hbot, card_bot] at hcard2
      norm_num at hcard2
    have hvU : (v : G) ∈ U := (mem_inf.1 hv).1
    have hv1G : (v : G) ≠ 1 := fun h => hv1 (Subtype.ext h)
    have hJv := isComponentOf_subgroupOf_centralizer hJH v (hJU (v : G) hvU hv1G)
    have hLv : L ≤ centralizer ({v} : Set H) := fun x hx => by
      rw [mem_centralizer_singleton_iff]
      exact mem_centralizer_iff.1 (mem_inf.1 hv).2 x (mem_sup_left hx)
    have hLv' : CFSG.Assembly.IsComponentOf L (centralizer ({v} : Set H)) :=
      isComponentOf_of_le hLtop hLv le_top
    rcases isComponentOf_eq_or_commute hJv hLv' with heq | hcomm
    ·
      apply hLa
      rw [← heq, hJeq]
      exact conjSub_eq_self_of_mem_centralizer (inv_mem haCJ)
    ·
      apply not_le_centralizer_self_of_isQuasisimple (assembly_isQuasisimple_of_isComponent hL)
      intro y hy
      rw [mem_centralizer_iff]
      intro x hx
      have hdiag : x * (a'⁻¹ * x * a') ∈ J.subgroupOf H := by
        rw [← SetLike.mem_coe, hJset]
        exact ⟨x, hx, rfl⟩
      have h1 := commute_of_commutator_eq_bot hcomm hdiag hy
      have h2 := commute_of_commutator_conj_eq_bot hAB hy (conj_mem_conjSub (t := a') hx)
      have h3 : x * y * (a'⁻¹ * x * a') = y * x * (a'⁻¹ * x * a') := by
        calc x * y * (a'⁻¹ * x * a') = x * (y * (a'⁻¹ * x * a')) := by group
          _ = x * ((a'⁻¹ * x * a') * y) := by rw [h2]
          _ = x * (a'⁻¹ * x * a') * y := by group
          _ = y * (x * (a'⁻¹ * x * a')) := h1
          _ = y * x * (a'⁻¹ * x * a') := by group
      exact mul_right_cancel h3

end CFSG.LocalAnalysis.ComponentInitial
