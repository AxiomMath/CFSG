module

public import CFSG.LocalAnalysis.ComponentInitial.KProperPumpUpStatement
public import CFSG.LocalAnalysis.ComponentInitial.KProperSubgroup
public import CFSG.LocalAnalysis.ComponentInitial.GroupCentralQuotient
public import CFSG.LocalAnalysis.ComponentInitial.EscapingNotAlternating
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBLocalB

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification

theorem split_central_involution_prevents_second_diagonal {C : CFSG.Assembly.GroupProp}
    (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X)
    (hpump : KProperOrdinaryLocalBPumpUp C) {G : Type} [Group G] [Finite G]
    (hK : CFSG.Assembly.KProper C G)
    (hB : CFSG.Assembly.ComponentType.LocalBProperty G) {a z : G} (_ha : orderOf a = 2)
    (hz : orderOf z = 2) (haz : a * z = z * a) {L : Subgroup G}
    (hL : CFSG.Assembly.IsComponentOf L (centralizer ({z} : Set G))) (hLa : conjSub a⁻¹ L ≠ L)
    {c : G} (hcL : c ∈ L) (hcZ : c ∈ centralizer (L : Set G)) (hc : orderOf c = 2)
    (hzc : z = c * (a⁻¹ * c * a))
    (hmax : ∀ t : G, orderOf t = 2 → ∀ Q : Subgroup G,
      CFSG.Assembly.IsComponentOf Q (centralizer ({t} : Set G)) →
        (center Q).index ≤ (center L).index) :
    CFSG.Assembly.IsComponentOf L (centralizer ({c} : Set G)) := by
  set H := centralizer ({c} : Set G) with hHdef
  set La := conjSub a⁻¹ L with hLadef
  have hza : a⁻¹ * z * a⁻¹⁻¹ = z := by
    rw [inv_inv, mul_assoc, ← haz, ← mul_assoc, inv_mul_cancel, one_mul]
  have hLaC : CFSG.Assembly.IsComponentOf La (centralizer ({z} : Set G)) := by
    have := isComponentOf_map_conj hL a⁻¹
    rwa [map_conj_centralizer_singleton, hza] at this
  have hLaCL : La ≤ centralizer (L : Set G) :=
    commutator_eq_bot_iff_le_centralizer.1 ((isComponentOf_eq_or_commute hLaC hL).resolve_left hLa)
  have hLH : L ≤ H := fun x hx => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hcZ x hx)
  have hLaH : La ≤ H := fun y hy =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 (hLaCL hy) c hcL).symm
  have hcaLa : a⁻¹ * c * a ∈ La := ⟨c, hcL, by simp⟩
  have hcca : c * (a⁻¹ * c * a) = (a⁻¹ * c * a) * c := mem_centralizer_iff.1 (hLaCL hcaLa) c hcL
  have hzH : z ∈ H := by
    rw [mem_centralizer_singleton_iff, hzc, mul_assoc, ← hcca]
  have hKH : CFSG.Assembly.KProper C H := kProper_subgroup hC hK H
  have hlocB : ∀ Q : Subgroup H, CFSG.Assembly.ComponentType.IsTwoPComponent Q →
      CFSG.Assembly.IsComponentOf Q ⊤ := fun Q hQ =>
    AssemblyBLocalB.ordinary_at_involution hB c hc Q hQ
  set t : H := ⟨z, hzH⟩ with htdef
  have ht : orderOf t = 2 := by rw [Subgroup.orderOf_mk]; exact hz
  have hJ' : CFSG.Assembly.IsComponentOf (L.subgroupOf H) (centralizer ({t} : Set H)) := by
    rw [← isComponentOf_map_iff H.subtype_injective, map_centralizer_singleton_of_injective
      H.subtype_injective, Subgroup.range_subtype, Subgroup.map_subgroupOf_eq_of_le hLH]
    exact isComponentOf_of_le hL (le_inf hLH hL.1) inf_le_right
  obtain ⟨-, M, hM, hcase⟩ := hpump H hKH hlocB t ht _ hJ'
  have hMG : CFSG.Assembly.IsComponentOf (M.map H.subtype) H := by
    have h := (isComponentOf_map_iff H.subtype_injective (Q := M) (K := ⊤)).2
      ((AssemblyBPredicates.isComponentOf_top_iff_native M).2 hM)
    rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  rcases hcase with ⟨-, hJM⟩ | ⟨hMt, hJset, -, -⟩
  ·
    have hJle : L.subgroupOf H ≤ M := hJM.1.trans inf_le_left
    rcases hJle.lt_or_eq with hlt | heq
    · exfalso
      have : Group.IsPerfect M := hM.1.1
      have h1 := index_center_lt_of_lt hlt
      have h2 := hmax c hc _ hMG
      rw [index_center_eq_of_mulEquiv (M.equivMapOfInjective H.subtype H.subtype_injective),
        index_center_eq_of_mulEquiv (subgroupOfEquivOfLe hLH)] at h1
      omega
    · have h := (isComponentOf_map_iff H.subtype_injective (Q := L.subgroupOf H) (K := ⊤)).2
        ((AssemblyBPredicates.isComponentOf_top_iff_native _).2 (heq ▸ hM))
      rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype,
        Subgroup.map_subgroupOf_eq_of_le hLH] at h
  ·
    exfalso
    obtain ⟨hJdiag, -, -, -, -, hCMnorm, -, -, hrel, -, -, -⟩ :=
      diagonal_component_centralizer_index_two hM hMt ht
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    set Jd := (swapDiag (commutator_conjSub_eq_bot hM hMt)).range with hJd
    have hJeq : Jd = L.subgroupOf H := SetLike.ext' (hJdiag.trans hJset.symm)
    set CJ := centralizer (Jd : Set H) with hCJ
    set CM := centralizer ((M ⊔ conjSub t⁻¹ M : Subgroup H) : Set H) with hCM
    have hKCJ : La.subgroupOf H ≤ CJ := by
      intro y hy
      rw [mem_centralizer_iff]
      intro x hx
      rw [hJeq] at hx
      exact Subtype.ext (mem_centralizer_iff.1 (hLaCL hy) x hx)
    have hKCM : La.subgroupOf H ≤ CM := by
      have : Group.IsPerfect La := ⟨hLaC.2.2.1⟩
      let K'' := (La.subgroupOf H).subgroupOf CJ
      let e : La ≃* K'' := (subgroupOfEquivOfLe hLaH).symm.trans (subgroupOfEquivOfLe hKCJ).symm
      have : Group.IsPerfect K'' := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
      have hcard : Nat.card (CJ ⧸ CM.subgroupOf CJ) = 2 := hrel
      let : IsCyclic (CJ ⧸ CM.subgroupOf CJ) := isCyclic_of_prime_card hcard
      let q : K'' →* CJ ⧸ CM.subgroupOf CJ := (QuotientGroup.mk' _).comp K''.subtype
      have hker : q.ker = ⊤ := by
        apply top_unique
        rw [← Group.IsPerfect.commutator_eq_top (G := K'')]
        exact Abelianization.commutator_subset_ker q
      intro y hy
      have hy' : (⟨y, hKCJ hy⟩ : CJ) ∈ CM.subgroupOf CJ := by
        apply (QuotientGroup.eq_one_iff _).mp
        exact MonoidHom.mem_ker.mp (show (⟨⟨y, hKCJ hy⟩, hy⟩ : K'') ∈ q.ker by rw [hker]; trivial)
      exact hy'
    have hcaCM : (⟨a⁻¹ * c * a, hLaH hcaLa⟩ : H) ∈ CM := hKCM hcaLa
    have hcCM : (⟨c, mem_centralizer_singleton_iff.2 rfl⟩ : H) ∈ CM := by
      rw [mem_centralizer_iff]
      intro x _
      exact Subtype.ext (mem_centralizer_singleton_iff.1 x.2)
    have htCM : t ∈ CM := by
      have := CM.mul_mem hcCM hcaCM
      convert this using 1
      exact Subtype.ext hzc
    have htM : t ∈ centralizer (M : Set H) :=
      Subgroup.centralizer_le (le_sup_left : M ≤ M ⊔ conjSub t⁻¹ M) htCM
    exact hMt (conjSub_eq_of_mem_normalizer (centralizer_le_normalizer _ (inv_mem htM)))

end CFSG.LocalAnalysis.ComponentInitial
