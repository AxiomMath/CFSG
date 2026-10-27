module

public import CFSG.ClassicalInvolution.Q3.Q3ExIntr
public import CFSG.ClassicalInvolution.Q3.Q3DBFuzzy
public import CFSG.ClassicalInvolution.Q3.Q3UBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3NH

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3.Q3DB
open scoped commutatorElement

section Members

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}

theorem oddCoreIn_eq_centralizer_of_mem_conjClass3 (hz : IsClassicalMember3 K z)
    (hint : oddCoreIn (Subgroup.centralizer ({z} : Set G)) ≤ K) {β : Subgroup G} {t : G}
    (hβ : β ∈ conjClass3 K) (ht : IsClassicalMember3 β t) :
    oddCoreIn β = oddCoreIn (Subgroup.centralizer ({t} : Set G)) :=
  Uniform.oddCoreIn_eq_of_intrinsic (IsClassicalMemberU.ofQ3 ht)
    (oddCoreIn_centralizer_le_of_mem_conjClass3 hz hint hβ ht)

variable [IsSimpleGroup G]

end Members

section DEdge

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}

theorem exactMembers3_of_alphaDEdge (hnab : ∃ a b : G, a * b ≠ b * a)
    (hz : IsClassicalMember3 K z) (hint : oddCoreIn (Subgroup.centralizer ({z} : Set G)) ≤ K)
    (hBelow : CIT3Below (Nat.card G)) {M N : Subgroup G} {a t : G}
    (hN : N ∈ omegaNbr (conjClass3 K) M) (ha : IsClassicalMember3 M a)
    (ht : IsClassicalMember3 N t) (hα : alphaCore (Subgroup.closure ({a, t} : Set G)) = ⊥) :
    ExactMembers3 (conjClass3 K) := by
  have hNΩ : N ∈ conjClass3 K := hN.1
  have hΩ : InClass3 (conjClass3 K) := inClass3_conjugates hz
  have hLoc : LocalLieSystems3 (conjClass3 K) := localLieSystems3_of_cit3Below hΩ hBelow
  have hact : ActsTrivOnQuot N a := actsTrivOnQuot_of_mem_omegaNbr hz (fun _ => hint) hN ha
  have hcN : a ∈ trivialOnQuot N := mem_trivialOnQuot_iff_actsTrivOnQuot.mpr hact
  have ha2 : IsPGroup 2 (Subgroup.zpowers a) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, ha.orderOf_eq_two]
    norm_num
  set V : Subgroup G := Subgroup.closure ({a, t} : Set G) with hV
  have haV : a ∈ V := Subgroup.subset_closure (by simp)
  have htV : t ∈ V := Subgroup.subset_closure (by simp)
  have hcom : ⁅uCore V, V⁆ = ⊥ := le_bot_iff.mp (commutator_le_alphaCore.trans hα.le)
  have hδ : deltaCore V = ⊥ := le_bot_iff.mp (deltaCore_le_alphaCore.trans hα.le)
  have hOa : ∀ x ∈ oddCoreIn N, a * x = x * a := by
    intro x hx
    have hx' : x ∈ involutionOddCore t := by
      have h0 : x ∈ oddCoreIn (Subgroup.centralizer ({t} : Set G)) :=
        (oddCoreIn_eq_centralizer_of_mem_conjClass3 hz hint hNΩ ht) ▸ hx
      exact h0
    have hxU : x ∈ uCore V := involutionOddCore_le_uCore htV ht.ne_one hx'
    have h1 : ⁅x, a⁆ ∈ ⁅uCore V, V⁆ := Subgroup.commutator_mem_commutator hxU haV
    rw [hcom, Subgroup.mem_bot] at h1
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  have hNa : N ≤ Subgroup.centralizer ({a} : Set G) := by
    intro y hy
    obtain ⟨i, hi, n, hn, rfl⟩ := exactCore3_cover ht ha2 hcN y hy
    have hia : i * a = a * i :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hi).2
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc i * n * a = i * (n * a) := by group
      _ = i * (a * n) := by rw [hOa n hn]
      _ = (i * a) * n := by group
      _ = (a * i) * n := by rw [hia]
      _ = a * (i * n) := by group
  have hNt : ∀ y ∈ N, y * t = t * y := fun y hy => ht.commute_involution hy
  have hVN : V ≤ Subgroup.centralizer (N : Set G) := by
    rw [hV, Subgroup.closure_le]
    intro f hf
    rcases hf with rfl | rfl
    · exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
        Subgroup.mem_centralizer_singleton_iff.mp (hNa hy)
    · exact Subgroup.mem_centralizer_iff.mpr hNt
  have hNV : N ≤ Subgroup.centralizer (V : Set G) := Subgroup.le_centralizer_iff.mp hVN
  have hnc : ∀ f ∈ V, f ≠ 1 → f ∉ Subgroup.center G := fun f _ hf1 hmem =>
    Q3W.not_subset_center_of_ne_one hnab hf1 (Set.singleton_subset_iff.mpr hmem)
  refine Q3.exactMembers3_of_deltaCore_eq_bot hΩ.conjInvariant hLoc hNΩ ht hNV hnc hδ ?_
  obtain ⟨g₀, hg₀⟩ := hNΩ
  have hg₀' : conjSub g₀ K = N := hg₀
  intro L hL
  obtain ⟨g, hg⟩ := hL
  have hg' : conjSub g K = L := hg
  exact ⟨g * g₀⁻¹, by rw [← hg', ← hg₀', ← conjSub_mul, mul_assoc, inv_mul_cancel, mul_one]⟩

theorem exists_dEdge_distinct (hnab : ∃ a b : G, a * b ≠ b * a) (hz : IsClassicalMember3 K z)
    (hD : DConnected (conjClass3 K)) :
    ∃ (M N : Subgroup G) (a t : G), M ∈ conjClass3 K ∧ N ∈ omegaNbr (conjClass3 K) M ∧
      IsClassicalMember3 M a ∧ IsClassicalMember3 N t ∧ a ≠ t := by
  by_contra hcon
  push Not at hcon
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hall : ∀ L, Relation.ReflTransGen
      (fun M N : Subgroup G => N ∈ conjClass3 K ∧ dAdj (conjClass3 K) M N) K L →
      L ∈ conjClass3 K ∧ IsClassicalMember3 L z := by
    intro L hL
    induction hL with
    | refl => exact ⟨hK, hz⟩
    | @tail b c _ hbc ih =>
      obtain ⟨hcΩ, hadj⟩ := hbc
      obtain ⟨g, hg⟩ := hcΩ
      have hcg : conjSub g K = c := hg
      have hc : IsClassicalMember3 c (g * z * g⁻¹) := hcg ▸ hz.conj g
      refine ⟨⟨g, hg⟩, ?_⟩
      rcases hadj with h | h
      · have := hcon b c z (g * z * g⁻¹) ih.1 h ih.2 hc
        rw [this]
        exact hc
      · have := hcon c b (g * z * g⁻¹) z ⟨g, hg⟩ h hc ih.2
        rw [← this]
        exact hc
  have hcentral : z ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := (hall (conjSub g K) (hD K hK _ ⟨g, rfl⟩)).2
    have h2 : IsClassicalMember3 (conjSub g K) (g * z * g⁻¹) := hz.conj g
    have h3 := involution_unique3 h1 h2
    calc g * z = (g * z * g⁻¹) * g := by group
      _ = z * g := by rw [← h3]
  exact Q3W.not_subset_center_of_ne_one hnab hz.ne_one (Set.singleton_subset_iff.mpr hcentral)

end DEdge

end CFSG.ClassicalInvolution.Q3.Q3NH
