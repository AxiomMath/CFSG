module

public import CFSG.ClassicalInvolution.Q3.Q3NHIntr
import CFSG.ClassicalInvolution.Q3.Q3DBExactConn

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3NH

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Uniform

section Layer

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem oddCoreIn_le_involutionOddCore₃ (hΩ : ConjInvariant Ω) (hLoc : LocalLieSystems3 Ω)
    {K : Subgroup G} {z f : G} (hKΩ : K ∈ Ω) (hz : IsClassicalMember3 K z)
    (hKf : K ≤ Subgroup.centralizer ({f} : Set G)) (hf : f ∉ Subgroup.center G) :
    oddCoreIn K ≤ CFSG.Assembly.Dichotomy.involutionOddCore f :=
  CFSG.ClassicalInvolution.Q3.Q3DB.oddCoreIn_le_involutionOddCore_of_le_centralizer hΩ hLoc hKΩ hz
    hKf hf

end Layer

section Members

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}

theorem oddCoreIn_centralizer_le_of_mem_conjClass3 (hz : IsClassicalMember3 K z)
    (hint : oddCoreIn (Subgroup.centralizer ({z} : Set G)) ≤ K) {β : Subgroup G} {t : G}
    (hβ : β ∈ conjClass3 K) (ht : IsClassicalMember3 β t) :
    oddCoreIn (Subgroup.centralizer ({t} : Set G)) ≤ β := by
  obtain ⟨g, hg, htg⟩ := conjClass3_involution hz hβ ht
  have h1 : oddCoreIn (Subgroup.centralizer ({t} : Set G)) =
      (oddCoreIn (Subgroup.centralizer ({z} : Set G))).map (MulAut.conj g).toMonoidHom := by
    rw [htg, ← map_conj_centralizer_singleton g z]
    exact Balance.Bootstrap.oddCoreIn_conjSub_eq g (Subgroup.centralizer ({z} : Set G))
  rw [h1, hg]
  exact Subgroup.map_mono hint

variable [IsSimpleGroup G]

theorem oddCoreIn_eq_of_commutes₃ (hnab : ∃ a b : G, a * b ≠ b * a) (hz : IsClassicalMember3 K z)
    (hint : oddCoreIn (Subgroup.centralizer ({z} : Set G)) ≤ K)
    (hLoc : LocalLieSystems3 (conjClass3 K)) (hΩ : ConjInvariant (conjClass3 K))
    {L M : Subgroup G} (hL : L ∈ conjClass3 K) (hM : M ∈ conjClass3 K) (hc : Commutes L M) :
    oddCoreIn L = oddCoreIn M := by
  have key : ∀ {L M : Subgroup G}, L ∈ conjClass3 K → M ∈ conjClass3 K → Commutes L M →
      oddCoreIn M ≤ oddCoreIn L := by
    intro L M hL hM hc
    obtain ⟨g, rfl⟩ := hL
    obtain ⟨h, rfl⟩ := hM
    have hzL : IsClassicalMember3 (conjSub g K) (g * z * g⁻¹) := hz.conj g
    have hzM : IsClassicalMember3 (conjSub h K) (h * z * h⁻¹) := hz.conj h
    have hintL := oddCoreIn_centralizer_le_of_mem_conjClass3 hz hint ⟨g, rfl⟩ hzL
    have heq : oddCoreIn (conjSub g K) =
        oddCoreIn (Subgroup.centralizer ({g * z * g⁻¹} : Set G)) :=
      Uniform.oddCoreIn_eq_of_intrinsic (IsClassicalMemberU.ofQ3 hzL) hintL
    have hMf : conjSub h K ≤ Subgroup.centralizer ({g * z * g⁻¹} : Set G) := by
      intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hc _ hzL.mem y hy).symm
    have hf : g * z * g⁻¹ ∉ Subgroup.center G := fun hmem =>
      Q3W.not_subset_center_of_ne_one hnab hzL.ne_one (Set.singleton_subset_iff.mpr hmem)
    rw [heq]
    exact oddCoreIn_le_involutionOddCore₃ hΩ hLoc ⟨h, rfl⟩ hzM hMf hf
  exact le_antisymm (key hM hL hc.symm) (key hL hM hc)

theorem exactMembers3_of_intrinsic (hnab : ∃ a b : G, a * b ≠ b * a) (hz : IsClassicalMember3 K z)
    (hint : oddCoreIn (Subgroup.centralizer ({z} : Set G)) ≤ K)
    (hBelow : CIT3Below (Nat.card G)) (hΔ : DeltaConnected K) : ExactMembers3 (conjClass3 K) := by
  have hΩ : InClass3 (conjClass3 K) := inClass3_conjugates hz
  have hLoc : LocalLieSystems3 (conjClass3 K) := localLieSystems3_of_cit3Below hΩ hBelow
  have hconn := omegaConnected_range_conjSub hΔ
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hall : ∀ L, Relation.ReflTransGen
      (fun M N : Subgroup G => N ∈ conjClass3 K ∧ Commutes M N) K L →
      L ∈ conjClass3 K ∧ oddCoreIn L = oddCoreIn K := by
    intro L hL
    induction hL with
    | refl => exact ⟨hK, rfl⟩
    | tail _ hbc ih =>
      exact ⟨hbc.1, (oddCoreIn_eq_of_commutes₃ hnab hz hint hLoc hΩ.conjInvariant ih.1 hbc.1
        hbc.2).symm.trans ih.2⟩
  have hN : (oddCoreIn K).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hg : conjSub g K ∈ conjClass3 K := ⟨g, rfl⟩
    have h1 := (hall _ (hconn K hK _ hg)).2
    rw [Balance.Bootstrap.oddCoreIn_conjSub_eq] at h1
    have : g * n * g⁻¹ ∈ conjSub g (oddCoreIn K) := conj_mem_conjSub hn
    rwa [h1] at this
  have hbot : oddCoreIn K = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (oddCoreIn K) with h | h
    · exact h
    · exfalso
      have hodd : Odd (Nat.card (oddCoreIn K)) := odd_card_oddCoreIn K
      rw [h, Subgroup.card_top] at hodd
      have h2 : 2 ∣ Nat.card G := hz.orderOf_eq_two ▸ orderOf_dvd_natCard z
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  intro L hL
  have hLe : oddCoreIn L = ⊥ := by
    obtain ⟨g, rfl⟩ := hL
    rw [(hall _ (hconn K hK _ ⟨g, rfl⟩)).2, hbot]
  exact (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).mp hLe

theorem setup3_of_intrinsic_deltaConnected (hnab : ∃ a b : G, a * b ≠ b * a)
    (hz : IsClassicalMember3 K z) (hint : oddCoreIn (Subgroup.centralizer ({z} : Set G)) ≤ K)
    (hBelow : CIT3Below (Nat.card G)) (hΔ : DeltaConnected K) : Setup3 K z :=
  setup3_of_exact_intrinsic hz hint (exactMembers3_of_intrinsic hnab hz hint hBelow hΔ)

end Members

end CFSG.ClassicalInvolution.Q3.Q3NH

