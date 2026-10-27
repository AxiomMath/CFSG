module

public import CFSG.ClassicalInvolution.Q3.Q3DBNoData

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3DB

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Uniform


section Layer

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem oddCoreIn_le_involutionOddCore_of_le_centralizer (hΩ : ConjInvariant Ω)
    (hLoc : LocalLieSystems3 Ω) {K : Subgroup G} {z f : G} (hKΩ : K ∈ Ω)
    (hz : IsClassicalMember3 K z) (hKf : K ≤ Subgroup.centralizer ({f} : Set G))
    (hf : f ∉ Subgroup.center G) :
    oddCoreIn K ≤ CFSG.Assembly.Dichotomy.involutionOddCore f := by
  have hKm : K ∈ centralizingMembers Ω {f} := ⟨hKΩ, hKf⟩
  have hKY : K ≤ centralizingLayer Ω {f} := le_centralizingLayer hKm
  have hLie := hLoc {f} (by
    rw [Set.singleton_subset_iff]
    exact hf)
  obtain ⟨ι, -, ⟨D⟩⟩ := hLie
  have hmemΦ : (K.subgroupOf (centralizingLayer Ω {f})).map
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(centralizingLayer Ω {f}))) ∈
      oddQuotientFamily (restrictFamily (centralizingMembers Ω {f})
        (centralizingLayer Ω {f})) :=
    ⟨K.subgroupOf (centralizingLayer Ω {f}), ⟨K, hKm, hKY, rfl⟩, rfl⟩
  have h24 := D.card_eq _ hmemΦ
  exact (oddCoreIn_le_of_card_image_eq hKY hz h24).trans (oddCoreIn_centralizingLayer_le hΩ f)

end Layer

section Members

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}

theorem oddCoreIn_centralizer_le_of_mem_conjClass (hz : IsClassicalMember3 K z)
    (hint : oddCoreIn (Subgroup.centralizer ({z} : Set G)) ≤ K) {β : Subgroup G} {t : G}
    (hβ : β ∈ CoreAssembly.conjClass K) (ht : IsClassicalMember3 β t) :
    oddCoreIn (Subgroup.centralizer ({t} : Set G)) ≤ β := by
  obtain ⟨g, hg⟩ := hβ
  have hg' : conjSub g K = β := hg
  have htg : t = g * z * g⁻¹ := involution_unique3 ht (hg' ▸ hz.conj g)
  have h1 : oddCoreIn (Subgroup.centralizer ({t} : Set G)) =
      (oddCoreIn (Subgroup.centralizer ({z} : Set G))).map (MulAut.conj g).toMonoidHom := by
    rw [htg, ← map_conj_centralizer_singleton g z]
    exact oddCoreIn_conjSub_eq g (Subgroup.centralizer ({z} : Set G))
  rw [h1, ← hg']
  exact Subgroup.map_mono hint

variable [IsSimpleGroup G]

theorem oddCoreIn_eq_of_commutes (hnab : ∃ a b : G, a * b ≠ b * a) (hz : IsClassicalMember3 K z)
    (hint : oddCoreIn (Subgroup.centralizer ({z} : Set G)) ≤ K)
    (hLoc : LocalLieSystems3 (CoreAssembly.conjClass K))
    (hΩ : ConjInvariant (CoreAssembly.conjClass K)) {L M : Subgroup G}
    (hL : L ∈ CoreAssembly.conjClass K) (hM : M ∈ CoreAssembly.conjClass K) (hc : Commutes L M) :
    oddCoreIn L = oddCoreIn M := by
  have key : ∀ {L M : Subgroup G}, L ∈ CoreAssembly.conjClass K → M ∈ CoreAssembly.conjClass K →
      Commutes L M → oddCoreIn M ≤ oddCoreIn L := by
    intro L M hL hM hc
    obtain ⟨g, hg⟩ := hL
    obtain ⟨h, hh⟩ := hM
    have hg' : conjSub g K = L := hg
    have hh' : conjSub h K = M := hh
    have hzL : IsClassicalMember3 L (g * z * g⁻¹) := hg' ▸ hz.conj g
    have hzM : IsClassicalMember3 M (h * z * h⁻¹) := hh' ▸ hz.conj h
    have hintL := oddCoreIn_centralizer_le_of_mem_conjClass hz hint ⟨g, hg⟩ hzL
    have heq : oddCoreIn L = oddCoreIn (Subgroup.centralizer ({g * z * g⁻¹} : Set G)) :=
      Uniform.oddCoreIn_eq_of_intrinsic (IsClassicalMemberU.ofQ3 hzL) hintL
    have hMf : M ≤ Subgroup.centralizer ({g * z * g⁻¹} : Set G) := by
      intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hc _ hzL.mem y hy).symm
    have hf : g * z * g⁻¹ ∉ Subgroup.center G := fun hmem =>
      Q3W.not_subset_center_of_ne_one hnab hzL.ne_one (Set.singleton_subset_iff.mpr hmem)
    rw [heq]
    exact oddCoreIn_le_involutionOddCore_of_le_centralizer hΩ hLoc ⟨h, hh⟩ hzM hMf hf
  exact le_antisymm (key hM hL hc.symm) (key hL hM hc)

theorem exactMembers3_of_omegaConnected (hnab : ∃ a b : G, a * b ≠ b * a)
    (hz : IsClassicalMember3 K z) (hint : oddCoreIn (Subgroup.centralizer ({z} : Set G)) ≤ K)
    (hBelow : CIT3Below (Nat.card G)) (hconn : OmegaConnected (CoreAssembly.conjClass K)) :
    ExactMembers3 (conjClass3 K) := by
  have hΩ : InClass3 (conjClass3 K) := inClass3_conjugates hz
  have hLoc : LocalLieSystems3 (conjClass3 K) := localLieSystems3_of_cit3Below hΩ hBelow
  have hK : K ∈ conjClass3 K := CoreAssembly.mem_conjClass_self K
  have hall : ∀ L, Relation.ReflTransGen
      (fun M N : Subgroup G => N ∈ conjClass3 K ∧ Commutes M N) K L →
      L ∈ conjClass3 K ∧ oddCoreIn L = oddCoreIn K := by
    intro L hL
    induction hL with
    | refl => exact ⟨hK, rfl⟩
    | tail _ hbc ih =>
      exact ⟨hbc.1, (oddCoreIn_eq_of_commutes hnab hz hint hLoc hΩ.conjInvariant ih.1 hbc.1
        hbc.2).symm.trans ih.2⟩
  have hN : (oddCoreIn K).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hg : conjSub g K ∈ conjClass3 K := ⟨g, rfl⟩
    have h1 := (hall _ (hconn K hK _ hg)).2
    rw [oddCoreIn_conjSub_eq] at h1
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

theorem exactMembers3_of_dConnected_of_not_a2 (hnab : ∃ a b : G, a * b ≠ b * a)
    (hz : IsClassicalMember3 K z) (hint : oddCoreIn (Subgroup.centralizer ({z} : Set G)) ≤ K)
    (hBelow : CIT3Below (Nat.card G)) (hA2 : ¬ A2Configuration z K)
    (hD : DConnected (CoreAssembly.conjClass K)) : ExactMembers3 (conjClass3 K) :=
  exactMembers3_of_omegaConnected hnab hz hint hBelow
    (omegaConnected_of_dConnected_of_not_a2 hnab hz (fun _ => hint) hA2 hD)

end Members

theorem oddCentralizerFree_of_dConnected_sat_of_not_a2 {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) {K : Subgroup G} {z : G}
    (hz : IsClassicalMemberU (.sl2 3 1) K z) (hBelowT : CITBelowT (.sl2 3 1) (Nat.card G))
    (hA2 : ¬ A2Configuration z (satU (.sl2 3 1) K z))
    (hD : DConnected (CoreAssembly.conjClass (satU (.sl2 3 1) K z))) :
    Balance.oddCoreIn (Subgroup.centralizer ({z} : Set G)) = ⊥ :=
  oddCentralizerFree_of_exact_sat hz
    (exactMembers3_of_dConnected_of_not_a2 hnab ((hz.satU_member).toQ3 (by norm_num))
      (oddCoreIn_le_satU (MemberType.isSolvableType_sl2.mpr (by norm_num)))
      ((citBelowT_three_iff (p := 3) (f := 1) (by norm_num) _).mp hBelowT) hA2 hD)

@[expose] def OddCoreFreeA2D3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMemberU (.sl2 3 1) K z →
      CITBelowT (.sl2 3 1) (Nat.card G) → 3 ≤ CFSG.Open.twoRank G →
      ¬ TwoSubgroupsFourGenerated G →
      DConnected (CoreAssembly.conjClass (satU (.sl2 3 1) K z)) →
      A2Configuration z (satU (.sl2 3 1) K z) →
      Balance.oddCoreIn (Subgroup.centralizer ({z} : Set G)) = ⊥

theorem oddCoreFreeD3_of_oddCoreFreeA2D3 (h : OddCoreFreeA2D3) : OddCoreFreeD3 :=
  fun G _ _ _ hnab K z hz hBelow hr hlarge hD => by
    by_cases hA2 : A2Configuration z (satU (.sl2 3 1) K z)
    · exact h G hnab K z hz hBelow hr hlarge hD hA2
    · exact oddCentralizerFree_of_dConnected_sat_of_not_a2 hnab hz hBelow hA2 hD

theorem dBridgeU_three_of_oddCoreFreeA2D3 (h : OddCoreFreeA2D3) : DBridgeU 3 1 :=
  dBridgeU_three_of_oddCoreFreeD3 (oddCoreFreeD3_of_oddCoreFreeA2D3 h)

end CFSG.ClassicalInvolution.Q3.Q3DB
