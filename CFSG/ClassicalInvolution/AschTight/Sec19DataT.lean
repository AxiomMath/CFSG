module

public import CFSG.ClassicalInvolution.AschTight.Thm6Tight2

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscL62
open scoped Pointwise

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem exists_sec19DataT [IsSimpleGroup G] {K : Subgroup G} {z : G} {S : Sylow 2 G}
    {W : Subgroup G} (hd : Sec19Data p f K z S W) :
    ∃ (L : Subgroup G) (t : G) (V : Subgroup G), Sec19DataT p f K z S W L t V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht := hd.tight
  have htb := ht.toTightBranch
  have hI := isUniqueInvolution_of_tight htb
  have hΩ := hypOmegaMod_of_tightD ht
  have hp := ht.branch.odd
  have huniq : ∀ J ∈ CoreAssembly.conjClass K, IsUniqueInvolution J z → J = K := by
    intro J hJ hJz
    obtain ⟨g, rfl⟩ := CoreAssembly.single_class K J hJ
    have h1 := (hI.conj g).eq hJz
    rw [conjSub_eq_conjSub_of_tight htb (a := g) (b := 1) (by rw [h1]; group)]
    exact conjSub_eq_self_of_mem K.one_mem
  have hinv : ∀ J ∈ CoreAssembly.conjClass K, ∃ u, IsUniqueInvolution J u := by
    intro J hJ
    obtain ⟨g, rfl⟩ := CoreAssembly.single_class K J hJ
    exact ⟨_, hI.conj g⟩
  have h4 : ∀ U ∈ USet (CoreAssembly.conjClass K), ∀ J ∈ CoreAssembly.conjClass K, U ≤ J →
      ∀ u, IsUniqueInvolution J u → u ∈ U := by
    intro U hU J hJ hUJ u hu
    obtain ⟨R', hR', hUR', -, hidx⟩ := hU
    have h8 := (exists_ne_comm_of_mem_rSet hp ht.branch.five ht.branch.member hR').2
    have hcard : Nat.card R' = 2 * Nat.card U := by
      have h1 := Subgroup.relIndex_mul_card (H := U) (K := R')
      rw [inf_eq_left.mpr hUR', hidx] at h1
      exact h1.symm
    exact mem_of_uniqueInvolution_of_pGroup hu hUJ ((isPGroup_of_mem_rSet hR').to_le hUR')
      (by omega)
  obtain ⟨η, ⟨S', hηS', hinvη⟩, rfl⟩ := hd.hW
  have hex : ∃ U ∈ η, ¬ U ≤ K := by
    by_contra hcon
    push Not at hcon
    have hle1 : η.ncard ≤ 1 := by
      rw [Set.ncard_le_one]
      intro U hU U' hU'
      by_contra hne
      exact hηS'.2.1 U hU U' hU' hne K (CoreAssembly.mem_conjClass_self K) ⟨hcon U hU, hcon U' hU'⟩
    obtain ⟨Q₀, hQ₀S⟩ := hd.sylow
    have hR : (Q₀ : Subgroup K).map K.subtype ∈ RSet (CoreAssembly.conjClass K) :=
      ⟨K, CoreAssembly.mem_conjClass_self K, Q₀, rfl⟩
    obtain ⟨J₀, hJ₀, hRJ₀, hR2, hmax⟩ := mem_RSet_iff.mp
      (show (Q₀ : Subgroup K).map K.subtype ∈ RSet ({K} : Set (Subgroup G)) from ⟨K, rfl, Q₀, rfl⟩)
    rw [Set.mem_singleton_iff] at hJ₀
    have hRsyl : IsSylow2In ((Q₀ : Subgroup K).map K.subtype) K := by
      have h : IsSylow2In ((Q₀ : Subgroup K).map K.subtype) J₀ := ⟨hRJ₀, hR2, hmax⟩
      rwa [hJ₀] at h
    obtain ⟨U₀, hU₀R, hU₀c, hU₀card⟩ := (hΩ.isQuatSub_of_mem_RSet hp hR).exists_cyclic_index_two
    have hU₀ : U₀ ∈ USet (CoreAssembly.conjClass K) :=
      mem_USet_of_natCard (CoreAssembly.mem_conjClass_self K) hRsyl hU₀R hU₀c hU₀card
    have hzU₀ : z ∈ U₀ := h4 U₀ hU₀ K (CoreAssembly.mem_conjClass_self K)
      (hU₀R.trans (Subgroup.map_subtype_le _)) z hI
    obtain ⟨L₁, hL₁, t₁, hL₁t, ht₁z, V₁, hV₁, hV₁S, ht₁V⟩ :=
      exists_data_of_not_allTypeTwo (l6_2ModTmp p f) ht hd.mu S hd.hSz
    have ht₁K : t₁ ∉ K := fun h => ht₁z ((hI.unique t₁ h hL₁t.sq).resolve_left hL₁t.ne_one)
    have hdist : ∀ J ∈ CoreAssembly.conjClass K, ¬ (U₀ ≤ J ∧ V₁ ≤ J) := by
      rintro J hJ ⟨hU₀J, hV₁J⟩
      obtain ⟨u, hu⟩ := hinv J hJ
      have hzJ : z = u := (hu.unique z (hU₀J hzU₀) hI.sq).resolve_left hI.ne_one
      have hJK : J = K := huniq J hJ (hzJ ▸ hu)
      exact ht₁K (hJK ▸ hV₁J ht₁V)
    have hne : U₀ ≠ V₁ := fun h => ht₁K ((hU₀R.trans (Subgroup.map_subtype_le _)) (h ▸ ht₁V))
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S S'
    have hconjS : ∀ A : Subgroup G, A ≤ (S : Subgroup G) → conjSub g A ≤ (S' : Subgroup G) := by
      rintro A hA _ ⟨a, ha, rfl⟩
      have h1 : (MulAut.conj g) • a ∈ (MulAut.conj g) • (S : Subgroup G) :=
        Subgroup.smul_mem_pointwise_smul a (MulAut.conj g) _ (hA ha)
      rw [← Sylow.coe_subgroup_smul, hg] at h1
      exact h1
    have hinj : ∀ A B : Subgroup G, conjSub g A = conjSub g B → A = B := by
      intro A B h
      have h1 := congrArg (conjSub g⁻¹) h
      rwa [← conjSub_mul, ← conjSub_mul, inv_mul_cancel, conjSub_one, conjSub_one] at h1
    have hsub : ({conjSub g U₀, conjSub g V₁} : Set (Subgroup G)) ⊆
        {U | U ∈ USet (CoreAssembly.conjClass K) ∧ U ≤ (S' : Subgroup G)} := by
      rintro U (rfl | rfl)
      · exact ⟨USet.conj hΩ.conjInvariant hU₀ g, hconjS _ (hU₀R.trans hQ₀S)⟩
      · exact ⟨USet.conj hΩ.conjInvariant hV₁ g, hconjS _ hV₁S⟩
    have hdist' : InDistinctMembers (CoreAssembly.conjClass K)
        ({conjSub g U₀, conjSub g V₁} : Set (Subgroup G)) := by
      have key : ∀ J ∈ CoreAssembly.conjClass K, ¬ (conjSub g U₀ ≤ J ∧ conjSub g V₁ ≤ J) := by
        rintro J hJ ⟨h1, h2⟩
        refine hdist (conjSub g⁻¹ J) (hΩ.conjInvariant g⁻¹ J hJ) ⟨?_, ?_⟩
        · intro x hx
          rw [mem_conjSub_iff, inv_inv]
          exact h1 (conj_mem_conjSub hx)
        · intro x hx
          rw [mem_conjSub_iff, inv_inv]
          exact h2 (conj_mem_conjSub hx)
      rintro U (rfl | rfl) U' (rfl | rfl) hUU' J hJ
      · exact absurd rfl hUU'
      · exact key J hJ
      · exact fun h => key J hJ ⟨h.2, h.1⟩
      · exact absurd rfl hUU'
    have h2 := hηS'.2.2 _ hsub hdist'
    rw [Set.ncard_pair (fun h => hne (hinj _ _ h))] at h2
    omega
  obtain ⟨U, hUη, hUK⟩ := hex
  have hU := (hηS'.1 hUη).1
  obtain ⟨R', hR', hUR', hUc, hUidx⟩ := id hU
  obtain ⟨J, hJ, P, hR'P⟩ := hR'
  have hUJ : U ≤ J := hUR'.trans (hR'P ▸ Subgroup.map_subtype_le _)
  obtain ⟨u, hu⟩ := hinv J hJ
  have huz : u ≠ z := by
    intro h
    exact hUK (huniq J hJ (h ▸ hu) ▸ hUJ)
  exact ⟨J, u, U, ⟨hd, hJ, hu, huz, hU,
    le_iSup₂ (f := fun (V : Subgroup G) (_ : V ∈ η) => V) U hUη, h4 U hU J hJ hUJ u hu⟩⟩

end CFSG.ClassicalInvolution.Disconnected.AschTight
