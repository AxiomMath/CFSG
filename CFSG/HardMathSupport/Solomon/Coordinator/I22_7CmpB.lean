module

public import CFSG.HardMathSupport.Solomon.Coordinator.I22_7CmpA
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs CFSG.LocalAnalysis.GLTheoremB

section Core

variable {K : Type} [Group K] [Finite K]

omit [Finite K] in
theorem i227cmp_isPGroup_of_elem {E : Subgroup K} (h : IsElemAbelian 3 E) : IsPGroup 3 E :=
  CFSG.Open.IsElemAbelian.isPGroup h

theorem i227cmp_zpowers_inter {L : Subgroup K} {x : K} (hord : orderOf x = 3)
    (hnc : ∃ y ∈ L, x * y ≠ y * x) {y : K} (hy : y ∈ Subgroup.zpowers x)
    (hyc : ∀ a ∈ L, a * y = y * a) : y = 1 := by
  by_contra hy1
  have hdvd : orderOf y ∣ 3 := hord ▸ orderOf_dvd_of_mem_zpowers hy
  have hne : orderOf y ≠ 1 := fun h => hy1 (orderOf_eq_one_iff.1 h)
  have h3 : orderOf y = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
    · exact absurd h hne
    · exact h
  have hle : Subgroup.zpowers y ≤ Subgroup.zpowers x := Subgroup.zpowers_le.2 hy
  have heq : Subgroup.zpowers y = Subgroup.zpowers x := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, h3, hord]
  have hx : x ∈ Subgroup.zpowers y := heq ▸ Subgroup.mem_zpowers x
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hx
  obtain ⟨y', hy'L, hy'⟩ := hnc
  have hc : Commute y' y := hyc y' hy'L
  have : y' * x = x * y' := by
    rw [← hm]
    exact ((Commute.zpow_right hc m)).eq
  exact hy' this.symm

theorem i227cmp_core (O : Set (Subgroup K))
    (hconj : ∀ k : K, ∀ L ∈ O, GLBConj k L ∈ O) (hcard : 4 ≤ Nat.card O)
    (hx : ∀ L ∈ O, ∃ x ∈ L, orderOf x = 3 ∧ ∃ y ∈ L, x * y ≠ y * x)
    (hcomm : ∀ L ∈ O, ∀ L' ∈ O, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a) :
    ∃ P0 : Subgroup K, IsPGroup 3 P0 ∧ Nat.card P0 = 3 ^ (Nat.card K).factorization 3 ∧
      (⊤ : Subgroup K) ≤ weakCoreIn 3 P0 ⊤ := by
  classical
  let _ : Fintype O := Fintype.ofFinite O
  choose x hxL hxo hxn using fun L : O => hx L.1 L.2
  have hcx : ∀ i j : O, i ≠ j → Commute (x i) (x j) := fun i j hij =>
    hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) _ (hxL i) _ (hxL j)
  have hind : iSupIndep fun i : O => Subgroup.zpowers (x i) := by
    intro i
    rw [Subgroup.disjoint_def]
    intro y hy1 hy2
    have hle : (⨆ (j : O) (_ : j ≠ i), Subgroup.zpowers (x j)) ≤
        Subgroup.centralizer (i.1 : Set K) := by
      refine iSup₂_le fun j hj => ?_
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro a ha
      exact hcomm i.1 i.2 j.1 j.2 (fun h => hj (Subtype.ext h).symm) a ha _ (hxL j)
    exact i227cmp_zpowers_inter (hxo i) (hxn i) hy1 (Subgroup.mem_centralizer_iff.1 (hle hy2))
  set Es : Finset O → Subgroup K := fun S => ⨆ i : S, Subgroup.zpowers (x i) with hEs
  have hE : ∀ S : Finset O, IsElemAbelian 3 (Es S) ∧ Nat.card (Es S) = 3 ^ S.card := by
    intro S
    have := i227cmp_elem_family (fun i : S => x i) (fun i => hxo i)
      (fun i j hij => hcx i j (fun h => hij (Subtype.ext h)))
      (hind.comp (f := fun i : S => (i : O)) Subtype.val_injective)
    simpa [Fintype.card_coe] using this
  have hmem : ∀ (S : Finset O), ∀ i ∈ S, x i ∈ Es S := fun S i hi =>
    (le_iSup (fun j : S => Subgroup.zpowers (x j)) ⟨i, hi⟩) (Subgroup.mem_zpowers _)
  have hle : ∀ (S : Finset O) (H : Subgroup K), (∀ i ∈ S, x i ∈ H) → Es S ≤ H :=
    fun S H h => iSup_le fun i => Subgroup.zpowers_le.2 (h i i.2)
  have hmono : ∀ S T : Finset O, S ⊆ T → Es S ≤ Es T := fun S T hST =>
    hle S _ fun i hi => hmem T i (hST hi)
  set M : Subgroup K := ⨆ (L : Subgroup K) (_ : L ∈ O), L with hM
  have hLM : ∀ L ∈ O, L ≤ M := fun L hL =>
    le_iSup₂ (f := fun (L : Subgroup K) (_ : L ∈ O) => L) L hL
  have hMn : M.Normal := by
    have h1 : ∀ g : K, M ≤ M.comap (MulAut.conj g).toMonoidHom := by
      intro g
      refine iSup₂_le fun L hL a ha => ?_
      have hL' : GLBConj g⁻¹ L ∈ O := hconj g⁻¹ L hL
      have : g * a * g⁻¹ ∈ GLBConj g⁻¹ L := by
        rw [mem_gLBConj]
        convert ha using 1
        group
      exact hLM _ hL' this
    exact ⟨fun n hn g => by simpa using h1 g hn⟩
  have hEM : Es Finset.univ ≤ M := hle _ _ fun i _ => hLM i.1 i.2 (hxL i)
  have hcardO : 4 ≤ (Finset.univ : Finset O).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact hcard
  obtain ⟨hEel, hEc⟩ := hE Finset.univ
  obtain ⟨Q0, hEQ0, hQ0M, hQ0p, hQ0c⟩ :=
    exists_sylow_ge Nat.prime_three hEM (i227cmp_isPGroup_of_elem hEel)
  have hfr : (⊤ : Subgroup K) ≤ M ⊔ Subgroup.normalizer (Q0 : Set K) :=
    le_sup_normalizer_of_sylow Nat.prime_three le_top (hMn.subgroupOf ⊤) hQ0M hQ0p hQ0c
  obtain ⟨P0, hQ0P0, -, hP0p, hP0c⟩ := exists_sylow_ge Nat.prime_three
    (K := (⊤ : Subgroup K)) le_top hQ0p
  refine ⟨P0, hP0p, by rw [hP0c, Subgroup.card_top], ?_⟩
  have hr0 : 3 ≤ CFSG.Open.pRank 3 Q0 :=
    ((by omega : 3 ≤ (Finset.univ : Finset O).card).trans
      (CFSG.SectionRank.le_pRank (by norm_num) hEQ0 hEel hEc))
  have hN0 : Subgroup.normalizer (Q0 : Set K) ≤ weakCoreIn 3 P0 ⊤ :=
    i227cmp_normalizer_le_weakCoreIn hQ0P0 hr0
  have hMH : M ≤ weakCoreIn 3 P0 ⊤ := by
    refine iSup₂_le fun L hL => ?_
    set i : O := ⟨L, hL⟩ with hi
    have hcard' : 3 ≤ (Finset.univ.erase i).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i)]; omega
    obtain ⟨S, hS, hS3⟩ := Finset.exists_subset_card_eq hcard'
    have hiS : i ∉ S := fun h => (Finset.mem_erase.1 (hS h)).1 rfl
    obtain ⟨hSel, hSc⟩ := hE S
    have hQP : Es S ≤ P0 := (hmono S Finset.univ (Finset.subset_univ S)).trans (hEQ0.trans hQ0P0)
    have hr : 3 ≤ CFSG.Open.pRank 3 (Es S) :=
      CFSG.SectionRank.le_pRank (by norm_num) le_rfl hSel (by rw [hSc, hS3])
    have hcent : Es S ≤ Subgroup.centralizer (L : Set K) := by
      refine hle S _ fun j hj => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have hji : j ≠ i := fun h => hiS (h ▸ hj)
      exact hcomm L hL j.1 j.2 (fun h => hji (Subtype.ext h.symm)) a ha _ (hxL j)
    refine le_trans ?_ (i227cmp_normalizer_le_weakCoreIn hQP hr)
    intro a ha
    apply Subgroup.centralizer_le_normalizer (Es S : Set K)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact ((Subgroup.mem_centralizer_iff.1 (hcent hh)) a ha).symm
  exact hfr.trans (sup_le hMH hN0)

theorem i227cmp_core_all (O : Set (Subgroup K))
    (hconj : ∀ k : K, ∀ L ∈ O, GLBConj k L ∈ O) (hcard : 4 ≤ Nat.card O)
    (hx : ∀ L ∈ O, ∃ x ∈ L, orderOf x = 3 ∧ ∃ y ∈ L, x * y ≠ y * x)
    (hcomm : ∀ L ∈ O, ∀ L' ∈ O, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a)
    (P : Subgroup K) (hPc : Nat.card P = 3 ^ (Nat.card K).factorization 3) :
    (⊤ : Subgroup K) ≤ weakCoreIn 3 P ⊤ := by
  obtain ⟨P0, hP0p, hP0c, h0⟩ := i227cmp_core O hconj hcard hx hcomm
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let S0 : Sylow 3 K := Sylow.ofCard P0 hP0c
  let S1 : Sylow 3 K := Sylow.ofCard P hPc
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K S0 S1
  have hS1 : (S1 : Subgroup K) = GLBConj g⁻¹ P0 := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    simp [GLBConj]
    rfl
  have hPeq : P = GLBConj g⁻¹ P0 := hS1
  rw [hPeq]
  exact i227cmp_top_le_weakCoreIn_conj h0 g⁻¹

end Core

end CFSG.HardMathSupport.Solomon.Coordinator
