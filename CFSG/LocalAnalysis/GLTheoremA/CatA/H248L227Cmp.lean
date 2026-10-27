module

public import CFSG.HardMathSupport.Solomon.Proving.CoreInConj
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H248L227

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Proving
  CFSG.LocalAnalysis.GLTheoremB

theorem elem_family {K : Type*} [Group K] {q : ℕ} {ι : Type*} [Fintype ι] (x : ι → K)
    (hord : ∀ i, orderOf (x i) = q) (hcomm : ∀ i j, i ≠ j → Commute (x i) (x j))
    (hind : iSupIndep fun i => Subgroup.zpowers (x i)) :
    CFSG.Open.IsElemAbelian q (⨆ i, Subgroup.zpowers (x i)) ∧
      Nat.card (⨆ i, Subgroup.zpowers (x i) : Subgroup K) = q ^ Fintype.card ι := by
  classical
  have hc : Pairwise fun i j : ι => ∀ a b : K, a ∈ Subgroup.zpowers (x i) →
      b ∈ Subgroup.zpowers (x j) → Commute a b := by
    intro i j hij a b ha hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (hcomm i j hij).zpow_zpow m n
  set φ := Subgroup.noncommPiCoprod hc
  have hinj : Function.Injective φ := Subgroup.injective_noncommPiCoprod_of_iSupIndep hind
  have hrange : φ.range = ⨆ i, Subgroup.zpowers (x i) := Subgroup.noncommPiCoprod_range
  have hzc : ∀ (i : ι) (a b : K), a ∈ Subgroup.zpowers (x i) → b ∈ Subgroup.zpowers (x i) →
      a * b = b * a := by
    intro i a b ha hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact ((Commute.refl (x i)).zpow_zpow m n).eq
  have hxq : ∀ i, x i ^ q = 1 := fun i => by
    rw [← hord i]; exact pow_orderOf_eq_one _
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, fun g hg => ?_⟩, ?_⟩
  · have ha : (a : K) ∈ φ.range := by rw [hrange]; exact a.2
    have hb : (b : K) ∈ φ.range := by rw [hrange]; exact b.2
    obtain ⟨u, hu⟩ := ha
    obtain ⟨v, hv⟩ := hb
    refine Subtype.ext ?_
    show (a : K) * b = b * a
    rw [← hu, ← hv, ← map_mul, ← map_mul]
    exact congrArg φ (funext fun i => Subtype.ext (hzc i _ _ (u i).2 (v i).2))
  · have hg' : g ∈ φ.range := by rw [hrange]; exact hg
    obtain ⟨u, rfl⟩ := hg'
    rw [← map_pow]
    have : u ^ q = 1 := by
      funext i
      refine Subtype.ext ?_
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (u i).2
      show ((u i : K)) ^ q = 1
      rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxq, one_zpow]
    rw [this, map_one]
  · have h1 : Nat.card (⨆ i, Subgroup.zpowers (x i) : Subgroup K) =
        Nat.card (∀ i, Subgroup.zpowers (x i)) := by
      rw [← hrange]
      exact (Nat.card_congr (Equiv.ofInjective φ hinj)).symm
    rw [h1, Nat.card_pi]
    simp [Nat.card_zpowers, hord]

private theorem zpowers_inter {K : Type*} [Group K] [Finite K] {q : ℕ} (hq : q.Prime)
    {L : Subgroup K} {x : K} (hord : orderOf x = q) (hnc : ∃ y ∈ L, x * y ≠ y * x) {y : K}
    (hy : y ∈ Subgroup.zpowers x) (hyc : ∀ a ∈ L, a * y = y * a) : y = 1 := by
  by_contra hy1
  have hdvd : orderOf y ∣ q := hord ▸ orderOf_dvd_of_mem_zpowers hy
  have hne : orderOf y ≠ 1 := fun h => hy1 (orderOf_eq_one_iff.1 h)
  have hyq : orderOf y = q := ((Nat.dvd_prime hq).1 hdvd).resolve_left hne
  have hle : Subgroup.zpowers y ≤ Subgroup.zpowers x := Subgroup.zpowers_le.2 hy
  have heq : Subgroup.zpowers y = Subgroup.zpowers x := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hyq, hord]
  have hx : x ∈ Subgroup.zpowers y := heq ▸ Subgroup.mem_zpowers x
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hx
  obtain ⟨y', hy'L, hy'⟩ := hnc
  have hc : Commute y' y := hyc y' hy'L
  have : y' * x = x * y' := by
    rw [← hm]
    exact ((Commute.zpow_right hc m)).eq
  exact hy' this.symm

private theorem normalizer_le_coreIn {K : Type*} [Group K] [Finite K] {q : ℕ} {P Q : Subgroup K}
    (hQP : Q ≤ P) (hr : 3 ≤ CFSG.Open.pRank q Q) :
    Subgroup.normalizer (Q : Set K) ≤ coreIn q 3 P ⊤ := by
  have h := le_coreIn (X := (⊤ : Subgroup K)) hQP hr
  rwa [top_inf_eq] at h

private theorem core_aux {K : Type} [Group K] [Finite K] {q : ℕ} (hq : q.Prime)
    (O : Set (Subgroup K)) (hconj : ∀ k : K, ∀ L ∈ O, GLBConj k L ∈ O) (hcard : 4 ≤ Nat.card O)
    (hx : ∀ L ∈ O, ∃ x ∈ L, orderOf x = q ∧ ∃ y ∈ L, x * y ≠ y * x)
    (hcomm : ∀ L ∈ O, ∀ L' ∈ O, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a) :
    4 ≤ CFSG.Open.pRank q (⊤ : Subgroup K) ∧ ∃ P0 : Subgroup K,
      Nat.card P0 = q ^ (Nat.card K).factorization q ∧ coreIn q 3 P0 ⊤ = ⊤ := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
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
    exact zpowers_inter hq (hxo i) (hxn i) hy1 (Subgroup.mem_centralizer_iff.1 (hle hy2))
  set Es : Finset O → Subgroup K := fun S => ⨆ i : S, Subgroup.zpowers (x i)
  have hE : ∀ S : Finset O, IsElemAbelian q (Es S) ∧ Nat.card (Es S) = q ^ S.card := by
    intro S
    have := elem_family (fun i : S => x i) (fun i => hxo i)
      (fun i j hij => hcx i j (fun h => hij (Subtype.ext h)))
      (hind.comp (f := fun i : S => (i : O)) Subtype.val_injective)
    simpa [Fintype.card_coe] using this
  have hmem : ∀ (S : Finset O), ∀ i ∈ S, x i ∈ Es S := fun S i hi =>
    (le_iSup (fun j : S => Subgroup.zpowers (x j)) ⟨i, hi⟩) (Subgroup.mem_zpowers _)
  have hle : ∀ (S : Finset O) (H : Subgroup K), (∀ i ∈ S, x i ∈ H) → Es S ≤ H :=
    fun S H h => iSup_le fun i => Subgroup.zpowers_le.2 (h i i.2)
  have hmono : ∀ S T : Finset O, S ⊆ T → Es S ≤ Es T := fun S T hST =>
    hle S _ fun i hi => hmem T i (hST hi)
  set M : Subgroup K := ⨆ (L : Subgroup K) (_ : L ∈ O), L
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
  have hEr : (Finset.univ : Finset O).card ≤ CFSG.Open.pRank q (⊤ : Subgroup K) :=
    CFSG.SectionRank.le_pRank hq.one_lt le_top hEel hEc
  refine ⟨hcardO.trans hEr, ?_⟩
  haveI : M.Normal := hMn
  obtain ⟨S0, hS0⟩ := (hEel.isPGroup.of_equiv
    (Subgroup.subgroupOfEquivOfLe hEM).symm).exists_le_sylow
  set Q0 : Subgroup K := (S0 : Subgroup ↥M).map M.subtype
  have hEQ0 : Es Finset.univ ≤ Q0 := fun e he =>
    ⟨⟨e, hEM he⟩, hS0 (Subgroup.mem_subgroupOf.2 he), rfl⟩
  have hfr : (⊤ : Subgroup K) ≤ M ⊔ Subgroup.normalizer (Q0 : Set K) := by
    rw [sup_comm, Sylow.normalizer_sup_eq_top S0]
  obtain ⟨P0, hQ0P0⟩ := (S0.isPGroup'.map M.subtype).exists_le_sylow
  refine ⟨P0, Sylow.card_eq_multiplicity P0, top_le_iff.1 ?_⟩
  have hr0 : 3 ≤ CFSG.Open.pRank q Q0 :=
    (by omega : 3 ≤ (Finset.univ : Finset O).card).trans
      (CFSG.SectionRank.le_pRank hq.one_lt hEQ0 hEel hEc)
  have hN0 : Subgroup.normalizer (Q0 : Set K) ≤ coreIn q 3 (P0 : Subgroup K) ⊤ :=
    normalizer_le_coreIn hQ0P0 hr0
  have hMH : M ≤ coreIn q 3 (P0 : Subgroup K) ⊤ := by
    refine iSup₂_le fun L hL => ?_
    set i : O := ⟨L, hL⟩
    have hcard' : 3 ≤ (Finset.univ.erase i).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i)]; omega
    obtain ⟨S, hS, hS3⟩ := Finset.exists_subset_card_eq hcard'
    have hiS : i ∉ S := fun h => (Finset.mem_erase.1 (hS h)).1 rfl
    obtain ⟨hSel, hSc⟩ := hE S
    have hQP : Es S ≤ (P0 : Subgroup K) :=
      (hmono S Finset.univ (Finset.subset_univ S)).trans (hEQ0.trans hQ0P0)
    have hr : 3 ≤ CFSG.Open.pRank q (Es S) :=
      CFSG.SectionRank.le_pRank hq.one_lt le_rfl hSel (by rw [hSc, hS3])
    have hcent : Es S ≤ Subgroup.centralizer (L : Set K) := by
      refine hle S _ fun j hj => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have hji : j ≠ i := fun h => hiS (h ▸ hj)
      exact hcomm L hL j.1 j.2 (fun h => hji (Subtype.ext h.symm)) a ha _ (hxL j)
    refine le_trans ?_ (normalizer_le_coreIn hQP hr)
    intro a ha
    apply Subgroup.centralizer_le_normalizer (Es S : Set K)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact ((Subgroup.mem_centralizer_iff.1 (hcent hh)) a ha).symm
  exact hfr.trans (sup_le hMH hN0)

theorem core_comps {K : Type} [Group K] [Finite K] {q : ℕ} (hq : q.Prime) (O : Set (Subgroup K))
    (hconj : ∀ k : K, ∀ L ∈ O, GLBConj k L ∈ O) (hcard : 4 ≤ Nat.card O)
    (hx : ∀ L ∈ O, ∃ x ∈ L, orderOf x = q ∧ ∃ y ∈ L, x * y ≠ y * x)
    (hcomm : ∀ L ∈ O, ∀ L' ∈ O, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a)
    (P : Subgroup K) (hP : IsPGroup q P) (hPc : Nat.card P = q ^ (Nat.card K).factorization q) :
    CFSG.HardMathSupport.Solomon.Coordinator.coreIn q 3 P ⊤ = ⊤ ∧ 4 ≤ CFSG.Open.pRank q P := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨hr4, P0, hP0c, h0⟩ := core_aux hq O hconj hcard hx hcomm
  let S0 : Sylow q K := Sylow.ofCard P0 hP0c
  let S1 : Sylow q K := Sylow.ofCard P hPc
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K S0 S1
  have hS1 : (S1 : Subgroup K) = GLBConj g⁻¹ P0 := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    simp [GLBConj]
    rfl
  have hPeq : P = GLBConj g⁻¹ P0 := hS1
  refine ⟨?_, ?_⟩
  · have htop : GLBConj g⁻¹ (⊤ : Subgroup K) = ⊤ := by ext z; simp [mem_gLBConj]
    have h := coreIn_gLBConj q 3 g⁻¹ P0 ⊤
    rw [htop, h0, htop] at h
    rw [hPeq]
    exact h
  · have h := (CFSG.SectionRank.pRank_sylow S1).1
    change 4 ≤ CFSG.Open.pRank q (S1 : Subgroup K)
    rw [h]
    exact hr4

end CFSG.LocalAnalysis.GLTheoremA.H248L227
