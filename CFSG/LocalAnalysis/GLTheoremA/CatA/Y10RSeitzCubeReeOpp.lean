module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10RSeitzCubeStd
public import CFSG.LieType.ChevTwo.OppositeFixedExcReeFinal
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalLargeReeMain
public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalExcOpp
public import CFSG.RankThree.PartOne.KLAY.Sz
public import CFSG.Quasithin.Recognition.SzVBLocal
public import CFSG.Quasithin.Recognition.SzVBPerm

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.LieType.ChevTwo CFSG.LieType.ChevTwo.Semi
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.Quasithin.SzVB (ConjSet)



variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}

private theorem fixedOrbitRoots_subset_radicalRoots_of_ne {i k : Fin ReeTag.F4.fixedOrbitCount}
    (hik : i ≠ k) :
    ReeTag.F4.fixedOrbitRoots i ⊆ parabolicRadicalRoots ReeTag.F4.tag (ReeTag.F4.fixedOrbitSet k) := by
  intro α hα
  obtain ⟨⟨hroot, hpos⟩, hsupp⟩ := (ReeTag.mem_fixedOrbitRoots (t := ReeTag.F4)).1 hα
  rw [mem_parabolicRadicalRoots_iff]
  refine ⟨hroot, hpos, ?_⟩
  obtain ⟨j, hj⟩ : ∃ j, α j ≠ 0 := by
    by_contra h
    push Not at h
    exact hroot.ne_zero (funext h)
  refine ⟨j, ?_, hj⟩
  intro hjk
  have hmem_i : j ∈ ReeTag.F4.fixedOrbitSet i := by
    by_contra h
    exact hj (hsupp j h)
  rw [ReeTag.mem_fixedOrbitSet] at hmem_i
  rw [ReeTag.mem_fixedOrbitSet] at hjk
  exact hik (hmem_i.symm.trans hjk)

private theorem neg_fixedOrbitRoots_subset_oppRadicalRoots_of_ne {i k : Fin ReeTag.F4.fixedOrbitCount}
    (hik : i ≠ k) :
    Neg.neg '' ReeTag.F4.fixedOrbitRoots i ⊆
      CFSG.LieType.Chevalley.EvenOddRadical.oppRadicalRoots ReeTag.F4.tag
        (ReeTag.F4.fixedOrbitSet k) := by
  rintro α ⟨β, hβ, rfl⟩
  have h := fixedOrbitRoots_subset_radicalRoots_of_ne hik hβ
  simpa [CFSG.LieType.Chevalley.EvenOddRadical.oppRadicalRoots] using h

private theorem subgroupOf_le_normalizer_of_le_normalizer {G : Type*} [Group G] {Γ L Q : Subgroup G}
    (hN : L ≤ Subgroup.normalizer (Q : Set G)) :
    L.subgroupOf Γ ≤ Subgroup.normalizer ((Q.subgroupOf Γ : Subgroup Γ) : Set Γ) := by
  rw [Subgroup.le_normalizer_iff]
  intro x hx y hy
  rw [Subgroup.mem_subgroupOf] at hx hy ⊢
  exact (Subgroup.mem_normalizer_iff.1 (hN hx) y).1 hy

private theorem reeGamma_eq_reeLocalBlock_sup_of_ne (hK : Nat.card K = 2 ^ (2 * a + 1))
    {i k : Fin ReeTag.F4.fixedOrbitCount} (hik : i ≠ k) :
    ReeTag.F4.reeGamma K a =
      ReeTag.F4.reeLocalBlock K a i ⊔ ReeTag.F4.reeLocalBlock K a k := by
  have h := ReeTag.large_Ree_simple_pair_generation a K hK
  fin_cases i <;> fin_cases k
  · exact absurd (Fin.ext rfl) hik
  · exact h
  · rw [sup_comm]; exact h
  · exact absurd (Fin.ext rfl) hik

theorem reeGamma_parabolicRadical_sup_oppRadical_of_ne (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {i k : Fin ReeTag.F4.fixedOrbitCount} (hik : i ≠ k) :
    (parabolicRadical ReeTag.F4.tag K (ReeTag.F4.fixedOrbitSet k)).subgroupOf
        (ReeTag.F4.reeGamma K a) ⊔
      (CFSG.LieType.Chevalley.EvenOddRadical.oppRadical ReeTag.F4.tag K
        (ReeTag.F4.fixedOrbitSet k)).subgroupOf (ReeTag.F4.reeGamma K a) = ⊤ := by
  classical
  set Γ : Subgroup (ModGL ReeTag.F4.tag K) := ReeTag.F4.reeGamma K a with hΓ
  let Q : Subgroup ↥Γ :=
    (parabolicRadical ReeTag.F4.tag K (ReeTag.F4.fixedOrbitSet k)).subgroupOf Γ
  let V : Subgroup ↥Γ :=
    (CFSG.LieType.Chevalley.EvenOddRadical.oppRadical ReeTag.F4.tag K
      (ReeTag.F4.fixedOrbitSet k)).subgroupOf Γ
  let H : Subgroup ↥Γ := Q ⊔ V
  have hXi : (ReeTag.F4.reeFixedOrbitUnipotent K a i).subgroupOf Γ ≤ Q := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    change (x : ModGL ReeTag.F4.tag K) ∈
      parabolicRadical ReeTag.F4.tag K (ReeTag.F4.fixedOrbitSet k)
    exact rootSpan_mono (fixedOrbitRoots_subset_radicalRoots_of_ne hik)
      (Subgroup.mem_inf.1 hx).1
  have hYi : (ReeTag.F4.reeFixedOrbitNegUnipotent K a i).subgroupOf Γ ≤ V := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    change (x : ModGL ReeTag.F4.tag K) ∈
      CFSG.LieType.Chevalley.EvenOddRadical.oppRadical ReeTag.F4.tag K
        (ReeTag.F4.fixedOrbitSet k)
    exact rootSpan_mono (neg_fixedOrbitRoots_subset_oppRadicalRoots_of_ne hik)
      (Subgroup.mem_inf.1 hx).1
  have hMi : (ReeTag.F4.reeLocalBlock K a i).subgroupOf Γ ≤ H := by
    have hsup : (ReeTag.F4.reeLocalBlock K a i).subgroupOf Γ =
        (ReeTag.F4.reeFixedOrbitUnipotent K a i).subgroupOf Γ ⊔
          (ReeTag.F4.reeFixedOrbitNegUnipotent K a i).subgroupOf Γ := by
      rw [ReeTag.reeLocalBlock,
        Subgroup.subgroupOf_sup (A := ReeTag.F4.reeFixedOrbitUnipotent K a i)
          (A' := ReeTag.F4.reeFixedOrbitNegUnipotent K a i) (B := Γ) inf_le_right inf_le_right]
    rw [hsup]
    exact sup_le (hXi.trans le_sup_left) (hYi.trans le_sup_right)
  have hMkΓ : ReeTag.F4.reeLocalBlock K a k ≤ Γ := by
    rw [hΓ]; exact ReeTag.reeLocalBlock_le_reeGamma k
  have hMkLevi : ReeTag.F4.reeLocalBlock K a k ≤
      parabolicLevi ReeTag.F4.tag K (ReeTag.F4.fixedOrbitSet k) :=
    (ReeTag.reeLocalBlock_le_rootLevi (t := ReeTag.F4) k).trans
      (CFSG.RankThree.PartOne.KLAY.rootLevi_le_parabolicLevi (K := K)
        (ReeTag.F4.fixedOrbitSet k))
  have hMkQA : ReeTag.F4.reeLocalBlock K a k ≤
      Subgroup.normalizer (parabolicRadical ReeTag.F4.tag K (ReeTag.F4.fixedOrbitSet k) :
        Set (ModGL ReeTag.F4.tag K)) :=
    hMkLevi.trans ((parabolicLevi_le_parabolicSubgroup (ReeTag.F4.fixedOrbitSet k)).trans
      (parabolicSubgroup_le_normalizer_parabolicRadical (ReeTag.F4.fixedOrbitSet k)))
  obtain ⟨w₀, δ, hinj, hδ, hsq, h₀⟩ :=
    CFSG.LieType.Chevalley.EvenOddRadical.exists_longest (τ := ReeTag.F4.tag)
  have hMkQopp : ReeTag.F4.reeLocalBlock K a k ≤
      Subgroup.normalizer (CFSG.LieType.Chevalley.EvenOddRadical.oppRadical ReeTag.F4.tag K
        (ReeTag.F4.fixedOrbitSet k) : Set (ModGL ReeTag.F4.tag K)) :=
    hMkLevi.trans (CFSG.StandardType.GGOppRadExc.parabolicLevi_le_normalizer_oppRadical
      hinj hδ hsq h₀ (ReeTag.F4.fixedOrbitSet k))
  have hMkQ : (ReeTag.F4.reeLocalBlock K a k).subgroupOf Γ ≤
      Subgroup.normalizer (Q : Set ↥Γ) := by
    exact subgroupOf_le_normalizer_of_le_normalizer hMkQA
  have hMkV : (ReeTag.F4.reeLocalBlock K a k).subgroupOf Γ ≤
      Subgroup.normalizer (V : Set ↥Γ) := by
    exact subgroupOf_le_normalizer_of_le_normalizer hMkQopp
  have hMkH : (ReeTag.F4.reeLocalBlock K a k).subgroupOf Γ ≤
      Subgroup.normalizer (H : Set ↥Γ) := by
    intro x hx
    have hxQ : Q.map (MulAut.conj x).toMonoidHom = Q :=
      Subgroup.mem_normalizer_iff_map_conj_eq.1 (hMkQ hx)
    have hxV : V.map (MulAut.conj x).toMonoidHom = V :=
      Subgroup.mem_normalizer_iff_map_conj_eq.1 (hMkV hx)
    refine Subgroup.mem_normalizer_iff_map_conj_eq.2 ?_
    show (Q ⊔ V).map (MulAut.conj x).toMonoidHom = Q ⊔ V
    rw [Subgroup.map_sup, hxQ, hxV]
  have hGen : (⊤ : Subgroup ↥Γ) = (ReeTag.F4.reeLocalBlock K a i).subgroupOf Γ ⊔
      (ReeTag.F4.reeLocalBlock K a k).subgroupOf Γ := by
    rw [← Subgroup.subgroupOf_sup (ReeTag.reeLocalBlock_le_reeGamma i) hMkΓ,
      ← reeGamma_eq_reeLocalBlock_sup_of_ne hK hik, Subgroup.subgroupOf_self]
  have hΓN : (⊤ : Subgroup ↥Γ) ≤ Subgroup.normalizer (H : Set ↥Γ) := by
    rw [hGen]
    exact sup_le (hMi.trans (Subgroup.le_normalizer (H := H))) hMkH
  haveI hHnorm : H.Normal :=
    ⟨fun n hn g => (Subgroup.mem_normalizer_iff.1 (hΓN (Subgroup.mem_top g)) n).1 hn⟩
  have hHbot : H ≠ ⊥ := by
    obtain ⟨u, hu, hu1⟩ := ReeTag.exists_ne_one_mem_reeFixedOrbitUnipotent
      (t := ReeTag.F4) (K := K) (a := a) i
    have huΓ : u ∈ Γ := by
      rw [hΓ]; exact (Subgroup.mem_inf.1 hu).2
    intro hbot
    have hmem : (⟨u, huΓ⟩ : ↥Γ) ∈ H := hMi (Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_left hu))
    rw [hbot] at hmem
    exact hu1 (congrArg Subtype.val (Subgroup.mem_bot.1 hmem))
  have hsimple : IsSimpleGroup ↥Γ := by
    rw [hΓ]; exact CFSG.SignalizerFunctorTheorem.CatalogBridge.isSimpleGroup_reeGamma_F4
      (b := a) (k := K) ha hK
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H with h | h
  · exact absurd h hHbot
  · show Q ⊔ V = ⊤
    exact h



theorem oppRadical_empty_eq_negUnipotent :
    CFSG.LieType.Chevalley.EvenOddRadical.oppRadical ReeTag.F4.tag K ∅ =
      negUnipotent ReeTag.F4.tag K := by
  unfold CFSG.LieType.Chevalley.EvenOddRadical.oppRadical negUnipotent
  congr 1
  ext α
  simp only [CFSG.LieType.Chevalley.EvenOddRadical.oppRadicalRoots, Set.mem_setOf_eq,
    mem_parabolicRadicalRoots_iff, Set.mem_empty_iff_false, not_false_eq_true, exists_true_left,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hroot, hpos, i, hi⟩
    refine ⟨by simpa using IsRoot.neg hroot, ?_⟩
    have h := hpos
    rw [height_neg] at h
    omega
  · rintro ⟨hroot, hneg⟩
    refine ⟨IsRoot.neg hroot, by rw [height_neg]; omega, ?_⟩
    obtain ⟨j, hj⟩ : ∃ j, α j ≠ 0 := by
      by_contra h
      push Not at h
      exact hroot.ne_zero (funext h)
    exact ⟨j, by simpa using hj⟩

theorem reeGamma_parabolicRadical_sup_oppRadical_empty
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (parabolicRadical ReeTag.F4.tag K (∅ : Set (Fin ReeTag.F4.tag.rank))).subgroupOf
        (ReeTag.F4.reeGamma K a) ⊔
      (CFSG.LieType.Chevalley.EvenOddRadical.oppRadical ReeTag.F4.tag K ∅).subgroupOf
        (ReeTag.F4.reeGamma K a) = ⊤ := by
  classical
  set Γ : Subgroup (ModGL ReeTag.F4.tag K) := ReeTag.F4.reeGamma K a with hΓ
  let Q : Subgroup ↥Γ :=
    (parabolicRadical ReeTag.F4.tag K (∅ : Set (Fin ReeTag.F4.tag.rank))).subgroupOf Γ
  let V : Subgroup ↥Γ :=
    (CFSG.LieType.Chevalley.EvenOddRadical.oppRadical ReeTag.F4.tag K ∅).subgroupOf Γ
  let H : Subgroup ↥Γ := Q ⊔ V
  have hQ : Q = (ReeTag.F4.reeFixedPosUnipotent K a).subgroupOf Γ := by
    show (reeQJ ReeTag.F4 K a none) = _
    rw [reeQJ_none]
  have hV : V = (ReeTag.F4.reeFixedNegUnipotent K a).subgroupOf Γ := by
    show (CFSG.LieType.Chevalley.EvenOddRadical.oppRadical ReeTag.F4.tag K ∅).subgroupOf Γ = _
    rw [oppRadical_empty_eq_negUnipotent]
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, ReeTag.reeFixedNegUnipotent,
      Subgroup.mem_inf]
    exact ⟨fun h => ⟨h, x.2⟩, fun h => h.1⟩
  have hM : ∀ i : Fin ReeTag.F4.fixedOrbitCount,
      (ReeTag.F4.reeLocalBlock K a i).subgroupOf Γ ≤ H := by
    intro i
    have hX : (ReeTag.F4.reeFixedOrbitUnipotent K a i).subgroupOf Γ ≤ Q := by
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx
      rw [hQ, Subgroup.mem_subgroupOf]
      exact Subgroup.mem_inf.2
        ⟨rootSpan_le_posUnipotent (ReeTag.fixedOrbitRoots_subset i) (Subgroup.mem_inf.1 hx).1,
          (Subgroup.mem_inf.1 hx).2⟩
    have hY : (ReeTag.F4.reeFixedOrbitNegUnipotent K a i).subgroupOf Γ ≤ V := by
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx
      rw [hV, Subgroup.mem_subgroupOf]
      exact Subgroup.mem_inf.2 ⟨rootSpan_le_negUnipotent (by
        rintro α ⟨β, hβ, rfl⟩
        refine ⟨IsRoot.neg (ReeTag.fixedOrbitRoots_subset i hβ).1, ?_⟩
        rw [height_neg]
        exact neg_neg_of_pos (ReeTag.fixedOrbitRoots_subset i hβ).2) (Subgroup.mem_inf.1 hx).1,
        (Subgroup.mem_inf.1 hx).2⟩
    have hsup : (ReeTag.F4.reeLocalBlock K a i).subgroupOf Γ =
        (ReeTag.F4.reeFixedOrbitUnipotent K a i).subgroupOf Γ ⊔
          (ReeTag.F4.reeFixedOrbitNegUnipotent K a i).subgroupOf Γ := by
      rw [ReeTag.reeLocalBlock,
        Subgroup.subgroupOf_sup (A := ReeTag.F4.reeFixedOrbitUnipotent K a i)
          (A' := ReeTag.F4.reeFixedOrbitNegUnipotent K a i) (B := Γ) inf_le_right inf_le_right]
    rw [hsup]
    exact sup_le (hX.trans le_sup_left) (hY.trans le_sup_right)
  have hM0Γ : ReeTag.F4.reeLocalBlock K a ⟨0, by decide⟩ ≤ Γ := by
    rw [hΓ]; exact ReeTag.reeLocalBlock_le_reeGamma _
  have hM1Γ : ReeTag.F4.reeLocalBlock K a ⟨1, by decide⟩ ≤ Γ := by
    rw [hΓ]; exact ReeTag.reeLocalBlock_le_reeGamma _
  have hGen : (⊤ : Subgroup ↥Γ) =
      (ReeTag.F4.reeLocalBlock K a ⟨0, by decide⟩).subgroupOf Γ ⊔
        (ReeTag.F4.reeLocalBlock K a ⟨1, by decide⟩).subgroupOf Γ := by
    rw [← Subgroup.subgroupOf_sup hM0Γ hM1Γ,
      ← ReeTag.large_Ree_simple_pair_generation a K hK, Subgroup.subgroupOf_self]
  show Q ⊔ V = ⊤
  refine le_antisymm le_top ?_
  rw [hGen]
  exact sup_le (hM ⟨0, by decide⟩) (hM ⟨1, by decide⟩)



private theorem fieldAut_mem_oppRadical {A : Set (Fin ReeTag.F4.tag.rank)} (σ : RingAut K)
    {g : ModGL ReeTag.F4.tag K}
    (hg : g ∈ CFSG.LieType.Chevalley.EvenOddRadical.oppRadical ReeTag.F4.tag K A) :
    fieldAutHom ReeTag.F4.tag K σ g ∈
      CFSG.LieType.Chevalley.EvenOddRadical.oppRadical ReeTag.F4.tag K A := by
  rw [CFSG.LieType.Chevalley.EvenOddRadical.oppRadical] at hg ⊢
  simpa [fieldAutHom_apply] using
    (CFSG.LieType.Chevalley.entrywise_mem_rootSpan (τ := ReeTag.F4.tag) (σ := (σ : K ≃+* K)) hg)

theorem exists_conj_oppRadical_of_mem (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {j : Option (Fin ReeTag.F4.fixedOrbitCount)}
    {R : Subgroup (MulAut ↥(ReeTag.F4.reeGamma K a))} {α : ↥R}
    (hRQ : ∀ α ∈ R, (reeQJ ReeTag.F4 K a j).map α.toMonoidHom = reeQJ ReeTag.F4 K a j)
    (hNQ : Subgroup.normalizer ((reeQJ ReeTag.F4 K a j : Subgroup ↥(ReeTag.F4.reeGamma K a)) :
        Set ↥(ReeTag.F4.reeGamma K a)) =
      (parabolicSubgroup ReeTag.F4.tag K (reeAset j)).subgroupOf (ReeTag.F4.reeGamma K a)) :
    ∃ q : ↥(reeQJ ReeTag.F4 K a j),
      Subgroup.map α.1.toMonoidHom
        ((CFSG.LieType.Chevalley.EvenOddRadical.oppRadical ReeTag.F4.tag K (reeAset j)).subgroupOf
          (ReeTag.F4.reeGamma K a)) =
      Subgroup.map (MulAut.conj (q : ↥(ReeTag.F4.reeGamma K a))).toMonoidHom
        ((CFSG.LieType.Chevalley.EvenOddRadical.oppRadical ReeTag.F4.tag K (reeAset j)).subgroupOf
          (ReeTag.F4.reeGamma K a)) := by
  classical
  let Γ : Subgroup (ModGL ReeTag.F4.tag K) := ReeTag.F4.reeGamma K a
  let A : Set (Fin ReeTag.F4.tag.rank) := reeAset j
  let Q : Subgroup ↥Γ := reeQJ ReeTag.F4 K a j
  let V₀ : Subgroup ↥Γ :=
    (CFSG.LieType.Chevalley.EvenOddRadical.oppRadical ReeTag.F4.tag K A).subgroupOf Γ
  have hQdef : Q = (parabolicRadical ReeTag.F4.tag K A).subgroupOf Γ := by
    cases j <;> rfl
  have hNF : UniqueNormalFormRee a R := uniqueNormalFormRee_of_large ha hK R
  let g : GamL ReeTag.F4.tag K := liftRee hNF α
  have hgΓ : g.left ∈ Γ := liftRee_left_mem hNF α
  have hQRα : Subgroup.map α.1.toMonoidHom
      ((parabolicRadical ReeTag.F4.tag K A).subgroupOf Γ) =
      (parabolicRadical ReeTag.F4.tag K A).subgroupOf Γ := by
    rw [← hQdef]
    exact hRQ α.1 α.2
  have hNQ' : Subgroup.normalizer
      (((parabolicRadical ReeTag.F4.tag K A).subgroupOf Γ : Subgroup ↥Γ) : Set ↥Γ) =
      (parabolicSubgroup ReeTag.F4.tag K A).subgroupOf Γ := by
    rw [← hQdef]
    exact hNQ
  have hgP : g.left ∈ parabolicSubgroup ReeTag.F4.tag K A := by
    have hmem := left_mem_normalizer (K := K) (Cg := Γ)
      (Qg := parabolicRadical ReeTag.F4.tag K A)
      (fun σ h hh => fieldAut_mem_reeGamma σ hh)
      (fun σ h hh => fieldAut_mem_parabolicRadical σ hh)
      hQRα hgΓ (liftRee_spec hNF α)
    rw [hNQ'] at hmem
    exact Subgroup.mem_subgroupOf.1 hmem
  obtain ⟨q, hq, m, hm, hqm⟩ :=
    reeGamma_decomp (A := A) (reeAset_perm j) hgP hgΓ
  obtain ⟨hqR, hqΓ⟩ := Subgroup.mem_inf.1 hq
  obtain ⟨hmL, hmΓ⟩ := Subgroup.mem_inf.1 hm
  let qΓ : ↥Γ := ⟨q, hqΓ⟩
  have hqQ : qΓ ∈ Q := by
    rw [hQdef]
    exact Subgroup.mem_subgroupOf.2 hqR
  obtain ⟨w₀, δ, hinj, hδ, hsq, h₀⟩ :=
    CFSG.LieType.Chevalley.EvenOddRadical.exists_longest (τ := ReeTag.F4.tag)
  have hmN : m ∈ Subgroup.normalizer
      (CFSG.LieType.Chevalley.EvenOddRadical.oppRadical ReeTag.F4.tag K A :
        Set (ModGL ReeTag.F4.tag K)) :=
    (CFSG.StandardType.GGOppRadExc.parabolicLevi_le_normalizer_oppRadical
      (τ := ReeTag.F4.tag) (K := K) (w₀ := w₀) (δ := δ) hinj hδ hsq h₀ A) hmL
  refine ⟨⟨qΓ, hqQ⟩, ?_⟩
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    have hxΓmem : ((x : ↥Γ) : ModGL ReeTag.F4.tag K) ∈ ReeTag.F4.reeGamma K a := (x : ↥Γ).2
    have hxOpp : (x : ModGL ReeTag.F4.tag K) ∈
        CFSG.LieType.Chevalley.EvenOddRadical.oppRadical ReeTag.F4.tag K A :=
      (Subgroup.mem_subgroupOf (H := CFSG.LieType.Chevalley.EvenOddRadical.oppRadical
        ReeTag.F4.tag K A) (K := Γ)).1 hx
    have hδxOpp : fieldAutHom ReeTag.F4.tag K g.right (x : ModGL ReeTag.F4.tag K) ∈
        CFSG.LieType.Chevalley.EvenOddRadical.oppRadical ReeTag.F4.tag K A :=
      fieldAut_mem_oppRadical g.right hxOpp
    have hδxΓ : fieldAutHom ReeTag.F4.tag K g.right (x : ModGL ReeTag.F4.tag K) ∈ Γ :=
      fieldAut_mem_reeGamma g.right x.2
    have hyOpp : m * fieldAutHom ReeTag.F4.tag K g.right (x : ModGL ReeTag.F4.tag K) * m⁻¹ ∈
        CFSG.LieType.Chevalley.EvenOddRadical.oppRadical ReeTag.F4.tag K A :=
      (Subgroup.mem_normalizer_iff.1 hmN _).1 hδxOpp
    have hyΓ : m * fieldAutHom ReeTag.F4.tag K g.right (x : ModGL ReeTag.F4.tag K) * m⁻¹ ∈ Γ :=
      mul_mem (mul_mem hmΓ hδxΓ) (inv_mem hmΓ)
    let y₀ : ↥Γ := ⟨m * fieldAutHom ReeTag.F4.tag K g.right (x : ModGL ReeTag.F4.tag K) * m⁻¹, hyΓ⟩
    have hy₀V : y₀ ∈ V₀ := Subgroup.mem_subgroupOf.2 hyOpp
    refine Subgroup.mem_map.2 ⟨y₀, hy₀V, ?_⟩
    apply Subtype.ext
    show (q : ModGL ReeTag.F4.tag K) *
      (m * fieldAutHom ReeTag.F4.tag K g.right (x : ModGL ReeTag.F4.tag K) * m⁻¹) *
        (q : ModGL ReeTag.F4.tag K)⁻¹ =
      ((α.1 x : ↥Γ) : ModGL ReeTag.F4.tag K)
    rw [liftRee_spec hNF α x, conjAct_apply, ← hqm, fieldAutHom_apply]
    dsimp only [g]
    group
  · rw [Subgroup.card_map_of_injective (K := V₀)
        (f := (MulAut.conj (↑(⟨qΓ, hqQ⟩ : ↥Q) : ↥Γ)).toMonoidHom) (MulAut.conj _).injective,
      Subgroup.card_map_of_injective (K := V₀) (f := α.1.toMonoidHom) α.1.injective]



theorem ree_family_core (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∀ (j : Option (Fin ReeTag.F4.fixedOrbitCount)) (p : ℕ), p.Prime → p ≠ 2 →
    ∀ R : Subgroup (MulAut ↥(ReeTag.F4.reeGamma K a)), IsPGroup p R →
      (∀ α ∈ R, Subgroup.map α.toMonoidHom (reeQJ ReeTag.F4 K a j) = reeQJ ReeTag.F4 K a j) →
      Subgroup.normalizer ((reeQJ ReeTag.F4 K a j : Subgroup ↥(ReeTag.F4.reeGamma K a)) :
          Set ↥(ReeTag.F4.reeGamma K a)) =
        (parabolicSubgroup ReeTag.F4.tag K (reeAset j)).subgroupOf (ReeTag.F4.reeGamma K a) →
      ∃ V : Subgroup ↥(ReeTag.F4.reeGamma K a), IsPGroup 2 V ∧
        (∀ α ∈ R, Subgroup.map α.toMonoidHom V = V) ∧
        reeQJ ReeTag.F4 K a j ⊔ V = ⊤ := by
  classical
  intro j p hp hp2 R hR hRQ hNQ
  let Γ : Subgroup (ModGL ReeTag.F4.tag K) := ReeTag.F4.reeGamma K a
  let Q : Subgroup ↥Γ := reeQJ ReeTag.F4 K a j
  let V₀ : Subgroup ↥Γ :=
    (CFSG.LieType.Chevalley.EvenOddRadical.oppRadical ReeTag.F4.tag K (reeAset j)).subgroupOf Γ
  have hV₀p : IsPGroup 2 V₀ := by
    have h : IsPGroup 2 (CFSG.LieType.Chevalley.EvenOddRadical.oppRadical ReeTag.F4.tag K
        (reeAset j)) :=
      (CFSG.LieType.Chevalley.EvenOddRadical.isPGroup_negUnipotent (K := K) (τ := ReeTag.F4.tag)).to_le
        (CFSG.LieType.Chevalley.EvenOddRadical.oppRadical_le_negUnipotent (reeAset j))
    exact h.comap_subtype
  have hgen : Q ⊔ V₀ = ⊤ := by
    cases j with
    | none =>
      simpa only [Q, V₀, Γ, reeQJ, reeAset, reeStdSet] using
        reeGamma_parabolicRadical_sup_oppRadical_empty (K := K) (a := a) hK
    | some k =>
      obtain ⟨i, hik⟩ : ∃ i : Fin ReeTag.F4.fixedOrbitCount, i ≠ k := by
        fin_cases k
        · exact ⟨⟨1, by decide⟩, by decide⟩
        · exact ⟨⟨0, by decide⟩, by decide⟩
      simpa only [Q, V₀, Γ, reeQJ, reeAset, reeStdSet] using
        reeGamma_parabolicRadical_sup_oppRadical_of_ne (K := K) (a := a) ha hK hik
  have hVα : ∀ α : ↥R, ∃ q : ↥Q,
      Subgroup.map α.1.toMonoidHom V₀ =
        Subgroup.map (MulAut.conj (q : ↥Γ)).toMonoidHom V₀ := by
    intro α
    exact exists_conj_oppRadical_of_mem ha hK (j := j) (R := R) (α := α) hRQ hNQ
  choose qOf hqOf using hVα
  haveI : Fact p.Prime := ⟨hp⟩
  letI : MulAction ↥R (ConjSet Q V₀) := {
    smul α W :=
      ⟨Subgroup.map α.1.toMonoidHom W.1, by
        obtain ⟨q, hqQ, hW⟩ := W.2
        have hαq : α.1 (q : ↥Γ) ∈ Q := by
          have := Subgroup.mem_map_of_mem (f := α.1.toMonoidHom) hqQ
          rwa [hRQ α.1 α.2] at this
        let x : ↥Γ :=
          ((⟨α.1 (q : ↥Γ) * (qOf α : ↥Γ), Q.mul_mem hαq (qOf α).2⟩ : ↥Q) : ↥Γ)
        refine ⟨x, ?_, ?_⟩
        · exact (⟨α.1 (q : ↥Γ) * (qOf α : ↥Γ), Q.mul_mem hαq (qOf α).2⟩ : ↥Q).2
        · rw [hW]
          change Subgroup.map α.1.toMonoidHom
            (Subgroup.map (MulAut.conj (q : ↥Γ)).toMonoidHom V₀) =
            Subgroup.map (MulAut.conj x).toMonoidHom V₀
          rw [Subgroup.map_map]
          have hcomp : α.1.toMonoidHom.comp (MulAut.conj (q : ↥Γ)).toMonoidHom =
              (MulAut.conj (α.1 (q : ↥Γ))).toMonoidHom.comp α.1.toMonoidHom := by
            ext v
            simp only [MonoidHom.comp_apply, MulAut.conj_apply, MulEquiv.coe_toMonoidHom,
              map_mul, map_inv]
          rw [hcomp, ← Subgroup.map_map, hqOf α, Subgroup.map_map]
          have hx : (MulAut.conj (α.1 (q : ↥Γ))).toMonoidHom.comp
              (MulAut.conj (qOf α : ↥Γ)).toMonoidHom = (MulAut.conj x).toMonoidHom := by
            apply MonoidHom.ext
            intro v
            change (MulAut.conj (α.1 (q : ↥Γ))) ((MulAut.conj (qOf α : ↥Γ)) v) =
              (MulAut.conj x) v
            rw [MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply]
            dsimp only [x]
            group
          rw [hx]
        ⟩
    one_smul W := by
      apply Subtype.ext
      change Subgroup.map (MonoidHom.id ↥Γ) W.1 = W.1
      rw [Subgroup.map_id]
    mul_smul α β W := by
      apply Subtype.ext
      change Subgroup.map (α.1 * β.1).toMonoidHom W.1 =
        Subgroup.map α.1.toMonoidHom (Subgroup.map β.1.toMonoidHom W.1)
      rw [Subgroup.map_map]
      rfl }
  have hnd : ¬ p ∣ Nat.card (ConjSet Q V₀) := by
    have horb : MulAction.orbit ↥Q (ConjSet.base Q V₀) = Set.univ := by
      apply Set.eq_univ_of_forall
      intro W
      obtain ⟨q, hqQ, hW⟩ := W.2
      refine MulAction.mem_orbit_iff.mpr ⟨⟨q, hqQ⟩, ?_⟩
      apply Subtype.ext
      rw [ConjSet.smul_val]
      exact hW.symm
    have hcardeq : Nat.card (ConjSet Q V₀) =
        Nat.card (MulAction.orbit ↥Q (ConjSet.base Q V₀)) := by
      rw [horb]
      exact (Nat.card_congr (Equiv.Set.univ (ConjSet Q V₀))).symm
    have hdvd_orbit : Nat.card (MulAction.orbit ↥Q (ConjSet.base Q V₀)) ∣ Nat.card ↥Q := by
      rw [Nat.card_coe_set_eq, ← MulAction.index_stabilizer]
      exact Subgroup.index_dvd_card _
    have hdvd : Nat.card (ConjSet Q V₀) ∣ Nat.card ↥Q := by
      rw [hcardeq]
      exact hdvd_orbit
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (ree_QJ_pgroup (t := ReeTag.F4) (K := K) (a := a) j)
    intro hpdiv
    have hdiv : p ∣ 2 ^ n := by
      have hdiv' : p ∣ Nat.card ↥Q := hpdiv.trans hdvd
      rw [hn] at hdiv'
      simpa [show ReeTag.F4.prime = 2 from rfl] using hdiv'
    exact hp2 (by
      have h2 : p ∣ 2 := hp.dvd_of_dvd_pow hdiv
      rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h1 | h1
      · exact absurd h1 hp.ne_one
      · exact h1)
  obtain ⟨W, hW⟩ := hR.nonempty_fixed_point_of_prime_not_dvd_card (ConjSet Q V₀) hnd
  have hWinv : ∀ α ∈ R, Subgroup.map α.toMonoidHom W.1 = W.1 := by
    intro α hα
    exact congrArg Subtype.val (MulAction.mem_fixedPoints.1 hW ⟨α, hα⟩)
  obtain ⟨q, hqQ, hWq⟩ := W.2
  refine ⟨W.1, ?_, hWinv, ?_⟩
  · rw [hWq]
    exact hV₀p.map _
  · show Q ⊔ W.1 = ⊤
    rw [hWq]
    change Q ⊔ Subgroup.map (MulAut.conj (q : ↥Γ)).toMonoidHom V₀ = ⊤
    have hQmap : Subgroup.map (MulAut.conj (q : ↥Γ)).toMonoidHom Q = Q :=
      Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer hqQ)
    rw [← hQmap, ← Subgroup.map_sup, hgen, Subgroup.map_top]
    exact MonoidHom.range_eq_top.2 (MulAut.conj (q : ↥Γ)).surjective




theorem seitzTwoGen_reeGamma (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    SeitzTwoGen ↥(ReeTag.F4.reeGamma K a) := by
  have hQeq : ∀ j : Option (Fin ReeTag.F4.fixedOrbitCount),
      reeQJ ReeTag.F4 K a j =
        (parabolicRadical ReeTag.F4.tag K (reeAset j)).subgroupOf
          (ReeTag.F4.reeGamma K a) := fun j => by cases j <;> rfl
  have hPeq : ∀ j : Option (Fin ReeTag.F4.fixedOrbitCount),
      reePJ ReeTag.F4 K a j =
        (parabolicSubgroup ReeTag.F4.tag K (reeAset j)).subgroupOf
          (ReeTag.F4.reeGamma K a) := fun j => by cases j <;> rfl
  refine seitzTwoGen_of_family (fun j => reeQJ ReeTag.F4 K a j)
    (fun j => reePJ ReeTag.F4 K a j) ?_ ?_ ?_ ?_
  · intro j
    exact ree_QJ_pgroup (t := ReeTag.F4) (K := K) (a := a) j
  · intro j
    exact ree_PJ_le_normalizer (t := ReeTag.F4) (K := K) (a := a) j
  · intro Q hQ hQ2
    obtain ⟨g, j, hN, hQ⟩ := ree_hstd_F4 Q hQ hQ2
    refine ⟨g, j, ?_, ?_⟩
    · intro x hx
      rw [hPeq j]
      exact hN x hx
    · intro y hy
      rw [hQeq j]
      exact hQ y hy
  · intro j p hp hp2 R hR hRQ hNQ
    have hNQ' : Subgroup.normalizer (reeQJ ReeTag.F4 K a j) =
        (parabolicSubgroup ReeTag.F4.tag K (reeAset j)).subgroupOf
          (ReeTag.F4.reeGamma K a) := by
      rw [hNQ, hPeq j]
    exact ree_family_core ha hK j p hp hp2 R hR hRQ hNQ'

end CFSG.LocalAnalysis.GLTheoremA.Y10F
