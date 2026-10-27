module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.EdgeFalseSec
public import CFSG.ClassicalInvolution.Q3.TL4VtxLay

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Asc77.T8 (XMem)
open CFSG.ClassicalInvolution.Asc77.T8T (TriFrame)
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open scoped commutatorElement

section Cit3


theorem commute_of_adj_four_le {r n : ℕ} (hr : 4 ≤ r) (hNo : NoQ16E4) (h4 : Thm4RBelow r n)
    (hB : TightBelowR r n) {Q : Type} [Group Q] [Finite Q] {Φ : Set (Subgroup Q)}
    (h : TypeRFam r Φ) (hO : classicalInvolutionOddCore Q = ⊥) (hn : Nat.card Q < n)
    {Ka Kb : Subgroup Q} (hKa : Ka ∈ Φ) (hKb : Kb ∈ omegaNbr Φ Ka) {a b : Q}
    (ha : IsUniqueInvolution Ka a) (hb : IsUniqueInvolution Kb b) {L : Subgroup Q}
    (hL : IsComponent L) : (∀ y ∈ L, a * y = y * a) ∨ (∀ y ∈ L, b * y = y * b) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨y, hy, hne⟩, ⟨y', hy', hne'⟩⟩ := hcon
  have hcl := h.hyp.conjInvariant
  have hLa : L ≤ Vtx.orbGrp Φ Ka :=
    Vtx.le_orbGrp_of_moves hcl hKa hL ⟨a, ha.mem, y, hy, hne⟩
  by_cases hc : ∃ g ∈ omegaGen Φ, conjSub g Ka = Kb
  · obtain ⟨g, hg, hgK⟩ := hc
    obtain ⟨S', hd, hcls⟩ := tightClsR_orbGrp (by omega) h4 h hO hn hKa ha
    have hedge := not_tightEdgeless_orbGrp h4 h hO hn hKa hKb hg hgK
    have hlt : Nat.card ↥(Vtx.orbGrp Φ Ka) < n :=
      lt_of_le_of_lt (Subgroup.card_le_card_group _) hn
    exact Vtx.not_tightInO2_orbGrp hcl hKa ha hL ⟨y, hy, hne⟩
      (inO2_of_edge_four_le hr hB hNo hlt hd hcls hedge)
  · have hcomm := Vtx.commute_conj_of_not_conj h4 h hO hn hKa Kb hKb.1 hc
    have hcent : Vtx.orbGrp Φ Ka ≤ Subgroup.centralizer ({b} : Set Q) := by
      refine iSup_le fun g => ?_
      intro x hx
      refine Subgroup.mem_centralizer_iff.mpr fun k hk => ?_
      rw [Set.mem_singleton_iff.mp hk]
      exact hcomm (g : Q) g.2 b hb.mem x hx
    exact hne' (Subgroup.mem_centralizer_iff.mp (hLa.trans hcent hy') b (Set.mem_singleton b))

theorem hyp51At_of_vtxPair_four_le {r n : ℕ} (hr : 4 ≤ r) (hNo : NoQ16E4) (h4 : Thm4RBelow r n)
    (hB : TightBelowR r n) {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    (hZ : Subgroup.center G = ⊥) (hGn : Nat.card G ≤ n) (hΩ : TypeRFam r Ω) {B : Subgroup G}
    (hBe : IsElemAbelian 2 B) {a b c : G}
    (hgen : B = Subgroup.closure {a, b, c}) (hc1 : c ≠ 1) (ha1 : a ≠ 1) (hac : a ≠ c)
    (hb1 : b ≠ 1) (hbc : b ≠ c) (hab : a ≠ b) (habc : a * b ≠ c) {Ma Mb : Subgroup G}
    (hMa : XMem Ω c Ma) (hMb : XMem Ω c Mb) (ha : IsUniqueInvolution Ma a)
    (hb : IsUniqueInvolution Mb b) {P : Subgroup G} (hP : IsSylow2In P Mb)
    (hPc : P ≤ Subgroup.centralizer ({c} : Set G)) (hPN : P ≤ Subgroup.normalizer (Ma : Set G)) :
    Hyp51At B c := by
  have haB : a ∈ B := hgen ▸ Subgroup.subset_closure (Set.mem_insert _ _)
  have hbB : b ∈ B :=
    hgen ▸ Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hcB : c ∈ B :=
    hgen ▸ Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hBe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hsq : ∀ x ∈ B, x * x = 1 := fun x hx => (sq x).symm.trans (hBe.2 x hx)
  have haC : a ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hBc a haB c hcB)
  have hbC : b ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hBc b hbB c hcB)
  have habC : a * b ∈ Subgroup.centralizer ({c} : Set G) := Subgroup.mul_mem _ haC hbC
  have habB : a * b ∈ B := Subgroup.mul_mem _ haB hbB
  have hab1 : a * b ≠ 1 := fun h1 => hab (by
    calc a = a * (b * b) := by rw [hsq b hbB, mul_one]
      _ = (a * b) * b := by group
      _ = b := by rw [h1, one_mul])
  have hΦ : TypeRFam r (vtxFam Ω c) := hΩ.vtxFam
  have hO := oddQuot_oddCore_eq_bot c
  have hQn : Nat.card (OddQuot c) < n := lt_of_lt_of_le (natCard_oddQuot_lt hZ hc1) hGn
  have hKa := modOdd_coreAt_mem_vtxFam hMa
  have haz := isUniqueInvolution_modOdd_coreAt hΩ hMa ha haC
  have hbz := isUniqueInvolution_modOdd_coreAt hΩ hMb hb hbC
  have haB' := oddQuotMk_mem_modOdd haB haC
  have hbB' := oddQuotMk_mem_modOdd hbB hbC
  have haZ := Lemma52Proof.oddQuotMk_not_mem_zpowers hBe hcB hc1 haB ha1 hac haC
  have hbZ := Lemma52Proof.oddQuotMk_not_mem_zpowers hBe hcB hc1 hbB hb1 hbc hbC
  have habZ := Lemma52Proof.oddQuotMk_not_mem_zpowers hBe hcB hc1 habB hab1 habc habC
  have hmul : oddQuotMk c ⟨a * b, habC⟩ = oddQuotMk c ⟨a, haC⟩ * oddQuotMk c ⟨b, hbC⟩ :=
    map_mul (oddQuotMk c) (⟨a, haC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ⟨b, hbC⟩
  have hne : modOdd c (coreAt c Ma) ≠ modOdd c (coreAt c Mb) := by
    intro e
    have he := haz.eq (e ▸ hbz)
    apply habZ
    have hbb : (⟨b, hbC⟩ * ⟨b, hbC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) = 1 :=
      Subtype.ext hb.sq
    rw [hmul, he, ← map_mul, hbb, map_one]
    exact Subgroup.one_mem _
  have hnbr := modOdd_coreAt_mem_omegaNbr hMb hP hPc hPN hne
  have hnone : ∀ L : Subgroup (OddQuot c), IsComponent L → ¬ MovedByAll B c L := by
    intro L hL hm
    obtain ⟨y₁, hy₁, hne₁⟩ := hm _ haB' haZ
    obtain ⟨y₂, hy₂, hne₂⟩ := hm _ hbB' hbZ
    rcases commute_of_adj_four_le hr hNo h4 hB hΦ hO hQn hKa hnbr haz hbz hL with h1 | h1
    · exact hne₁ (h1 y₁ hy₁)
    · exact hne₂ (h1 y₂ hy₂)
  exact ⟨fun L₁ L₂ h₁ h₂ m₁ m₂ => (hnone L₁ h₁ m₁).elim, fun L hL m => (hnone L hL m).elim⟩

theorem hyp51_triFrame_four_le {r n : ℕ} (hr : 4 ≤ r) (hNo : NoQ16E4) (h4 : Thm4RBelow r n) :
    ∀ (Y : Type) [Group Y] [Finite Y] (Rd : Subgroup Y) (Sd : Sylow 2 Rd) (z : Y),
      TightLargeHypR r n Y Rd Sd z →
        ∀ (M : Fin 3 → Subgroup Y) (x : Fin 3 → Y) (P : Fin 3 → Subgroup Y),
          TriFrame (CoreAssembly.conjClass (tightCore Rd)) M x P →
            x 2 ∉ Subgroup.closure ({x 0, x 1} : Set Y) →
              Hyp51 (Subgroup.closure ({x 0, x 1, x 2} : Set Y)) := by
  intro Y _ _ Rd Sd z hL M x P hF hx2
  have hd := hL.datum
  have hΩ := hd.hypOmegaGen
  have hΩR := TightLargeHypR.typeRFam hL
  have hnt : ∀ L ∈ CoreAssembly.conjClass (tightCore Rd),
      ∀ L' ∈ twinSet (CoreAssembly.conjClass (tightCore Rd)) L, L' = L := fun L hL' =>
    T8.noTwins_of_mem hΩ.conjInvariant (fun J hJ => hJ) (fun K' hK' => by
      rw [hd.twinSet_eq] at hK'
      exact hK') hL'
  have hcomm : ∀ i j : Fin 3, x i * x j = x j * x i := fun i j => by
    by_cases hij : i = j
    · rw [hij]
    · exact Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ (hF.inv i) (hF.nbr i j hij) (hF.inv j)
  have hBe : IsElemAbelian 2 (Subgroup.closure ({x 0, x 1, x 2} : Set Y)) :=
    T8T.isElemAbelian_closure_three (hF.sq 0) (hF.sq 1) (hF.sq 2) (hcomm 0 1) (hcomm 0 2)
      (hcomm 1 2)
  have hB8 : Nat.card ↥(Subgroup.closure ({x 0, x 1, x 2} : Set Y)) = 8 :=
    T8T.natCard_closure_three (hF.sq 0) (hF.sq 1) (hF.sq 2) (hcomm 0 1) (hcomm 0 2)
      (hcomm 1 2) (hF.ne_one 0) (hF.ne_one 1) (hF.x_ne hnt (by decide)) (hF.ne_one 2) hx2
  have hmem3 : ∀ {w : Y}, w ∈ ({x 0, x 1} : Set Y) →
      w ∈ Subgroup.closure ({x 0, x 1} : Set Y) := fun hw => Subgroup.subset_closure hw
  refine ⟨hBe, hB8, fun c hcB hc1 => ?_⟩
  have hpair : ∀ i j : Fin 3, i ≠ j →
      Subgroup.closure ({x 0, x 1, x 2} : Set Y) = Subgroup.closure ({x i, x j, c} : Set Y) →
      x i ≠ c → x j ≠ c → x i * x j ≠ c →
        Hyp51At (Subgroup.closure ({x 0, x 1, x 2} : Set Y)) c := by
    intro i j hij hgen hic hjc hijc
    have hPc : P j ≤ Subgroup.centralizer ({c} : Set Y) := fun p hp => by
      have hle : Subgroup.closure ({x 0, x 1, x 2} : Set Y) ≤
          Subgroup.centralizer ({p} : Set Y) := by
        rw [Subgroup.closure_le]
        rintro w (rfl | rfl | rfl) <;>
          exact Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_singleton_iff.mp (hF.cent j _ hp)).symm
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp (hle hcB)).symm
    have hPN : P j ≤ Subgroup.normalizer (M i : Set Y) :=
      (hF.cent j i).trans (T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant (hF.mem i)
        (hnt _ (hF.mem i)) (hF.inv i))
    exact hyp51At_of_vtxPair_four_le hr hNo h4 hL.tbelow hL.center hL.card.le hΩR hBe hgen hc1
      (hF.ne_one i) hic (hF.ne_one j) hjc (hF.x_ne hnt hij) hijc
      (xMem_of_triFrame_of_mem hΩ hnt hF hcB i) (xMem_of_triFrame_of_mem hΩ hnt hF hcB j)
      (hF.inv i) (hF.inv j) (hF.syl j) hPc hPN
  by_cases hm0 : c = x 0
  · subst hm0
    refine hpair 1 2 (by decide) ?_ (hF.x_ne hnt (by decide)) (hF.x_ne hnt (by decide)) ?_
    · congr 1
      ext w
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    · intro h
      apply hx2
      have e : x 2 = x 1 * x 0 := by
        calc x 2 = x 1 * (x 1 * x 2) := by rw [← mul_assoc, hF.sq 1, one_mul]
          _ = x 1 * x 0 := by rw [h]
      rw [e]
      exact Subgroup.mul_mem _ (hmem3 (by simp)) (hmem3 (by simp))
  by_cases hm1 : c = x 1
  · subst hm1
    refine hpair 0 2 (by decide) ?_ (hF.x_ne hnt (by decide)) (hF.x_ne hnt (by decide)) ?_
    · congr 1
      ext w
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    · intro h
      apply hx2
      have e : x 2 = x 0 * x 1 := by
        calc x 2 = x 0 * (x 0 * x 2) := by rw [← mul_assoc, hF.sq 0, one_mul]
          _ = x 0 * x 1 := by rw [h]
      rw [e]
      exact Subgroup.mul_mem _ (hmem3 (by simp)) (hmem3 (by simp))
  by_cases hm2 : c = x 2
  · subst hm2
    refine hpair 0 1 (by decide) rfl (hF.x_ne hnt (by decide)) (hF.x_ne hnt (by decide)) ?_
    intro h
    apply hx2
    rw [← h]
    exact Subgroup.mul_mem _ (hmem3 (by simp)) (hmem3 (by simp))
  have hmem : ∀ i, c ≠ x i := by
    intro i
    fin_cases i
    exacts [hm0, hm1, hm2]
  rcases mem_closure_three_cases (hF.sq 2) (hcomm 0 2) (hcomm 1 2) hcB with hc01 | ⟨e, he, rfl⟩
  · have hc : c = x 0 * x 1 := by
      rcases TypeCSetup.mem_closure_pair (hF.sq 0) (hF.sq 1) (hcomm 0 1) hc01 with
        h | h | h | h
      · exact absurd h hc1
      · exact absurd h (hmem 0)
      · exact absurd h (hmem 1)
      · exact h
    subst hc
    refine hpair 0 2 (by decide) ?_ (fun h => hmem 0 h.symm) (fun h => hmem 2 h.symm) ?_
    · apply le_antisymm
      · rw [Subgroup.closure_le]
        rintro w (rfl | rfl | rfl)
        · exact Subgroup.subset_closure (by simp)
        · have h1 : x 0 * (x 0 * x 1) ∈ Subgroup.closure ({x 0, x 2, x 0 * x 1} : Set Y) :=
            Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
              (Subgroup.subset_closure (by simp))
          rwa [← mul_assoc, hF.sq 0, one_mul] at h1
        · exact Subgroup.subset_closure (by simp)
      · rw [Subgroup.closure_le]
        rintro w (rfl | rfl | rfl)
        · exact mem_triFrame_closure 0
        · exact mem_triFrame_closure 2
        · exact Subgroup.mul_mem _ (mem_triFrame_closure 0) (mem_triFrame_closure 1)
    · intro h
      exact hF.x_ne hnt (show (2 : Fin 3) ≠ 1 by decide) (mul_left_cancel h)
  · refine hpair 0 1 (by decide) ?_ (fun h => hmem 0 h.symm) (fun h => hmem 1 h.symm) ?_
    · apply le_antisymm
      · rw [Subgroup.closure_le]
        rintro w (rfl | rfl | rfl)
        · exact Subgroup.subset_closure (by simp)
        · exact Subgroup.subset_closure (by simp)
        · have heR : e ∈ Subgroup.closure ({x 0, x 1, e * x 2} : Set Y) :=
            Subgroup.closure_mono (by intro w hw; rcases hw with rfl | rfl <;> simp) he
          have h1 : e⁻¹ * (e * x 2) ∈ Subgroup.closure ({x 0, x 1, e * x 2} : Set Y) :=
            Subgroup.mul_mem _ (Subgroup.inv_mem _ heR) (Subgroup.subset_closure (by simp))
          rwa [inv_mul_cancel_left] at h1
      · rw [Subgroup.closure_le]
        rintro w (rfl | rfl | rfl)
        · exact mem_triFrame_closure 0
        · exact mem_triFrame_closure 1
        · refine Subgroup.mul_mem _ ?_ (mem_triFrame_closure 2)
          exact Subgroup.closure_mono (by
            intro w hw
            rcases hw with rfl | rfl <;> simp) he
    · intro h
      apply hx2
      have e2 : x 2 = e⁻¹ * (x 0 * x 1) := by rw [h]; group
      rw [e2]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ he)
        (Subgroup.mul_mem _ (hmem3 (by simp)) (hmem3 (by simp)))

theorem tightHyp51TriR_of_four_le {r n : ℕ} (hr : 4 ≤ r) (hNo : NoQ16E4)
    (h4 : CIT3Below n → TightBelowR r n → Thm4RBelow r n) : TightHyp51TriR r n :=
  fun Y _ _ Rd Sd z hL M x P hF hx =>
    hyp51_triFrame_four_le hr hNo (h4 hL.below hL.tbelow) Y Rd Sd z hL M x P hF hx

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
