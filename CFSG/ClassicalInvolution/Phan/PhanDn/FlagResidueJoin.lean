module

public import CFSG.ClassicalInvolution.Phan.PhanDn.FlagResidue
public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.Defs
public import CFSG.Mathlib.Combinatorics.SimpleGraph.JoinTriangulable
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient

public section

namespace CFSG.ClassicalInvolution.PhanDn

open CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.Monster.B.Recog CFSG.StandardType CFSG.Combinatorics

variable {F K : Type} [Field F] [Field K] [Algebra F K] {σ : K ≃+* K} {m : ℕ}

@[expose] def DConn (m : ℕ) (C : Set (Fin (m + 1))) : Prop :=
  ∀ s ∈ C, ∀ t ∈ C, ∀ j, j ∉ C → ¬ DSep m j s t

theorem dLevel_ne_of_mem {J : Set (Fin (m + 1))} {j t : Fin (m + 1)} (hj : j ∈ J)
    (hjm : (j : ℕ) + 2 ≤ m) (ht : t ∉ J) : dLevel m t ≠ j := by
  intro h
  have htj : t = j := Fin.ext (by unfold dLevel at h; omega)
  exact ht (htj ▸ hj)

theorem dSep_of_level {J : Set (Fin (m + 1))} {j s t : Fin (m + 1)} (hj : j ∈ J)
    (hjm : (j : ℕ) + 2 ≤ m) (hs : s ∉ J) (ht : t ∉ J)
    (h : ¬ (dLevel m s < j ↔ dLevel m t < j)) : DSep m j s t := by
  have h₁ := dLevel_ne_of_mem hj hjm hs
  have h₂ := dLevel_ne_of_mem hj hjm ht
  refine ⟨hjm, ?_⟩
  by_cases hs' : dLevel m s < j <;> by_cases ht' : dLevel m t < j
  · exact absurd ⟨fun _ => ht', fun _ => hs'⟩ h
  · exact Or.inl ⟨hs', by omega⟩
  · exact Or.inr (Or.inl ⟨ht', by omega⟩)
  · exact absurd ⟨fun h => absurd h hs', fun h => absurd h ht'⟩ h

theorem ggCoxeterMatrixD_eq_two_of_dSep (hm : 2 ≤ m) {j s t : Fin (m + 1)} (hst : s ≠ t)
    (h : DSep m j s t) : ggCoxeterMatrixD (m + 1) s t = 2 := by
  have hst' : (s : ℕ) ≠ t := fun e => hst (Fin.ext e)
  rcases QTwo.ggCoxeterMatrixD_two_or_three s t hst with h2 | h3
  · exact h2
  · exfalso
    rw [OrthTorus.ggCoxeterMatrixD_eq_three_iff (by omega)] at h3
    obtain ⟨hj, h | h | ⟨h₁, h₂, h₃, -⟩⟩ := h <;> unfold dLevel at * <;>
      rcases h3 with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;> omega

theorem ggCoxeterMatrixD_eq_three_of_not_dSep (hm : 2 ≤ m) {s t : Fin (m + 1)} (hst : s ≠ t)
    (h : ∀ j, j ≠ s → j ≠ t → ¬ DSep m j s t) : ggCoxeterMatrixD (m + 1) s t = 3 := by
  have hst' : (s : ℕ) ≠ t := fun e => hst (Fin.ext e)
  rw [OrthTorus.ggCoxeterMatrixD_eq_three_iff (by omega)]
  by_contra hadj
  push Not at hadj
  have hs := s.is_lt
  have ht := t.is_lt
  by_cases h₁ : dLevel m s + 1 < dLevel m t
  · refine h ⟨dLevel m s + 1, by unfold dLevel at *; omega⟩ (fun e => ?_) (fun e => ?_)
      ⟨by unfold dLevel at *; simp only; omega, Or.inl ⟨by simp only; omega, by simp only; omega⟩⟩
    · have := congrArg Fin.val e
      unfold dLevel at *
      simp only at this
      omega
    · have := congrArg Fin.val e
      unfold dLevel at *
      simp only at this
      omega
  by_cases h₂ : dLevel m t + 1 < dLevel m s
  · refine h ⟨dLevel m t + 1, by unfold dLevel at *; omega⟩ (fun e => ?_) (fun e => ?_)
      ⟨by unfold dLevel at *; simp only; omega,
        Or.inr (Or.inl ⟨by simp only; omega, by simp only; omega⟩)⟩
    · have := congrArg Fin.val e
      unfold dLevel at *
      simp only at this
      omega
    · have := congrArg Fin.val e
      unfold dLevel at *
      simp only at this
      omega
  unfold dLevel at h₁ h₂
  have hs1 : m ≤ (s : ℕ) + 1 := by omega
  have ht1 : m ≤ (t : ℕ) + 1 := by omega
  refine h ⟨m - 2, by omega⟩ (fun e => ?_) (fun e => ?_) ⟨by simp only; omega,
    Or.inr (Or.inr ⟨by simp only; omega, hs1, ht1, hst⟩)⟩
  · have := congrArg Fin.val e
    simp only at this
    omega
  · have := congrArg Fin.val e
    simp only at this
    omega

theorem dSep_cut_level {J : Set (Fin (m + 1))} {j : Fin (m + 1)} (hj : j ∈ J)
    (hjm : (j : ℕ) + 2 ≤ m) (s t : Fin (m + 1)) (hs : s ∉ J) (ht : t ∉ J)
    (h : ¬ (dLevel m s < j ↔ dLevel m t < j)) : ∃ j ∈ J, DSep m j s t :=
  ⟨j, hj, dSep_of_level hj hjm hs ht h⟩

theorem dSep_cut_last {J : Set (Fin (m + 1))} {j : Fin (m + 1)} (hj : j ∈ J)
    (hjm : (j : ℕ) + 2 = m) (s t : Fin (m + 1)) (hs : s ∉ J) (ht : t ∉ J)
    (h : ¬ ((s : ℕ) = m ↔ (t : ℕ) = m)) : ∃ j ∈ J, DSep m j s t := by
  have hsj : (s : ℕ) ≠ j := fun e => hs (Fin.ext e ▸ hj)
  have htj : (t : ℕ) ≠ j := fun e => ht (Fin.ext e ▸ hj)
  have hs' := s.is_lt
  have ht' := t.is_lt
  refine ⟨j, hj, by omega, ?_⟩
  unfold dLevel
  by_cases hsm : (s : ℕ) = m
  · have htm : (t : ℕ) ≠ m := fun e => h ⟨fun _ => e, fun _ => hsm⟩
    by_cases ht1 : (t : ℕ) + 1 = m
    · exact Or.inr (Or.inr ⟨hjm, by omega, by omega, fun e => htm (e ▸ hsm)⟩)
    · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
  · have htm : (t : ℕ) = m := by
      by_contra htm
      exact h ⟨fun e => absurd e hsm, fun e => absurd e htm⟩
    by_cases hs1 : (s : ℕ) + 1 = m
    · exact Or.inr (Or.inr ⟨hjm, by omega, by omega, fun e => hsm (e ▸ htm)⟩)
    · exact Or.inl ⟨by omega, by omega⟩

theorem flagTyp_flagResidueChamber (E : QuadExt F K σ) (J : Set (Fin (m + 1)))
    {t : Fin (m + 1)} (ht : t ∉ J) : flagTyp (flagResidueChamber E J ht).1 = t :=
  flagTyp_flagChamber E t

theorem flagResidue_conn_tri_of_three (E : QuadExt F K σ) {J : Set (Fin (m + 1))}
    (P Q : Fin (m + 1) → Prop) [DecidablePred P] [DecidablePred Q]
    (hP : ∀ s t, s ∉ J → t ∉ J → ¬ (P s ↔ P t) → ∃ j ∈ J, DSep m j s t)
    (hQ : ∀ s t, s ∉ J → t ∉ J → ¬ (Q s ↔ Q t) → ∃ j ∈ J, DSep m j s t)
    {a b c : Fin (m + 1)} (ha : a ∉ J) (hb : b ∉ J) (hc : c ∉ J)
    (hab : ¬ ((P a ↔ P b) ∧ (Q a ↔ Q b))) (hbc : ¬ ((P b ↔ P c) ∧ (Q b ↔ Q c)))
    (hac : ¬ ((P a ↔ P c) ∧ (Q a ↔ Q c))) :
    (residueGraph (flagGraph σ m) flagTyp (flagChamber E m) J).Connected ∧
      Triangulable (residueGraph (flagGraph σ m) flagTyp (flagChamber E m) J) := by
  let part : residueVertex (flagGraph σ m) flagTyp (flagChamber E m) J → Bool × Bool :=
    fun x => (decide (P (flagTyp x.1)), decide (Q (flagTyp x.1)))
  have hadj : ∀ x y, part x ≠ part y →
      (residueGraph (flagGraph σ m) flagTyp (flagChamber E m) J).Adj x y := by
    intro x y h
    obtain ⟨j, hj, hsep⟩ : ∃ j ∈ J, DSep m j (flagTyp x.1) (flagTyp y.1) := by
      by_cases h₁ : (P (flagTyp x.1) ↔ P (flagTyp y.1))
      · refine hQ _ _ x.2.1 y.2.1 fun h₂ => h ?_
        simp only [part, Prod.mk.injEq, decide_eq_decide]
        exact ⟨h₁, h₂⟩
      · exact hP _ _ x.2.1 y.2.1 h₁
    exact flagResidue_adj_of_sep E hj hsep
  have key : ∀ {s t : Fin (m + 1)} (hs : s ∉ J) (ht : t ∉ J),
      ¬ ((P s ↔ P t) ∧ (Q s ↔ Q t)) →
        part (flagResidueChamber E J hs) ≠ part (flagResidueChamber E J ht) := by
    intro s t hs ht h e
    simp only [part, flagTyp_flagResidueChamber, Prod.mk.injEq, decide_eq_decide] at e
    exact h e
  exact ⟨connected_of_part part hadj (key ha hb hab),
    triangulable_of_part_three part hadj (key ha hb hab) (key hb hc hbc) (key ha hc hac)⟩

theorem flagResidue_conn_tri_of_gap (E : QuadExt F K σ) {J C : Set (Fin (m + 1))}
    (P : Fin (m + 1) → Prop) [DecidablePred P]
    (hP : ∀ s t, s ∉ J → t ∉ J → ¬ (P s ↔ P t) → ∃ j ∈ J, DSep m j s t)
    (hC : ∀ t, t ∈ C ↔ t ∉ J ∧ P t) {b : Fin (m + 1)} (hb : b ∉ J) (hbP : ¬ P b)
    (hconn : (residueGraph (flagGraph σ m) flagTyp (flagChamber E m) Cᶜ).Connected) :
    (residueGraph (flagGraph σ m) flagTyp (flagChamber E m) J).Connected ∧
      Triangulable (residueGraph (flagGraph σ m) flagTyp (flagChamber E m) J) := by
  let part : residueVertex (flagGraph σ m) flagTyp (flagChamber E m) J → Bool :=
    fun x => decide (P (flagTyp x.1))
  have hadj : ∀ x y, part x ≠ part y →
      (residueGraph (flagGraph σ m) flagTyp (flagChamber E m) J).Adj x y := by
    intro x y h
    obtain ⟨j, hj, hsep⟩ := hP _ _ x.2.1 y.2.1 fun h' => h (decide_eq_decide.2 h')
    exact flagResidue_adj_of_sep E hj hsep
  obtain ⟨e⟩ := nonempty_flagResidue_induce_iso E (J := J) (C := C)
    (fun t ht => ((hC t).1 ht).1) fun s hs t ht htC =>
      hP s t ((hC s).1 hs).1 ht fun h => htC ((hC t).2 ⟨ht, h.1 ((hC s).1 hs).2⟩)
  have hset : {x | part x = true} = {x | flagTyp x.1 ∈ C} := by
    ext x
    simp only [part, Set.mem_setOf_eq, decide_eq_true_iff]
    exact ⟨fun h => (hC _).2 ⟨x.2.1, h⟩, fun h => ((hC _).1 h).2⟩
  have hP' : ((residueGraph (flagGraph σ m) flagTyp (flagChamber E m) J).induce
      {x | part x = true}).Connected := by
    rw [hset]
    exact e.connected_iff.2 hconn
  have hb' : part (flagResidueChamber E J hb) ≠ true := by
    simp only [part, flagTyp_flagResidueChamber, ne_eq, decide_eq_true_iff]
    exact hbP
  obtain ⟨⟨a, ha⟩⟩ := hP'.nonempty
  exact ⟨connected_of_part part hadj (a := a) (b := flagResidueChamber E J hb)
      fun h => hb' (h.symm.trans ha), triangulable_of_part_connected part hadj hb' hP'⟩

theorem flagResidue_conn_tri_of_stem_stem (E : QuadExt F K σ) {J : Set (Fin (m + 1))}
    {j₁ j₂ x y z : Fin (m + 1)} (hj₁ : j₁ ∈ J) (hj₂ : j₂ ∈ J) (hj₂m : (j₂ : ℕ) + 2 ≤ m)
    (hx : x ∉ J) (hy : y ∉ J) (hz : z ∉ J) (hxj : dLevel m x < j₁)
    (hjy : (j₁ : ℕ) < dLevel m y) (hyj : dLevel m y < j₂) (hjz : (j₂ : ℕ) < dLevel m z) :
    (residueGraph (flagGraph σ m) flagTyp (flagChamber E m) J).Connected ∧
      Triangulable (residueGraph (flagGraph σ m) flagTyp (flagChamber E m) J) :=
  flagResidue_conn_tri_of_three E (fun v => dLevel m v < j₁) (fun v => dLevel m v < j₂)
    (dSep_cut_level hj₁ (by omega)) (dSep_cut_level hj₂ hj₂m) hx hy hz
    (fun h => absurd (h.1.1 hxj) (by omega)) (fun h => absurd (h.2.1 hyj) (by omega))
    (fun h => absurd (h.2.1 (by omega)) (by omega))

theorem flagResidue_conn_tri_of_stem_fork (E : QuadExt F K σ) {J : Set (Fin (m + 1))}
    {j₁ j₂ x s t : Fin (m + 1)} (hj₁ : j₁ ∈ J) (hj₁m : (j₁ : ℕ) + 2 ≤ m) (hj₂ : j₂ ∈ J)
    (hj₂m : (j₂ : ℕ) + 2 = m) (hx : x ∉ J) (hs : s ∉ J) (ht : t ∉ J)
    (hxj : dLevel m x < j₁) (hs1 : m ≤ (s : ℕ) + 1) (ht1 : m ≤ (t : ℕ) + 1) (hst : s ≠ t) :
    (residueGraph (flagGraph σ m) flagTyp (flagChamber E m) J).Connected ∧
      Triangulable (residueGraph (flagGraph σ m) flagTyp (flagChamber E m) J) := by
  have hst' : (s : ℕ) ≠ t := fun e => hst (Fin.ext e)
  have hs' := s.is_lt
  have ht' := t.is_lt
  have hls : dLevel m s = m - 1 := by unfold dLevel; omega
  have hlt : dLevel m t = m - 1 := by unfold dLevel; omega
  refine flagResidue_conn_tri_of_three E (fun v => dLevel m v < j₁) (fun v => (v : ℕ) = m)
    (dSep_cut_level hj₁ hj₁m) (dSep_cut_last hj₂ hj₂m) hx hs ht
    (fun h => absurd (h.1.1 hxj) (by omega)) (fun h => ?_)
    (fun h => absurd (h.1.1 hxj) (by omega))
  by_cases hsm : (s : ℕ) = m
  · exact absurd (h.2.1 hsm) (by omega)
  · exact hsm (h.2.2 (by omega))

theorem flagResidue_conn_tri_of_model (E : QuadExt F K σ) (hm : 3 ≤ m)
    (hmodel : ∀ C : Set (Fin (m + 1)), DConn m C → Cᶜ.Nonempty → 3 ≤ C.ncard →
      (residueGraph (flagGraph σ m) flagTyp (flagChamber E m) Cᶜ).Connected ∧
        (4 ≤ C.ncard →
          Triangulable (residueGraph (flagGraph σ m) flagTyp (flagChamber E m) Cᶜ)))
    {J : Set (Fin (m + 1))} (hJ : J.Nonempty)
    (hJS : Jᶜ ∉ QTwo.qTwoShape (ggCoxeterMatrixD (m + 1))) :
    (residueGraph (flagGraph σ m) flagTyp (flagChamber E m) J).Connected ∧
      Triangulable (residueGraph (flagGraph σ m) flagTyp (flagChamber E m) J) := by
  classical
  have hS : 4 ≤ Jᶜ.ncard ∧ ¬ QTwo.IsA2A2 (ggCoxeterMatrixD (m + 1)) Jᶜ := by
    obtain ⟨j₀, hj₀⟩ := hJ
    have hne : Jᶜ ≠ Set.univ := fun h => (Set.mem_compl_iff J j₀).1 (h ▸ Set.mem_univ j₀) hj₀
    by_contra hcon
    refine hJS ⟨hne, ?_⟩
    by_cases h3 : Jᶜ.ncard ≤ 3
    · exact Or.inl h3
    · exact Or.inr (by_contra fun hA => hcon ⟨by omega, hA⟩)
  by_cases hconn : DConn m Jᶜ
  · have h := hmodel Jᶜ hconn (by rwa [compl_compl]) (by omega)
    rw [compl_compl] at h
    exact ⟨h.1, h.2 hS.1⟩
  have stem : ∀ j ∈ J, (j : ℕ) + 2 ≤ m → ∀ s t, s ∉ J → t ∉ J → dLevel m s < j →
      (j : ℕ) < dLevel m t →
      (residueGraph (flagGraph σ m) flagTyp (flagChamber E m) J).Connected ∧
        Triangulable (residueGraph (flagGraph σ m) flagTyp (flagChamber E m) J) := by
    intro j hj hjm s t hs ht hsj hjt
    obtain ⟨B, hB⟩ : ∃ B : Set (Fin (m + 1)), ∀ u, u ∈ B ↔ u ∉ J ∧ dLevel m u < j :=
      ⟨_, fun _ => Iff.rfl⟩
    obtain ⟨A, hA⟩ : ∃ A : Set (Fin (m + 1)), ∀ u, u ∈ A ↔ u ∉ J ∧ ¬ dLevel m u < j :=
      ⟨_, fun _ => Iff.rfl⟩
    have hcut := dSep_cut_level hj hjm
    have hBj : Bᶜ.Nonempty := ⟨j, fun h => ((hB j).1 h).1 hj⟩
    have hAj : Aᶜ.Nonempty := ⟨j, fun h => ((hA j).1 h).1 hj⟩
    by_cases hBc : DConn m B ∧ 3 ≤ B.ncard
    · exact flagResidue_conn_tri_of_gap E (fun v => dLevel m v < j) hcut hB ht
        (not_lt.2 hjt.le) (hmodel B hBc.1 hBj hBc.2).1
    by_cases hAc : DConn m A ∧ 3 ≤ A.ncard
    · exact flagResidue_conn_tri_of_gap E (fun v => ¬ dLevel m v < j)
        (fun s t hs ht h => hcut s t hs ht fun h' => h (not_congr h')) hA hs (not_not.2 hsj)
        (hmodel A hAc.1 hAj hAc.2).1
    by_cases hBd : DConn m B
    swap
    · unfold DConn at hBd
      push Not at hBd
      obtain ⟨x, hx, y, hy, j', hj', hxy⟩ := hBd
      obtain ⟨hxJ, hxl⟩ := (hB x).1 hx
      obtain ⟨hyJ, hyl⟩ := (hB y).1 hy
      have hj'J : j' ∈ J := by
        by_contra h
        refine hj' ((hB j').2 ⟨h, ?_⟩)
        obtain ⟨hj'm, h | h | ⟨-, h₁, -⟩⟩ := hxy <;> unfold dLevel at * <;> omega
      obtain ⟨hj'm, h | h | ⟨-, h₁, -⟩⟩ := hxy
      · exact flagResidue_conn_tri_of_stem_stem E hj'J hj hjm hxJ hyJ ht h.1 h.2 hyl hjt
      · exact flagResidue_conn_tri_of_stem_stem E hj'J hj hjm hyJ hxJ ht h.1 h.2 hxl hjt
      · exfalso
        unfold dLevel at hxl
        omega
    by_cases hAd : DConn m A
    swap
    · unfold DConn at hAd
      push Not at hAd
      obtain ⟨x, hx, y, hy, j', hj', hxy⟩ := hAd
      obtain ⟨hxJ, hxl⟩ := (hA x).1 hx
      obtain ⟨hyJ, hyl⟩ := (hA y).1 hy
      have hxl' : (j : ℕ) < dLevel m x :=
        lt_of_le_of_ne (not_lt.1 hxl) (dLevel_ne_of_mem hj hjm hxJ).symm
      have hyl' : (j : ℕ) < dLevel m y :=
        lt_of_le_of_ne (not_lt.1 hyl) (dLevel_ne_of_mem hj hjm hyJ).symm
      have hj'J : j' ∈ J := by
        by_contra h
        refine hj' ((hA j').2 ⟨h, ?_⟩)
        obtain ⟨hj'm, h | h | ⟨h₀, -⟩⟩ := hxy <;> unfold dLevel at * <;> omega
      obtain ⟨hj'm, h | h | ⟨h₀, h₁, h₂, h₃⟩⟩ := hxy
      · exact flagResidue_conn_tri_of_stem_stem E hj hj'J hj'm hs hxJ hyJ hsj hxl' h.1 h.2
      · exact flagResidue_conn_tri_of_stem_stem E hj hj'J hj'm hs hyJ hxJ hsj hyl' h.1 h.2
      · exact flagResidue_conn_tri_of_stem_fork E hj hjm hj'J h₀ hs hxJ hyJ hsj h₁ h₂ h₃
    exfalso
    have hunion : Jᶜ = B ∪ A := by
      ext u
      simp only [Set.mem_compl_iff, Set.mem_union, hB, hA]
      tauto
    have hdisj : Disjoint B A :=
      Set.disjoint_left.2 fun u hu hu' => ((hA u).1 hu').2 ((hB u).1 hu).2
    have hcard := Set.ncard_union_eq hdisj (Set.toFinite B) (Set.toFinite A)
    rw [← hunion] at hcard
    have h1 : ¬ 3 ≤ B.ncard := fun h => hBc ⟨hBd, h⟩
    have h2 : ¬ 3 ≤ A.ncard := fun h => hAc ⟨hAd, h⟩
    have hB2 : B.ncard = 2 := by have := hS.1; omega
    have hA2 : A.ncard = 2 := by have := hS.1; omega
    have cross : ∀ b ∈ B, ∀ a ∈ A, ggCoxeterMatrixD (m + 1) b a = 2 := by
      intro b hb a ha
      obtain ⟨hbJ, hbl⟩ := (hB b).1 hb
      obtain ⟨haJ, hal⟩ := (hA a).1 ha
      exact ggCoxeterMatrixD_eq_two_of_dSep (by omega) (fun e => hal (e ▸ hbl))
        (dSep_of_level hj hjm hbJ haJ fun h => hal (h.1 hbl))
    obtain ⟨b₁, b₂, hb, rfl⟩ := Set.ncard_eq_two.1 hB2
    obtain ⟨a₁, a₂, ha, rfl⟩ := Set.ncard_eq_two.1 hA2
    refine hS.2 ⟨b₁, b₂, a₁, a₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hunion]
      ext u
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc]
    · exact ggCoxeterMatrixD_eq_three_of_not_dSep (by omega) hb fun j' h₁ h₂ =>
        hBd b₁ (by simp) b₂ (by simp) j' (by simp [h₁, h₂])
    · exact ggCoxeterMatrixD_eq_three_of_not_dSep (by omega) ha fun j' h₁ h₂ =>
        hAd a₁ (by simp) a₂ (by simp) j' (by simp [h₁, h₂])
    · exact cross _ (by simp) _ (by simp)
    · exact cross _ (by simp) _ (by simp)
    · exact cross _ (by simp) _ (by simp)
    · exact cross _ (by simp) _ (by simp)
  unfold DConn at hconn
  push Not at hconn
  obtain ⟨s, hs, t, ht, j, hj, hsep⟩ := hconn
  have hs : s ∉ J := hs
  have ht : t ∉ J := ht
  have hj : j ∈ J := by simpa using hj
  obtain ⟨hjm, h | h | ⟨hj2, hs1, ht1, hst⟩⟩ := hsep
  · exact stem j hj hjm s t hs ht h.1 h.2
  · exact stem j hj hjm t s ht hs h.1 h.2
  obtain ⟨u, hu, hus, hut⟩ : ∃ u, u ∉ J ∧ u ≠ s ∧ u ≠ t := by
    by_contra hcon
    push Not at hcon
    have hsub : Jᶜ ⊆ {s, t} := fun u hu => by
      rw [Set.mem_insert_iff, Set.mem_singleton_iff]
      by_cases hus : u = s
      · exact Or.inl hus
      · exact Or.inr (hcon u hu hus)
    have := (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_pair hst).le
    have := hS.1
    omega
  have hus' : (u : ℕ) ≠ s := fun e => hus (Fin.ext e)
  have hut' : (u : ℕ) ≠ t := fun e => hut (Fin.ext e)
  have hst' : (s : ℕ) ≠ t := fun e => hst (Fin.ext e)
  have huj : (u : ℕ) ≠ j := fun e => hu (Fin.ext e ▸ hj)
  have hu' := u.is_lt
  have hs' := s.is_lt
  have ht' := t.is_lt
  exact flagResidue_conn_tri_of_stem_fork E hj (by omega) hj hj2 hu hs ht
    (by unfold dLevel; omega) hs1 ht1 hst

theorem DConn.cases (hm : 2 ≤ m) {C : Set (Fin (m + 1))} (hC : DConn m C) (hCu : Cᶜ.Nonempty)
    (h2 : 2 ≤ C.ncard) :
    (∃ a b : ℕ, a ≤ b ∧ b + 2 ≤ m ∧ C = {t : Fin (m + 1) | a ≤ (t : ℕ) ∧ (t : ℕ) ≤ b}) ∨
      (∃ a : ℕ, a + 1 ≤ m ∧ C = {t : Fin (m + 1) | a ≤ (t : ℕ) ∧ (t : ℕ) + 1 ≤ m}) ∨
      (∃ a : ℕ, a + 1 ≤ m ∧ C = {t : Fin (m + 1) | a ≤ (t : ℕ) ∧ ((t : ℕ) + 2 ≤ m ∨ (t : ℕ) = m)}) ∨
      ∃ k : ℕ, 1 ≤ k ∧ k + 2 ≤ m ∧ C = {t : Fin (m + 1) | k ≤ (t : ℕ)} := by
  classical
  have hne : C.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨a, haC, ha⟩ := C.toFinset.exists_min_image (fun t : Fin (m + 1) => (t : ℕ))
    (Set.toFinset_nonempty.2 hne)
  obtain ⟨b, hbC, hb⟩ := C.toFinset.exists_max_image (fun t : Fin (m + 1) => (t : ℕ))
    (Set.toFinset_nonempty.2 hne)
  rw [Set.mem_toFinset] at haC hbC
  have ha' : ∀ t ∈ C, (a : ℕ) ≤ t := fun t ht => ha t (Set.mem_toFinset.2 ht)
  have hb' : ∀ t ∈ C, (t : ℕ) ≤ b := fun t ht => hb t (Set.mem_toFinset.2 ht)
  have hval : ∀ t u : Fin (m + 1), (t : ℕ) = u → u ∈ C → t ∈ C := fun t u h hu =>
    (Fin.ext h : t = u) ▸ hu
  have hmid : ∀ t : Fin (m + 1), (a : ℕ) ≤ t → (t : ℕ) + 2 ≤ m → ∀ s ∈ C,
      (t : ℕ) < dLevel m s → t ∈ C := by
    intro t hat htm s hs hts
    rcases eq_or_lt_of_le hat with h | h
    · exact hval t a h.symm haC
    · by_contra ht
      exact hC a haC s hs t ht ⟨htm, Or.inl ⟨by unfold dLevel; omega, hts⟩⟩
  obtain ⟨s₁, hs₁⟩ : ∃ s : Fin (m + 1), (s : ℕ) = m - 1 := ⟨⟨m - 1, by omega⟩, rfl⟩
  obtain ⟨s₂, hs₂⟩ : ∃ s : Fin (m + 1), (s : ℕ) = m := ⟨Fin.last m, rfl⟩
  have hl₁ : dLevel m s₁ = m - 1 := by unfold dLevel; omega
  have hl₂ : dLevel m s₂ = m - 1 := by unfold dLevel; omega
  have hlt : ∀ t : Fin (m + 1), (t : ℕ) < m + 1 := fun t => t.is_lt
  by_cases h₁ : s₁ ∈ C <;> by_cases h₂ : s₂ ∈ C
  ·
    obtain ⟨s₀, hs₀⟩ : ∃ s : Fin (m + 1), (s : ℕ) = m - 2 := ⟨⟨m - 2, by omega⟩, rfl⟩
    have h₀ : s₀ ∈ C := by
      by_contra h
      exact hC s₁ h₁ s₂ h₂ s₀ h ⟨by omega, Or.inr (Or.inr ⟨by omega, by omega, by omega,
        fun e => by have := congrArg Fin.val e; omega⟩)⟩
    have hseg : C = {t : Fin (m + 1) | (a : ℕ) ≤ t} := by
      ext t
      refine ⟨fun ht => ha' t ht, fun ht => ?_⟩
      by_cases htm : (t : ℕ) + 2 ≤ m
      · exact hmid t ht htm s₂ h₂ (by omega)
      · by_cases ht₂ : (t : ℕ) = m
        · exact hval t s₂ (by omega) h₂
        · exact hval t s₁ (by have := hlt t; omega) h₁
    refine Or.inr (Or.inr (Or.inr ⟨a, ?_, by have := ha' s₀ h₀; omega, hseg⟩))
    by_contra h0
    obtain ⟨u, hu⟩ := hCu
    exact hu (by rw [hseg]; show (a : ℕ) ≤ u; omega)
  ·
    refine Or.inr (Or.inl ⟨a, by have := ha' s₁ h₁; omega, ?_⟩)
    ext t
    refine ⟨fun ht => ⟨ha' t ht, ?_⟩, fun ht => ?_⟩
    · have := hlt t
      by_contra h
      exact h₂ (hval s₂ t (by omega) ht)
    · by_cases htm : (t : ℕ) + 2 ≤ m
      · exact hmid t ht.1 htm s₁ h₁ (by omega)
      · have := ht.2
        exact hval t s₁ (by omega) h₁
  ·
    have ham : (a : ℕ) + 1 ≤ m := by
      by_contra h
      have hsub : C ⊆ {s₂} := fun t ht => by
        have := ha' t ht
        have := hlt t
        rw [Set.mem_singleton_iff]
        exact Fin.ext (by omega)
      have := (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_singleton s₂).le
      omega
    refine Or.inr (Or.inr (Or.inl ⟨a, ham, ?_⟩))
    ext t
    refine ⟨fun ht => ⟨ha' t ht, ?_⟩, fun ht => ?_⟩
    · have := hlt t
      by_contra h
      exact h₁ (hval s₁ t (by omega) ht)
    · rcases ht with ⟨hat, htm | htm⟩
      · exact hmid t hat htm s₂ h₂ (by omega)
      · exact hval t s₂ (by omega) h₂
  ·
    have hbm : (b : ℕ) + 2 ≤ m := by
      have := hlt b
      by_contra h
      by_cases hb₂ : (b : ℕ) = m
      · exact h₂ (hval s₂ b (by omega) hbC)
      · exact h₁ (hval s₁ b (by omega) hbC)
    refine Or.inl ⟨a, b, ha' b hbC, hbm, ?_⟩
    ext t
    refine ⟨fun ht => ⟨ha' t ht, hb' t ht⟩, fun ht => ?_⟩
    rcases eq_or_lt_of_le ht.2 with h | h
    · exact hval t b h hbC
    · exact hmid t ht.1 (by omega) b hbC (by unfold dLevel; omega)

end CFSG.ClassicalInvolution.PhanDn
