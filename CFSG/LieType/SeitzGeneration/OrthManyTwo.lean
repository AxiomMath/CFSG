module

public import CFSG.LieType.SeitzGeneration.OrthManyTwoPairs

public section

namespace CFSG.LieType.SeitzGeneration

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical CFSG.Open OrthNS OrthBlk
open CFSG.RankThree.Classical2 (orthDerived)

section Helpers

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem manyTwo_finrank_iSup_fin_le {n : ℕ} (P : Fin n → Submodule K V) :
    finrank K ↥(⨆ i, P i) ≤ ∑ i, finrank K ↥(P i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : (⨆ i : Fin (n + 1), P i) = (⨆ i : Fin n, P i.castSucc) ⊔ P (Fin.last n) := by
      apply le_antisymm
      · refine iSup_le fun i => ?_
        refine Fin.lastCases ?_ (fun j => ?_) i
        · exact le_sup_right
        · exact le_sup_of_le_left (le_iSup (fun i : Fin n => P i.castSucc) j)
      · exact sup_le (iSup_le fun j => le_iSup P j.castSucc) (le_iSup P (Fin.last n))
    rw [h1, Fin.sum_univ_castSucc]
    calc finrank K ↥((⨆ i : Fin n, P i.castSucc) ⊔ P (Fin.last n))
        ≤ finrank K ↥(⨆ i : Fin n, P i.castSucc) + finrank K ↥(P (Fin.last n)) :=
          Submodule.finrank_add_le_finrank_add_finrank _ _
      _ ≤ _ := Nat.add_le_add_right (ih (fun i => P i.castSucc)) _

omit [Finite K] [FiniteDimensional K V] in
theorem manyTwo_orthSep_sup_left {S S' T : Submodule K V} (h : OrthSep Q S T)
    (h' : OrthSep Q S' T) : OrthSep Q (S ⊔ S') T := by
  intro x hx t ht
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
  rw [polar_add_left, h a ha t ht, h' b hb t ht, add_zero]

omit [Finite K] [FiniteDimensional K V] in
theorem manyTwo_orthSep_sup_right {S T T' : Submodule K V} (h : OrthSep Q S T)
    (h' : OrthSep Q S T') : OrthSep Q S (T ⊔ T') :=
  (manyTwo_orthSep_sup_left h.symm h'.symm).symm

theorem manyTwo_exists_fin_notMem {n m : ℕ} (hn : m < n) (S : Finset (Fin n)) (hS : S.card ≤ m) :
    ∃ l : Fin n, l ∉ S := by
  by_contra hcon
  push Not at hcon
  have : S = Finset.univ := Finset.eq_univ_of_forall hcon
  rw [this, Finset.card_univ, Fintype.card_fin] at hS
  omega

theorem manyTwo_subset_rootSet_of_pivot {H : Subgroup (V ≃ₗ[K] V)}
    (hH : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q) {Y : Submodule K V}
    (hY : PolarNondegOn Q Y) (hY3 : 3 ≤ finrank K Y) (h2 : finrank K Y = 3 → (2 : K) ≠ 0)
    (hYH : ∀ e ∈ Y, ∀ w ∈ Y, eichler Q e w ∈ H) {s : V} (hs : ∀ y ∈ Y, polar Q s y = 0)
    (hmix : ∃ w ∈ rootSet Q H s, ∃ y ∈ Y, ∃ r : V, w = y + r ∧ (∀ z ∈ Y, polar Q z r = 0) ∧
      y ≠ 0) :
    ∀ y ∈ Y, y ∈ rootSet Q H s := by
  by_cases h4 : 4 ≤ finrank K Y
  · obtain ⟨w, hw, y, hyY, r, hwyr, hr, hy0⟩ := hmix
    obtain ⟨e, heY, f, hfY, hne⟩ := exists_eichler_apply_ne hY hY3 hyY hy0
    exact subset_rootSet_of_mixed hH hY h4 hYH hs ⟨w, hw, y, hyY, r, hwyr, hr, e, heY, f, hfY, hne⟩
  · exact subset_rootSet_of_mixed_three (h2 (by omega)) hH hY (by omega) hYH hs hmix

end Helpers

section Main

theorem closure_eq_top_of_noSingular_two {K V : Type} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (Q : QuadraticForm K V)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) (hdim : 7 ≤ finrank K V)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpl : p ≠ ringChar K) (E : Subgroup (orthDerived Q))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E = p ^ 2) (hNS : OrthNoInvariantSingular Q E)
    (h2 : orderOf ((Nat.card K : ℕ) : ZMod p) = 2) :
    Subgroup.closure {h : orthDerived Q | ∃ x ∈ E, x ≠ 1 ∧ h * x = x * h} = ⊤ := by
  classical
  have hp2 : p ≠ 2 := by omega
  haveI : Nontrivial V := nontrivial_of_three_singular hT
  obtain ⟨hK, -⟩ := exists_kernelLineData_of_le hQ hp hp2 hpl E hcomm hexp hcard
  obtain ⟨n, P, hP, hPP, hPV, hPsp⟩ :=
    exists_piece_decomposition hQ hp hp2 hpl E hcomm hexp hcard hNS
  choose M hMc hMP hMk hMf _ _ using fun i => (hP i).exists_line hK hp hp2 hpl
  obtain ⟨a, b, hab⟩ := exists_pieces_diff_lines hK hp hpl hP hPsp (M := M)
    fun i => ⟨hMc i, hMP i⟩
  have hab' : a ≠ b := fun h => hab (h ▸ rfl)
  have hEΩ : elementaryGroup Q ≤ orthDerived Q := (orthDerived_eq_and_le_closure hQ hT).1.ge
  have hH : orthCentralizerSpan Q E ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthCentralizerSpan_le_orthogonalGroup E
  have hdimP : ∀ i, finrank K (P i) = 2 := fun i => (hMf i).trans h2
  have hV0reg : PolarNondegOn Q (planeFixSpace E) := polarNondegOn_planeFixSpace hK
  have haniso : ∀ i, ∀ t ∈ P i, Q t = 0 → t = 0 := fun i =>
    (hP i).anisotropic_of_orderOf_two hK hp hp5 hpl h2
  have hK3 : 3 ≤ Nat.card K := by
    by_contra hlt
    push Not at hlt
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    have hq : Nat.card K = 2 := by omega
    rw [hq] at h2
    have hsq : ((2 : ℕ) : ZMod p) ^ 2 = 1 := by
      have := pow_orderOf_eq_one ((2 : ℕ) : ZMod p)
      rwa [h2] at this
    have h3 : ((3 : ℕ) : ZMod p) = 0 := by
      have : ((3 : ℕ) : ZMod p) = ((2 : ℕ) : ZMod p) ^ 2 - 1 := by push_cast; ring
      rw [this, hsq, sub_self]
    have := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff 3 p).mp h3)
    omega
  have hV02 : finrank K (planeFixSpace E) ≤ 2 := finrank_planeFixSpace_le_two hNS
  have hcount : 7 ≤ finrank K (planeFixSpace E) + 2 * n := by
    have h1 : finrank K V ≤ finrank K ↥(planeFixSpace E ⊔ ⨆ i, P i) := by
      rw [← finrank_top K V]
      exact Submodule.finrank_mono hPsp
    have h3 := Submodule.finrank_add_le_finrank_add_finrank (planeFixSpace E) (⨆ i, P i)
    have h4 := manyTwo_finrank_iSup_fin_le P
    simp only [hdimP, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h4
    omega
  have hEichPair : ∀ i j : Fin n, i ≠ j → ∀ e ∈ P i ⊔ P j, ∀ w ∈ P i ⊔ P j,
      eichler Q e w ∈ orthCentralizerSpan Q E := by
    intro i j hij
    by_cases hM : M i = M j
    · have hle : P i ⊔ P j ≤ planeFixSpace E ⊔ lineSpace (M i) := by
        refine sup_le ((hMP i).trans le_sup_right) ?_
        rw [hM]
        exact (hMP j).trans le_sup_right
      exact fun e he w hw => eichler_mem_span_of_mem_sup hEΩ
        (ne_bot_of_card_prime hp (hMc i)) (hle he) (hle hw)
    · exact eichler_mem_of_pair_pieces hQ hp hK hEΩ hNS (hMc i) (hMc j) hM (hP i) (hP j)
        (hMP i) (hMP j) (hPP i j hij) h2
  have hY : ∀ k : Fin n, k ≠ a → k ≠ b → ∃ Y : Submodule K V, P k ≤ Y ∧
      (planeFixSpace E ≠ ⊥ → planeFixSpace E ≤ Y) ∧ OrthSep Q Y (P a ⊔ P b) ∧
      PolarNondegOn Q Y ∧ (∀ e ∈ Y, ∀ w ∈ Y, eichler Q e w ∈ orthCentralizerSpan Q E) ∧
      3 ≤ finrank K Y ∧ (finrank K Y = 3 → (2 : K) ≠ 0) := by
    intro k hka hkb
    have hkab : OrthSep Q (P k) (P a ⊔ P b) :=
      manyTwo_orthSep_sup_right (hPP k a hka) (hPP k b hkb)
    by_cases hV0 : planeFixSpace E = ⊥
    ·
      have hn4 : 4 ≤ n := by
        have : finrank K (planeFixSpace E) = 0 := by rw [hV0]; exact finrank_bot K V
        omega
      obtain ⟨l, hl⟩ := manyTwo_exists_fin_notMem (S := {a, b, k}) (m := 3) (by omega)
        Finset.card_le_three
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
      obtain ⟨hla, hlb, hlk⟩ := hl
      have hkl : OrthSep Q (P k) (P l) := hPP k l (Ne.symm hlk)
      have hlab : OrthSep Q (P l) (P a ⊔ P b) :=
        manyTwo_orthSep_sup_right (hPP l a hla) (hPP l b hlb)
      have hdisj := OrthSep.disjoint (hP k).regular hkl
      have hdimY : finrank K ↥(P k ⊔ P l) = 4 := by
        have := Submodule.finrank_sup_add_finrank_inf_eq (P k) (P l)
        rw [hdisj.eq_bot, finrank_bot, add_zero, hdimP k, hdimP l] at this
        omega
      exact ⟨P k ⊔ P l, le_sup_left, fun h => absurd hV0 h, manyTwo_orthSep_sup_left hkab hlab,
        polarNondegOn_sup (hP k).regular (hP l).regular hkl,
        hEichPair k l (Ne.symm hlk), by omega, fun h => absurd h (by omega)⟩
    ·
      have hd0 : 1 ≤ finrank K (planeFixSpace E) := Submodule.one_le_finrank_iff.mpr hV0
      have hdisj := (hP k).disjoint.symm
      have hdimY : finrank K ↥(planeFixSpace E ⊔ P k) = finrank K (planeFixSpace E) + 2 := by
        have := Submodule.finrank_sup_add_finrank_inf_eq (planeFixSpace E) (P k)
        rw [hdisj.eq_bot, finrank_bot, add_zero, hdimP k] at this
        omega
      have hle : planeFixSpace E ⊔ P k ≤ planeFixSpace E ⊔ lineSpace (M k) :=
        sup_le le_sup_left ((hMP k).trans le_sup_right)
      refine ⟨planeFixSpace E ⊔ P k, le_sup_right, fun _ => le_sup_left,
        manyTwo_orthSep_sup_left (manyTwo_orthSep_sup_right (hPV a) (hPV b)) hkab,
        polarNondegOn_sup hV0reg (hP k).regular (hPV k),
        fun e he w hw => eichler_mem_span_of_mem_sup hEΩ (ne_bot_of_card_prime hp (hMc k))
          (hle he) (hle hw), by omega, fun h3 => ?_⟩
      exact two_ne_zero_of_finrank_planeFixSpace hK (by omega)
  have hRoot : ∀ s ∈ P a ⊔ P b, s ≠ 0 → Q s = 0 →
      IsRootCenter Q (orthCentralizerSpan Q E) s := by
    intro s hs hs0 hsQ
    have hrel : ∀ w ∈ P a ⊔ P b, polar Q s w = 0 → w ∈ rootSet Q (orthCentralizerSpan Q E) s :=
      fun w hw hsw => ⟨hsw, hEichPair a b hab' s hs w hw⟩
    have hYR : ∀ k : Fin n, k ≠ a → k ≠ b → ∃ Y : Submodule K V, P k ≤ Y ∧
        (planeFixSpace E ≠ ⊥ → planeFixSpace E ≤ Y) ∧
        ∀ y ∈ Y, y ∈ rootSet Q (orthCentralizerSpan Q E) s := by
      intro k hka hkb
      obtain ⟨Y, hPY, hV0Y, hYP, hYreg, hYH, hY3, h2Y⟩ := hY k hka hkb
      have hsY : ∀ y ∈ Y, polar Q s y = 0 := fun y hy => by
        rw [polar_comm]
        exact hYP y hy s hs
      have hmix := exists_mixed_vector hH (hP a).regular (hP b).regular (hP k).regular
        (hPP a b hab') (hPP a k (Ne.symm hka)) (hPP b k (Ne.symm hkb)) (hdimP a) (hdimP b)
        (hdimP k) (haniso a) (haniso b) (haniso k) hK3 hPY hYP
        (hEichPair b k (Ne.symm hkb)) hs hs0 hsQ hrel
      exact ⟨Y, hPY, hV0Y, manyTwo_subset_rootSet_of_pivot hH hYreg hY3 h2Y hYH hsY hmix⟩
    refine ⟨hs0, hsQ, fun w hsw => ?_⟩
    have hspan : (⊤ : Submodule K V) ≤ (P a ⊔ P b) ⊔
        (planeFixSpace E ⊔ ⨆ k : {k : Fin n // k ≠ a ∧ k ≠ b}, P k.1) := by
      refine hPsp.trans (sup_le ?_ (iSup_le fun i => ?_))
      · exact le_sup_of_le_right le_sup_left
      · by_cases hia : i = a
        · rw [hia]
          exact le_sup_of_le_left le_sup_left
        by_cases hib : i = b
        · rw [hib]
          exact le_sup_of_le_left le_sup_right
        · exact le_sup_of_le_right (le_sup_of_le_right
            (le_iSup (fun k : {k : Fin n // k ≠ a ∧ k ≠ b} => P k.1) ⟨i, hia, hib⟩))
    obtain ⟨w₁, hw₁, z, hz, rfl⟩ := Submodule.mem_sup.mp (hspan (Submodule.mem_top (x := w)))
    have hzR : polar Q s z = 0 ∧ z ∈ rootSet Q (orthCentralizerSpan Q E) s := by
      obtain ⟨v₀, hv₀, z', hz', rfl⟩ := Submodule.mem_sup.mp hz
      have hv₀perp : polar Q s v₀ = 0 := by
        rw [polar_comm]
        exact manyTwo_orthSep_sup_right (hPV a) (hPV b) v₀ hv₀ s hs
      have hz'R : polar Q s z' = 0 ∧ z' ∈ rootSet Q (orthCentralizerSpan Q E) s := by
        refine Submodule.iSup_induction (fun k : {k : Fin n // k ≠ a ∧ k ≠ b} => P k.1)
          (motive := fun x => polar Q s x = 0 ∧ x ∈ rootSet Q (orthCentralizerSpan Q E) s) hz'
          ?_ ⟨polar_zero_right Q s, AddSubgroup.zero_mem _⟩ ?_
        · rintro ⟨k, hka, hkb⟩ x hx
          obtain ⟨Y, hPY, -, hYR'⟩ := hYR k hka hkb
          refine ⟨?_, hYR' x (hPY hx)⟩
          rw [polar_comm]
          exact manyTwo_orthSep_sup_right (hPP k a hka) (hPP k b hkb) x hx s hs
        · rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
          exact ⟨by rw [polar_add_right, hx1, hy1, add_zero], AddSubgroup.add_mem _ hx2 hy2⟩
      have hv₀R : v₀ ∈ rootSet Q (orthCentralizerSpan Q E) s := by
        by_cases hV0 : planeFixSpace E = ⊥
        · rw [hV0] at hv₀
          rw [(Submodule.mem_bot K).mp hv₀]
          exact AddSubgroup.zero_mem _
        · have hn3 : 2 < n := by omega
          obtain ⟨k, hk⟩ := manyTwo_exists_fin_notMem (S := {a, b}) (m := 2) hn3 Finset.card_le_two
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
          obtain ⟨Y, -, hV0Y, hYR'⟩ := hYR k hk.1 hk.2
          exact hYR' v₀ (hV0Y hV0 hv₀)
      exact ⟨by rw [polar_add_right, hv₀perp, hz'R.1, add_zero],
        AddSubgroup.add_mem _ hv₀R hz'R.2⟩
    have hw₁perp : polar Q s w₁ = 0 := by
      rw [polar_add_right, hzR.1, add_zero] at hsw
      exact hsw
    exact (AddSubgroup.add_mem _ (hrel w₁ hw₁ hw₁perp) hzR.2).2
  have hXreg : PolarNondegOn Q (P a ⊔ P b) :=
    polarNondegOn_sup (hP a).regular (hP b).regular (hPP a b hab')
  have hX3 : 3 ≤ finrank K ↥(P a ⊔ P b) := by
    have hdisj := OrthSep.disjoint (hP a).regular (hPP a b hab')
    have := Submodule.finrank_sup_add_finrank_inf_eq (P a) (P b)
    rw [hdisj.eq_bot, finrank_bot, add_zero, hdimP a, hdimP b] at this
    omega
  obtain ⟨u, huX, hu0, huQ⟩ := exists_singular_of_three_le_any (Q := Q) hX3
  obtain ⟨u', hu'X, hu'Q, huu'⟩ := exists_partner_of_polarNondegOn hXreg huX hu0 huQ
  have hu'0 : u' ≠ 0 := fun h0 => by
    rw [h0, polar_zero_right] at huu'
    exact zero_ne_one huu'
  have hle : elementaryGroup Q ≤ orthCentralizerSpan Q E :=
    elementaryGroup_le_of_hypPair hQ hH ⟨u, u', huQ, hu'Q, huu'⟩ (hRoot u huX hu0 huQ)
      (hRoot u' hu'X hu'0 hu'Q)
  exact closure_centralizers_eq_top_of_le E
    ((orthDerived_eq_and_le_closure hQ hT).1.le.trans hle)

end Main

end CFSG.LieType.SeitzGeneration
