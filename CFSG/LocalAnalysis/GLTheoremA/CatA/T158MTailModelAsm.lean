module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MTailRankTE6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShDefs
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA

private theorem three_dvd_two_pow_add_one {n : ℕ} (hn : Odd n) : 3 ∣ 2 ^ n + 1 := by
  simpa using Odd.nat_add_dvd_pow_add_pow (x := 2) (y := 1) (n := n) hn

theorem catalogIs_setupLU_of_isU6n {S : Type} [Group S] {n : ℕ} (hn : Odd n) (h : catalogIs S (S10.isU6n n)) :
    catalogIs S (onLie fun i => ∃ q, (i = .A (6 - 1) q ∨ i = .twistedA (6 - 1) q) ∧ I171.I171LieShape 3 i) := by
  refine catalogIs_imp (fun i hi => ?_) h
  cases i with
  | cyclic p hp => simp [S10.isU6n, onLie] at hi
  | alternating k hk => simp [S10.isU6n, onLie] at hi
  | sporadic s => simp [S10.isU6n, onLie] at hi
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | twistedA r q =>
      rcases r with _ | _ | _ | _ | _ | _ | r
      all_goals first | (simp [S10.isU6n, onLie] at hi; done) | skip
      simp only [S10.isU6n, onLie] at hi
      obtain ⟨hp, hnq⟩ := hi
      refine ⟨q, Or.inr rfl, hp, ?_⟩
      rw [TauCeti.PrimePower.card_def, hp, hnq]
      exact Nat.dvd_gcd (by norm_num) (three_dvd_two_pow_add_one hn)
    | _ => simp [S10.isU6n, onLie] at hi

theorem catalogIs_setupE6_of_isTE6n {S : Type} [Group S] {n : ℕ} (hn : Odd n)
    (h : catalogIs S (S10.isTE6n n)) :
    catalogIs S (onLie fun i => ∃ q, I171.I171LieShape 3 i ∧ (i = .E6 q ∨ i = .twistedE6 q)) := by
  refine catalogIs_imp (fun i hi => ?_) h
  cases i with
  | cyclic p hp => simp [S10.isTE6n, onLie] at hi
  | alternating k hk => simp [S10.isTE6n, onLie] at hi
  | sporadic s => simp [S10.isTE6n, onLie] at hi
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | twistedE6 q =>
      simp only [S10.isTE6n, onLie] at hi
      obtain ⟨hp, hnq⟩ := hi
      refine ⟨q, ⟨rfl, hp, ?_⟩, Or.inr rfl⟩
      rw [TauCeti.PrimePower.card_def, hp, hnq]
      exact three_dvd_two_pow_add_one hn
    | _ => simp [S10.isTE6n, onLie] at hi

theorem catalogIs_t158Shape_of_isU6n {S : Type} [Group S] {n : ℕ} (hn : Odd n)
    (h : catalogIs S (S10.isU6n n)) : catalogIs S (t158Shape 3) := by
  refine catalogIs_imp (fun i hi => ?_) h
  cases i with
  | cyclic p hp => simp [S10.isU6n, onLie] at hi
  | alternating k hk => simp [S10.isU6n, onLie] at hi
  | sporadic s => simp [S10.isU6n, onLie] at hi
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | twistedA r q =>
      rcases r with _ | _ | _ | _ | _ | _ | r
      all_goals first | (simp [S10.isU6n, onLie] at hi; done) | skip
      simp only [S10.isU6n, onLie] at hi
      obtain ⟨hp, hnq⟩ := hi
      refine Or.inr (Or.inl ⟨hp, ?_⟩)
      rw [TauCeti.PrimePower.card_def, hp, hnq]
      exact Nat.dvd_gcd (by norm_num) (three_dvd_two_pow_add_one hn)
    | _ => simp [S10.isU6n, onLie] at hi

theorem catalogIs_t158Shape_of_isTE6n {S : Type} [Group S] {n : ℕ} (hn : Odd n)
    (h : catalogIs S (S10.isTE6n n)) : catalogIs S (t158Shape 3) := by
  refine catalogIs_imp (fun i hi => ?_) h
  cases i with
  | cyclic p hp => simp [S10.isTE6n, onLie] at hi
  | alternating k hk => simp [S10.isTE6n, onLie] at hi
  | sporadic s => simp [S10.isTE6n, onLie] at hi
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | twistedE6 q =>
      simp only [S10.isTE6n, onLie] at hi
      obtain ⟨hp, hnq⟩ := hi
      refine Or.inr (Or.inr (Or.inr ⟨rfl, hp, ?_⟩))
      rw [TauCeti.PrimePower.card_def, hp, hnq]
      exact three_dvd_two_pow_add_one hn
    | _ => simp [S10.isTE6n, onLie] at hi

theorem catalogIs_famTwo_of_tail {S : Type} [Group S] {n : ℕ}
    (h : catalogIs S (S10.isU6n n) ∨ catalogIs S (S10.isTE6n n)) : catalogIs S t158FamTwo := by
  rcases h with h | h
  · refine catalogIs_imp (fun i hi => ?_) h
    cases i with
    | cyclic p hp => simp [S10.isU6n, onLie] at hi
    | alternating k hk => simp [S10.isU6n, onLie] at hi
    | sporadic s => simp [S10.isU6n, onLie] at hi
    | lie j =>
      obtain ⟨d, hv⟩ := j
      simp only [S10.isU6n, onLie] at hi
      simp only [t158FamTwo, onLie]
      split at hi
      · rename_i q
        rw [TauCeti.LieTypeIndex.characteristic_twistedA]
        exact hi.1
      · exact absurd hi id
  · refine catalogIs_imp (fun i hi => ?_) h
    cases i with
    | cyclic p hp => simp [S10.isTE6n, onLie] at hi
    | alternating k hk => simp [S10.isTE6n, onLie] at hi
    | sporadic s => simp [S10.isTE6n, onLie] at hi
    | lie j =>
      obtain ⟨d, hv⟩ := j
      simp only [S10.isTE6n, onLie] at hi
      simp only [t158FamTwo, onLie]
      split at hi
      · rename_i q
        rw [TauCeti.LieTypeIndex.characteristic_twistedE6]
        exact hi.1
      · exact absurd hi id

theorem t158MainTail_of_tailOn_union (h : T158TailOn fun i => t158FamU6 i ∨ t158FamTE6 i) : T158MainTail := by
  intro X _ _ p K B x₁ x₂ L₁ L₂ hh hc T hT hT2 hBT
  have hc0 := hc
  obtain ⟨hp3, n, -, -, hD⟩ := hc
  subst hp3
  have hK : catalogIs (PSimple 3 K) fun i => t158FamU6 i ∨ t158FamTE6 i := by
    rcases hD with ⟨⟨i, hi, e⟩, -⟩ | ⟨⟨i, hi, e⟩, -⟩
    · exact ⟨i, Or.inl ⟨n, hi⟩, e⟩
    · exact ⟨i, Or.inr ⟨n, hi⟩, e⟩
  exact h X 3 K B x₁ x₂ L₁ L₂ hK hh hc0 T hT hT2 hBT

theorem t158TailOn_of_mainTail (h : T158MainTail) {Q : TauCeti.CFSGIndex → Prop} : T158TailOn Q :=
  fun X _ _ p K B x₁ x₂ L₁ L₂ _ hh hc T hT hT2 hBT => h X p K B x₁ x₂ L₁ L₂ hh hc T hT hT2 hBT

section Tables

open CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Solomon.Coordinator

theorem t158MainTail_of_model
    (T : Tables112) (TL : TableL2) (TT : Tables112Types)
    (hM : T158TailModel fun i => t158FamU6 i ∨ t158FamTE6 i) :
    T158MainTail :=
  t158MainTail_of_tailOn_union
    (t158TailOn_of (t158NormConj_of_tables T TL TT) (t158TailFaith_of_norm (t158NormConj_of_tables T TL TT)) hM)

end Tables

end CFSG.LocalAnalysis.GLTheoremA.T158

end
