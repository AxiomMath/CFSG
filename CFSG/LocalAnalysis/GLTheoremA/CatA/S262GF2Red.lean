module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S262Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S262

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open TauCeti
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

@[expose] def Good3 (T : Type) [Group T] : Prop :=
  ∀ a : MulAut T, a ≠ 1 → a ^ 3 = 1 → GLAPLayer 3 (fixSubgroup a) ≠ ⊥

@[expose] def E9Good (T : Type) [Group T] : Prop :=
  ∀ A : Subgroup (MulAut T), IsElemAbelian 3 A → 9 ≤ Nat.card A →
    ∃ a ∈ A, a ≠ 1 ∧ GLAPLayer 3 (fixSubgroup a) ≠ ⊥

@[expose] def Good3On (Q : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) [Finite (TauCeti.CFSGIndex.lie d).Group], Q d.1 →
    Good3 (TauCeti.CFSGIndex.lie d).Group

@[expose] def E9GoodOn (Q : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) [Finite (TauCeti.CFSGIndex.lie d).Group], Q d.1 →
    E9Good (TauCeti.CFSGIndex.lie d).Group

@[expose] def gf2Lin : TauCeti.LieTypeIndex → Prop
  | .A r q => 4 ≤ r ∧ q.card = 2
  | _ => False
@[expose] def gf2Uni : TauCeti.LieTypeIndex → Prop
  | .twistedA r q => 9 ≤ r ∧ q.card = 2
  | _ => False
@[expose] def gf2Symp : TauCeti.LieTypeIndex → Prop
  | .B r q => 5 ≤ r ∧ q.card = 2
  | _ => False
@[expose] def gf2OrthPlus : TauCeti.LieTypeIndex → Prop
  | .D r q => 5 ≤ r ∧ q.card = 2
  | _ => False
@[expose] def gf2OrthMinus : TauCeti.LieTypeIndex → Prop
  | .twistedD r q => 6 ≤ r ∧ q.card = 2
  | _ => False
@[expose] def gf2OmMinus8 : TauCeti.LieTypeIndex → Prop
  | .twistedD 4 q => q.card = 2
  | _ => False
@[expose] def gf2E6 : TauCeti.LieTypeIndex → Prop
  | .E6 q => q.card = 2
  | _ => False
@[expose] def gf2E7 : TauCeti.LieTypeIndex → Prop
  | .E7 q => q.card = 2
  | _ => False
@[expose] def gf2E8 : TauCeti.LieTypeIndex → Prop
  | .E8 q => q.card = 2
  | _ => False

theorem e9Good_of_good3 {T : Type} [Group T] (h : Good3 T) : E9Good T := by
  intro A hA h9
  have hpos : 0 < Nat.card A := by omega
  obtain ⟨hne, hfin⟩ := Nat.card_pos_iff.mp hpos
  haveI := hfin
  have hnt : Nontrivial A := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    omega
  haveI := hnt
  obtain ⟨a, ha, ha1⟩ := A.exists_ne_one_of_nontrivial
  exact ⟨a, ha, ha1, h a ha1 (hA.2 a ha)⟩

theorem e9GoodOn_of_good3On {Q : TauCeti.LieTypeIndex → Prop} (h : Good3On Q) : E9GoodOn Q := by
  intro d _ hQ
  exact e9Good_of_good3 (h d hQ)

theorem family_of_not_list (d : TauCeti.ValidLieTypeIndex)
    (hchar : d.1.characteristic = 2) (hov : KD264Lie.ov2Idx d.1)
    (h : ¬ (S265.tyA (.lie d) ∨ S265.tyUn (.lie d) ∨ S265.tyC (.lie d))) :
    gf2Lin d.1 ∨ gf2Uni d.1 ∨ gf2Symp d.1 ∨ gf2OrthPlus d.1 ∨ gf2OrthMinus d.1 ∨
      gf2OmMinus8 d.1 ∨ gf2E6 d.1 ∨ gf2E7 d.1 ∨ gf2E8 d.1 := by
  obtain ⟨e, hv⟩ := d
  change KD264Lie.fieldSize e = 2 at hov
  cases e with
  | A r q =>
    have hstd := (LieTypeIndex.inStandardRange_iff (.A r q)).1
      ((LieTypeIndex.valid_iff (.A r q)).1 hv).1
    have hdup := ((LieTypeIndex.valid_iff (.A r q)).1 hv).2
    rw [LieTypeIndex.isDuplicateRepresentative_iff] at hdup
    have hcard : q.card = 2 := by
      simpa [KD264Lie.ov2Idx, KD264Lie.fieldSize] using hov
    left
    refine ⟨?_, hcard⟩
    have h1 : r ≠ 1 := fun hr => by
      have := hstd.2 hr
      omega
    have h2 : r ≠ 2 := fun hr => hdup (Or.inr (Or.inl ⟨hr, hcard⟩))
    have h3 : r ≠ 3 := fun hr => hdup (Or.inr (Or.inr ⟨hr, hcard⟩))
    omega
  | twistedA r q =>
    have hstd := (LieTypeIndex.inStandardRange_iff (.twistedA r q)).1
      ((LieTypeIndex.valid_iff (.twistedA r q)).1 hv).1
    have hcard : q.card = 2 := by
      simpa [KD264Lie.ov2Idx, KD264Lie.fieldSize] using hov
    have hcard' : q.p ^ q.exponent = 2 := by
      rw [← TauCeti.PrimePower.card_def]
      exact hcard
    have hr3 : 3 ≤ r := by
      have hr2 : r ≠ 2 := fun hr => by
        have := hstd.2 hr
        omega
      omega
    rcases Nat.lt_or_ge r 9 with hr9 | hr9
    · exfalso
      have hr8 : r ≤ 8 := by omega
      have hUn : S265.tyUn (.lie ⟨.twistedA r q, hv⟩) := by
        simp [S265.tyUn, onLie, hcard', hr3, hr8]
      exact (h (Or.inr (Or.inl hUn))).elim
    · exact Or.inr (Or.inl ⟨hr9, hcard⟩)
  | B r q =>
    have hstd := (LieTypeIndex.inStandardRange_iff (.B r q)).1
      ((LieTypeIndex.valid_iff (.B r q)).1 hv).1
    have hcard : q.card = 2 := by
      simpa [KD264Lie.ov2Idx, KD264Lie.fieldSize] using hov
    have hcard' : q.p ^ q.exponent = 2 := by
      rw [← TauCeti.PrimePower.card_def]
      exact hcard
    rcases Nat.lt_or_ge r 5 with hr5 | hr5
    · exfalso
      have hr3 : 3 ≤ r := by
        have hr2 : r ≠ 2 := fun hr => hstd.2 ⟨hr, hcard⟩
        omega
      have hA : S265.tyA (.lie ⟨.B r q, hv⟩) := by
        have hr34 : r = 3 ∨ r = 4 := by omega
        rcases hr34 with rfl | rfl
        · simp [S265.tyA, S9.isD4two, S9.isSp6two, S265.tySp8, S265.tyOm10m, S265.tyAlt6,
            onLie, hcard']
        · simp [S265.tyA, S9.isD4two, S9.isSp6two, S265.tySp8, S265.tyOm10m, S265.tyAlt6,
            onLie, hcard']
      exact (h (Or.inl hA)).elim
    · exact Or.inr (Or.inr (Or.inl ⟨hr5, hcard⟩))
  | C r q =>
    have hstd := (LieTypeIndex.inStandardRange_iff (.C r q)).1
      ((LieTypeIndex.valid_iff (.C r q)).1 hv).1
    exfalso
    have hcp : q.p = 2 := by
      simpa using hchar
    exact hstd.2 hcp
  | D r q =>
    have hstd := (LieTypeIndex.inStandardRange_iff (.D r q)).1
      ((LieTypeIndex.valid_iff (.D r q)).1 hv).1
    have hcard : q.card = 2 := by
      simpa [KD264Lie.ov2Idx, KD264Lie.fieldSize] using hov
    have hcard' : q.p ^ q.exponent = 2 := by
      rw [← TauCeti.PrimePower.card_def]
      exact hcard
    rcases Nat.lt_or_ge r 5 with hr5 | hr5
    · exfalso
      have hA : S265.tyA (.lie ⟨.D r q, hv⟩) := by
        have hr4 : r = 4 := by omega
        subst r
        simp [S265.tyA, S9.isD4two, S9.isSp6two, S265.tySp8, S265.tyOm10m, S265.tyAlt6,
          onLie, hcard']
      exact (h (Or.inl hA)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hr5, hcard⟩)))
  | twistedD r q =>
    have hstd := (LieTypeIndex.inStandardRange_iff (.twistedD r q)).1
      ((LieTypeIndex.valid_iff (.twistedD r q)).1 hv).1
    have hcard : q.card = 2 := by
      simpa [KD264Lie.ov2Idx, KD264Lie.fieldSize] using hov
    have hcard' : q.p ^ q.exponent = 2 := by
      rw [← TauCeti.PrimePower.card_def]
      exact hcard
    rcases Nat.lt_or_ge r 5 with hr5 | hr5
    · have hr4 : r = 4 := by omega
      subst r
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hcard)))))
    · rcases Nat.lt_or_ge r 6 with hr6 | hr6
      · exfalso
        have hA : S265.tyA (.lie ⟨.twistedD r q, hv⟩) := by
          have hr5' : r = 5 := by omega
          subst r
          simp [S265.tyA, S9.isD4two, S9.isSp6two, S265.tySp8, S265.tyOm10m, S265.tyAlt6,
            onLie, hcard']
        exact (h (Or.inl hA)).elim
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hr6, hcard⟩))))
  | E6 q =>
    have hcard : q.card = 2 := by
      simpa [KD264Lie.ov2Idx, KD264Lie.fieldSize] using hov
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hcard))))))
  | E7 q =>
    have hcard : q.card = 2 := by
      simpa [KD264Lie.ov2Idx, KD264Lie.fieldSize] using hov
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hcard)))))))
  | E8 q =>
    have hcard : q.card = 2 := by
      simpa [KD264Lie.ov2Idx, KD264Lie.fieldSize] using hov
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hcard)))))))
  | F4 q =>
    exfalso
    have hcard : q.card = 2 := by
      simpa [KD264Lie.ov2Idx, KD264Lie.fieldSize] using hov
    have hcard' : q.p ^ q.exponent = 2 := by
      rw [← TauCeti.PrimePower.card_def]
      exact hcard
    have hC : S265.tyC (.lie ⟨.F4 q, hv⟩) := by
      simp [S265.tyC, S9.isTD4two, S9.isF4two, S9.isTE6two, onLie, hcard']
    exact (h (Or.inr (Or.inr hC))).elim
  | G2 q =>
    exfalso
    have hstd := (LieTypeIndex.inStandardRange_iff (.G2 q)).1
      ((LieTypeIndex.valid_iff (.G2 q)).1 hv).1
    have hcard : q.card = 2 := by
      simpa [KD264Lie.ov2Idx, KD264Lie.fieldSize] using hov
    omega
  | twistedE6 q =>
    exfalso
    have hcard : q.card = 2 := by
      simpa [KD264Lie.ov2Idx, KD264Lie.fieldSize] using hov
    have hcard' : q.p ^ q.exponent = 2 := by
      rw [← TauCeti.PrimePower.card_def]
      exact hcard
    have hC : S265.tyC (.lie ⟨.twistedE6 q, hv⟩) := by
      simp [S265.tyC, S9.isTD4two, S9.isF4two, S9.isTE6two, onLie, hcard']
    exact (h (Or.inr (Or.inr hC))).elim
  | trialityD4 q =>
    exfalso
    have hcard : q.card = 2 := by
      simpa [KD264Lie.ov2Idx, KD264Lie.fieldSize] using hov
    have hcard' : q.p ^ q.exponent = 2 := by
      rw [← TauCeti.PrimePower.card_def]
      exact hcard
    have hC : S265.tyC (.lie ⟨.trialityD4 q, hv⟩) := by
      simp [S265.tyC, S9.isTD4two, S9.isF4two, S9.isTE6two, onLie, hcard']
    exact (h (Or.inr (Or.inr hC))).elim
  | suzuki m =>
    exfalso
    have hstd := (LieTypeIndex.inStandardRange_iff (.suzuki m)).1
      ((LieTypeIndex.valid_iff (.suzuki m)).1 hv).1
    have hpow : 2 ^ (2 * m + 1) = 2 := by
      simpa [KD264Lie.ov2Idx, KD264Lie.fieldSize] using hov
    have hm0 : m = 0 := by
      have h1 : 2 ^ (2 * m + 1) = 2 ^ 1 := by simpa using hpow
      have h2 : 2 * m + 1 = 1 := Nat.pow_right_injective (by norm_num) h1
      omega
    omega
  | reeG2 m =>
    exfalso
    have h3 : 3 = 2 := by
      simpa [LieTypeIndex.characteristic_reeG2] using hchar
    omega
  | reeF4 m =>
    exfalso
    have hstd := (LieTypeIndex.inStandardRange_iff (.reeF4 m)).1
      ((LieTypeIndex.valid_iff (.reeF4 m)).1 hv).1
    have hpow : 2 ^ (2 * m + 1) = 2 := by
      simpa [KD264Lie.ov2Idx, KD264Lie.fieldSize] using hov
    have hm0 : m = 0 := by
      have h1 : 2 ^ (2 * m + 1) = 2 ^ 1 := by simpa using hpow
      have h2 : 2 * m + 1 = 1 := Nat.pow_right_injective (by norm_num) h1
      omega
    omega
  | tits =>
    exfalso
    have hC : S265.tyC (.lie ⟨.tits, hv⟩) := by
      simp [S265.tyC, S9.isTD4two, S9.isF4two, S9.isTE6two, onLie]
    exact (h (Or.inr (Or.inr hC))).elim

theorem i262GF2_of_families (hLin : Good3On gf2Lin) (hUni : Good3On gf2Uni)
    (hSymp : Good3On gf2Symp) (hOP : Good3On gf2OrthPlus) (hOM : Good3On gf2OrthMinus)
    (hE7 : Good3On gf2E7) (hE8 : Good3On gf2E8) (hOM8 : E9GoodOn gf2OmMinus8)
    (hE6 : E9GoodOn gf2E6) : I262GF2 := by
  intro d hfin hchar hov A hA h9 hbot
  by_cases hlist : S265.tyA (.lie d) ∨ S265.tyUn (.lie d) ∨ S265.tyC (.lie d)
  · exact hlist
  · have key : ∀ {Q : TauCeti.LieTypeIndex → Prop}, Good3On Q → Q d.1 → False := by
      intro Q hQ hQd
      obtain ⟨a, ha, ha1, hne⟩ := e9GoodOn_of_good3On hQ d hQd A hA h9
      exact hne (hbot a ha ha1)
    have keyE : ∀ {Q : TauCeti.LieTypeIndex → Prop}, E9GoodOn Q → Q d.1 → False := by
      intro Q hQ hQd
      obtain ⟨a, ha, ha1, hne⟩ := hQ d hQd A hA h9
      exact hne (hbot a ha ha1)
    have hfam := family_of_not_list d hchar hov hlist
    rcases hfam with h | h | h | h | h | h | h | h | h
    · exact (key hLin h).elim
    · exact (key hUni h).elim
    · exact (key hSymp h).elim
    · exact (key hOP h).elim
    · exact (key hOM h).elim
    · exact (keyE hOM8 h).elim
    · exact (keyE hE6 h).elim
    · exact (key hE7 h).elim
    · exact (key hE8 h).elim

end CFSG.LocalAnalysis.GLTheoremA.S262

end
