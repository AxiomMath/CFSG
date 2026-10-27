module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.List93Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS07I67

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

namespace List93

theorem noE_of_bound {p : ℕ} {S : Type} [Group S]
    (h : ∀ E : Subgroup (MulAut S), CFSG.Open.IsElemAbelian p E → Nat.card E < p ^ 3) :
    ¬ ∃ E : Subgroup (MulAut S), CFSG.Open.IsElemAbelian p E ∧ p ^ 3 ≤ Nat.card E := by
  rintro ⟨E, hE, hle⟩
  exact absurd hle (not_le.2 (h E hE))

theorem l93_D4 {i : TauCeti.CFSGIndex} (h : S9.isD4two i) : S9.isList93 3 i :=
  Or.inr ⟨rfl, Or.inl h⟩

theorem l93_Sp4 {i : TauCeti.CFSGIndex} (h : S9.isSp4eight i) : S9.isList93 3 i :=
  Or.inr ⟨rfl, Or.inr (Or.inl h)⟩

theorem l93_G2 {i : TauCeti.CFSGIndex} (h : S9.isG2eight i) : S9.isList93 3 i :=
  Or.inr ⟨rfl, Or.inr (Or.inr (Or.inl h))⟩

theorem l93_U4 {i : TauCeti.CFSGIndex} (h : S9.isU4eight i) : S9.isList93 3 i :=
  Or.inr ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inl h)))⟩

theorem l93_U6 {i : TauCeti.CFSGIndex} (h : S9.isU6two i) : S9.isList93 3 i :=
  Or.inr ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))⟩

theorem l93_TD4 {i : TauCeti.CFSGIndex} (h : S9.isTD4two i) : S9.isList93 3 i :=
  Or.inr ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))⟩

theorem l93_ReeF48 {i : TauCeti.CFSGIndex} (h : S9.isReeF48 i) : S9.isList93 3 i :=
  Or.inr ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))⟩

theorem l93_L3 {i : TauCeti.CFSGIndex} (h : S9.isL3char2 i) : S9.isList93 3 i :=
  Or.inr ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))⟩

theorem l93_U3 {i : TauCeti.CFSGIndex} (h : S9.isU3char2 i) : S9.isList93 3 i :=
  Or.inr ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))⟩

theorem l94_Sp6 {i : TauCeti.CFSGIndex} (h : S9.isSp6two i) : S9.isList94 i :=
  Or.inl h

theorem l94_U5 {i : TauCeti.CFSGIndex} (h : S9.isU5two i) : S9.isList94 i :=
  Or.inr (Or.inr (Or.inr h))

theorem lie_case (hF : I9List93Residual) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (S : Type) [Group S] [Finite S] (h2 : IsChevSimple 2 S)
    (d : TauCeti.LieTypeIndex) (hv : d.Valid)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨d, hv⟩).Group)
    (hk : k2Lie p d) :
    catalogIs S (S9.isList93 p) ∨ (p = 3 ∧ catalogIs S S9.isList94) ∨
      ¬ ∃ E : Subgroup (MulAut S), CFSG.Open.IsElemAbelian p E ∧ p ^ 3 ≤ Nat.card E := by
  cases d with
  | A n q =>
    match n, hk with
    | 1, hk =>
      obtain ⟨rfl, hn3⟩ := hk
      by_cases h2' : q.p = 2
      · have hl : catalogIs S l2Two :=
          ⟨.lie ⟨.A 1 q, hv⟩, show q.p = 2 from h2', ⟨e⟩⟩
        exact Or.inr (Or.inr (noE_of_bound (hF.l2Two S hl)))
      · have hne3 : q.p ≠ 3 := by
          intro h
          apply hn3
          rw [TauCeti.PrimePower.card_def, h]
          exact dvd_pow_self 3 q.exponent_pos.ne'
        have hc : IsChevSimple q.p S :=
          Or.inl ⟨.lie ⟨.A 1 q, hv⟩, by simp [onLie], ⟨e⟩⟩
        exact Or.inr (Or.inr (noE_of_bound
          (hF.chevOdd S q.p q.prime_p h2' hne3 hc h2 _ hp hp2)))
    | 2, hk =>
      rcases hk with ⟨rfl, h2', he⟩ | ⟨rfl, hc3⟩
      · have hL3 : S9.isL3char2 (.lie ⟨.A 2 q, hv⟩) :=
          show q.p = 2 ∧ q.card % 3 = 1 from ⟨h2', card_mod_three_of_even h2' he⟩
        exact Or.inl ⟨.lie ⟨.A 2 q, hv⟩, l93_L3 hL3, ⟨e⟩⟩
      · have hl33 : List93.l33Idx (.lie ⟨.A 2 q, hv⟩) := show q.card = 3 from hc3
        exact absurd h2 (hF.notChev2 S _ (Or.inr (Or.inr (Or.inr hl33))) ⟨e⟩)
    | n + 3, hk => exact False.elim hk
    | 0, hk => exact False.elim hk
  | twistedA n q =>
    match n, hk with
    | 2, hk =>
      obtain ⟨rfl, h2', ho, -⟩ := hk
      have hU3 : S9.isU3char2 (.lie ⟨.twistedA 2 q, hv⟩) :=
        show q.p = 2 ∧ q.card % 3 = 2 from ⟨h2', card_mod_three_of_odd h2' ho⟩
      exact Or.inl ⟨.lie ⟨.twistedA 2 q, hv⟩, l93_U3 hU3, ⟨e⟩⟩
    | 3, hk =>
      obtain ⟨rfl, hc8⟩ := hk
      have hU4 : S9.isU4eight (.lie ⟨.twistedA 3 q, hv⟩) := show q.card = 8 from hc8
      exact Or.inl ⟨.lie ⟨.twistedA 3 q, hv⟩, l93_U4 hU4, ⟨e⟩⟩
    | 4, hk =>
      obtain ⟨rfl, hc2⟩ := hk
      have hU5 : S9.isU5two (.lie ⟨.twistedA 4 q, hv⟩) := show q.card = 2 from hc2
      exact Or.inr (Or.inl ⟨rfl, .lie ⟨.twistedA 4 q, hv⟩, l94_U5 hU5, ⟨e⟩⟩)
    | 5, hk =>
      obtain ⟨rfl, hc2⟩ := hk
      have hU6 : S9.isU6two (.lie ⟨.twistedA 5 q, hv⟩) := show q.card = 2 from hc2
      exact Or.inl ⟨.lie ⟨.twistedA 5 q, hv⟩, l93_U6 hU6, ⟨e⟩⟩
    | n + 6, hk => exact False.elim hk
    | 0, hk => exact False.elim hk
    | 1, hk => exact False.elim hk
  | B n q =>
    match n, hk with
    | 2, hk =>
      obtain ⟨rfl, hc8⟩ := hk
      have hS : S9.isSp4eight (.lie ⟨.B 2 q, hv⟩) := show q.card = 8 from hc8
      exact Or.inl ⟨.lie ⟨.B 2 q, hv⟩, l93_Sp4 hS, ⟨e⟩⟩
    | 3, hk =>
      obtain ⟨rfl, hc2⟩ := hk
      have hS : S9.isSp6two (.lie ⟨.B 3 q, hv⟩) := show q.card = 2 from hc2
      exact Or.inr (Or.inl ⟨rfl, .lie ⟨.B 3 q, hv⟩, l94_Sp6 hS, ⟨e⟩⟩)
    | n + 4, hk => exact False.elim hk
    | 0, hk => exact False.elim hk
    | 1, hk => exact False.elim hk
  | D n q =>
    match n, hk with
    | 4, hk =>
      obtain ⟨rfl, hc2⟩ := hk
      have hS : S9.isD4two (.lie ⟨.D 4 q, hv⟩) := show q.card = 2 from hc2
      exact Or.inl ⟨.lie ⟨.D 4 q, hv⟩, l93_D4 hS, ⟨e⟩⟩
    | n + 5, hk => exact False.elim hk
    | 0, hk => exact False.elim hk
    | 1, hk => exact False.elim hk
    | 2, hk => exact False.elim hk
    | 3, hk => exact False.elim hk
  | C n q => exact False.elim hk
  | twistedD n q => exact False.elim hk
  | E6 q => exact False.elim hk
  | E7 q => exact False.elim hk
  | E8 q => exact False.elim hk
  | F4 q => exact False.elim hk
  | G2 q =>
    obtain ⟨rfl, hc8⟩ := hk
    have hS : S9.isG2eight (.lie ⟨.G2 q, hv⟩) := show q.card = 8 from hc8
    exact Or.inl ⟨.lie ⟨.G2 q, hv⟩, l93_G2 hS, ⟨e⟩⟩
  | twistedE6 q => exact False.elim hk
  | trialityD4 q =>
    obtain ⟨rfl, hc2⟩ := hk
    have hS : S9.isTD4two (.lie ⟨.trialityD4 q, hv⟩) := show q.card = 2 from hc2
    exact Or.inl ⟨.lie ⟨.trialityD4 q, hv⟩, l93_TD4 hS, ⟨e⟩⟩
  | suzuki m =>
    obtain ⟨rfl, rfl⟩ := hk
    have hsz : szIdx (.lie ⟨.suzuki 2, hv⟩) := rfl
    exact Or.inr (Or.inr (noE_of_bound (hF.suzuki S ⟨_, hsz, ⟨e⟩⟩)))
  | reeG2 m => exact False.elim hk
  | reeF4 m =>
    rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hS : S9.isReeF48 (.lie ⟨.reeF4 1, hv⟩) := rfl
      exact Or.inl ⟨.lie ⟨.reeF4 1, hv⟩, l93_ReeF48 hS, ⟨e⟩⟩
    · have hS : S9.isReeF432 (.lie ⟨.reeF4 2, hv⟩) := rfl
      exact Or.inl ⟨.lie ⟨.reeF4 2, hv⟩, Or.inl ⟨rfl, hS⟩, ⟨e⟩⟩
  | tits =>
    have htits : titsIdx (.lie ⟨.tits, hv⟩) := rfl
    obtain ⟨E3, E5⟩ := hF.tits S ⟨_, htits, ⟨e⟩⟩
    rcases hk with rfl | rfl
    · exact Or.inr (Or.inr (noE_of_bound E3))
    · exact Or.inr (Or.inr (noE_of_bound E5))

end List93

open List93 in
theorem i9List93_dispatch (hF : I9List93Residual) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (S : Type) [Group S] [Finite S] (h2 : IsChevSimple 2 S)
    (hP : IsChevSimple p S ∨ catalogIs S (k2 p)) :
    catalogIs S (S9.isList93 p) ∨ (p = 3 ∧ catalogIs S S9.isList94) ∨
      ¬ ∃ E : Subgroup (MulAut S), CFSG.Open.IsElemAbelian p E ∧ p ^ 3 ≤ Nat.card E := by
  rcases hP with hC | hk2
  · by_cases hp3 : p = 3
    · subst hp3
      rcases hF.chev23 S h2 hC with hU | hE
      · exact Or.inr (Or.inl ⟨rfl, catalogIs_mono (fun i hi => Or.inr (Or.inl hi)) hU⟩)
      · exact Or.inr (Or.inr (noE_of_bound hE))
    · exact Or.inr (Or.inr (noE_of_bound (hF.chevOdd S p hp hp2 hp3 hC h2 p hp hp2)))
  · obtain ⟨j, hj, ⟨e⟩⟩ := hk2
    cases j with
    | cyclic r hr => exact False.elim hj
    | alternating n hn =>
      have hj' : (p = 3 ∧ (n = 5 ∨ n = 9)) ∨ (p = 7 ∧ n = 7) := hj
      rcases hj' with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr (Or.inr fun ⟨E, hE, h3⟩ => no_alt5 hp hp2 e hE h3)
      · exact absurd h2 (hF.notChev2 S _ (Or.inr (Or.inr (Or.inl ⟨hn, rfl⟩))) ⟨e⟩)
      · exact absurd h2 (hF.notChev2 S _ (Or.inr (Or.inl ⟨hn, rfl⟩)) ⟨e⟩)
    | lie i =>
      obtain ⟨d, hv⟩ := i
      exact lie_case hF hp hp2 S h2 d hv e hj
    | sporadic s =>
      have hj' : k2Spor p s := hj
      exact absurd h2 (hF.notChev2 S _ (Or.inl ⟨s, rfl, p, hj'⟩) ⟨e⟩)

end CFSG.LocalAnalysis.GLTheoremA

end
