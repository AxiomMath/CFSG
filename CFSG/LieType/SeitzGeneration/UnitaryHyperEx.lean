module

public import CFSG.LieType.SeitzGeneration.UnitaryHyperPSU
public import CFSG.LieType.SeitzGeneration.UnitaryNonsplit

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open TauCeti

@[expose] def USplitPrime (d : ValidLieTypeIndex) (p : ℕ) : Prop :=
  ∃ (m : ℕ) (q : PrimePower), d.1 = .twistedA m q ∧ p ∣ q.card - 1

@[expose] def UToralPrime (d : ValidLieTypeIndex) (p : ℕ) : Prop :=
  ∃ (m : ℕ) (q : PrimePower), d.1 = .twistedA m q ∧ p ∣ q.card + 1 ∧ q.card ≠ 2 ∧
    ¬ p ∣ Nat.gcd (m + 1) (q.card + 1)

@[expose] def URestPrime (d : ValidLieTypeIndex) (p : ℕ) : Prop :=
  ∃ (m : ℕ) (q : PrimePower), d.1 = .twistedA m q ∧ ¬ p ∣ q.card - 1 ∧
    ¬ (p ∣ q.card + 1 ∧ q.card ≠ 2 ∧ ¬ p ∣ Nat.gcd (m + 1) (q.card + 1))

@[expose] def UnitaryHyperExRest : Prop := SeitzHyperLieEx fun d p _ => URestPrime d p

theorem card_twistedA (m : ℕ) (q : PrimePower) (hv : (LieTypeIndex.twistedA m q).Valid) :
    ValidLieTypeIndex.characteristic ⟨.twistedA m q, hv⟩ ^
      ValidLieTypeIndex.fieldExponent ⟨.twistedA m q, hv⟩ = q.card := by
  simp [ValidLieTypeIndex.characteristic, ValidLieTypeIndex.fieldExponent, PrimePower.card_def]

theorem seitzHyperLie_unitary_split : SeitzHyperLie fun d p _ => USplitPrime d p := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hlist E₀ hE hcard ⟨m, q, hd, hpq⟩
  simp only at hd
  subst hd
  have hrange := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have hm2 : 2 ≤ m := hrange.1
  have hU := CFSG.RankThree.PartTwo.Census.unitaryFieldData_galoisField
    (ValidLieTypeIndex.characteristic ⟨.twistedA m q, hv⟩)
    (ValidLieTypeIndex.fieldExponent ⟨.twistedA m q, hv⟩)
    (ValidLieTypeIndex.fieldExponent_pos ⟨.twistedA m q, hv⟩)
  have hqc := card_twistedA m q hv
  let e := CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj m q hv
  have hE' : IsElemAbelian p (E₀.map e.toMonoidHom) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE _
  have hcard' : Nat.card (E₀.map e.toMonoidHom) = p ^ 3 := by
    rw [Subgroup.card_map_of_injective e.injective, hcard]
  refine hyperGen_top_of_mulEquiv e (hyperGen_statedProj_unitary_split hU (by omega)
    (fun h3 => ?_) hp hp2 (by rw [hqc]; exact hpq) hE' hcard')
  have hq2 : ValidLieTypeIndex.characteristic ⟨.twistedA m q, hv⟩ ^
      ValidLieTypeIndex.fieldExponent ⟨.twistedA m q, hv⟩ ≠ 2 := by
    rw [hqc]
    have := hrange.2 (by omega)
    omega
  exact Nonsplit.exists_norm_ne_one hU hq2

theorem seitzHyperLie_unitary_toral : SeitzHyperLie fun d p _ => UToralPrime d p := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hlist E₀ hE hcard ⟨m, q, hd, hpq, hq2, hgcd⟩
  simp only at hd
  subst hd
  have hU := CFSG.RankThree.PartTwo.Census.unitaryFieldData_galoisField
    (ValidLieTypeIndex.characteristic ⟨.twistedA m q, hv⟩)
    (ValidLieTypeIndex.fieldExponent ⟨.twistedA m q, hv⟩)
    (ValidLieTypeIndex.fieldExponent_pos ⟨.twistedA m q, hv⟩)
  have hqc := card_twistedA m q hv
  let e := CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj m q hv
  have hE' : IsElemAbelian p (E₀.map e.toMonoidHom) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE _
  have hcard' : Nat.card (E₀.map e.toMonoidHom) = p ^ 3 := by
    rw [Subgroup.card_map_of_injective e.injective, hcard]
  exact hyperGen_top_of_mulEquiv e (hyperGen_statedProj_unitary_toral hU hp
    (by rw [hqc]; exact hpq) (by rw [hqc]; exact hq2) (by rw [hqc]; exact hgcd) hE' hcard')

theorem hyperExFor_unitary_of_rest (h : UnitaryHyperExRest) :
    HyperExFor fun d => IsUnitaryIndex' d.1 := by
  refine SeitzHyperLieEx.of_cover
    (S₁ := fun d p _ => USplitPrime d p ∨ UToralPrime d p) (S₂ := fun d p _ => URestPrime d p)
    (fun d p _ hd => ?_)
    (SeitzHyperLieEx.of_cover (fun _ _ _ h => h) seitzHyperLie_unitary_split.toEx
      seitzHyperLie_unitary_toral.toEx) h
  obtain ⟨m, q, hd⟩ := hd
  by_cases h1 : p ∣ q.card - 1
  · exact Or.inl (Or.inl ⟨m, q, hd, h1⟩)
  by_cases h2 : p ∣ q.card + 1 ∧ q.card ≠ 2 ∧ ¬ p ∣ Nat.gcd (m + 1) (q.card + 1)
  · exact Or.inl (Or.inr ⟨m, q, hd, h2⟩)
  · exact Or.inr ⟨m, q, hd, h1, h2⟩

end CFSG.LieType.SeitzGeneration
