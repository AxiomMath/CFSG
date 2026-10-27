module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDRank3

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

@[expose] def KDRank3FieldAt (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (S : Type) [Group S] [Finite S],
    Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) → d.1.characteristic = p →
      GLATwoLocalRank p S ≤ 3 → p ∣ Nat.card (Outer S) → IsRank3Handled d.1

theorem kdRank3Field_of_forall (h : ∀ d, KDRank3FieldAt d) : KDRank3Field :=
  fun p hp hp2 S _ _ d e hc hr hout => h d p hp hp2 S e hc hr hout

namespace KDRank3FieldAux

theorem le_gla_of_carrier {S H : Type} [Group S] [Finite S] [Group H] [Finite H] (e : S ≃* H)
    {p k : ℕ} (hp : p.Prime) (h : k ≤ CFSG.Assembly.RankThreeEven.localRank p H) :
    k ≤ GLATwoLocalRank p S :=
  h.trans (CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e.symm hp).le

theorem four_le_of_mul_four {e g : ℕ} (he : 0 < e) (h : e * 4 ≤ g) : 4 ≤ g := by omega

theorem dvd_of_dvd_index_chain {G : Type*} [Group G] {I D E : Subgroup G} (hID : I ≤ D)
    (hDE : D ≤ E) {p f : ℕ} (hp : p.Prime) (h1 : ¬ p ∣ I.relIndex D) (h2 : D.relIndex E ∣ f)
    (h3 : ¬ p ∣ E.index) (h : p ∣ I.index) : p ∣ f := by
  rw [← Subgroup.relIndex_mul_index hID, ← Subgroup.relIndex_mul_index hDE] at h
  rcases (Nat.Prime.dvd_mul hp).1 h with h' | h'
  · exact absurd h' h1
  · rcases (Nat.Prime.dvd_mul hp).1 h' with h'' | h''
    · exact h''.trans h2
    · exact absurd h'' h3

theorem not_dvd_pow_sub_one {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) : ¬ p ∣ p ^ f - 1 := by
  intro h
  have h1 : p ∣ p ^ f := dvd_pow_self p (by omega)
  have h2 : p ^ f - 1 + 1 = p ^ f := Nat.sub_add_cancel (Nat.one_le_pow _ _ hp.pos)
  rw [← h2] at h1
  exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h).1 h1))

theorem card_ringEquiv_eq {K : Type*} [Field K] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) : Nat.card (K ≃+* K) = f :=
  (CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hp hf
    hK).choose_spec.2.2.2.1

theorem card_outer_eq_of_surj {N A : Type*} [Group N] [Group A] (Θ : MulAut N →* A)
    (hs : Function.Surjective Θ) (hker : Θ.ker = (MulAut.conj : N →* MulAut N).range) :
    Nat.card (Outer N) = Nat.card A := by
  have h1 : Nat.card (Outer N) = (inner N).index := rfl
  rw [h1]
  have h2 : inner N = Θ.ker := hker.symm
  rw [h2, Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective _ hs, Subgroup.card_top]

open CFSG.RankThree.PartTwo.Census.Exceptional in
open scoped MatrixGroups in
theorem card_mul_le_localRank_of_commuting_SL2 {G : Type} [Group G] [Finite G] {ι : Type}
    [Fintype ι] [DecidableEq ι] [Nonempty ι] {K : Type} [Field K] [Fintype K] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Fintype.card K = p ^ f) (φ : ι → SL(2, K) →* G)
    (hφ : ∀ i, Function.Injective (φ i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B : SL(2, K), φ i A * φ j B = φ j B * φ i A) :
    Fintype.card ι * f ≤ CFSG.Assembly.RankThreeEven.localRank p G := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have h := sum_le_localRank_of_commuting_SL2 hp hp2 i₀ (K := fun _ => K) (fun _ => f)
    (fun _ => hK) φ hφ hcomm
  simpa [Finset.sum_const, Finset.card_univ] using h

end KDRank3FieldAux

end CFSG.LocalAnalysis.GLTheoremA
