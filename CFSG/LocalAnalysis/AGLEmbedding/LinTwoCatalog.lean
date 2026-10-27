module

public import CFSG.Adapters.LinearCatalog
public import CFSG.LocalAnalysis.SectionRank.OddCover.PSL2

public section

namespace CFSG.AGLEmbedding

abbrev PSL2GF (p n : ℕ) [Fact p.Prime] : Type :=
  Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p n)

@[expose] def IsLinTwoIndex (p n : ℕ) (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, d.1 = .A 1 q ∧ q.p = p ∧ q.exponent = n

theorem nonempty_mulEquiv_psl2GF_of_isLinTwoIndex {p n : ℕ} [Fact p.Prime]
    {d : TauCeti.ValidLieTypeIndex} (hd : IsLinTwoIndex p n d) :
    Nonempty ((TauCeti.CFSGIndex.lie d).Group ≃* PSL2GF p n) := by
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
  obtain ⟨q, hq, hqp, hqn⟩ := hd
  obtain ⟨qp, qe, hqprime, hqpos⟩ := q
  simp only at hq hqp hqn
  subst hqp hqn
  subst hq
  exact ⟨CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 ⟨qp, qe, hqprime, hqpos⟩ hv⟩

theorem card_ne_nine_of_isLinTwoIndex {p n : ℕ} {d : TauCeti.ValidLieTypeIndex}
    (hd : IsLinTwoIndex p n d) : p ^ n ≠ 9 := by
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
  obtain ⟨q, hq, hqp, hqn⟩ := hd
  simp only at hq
  subst hq
  rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.isDuplicateRepresentative_iff] at hv
  simp only [TauCeti.PrimePower.card_def] at hv
  rw [← hqp, ← hqn]
  intro h9
  exact hv.2 (Or.inl ⟨trivial, Or.inr (Or.inr h9)⟩)

theorem center_eq_bot_of_center_quotient_psl2 {K : Type} [Group K] [Finite K] {p n : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hn : n ≠ 0) (h9 : p ^ n ≠ 9) (hK : Open.IsQuasisimple K)
    (hZ : IsPGroup p (Subgroup.center K)) (e : K ⧸ Subgroup.center K ≃* PSL2GF p n) :
    Subgroup.center K = ⊥ := by
  have : Group.IsPerfect K := ⟨hK.1⟩
  set π : K →* PSL2GF p n := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center K := by
    ext x
    simp only [π, MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
  have hodd : Odd (Nat.card π.ker) := by
    rw [hker]
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ
    rw [hk]
    exact Odd.pow (Nat.Prime.odd_of_ne_two Fact.out hp2)
  have h := (CFSG.SectionRank.OddCover.psl_two_perfect_odd_cover_kernel hp2
    (GaloisField.card p n hn) π hπ (hker.le) hodd).1 h9
  rwa [hker] at h

end CFSG.AGLEmbedding
