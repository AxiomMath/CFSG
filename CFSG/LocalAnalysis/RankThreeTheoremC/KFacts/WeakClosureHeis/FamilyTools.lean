module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

open CFSG.Open
open scoped commutatorElement

section Tools

theorem isMulCommutative_map_iff_of_injective {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (S : Subgroup G) :
    IsMulCommutative (S.map f) ↔ IsMulCommutative S := by
  rw [isMulCommutative_iff, isMulCommutative_iff]
  constructor
  · intro h a b
    have h1 := h ⟨f a, Subgroup.mem_map_of_mem f a.2⟩ ⟨f b, Subgroup.mem_map_of_mem f b.2⟩
    have h2 : f ((a : G) * b) = f ((b : G) * a) := by
      simpa [map_mul] using congrArg Subtype.val h1
    exact Subtype.ext (hf h2)
  · intro h a b
    obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.1 a.2
    obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.1 b.2
    apply Subtype.ext
    show (a : H) * b = b * a
    rw [← hxa, ← hyb, ← map_mul, ← map_mul]
    have := congrArg (fun z : S => f z) (h ⟨x, hx⟩ ⟨y, hy⟩)
    simpa using this

theorem isElemAbelian_map_iff_of_injective {p : ℕ} {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (E : Subgroup G) :
    IsElemAbelian p (E.map f) ↔ IsElemAbelian p E := by
  unfold IsElemAbelian
  rw [isMulCommutative_map_iff_of_injective f hf E]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h x hx
    apply hf
    rw [map_pow, map_one]
    exact h _ (Subgroup.mem_map_of_mem f hx)
  · rintro h _ ⟨x, hx, rfl⟩
    rw [← map_pow, h x hx, map_one]

variable {K : Type} [Group K] [Finite K] {p : ℕ}

theorem le_pRank_of_elemAbelian (hp : 1 < p) {H E : Subgroup K} (hEH : E ≤ H)
    (hE : IsElemAbelian p E) {k : ℕ} (hk : Nat.card E = p ^ k) : k ≤ CFSG.Open.pRank p H := by
  unfold CFSG.Open.pRank
  apply le_csSup
  · refine ⟨Nat.card K, ?_⟩
    rintro k' ⟨E', -, -, hk'⟩
    have h1 : p ^ k' ≤ Nat.card K := hk' ▸ Subgroup.card_le_card_group E'
    exact (Nat.lt_pow_self hp).le.trans h1
  · exact ⟨E, hEH, hE, hk⟩

theorem pRank_map_mulEquiv {L : Type} [Group L] [Finite L] (e : K ≃* L) (H : Subgroup K) :
    CFSG.Open.pRank p (H.map e.toMonoidHom) = CFSG.Open.pRank p H := by
  unfold CFSG.Open.pRank
  congr 1
  ext k
  constructor
  · rintro ⟨E, hEH, hE, hcard⟩
    refine ⟨E.map e.symm.toMonoidHom, ?_, ?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 (hEH hy)
      have : e.symm y = x := by rw [← hxy]; simp
      show e.symm y ∈ H
      rw [this]
      exact hx
    · exact (isElemAbelian_map_iff_of_injective _ e.symm.injective E).2 hE
    · rw [Subgroup.card_map_of_injective e.symm.injective]
      exact hcard
  · rintro ⟨E, hEH, hE, hcard⟩
    refine ⟨E.map e.toMonoidHom, Subgroup.map_mono hEH,
      (isElemAbelian_map_iff_of_injective _ e.injective E).2 hE, ?_⟩
    rw [Subgroup.card_map_of_injective e.injective]
    exact hcard

end Tools

namespace SylowDichotomyAt

variable {K : Type} [Group K] [Finite K] {p : ℕ}

theorem of_factorization_le (h : (Nat.card K).factorization p ≤ 3) : SylowDichotomyAt K p :=
  Or.inl h

theorem of_sylow_comm (h : ∀ S : Sylow p K, IsMulCommutative (S : Subgroup K)) :
    SylowDichotomyAt K p :=
  Or.inr (Or.inl h)

theorem of_pRank_le (h : CFSG.Open.pRank p (⊤ : Subgroup K) ≤ 2) : SylowDichotomyAt K p :=
  Or.inr (Or.inr (Or.inl h))

theorem of_violation {U : Subgroup K} (hU : IsPGroup p U)
    (h : 4 ≤ CFSG.Open.pRank p U ∨ ¬ IsCyclic ↥⁅U, U⁆ ∨
      ((∀ u ∈ U, u ^ p = 1) ∧ p ^ 5 ≤ Nat.card U)) : SylowDichotomyAt K p :=
  Or.inr (Or.inr (Or.inr ⟨U, hU, h⟩))

theorem of_four_le_pRank {U : Subgroup K} (hU : IsPGroup p U) (h : 4 ≤ CFSG.Open.pRank p U) :
    SylowDichotomyAt K p :=
  of_violation hU (Or.inl h)

theorem of_not_cyclic_derived {U : Subgroup K} (hU : IsPGroup p U) (h : ¬ IsCyclic ↥⁅U, U⁆) :
    SylowDichotomyAt K p :=
  of_violation hU (Or.inr (Or.inl h))

theorem of_exponent {U : Subgroup K} (hU : IsPGroup p U) (hexp : ∀ u ∈ U, u ^ p = 1)
    (hcard : p ^ 5 ≤ Nat.card U) : SylowDichotomyAt K p :=
  of_violation hU (Or.inr (Or.inr ⟨hexp, hcard⟩))

theorem of_elemAbelian (hp : p.Prime) {E : Subgroup K} (hE : IsElemAbelian p E) {k : ℕ}
    (hk : Nat.card E = p ^ k) (h4 : 4 ≤ k) : SylowDichotomyAt K p := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact of_four_le_pRank (IsPGroup.of_card hk)
    (h4.trans (le_pRank_of_elemAbelian hp.one_lt le_rfl hE hk))

theorem of_card_elemAbelian_le (hp : p.Prime)
    (h : ∀ F : Subgroup K, IsElemAbelian p F → Nat.card F ≤ p ^ 2) : SylowDichotomyAt K p := by
  apply of_pRank_le
  unfold CFSG.Open.pRank
  refine csSup_le ⟨0, ⊥, bot_le, ⟨inferInstance, fun x hx => by
    rw [(Subgroup.mem_bot).1 hx, one_pow]⟩, by simp⟩ ?_
  rintro k ⟨E, -, hE, hk⟩
  have := h E hE
  rw [hk] at this
  exact (Nat.pow_le_pow_iff_right hp.one_lt).1 this

theorem of_four_le_pRank_top (hp : p.Prime) (h : 4 ≤ CFSG.Open.pRank p (⊤ : Subgroup K)) :
    SylowDichotomyAt K p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hne : {k | ∃ E : Subgroup K, E ≤ (⊤ : Subgroup K) ∧ IsElemAbelian p E ∧
      Nat.card E = p ^ k}.Nonempty :=
    ⟨0, ⊥, bot_le, ⟨inferInstance, fun x hx => by
      rw [(Subgroup.mem_bot).1 hx, one_pow]⟩, by simp⟩
  have hbdd : BddAbove {k | ∃ E : Subgroup K, E ≤ (⊤ : Subgroup K) ∧ IsElemAbelian p E ∧
      Nat.card E = p ^ k} := by
    refine ⟨Nat.card K, ?_⟩
    rintro k' ⟨E', -, -, hk'⟩
    have h1 : p ^ k' ≤ Nat.card K := hk' ▸ Subgroup.card_le_card_group E'
    exact (Nat.lt_pow_self hp.one_lt).le.trans h1
  obtain ⟨E, -, hE, hk⟩ := Nat.sSup_mem hne hbdd
  exact of_elemAbelian hp hE hk h

theorem of_abelian_full (hp : p.Prime) {A : Subgroup K} (hA : IsMulCommutative A)
    (hcard : Nat.card A = p ^ (Nat.card K).factorization p) : SylowDichotomyAt K p := by
  haveI : Fact p.Prime := ⟨hp⟩
  apply of_sylow_comm
  intro S
  let A' : Sylow p K := Sylow.ofCard A hcard
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K A' S
  have h2 : ((g • A' : Sylow p K) : Subgroup K) = (S : Subgroup K) := congrArg _ hg
  have hA' : (A' : Subgroup K) = A := Sylow.coe_ofCard _ _
  have hS : (S : Subgroup K) = A.map (MulAut.conj g).toMonoidHom := by
    rw [← h2, Sylow.coe_subgroup_smul, hA']
    ext x
    simp [Subgroup.mem_map, Subgroup.mem_smul_pointwise_iff_exists]
  rw [hS]
  exact (isMulCommutative_map_iff_of_injective _ (MulAut.conj g).injective A).2 hA

theorem of_mulEquiv {L : Type} [Group L] [Finite L] (hp : p.Prime) (e : K ≃* L)
    (h : SylowDichotomyAt L p) : SylowDichotomyAt K p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card K = Nat.card L := Nat.card_congr e.toEquiv
  rcases h with h | h | h | ⟨U, hU, hv⟩
  · exact of_factorization_le (by rwa [hcard])
  · apply of_sylow_comm
    intro S
    have hcardP : Nat.card (S.map e.toMonoidHom) = p ^ (Nat.card L).factorization p := by
      rw [Subgroup.card_map_of_injective e.injective, S.card_eq_multiplicity, hcard]
    let P' : Sylow p L := Sylow.ofCard (S.map e.toMonoidHom) hcardP
    have hP' : (P' : Subgroup L) = (S : Subgroup K).map e.toMonoidHom := Sylow.coe_ofCard _ _
    have := h P'
    rw [hP'] at this
    exact (isMulCommutative_map_iff_of_injective _ e.injective _).1 this
  · apply of_pRank_le
    have := pRank_map_mulEquiv (p := p) e (⊤ : Subgroup K)
    rw [Subgroup.map_top_of_surjective _ e.surjective] at this
    omega
  ·
    refine of_violation (U := U.map e.symm.toMonoidHom) (hU.map _) ?_
    rcases hv with h4 | hnc | ⟨hexp, hc⟩
    · left
      have := pRank_map_mulEquiv (p := p) e.symm U
      omega
    · right; left
      intro hcyc
      apply hnc
      have hmap : ⁅U.map e.symm.toMonoidHom, U.map e.symm.toMonoidHom⁆ =
          (⁅U, U⁆).map e.symm.toMonoidHom := (Subgroup.map_commutator _ _ _).symm
      rw [hmap] at hcyc
      haveI : IsCyclic ↥((⁅U, U⁆).map e.symm.toMonoidHom) := hcyc
      exact isCyclic_of_surjective
        (Subgroup.equivMapOfInjective ⁅U, U⁆ e.symm.toMonoidHom e.symm.injective).symm.toMonoidHom
        (MulEquiv.surjective _)
    · right; right
      refine ⟨?_, ?_⟩
      · rintro _ ⟨u, hu, rfl⟩
        show e.symm u ^ p = 1
        rw [← map_pow, hexp u hu, map_one]
      · rw [Subgroup.card_map_of_injective e.symm.injective]
        exact hc

end SylowDichotomyAt


end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
