module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsPL
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactsThreeFive
public import CFSG.RankThree.PartOne.S12.Sec154Fin

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.RankThree.PartOne.Sec154Fin (klein4 isKlein pCore_s4)

section TwoCore

theorem eq_bot_of_normal_two_group_of_preprimitive {G X : Type*} [Group G] [Finite G]
    [MulAction G X] [Finite X] [FaithfulSMul G X] (hprim : MulAction.IsPreprimitive G X)
    (hX : ∀ j, Nat.card X ≠ 2 ^ j) {N : Subgroup G} [N.Normal] (hN : IsPGroup 2 N) : N = ⊥ := by
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  apply eq_of_smul_eq_smul (α := X)
  intro x
  rw [one_smul]
  have hB := MulAction.IsBlock.orbit_of_normal (G := G) (N := N) x
  rcases hprim.isTrivialBlock_of_isBlock hB with hsub | huniv
  · exact hsub (MulAction.mem_orbit x (⟨n, hn⟩ : N)) (MulAction.mem_orbit_self x)
  · exfalso
    have hcard : (MulAction.orbit N x).ncard = Nat.card X := by
      rw [huniv, Set.ncard_univ]
    have hdvd : (MulAction.orbit N x).ncard ∣ Nat.card N := by
      rw [← MulAction.index_stabilizer N x]
      exact Subgroup.index_dvd_card _
    rw [hcard] at hdvd
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := hN.exists_card_eq
    rw [hk] at hdvd
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact hX j hj

theorem pCore_perm_eq_bot (n : ℕ) (hn : ∀ j, n ≠ 2 ^ j) :
    CFSG.pCore 2 (Equiv.Perm (Fin n)) = ⊥ := by
  have h2 := Equiv.Perm.isMultiplyPretransitive (Fin n) 2
  refine eq_bot_of_normal_two_group_of_preprimitive
    (MulAction.isPreprimitive_of_is_two_pretransitive h2) (fun j hj => ?_) CFSG.pCore_isPGroup
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hj
  exact hn j hj

theorem pCore_perm_three_eq_bot : CFSG.pCore 2 (Equiv.Perm (Fin 3)) = ⊥ :=
  pCore_perm_eq_bot 3 fun j hj => by
    have : j < 2 := by
      by_contra h
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (not_lt.1 h)
      omega
    interval_cases j <;> omega

theorem pCore_perm_six_eq_bot : CFSG.pCore 2 (Equiv.Perm (Fin 6)) = ⊥ :=
  pCore_perm_eq_bot 6 fun j hj => by
    have : j < 3 := by
      by_contra h
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (not_lt.1 h)
      omega
    interval_cases j <;> omega

end TwoCore

section S4

@[expose] def pairClass (x y : Fin 4) : Fin 3 :=
  (![![0, 0, 1, 2], ![0, 0, 2, 1], ![1, 2, 0, 0], ![2, 1, 0, 0]] : Fin 4 → Fin 4 → Fin 3) x y

@[expose] def pairAct (σ : Equiv.Perm (Fin 4)) (i : Fin 3) : Fin 3 := pairClass (σ 0) (σ i.succ)

theorem pairAct_one : ∀ i, pairAct 1 i = i := by decide +kernel

theorem pairAct_mul : ∀ σ τ : Equiv.Perm (Fin 4), ∀ i,
    pairAct (σ * τ) i = pairAct σ (pairAct τ i) := by
  decide +kernel

theorem pairAct_inv_left : ∀ σ : Equiv.Perm (Fin 4), ∀ i, pairAct σ⁻¹ (pairAct σ i) = i := by
  decide +kernel

theorem pairAct_inv_right : ∀ σ : Equiv.Perm (Fin 4), ∀ i, pairAct σ (pairAct σ⁻¹ i) = i := by
  decide +kernel

theorem pairAct_surjective : ∀ τ : Equiv.Perm (Fin 3), ∃ σ : Equiv.Perm (Fin 4),
    ∀ i, pairAct σ i = τ i := by
  decide +kernel

theorem pairAct_ker : ∀ σ : Equiv.Perm (Fin 4), (∀ i, pairAct σ i = i) ↔ isKlein σ := by
  decide +kernel

@[expose] def s4toS3 : Equiv.Perm (Fin 4) →* Equiv.Perm (Fin 3) where
  toFun σ := ⟨pairAct σ, pairAct σ⁻¹, pairAct_inv_left σ, pairAct_inv_right σ⟩
  map_one' := Equiv.ext pairAct_one
  map_mul' σ τ := Equiv.ext (pairAct_mul σ τ)

theorem s4toS3_surjective : Function.Surjective s4toS3 := fun τ => by
  obtain ⟨σ, hσ⟩ := pairAct_surjective τ
  exact ⟨σ, Equiv.ext hσ⟩

theorem ker_s4toS3 : s4toS3.ker = klein4 := by
  ext σ
  rw [MonoidHom.mem_ker, Equiv.ext_iff]
  exact pairAct_ker σ

noncomputable def s4QuotientEquiv :
    Equiv.Perm (Fin 4) ⧸ CFSG.pCore 2 (Equiv.Perm (Fin 4)) ≃* Equiv.Perm (Fin 3) :=
  (QuotientGroup.quotientMulEquivOfEq (pCore_s4.trans ker_s4toS3.symm)).trans
    (QuotientGroup.quotientKerEquivOfSurjective s4toS3 s4toS3_surjective)

end S4

section Quotient

theorem nonempty_quotient_pCore_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    Nonempty (X ⧸ CFSG.pCore 2 X ≃* Y ⧸ CFSG.pCore 2 Y) :=
  haveI := CFSG.pCore_normal (p := 2) (G := X)
  haveI := CFSG.pCore_normal (p := 2) (G := Y)
  ⟨QuotientGroup.congr (CFSG.pCore 2 X) (CFSG.pCore 2 Y) e (CFSG.pCore_map_iso 2 e)⟩

theorem nonempty_quotient_pCore_mulEquiv_of_bot {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (hY : CFSG.pCore 2 Y = ⊥) : Nonempty (X ⧸ CFSG.pCore 2 X ≃* Y) := by
  obtain ⟨φ⟩ := nonempty_quotient_pCore_mulEquiv e
  exact ⟨φ.trans ((QuotientGroup.quotientMulEquivOfEq hY).trans QuotientGroup.quotientBot)⟩

end Quotient

@[expose] def CitedBlockTransvectionPLType : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), Open.IsKGroup ↥M →
    Asc81bHyp M S → IsWeakSBlock M S L → ¬ InClassXBlock L → ¬ IsSylowTwoOf (S ⊓ L) L →
    NineThreeThree M S L →
    (∀ (m : ℕ) (d : TauCeti.ValidLieTypeIndex),
        (∃ q : TauCeti.PrimePower, q.card = 2 ∧ (d.1 = .D m q ∨ d.1 = .twistedD m q)) →
        Nonempty (↥(barM M L) ≃* (TauCeti.CFSGIndex.lie d).Group) →
        ∃ d' : TauCeti.ValidLieTypeIndex,
          (∃ q : TauCeti.PrimePower, q.card = 2 ∧ d'.1 = .B (m - 1) q) ∧
          Nonempty (↥(blockPL M S L) ⧸ CFSG.pCore 2 ↥(blockPL M S L) ≃*
            (TauCeti.CFSGIndex.lie d').Group)) ∧
    (∀ d : TauCeti.ValidLieTypeIndex,
        (∃ q : TauCeti.PrimePower, q.card = 2 ∧ d.1 = .twistedA 3 q) →
        Nonempty (↥(barM M L) ≃* (TauCeti.CFSGIndex.lie d).Group) →
        Nonempty (↥(blockPL M S L) ≃* Equiv.Perm (Fin 6))) ∧
    (Nonempty (↥(barM M L) ≃* alternatingGroup (Fin 5)) →
        Nonempty (↥(blockPL M S L) ≃* Equiv.Perm (Fin 3))) ∧
    (Nonempty (↥(barM M L) ≃* alternatingGroup (Fin 6)) →
        Nonempty (↥(blockPL M S L) ≃* Equiv.Perm (Fin 4))) ∧
    (Nonempty (↥(barM M L) ≃* alternatingGroup (Fin 8)) →
        Nonempty (↥(blockPL M S L) ≃* Equiv.Perm (Fin 6)))

theorem citedBlockTransvectionPL_of_type (hT : CitedBlockTransvectionPLType) :
    CitedBlockTransvectionPL := by
  intro G _ _ M S L hK hA hL hX hS h3
  obtain ⟨hOrth, hU4, hA5, hA6, hA8⟩ := hT G M S L hK hA hL hX hS h3
  rcases h3.2.1 with ⟨d, ⟨m, q, hq, hd⟩, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · rcases hd with hd | hd | ⟨rfl, hd⟩
    · obtain ⟨d', ⟨q', hq', hd'⟩, hP⟩ := hOrth m d ⟨q, hq, Or.inl hd⟩ ⟨e⟩
      have hm : 4 ≤ m := by
        have h := d.2
        rw [hd] at h
        exact (TauCeti.LieTypeIndex.inStandardRange_iff _).1
          ((TauCeti.LieTypeIndex.valid_iff _).1 h).1
      exact Or.inl ⟨m - 1, d', by omega, ⟨q', hq', hd'⟩, hP⟩
    · obtain ⟨d', ⟨q', hq', hd'⟩, hP⟩ := hOrth m d ⟨q, hq, Or.inr hd⟩ ⟨e⟩
      have hm : 4 ≤ m := by
        have h := d.2
        rw [hd] at h
        exact (TauCeti.LieTypeIndex.inStandardRange_iff _).1
          ((TauCeti.LieTypeIndex.valid_iff _).1 h).1
      exact Or.inl ⟨m - 1, d', by omega, ⟨q', hq', hd'⟩, hP⟩
    · obtain ⟨e6⟩ := hU4 d ⟨q, hq, hd⟩ ⟨e⟩
      obtain ⟨φ⟩ := nonempty_quotient_pCore_mulEquiv_of_bot e6 pCore_perm_six_eq_bot
      exact Or.inr ⟨6, Or.inr (Or.inr rfl), ⟨φ⟩⟩
  · rcases hn with rfl | rfl | rfl
    · obtain ⟨e3⟩ := hA5 ⟨e⟩
      obtain ⟨φ⟩ := nonempty_quotient_pCore_mulEquiv_of_bot e3 pCore_perm_three_eq_bot
      exact Or.inr ⟨3, Or.inl rfl, ⟨φ⟩⟩
    · obtain ⟨e4⟩ := hA6 ⟨e⟩
      obtain ⟨φ⟩ := nonempty_quotient_pCore_mulEquiv e4
      exact Or.inr ⟨3, Or.inl rfl, ⟨φ.trans s4QuotientEquiv⟩⟩
    · obtain ⟨e6⟩ := hA8 ⟨e⟩
      obtain ⟨φ⟩ := nonempty_quotient_pCore_mulEquiv_of_bot e6 pCore_perm_six_eq_bot
      exact Or.inr ⟨6, Or.inr (Or.inr rfl), ⟨φ⟩⟩

end CFSG.AGLEmbedding
