module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsPLType
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsSpTwo
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimOrders
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.AltRank
public import CFSG.LocalAnalysis.AGLEmbeddingD2.PairPureAssembly
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank
public import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.AGLEmbedding CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbeddingD2
  CFSG.AGLEmbeddingD2.McLaughlin

theorem exists_perfect_of_surj {H X : Type*} [Group H] [Finite H] [Group X] (φ : H →* X)
    (hφ : Function.Surjective φ) {X' : Subgroup X} (hX' : ⁅X', X'⁆ = X')
    (h3 : 3 ∣ Nat.card X') : ∃ Y : Subgroup H, ⁅Y, Y⁆ = Y ∧ 3 ∣ Nat.card Y := by
  classical
  have hex : ∃ n, ∃ Y : Subgroup H, Y.map φ = X' ∧ Nat.card Y = n :=
    ⟨_, X'.comap φ, Subgroup.map_comap_eq_self_of_surjective hφ _, rfl⟩
  obtain ⟨Y, hY, hYn⟩ := Nat.find_spec hex
  have hle : ⁅Y, Y⁆ ≤ Y := Subgroup.commutator_le.mpr fun g hg h hh => by
    rw [commutatorElement_def]
    exact Y.mul_mem (Y.mul_mem (Y.mul_mem hg hh) (Y.inv_mem hg)) (Y.inv_mem hh)
  have himg : (⁅Y, Y⁆).map φ = X' := by rw [Subgroup.map_commutator, hY, hX']
  have hmin := Nat.find_min' hex ⟨⁅Y, Y⁆, himg, rfl⟩
  refine ⟨Y, Subgroup.eq_of_le_of_card_ge hle (by omega), ?_⟩
  have hs : Function.Surjective (φ.subgroupMap Y) := MonoidHom.subgroupMap_surjective φ Y
  have h3' : 3 ∣ Nat.card (Y.map φ) := by rw [hY]; exact h3
  exact h3'.trans (Subgroup.card_dvd_of_surjective hs)

theorem three_dvd_card_catGroup_B {d : TauCeti.ValidLieTypeIndex} {k : ℕ} (hk : 3 ≤ k)
    (hd : ∃ q : TauCeti.PrimePower, q.card = 2 ∧ d.1 = .B k q) :
    3 ∣ Nat.card (CatGroup d) := by
  obtain ⟨q, hq2, hd⟩ := hd
  have hpe : q.p ^ q.exponent = 2 := (TauCeti.PrimePower.card_def q).symm.trans hq2
  have hdvd : q.p ∣ 2 := hpe ▸ dvd_pow_self q.p q.exponent_pos.ne'
  have hqp : q.p = 2 := (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).mp hdvd
  have hqe : q.exponent = 1 := by
    rw [hqp] at hpe
    exact Nat.pow_right_injective le_rfl (by simpa using hpe)
  rw [card_catGroup_B_even hk hqp hd, hqe]
  unfold CFSG.Open.ordBC
  rw [show Nat.gcd 2 (2 ^ 1 - 1) = 1 by norm_num, Nat.div_one]
  refine Dvd.dvd.mul_left ?_ _
  exact (show (3 : ℕ) ∣ 2 ^ (2 * 1) - 1 by norm_num).trans
    (Finset.dvd_prod_of_mem (fun i => 2 ^ (2 * i) - 1) (Finset.mem_Icc.mpr ⟨le_refl 1, by omega⟩))

theorem exists_perfect_of_B_quotient {H : Type} [Group H] [Finite H] {d : TauCeti.ValidLieTypeIndex}
    {k : ℕ} (hk : 3 ≤ k) (hd : ∃ q : TauCeti.PrimePower, q.card = 2 ∧ d.1 = .B k q)
    (e : H ⧸ CFSG.pCore 2 H ≃* (TauCeti.CFSGIndex.lie d).Group) :
    ∃ Y : Subgroup H, ⁅Y, Y⁆ = Y ∧ 3 ∣ Nat.card Y := by
  have hperf := kFactSpTwoPerfect_of_simple kFactSpTwoSimple_holds k d hk hd
  refine exists_perfect_of_surj (e.toMonoidHom.comp (QuotientGroup.mk' _))
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) (X' := ⊤) hperf ?_
  rw [Subgroup.card_top]
  exact three_dvd_card_catGroup_B hk hd

theorem exists_perfect_of_perm_six_quotient {H : Type} [Group H] [Finite H]
    (e : H ⧸ CFSG.pCore 2 H ≃* Equiv.Perm (Fin 6)) :
    ∃ Y : Subgroup H, ⁅Y, Y⁆ = Y ∧ 3 ∣ Nat.card Y := by
  have hA : ⁅(alternatingGroup (Fin 6) : Subgroup (Equiv.Perm (Fin 6))),
      (alternatingGroup (Fin 6) : Subgroup (Equiv.Perm (Fin 6)))⁆ = alternatingGroup (Fin 6) := by
    have h := commutator_alternatingGroup_eq_top (α := Fin 6) (by simp)
    have h2 := congrArg (Subgroup.map (alternatingGroup (Fin 6)).subtype) h
    rwa [commutator, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype] at h2
  refine exists_perfect_of_surj (e.toMonoidHom.comp (QuotientGroup.mk' _))
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
    (X' := (alternatingGroup (Fin 6) : Subgroup (Equiv.Perm (Fin 6)))) hA ?_
  have h2 := two_mul_nat_card_alternatingGroup (α := Fin 6)
  rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 6), Fintype.card_fin] at h2
  have h6 : Nat.factorial 6 = 720 := by decide
  have : Nat.card (alternatingGroup (Fin 6)) = 360 := by omega
  rw [show Nat.card ↥(alternatingGroup (Fin 6) : Subgroup (Equiv.Perm (Fin 6))) = 360 from this]
  norm_num

section Main

variable {G : Type} [Group G] [Finite G]

@[expose] def BlockExtras (M S L : Subgroup G) : Prop :=
  Open.IsKGroup ↥M ∧ Asc81bHyp M S ∧ ¬ InClassXBlock L ∧ ¬ IsSylowTwoOf (S ⊓ L) L

theorem not_blockPLThreeSolv_of_type (hT : CitedBlockTransvectionPLType) {M S L : Subgroup G}
    (hx : BlockExtras M S L) (hL : IsWeakSBlock M S L) (h3 : NineThreeThree M S L)
    (hr : 2 ≤ Open.pRank 3 L)
    (h6 : ¬ Nonempty (↥(barM M L) ≃* alternatingGroup (Fin 6))) : ¬ BlockPLThreeSolv M S L := by
  obtain ⟨hK, hA, hX, hS⟩ := hx
  obtain ⟨hOrth, hU4, hA5, hA6, hA8⟩ := hT G M S L hK hA hL hX hS h3
  set Pb := barM M (Subgroup.normalizer (S : Set G) ⊓ L) with hPb
  suffices hY : ∃ Y : Subgroup ↥Pb, ⁅Y, Y⁆ = Y ∧ 3 ∣ Nat.card Y by
    obtain ⟨Y, hYp, hY3⟩ := hY
    intro hsolv
    refine hsolv (Y.map Pb.subtype) (fun x ⟨y, _, hy⟩ => hy ▸ y.2) ?_ ?_
    · rw [← Subgroup.map_commutator, hYp]
    · rw [← Nat.card_congr (Y.equivMapOfInjective Pb.subtype Pb.subtype_injective).toEquiv]
      exact hY3
  have hrb : Open.pRank 3 (⊤ : Subgroup ↥(barM M L)) = Open.pRank 3 L := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup, pRank_barM_eq Nat.prime_three
      (by norm_num) M L hL.le]
  rcases h3.2.1 with ⟨d, ⟨m, q, hq, hd⟩, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · rcases hd with hd | hd | ⟨rfl, hd⟩
    · obtain ⟨d', ⟨q', hq', hd'⟩, ⟨φ⟩⟩ := hOrth m d ⟨q, hq, Or.inl hd⟩ ⟨e⟩
      have hm : 4 ≤ m := by
        have h := d.2
        rw [hd] at h
        exact (TauCeti.LieTypeIndex.inStandardRange_iff _).1
          ((TauCeti.LieTypeIndex.valid_iff _).1 h).1
      exact exists_perfect_of_B_quotient (k := m - 1) (by omega) ⟨q', hq', hd'⟩ φ
    · obtain ⟨d', ⟨q', hq', hd'⟩, ⟨φ⟩⟩ := hOrth m d ⟨q, hq, Or.inr hd⟩ ⟨e⟩
      have hm : 4 ≤ m := by
        have h := d.2
        rw [hd] at h
        exact (TauCeti.LieTypeIndex.inStandardRange_iff _).1
          ((TauCeti.LieTypeIndex.valid_iff _).1 h).1
      exact exists_perfect_of_B_quotient (k := m - 1) (by omega) ⟨q', hq', hd'⟩ φ
    · obtain ⟨e6⟩ := hU4 d ⟨q, hq, hd⟩ ⟨e⟩
      exact exists_perfect_of_perm_six_quotient
        (nonempty_quotient_pCore_mulEquiv_of_bot e6 pCore_perm_six_eq_bot).some
  · have hrk := (CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e).symm.trans hrb
    rcases hn with rfl | rfl | rfl
    · have := pRank_three_alternating_le (N := 5)
      omega
    · exact absurd ⟨e⟩ h6
    · obtain ⟨e6⟩ := hA8 ⟨e⟩
      exact exists_perfect_of_perm_six_quotient
        (nonempty_quotient_pCore_mulEquiv_of_bot e6 pCore_perm_six_eq_bot).some

end Main

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
