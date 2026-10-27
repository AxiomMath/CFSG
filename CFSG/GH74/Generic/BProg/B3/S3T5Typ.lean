module

public import CFSG.GH74.Generic.BProg.B3.S3T5Cls
public import CFSG.GH74.Generic.BProg.B3.S3T5A7M
public import CFSG.GH74.Generic.BProg.B3.S3T5L2Bal
public import CFSG.GH74.Generic.BProg.B3.SolvStabL34
public import CFSG.GH74.Generic.BProg.B3.S3SL2Depth
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SubSec31TwoAux
public import CFSG.GH74.GLS.C3.Layer1.Th2BalK10
public import CFSG.GH74.Generic.BProg.B3.S3Ctx29wDefs

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3T5

namespace W

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg
  CFSG.ClassicalInvolution.Balance CFSG.Assembly.LowTwoRank Subgroup
open scoped MatrixGroups

theorem pow_two_of_fm9 {p f : ℕ} (hp : p.Prime) (h : IsFM9 (p ^ f)) : ∃ k : ℕ, f = 2 ^ k := by
  rcases h with h9 | ⟨hpr, -⟩
  · have hf0 : f ≠ 0 := by
      rintro rfl
      norm_num at h9
    have hp3 : p = 3 := by
      have hdvd : p ∣ 3 ^ 2 := by
        rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← h9]
        exact dvd_pow_self p hf0
      exact Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_three hdvd
    subst hp3
    have hf : f = 2 := Nat.pow_right_injective (a := 3) (by norm_num)
      (show 3 ^ f = 3 ^ 2 by rw [h9])
    exact ⟨1, by rw [hf]; norm_num⟩
  · exact ⟨0, by rw [Nat.Prime.eq_one_of_pow hpr]; norm_num⟩

theorem center_eq_bot_of_perfect {X : Type*} [Group X] [IsSimpleGroup X] [Group.IsPerfect X] :
    center X = ⊥ := by
  rcases (inferInstance : (center X).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have hab : commutator X = ⊥ := by
      rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a _
      rw [Subgroup.mem_centralizer_iff]
      intro c _
      exact (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a)) c
    have htop : commutator X = ⊤ := Group.IsPerfect.commutator_eq_top
    obtain ⟨y, hy⟩ := exists_ne (1 : X)
    have hy' : y ∈ commutator X := htop ▸ Subgroup.mem_top y
    rw [hab, Subgroup.mem_bot] at hy'
    exact hy hy'

theorem not_isSolvable_of_quasisimple {X : Type*} [Group X] (hX : IsQuasisimple X) :
    ¬ Group.IsSolvable X := by
  intro hs
  have : Nontrivial X := CFSG.LocalCores.isQuasisimple_nontrivial hX
  have : Group.IsPerfect X := hX.1
  have h1 := Group.IsSolvable.commutator_lt_top_of_nontrivial X
  rw [Group.IsPerfect.commutator_eq_top] at h1
  exact lt_irrefl _ h1

theorem exists_pow_of_sl2
    {Q : Type} [Group Q] [Finite Q] (hq : IsQuasisimple Q)
    {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F)) (eF : Q ≃* StatedSL 2 F)
    (hnZ : ¬ Th2.Bal.IsLocallyKBalanced 2 (Q ⧸ center Q)) :
    ∃ r m : ℕ, r.Prime ∧ r ≠ 2 ∧ (¬ ∃ k : ℕ, m = 2 ^ k) ∧ Nat.card F = r ^ m := by
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨p, -, n, hp, hn⟩ := FiniteField.card' (K := F)
  have hcard : Nat.card F = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have hp2 : p ≠ 2 := by
    rintro rfl
    rw [hcard] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, n.pos.ne'⟩)
  have h3 : Nat.card F ≠ 3 := by
    intro h3
    apply not_isSolvable_of_quasisimple hq
    have := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.isSolvable_statedSL_of_card_three h3
    exact Group.isSolvable_of_surjective (f := eF.symm.toMonoidHom) eF.symm.surjective
  refine ⟨p, n, hp, hp2, ?_, hcard⟩
  rintro ⟨k, hk⟩
  apply hnZ
  have h1 : 1 < Nat.card F := Finite.one_lt_card
  have hF : IVK.L2Field F := ⟨hodd, by obtain ⟨m, hm⟩ := hodd; omega⟩
  let e' : SL(2, F) ≃* Q :=
    (specialLinearGroupEquivStatedSL 2 F).trans eF.symm
  let e₁ : Q ⧸ center Q ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
    (QuotientGroup.congr (center SL(2, F)) (center Q) e' (Subgroup.map_center_eq e')).symm
  exact S3T5.isLocallyKBalanced_two_of_pow_two hF (e₁.trans (IVK.L2.equivPSL F).symm) hp
    (by rw [hcard, hk])

variable {G : Type} [Group G] [Finite G] {x : G} {K B : Subgroup G} {b : G} {D J : Subgroup G}

theorem type_of_obs52
    (hF1 : AltLocBal2) (hF2 : L3OuterOddCore) (hGKF : GenericKnownFacts)
    (hE2 : E2.E2ComponentFacts) (hyp : Hyp2 G) (hc : IsJ2Circ x K)
    (h3 : QShape3 (↥K ⧸ pPrimeCore 2 ↥K)) (h : Obs52 B b D J)
    (hBel : CFSG.IsElementaryAbelian 2 ↥B) (hB3 : 3 ≤ pRank 2 ↥B)
    (h11 : ¬ IsDoubleCoverOfAlt (kBar J) 11) : IsA7Bar J ∨ IsL2OddW J := by
  classical
  have hnb : ¬ Th2.Bal.IsLocallyKBalanced 2 (kBar J) := not_isLocallyKBalanced_two h hBel
  have hq : IsQuasisimple (kBar J) := TwoThin.isQuasisimple_hat h.comp
  have : Group.IsPerfect (kBar J) := hq.1
  have hnZ : ¬ Th2.Bal.IsLocallyKBalanced 2 (kBar J ⧸ center (kBar J)) := fun hl =>
    hnb (isLocallyKBalanced_of_center_quotient hl)
  have hb2 : orderOf b = 2 := h.b_ord
  have hILo : IsILo 2 b J := by
    refine ⟨h.b_ord, ?_, h.comp⟩
    calc oBound 2 = 3 := rfl
      _ ≤ pRank 2 ↥B := hB3
      _ ≤ pRank 2 ↥(centralizer ({b} : Set G)) :=
        C3.Layer1.Back.pRank_mono' (B_le_centralizer h)
  have hKP : IsKProperSimple G := ⟨hyp.simple, hyp.nonab, CFSG.GH74.kProper_of_kgh hyp.kgh⟩
  set L : Subgroup (CentralizerBar b) :=
    (J.subgroupOf (centralizer ({b} : Set G))).map (Th2.Bal.piBar b) with hL
  have hLc : IsComponent L :=
    TwoThin.isComponent_map_barMk (TwoThin.isPCompIn_two_iff.mp h.comp).2
  obtain ⟨e⟩ := Th2.Bal.kBar_equiv_of_over h.comp hL.symm
  have hK2 : InCalK2 (kBar J) :=
    inCalK2_of_mulEquiv e.symm (inCalK2_of_isComponent hKP hb2 hLc)
  by_cases hC2 : InC2 (kBar J)
  ·
    exfalso
    by_cases hfm : HasL2Model (kBar J) IsFM9
    · obtain ⟨p, f, hp, -, hfm9, hLie⟩ := hfm
      exact S3T5.not_pow_two_of_not_locallyBalanced hp (isFM9_odd hfm9) hLie hnZ
        (pow_two_of_fm9 hp hfm9)
    · have hC2L : InC2 ↥L := E2.inC2_of_mulEquiv e hC2
      have hnoL : ¬ HasL2Model ↥L IsFM9 := fun hl =>
        hfm (TwoThin.hasL2Model_of_mulEquiv e.symm hl)
      have hS : Prop27.Shapes7 ↥L := Prop27.shapes7_of_component hGKF hE2
        (Prop27.compData7_of_component hyp.gen4 hb2 hC2L hnoL) hC2L.2.2.1
      have hLB := Prop27.locBal2_of_shapes7 Prop27.prop27LocalBalance hS
      have hbal := Th2.Bal.isLocallyKBalanced_of_locBal2 (Prop27.center_quotient_eq_bot hLc.1)
        hLB (k := 2) (by norm_num)
      have : Group.IsPerfect ↥L := hLc.1.1
      exact hnb (isLocallyKBalanced_of_mulEquiv e (isLocallyKBalanced_of_center_quotient hbal))
  by_cases hT2 : InT2 (kBar J)
  ·
    obtain ⟨-, hT⟩ := hT2
    rcases hT with ⟨p, f, hp, hf, ⟨hodd, -⟩, hLie⟩ | ⟨F, _, _, hodd, ⟨eF⟩⟩ | hA |
      ⟨n, hn7, hn11, hcov⟩ | ⟨hL34, -⟩
    · right
      have hp2 : p ≠ 2 := by
        rintro rfl
        exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, by omega⟩)
      exact ⟨p, f, hp, hp2, S3T5.not_pow_two_of_not_locallyBalanced hp hodd hLie hnZ,
        Or.inl hLie⟩
    · right
      obtain ⟨r, m, hr, hr2, hm, hcard⟩ := exists_pow_of_sl2 hq hodd eF hnZ
      exact ⟨r, m, hr, hr2, hm, Or.inr ⟨F, inferInstance, inferInstance, hcard, ⟨eF⟩⟩⟩
    · exact Or.inl hA
    · exfalso
      interval_cases n
      · exact false_of_twoA7 hyp h hBel hB3 hcov
      · exact hnZ (hF1 _ 8 le_rfl (by norm_num) hcov.2.2)
      · exact hnZ (hF1 _ 9 (by norm_num) (by norm_num) hcov.2.2)
      · exact hnZ (hF1 _ 10 (by norm_num) le_rfl hcov.2.2)
      · exact absurd hcov h11
    · exact (false_of_isL34Quotient hyp.gen4 hb2 h.comp hL34).elim
  ·
    exfalso
    have hG2 : InG2 (kBar J) := ⟨hK2, hC2, hT2⟩
    rcases depth7_simple hc h3 hILo hG2 with ⟨-, h7⟩ | ⟨-, h8⟩
    · have hL3 : IsL3OddGt3 (kBar J) := by
        rcases h7 with ⟨hi, -⟩ | ⟨hi, -⟩ | ⟨hi, -⟩ | ⟨hi, -⟩ | ⟨hi, -⟩ | ⟨hi, -⟩ | ⟨-, hL3⟩ |
          ⟨hi, -⟩
        all_goals first | exact hL3 | omega
      have : IsSimpleGroup (kBar J) := (LocBalL3.modelData_of_qShape3 hL3).1
      exact hnb (isLocallyKBalanced_two_of_l3 hF2 hL3 center_eq_bot_of_perfect)
    · rcases h8 with ⟨hi, -⟩ | ⟨hi, -⟩ | ⟨hi, -⟩ | ⟨hi, -⟩ | ⟨hi, -⟩ | ⟨hi, -⟩ | ⟨hi, -⟩ |
        ⟨-, -, hA9 | hA10⟩
      all_goals first
        | omega
        | exact hnb (hF1 _ 9 (by norm_num) (by norm_num) hA9)
        | exact hnb (hF1 _ 10 (by norm_num) le_rfl hA10)

end W

end S3T5

end CFSG.GH74.Generic.BProg.B3
