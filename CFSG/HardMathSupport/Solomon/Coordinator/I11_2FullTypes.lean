module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_TablesA
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointAutRank
public import CFSG.LocalAnalysis.AGLEmbedding.AltOuterOdd
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentOffCharAut
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs2

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Timmesfeld.ComponentBalance

section Transport

variable {X Y : Type*} [Group X] [Group Y]

theorem i112f_hat_of_mulEquiv (e : X ≃* Y) {S : Type*} [Group S]
    (h : commutator X = ⊤ ∧ Nat.card (Subgroup.center X) = 3 ∧
      Nonempty ((X ⧸ Subgroup.center X) ≃* S)) :
    commutator Y = ⊤ ∧ Nat.card (Subgroup.center Y) = 3 ∧
      Nonempty ((Y ⧸ Subgroup.center Y) ≃* S) := by
  obtain ⟨hc, hcard, ⟨f⟩⟩ := h
  have hcen : (Subgroup.center X).map e.toMonoidHom = Subgroup.center Y :=
    Subgroup.map_center_eq e
  refine ⟨?_, ?_, ⟨(QuotientGroup.congr _ _ e hcen).symm.trans f⟩⟩
  · have h1 := congrArg (Subgroup.map e.toMonoidHom) hc
    rw [commutator, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] at h1
    rw [commutator]
    exact h1
  · rw [← hcen, Subgroup.card_map_of_injective e.injective, hcard]

theorem i112f_isHatSix_of_mulEquiv (e : X ≃* Y) (h : IsHatSix X) : IsHatSix Y :=
  i112f_hat_of_mulEquiv e h

theorem i112f_isHatSeven_of_mulEquiv (e : X ≃* Y) (h : IsHatSeven X) : IsHatSeven Y :=
  i112f_hat_of_mulEquiv e h

theorem i112f_isHatMTwentyTwo_of_mulEquiv (e : X ≃* Y) (h : IsHatMTwentyTwo X) :
    IsHatMTwentyTwo Y :=
  i112f_hat_of_mulEquiv e h

theorem i112f_isSLThreeExc_of_mulEquiv (e : X ≃* Y) (h : IsSLThreeExc X) : IsSLThreeExc Y := by
  obtain ⟨K, hK, hf, hq, ⟨f⟩⟩ := h
  exact ⟨K, hK, hf, hq, ⟨e.symm.trans f⟩⟩

theorem i112f_isSUThreeExc_of_mulEquiv (e : X ≃* Y) (h : IsSUThreeExc X) : IsSUThreeExc Y := by
  obtain ⟨K, hK, hf, q, hq, hq9, ⟨f⟩⟩ := h
  exact ⟨K, hK, hf, q, hq, hq9, ⟨e.symm.trans f⟩⟩

theorem i112f_isLTwoOddPow_of_mulEquiv (e : X ≃* Y) (h : IsLTwoOddPow X) : IsLTwoOddPow Y := by
  obtain ⟨K, hK, hf, n, hn, hn1, hcard, ⟨f⟩⟩ := h
  exact ⟨K, hK, hf, n, hn, hn1, hcard, ⟨e.symm.trans f⟩⟩

theorem i112f_pRank_mulAut_of_mulEquiv [Finite X] [Finite Y] (e : X ≃* Y) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut X)) = CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut Y)) :=
  CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) (MulAut.congr e)

theorem i112f_center_eq_bot_of_mulEquiv (e : X ≃* Y) (h : Subgroup.center Y = ⊥) :
    Subgroup.center X = ⊥ := by
  have hcen : (Subgroup.center X).map e.toMonoidHom = Subgroup.center Y :=
    Subgroup.map_center_eq e
  rw [h] at hcen
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 hcen

end Transport

section LTwo

theorem i112f_isLTwoOddPow_of_isL2 {L : Type*} [Group L] (h : IsL2TwoPowOdd L) :
    IsLTwoOddPow L := by
  obtain ⟨n, hn, hn1, ⟨e⟩⟩ := h.exists_mulEquiv_sl2
  exact ⟨GaloisField 2 n, inferInstance, inferInstance, n, Nat.odd_iff.1 hn, hn1,
    GaloisField.card 2 n (by omega),
    ⟨e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 (GaloisField 2 n))⟩⟩

theorem i112f_pRank_mulAut_L2 {L : Type} [Group L] [Finite L] (h : IsL2TwoPowOdd L) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut L)) ≤ 2 :=
  CFSG.SectionRank.pRank_le (by norm_num) fun E _ hE => by
    have := (table113_T2 L h E hE).1
    norm_num
    exact this

end LTwo

section Hat

theorem i112f_pRank_mulAut_le_quot {K : Type} [Group K] [Finite K] (hK : commutator K = ⊤) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut K)) ≤
      CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (K ⧸ Subgroup.center K))) := by
  let β : MulAut K →* MulAut (K ⧸ Subgroup.center K) :=
    { toFun := fun α => QuotientGroup.congr _ _ α (Subgroup.map_center_eq α)
      map_one' := by
        ext q
        induction q using QuotientGroup.induction_on
        rfl
      map_mul' := by
        intro α γ
        ext q
        induction q using QuotientGroup.induction_on
        rfl }
  have hβ : ∀ (α : MulAut K) (x : K), β α (QuotientGroup.mk x) = QuotientGroup.mk (α x) :=
    fun α x => rfl
  have hinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro α hα
    have hc : ∀ x : K, x⁻¹ * α x ∈ Subgroup.center K := by
      intro x
      have h1 := congrArg (fun φ : MulAut (K ⧸ Subgroup.center K) => φ (QuotientGroup.mk x)) hα
      simp only [hβ, MulAut.one_apply] at h1
      exact QuotientGroup.eq.1 h1.symm
    let δ : K →* ↥(Subgroup.center K) :=
      { toFun := fun x => ⟨x⁻¹ * α x, hc x⟩
        map_one' := by
          apply Subtype.ext
          simp
        map_mul' := by
          intro x y
          apply Subtype.ext
          have hxc := Subgroup.mem_center_iff.1 (hc x) (y⁻¹)
          simp only [Subgroup.coe_mul, mul_inv_rev, map_mul]
          calc y⁻¹ * x⁻¹ * (α x * α y) = y⁻¹ * (x⁻¹ * α x) * α y := by group
            _ = (x⁻¹ * α x) * y⁻¹ * α y := by rw [← hxc]
            _ = x⁻¹ * α x * (y⁻¹ * α y) := by group }
    have hδ : ∀ x : K, δ x = 1 := fun x =>
      (Abelianization.commutator_subset_ker δ (hK ▸ Subgroup.mem_top x) : x ∈ δ.ker)
    refine MulEquiv.ext fun x => ?_
    have h1 : x⁻¹ * α x = 1 := congrArg Subtype.val (hδ x)
    rw [MulAut.one_apply]
    calc α x = x * (x⁻¹ * α x) := by group
      _ = x := by rw [h1, mul_one]
  calc CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut K))
      = CFSG.Open.pRank 3 ((⊤ : Subgroup (MulAut K)).map β) :=
        (pRank_map_eq_of_injective (by norm_num) β hinj ⊤).symm
    _ ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (K ⧸ Subgroup.center K))) :=
        CFSG.SectionRank.pRank_mono (by norm_num) le_top

theorem i112f_pRank_mulAut_alt {K : Type} [Group K] [Finite K] {n : ℕ} (hn : n = 6 ∨ n = 7)
    (hZ : Subgroup.center K = ⊥) (e : K ≃* alternatingGroup (Fin n)) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut K)) ≤ 2 := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  refine (CFSG.LocalAnalysis.RankFourTheoremC.pRank_mulAut_le_add_pRank_outer hp hZ).trans ?_
  have h1 : CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ 2 := by
    refine CFSG.AGLEmbedding.openPRank_top_le_of_not_dvd 2 fun hd => ?_
    have hcard : Nat.card K = 360 ∨ Nat.card K = 2520 := by
      rw [Nat.card_congr e.toEquiv]
      rcases hn with rfl | rfl
      · left
        rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
        decide
      · right
        rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
        decide
    rcases hcard with h | h <;> rw [h] at hd <;> omega
  have h2 : CFSG.Open.pRank 3
      (⊤ : Subgroup (CFSG.ComponentClassification.OuterAutomorphisms.Outer K)) ≤ 0 := by
    refine CFSG.AGLEmbedding.openPRank_top_le_of_not_dvd 0 fun hd => ?_
    have h4 := CFSG.AGLEmbedding.card_outer_alternatingGroup_dvd_four n (by omega)
    rw [← Nat.card_congr
      (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv] at h4
    have := hd.trans h4
    omega
  omega

theorem i112f_pRank_mulAut_hatAlt {K : Type} [Group K] [Finite K] {n : ℕ} (hn : n = 6 ∨ n = 7)
    (hc : commutator K = ⊤) (e : (K ⧸ Subgroup.center K) ≃* alternatingGroup (Fin n)) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut K)) ≤ 2 := by
  refine (i112f_pRank_mulAut_le_quot hc).trans (i112f_pRank_mulAut_alt hn ?_ e)
  refine i112f_center_eq_bot_of_mulEquiv e (alternatingGroup.center_eq_bot ?_)
  rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  omega

theorem i112f_pRank_mulAut_hatSix {K : Type} [Group K] [Finite K] (h : IsHatSix K) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut K)) ≤ 2 := by
  obtain ⟨hc, -, ⟨e⟩⟩ := h
  exact i112f_pRank_mulAut_hatAlt (Or.inl rfl) hc e

theorem i112f_pRank_mulAut_hatSeven {K : Type} [Group K] [Finite K] (h : IsHatSeven K) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut K)) ≤ 2 := by
  obtain ⟨hc, -, ⟨e⟩⟩ := h
  exact i112f_pRank_mulAut_hatAlt (Or.inr rfl) hc e

end Hat

end CFSG.HardMathSupport.Solomon.Coordinator
