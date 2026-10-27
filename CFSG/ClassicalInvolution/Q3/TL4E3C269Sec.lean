module

public import CFSG.ClassicalInvolution.Q3.TL4E3C269Defs
public import CFSG.ClassicalInvolution.Q3.TL4MF163L2
public import CFSG.ClassicalInvolution.Q3.TL4SecIdRed
public import CFSG.ClassicalInvolution.Q3.TL4E3Fin
public import CFSG.ClassicalInvolution.Q3.TL4MF163L33
public import CFSG.ClassicalInvolution.Q3.TL4MF163L3Z
public import CFSG.ClassicalInvolution.Q3.TL4MF163U3Q5
public import CFSG.ClassicalInvolution.Q3.TL4MFMuZ2Cl

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Blueprint
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace E3C269

variable {X : Type} [Group X] [Finite X] {R : Subgroup X} {S : Sylow 2 R} {z : X}

omit [Finite X] in
theorem exists_psl3_equiv [IsSimpleGroup ↥(genFittingFStar X)] {p f : ℕ}
    (hl : LieModel (FStarQuot X) .PSL 3 p f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ f ∧
      Nonempty (↥(genFittingFStar X) ≃* projectiveSL 3 K) ∧
        ∃ a b : ↥(genFittingFStar X), a * b ≠ b * a := by
  rcases hl with ⟨-, -, K, _, _, hK, ⟨e₀⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  rotate_left
  · exact absurd h0 (by norm_num)
  · exact absurd h0 (by norm_num)
  · exact absurd h0 (by norm_num)
  set N := genFittingFStar X with hNdef
  let e₁ : FStarQuot X ≃* projectiveSL 3 K :=
    (e₀.trans (Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K)
  obtain ⟨a, b, hab⟩ := MF163.L3.exists_noncomm (K := K)
  have hZ : Subgroup.center N = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center N) with h | h
    · exact h
    · exfalso
      have h1 : ∀ q : FStarQuot X, q = 1 := fun q => by
        obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
        exact (QuotientGroup.eq_one_iff n).2 (h ▸ Subgroup.mem_top n)
      apply hab
      rw [← e₁.apply_symm_apply a, ← e₁.apply_symm_apply b, h1 (e₁.symm a), h1 (e₁.symm b)]
  let ψ : ↥N ≃* FStarQuot X :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  let e : ↥N ≃* projectiveSL 3 K := ψ.trans e₁
  exact ⟨K, inferInstance, inferInstance, hK, ⟨e⟩, e.symm a, e.symm b,
    fun h => hab (by simpa using congrArg e h)⟩

theorem concl163_psl3_of_ne_three (hm : EdgelessMember3 R S z)
    [IsSimpleGroup ↥(genFittingFStar X)] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hl : LieModel (FStarQuot X) .PSL 3 p f) (hq3 : p ^ f ≠ 3) : Concl163 R z := by
  obtain ⟨K, _, _, hK, ⟨e⟩, -⟩ := exists_psl3_equiv hl
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · rw [pow_zero] at hK
      exact absurd hK (Finite.one_lt_card (α := K)).ne'
    · exact h
  have h5 : 5 ≤ p ^ f := by
    have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have hle : p ≤ p ^ f := Nat.le_self_pow (by omega) p
    obtain ⟨k, hk⟩ := hodd
    omega
  exact MF163.L3.concl163_of_psl3 hm hp hp2 hf hK h5 e

theorem tightActs3_of_psl3_three
    (hm : EdgelessMember3 R S z)
    [IsSimpleGroup ↥(genFittingFStar X)] {p f : ℕ} (hl : LieModel (FStarQuot X) .PSL 3 p f)
    (hq3 : p ^ f = 3) : TightActs3 R z := by
  obtain ⟨K, _, _, -, -, hnab⟩ := exists_psl3_equiv hl
  obtain ⟨rfl, rfl⟩ := TA3.eq_three_of_pow_eq_three hq3
  have : (genFittingFStar X).Normal := genFittingFStar_normal X
  have hZ : Subgroup.center ↥(genFittingFStar X) = ⊥ := center_eq_bot_of_isSimpleGroup hnab
  let ψ : ↥(genFittingFStar X) ≃* FStarQuot X :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  obtain ⟨eQ⟩ := GH74.KGroups.L33.equiv_of_lieModel hl
  exact MF163.tightActs3_of_l33 (centralizer_genFittingFStar_eq_bot hnab) (ψ.trans eQ) hm.datum
    hm.cls

theorem concl163_psu3_of_ne_three (hm : EdgelessMember3 R S z)
    [IsSimpleGroup ↥(genFittingFStar X)] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hL : LieModel (FStarQuot X) .PSU 3 p f) (hq3' : p ^ f ≠ 3) :
    Concl163 R z := by
  obtain ⟨-, hf, K, _, _, hK, ⟨e₀⟩⟩ := CFSG.GH74.Generic.lieModel_psu_data hL
  have hq3 : 3 ≤ p ^ f := by
    have h2 := hp.two_le
    have : p ≤ p ^ f := Nat.le_self_pow (by omega) p
    omega
  have hnab : ∃ a b : genFittingFStar X, a * b ≠ b * a := by
    by_contra hcomm
    simp only [not_exists, ne_eq, not_not] at hcomm
    have hZ : Subgroup.center (genFittingFStar X) = ⊤ :=
      eq_top_iff.mpr fun x _ => Subgroup.mem_center_iff.mpr fun y => hcomm y x
    have h1 : Nat.card (FStarQuot X) = 1 := by
      rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hZ).toEquiv]
      exact Subgroup.index_top
    have h2 := MFMuZ2.card_psu3_mul hp hf hK
    rw [← Nat.card_congr e₀.toEquiv, h1, one_mul] at h2
    have h4 : 4 ≤ (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)) := by
      have h5 : 27 ≤ (p ^ f) ^ 3 := by
        calc 27 = 3 ^ 3 := by norm_num
          _ ≤ (p ^ f) ^ 3 := Nat.pow_le_pow_left hq3 3
      have h6 : 1 ≤ ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) := by
        have : 9 ≤ (p ^ f) ^ 2 := by
          calc 9 = 3 ^ 2 := by norm_num
            _ ≤ (p ^ f) ^ 2 := Nat.pow_le_pow_left hq3 2
        exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
      calc 4 ≤ (p ^ f) ^ 3 := by omega
        _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega)
    have h7 : Nat.gcd 3 (p ^ f + 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
    omega
  have hC := centralizer_genFittingFStar_eq_bot hnab
  have : (genFittingFStar X).Normal := genFittingFStar_normal X
  obtain ⟨eF⟩ := MFMuZ2.nonempty_fstar_equiv (MFMuZ2.center_fstar_eq_bot hnab)
  have h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hodd : p ^ f % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2).pow
  have h5 : 5 ≤ p ^ f := by omega
  exact MF163.U3.concl163_ge_five hm.datum hm.cls.1 hC h hp2 h5 (eF.trans e₀)

theorem concl163_of_e3Z2 (hT : MuZ2Table) (hE3 : SecIdE3MuZ2) (hm : EdgelessMember3 R S z)
    (hmu : MuZ2Member R) (hO2 : ¬ TightInO2 z)
    (hx : (¬ TightActs3 R z ∧ (Thm6Exit X ∨ TightTwisted X z)) ∨
      Nonempty (X ⧸ Subgroup.center X ≃* NativeSporadic.Carrier .M12)) : Concl163 R z := by
  obtain ⟨hFs, hi, hX⟩ := hE3 X R S z hm hmu hO2 hx
  have := hFs
  obtain ⟨hTL3, hTU3, -, -, hTM12⟩ := hT X R S z hm hmu hFs (index_dvd_six_of_le_two hi)
  rcases hX with ⟨p, f, hp, hp2, ⟨hf, hl⟩ | hl | hl⟩ | hm12
  · exact model163L2_proved X R S z hm hFs hi p f hp hp2 hf hl
  · by_cases hq3 : p ^ f = 3
    · exfalso
      rcases hx with ⟨h3, -⟩ | he
      · exact h3 (tightActs3_of_psl3_three hm hl hq3)
      · obtain ⟨e⟩ := he
        obtain ⟨hs, hl'⟩ := hTL3 p f hl
        have := hs
        obtain ⟨rfl, rfl⟩ := TA3.eq_three_of_pow_eq_three hq3
        have hcard := card_of_lieModel_psl_three_three_one hl'
        have hZ : Subgroup.center X = ⊥ :=
          center_eq_bot_of_isSimpleGroup (exists_ne_comm_of_not_prime (by rw [hcard]; norm_num))
        have h1 : Nat.card X = Nat.card (NativeSporadic.Carrier .M12) := by
          rw [← Nat.card_congr
            ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).toEquiv]
          exact Nat.card_congr e.toEquiv
        have hM : Nat.card (NativeSporadic.Carrier .M12) = 95040 :=
          CFSG.Sporadic.Mathieu.card_M12
        rw [hcard, hM] at h1
        norm_num at h1
    · exact concl163_psl3_of_ne_three hm hp hp2 hl hq3
  · obtain ⟨-, -, h4⟩ := hTU3 p f hl
    refine concl163_psu3_of_ne_three hm hp hp2 hl fun h => ?_
    rw [h] at h4
    norm_num at h4
  · exact absurd hm12 hTM12

end E3C269

theorem tightE3Z2Sec163_of {n : ℕ} (hT : MuZ2Table) (hE3 : SecIdE3MuZ2) (hE4 : SecIdE4Edge) :
    TightE3Z2Sec163 n := by
  intro Y _ _ R S t J u hF htu ht Sb hex hedge hμ hnE2
  obtain ⟨Sq, hd, hc⟩ := hF.exists_secCls htu ht
  have hcR : TightClsR 3 (SecQ R u) (secR R u) Sq (E3.secT htu ht) := tightClsR_three_iff.mpr hc
  have hm : EdgelessMember3 (secR R u) Sq (E3.secT htu ht) := ⟨hd, hcR, hedge⟩
  have hmu : MuZ2Member (secR R u) := hμ
  rcases TightEx.reduce hd hc hex hnE2 with ⟨-, h3⟩ | ⟨-, hM⟩ | ⟨hZ, h4⟩
  · rcases (tightDichotomy_of hd hc).resolve_left hnE2 with hq | htw
    · rcases hF.plus.thm6 (SecQ R u) hF.card_secQ_lt (secR R u) Sq (E3.secT htu ht) hd hcR hnE2
          hq hedge with hg | hx
      · exact absurd (acts3_of_good hg) h3
      · exact E3C269.concl163_of_e3Z2 hT hE3 hm hmu hnE2 (Or.inl ⟨h3, Or.inl hx⟩)
    · exact E3C269.concl163_of_e3Z2 hT hE3 hm hmu hnE2 (Or.inl ⟨h3, Or.inr htw⟩)
  · exact E3C269.concl163_of_e3Z2 hT hE3 hm hmu hnE2 (Or.inr hM)
  · exact absurd hedge (hE4 _ _ _ _ hd hc hnE2 hZ h4)

end CFSG.ClassicalInvolution.Q3.TL4
