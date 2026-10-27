module

public import CFSG.CGT.PushingUpLit.CGT6.SixSixteen
public import CFSG.CGT.PushingUpLit.CGT6.SixTwoBasic
public import CFSG.CGT.PushingUpLit.EightOneRel
public import CFSG.CGT.PushingUpLit.Glue.RadicalSylow

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.SixThree CFSG.CGT.PushingUpLit.EightOneRel
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

theorem inf_normalizer_le_of_isSylowOf_centralizerModCore [Finite G] {Y R P : Subgroup G}
    (hR : IsSylowOf 2 R (centralizerModCore Y)) (hP : IsPGroup 2 P)
    (hYP : Y ≤ Subgroup.normalizer (P : Set G)) (hRP : R ≤ P) :
    P ⊓ Subgroup.normalizer (Y : Set G) ≤ R := by
  set Q : Subgroup G := P ⊓ Subgroup.normalizer (Y : Set G) with hQ
  have hQ2 : IsPGroup 2 Q := hP.to_le inf_le_left
  have hQY : Q ≤ Subgroup.normalizer (Y : Set G) := inf_le_right
  have hYQ : Y ≤ Subgroup.normalizer (Q : Set G) :=
    le_trans (le_inf hYP (Subgroup.le_normalizer.trans Subgroup.le_normalizer))
      Subgroup.inf_normalizer_le_normalizer_inf
  have hM : ⁅Q, Y⁆ ≤ oTwoIn Y := commutator_le_oTwoIn_of_normalizes hQ2 hQY hYQ
  have hQC : Q ≤ centralizerModCore Y := fun g hg =>
    ⟨hQY hg, fun x hx => hM (Subgroup.commutator_mem_commutator hg hx)⟩
  have hRQ : R ≤ Q := le_inf hRP fun r hr => (hR.1 hr).1
  exact Nine.le_of_isSylowOf_of_le hR hQ2 hRQ hQC

@[expose] def actsTrivially (N P R : Subgroup G) (hNR : N ≤ Subgroup.normalizer (R : Set G)) :
    Subgroup G where
  carrier := {h | h ∈ N ∧ ∀ p ∈ P, ⁅h, p⁆ ∈ R}
  one_mem' := ⟨N.one_mem, fun p _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨haN, ha⟩ ⟨hbN, hb⟩
    refine ⟨N.mul_mem haN hbN, fun p hp => ?_⟩
    have e : ⁅a * b, p⁆ = (a * ⁅b, p⁆ * a⁻¹) * ⁅a, p⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact R.mul_mem ((Subgroup.mem_normalizer_iff.mp (hNR haN) _).mp (hb p hp)) (ha p hp)
  inv_mem' := by
    rintro a ⟨haN, ha⟩
    refine ⟨N.inv_mem haN, fun p hp => ?_⟩
    have e : ⁅a⁻¹, p⁆ = a⁻¹ * (⁅a, p⁆)⁻¹ * a := by
      simp only [commutatorElement_def]
      group
    rw [e]
    have h1 := (Subgroup.mem_normalizer_iff.mp (hNR (N.inv_mem haN)) _).mp (R.inv_mem (ha p hp))
    simpa using h1

theorem conj_mem_actsTrivially {N P R : Subgroup G} (hNP : N ≤ Subgroup.normalizer (P : Set G))
    (hNR : N ≤ Subgroup.normalizer (R : Set G)) {g h : G} (hg : g ∈ N)
    (hh : h ∈ actsTrivially N P R hNR) : g * h * g⁻¹ ∈ actsTrivially N P R hNR := by
  obtain ⟨hhN, hh⟩ := hh
  refine ⟨N.mul_mem (N.mul_mem hg hhN) (N.inv_mem hg), fun p hp => ?_⟩
  have hp' : g⁻¹ * p * g ∈ P := by
    have := (Subgroup.mem_normalizer_iff.mp (hNP (N.inv_mem hg)) p).mp hp
    simpa using this
  have h1 := hh _ hp'
  have e : ⁅g * h * g⁻¹, p⁆ = g * ⁅h, g⁻¹ * p * g⁆ * g⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (hNR hg) _).mp h1

theorem oTwoIn_normalizer_eq_of_normalized_j [Finite G] {Y R S J : Subgroup G}
    (hNo : SubTwo.NoTwoQuotient Y) (hR : IsSylowOf 2 R (centralizerModCore Y))
    (hS : IsSylowOf 2 S (Subgroup.normalizer (R : Set G))) (hJS : J ≤ S)
    (hJY : J ≤ Subgroup.normalizer (Y : Set G)) (hJc : Y ≤ ⁅J, Y⁆)
    (hSJ : S ≤ Subgroup.normalizer (J : Set G)) :
    oTwoIn (Subgroup.normalizer (R : Set G)) = R := by
  set N : Subgroup G := Subgroup.normalizer (R : Set G) with hN
  set P : Subgroup G := oTwoIn N with hP
  have hYN : Y ≤ N := Glue.le_normalizer_of_isSylowOf_centralizerModCore hR
  have hRP : R ≤ P := le_oTwoIn_of_isPGroup Subgroup.le_normalizer hR.2.1 le_rfl
  have hP2 : IsPGroup 2 P := ThreeFromEight.isPGroup_oTwoIn _
  have hPN : P ≤ N := SixThree.oTwoIn_le N
  have hNP : N ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.le_normalizer.trans (SixThree.normalizer_le_normalizer_oTwoIn N)
  have hPS : P ≤ S := Nine.le_of_isSylowOf_of_normal hS hP2 hPN hNP
  have hYP : Y ≤ Subgroup.normalizer (P : Set G) := hYN.trans hNP
  have hRY : R ≤ Subgroup.normalizer (Y : Set G) := fun r hr => (hR.1 hr).1
  have hPY : P ⊓ Subgroup.normalizer (Y : Set G) ≤ R :=
    inf_normalizer_le_of_isSylowOf_centralizerModCore hR hP2 hYP hRP
  let Cn : Subgroup G := actsTrivially N P R le_rfl
  have hJC : J ≤ Cn := by
    intro a ha
    have haN : a ∈ N := hS.1 (hJS ha)
    refine ⟨haN, fun p hp => ?_⟩
    have h1 : ⁅a, p⁆ ∈ J := by
      have h2 : p * a⁻¹ * p⁻¹ ∈ J :=
        (Subgroup.mem_normalizer_iff.mp (hSJ (hPS hp)) _).mp (J.inv_mem ha)
      have e : ⁅a, p⁆ = a * (p * a⁻¹ * p⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact J.mul_mem ha h2
    have h2 : ⁅a, p⁆ ∈ P := by
      have h3 : a * p * a⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hNP haN) p).mp hp
      have e : ⁅a, p⁆ = (a * p * a⁻¹) * p⁻¹ := by
        simp only [commutatorElement_def]
      rw [e]
      exact P.mul_mem h3 (P.inv_mem hp)
    exact hPY ⟨h2, hJY h1⟩
  have hYC : Y ≤ Cn := by
    have hcomm : ⁅J, Y⁆ ≤ Cn := by
      rw [Subgroup.commutator_le]
      intro j hj y hy
      have h1 : y * j * y⁻¹ ∈ Cn := conj_mem_actsTrivially hNP le_rfl (hYN hy) (hJC hj)
      have e : ⁅j, y⁆ = j * (y * j * y⁻¹)⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact Cn.mul_mem (hJC hj) (Cn.inv_mem h1)
    exact hJc.trans hcomm
  have hYPR : ∀ y ∈ Y, ∀ p ∈ P, ⁅y, p⁆ ∈ R := fun y hy p hp => (hYC hy).2 p hp
  have hB : ((Y ⊔ R : Subgroup G) : Set G) = (Y : Set G) * R :=
    Subgroup.coe_mul_of_right_le_normalizer_left Y R hRY
  have hconj : ∀ p ∈ P, ∀ b ∈ Y ⊔ R, p * b * p⁻¹ ∈ Y ⊔ R := by
    intro p hp b hb
    rw [← SetLike.mem_coe, hB] at hb
    obtain ⟨y, hy, r, hr, rfl⟩ := hb
    have e : p * (y * r) * p⁻¹ = (⁅p, y⁆ * y) * (p * r * p⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    refine (Y ⊔ R).mul_mem ?_ ?_
    · have h1 : ⁅p, y⁆ ∈ R := by
        have := R.inv_mem (hYPR y hy p hp)
        rwa [commutatorElement_inv] at this
      exact (Y ⊔ R).mul_mem (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left hy)
    · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hPN hp) r).mp hr)
  have hpB : ∀ p ∈ P, p ∈ Subgroup.normalizer ((Y ⊔ R : Subgroup G) : Set G) := by
    intro p hp
    have hmap : (Y ⊔ R).map (MulAut.conj p).toMonoidHom = Y ⊔ R := by
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · rintro _ ⟨b, hb, rfl⟩
        simpa [MulAut.conj_apply] using hconj p hp b hb
      · rw [Subgroup.card_map_of_injective (MulAut.conj p).injective]
    refine Subgroup.mem_normalizer_iff.mpr fun b => ⟨fun hb => hconj p hp b hb, fun hb => ?_⟩
    have hb' : p * b * p⁻¹ ∈ (Y ⊔ R).map (MulAut.conj p).toMonoidHom := by
      rw [hmap]
      exact hb
    obtain ⟨z, hz, hzb⟩ := hb'
    have h2 : p * z * p⁻¹ = p * b * p⁻¹ := by simpa [MulAut.conj_apply] using hzb
    have hzb' : z = b := mul_left_cancel (mul_right_cancel h2)
    rw [← hzb']
    exact hz
  have hNormY : ∀ p ∈ P, p ∈ Subgroup.normalizer (Y : Set G) := by
    intro p hp
    refine SubTwo.mem_normalizer_of_normal_chain (B := Y ⊔ R)
      (B' := Subgroup.normalizer ((Y ⊔ R : Subgroup G) : Set G)) hNo le_sup_left
      (sup_le Subgroup.le_normalizer hRY) le_rfl hR.2.1 ?_ (hpB p hp)
    intro b hb
    rw [← SetLike.mem_coe, hB] at hb
    obtain ⟨y, hy, r, hr, rfl⟩ := hb
    exact ⟨y, hy, r, hr, Subgroup.mem_sup_right hr, rfl⟩
  have hPR : P ≤ R := fun p hp => hPY ⟨hp, hNormY p hp⟩
  exact le_antisymm hPR hRP

theorem aschbacherSixSixteenPR_holds : AschbacherSixSixteenPR := by
  intro G _ _ _ _ Y T hY hYT R hR U₀ _ _ _ _ S hS hSY _
  have hNo : SubTwo.NoTwoQuotient Y := SubTwo.noTwoQuotient_of_oResidualTwo hY.1.residual_eq
  set NY : Subgroup G := Subgroup.normalizer (Y : Set G) with hNY
  have hT2 : IsPGroup 2 (T : Subgroup G) := T.isPGroup'
  have hTtop : IsSylowOf 2 (T : Subgroup G) ⊤ :=
    ⟨le_top, hT2, by simpa [Subgroup.relIndex_top_right] using T.not_dvd_index⟩
  have hJTY : jIn (T : Subgroup G) ≤ NY :=
    Subgroup.le_normalizer_iff_commutator_le_right.mpr hYT.symm.le
  obtain ⟨Q, hQ, hTQ⟩ := Nine.exists_isSylowOf_ge (K := NY)
    (hT2.to_le (inf_le_left : (T : Subgroup G) ⊓ NY ≤ T)) inf_le_right
  obtain ⟨a, haNY, hQa⟩ := exists_conjugate_eq_of_isSylowOf hQ hSY
  let J : Subgroup G := (jIn (T : Subgroup G)).map (MulAut.conj a).toMonoidHom
  have hJmem : ∀ x ∈ J, ∃ j ∈ jIn (T : Subgroup G), a * j * a⁻¹ = x := by
    rintro x ⟨j, hj, rfl⟩
    exact ⟨j, hj, by simp [MulAut.conj_apply]⟩
  have hJS : J ≤ S := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := hJmem x hx
    have hjQ : j ∈ Q := hTQ ⟨jIn_le _ hj, hJTY hj⟩
    rw [hQa] at hjQ
    obtain ⟨d, hd, hdj⟩ := hjQ
    have hdj' : a⁻¹ * d * a = j := by simpa [MulAut.conj_apply] using hdj
    have : a * j * a⁻¹ = d := by rw [← hdj']; group
    rw [this]
    exact hd.1
  have hJY : J ≤ NY := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := hJmem x hx
    exact NY.mul_mem (NY.mul_mem haNY (hJTY hj)) (NY.inv_mem haNY)
  have hYmap : Y.map (MulAut.conj a).toMonoidHom = Y := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp haNY y).mp hy
    · intro hx
      refine ⟨a⁻¹ * x * a, ?_, ?_⟩
      · have e : a * (a⁻¹ * x * a) * a⁻¹ = x := by group
        have := (Subgroup.mem_normalizer_iff.mp haNY (a⁻¹ * x * a)).mpr (by rw [e]; exact hx)
        exact this
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
  have hJc : Y ≤ ⁅J, Y⁆ := by
    have h1 : ⁅J, Y⁆ = (⁅jIn (T : Subgroup G), Y⁆).map (MulAut.conj a).toMonoidHom := by
      rw [Subgroup.map_commutator, hYmap]
    rw [h1, ← hYT, hYmap]
  obtain ⟨T₁, hT₁, hST₁⟩ := Nine.exists_isSylowOf_ge (K := ⊤) hS.2.1 le_top
  obtain ⟨h, -, hTh⟩ := exists_conjugate_eq_of_isSylowOf hT₁ hTtop
  have hJT : J = jIn ((T : Subgroup G).map (MulAut.conj a).toMonoidHom) :=
    (jIn_map_equiv (MulAut.conj a) (T : Subgroup G)).symm
  have hJJ : jIn J = J := by
    rw [hJT, jIn_jIn]
  have hrank : pRank 2 ↥J = pRank 2 ↥T₁ := by
    rw [hJT, pRank_jIn, hTh]
    exact (Nine.pRank_map_injective (MulAut.conj a).toMonoidHom (MulAut.conj a).injective
      (T : Subgroup G) 2).trans
      (Nine.pRank_map_injective (MulAut.conj h⁻¹).toMonoidHom (MulAut.conj h⁻¹).injective
        (T : Subgroup G) 2).symm
  have hJT₁ : J ≤ T₁ := hJS.trans hST₁
  have hle : J ≤ jIn T₁ := by
    have h1 := jIn_mono_of_pRank_eq hJT₁ hrank
    rwa [hJJ] at h1
  have hcardJ : Nat.card ↥J = Nat.card ↥(jIn (T : Subgroup G)) :=
    Subgroup.card_map_of_injective (MulAut.conj a).injective
  have hcard : Nat.card ↥(jIn T₁) ≤ Nat.card ↥J := by
    rw [hTh, ← conjugate_jIn, hcardJ]
    exact (Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective).le
  have hJeq : J = jIn T₁ := Subgroup.eq_of_le_of_card_ge hle hcard
  have hSJ : S ≤ Subgroup.normalizer (J : Set G) := by
    rw [hJeq]
    exact hST₁.trans (Subgroup.le_normalizer.trans (normalizer_le_normalizer_jIn T₁))
  exact oTwoIn_normalizer_eq_of_normalized_j hNo hR hS hJS hJY hJc hSJ

end CFSG.CGT.PushingUpLit.CGT6
