module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Defs
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step15Points

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FieldFourCover LinearFlag
open scoped Pointwise

namespace Sec2

variable {G : Type} [Group G]

theorem inf_centerIn_ne_bot' [Finite G] {T Q : Subgroup G} (hT : IsPGroup 2 T) (hQT : Q ≤ T)
    (hTQ : T ≤ normalizer (Q : Set G)) (hQ : Q ≠ ⊥) : Q ⊓ centerIn T ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent T := hT.isNilpotent
  have hn : (Q.subgroupOf T).Normal := (normal_subgroupOf_iff_le_normalizer hQT).mpr hTQ
  have hne : Q.subgroupOf T ≠ ⊥ := by
    intro h
    apply hQ
    rw [eq_bot_iff]
    intro q hq
    have : (⟨q, hQT hq⟩ : T) ∈ Q.subgroupOf T := hq
    rw [h, mem_bot] at this
    exact congrArg Subtype.val this
  have h := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  intro hbot
  apply h
  rw [eq_bot_iff]
  rintro t ⟨htQ, htc⟩
  have hmem : (t : G) ∈ Q ⊓ centerIn T :=
    ⟨htQ, t.2, mem_centralizer_iff.mpr fun x hx => congrArg Subtype.val
      (mem_center_iff.mp htc ⟨x, hx⟩)⟩
  rw [hbot, mem_bot] at hmem
  exact Subtype.ext hmem

theorem mem_of_mem_sup_of_odd' {Q O : Subgroup G} (hQ : IsPGroup 2 Q) (hO : Odd (Nat.card O))
    (hOQ : O ≤ centralizer (Q : Set G)) {w : G} (hw : w ∈ Q ⊔ O) {k : ℕ} (hk : w ^ 2 ^ k = 1) :
    w ∈ Q := by
  have hON : O ≤ normalizer (Q : Set G) := hOQ.trans (centralizer_le_normalizer _)
  have hw' : w ∈ (Q : Set G) * (O : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left Q O hON]
    exact hw
  obtain ⟨q, hq, o, ho, rfl⟩ := hw'
  have hcomm : Commute q o := (mem_centralizer_iff.mp (hOQ ho) q hq)
  obtain ⟨m, hm⟩ := hQ ⟨q, hq⟩
  have hqm : q ^ 2 ^ m = 1 := by
    have := congrArg Subtype.val hm
    simpa using this
  have ho2 : o ^ 2 ^ (k + m) = 1 := by
    have h1 : (q * o) ^ 2 ^ (k + m) = 1 := by
      rw [pow_add, pow_mul, hk, one_pow]
    rw [hcomm.mul_pow, pow_add, mul_comm (2 ^ k) (2 ^ m), pow_mul, hqm, one_pow, one_mul] at h1
    rw [pow_add]
    calc o ^ (2 ^ k * 2 ^ m) = o ^ (2 ^ m * 2 ^ k) := by rw [mul_comm]
      _ = 1 := h1
  have hodd : Odd (orderOf o) := hO.of_dvd_nat (by
    have := Subgroup.orderOf_dvd_natCard O ho
    exact this)
  have hdvd : orderOf o ∣ 2 ^ (k + m) := orderOf_dvd_of_pow_eq_one ho2
  have h1 : orderOf o = 1 := by
    have hc : Nat.Coprime (orderOf o) (2 ^ (k + m)) :=
      Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd)
    exact Nat.Coprime.eq_one_of_dvd hc hdvd
  show q * o ∈ Q
  rw [orderOf_eq_one_iff.mp h1, mul_one]
  exact hq

theorem le_normalizer_of_card_sixteen [Finite G] {A H T : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple ↥A) (hL : TypeL34 (rankTwoQuot A))
    (hodd : Odd (Nat.card (center ↥A))) (hTsyl : IsSylowOf 2 T A) (hHT : H ≤ T)
    (hH : IsElemAbelian 2 H) (hH16 : Nat.card H = 16) : T ≤ normalizer (H : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c⟩ := nonempty_l34Cover_of_odd hq hL hodd
  have hO := oddCore_le_center hq.1 hq.2
  obtain ⟨T₀, hT₀⟩ := hTsyl
  have hTA : T ≤ A := hT₀ ▸ map_subtype_le _
  have hHA : H ≤ A := hHT.trans hTA
  obtain ⟨φ, -, hφk, hφT⟩ := c.exists_std hO T₀
  have hkerodd : Odd (Nat.card φ.ker) := by rw [hφk]; exact hodd
  have hkerZ : φ.ker ≤ center ↥A := hφk.le
  have hTsub : T.subgroupOf A = T₀ := by
    rw [← hT₀]
    exact comap_map_eq_self_of_injective A.subtype_injective _
  have hT₀2 : IsPGroup 2 (T₀ : Subgroup ↥A) := T₀.2
  have hH₀T : H.subgroupOf A ≤ T₀ := fun x hx => hTsub ▸ (hHT (mem_subgroupOf.mp hx))
  have hH₀ : IsPGroup 2 (H.subgroupOf A) := hT₀2.to_le hH₀T
  have hH₀2' : ∀ x ∈ (H.subgroupOf A).map φ, x ^ 2 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, show x ^ 2 = 1 from Subtype.ext (by simpa using hH.2 _ (mem_subgroupOf.mp hx)),
      map_one]
  have hH₀16 : Nat.card ((H.subgroupOf A).map φ) = 16 := by
    rw [card_map_of_isPGroup φ hkerodd hH₀, ← hH16]
    exact Nat.card_congr (subgroupOfEquivOfLe hHA).toEquiv
  have hH₀U : (H.subgroupOf A).map φ ≤ projUnip c.k := hφT ▸ map_mono hH₀T
  obtain ⟨i, hi⟩ : ∃ i : Fin 2, (H.subgroupOf A).map φ = projRad c.k i := by
    rcases eq_projRad_of_le_projUnip c.card_k hH₀U hH₀2' hH₀16 with h0 | h1
    · exact ⟨0, h0⟩
    · exact ⟨1, h1⟩
  intro t ht
  have htA := hTA ht
  have htT₀ : (⟨t, htA⟩ : ↥A) ∈ T₀ := by
    have h1 : (⟨t, htA⟩ : ↥A) ∈ T.subgroupOf A := ht
    rwa [hTsub] at h1
  have hφt : φ ⟨t, htA⟩ ∈ projUnip c.k := hφT ▸ mem_map_of_mem φ htT₀
  have hn := mem_normalizer_of_map φ hkerZ hkerodd hH₀
    (hi ▸ projUnip_le_normalizer_projRad i hφt)
  exact mem_normalizer_of_mem_normalizer_subgroupOf hHA hn

end Sec2

section Frame

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {g : G} {E F : Subgroup G}

theorem Frame.F_le_normalizer (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (hodd : Odd (Nat.card (center ↥A))) : F ≤ normalizer (E : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR := hF.sylowR
  have hRA : R ≤ centralizer (A : Set G) := hR.le
  obtain ⟨hRD, hDA, -⟩ := sylow_sup_structure hRA hR.isPGroup hF.sylow
  have hRA1 : R ⊓ A = ⊥ := inf_eq_bot_of_odd_center hRA hR.isPGroup hodd
  have hEA16 : Nat.card (E ⊓ A : Subgroup G) = 16 := by
    have := card_eq_card_inf_mul hRA hF.R_le_E hF.E_le hRA1
    rw [hF.cardE, hF.cardR] at this
    omega
  have hN := Sec2.le_normalizer_of_card_sixteen hF.base.hyp.standard.1 hL hodd hDA
    (inf_le_inf_right A le_sup_left) (AS76b.IsElemAbelian.mono hF.elemE inf_le_left) hEA16
  intro f hf
  obtain ⟨a, ha, r, hr, rfl⟩ := exists_eq_mul_of_le_sup hRA hF.R_le_F hF.F_le hf
  have haD : a ∈ (E ⊔ F) ⊓ A := ⟨mem_sup_right ha.1, ha.2⟩
  have haR : a ∈ normalizer (R : Set G) := Subgroup.centralizer_le_normalizer _
    (mem_centralizer_iff.mpr fun r' hr' => (mem_centralizer_iff.mp (hRA hr') a ha.2).symm)
  have haE : a ∈ normalizer (E : Set G) := by
    rw [eq_inf_sup_of_le_sup hRA hF.R_le_E hF.E_le]
    exact mem_normalizer_sup (hN haD) haR
  have hrE : r ∈ normalizer (E : Set G) := le_normalizer (hF.R_le_E hr)
  exact mul_mem haE hrE

theorem Frame.sec2Z_eq (hF : Frame G A A R g E F) : sec2Z A E F = E ⊓ F ⊓ A := by
  rw [sec2Z, ← hF.inf_eq_center, inf_comm]

theorem Frame.sup_sec2Z (hF : Frame G A A R g E F) : R ⊔ sec2Z A E F = E ⊓ F := by
  have hRA : R ≤ centralizer (A : Set G) := hF.sylowR.le
  have hREF : R ≤ E ⊓ F := hF.inf_eq ▸ le_sup_left
  rw [hF.sec2Z_eq, sup_comm]
  exact (eq_inf_sup_of_le_sup hRA hREF (inf_le_left.trans hF.E_le)).symm

theorem Frame.inf_rightConjugate (hF : Frame G A A R g E F) : R ⊓ rightConjugate R g = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstd := hF.base.hyp.standard
  have hKte := AS76b.tightlyEmbedded_centralizer hstd
  have hNK := AS76b.normalizer_centralizer_eq hstd
  have hR := hF.sylowR
  have hRA : R ≤ centralizer (A : Set G) := hR.le
  have hgK : g ∉ normalizer (centralizer (A : Set G) : Set G) := hNK ▸ hF.not_mem
  have h := two_subgroup_inf_conjugate_eq_bot _ (R ⊓ rightConjugate R g) hKte
    (hR.isPGroup.to_le inf_le_left) g hgK
    (inf_le_right.trans (AschbacherTheorem3.rightConjugate_le_rightConjugate hRA g))
  rwa [inf_eq_left.mpr (inf_le_left.trans hRA)] at h

theorem Frame.card_inf (hF : Frame G A A R g E F) : Nat.card (E ⊓ F : Subgroup G) = 16 := by
  have hRg : rightConjugate R g ≤ normalizer (R : Set G) :=
    hF.comm.trans (centralizer_le_normalizer _)
  have h := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer R
    (rightConjugate R g) hRg
    (disjoint_iff.mpr hF.inf_rightConjugate)
  have hRg4 : Nat.card (rightConjugate R g) = 4 := by
    rw [← hF.cardR]
    exact Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  rw [← hF.inf_eq] at h
  rw [h, hF.cardR, hRg4]

theorem Frame.card_sec2Z (hF : Frame G A A R g E F) (hodd : Odd (Nat.card (center ↥A))) :
    Nat.card (sec2Z A E F) = 4 := by
  have hR := hF.sylowR
  have hRA : R ≤ centralizer (A : Set G) := hR.le
  have hREF : R ≤ E ⊓ F := hF.inf_eq ▸ le_sup_left
  have hRA1 : R ⊓ A = ⊥ := inf_eq_bot_of_odd_center hRA hR.isPGroup hodd
  have h := card_eq_card_inf_mul hRA hREF (inf_le_left.trans hF.E_le) hRA1
  rw [hF.card_inf, hF.cardR] at h
  rw [hF.sec2Z_eq]
  omega

end Frame

namespace Sec2

variable {G : Type} [Group G]

section Core

theorem sec2P_le (E : Subgroup G) : sec2P E ≤ normalizer (E : Set G) :=
  ABGTheoremB.pCoreIn_le 2 _

theorem normalizer_le_normalizer_sec2P (E : Subgroup G) :
    normalizer (E : Set G) ≤ normalizer (sec2P E : Set G) := by
  have := CFSG.pCore_normal (p := 2) (G := ↥(normalizer (E : Set G)))
  exact ABGTheoremB.le_normalizer_map_subtype _ _

theorem isPGroup_sec2P (E : Subgroup G) : IsPGroup 2 (sec2P E) :=
  CFSG.pCore_isPGroup.map _

theorem le_sec2P {E X : Subgroup G} (hX2 : IsPGroup 2 X) (hXE : X ≤ normalizer (E : Set G))
    (hEX : normalizer (E : Set G) ≤ normalizer (X : Set G)) : X ≤ sec2P E := by
  have hnormal : (X.subgroupOf (normalizer (E : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXE).mpr hEX
  have hp : IsPGroup 2 (X.subgroupOf (normalizer (E : Set G))) := hX2.comap_subtype
  have hle : X.subgroupOf (normalizer (E : Set G)) ≤ CFSG.pCore 2 (normalizer (E : Set G)) :=
    le_sSup ⟨hnormal, hp⟩
  intro k hk
  exact ⟨⟨k, hXE hk⟩, hle hk, rfl⟩

end Core

end Sec2

end CFSG.ComponentClassification.AS81
