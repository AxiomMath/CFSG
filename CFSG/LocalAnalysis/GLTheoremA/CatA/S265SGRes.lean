module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGPin
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGSplit
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGClsLift
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGExcLift
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGTor
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLParity

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10

@[expose] def QSF3ResF4 : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x : Ω) (D K : Subgroup Ω)
    (lab : GLALabel), QSNL 3 S B T x D K → catalogIs (PSimple 3 K) (tyF 3) → Nat.card B = 3 ^ 4 →
    InnLabelOf B S lab → GLAInLambda2 lab → 3 ≤ rk2Mult lab (rk2Ord 3 lab.n) →
    (lab.tag = .F4 ∧ 3 ∣ 2 ^ lab.n + 1) → False

@[expose] def QSF3ResU6 : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x : Ω) (D K : Subgroup Ω)
    (lab : GLALabel), QSNL 3 S B T x D K → catalogIs (PSimple 3 K) (tyF 3) → Nat.card B = 3 ^ 4 →
    InnLabelOf B S lab → GLAInLambda2 lab → 3 ≤ rk2Mult lab (rk2Ord 3 lab.n) →
    (lab.tag = .twA ∧ lab.rank = 5 ∧ 3 ∣ 2 ^ lab.n + 1) → False

@[expose] def QSF3ResCls : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x : Ω) (D K : Subgroup Ω)
    (lab : GLALabel), QSNL 3 S B T x D K → catalogIs (PSimple 3 K) (tyF 3) → Nat.card B = 3 ^ 4 →
    InnLabelOf B S lab → GLAInLambda2 lab → 3 ≤ rk2Mult lab (rk2Ord 3 lab.n) →
    ((lab.tag = .A ∧ 3 ∣ 2 ^ lab.n - 1 ∧ lab.rank ≤ 4) ∨
      (lab.tag = .A ∧ 3 ∣ 2 ^ lab.n + 1 ∧ lab.rank ≤ 8) ∨
      (lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n + 1 ∧ lab.rank ≤ 4) ∨
      (lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n - 1) ∨
      ((lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank ≤ 4) ∨
      (lab.tag = .D ∧ 3 ∣ 2 ^ lab.n - 1 ∧ lab.rank ≤ 3) ∨
      (lab.tag = .D ∧ 3 ∣ 2 ^ lab.n + 1 ∧ lab.rank ≤ 5) ∨
      (lab.tag = .twD ∧ 3 ∣ 2 ^ lab.n - 1 ∧ lab.rank ≤ 4) ∨
      (lab.tag = .twD ∧ 3 ∣ 2 ^ lab.n + 1 ∧ lab.rank ≤ 4)) → False

section


theorem SG.false_of_classLabel {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x : Ω}
    {D K : Subgroup Ω} (h : QSNL 3 S B T x D K) (hB : Nat.card B = 3 ^ 4) {lab : GLALabel}
    (hlab : LabelOf S lab) (hlab2 : GLAInLambda2 lab)
    (ht : (lab.tag = .A ∧ 3 ∣ 2 ^ lab.n - 1 ∧ 5 ≤ lab.rank) ∨
      (lab.tag = .A ∧ 3 ∣ 2 ^ lab.n + 1 ∧ 9 ≤ lab.rank) ∨
      (lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n + 1 ∧ 6 ≤ lab.rank) ∨
      ((lab.tag = .B ∨ lab.tag = .C) ∧ 5 ≤ lab.rank) ∨
      (lab.tag = .D ∧ 3 ∣ 2 ^ lab.n - 1 ∧ 4 ≤ lab.rank) ∨
      (lab.tag = .D ∧ 3 ∣ 2 ^ lab.n + 1 ∧ 6 ≤ lab.rank) ∨
      (lab.tag = .twD ∧ 3 ∣ 2 ^ lab.n - 1 ∧ 5 ≤ lab.rank) ∨
      (lab.tag = .twD ∧ 3 ∣ 2 ^ lab.n + 1 ∧ 5 ≤ lab.rank)) : False :=
  false_of_torusLift h hB hlab le_rfl (labelAll_torusLift_cls hlab2 ht)


theorem SG.false_of_excLabel {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x : Ω}
    {D K : Subgroup Ω} (h : QSNL 3 S B T x D K) (hB : Nat.card B = 3 ^ 4) {lab : GLALabel}
    (hlab : LabelOf S lab) (hlab2 : GLAInLambda2 lab)
    (ht : lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7 ∨ lab.tag = .E8 ∨
      (lab.tag = .F4 ∧ 3 ∣ 2 ^ lab.n - 1)) : False :=
  false_of_torusLift h hB hlab le_rfl (labelAll_torusLift_exc hlab2 ht)


theorem qsF3Gen_of_res (hF4 : QSF3ResF4) (hU6 : QSF3ResU6) (hCls : QSF3ResCls) : QSF3Gen := by
  intro Ω _ _ S B T x D K hN hcat hB
  obtain ⟨lab, hlab, hlab2, h3, hsmall⟩ := SG.exists_innLabel_of_qsnl_big hN
  have hf := hF4 Ω S B T x D K lab hN hcat hB hlab hlab2 h3
  have hu := hU6 Ω S B T x D K lab hN hcat hB hlab hlab2 h3
  have hc := hCls Ω S B T x D K lab hN hcat hB hlab hlab2 h3
  have he := SG.false_of_excLabel hN hB hlab.labelOf hlab2
  have hk := SG.false_of_classLabel hN hB hlab.labelOf hlab2
  simp only [or_imp] at hc he hk
  simp only [not_or] at hsmall
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := hc
  obtain ⟨e1, e2, e3, e4, e5⟩ := he
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8⟩ := hk
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := hsmall
  have hn := CFSG.StandardType.SCFourCover.three_dvd_two_pow_add_one_or_sub_one lab.n
  cases ht : lab.tag
  · rcases hn with hp | hm
    · exact (Nat.lt_or_ge lab.rank 9).elim (fun hr => c2 ⟨ht, hp, by omega⟩) (k2 ⟨ht, hp, ·⟩)
    · exact (Nat.lt_or_ge lab.rank 5).elim (fun hr => c1 ⟨ht, hm, by omega⟩) (k1 ⟨ht, hm, ·⟩)
  · rcases hn with hp | hm
    · rcases Nat.lt_or_ge lab.rank 6 with hr | hr
      · exact (Nat.lt_or_ge lab.rank 5).elim (fun h5 => c3 ⟨ht, hp, by omega⟩)
          (fun h5 => hu ⟨ht, by omega, hp⟩)
      · exact k3 ⟨ht, hp, hr⟩
    · exact c4 ⟨ht, hm⟩
  · exact (Nat.lt_or_ge lab.rank 5).elim (fun hr => c5 ⟨.inl ht, by omega⟩) (k4 ⟨.inl ht, ·⟩)
  · exact (Nat.lt_or_ge lab.rank 5).elim (fun hr => c5 ⟨.inr ht, by omega⟩) (k4 ⟨.inr ht, ·⟩)
  · rcases hn with hp | hm
    · exact (Nat.lt_or_ge lab.rank 6).elim (fun hr => c7 ⟨ht, hp, by omega⟩) (k6 ⟨ht, hp, ·⟩)
    · exact (Nat.lt_or_ge lab.rank 4).elim (fun hr => c6 ⟨ht, hm, by omega⟩) (k5 ⟨ht, hm, ·⟩)
  · rcases hn with hp | hm
    · exact (Nat.lt_or_ge lab.rank 5).elim (fun hr => c9 ⟨ht, hp, by omega⟩) (k8 ⟨ht, hp, ·⟩)
    · exact (Nat.lt_or_ge lab.rank 5).elim (fun hr => c8 ⟨ht, hm, by omega⟩) (k7 ⟨ht, hm, ·⟩)
  · exact e1 ht
  · exact e3 ht
  · exact e4 ht
  · rcases hn with hp | hm
    · exact hf ⟨ht, hp⟩
    · exact e5 ⟨ht, hm⟩
  · exact e2 ht
  all_goals contradiction

end

end CFSG.LocalAnalysis.GLTheoremA.S265

end
