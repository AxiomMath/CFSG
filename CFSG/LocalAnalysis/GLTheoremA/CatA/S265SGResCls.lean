module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGRes

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10

@[expose] def QSF3ResLin : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x : Ω) (D K : Subgroup Ω)
    (lab : GLALabel), QSNL 3 S B T x D K → catalogIs (PSimple 3 K) (tyF 3) → Nat.card B = 3 ^ 4 →
    InnLabelOf B S lab → GLAInLambda2 lab → 3 ≤ rk2Mult lab (rk2Ord 3 lab.n) →
    ((lab.tag = .A ∧ 3 ∣ 2 ^ lab.n - 1 ∧ lab.rank ≤ 4) ∨
      (lab.tag = .A ∧ 3 ∣ 2 ^ lab.n + 1 ∧ lab.rank ≤ 8) ∨
      (lab.tag = .D ∧ 3 ∣ 2 ^ lab.n - 1 ∧ lab.rank ≤ 3)) → False

@[expose] def QSF3ResUni : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x : Ω) (D K : Subgroup Ω)
    (lab : GLALabel), QSNL 3 S B T x D K → catalogIs (PSimple 3 K) (tyF 3) → Nat.card B = 3 ^ 4 →
    InnLabelOf B S lab → GLAInLambda2 lab → 3 ≤ rk2Mult lab (rk2Ord 3 lab.n) →
    ((lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n + 1 ∧ lab.rank ≤ 4) ∨ (lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n - 1) ∨
      (lab.tag = .twD ∧ 3 ∣ 2 ^ lab.n + 1 ∧ lab.rank = 3)) → False

@[expose] def QSF3ResSp : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x : Ω) (D K : Subgroup Ω)
    (lab : GLALabel), QSNL 3 S B T x D K → catalogIs (PSimple 3 K) (tyF 3) → Nat.card B = 3 ^ 4 →
    InnLabelOf B S lab → GLAInLambda2 lab → 3 ≤ rk2Mult lab (rk2Ord 3 lab.n) →
    ((lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank ≤ 4) → False

@[expose] def QSF3ResOmP : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x : Ω) (D K : Subgroup Ω)
    (lab : GLALabel), QSNL 3 S B T x D K → catalogIs (PSimple 3 K) (tyF 3) → Nat.card B = 3 ^ 4 →
    InnLabelOf B S lab → GLAInLambda2 lab → 3 ≤ rk2Mult lab (rk2Ord 3 lab.n) →
    (lab.tag = .D ∧ 3 ∣ 2 ^ lab.n + 1 ∧ lab.rank ≤ 5) → False

@[expose] def QSF3ResOmM : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x : Ω) (D K : Subgroup Ω)
    (lab : GLALabel), QSNL 3 S B T x D K → catalogIs (PSimple 3 K) (tyF 3) → Nat.card B = 3 ^ 4 →
    InnLabelOf B S lab → GLAInLambda2 lab → 3 ≤ rk2Mult lab (rk2Ord 3 lab.n) →
    (lab.tag = .twD ∧ lab.rank = 4) → False

theorem qsF3ResCls_of_parts (hLin : QSF3ResLin) (hUni : QSF3ResUni) (hSp : QSF3ResSp)
    (hOmP : QSF3ResOmP) (hOmM : QSF3ResOmM) : QSF3ResCls := by
  intro Ω _ _ S B T x D K lab hN hcat hB hlab hlab2 h3 hc
  have l := hLin Ω S B T x D K lab hN hcat hB hlab hlab2 h3
  have u := hUni Ω S B T x D K lab hN hcat hB hlab hlab2 h3
  have om := hOmM Ω S B T x D K lab hN hcat hB hlab hlab2 h3
  rcases hc with h | h | h | h | h | h | h | ⟨ht, hm, hr⟩ | ⟨ht, hp, hr⟩
  · exact l (.inl h)
  · exact l (.inr (.inl h))
  · exact u (.inl h)
  · exact u (.inr (.inl h))
  · exact hSp Ω S B T x D K lab hN hcat hB hlab hlab2 h3 h
  · exact l (.inr (.inr h))
  · exact hOmP Ω S B T x D K lab hN hcat hB hlab hlab2 h3 h
  · rw [rk2Ord_eq_one_iff.2 hm] at h3
    simp [rk2Mult, ht] at h3
    exact om ⟨ht, by omega⟩
  · rw [(rk2Ord_eq_two_iff Nat.prime_three (by decide)).2 hp] at h3
    simp [rk2Mult, ht] at h3
    have hr' : lab.rank = 3 ∨ lab.rank = 4 := by split_ifs at h3 <;> omega
    rcases hr' with hr' | hr'
    · exact u (.inr (.inr ⟨ht, hp, hr'⟩))
    · exact om ⟨ht, hr'⟩

end CFSG.LocalAnalysis.GLTheoremA.S265

end
