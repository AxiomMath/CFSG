module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93W

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.LU.Local CFSG.Blueprint
  CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def Ivk93WEmpty (P : (X : Type) → [Group X] → Prop) : Prop :=
  ∀ (J : Type) [Group J] [Finite J], P J → ∀ (x : J) (q : ℕ) (B : Subgroup J), Ivk93W x q B →
    Ivk93WBound J q → False

@[expose] def Ivk93WEmptyQ (P : (X : Type) → [Group X] → Prop) : Prop :=
  ∀ (J : Type) [Group J] [Finite J], P J → ∀ (x : J) (q : ℕ) (B : Subgroup J), Ivk93W x q B →
    Ivk93WBound J q → (Odd (Nat.card (commutator (Outer J))) → Ivk93WQuat x B) → False

@[expose] def Ivk93WD4 (r : ℕ) : Prop :=
  ∀ (J : Type) [Group J] [Finite J], (∃ p f : ℕ, p ^ f = r ∧ LieModel J .trialityD4 0 p f) →
    ∀ (x : J) (q : ℕ) (B : Subgroup J), Ivk93W x q B → Ivk93WBound J q → r = 3 ∧ q = 27

structure Ivk93WLeaves : Prop where
  alt : ∀ n : ℕ, 7 ≤ n → n ≤ 11 → Ivk93WEmpty (fun X _ => Nonempty (X ≃* alternatingGroup (Fin n)))
  m11 : Ivk93WEmpty (fun X _ => NativeSporadic.IsSporadic X .M11)
  m12 : Ivk93WEmpty (fun X _ => NativeSporadic.IsSporadic X .M12)
  m22 : Ivk93WEmpty (fun X _ => NativeSporadic.IsSporadic X .M22)
  m23 : Ivk93WEmpty (fun X _ => NativeSporadic.IsSporadic X .M23)
  j1 : Ivk93WEmpty (fun X _ => NativeSporadic.IsSporadic X .J1)
  j2 : Ivk93WEmpty (fun X _ => NativeSporadic.IsSporadic X .J2)
  j3 : Ivk93WEmpty (fun X _ => NativeSporadic.IsSporadic X .J3)
  mcl : Ivk93WEmpty (fun X _ => NativeSporadic.IsSporadic X .McL)
  ly : Ivk93WEmpty (fun X _ => NativeSporadic.IsSporadic X .Ly)
  l2 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk93WEmpty (fun X _ => LieModel X .PSL 2 p f)
  l3 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk93WEmptyQ (fun X _ => LieModel X .PSL 3 p f)
  u3 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk93WEmptyQ (fun X _ => LieModel X .PSU 3 p f)
  sp4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk93WEmpty (fun X _ => LieModel X .PSp 2 p f)
  g2 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk93WEmpty (fun X _ => LieModel X .G2 0 p f)
  d4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk93WD4 (p ^ f)
  l4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → p ^ f % 8 ≠ 1 →
    Ivk93WEmpty (fun X _ => LieModel X .PSL 4 p f)
  u4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → p ^ f % 8 ≠ 7 →
    Ivk93WEmpty (fun X _ => LieModel X .PSU 4 p f)
  l5 : ∀ p f : ℕ, p.Prime → 1 ≤ f → p ^ f % 4 = 3 → Ivk93WEmpty (fun X _ => LieModel X .PSL 5 p f)
  u5 : ∀ p f : ℕ, p.Prime → 1 ≤ f → p ^ f % 4 = 1 → Ivk93WEmpty (fun X _ => LieModel X .PSU 5 p f)
  ree : ∀ f : ℕ, Ivk93WEmpty (fun X _ => LieModel X .twistedG2 0 3 f)
  l28 : Ivk93WEmpty (fun X _ => LieModel X .PSL 2 2 3)
  l216 : Ivk93WEmpty (fun X _ => LieModel X .PSL 2 2 4)
  l34 : Ivk93WEmpty (fun X _ => LieModel X .PSL 3 2 2)
  u34 : Ivk93WEmpty (fun X _ => LieModel X .PSU 3 2 2)
  sz8 : Ivk93WEmpty (fun X _ => LieModel X .twistedB2 0 2 3)

theorem ivk93W_of_leaves (hl : Ivk93WLeaves) :
    ∀ (J : Type) [Group J] [Finite J], GHList J → ∀ (x : J) (q : ℕ) (B : Subgroup J),
      Ivk93W x q B → Ivk93WBound J q →
      (Odd (Nat.card (commutator (Outer J))) → Ivk93WQuat x B) →
      LieModel J .trialityD4 0 3 1 ∧ q = 27 := by
  intro J _ _ hGH x q B hW hB hQ
  rcases hGH with ⟨n, h7, h11, he⟩ | hspor | ⟨p, f, hp, hf, hlie⟩
  · exact (hl.alt n h7 h11 J he x q B hW hB).elim
  · rcases hspor with hs | hs | hs | hs | hs | hs | hs | hs | hs
    · exact (hl.m11 J hs x q B hW hB).elim
    · exact (hl.m12 J hs x q B hW hB).elim
    · exact (hl.m22 J hs x q B hW hB).elim
    · exact (hl.m23 J hs x q B hW hB).elim
    · exact (hl.j1 J hs x q B hW hB).elim
    · exact (hl.j2 J hs x q B hW hB).elim
    · exact (hl.j3 J hs x q B hW hB).elim
    · exact (hl.mcl J hs x q B hW hB).elim
    · exact (hl.ly J hs x q B hW hB).elim
  · rcases hlie with ⟨hp2, hm | hm | hm | hm | hm | hm⟩ | ⟨hp2, hmod, hm⟩ | ⟨hp2, hmod, hm⟩ |
      ⟨hmod, hm⟩ | ⟨hmod, hm⟩ | hm | ⟨hp2, hm | hm | hm | hm | hm⟩
    · exact (hl.l2 p f hp hp2 hf J hm x q B hW hB).elim
    · exact (hl.l3 p f hp hp2 hf J hm x q B hW hB hQ).elim
    · exact (hl.u3 p f hp hp2 hf J hm x q B hW hB hQ).elim
    · exact (hl.sp4 p f hp hp2 hf J hm x q B hW hB).elim
    · exact (hl.g2 p f hp hp2 hf J hm x q B hW hB).elim
    ·
      obtain ⟨h3, h27⟩ := hl.d4 p f hp hp2 hf J ⟨p, f, rfl, hm⟩ x q B hW hB
      refine ⟨?_, h27⟩
      have hp3 : p = 3 := by
        have : p ∣ 3 := by
          rw [← h3]
          exact dvd_pow_self p (by omega)
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 this
      subst hp3
      have hf1 : f = 1 := by
        have : (3 : ℕ) ^ f = 3 ^ 1 := by rw [h3]; norm_num
        exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) this
      subst hf1
      exact hm
    · exact (hl.l4 p f hp hp2 hf hmod J hm x q B hW hB).elim
    · exact (hl.u4 p f hp hp2 hf hmod J hm x q B hW hB).elim
    · exact (hl.l5 p f hp hf hmod J hm x q B hW hB).elim
    · exact (hl.u5 p f hp hf hmod J hm x q B hW hB).elim
    · exact (hl.ree f J hm x q B hW hB).elim
    · exact (hl.l28 J hm x q B hW hB).elim
    · exact (hl.l216 J hm x q B hW hB).elim
    · exact (hl.l34 J hm x q B hW hB).elim
    · exact (hl.u34 J hm x q B hW hB).elim
    · exact (hl.sz8 J hm x q B hW hB).elim

end CFSG.GH74.GLS.IVK.Proofs2
