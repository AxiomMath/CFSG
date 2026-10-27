module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Cfg
public import CFSG.GH74.GLS.Stage2.Final.ClassicalN

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.LU.Local CFSG.Blueprint

@[expose] def Ivk93Concl (J : Type) [Group J] (q : ℕ) : Prop :=
  IVK.IsPSp4 J q ∨
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f = q ∧ q % 8 ≠ 1 ∧ LieModel J .PSL 4 p f) ∨
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f = q ∧ q % 8 ≠ 7 ∧ LieModel J .PSU 4 p f) ∨
    ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f = q ∧ LieModel J .G2 0 p f

@[expose] def Ivk93Pair : Prop :=
  ∀ (J : Type) [Group J] [Finite J], IsSimpleGroup J → GHList J → ∀ x : J, IsCentralInvolution x →
    ∀ (q : ℕ) (L₁ L₂ : Subgroup J), Ivk93Cfg x q L₁ L₂ → Ivk93Concl J q

@[expose] def Ivk93Empty (P : (X : Type) → [Group X] → Prop) : Prop :=
  ∀ (J : Type) [Group J] [Finite J], P J → ∀ x : J, IsCentralInvolution x →
    ∀ (q : ℕ) (L₁ L₂ : Subgroup J), Ivk93Cfg x q L₁ L₂ → False

@[expose] def Ivk93Eq (P : (X : Type) → [Group X] → Prop) (r : ℕ) : Prop :=
  ∀ (J : Type) [Group J] [Finite J], P J → ∀ x : J, IsCentralInvolution x →
    ∀ (q : ℕ) (L₁ L₂ : Subgroup J), Ivk93Cfg x q L₁ L₂ → r = q

theorem Ivk93Empty.eq {P : (X : Type) → [Group X] → Prop} (h : Ivk93Empty P) (r : ℕ) : Ivk93Eq P r :=
  fun J _ _ hJ x hx q L₁ L₂ hc => (h J hJ x hx q L₁ L₂ hc).elim

theorem ivk93_empty_of_cfg {P : (X : Type) → [Group X] → Prop}
    (h : ∀ (J : Type) [Group J] [Finite J], P J → ∀ x : J, IsCentralInvolution x →
      ∀ (q : ℕ) (L₁ L₂ : Subgroup J), Ivk93Cfg x q L₁ L₂ → False) : Ivk93Empty P := h

structure Ivk93Leaves : Prop where
  alt : ∀ n : ℕ, 7 ≤ n → n ≤ 11 → Ivk93Empty (fun X _ => Nonempty (X ≃* alternatingGroup (Fin n)))
  m11 : Ivk93Empty (fun X _ => NativeSporadic.IsSporadic X .M11)
  m12 : Ivk93Empty (fun X _ => NativeSporadic.IsSporadic X .M12)
  m22 : Ivk93Empty (fun X _ => NativeSporadic.IsSporadic X .M22)
  m23 : Ivk93Empty (fun X _ => NativeSporadic.IsSporadic X .M23)
  j1 : Ivk93Empty (fun X _ => NativeSporadic.IsSporadic X .J1)
  j2 : Ivk93Empty (fun X _ => NativeSporadic.IsSporadic X .J2)
  j3 : Ivk93Empty (fun X _ => NativeSporadic.IsSporadic X .J3)
  mcl : Ivk93Empty (fun X _ => NativeSporadic.IsSporadic X .McL)
  ly : Ivk93Empty (fun X _ => NativeSporadic.IsSporadic X .Ly)
  l2 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk93Empty (fun X _ => LieModel X .PSL 2 p f)
  l3 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk93Empty (fun X _ => LieModel X .PSL 3 p f)
  u3 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk93Empty (fun X _ => LieModel X .PSU 3 p f)
  sp4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk93Eq (fun X _ => LieModel X .PSp 2 p f) (p ^ f)
  g2 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk93Eq (fun X _ => LieModel X .G2 0 p f) (p ^ f)
  d4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk93Empty (fun X _ => LieModel X .trialityD4 0 p f)
  l4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → p ^ f % 8 ≠ 1 →
    Ivk93Eq (fun X _ => LieModel X .PSL 4 p f) (p ^ f)
  u4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → p ^ f % 8 ≠ 7 →
    Ivk93Eq (fun X _ => LieModel X .PSU 4 p f) (p ^ f)
  l5 : ∀ p f : ℕ, p.Prime → 1 ≤ f → p ^ f % 4 = 3 → Ivk93Empty (fun X _ => LieModel X .PSL 5 p f)
  u5 : ∀ p f : ℕ, p.Prime → 1 ≤ f → p ^ f % 4 = 1 → Ivk93Empty (fun X _ => LieModel X .PSU 5 p f)
  ree : ∀ f : ℕ, Ivk93Empty (fun X _ => LieModel X .twistedG2 0 3 f)
  l28 : Ivk93Empty (fun X _ => LieModel X .PSL 2 2 3)
  l216 : Ivk93Empty (fun X _ => LieModel X .PSL 2 2 4)
  l34 : Ivk93Empty (fun X _ => LieModel X .PSL 3 2 2)
  u34 : Ivk93Empty (fun X _ => LieModel X .PSU 3 2 2)
  sz8 : Ivk93Empty (fun X _ => LieModel X .twistedB2 0 2 3)

theorem ivk93Pair_of_leaves (hl : Ivk93Leaves) : Ivk93Pair := by
  intro J _ _ _ hGH x hx q L₁ L₂ hc
  rcases hGH with ⟨n, h7, h11, he⟩ | hspor | ⟨p, f, hp, hf, hlie⟩
  · exact (hl.alt n h7 h11 J he x hx q L₁ L₂ hc).elim
  · rcases hspor with hs | hs | hs | hs | hs | hs | hs | hs | hs
    · exact (hl.m11 J hs x hx q L₁ L₂ hc).elim
    · exact (hl.m12 J hs x hx q L₁ L₂ hc).elim
    · exact (hl.m22 J hs x hx q L₁ L₂ hc).elim
    · exact (hl.m23 J hs x hx q L₁ L₂ hc).elim
    · exact (hl.j1 J hs x hx q L₁ L₂ hc).elim
    · exact (hl.j2 J hs x hx q L₁ L₂ hc).elim
    · exact (hl.j3 J hs x hx q L₁ L₂ hc).elim
    · exact (hl.mcl J hs x hx q L₁ L₂ hc).elim
    · exact (hl.ly J hs x hx q L₁ L₂ hc).elim
  · rcases hlie with ⟨hp2, hm | hm | hm | hm | hm | hm⟩ | ⟨hp2, hmod, hm⟩ | ⟨hp2, hmod, hm⟩ |
      ⟨hmod, hm⟩ | ⟨hmod, hm⟩ | hm | ⟨hp2, hm | hm | hm | hm | hm⟩
    · exact (hl.l2 p f hp hp2 hf J hm x hx q L₁ L₂ hc).elim
    · exact (hl.l3 p f hp hp2 hf J hm x hx q L₁ L₂ hc).elim
    · exact (hl.u3 p f hp hp2 hf J hm x hx q L₁ L₂ hc).elim
    ·
      have hq := hl.sp4 p f hp hp2 hf J hm x hx q L₁ L₂ hc
      left
      rw [← hq]
      exact CFSG.GH74.GLS.Stage2.Final.isPSp4_of_lieModel hm
    ·
      have hq := hl.g2 p f hp hp2 hf J hm x hx q L₁ L₂ hc
      exact Or.inr (Or.inr (Or.inr ⟨p, f, hp, hp2, hf, hq, hm⟩))
    · exact (hl.d4 p f hp hp2 hf J hm x hx q L₁ L₂ hc).elim
    ·
      have hq := hl.l4 p f hp hp2 hf hmod J hm x hx q L₁ L₂ hc
      right; left
      exact ⟨p, f, hp, hp2, hf, hq, hq ▸ hmod, hm⟩
    ·
      have hq := hl.u4 p f hp hp2 hf hmod J hm x hx q L₁ L₂ hc
      right; right; left
      exact ⟨p, f, hp, hp2, hf, hq, hq ▸ hmod, hm⟩
    · exact (hl.l5 p f hp hf hmod J hm x hx q L₁ L₂ hc).elim
    · exact (hl.u5 p f hp hf hmod J hm x hx q L₁ L₂ hc).elim
    · exact (hl.ree f J hm x hx q L₁ L₂ hc).elim
    · exact (hl.l28 J hm x hx q L₁ L₂ hc).elim
    · exact (hl.l216 J hm x hx q L₁ L₂ hc).elim
    · exact (hl.l34 J hm x hx q L₁ L₂ hc).elim
    · exact (hl.u34 J hm x hx q L₁ L₂ hc).elim
    · exact (hl.sz8 J hm x hx q L₁ L₂ hc).elim

end CFSG.GH74.GLS.IVK.Proofs2
