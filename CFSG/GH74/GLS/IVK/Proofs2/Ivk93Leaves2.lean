module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Cfg2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Leaves

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.LU.Local CFSG.Blueprint

@[expose] def Ivk93Concl2 (J : Type) [Group J] (q₁ q₂ : ℕ) : Prop :=
  (q₁ = q₂ ∧ Ivk93Concl J q₁) ∨
    ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ LieModel J .trialityD4 0 p f ∧
      ((q₁ = (p ^ f) ^ 3 ∧ q₂ = p ^ f) ∨ (q₁ = p ^ f ∧ q₂ = (p ^ f) ^ 3))

@[expose] def Ivk93Pair2 : Prop :=
  ∀ (J : Type) [Group J] [Finite J], IsSimpleGroup J → GHList J → ∀ x : J, IsCentralInvolution x →
    ∀ (q₁ q₂ : ℕ) (L₁ L₂ : Subgroup J), Ivk93Cfg2 x q₁ q₂ L₁ L₂ → Ivk93Concl2 J q₁ q₂

@[expose] def Ivk93Empty2 (P : (X : Type) → [Group X] → Prop) : Prop :=
  ∀ (J : Type) [Group J] [Finite J], P J → ∀ x : J, IsCentralInvolution x →
    ∀ (q₁ q₂ : ℕ) (L₁ L₂ : Subgroup J), Ivk93Cfg2 x q₁ q₂ L₁ L₂ → False

@[expose] def Ivk93Eq2 (P : (X : Type) → [Group X] → Prop) (r : ℕ) : Prop :=
  ∀ (J : Type) [Group J] [Finite J], P J → ∀ x : J, IsCentralInvolution x →
    ∀ (q₁ q₂ : ℕ) (L₁ L₂ : Subgroup J), Ivk93Cfg2 x q₁ q₂ L₁ L₂ → r = q₁ ∧ r = q₂

@[expose] def Ivk93D42 (r : ℕ) : Prop :=
  ∀ (J : Type) [Group J] [Finite J], (∃ p f : ℕ, p ^ f = r ∧ LieModel J .trialityD4 0 p f) →
    ∀ x : J, IsCentralInvolution x →
    ∀ (q₁ q₂ : ℕ) (L₁ L₂ : Subgroup J), Ivk93Cfg2 x q₁ q₂ L₁ L₂ →
      (q₁ = r ^ 3 ∧ q₂ = r) ∨ (q₁ = r ∧ q₂ = r ^ 3)

theorem ivk93_empty2_of_cfg {P : (X : Type) → [Group X] → Prop}
    (h : ∀ (J : Type) [Group J] [Finite J], P J → ∀ x : J, IsCentralInvolution x →
      ∀ (q₁ q₂ : ℕ) (L₁ L₂ : Subgroup J), Ivk93Cfg2 x q₁ q₂ L₁ L₂ → False) : Ivk93Empty2 P := h

structure Ivk93Leaves2 : Prop where
  alt : ∀ n : ℕ, 7 ≤ n → n ≤ 11 → Ivk93Empty2 (fun X _ => Nonempty (X ≃* alternatingGroup (Fin n)))
  m11 : Ivk93Empty2 (fun X _ => NativeSporadic.IsSporadic X .M11)
  m12 : Ivk93Empty2 (fun X _ => NativeSporadic.IsSporadic X .M12)
  m22 : Ivk93Empty2 (fun X _ => NativeSporadic.IsSporadic X .M22)
  m23 : Ivk93Empty2 (fun X _ => NativeSporadic.IsSporadic X .M23)
  j1 : Ivk93Empty2 (fun X _ => NativeSporadic.IsSporadic X .J1)
  j2 : Ivk93Empty2 (fun X _ => NativeSporadic.IsSporadic X .J2)
  j3 : Ivk93Empty2 (fun X _ => NativeSporadic.IsSporadic X .J3)
  mcl : Ivk93Empty2 (fun X _ => NativeSporadic.IsSporadic X .McL)
  ly : Ivk93Empty2 (fun X _ => NativeSporadic.IsSporadic X .Ly)
  l2 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk93Empty2 (fun X _ => LieModel X .PSL 2 p f)
  l3 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk93Empty2 (fun X _ => LieModel X .PSL 3 p f)
  u3 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk93Empty2 (fun X _ => LieModel X .PSU 3 p f)
  sp4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk93Eq2 (fun X _ => LieModel X .PSp 2 p f) (p ^ f)
  g2 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk93Eq2 (fun X _ => LieModel X .G2 0 p f) (p ^ f)
  d4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk93D42 (p ^ f)
  l4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → p ^ f % 8 ≠ 1 →
    Ivk93Eq2 (fun X _ => LieModel X .PSL 4 p f) (p ^ f)
  u4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → p ^ f % 8 ≠ 7 →
    Ivk93Eq2 (fun X _ => LieModel X .PSU 4 p f) (p ^ f)
  l5 : ∀ p f : ℕ, p.Prime → 1 ≤ f → p ^ f % 4 = 3 → Ivk93Empty2 (fun X _ => LieModel X .PSL 5 p f)
  u5 : ∀ p f : ℕ, p.Prime → 1 ≤ f → p ^ f % 4 = 1 → Ivk93Empty2 (fun X _ => LieModel X .PSU 5 p f)
  ree : ∀ f : ℕ, Ivk93Empty2 (fun X _ => LieModel X .twistedG2 0 3 f)
  l28 : Ivk93Empty2 (fun X _ => LieModel X .PSL 2 2 3)
  l216 : Ivk93Empty2 (fun X _ => LieModel X .PSL 2 2 4)
  l34 : Ivk93Empty2 (fun X _ => LieModel X .PSL 3 2 2)
  u34 : Ivk93Empty2 (fun X _ => LieModel X .PSU 3 2 2)
  sz8 : Ivk93Empty2 (fun X _ => LieModel X .twistedB2 0 2 3)

theorem ivk93Pair2_of_leaves (hl : Ivk93Leaves2) : Ivk93Pair2 := by
  intro J _ _ _ hGH x hx q₁ q₂ L₁ L₂ hc
  rcases hGH with ⟨n, h7, h11, he⟩ | hspor | ⟨p, f, hp, hf, hlie⟩
  · exact (hl.alt n h7 h11 J he x hx q₁ q₂ L₁ L₂ hc).elim
  · rcases hspor with hs | hs | hs | hs | hs | hs | hs | hs | hs
    · exact (hl.m11 J hs x hx q₁ q₂ L₁ L₂ hc).elim
    · exact (hl.m12 J hs x hx q₁ q₂ L₁ L₂ hc).elim
    · exact (hl.m22 J hs x hx q₁ q₂ L₁ L₂ hc).elim
    · exact (hl.m23 J hs x hx q₁ q₂ L₁ L₂ hc).elim
    · exact (hl.j1 J hs x hx q₁ q₂ L₁ L₂ hc).elim
    · exact (hl.j2 J hs x hx q₁ q₂ L₁ L₂ hc).elim
    · exact (hl.j3 J hs x hx q₁ q₂ L₁ L₂ hc).elim
    · exact (hl.mcl J hs x hx q₁ q₂ L₁ L₂ hc).elim
    · exact (hl.ly J hs x hx q₁ q₂ L₁ L₂ hc).elim
  · rcases hlie with ⟨hp2, hm | hm | hm | hm | hm | hm⟩ | ⟨hp2, hmod, hm⟩ | ⟨hp2, hmod, hm⟩ |
      ⟨hmod, hm⟩ | ⟨hmod, hm⟩ | hm | ⟨hp2, hm | hm | hm | hm | hm⟩
    · exact (hl.l2 p f hp hp2 hf J hm x hx q₁ q₂ L₁ L₂ hc).elim
    · exact (hl.l3 p f hp hp2 hf J hm x hx q₁ q₂ L₁ L₂ hc).elim
    · exact (hl.u3 p f hp hp2 hf J hm x hx q₁ q₂ L₁ L₂ hc).elim
    ·
      obtain ⟨h1, h2⟩ := hl.sp4 p f hp hp2 hf J hm x hx q₁ q₂ L₁ L₂ hc
      left
      refine ⟨h1.symm.trans h2, Or.inl ?_⟩
      rw [← h1]
      exact CFSG.GH74.GLS.Stage2.Final.isPSp4_of_lieModel hm
    ·
      obtain ⟨h1, h2⟩ := hl.g2 p f hp hp2 hf J hm x hx q₁ q₂ L₁ L₂ hc
      left
      exact ⟨h1.symm.trans h2, Or.inr (Or.inr (Or.inr ⟨p, f, hp, hp2, hf, h1, hm⟩))⟩
    ·
      right
      refine ⟨p, f, hp, hp2, hf, hm, ?_⟩
      have := hl.d4 p f hp hp2 hf J ⟨p, f, rfl, hm⟩ x hx q₁ q₂ L₁ L₂ hc
      rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨h1, h2⟩
    ·
      obtain ⟨h1, h2⟩ := hl.l4 p f hp hp2 hf hmod J hm x hx q₁ q₂ L₁ L₂ hc
      left
      refine ⟨h1.symm.trans h2, Or.inr (Or.inl ⟨p, f, hp, hp2, hf, h1, h1 ▸ hmod, hm⟩)⟩
    ·
      obtain ⟨h1, h2⟩ := hl.u4 p f hp hp2 hf hmod J hm x hx q₁ q₂ L₁ L₂ hc
      left
      refine ⟨h1.symm.trans h2, Or.inr (Or.inr (Or.inl ⟨p, f, hp, hp2, hf, h1, h1 ▸ hmod, hm⟩))⟩
    · exact (hl.l5 p f hp hf hmod J hm x hx q₁ q₂ L₁ L₂ hc).elim
    · exact (hl.u5 p f hp hf hmod J hm x hx q₁ q₂ L₁ L₂ hc).elim
    · exact (hl.ree f J hm x hx q₁ q₂ L₁ L₂ hc).elim
    · exact (hl.l28 J hm x hx q₁ q₂ L₁ L₂ hc).elim
    · exact (hl.l216 J hm x hx q₁ q₂ L₁ L₂ hc).elim
    · exact (hl.l34 J hm x hx q₁ q₂ L₁ L₂ hc).elim
    · exact (hl.u34 J hm x hx q₁ q₂ L₁ L₂ hc).elim
    · exact (hl.sz8 J hm x hx q₁ q₂ L₁ L₂ hc).elim

theorem three_le_pow {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) : 3 ≤ p ^ f := by
  have h2 := hp.two_le
  have h3 : 3 ≤ p := by omega
  exact h3.trans (Nat.le_self_pow (by omega) p)

end CFSG.GH74.GLS.IVK.Proofs2
