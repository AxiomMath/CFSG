module

public import CFSG.GH74.GLS.LU.Local.KStepGHDefs

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.LU.Local CFSG.Blueprint

@[expose] def Ivk95Fam (P : (X : Type) → [Group X] → Prop) : Prop :=
  ∀ (J : Type) [Group J] [Finite J], P J → ∀ z : J, orderOf z = 2 → ∀ q : ℕ, Odd q → 5 ≤ q →
    HasSL2Model ↥(Ez z) (fun r => r = q) →
    (∀ S : Sylow 2 ↥(centralizer ((Ez z : Subgroup J) : Set J)), IsCyclic ↥S) →
      ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ IsLnEps 3 J ε q

@[expose] def Ivk95Empty (P : (X : Type) → [Group X] → Prop) : Prop :=
  ∀ (J : Type) [Group J] [Finite J], P J → ∀ z : J, orderOf z = 2 → ∀ q : ℕ, Odd q → 5 ≤ q →
    HasSL2Model ↥(Ez z) (fun r => r = q) →
    (∀ S : Sylow 2 ↥(centralizer ((Ez z : Subgroup J) : Set J)), IsCyclic ↥S) → False

theorem Ivk95Empty.fam {P : (X : Type) → [Group X] → Prop} (h : Ivk95Empty P) : Ivk95Fam P :=
  fun J _ _ hJ z hz q hq h5 hsl hcyc => (h J hJ z hz q hq h5 hsl hcyc).elim

structure Ivk95Leaves : Prop where
  alt : ∀ n : ℕ, 7 ≤ n → n ≤ 11 → Ivk95Empty (fun X _ => Nonempty (X ≃* alternatingGroup (Fin n)))
  m11 : Ivk95Empty (fun X _ => NativeSporadic.IsSporadic X .M11)
  m12 : Ivk95Empty (fun X _ => NativeSporadic.IsSporadic X .M12)
  m22 : Ivk95Empty (fun X _ => NativeSporadic.IsSporadic X .M22)
  m23 : Ivk95Empty (fun X _ => NativeSporadic.IsSporadic X .M23)
  j1 : Ivk95Empty (fun X _ => NativeSporadic.IsSporadic X .J1)
  j2 : Ivk95Empty (fun X _ => NativeSporadic.IsSporadic X .J2)
  j3 : Ivk95Empty (fun X _ => NativeSporadic.IsSporadic X .J3)
  mcl : Ivk95Empty (fun X _ => NativeSporadic.IsSporadic X .McL)
  ly : Ivk95Empty (fun X _ => NativeSporadic.IsSporadic X .Ly)
  l2 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk95Empty (fun X _ => LieModel X .PSL 2 p f)
  l3 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk95Fam (fun X _ => LieModel X .PSL 3 p f)
  u3 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk95Fam (fun X _ => LieModel X .PSU 3 p f)
  sp4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk95Empty (fun X _ => LieModel X .PSp 2 p f)
  g2 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk95Empty (fun X _ => LieModel X .G2 0 p f)
  d4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk95Empty (fun X _ => LieModel X .trialityD4 0 p f)
  l4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → p ^ f % 8 ≠ 1 →
    Ivk95Empty (fun X _ => LieModel X .PSL 4 p f)
  u4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → p ^ f % 8 ≠ 7 →
    Ivk95Empty (fun X _ => LieModel X .PSU 4 p f)
  l5 : ∀ p f : ℕ, p.Prime → 1 ≤ f → p ^ f % 4 = 3 → Ivk95Empty (fun X _ => LieModel X .PSL 5 p f)
  u5 : ∀ p f : ℕ, p.Prime → 1 ≤ f → p ^ f % 4 = 1 → Ivk95Empty (fun X _ => LieModel X .PSU 5 p f)
  ree : ∀ f : ℕ, Ivk95Empty (fun X _ => LieModel X .twistedG2 0 3 f)
  l28 : Ivk95Empty (fun X _ => LieModel X .PSL 2 2 3)
  l216 : Ivk95Empty (fun X _ => LieModel X .PSL 2 2 4)
  l34 : Ivk95Empty (fun X _ => LieModel X .PSL 3 2 2)
  u34 : Ivk95Empty (fun X _ => LieModel X .PSU 3 2 2)
  sz8 : Ivk95Empty (fun X _ => LieModel X .twistedB2 0 2 3)

theorem ivk_9_5At_gh_all_of_leaves (hl : Ivk95Leaves) : IVK_9_5At_gh_all := by
  intro q hq5 J _ _ _ _ hGH z hz hodd hsl hcyc
  rcases hGH with ⟨n, h7, h11, he⟩ | hspor | ⟨p, f, hp, hf, hlie⟩
  · exact (hl.alt n h7 h11 J he z hz q hodd hq5 hsl hcyc).elim
  · rcases hspor with hs | hs | hs | hs | hs | hs | hs | hs | hs
    · exact (hl.m11 J hs z hz q hodd hq5 hsl hcyc).elim
    · exact (hl.m12 J hs z hz q hodd hq5 hsl hcyc).elim
    · exact (hl.m22 J hs z hz q hodd hq5 hsl hcyc).elim
    · exact (hl.m23 J hs z hz q hodd hq5 hsl hcyc).elim
    · exact (hl.j1 J hs z hz q hodd hq5 hsl hcyc).elim
    · exact (hl.j2 J hs z hz q hodd hq5 hsl hcyc).elim
    · exact (hl.j3 J hs z hz q hodd hq5 hsl hcyc).elim
    · exact (hl.mcl J hs z hz q hodd hq5 hsl hcyc).elim
    · exact (hl.ly J hs z hz q hodd hq5 hsl hcyc).elim
  · rcases hlie with ⟨hp2, hm | hm | hm | hm | hm | hm⟩ | ⟨hp2, hmod, hm⟩ | ⟨hp2, hmod, hm⟩ |
      ⟨hmod, hm⟩ | ⟨hmod, hm⟩ | hm | ⟨hp2, hm | hm | hm | hm | hm⟩
    · exact (hl.l2 p f hp hp2 hf J hm z hz q hodd hq5 hsl hcyc).elim
    · exact hl.l3 p f hp hp2 hf J hm z hz q hodd hq5 hsl hcyc
    · exact hl.u3 p f hp hp2 hf J hm z hz q hodd hq5 hsl hcyc
    · exact (hl.sp4 p f hp hp2 hf J hm z hz q hodd hq5 hsl hcyc).elim
    · exact (hl.g2 p f hp hp2 hf J hm z hz q hodd hq5 hsl hcyc).elim
    · exact (hl.d4 p f hp hp2 hf J hm z hz q hodd hq5 hsl hcyc).elim
    · exact (hl.l4 p f hp hp2 hf hmod J hm z hz q hodd hq5 hsl hcyc).elim
    · exact (hl.u4 p f hp hp2 hf hmod J hm z hz q hodd hq5 hsl hcyc).elim
    · exact (hl.l5 p f hp hf hmod J hm z hz q hodd hq5 hsl hcyc).elim
    · exact (hl.u5 p f hp hf hmod J hm z hz q hodd hq5 hsl hcyc).elim
    · exact (hl.ree f J hm z hz q hodd hq5 hsl hcyc).elim
    · exact (hl.l28 J hm z hz q hodd hq5 hsl hcyc).elim
    · exact (hl.l216 J hm z hz q hodd hq5 hsl hcyc).elim
    · exact (hl.l34 J hm z hz q hodd hq5 hsl hcyc).elim
    · exact (hl.u34 J hm z hz q hodd hq5 hsl hcyc).elim
    · exact (hl.sz8 J hm z hz q hodd hq5 hsl hcyc).elim

end CFSG.GH74.GLS.IVK.Proofs2
