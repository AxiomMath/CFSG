module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Cfg

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.ABGLocalTools Blueprint

@[expose] def Ivk73Fam (P : (X : Type) → [Group X] → Prop) : Prop :=
  ∀ (N : Type) [Group N] [Finite N] (L K Q : Subgroup N), Ivk73Cfg N L K Q → P ↥L → Ivk73Concl N L K Q

@[expose] def Ivk73Empty (P : (X : Type) → [Group X] → Prop) : Prop :=
  ∀ (N : Type) [Group N] [Finite N] (L K Q : Subgroup N), Ivk73Cfg N L K Q → P ↥L → False

structure Ivk73Leaves : Prop where
  alt : ∀ n : ℕ, 7 ≤ n → n ≤ 11 → Ivk73Fam (fun X _ => Nonempty (X ≃* alternatingGroup (Fin n)))
  m11 : Ivk73Empty (fun X _ => NativeSporadic.IsSporadic X .M11)
  m12 : Ivk73Fam (fun X _ => NativeSporadic.IsSporadic X .M12)
  m22 : Ivk73Empty (fun X _ => NativeSporadic.IsSporadic X .M22)
  m23 : Ivk73Empty (fun X _ => NativeSporadic.IsSporadic X .M23)
  j1 : Ivk73Empty (fun X _ => NativeSporadic.IsSporadic X .J1)
  j2 : Ivk73Fam (fun X _ => NativeSporadic.IsSporadic X .J2)
  j3 : Ivk73Empty (fun X _ => NativeSporadic.IsSporadic X .J3)
  mcl : Ivk73Empty (fun X _ => NativeSporadic.IsSporadic X .McL)
  ly : Ivk73Empty (fun X _ => NativeSporadic.IsSporadic X .Ly)
  l2 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk73Empty (fun X _ => LieModel X .PSL 2 p f)
  l3 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk73Empty (fun X _ => LieModel X .PSL 3 p f)
  u3 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk73Empty (fun X _ => LieModel X .PSU 3 p f)
  sp4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk73Empty (fun X _ => LieModel X .PSp 2 p f)
  g2 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk73Empty (fun X _ => LieModel X .G2 0 p f)
  d4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk73Empty (fun X _ => LieModel X .trialityD4 0 p f)
  l4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → p ^ f % 8 ≠ 1 →
    Ivk73Empty (fun X _ => LieModel X .PSL 4 p f)
  u4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → p ^ f % 8 ≠ 7 →
    Ivk73Empty (fun X _ => LieModel X .PSU 4 p f)
  l5 : ∀ p f : ℕ, p.Prime → 1 ≤ f → p ^ f % 4 = 3 → Ivk73Empty (fun X _ => LieModel X .PSL 5 p f)
  u5 : ∀ p f : ℕ, p.Prime → 1 ≤ f → p ^ f % 4 = 1 → Ivk73Empty (fun X _ => LieModel X .PSU 5 p f)
  ree : ∀ f : ℕ, Ivk73Empty (fun X _ => LieModel X .twistedG2 0 3 f)
  l28 : Ivk73Empty (fun X _ => LieModel X .PSL 2 2 3)
  l216 : Ivk73Empty (fun X _ => LieModel X .PSL 2 2 4)
  l34 : Ivk73Empty (fun X _ => LieModel X .PSL 3 2 2)
  u34 : Ivk73Empty (fun X _ => LieModel X .PSU 3 2 2)
  sz8 : Ivk73Empty (fun X _ => LieModel X .twistedB2 0 2 3)

theorem ivk73Concl_of_leaves (hl : Ivk73Leaves) {N : Type} [Group N] [Finite N] {L K Q : Subgroup N}
    (h : Ivk73Cfg N L K Q) : Ivk73Concl N L K Q := by
  rcases h.ghList with ⟨n, h7, h11, he⟩ | hspor | ⟨p, f, hp, hf, hlie⟩
  · exact hl.alt n h7 h11 N L K Q h he
  · rcases hspor with hs | hs | hs | hs | hs | hs | hs | hs | hs
    · exact (hl.m11 N L K Q h hs).elim
    · exact hl.m12 N L K Q h hs
    · exact (hl.m22 N L K Q h hs).elim
    · exact (hl.m23 N L K Q h hs).elim
    · exact (hl.j1 N L K Q h hs).elim
    · exact hl.j2 N L K Q h hs
    · exact (hl.j3 N L K Q h hs).elim
    · exact (hl.mcl N L K Q h hs).elim
    · exact (hl.ly N L K Q h hs).elim
  · exfalso
    rcases hlie with ⟨hp2, hm | hm | hm | hm | hm | hm⟩ | ⟨hp2, hmod, hm⟩ | ⟨hp2, hmod, hm⟩ |
      ⟨hmod, hm⟩ | ⟨hmod, hm⟩ | hm | ⟨hp2, hm | hm | hm | hm | hm⟩
    · exact hl.l2 p f hp hp2 hf N L K Q h hm
    · exact hl.l3 p f hp hp2 hf N L K Q h hm
    · exact hl.u3 p f hp hp2 hf N L K Q h hm
    · exact hl.sp4 p f hp hp2 hf N L K Q h hm
    · exact hl.g2 p f hp hp2 hf N L K Q h hm
    · exact hl.d4 p f hp hp2 hf N L K Q h hm
    · exact hl.l4 p f hp hp2 hf hmod N L K Q h hm
    · exact hl.u4 p f hp hp2 hf hmod N L K Q h hm
    · exact hl.l5 p f hp hf hmod N L K Q h hm
    · exact hl.u5 p f hp hf hmod N L K Q h hm
    · exact hl.ree f N L K Q h hm
    · exact hl.l28 N L K Q h hm
    · exact hl.l216 N L K Q h hm
    · exact hl.l34 N L K Q h hm
    · exact hl.u34 N L K Q h hm
    · exact hl.sz8 N L K Q h hm

theorem ivk_7_3_g4_of_leaves (hl : Ivk73Leaves) : IVK_7_3_g4 :=
  ivk_7_3_g4_of_core fun _ _ _ _ _ _ h => ivk73Concl_of_leaves hl h

end CFSG.GH74.GLS.IVK
