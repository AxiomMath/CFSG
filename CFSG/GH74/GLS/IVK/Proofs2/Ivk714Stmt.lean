module

public import CFSG.GH74.GLS.IVK.Defs

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.Blueprint CFSG.GH74.GLS

@[expose] def Ivk714Hyp (K : Type) [Group K] (z : MulAut K) : Prop :=
  Nonempty (↥(layer ↥(fixedSubgroup K z)) ⧸ pPrimeCore 2 ↥(layer ↥(fixedSubgroup K z)) ≃*
    alternatingGroup (Fin 7))

@[expose] def kz (K : Type) [Group K] (z : MulAut K) : Subgroup (MulAut K) := innAut K ⊔ zpowers z

@[expose] def Ivk714Concl (K : Type) [Group K] (z : MulAut K) : Prop :=
  (Nonempty (↥(kz K z) ≃* Equiv.Perm (Fin 9)) ∨ ∃ n : ℕ, 11 ≤ n ∧ Nonempty (K ≃* alternatingGroup (Fin n))) ∧
    2 ^ 7 ∣ Nat.card ↥(kz K z)

@[expose] def IVK_7_14_g4 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → GHList K →
    ∀ z : MulAut K, orderOf z = 2 → Ivk714Hyp K z → Ivk714Concl K z

@[expose] def Ivk714Fam (P : (X : Type) → [Group X] → Prop) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → P K →
    ∀ z : MulAut K, orderOf z = 2 → Ivk714Hyp K z → Ivk714Concl K z

@[expose] def Ivk714Empty (P : (X : Type) → [Group X] → Prop) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → P K →
    ∀ z : MulAut K, orderOf z = 2 → Ivk714Hyp K z → False

structure Ivk714Leaves : Prop where
  alt : ∀ n : ℕ, 7 ≤ n → n ≤ 11 → Ivk714Fam (fun X _ => Nonempty (X ≃* alternatingGroup (Fin n)))
  m11 : Ivk714Empty (fun X _ => NativeSporadic.IsSporadic X .M11)
  m12 : Ivk714Empty (fun X _ => NativeSporadic.IsSporadic X .M12)
  m22 : Ivk714Empty (fun X _ => NativeSporadic.IsSporadic X .M22)
  m23 : Ivk714Empty (fun X _ => NativeSporadic.IsSporadic X .M23)
  j1 : Ivk714Empty (fun X _ => NativeSporadic.IsSporadic X .J1)
  j2 : Ivk714Empty (fun X _ => NativeSporadic.IsSporadic X .J2)
  j3 : Ivk714Empty (fun X _ => NativeSporadic.IsSporadic X .J3)
  mcl : Ivk714Empty (fun X _ => NativeSporadic.IsSporadic X .McL)
  ly : Ivk714Empty (fun X _ => NativeSporadic.IsSporadic X .Ly)
  l2 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk714Empty (fun X _ => LieModel X .PSL 2 p f)
  l3 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk714Empty (fun X _ => LieModel X .PSL 3 p f)
  u3 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk714Empty (fun X _ => LieModel X .PSU 3 p f)
  sp4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk714Empty (fun X _ => LieModel X .PSp 2 p f)
  g2 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk714Empty (fun X _ => LieModel X .G2 0 p f)
  d4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk714Empty (fun X _ => LieModel X .trialityD4 0 p f)
  l4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → p ^ f % 8 ≠ 1 →
    Ivk714Empty (fun X _ => LieModel X .PSL 4 p f)
  u4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → p ^ f % 8 ≠ 7 →
    Ivk714Empty (fun X _ => LieModel X .PSU 4 p f)
  l5 : ∀ p f : ℕ, p.Prime → 1 ≤ f → p ^ f % 4 = 3 → Ivk714Empty (fun X _ => LieModel X .PSL 5 p f)
  u5 : ∀ p f : ℕ, p.Prime → 1 ≤ f → p ^ f % 4 = 1 → Ivk714Empty (fun X _ => LieModel X .PSU 5 p f)
  ree : ∀ f : ℕ, Ivk714Empty (fun X _ => LieModel X .twistedG2 0 3 f)
  l28 : Ivk714Empty (fun X _ => LieModel X .PSL 2 2 3)
  l216 : Ivk714Empty (fun X _ => LieModel X .PSL 2 2 4)
  l34 : Ivk714Empty (fun X _ => LieModel X .PSL 3 2 2)
  u34 : Ivk714Empty (fun X _ => LieModel X .PSU 3 2 2)
  sz8 : Ivk714Empty (fun X _ => LieModel X .twistedB2 0 2 3)

theorem ivk_7_14_g4_of_leaves (hl : Ivk714Leaves) : IVK_7_14_g4 := by
  intro K _ _ hs hGH z hz hE
  rcases hGH with ⟨n, h7, h11, he⟩ | hspor | ⟨p, f, hp, hf, hlie⟩
  · exact hl.alt n h7 h11 K hs he z hz hE
  · rcases hspor with hs' | hs' | hs' | hs' | hs' | hs' | hs' | hs' | hs'
    · exact (hl.m11 K hs hs' z hz hE).elim
    · exact (hl.m12 K hs hs' z hz hE).elim
    · exact (hl.m22 K hs hs' z hz hE).elim
    · exact (hl.m23 K hs hs' z hz hE).elim
    · exact (hl.j1 K hs hs' z hz hE).elim
    · exact (hl.j2 K hs hs' z hz hE).elim
    · exact (hl.j3 K hs hs' z hz hE).elim
    · exact (hl.mcl K hs hs' z hz hE).elim
    · exact (hl.ly K hs hs' z hz hE).elim
  · rcases hlie with ⟨hp2, hm | hm | hm | hm | hm | hm⟩ | ⟨hp2, hmod, hm⟩ | ⟨hp2, hmod, hm⟩ |
      ⟨hmod, hm⟩ | ⟨hmod, hm⟩ | hm | ⟨hp2, hm | hm | hm | hm | hm⟩
    · exact (hl.l2 p f hp hp2 hf K hs hm z hz hE).elim
    · exact (hl.l3 p f hp hp2 hf K hs hm z hz hE).elim
    · exact (hl.u3 p f hp hp2 hf K hs hm z hz hE).elim
    · exact (hl.sp4 p f hp hp2 hf K hs hm z hz hE).elim
    · exact (hl.g2 p f hp hp2 hf K hs hm z hz hE).elim
    · exact (hl.d4 p f hp hp2 hf K hs hm z hz hE).elim
    · exact (hl.l4 p f hp hp2 hf hmod K hs hm z hz hE).elim
    · exact (hl.u4 p f hp hp2 hf hmod K hs hm z hz hE).elim
    · exact (hl.l5 p f hp hf hmod K hs hm z hz hE).elim
    · exact (hl.u5 p f hp hf hmod K hs hm z hz hE).elim
    · exact (hl.ree f K hs hm z hz hE).elim
    · exact (hl.l28 K hs hm z hz hE).elim
    · exact (hl.l216 K hs hm z hz hE).elim
    · exact (hl.l34 K hs hm z hz hE).elim
    · exact (hl.u34 K hs hm z hz hE).elim
    · exact (hl.sz8 K hs hm z hz hE).elim

end CFSG.GH74.GLS.IVK
