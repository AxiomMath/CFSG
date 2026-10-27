module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12Red

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.Blueprint CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12

structure Ivk93M12Data (J : Type) [Group J] [Finite J] (y : J) : Prop where
  simple : IsSimpleGroup J
  nonab : ∃ a b : J, a * b ≠ b * a
  central : IsCentralInvolution y
  solvable : Group.IsSolvable ↥(centralizer ({y} : Set J))
  elemAbelian_le : ∀ E : Subgroup J, (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → (∀ a ∈ E, a ^ 2 = 1) →
    Nat.card ↥E ≤ 8
  elemAbelian_cent : ∃ E : Subgroup J, E ≤ centralizer ({y} : Set J) ∧
    (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a ^ 2 = 1) ∧ Nat.card ↥E = 8
  sylow_card : ∀ S : Sylow 2 J, Nat.card ↥(S : Subgroup J) = 8 ∨ Nat.card ↥(S : Subgroup J) = 32 ∨
    Nat.card ↥(S : Subgroup J) = 64
  cent_card : ∃ n m : ℕ, (n = 8 ∨ n = 32 ∨ n = 96 ∨ n = 192) ∧ Odd m ∧
    Nat.card ↥(centralizer ({y} : Set J)) = n * m
  aut : 192 ∣ Nat.card ↥(MulAction.stabilizer (MulAut J) y)
  quot : ∃ (P : Type) (_ : Group P) (_ : Finite P) (zc : P), BarShape P zc ∧
    ∃ N : Subgroup P, N.Normal ∧ ∃ (hz : zc ∈ N) (φ : ↥(centralizer ({y} : Set J)) →* ↥N),
      Function.Surjective φ ∧ (∀ k ∈ φ.ker, Odd (orderOf k)) ∧
        φ ⟨y, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ = ⟨zc, hz⟩

@[expose] def Ivk93M12Empty (F : (X : Type) → [Group X] → Prop) : Prop :=
  ∀ (J : Type) [Group J] [Finite J], F J → ∀ y : J, Ivk93M12Data J y → False

@[expose] def Ivk93M12Der : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (x : X), orderOf x = 2 → ∀ hxJ : x ∈ generalizedFitting X,
    IsSimpleGroup ↥(generalizedFitting X) → (∃ a b : ↥(generalizedFitting X), a * b ≠ b * a) →
    (∃ T : Sylow 2 X, ∀ t ∈ (T : Subgroup X), t * x = x * t) →
    ∀ (P : Type) [Group P] [Finite P] (zc : P), BarShape P zc →
      ∀ ρ : ↥(centralizer ({x} : Set X)) →* P, Function.Surjective ρ →
        (∀ y ∈ ρ.ker, Odd (orderOf y)) →
        ρ ⟨x, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ = zc →
          Ivk93M12Data ↥(generalizedFitting X) ⟨x, hxJ⟩

structure Ivk93M12Leaves : Prop where
  alt : ∀ m : ℕ, 7 ≤ m → m ≤ 11 →
    Ivk93M12Empty (fun X _ => Nonempty (X ≃* alternatingGroup (Fin m)))
  m11 : Ivk93M12Empty (fun X _ => NativeSporadic.IsSporadic X .M11)
  m22 : Ivk93M12Empty (fun X _ => NativeSporadic.IsSporadic X .M22)
  m23 : Ivk93M12Empty (fun X _ => NativeSporadic.IsSporadic X .M23)
  j1 : Ivk93M12Empty (fun X _ => NativeSporadic.IsSporadic X .J1)
  j2 : Ivk93M12Empty (fun X _ => NativeSporadic.IsSporadic X .J2)
  j3 : Ivk93M12Empty (fun X _ => NativeSporadic.IsSporadic X .J3)
  mcl : Ivk93M12Empty (fun X _ => NativeSporadic.IsSporadic X .McL)
  ly : Ivk93M12Empty (fun X _ => NativeSporadic.IsSporadic X .Ly)
  l2 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk93M12Empty (fun X _ => LieModel X .PSL 2 p f)
  l3 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk93M12Empty (fun X _ => LieModel X .PSL 3 p f)
  u3 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk93M12Empty (fun X _ => LieModel X .PSU 3 p f)
  sp4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk93M12Empty (fun X _ => LieModel X .PSp 2 p f)
  g2 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk93M12Empty (fun X _ => LieModel X .G2 0 p f)
  d4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    Ivk93M12Empty (fun X _ => LieModel X .trialityD4 0 p f)
  l4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → p ^ f % 8 ≠ 1 →
    Ivk93M12Empty (fun X _ => LieModel X .PSL 4 p f)
  u4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → p ^ f % 8 ≠ 7 →
    Ivk93M12Empty (fun X _ => LieModel X .PSU 4 p f)
  l5 : ∀ p f : ℕ, p.Prime → 1 ≤ f → p ^ f % 4 = 3 →
    Ivk93M12Empty (fun X _ => LieModel X .PSL 5 p f)
  u5 : ∀ p f : ℕ, p.Prime → 1 ≤ f → p ^ f % 4 = 1 →
    Ivk93M12Empty (fun X _ => LieModel X .PSU 5 p f)
  ree : ∀ f : ℕ, Ivk93M12Empty (fun X _ => LieModel X .twistedG2 0 3 f)
  l28 : Ivk93M12Empty (fun X _ => LieModel X .PSL 2 2 3)
  l216 : Ivk93M12Empty (fun X _ => LieModel X .PSL 2 2 4)
  l34 : Ivk93M12Empty (fun X _ => LieModel X .PSL 3 2 2)
  u34 : Ivk93M12Empty (fun X _ => LieModel X .PSU 3 2 2)
  sz8 : Ivk93M12Empty (fun X _ => LieModel X .twistedB2 0 2 3)

theorem ivk93M12J_of_leaves (hder : Ivk93M12Der) (hl : Ivk93M12Leaves) : Ivk93M12J := by
  intro X _ _ x hx hxJ hs hn hGH hT P _ _ zc hP ρ hρ hodd hρx
  have hD := hder X x hx hxJ hs hn hT P zc hP ρ hρ hodd hρx
  set J := ↥(generalizedFitting X) with hJ
  set y : J := ⟨x, hxJ⟩ with hy
  rcases hGH with ⟨m, h7, h11, he⟩ | hspor | ⟨p, f, hp, hf, hlie⟩
  · exact (hl.alt m h7 h11 J he y hD).elim
  · rcases hspor with h | h | h | h | h | h | h | h | h
    · exact (hl.m11 J h y hD).elim
    · exact h
    · exact (hl.m22 J h y hD).elim
    · exact (hl.m23 J h y hD).elim
    · exact (hl.j1 J h y hD).elim
    · exact (hl.j2 J h y hD).elim
    · exact (hl.j3 J h y hD).elim
    · exact (hl.mcl J h y hD).elim
    · exact (hl.ly J h y hD).elim
  · rcases hlie with ⟨hp2, hm | hm | hm | hm | hm | hm⟩ | ⟨hp2, hmod, hm⟩ | ⟨hp2, hmod, hm⟩ |
      ⟨hmod, hm⟩ | ⟨hmod, hm⟩ | hm | ⟨hp2, hm | hm | hm | hm | hm⟩
    · exact (hl.l2 p f hp hp2 hf J hm y hD).elim
    · exact (hl.l3 p f hp hp2 hf J hm y hD).elim
    · exact (hl.u3 p f hp hp2 hf J hm y hD).elim
    · exact (hl.sp4 p f hp hp2 hf J hm y hD).elim
    · exact (hl.g2 p f hp hp2 hf J hm y hD).elim
    · exact (hl.d4 p f hp hp2 hf J hm y hD).elim
    · exact (hl.l4 p f hp hp2 hf hmod J hm y hD).elim
    · exact (hl.u4 p f hp hp2 hf hmod J hm y hD).elim
    · exact (hl.l5 p f hp hf hmod J hm y hD).elim
    · exact (hl.u5 p f hp hf hmod J hm y hD).elim
    · exact (hl.ree f J hm y hD).elim
    · exact (hl.l28 J hm y hD).elim
    · exact (hl.l216 J hm y hD).elim
    · exact (hl.l34 J hm y hD).elim
    · exact (hl.u34 J hm y hD).elim
    · exact (hl.sz8 J hm y hD).elim

end CFSG.GH74.GLS.IVK.Proofs2
