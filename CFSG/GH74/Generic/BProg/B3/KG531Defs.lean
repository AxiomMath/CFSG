module

public import CFSG.GH74.GLS.Classes
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.GH74.Generic.BProg.B3

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.Blueprint
open scoped MatrixGroups


structure KG531Cfg {S : Type} [Group S] (t : S) (B₁ B₂ : Subgroup S) (p f : ℕ) : Prop where
  t_ord : orderOf t = 2
  comp₁ : IsCompIn (centralizer ({t} : Set S)) B₁
  comp₂ : IsCompIn (centralizer ({t} : Set S)) B₂
  center₁ : center ↥B₁ = ⊥
  t_mem : t ∈ B₂
  comm : ∀ b ∈ B₁, ∀ c ∈ B₂, b * c = c * b
  disj : B₁ ⊓ B₂ = ⊥
  prime : p.Prime
  odd : p ≠ 2
  five : 5 ≤ p ^ f
  model₁ : StatedClassicalModel (↥B₁ ⧸ center ↥B₁) .PSL 2 p f
  model₂ : HasSL2Model ↥B₂ (fun q => q = p ^ f)

@[expose] def KG531Table : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) → GHList S →
    ∀ (t : S) (B₁ B₂ : Subgroup S) (p f : ℕ), KG531Cfg t B₁ B₂ p f → False

@[expose] def KG531Empty (P : (X : Type) → [Group X] → Prop) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) → P S →
    ∀ (t : S) (B₁ B₂ : Subgroup S) (p f : ℕ), KG531Cfg t B₁ B₂ p f → False

structure KG531Leaves : Prop where
  alt : ∀ n : ℕ, 7 ≤ n → n ≤ 11 → KG531Empty (fun X _ => Nonempty (X ≃* alternatingGroup (Fin n)))
  m11 : KG531Empty (fun X _ => NativeSporadic.IsSporadic X .M11)
  m12 : KG531Empty (fun X _ => NativeSporadic.IsSporadic X .M12)
  m22 : KG531Empty (fun X _ => NativeSporadic.IsSporadic X .M22)
  m23 : KG531Empty (fun X _ => NativeSporadic.IsSporadic X .M23)
  j1 : KG531Empty (fun X _ => NativeSporadic.IsSporadic X .J1)
  j2 : KG531Empty (fun X _ => NativeSporadic.IsSporadic X .J2)
  j3 : KG531Empty (fun X _ => NativeSporadic.IsSporadic X .J3)
  mcl : KG531Empty (fun X _ => NativeSporadic.IsSporadic X .McL)
  ly : KG531Empty (fun X _ => NativeSporadic.IsSporadic X .Ly)
  l2 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → KG531Empty (fun X _ => LieModel X .PSL 2 p f)
  l3 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → KG531Empty (fun X _ => LieModel X .PSL 3 p f)
  u3 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → KG531Empty (fun X _ => LieModel X .PSU 3 p f)
  sp4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → KG531Empty (fun X _ => LieModel X .PSp 2 p f)
  g2 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → KG531Empty (fun X _ => LieModel X .G2 0 p f)
  d4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → KG531Empty (fun X _ => LieModel X .trialityD4 0 p f)
  l4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → p ^ f % 8 ≠ 1 →
    KG531Empty (fun X _ => LieModel X .PSL 4 p f)
  u4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → p ^ f % 8 ≠ 7 →
    KG531Empty (fun X _ => LieModel X .PSU 4 p f)
  l5 : ∀ p f : ℕ, p.Prime → 1 ≤ f → p ^ f % 4 = 3 → KG531Empty (fun X _ => LieModel X .PSL 5 p f)
  u5 : ∀ p f : ℕ, p.Prime → 1 ≤ f → p ^ f % 4 = 1 → KG531Empty (fun X _ => LieModel X .PSU 5 p f)
  ree : ∀ f : ℕ, KG531Empty (fun X _ => LieModel X .twistedG2 0 3 f)
  l28 : KG531Empty (fun X _ => LieModel X .PSL 2 2 3)
  l216 : KG531Empty (fun X _ => LieModel X .PSL 2 2 4)
  l34 : KG531Empty (fun X _ => LieModel X .PSL 3 2 2)
  u34 : KG531Empty (fun X _ => LieModel X .PSU 3 2 2)
  sz8 : KG531Empty (fun X _ => LieModel X .twistedB2 0 2 3)

theorem kg531Table_of_leaves (hl : KG531Leaves) : KG531Table := by
  intro S _ _ hS hnab hGH t B₁ B₂ p f h
  rcases hGH with ⟨n, h7, h11, he⟩ | hspor | ⟨p', f', hp, hf, hlie⟩
  · exact hl.alt n h7 h11 S hS hnab he t B₁ B₂ p f h
  · rcases hspor with hs | hs | hs | hs | hs | hs | hs | hs | hs
    · exact hl.m11 S hS hnab hs t B₁ B₂ p f h
    · exact hl.m12 S hS hnab hs t B₁ B₂ p f h
    · exact hl.m22 S hS hnab hs t B₁ B₂ p f h
    · exact hl.m23 S hS hnab hs t B₁ B₂ p f h
    · exact hl.j1 S hS hnab hs t B₁ B₂ p f h
    · exact hl.j2 S hS hnab hs t B₁ B₂ p f h
    · exact hl.j3 S hS hnab hs t B₁ B₂ p f h
    · exact hl.mcl S hS hnab hs t B₁ B₂ p f h
    · exact hl.ly S hS hnab hs t B₁ B₂ p f h
  · rcases hlie with ⟨hp2, hm | hm | hm | hm | hm | hm⟩ | ⟨hp2, hmod, hm⟩ | ⟨hp2, hmod, hm⟩ |
      ⟨hmod, hm⟩ | ⟨hmod, hm⟩ | hm | ⟨hp2, hm | hm | hm | hm | hm⟩
    · exact hl.l2 p' f' hp hp2 hf S hS hnab hm t B₁ B₂ p f h
    · exact hl.l3 p' f' hp hp2 hf S hS hnab hm t B₁ B₂ p f h
    · exact hl.u3 p' f' hp hp2 hf S hS hnab hm t B₁ B₂ p f h
    · exact hl.sp4 p' f' hp hp2 hf S hS hnab hm t B₁ B₂ p f h
    · exact hl.g2 p' f' hp hp2 hf S hS hnab hm t B₁ B₂ p f h
    · exact hl.d4 p' f' hp hp2 hf S hS hnab hm t B₁ B₂ p f h
    · exact hl.l4 p' f' hp hp2 hf hmod S hS hnab hm t B₁ B₂ p f h
    · exact hl.u4 p' f' hp hp2 hf hmod S hS hnab hm t B₁ B₂ p f h
    · exact hl.l5 p' f' hp hf hmod S hS hnab hm t B₁ B₂ p f h
    · exact hl.u5 p' f' hp hf hmod S hS hnab hm t B₁ B₂ p f h
    · exact hl.ree f' S hS hnab hm t B₁ B₂ p f h
    · exact hl.l28 S hS hnab hm t B₁ B₂ p f h
    · exact hl.l216 S hS hnab hm t B₁ B₂ p f h
    · exact hl.l34 S hS hnab hm t B₁ B₂ p f h
    · exact hl.u34 S hS hnab hm t B₁ B₂ p f h
    · exact hl.sz8 S hS hnab hm t B₁ B₂ p f h


end CFSG.GH74.Generic.BProg.B3
