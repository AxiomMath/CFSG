module

public import CFSG.GH74.GLS.C3.Layer1.St1EndNCfg
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Leaf

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools Blueprint

@[expose] def Lem711Empty (P : (X : Type) → [Group X] → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L K : Subgroup X) (x y : X),
    Lem711Cfg X L K x y → P ↥L → False

structure Lem711Leaves : Prop where
  alt : ∀ n : ℕ, 7 ≤ n → n ≤ 11 → Lem711Empty (fun X _ => Nonempty (X ≃* alternatingGroup (Fin n)))
  m11 : Lem711Empty (fun X _ => NativeSporadic.IsSporadic X .M11)
  m12 : Lem711Empty (fun X _ => NativeSporadic.IsSporadic X .M12)
  m22 : Lem711Empty (fun X _ => NativeSporadic.IsSporadic X .M22)
  m23 : Lem711Empty (fun X _ => NativeSporadic.IsSporadic X .M23)
  j1 : Lem711Empty (fun X _ => NativeSporadic.IsSporadic X .J1)
  j2 : Lem711Empty (fun X _ => NativeSporadic.IsSporadic X .J2)
  j3 : Lem711Empty (fun X _ => NativeSporadic.IsSporadic X .J3)
  mcl : Lem711Empty (fun X _ => NativeSporadic.IsSporadic X .McL)
  ly : Lem711Empty (fun X _ => NativeSporadic.IsSporadic X .Ly)
  l2 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Lem711Empty (fun X _ => LieModel X .PSL 2 p f)
  oddClassical : Lem711Empty fun X _ => IVK.OddClassicalSix X
  g2 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Lem711Empty (fun X _ => LieModel X .G2 0 p f)
  d4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Lem711Empty (fun X _ => LieModel X .trialityD4 0 p f)
  ree : ∀ f : ℕ, Lem711Empty (fun X _ => LieModel X .twistedG2 0 3 f)
  l28 : Lem711Empty (fun X _ => LieModel X .PSL 2 2 3)
  l216 : Lem711Empty (fun X _ => LieModel X .PSL 2 2 4)
  l34 : Lem711Empty (fun X _ => LieModel X .PSL 3 2 2)
  u34 : Lem711Empty (fun X _ => LieModel X .PSU 3 2 2)
  sz8 : Lem711Empty (fun X _ => LieModel X .twistedB2 0 2 3)

theorem lem711_false_of_leaves (hl : Lem711Leaves) {X : Type} [Group X] [Finite X]
    {L K : Subgroup X} {x y : X} (h : Lem711Cfg X L K x y) : False := by
  rcases h.ghList with ⟨n, h7, h11, he⟩ | hspor | ⟨p, f, hp, hf, hlie⟩
  · exact hl.alt n h7 h11 X L K x y h he
  · rcases hspor with hs | hs | hs | hs | hs | hs | hs | hs | hs
    · exact hl.m11 X L K x y h hs
    · exact hl.m12 X L K x y h hs
    · exact hl.m22 X L K x y h hs
    · exact hl.m23 X L K x y h hs
    · exact hl.j1 X L K x y h hs
    · exact hl.j2 X L K x y h hs
    · exact hl.j3 X L K x y h hs
    · exact hl.mcl X L K x y h hs
    · exact hl.ly X L K x y h hs
  · rcases hlie with ⟨hp2, hm | hm | hm | hm | hm | hm⟩ | ⟨hp2, hmod, hm⟩ | ⟨hp2, hmod, hm⟩ |
      ⟨hmod, hm⟩ | ⟨hmod, hm⟩ | hm | ⟨hp2, hm | hm | hm | hm | hm⟩
    · exact hl.l2 p f hp hp2 hf X L K x y h hm
    · exact hl.oddClassical X L K x y h (Or.inl ⟨p, f, hp, hp2, hf, Or.inl hm⟩)
    · exact hl.oddClassical X L K x y h (Or.inl ⟨p, f, hp, hp2, hf, Or.inr (Or.inl hm)⟩)
    · exact hl.oddClassical X L K x y h (Or.inl ⟨p, f, hp, hp2, hf, Or.inr (Or.inr (Or.inl hm))⟩)
    · exact hl.g2 p f hp hp2 hf X L K x y h hm
    · exact hl.d4 p f hp hp2 hf X L K x y h hm
    · exact hl.oddClassical X L K x y h
        (Or.inl ⟨p, f, hp, hp2, hf, Or.inr (Or.inr (Or.inr (Or.inl ⟨hmod, hm⟩)))⟩)
    · exact hl.oddClassical X L K x y h
        (Or.inl ⟨p, f, hp, hp2, hf, Or.inr (Or.inr (Or.inr (Or.inr ⟨hmod, hm⟩)))⟩)
    · exact hl.oddClassical X L K x y h (Or.inr ⟨p, f, hp, hf, Or.inl ⟨hmod, hm⟩⟩)
    · exact hl.oddClassical X L K x y h (Or.inr ⟨p, f, hp, hf, Or.inr ⟨hmod, hm⟩⟩)
    · exact hl.ree f X L K x y h hm
    · exact hl.l28 X L K x y h hm
    · exact hl.l216 X L K x y h hm
    · exact hl.l34 X L K x y h hm
    · exact hl.u34 X L K x y h hm
    · exact hl.sz8 X L K x y h hm

theorem b_st1_prop71_lemma711_simple_of_leaves (hl : Lem711Leaves) :
    B_st1_prop71_lemma711_simple :=
  b_st1_prop71_lemma711_simple_iff.2 fun _ _ _ _ _ _ _ h => lem711_false_of_leaves hl h

end CFSG.GH74.GLS
