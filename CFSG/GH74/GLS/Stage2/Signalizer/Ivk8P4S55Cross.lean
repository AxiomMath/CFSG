module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55Stmt

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped commutatorElement

section Types

variable (r : ℕ) (Y : Type) [Group Y]

@[expose] def FL2d : Prop := ∃ f : ℕ, 1 ≤ f ∧ LieModel Y .PSL 2 r f

@[expose] def FL3d : Prop := ∃ f : ℕ, 1 ≤ f ∧ LieModel Y .PSL 3 r f

@[expose] def FU3d : Prop := ∃ f : ℕ, 1 ≤ f ∧ LieModel Y .PSU 3 r f

@[expose] def FSp4d : Prop := ∃ f : ℕ, 1 ≤ f ∧ LieModel Y .PSp 2 r f

@[expose] def FG2d : Prop := ∃ f : ℕ, 1 ≤ f ∧ LieModel Y .G2 0 r f

@[expose] def FD4d : Prop := ∃ f : ℕ, 1 ≤ f ∧ LieModel Y .trialityD4 0 r f

@[expose] def FL4d : Prop := ∃ f : ℕ, 1 ≤ f ∧ r ^ f % 8 ≠ 1 ∧ LieModel Y .PSL 4 r f

@[expose] def FU4d : Prop := ∃ f : ℕ, 1 ≤ f ∧ r ^ f % 8 ≠ 7 ∧ LieModel Y .PSU 4 r f

@[expose] def FReed : Prop := r = 3 ∧ ∃ f : ℕ, 1 ≤ f ∧ LieModel Y .twistedG2 0 3 f

@[expose] def OddChev : Prop :=
  r.Prime ∧ r ≠ 2 ∧
    (FL2d r Y ∨ FL3d r Y ∨ FU3d r Y ∨ FSp4d r Y ∨ FG2d r Y ∨ FD4d r Y ∨ FL4d r Y ∨ FU4d r Y ∨
      FReed r Y)

end Types

@[expose] def Cross55 : Prop :=
  ∀ (p : ℕ) (Γ : Type) [Group Γ] [Finite Γ] (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    [Module.Finite (ZMod p) V] (ρ : Γ →* (V →ₗ[ZMod p] V)ˣ) (K : Subgroup Γ) (a : Γ)
    (P : Subgroup Γ), Mod55 p ρ K a P → ∀ r : ℕ, OddChev r (↥K ⧸ center ↥K) →
      r = p ∨ (p = 3 ∧ HasSL2Model ↥K (fun q => q = 5))

@[expose] def Sl2Five55 : Prop :=
  ∀ (k : Kind) (p : ℕ) (Γ : Type) [Group Γ] [Finite Γ] (V : Type) [AddCommGroup V]
    [Module (ZMod p) V] [Module.Finite (ZMod p) V] (ρ : Γ →* (V →ₗ[ZMod p] V)ˣ)
    (K : Subgroup Γ) (a : Γ) (P R : Subgroup Γ), Frame55 k p ρ K a P R → p = 3 →
      HasSL2Model ↥K (fun q => q = 5) → False

@[expose] def Def55 (Fd : ℕ → (Y : Type) → [Group Y] → Prop) : Prop :=
  ∀ (k : Kind) (p : ℕ) (Γ : Type) [Group Γ] [Finite Γ] (V : Type) [AddCommGroup V]
    [Module (ZMod p) V] [Module.Finite (ZMod p) V] (ρ : Γ →* (V →ₗ[ZMod p] V)ˣ)
    (K : Subgroup Γ) (a : Γ) (P R : Subgroup Γ),
    Frame55 k p ρ K a P R → Fd p (↥K ⧸ center ↥K) → Concl55 p K

@[expose] def Excl55 (F : (Y : Type) → [Group Y] → Prop) : Prop :=
  ∀ (k : Kind) (Y : Type) [Group Y], F Y → InvSecGroup k Y → False

theorem cell55_of_excl {F : (Y : Type) → [Group Y] → Prop} (h : Excl55 F) : Cell55 F :=
  fun k _ _ _ _ _ _ _ _ _ _ _ _ _ hf hF => (h k _ hF hf.r3).elim

theorem cell55_of_cross_def {F : (Y : Type) → [Group Y] → Prop}
    {Fd : ℕ → (Y : Type) → [Group Y] → Prop}
    (hF : ∀ (Y : Type) [Group Y], F Y → ∃ r : ℕ, OddChev r Y ∧ Fd r Y)
    (hX : Cross55) (hS : Sl2Five55) (hD : Def55 Fd) : Cell55 F := by
  intro k p Γ _ _ V _ _ _ ρ K a P R hf hFK
  obtain ⟨r, hr, hFd⟩ := hF _ hFK
  rcases hX p Γ V ρ K a P hf.toMod55 r hr with hrp | ⟨hp3, h5⟩
  · rw [hrp] at hFd
    exact hD k p Γ V ρ K a P R hf hFd
  · exact (hS k p Γ V ρ K a P R hf hp3 h5).elim

theorem link_l2 (Y : Type) [Group Y] (h : FL2 Y) : ∃ r : ℕ, OddChev r Y ∧ FL2d r Y := by
  obtain ⟨p, f, hp, hf, hp2, h⟩ := h
  exact ⟨p, ⟨hp, hp2, Or.inl ⟨f, hf, h⟩⟩, f, hf, h⟩

theorem link_l3 (Y : Type) [Group Y] (h : FL3 Y) : ∃ r : ℕ, OddChev r Y ∧ FL3d r Y := by
  obtain ⟨p, f, hp, hf, hp2, h⟩ := h
  exact ⟨p, ⟨hp, hp2, Or.inr (Or.inl ⟨f, hf, h⟩)⟩, f, hf, h⟩

theorem link_u3 (Y : Type) [Group Y] (h : FU3 Y) : ∃ r : ℕ, OddChev r Y ∧ FU3d r Y := by
  obtain ⟨p, f, hp, hf, hp2, h⟩ := h
  exact ⟨p, ⟨hp, hp2, Or.inr (Or.inr (Or.inl ⟨f, hf, h⟩))⟩, f, hf, h⟩

theorem link_sp4 (Y : Type) [Group Y] (h : FSp4 Y) : ∃ r : ℕ, OddChev r Y ∧ FSp4d r Y := by
  obtain ⟨p, f, hp, hf, hp2, h⟩ := h
  exact ⟨p, ⟨hp, hp2, Or.inr (Or.inr (Or.inr (Or.inl ⟨f, hf, h⟩)))⟩, f, hf, h⟩

theorem link_g2 (Y : Type) [Group Y] (h : FG2 Y) : ∃ r : ℕ, OddChev r Y ∧ FG2d r Y := by
  obtain ⟨p, f, hp, hf, hp2, h⟩ := h
  exact ⟨p, ⟨hp, hp2, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f, hf, h⟩))))⟩, f, hf, h⟩

theorem link_d4 (Y : Type) [Group Y] (h : FD4 Y) : ∃ r : ℕ, OddChev r Y ∧ FD4d r Y := by
  obtain ⟨p, f, hp, hf, hp2, h⟩ := h
  exact ⟨p, ⟨hp, hp2, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f, hf, h⟩)))))⟩, f, hf, h⟩

theorem link_l4 (Y : Type) [Group Y] (h : FL4 Y) : ∃ r : ℕ, OddChev r Y ∧ FL4d r Y := by
  obtain ⟨p, f, hp, hf, hp2, hq, h⟩ := h
  exact ⟨p, ⟨hp, hp2, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl ⟨f, hf, hq, h⟩))))))⟩, f, hf, hq, h⟩

theorem link_u4 (Y : Type) [Group Y] (h : FU4 Y) : ∃ r : ℕ, OddChev r Y ∧ FU4d r Y := by
  obtain ⟨p, f, hp, hf, hp2, hq, h⟩ := h
  exact ⟨p, ⟨hp, hp2, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl ⟨f, hf, hq, h⟩)))))))⟩, f, hf, hq, h⟩

theorem link_ree (Y : Type) [Group Y] (h : FRee Y) : ∃ r : ℕ, OddChev r Y ∧ FReed r Y := by
  obtain ⟨f, hf, h⟩ := h
  have hd : FReed 3 Y := ⟨rfl, f, hf, h⟩
  exact ⟨3, ⟨Nat.prime_three, by norm_num, by tauto⟩, hd⟩

structure Parts55 : Prop where
  cross : Cross55
  sl2five : Sl2Five55
  alt : Cell55 FAlt
  spor : Cell55 FSpor
  mcly : Cell55 FMcLy
  two : Cell55 FTwo
  l2 : Def55 FL2d
  l3 : Def55 FL3d
  u3 : Def55 FU3d
  sp4 : Def55 FSp4d
  g2 : Def55 FG2d
  d4 : Def55 FD4d
  l4 : Def55 FL4d
  u4 : Def55 FU4d
  ree : Def55 FReed
  l5 : Excl55 FL5
  u5 : Excl55 FU5

theorem cells55_of_parts (h : Parts55) : Cells55 where
  alt := h.alt
  spor := h.spor
  mcly := h.mcly
  two := h.two
  l2 := cell55_of_cross_def link_l2 h.cross h.sl2five h.l2
  l3 := cell55_of_cross_def link_l3 h.cross h.sl2five h.l3
  u3 := cell55_of_cross_def link_u3 h.cross h.sl2five h.u3
  sp4 := cell55_of_cross_def link_sp4 h.cross h.sl2five h.sp4
  g2 := cell55_of_cross_def link_g2 h.cross h.sl2five h.g2
  d4 := cell55_of_cross_def link_d4 h.cross h.sl2five h.d4
  l4 := cell55_of_cross_def link_l4 h.cross h.sl2five h.l4
  u4 := cell55_of_cross_def link_u4 h.cross h.sl2five h.u4
  l5 := cell55_of_excl h.l5
  u5 := cell55_of_excl h.u5
  ree := cell55_of_cross_def link_ree h.cross h.sl2five h.ree

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
