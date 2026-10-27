module

public import CFSG.GH74.Generic.BProg.B2.Defs

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

@[expose] def PuL5 (H : Type) [Group H] : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
    ((p ^ f % 4 = 3 ∧ LieModel H .PSL 5 p f) ∨ (p ^ f % 4 = 1 ∧ LieModel H .PSU 5 p f))

@[expose] def PuL4 (H : Type) [Group H] : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 3 < p ^ f ∧
    ((p ^ f % 8 ≠ 1 ∧ LieModel H .PSL 4 p f) ∨ (p ^ f % 8 ≠ 7 ∧ LieModel H .PSU 4 p f))

@[expose] def PuL3sq (H : Type) [Group H] : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ LieModel H .PSL 3 p (2 * f)

@[expose] def PuG2 (H : Type) [Group H] : Prop :=
  ∃ f : ℕ, 2 ≤ f ∧ LieModel H .G2 0 3 f

@[expose] def PuTarget (H : Type) [Group H] : Prop :=
  PuL5 H ∨ PuL4 H ∨ PuL3sq H ∨ PuG2 H

@[expose] def PumpupTableU : Prop :=
  ∀ (N : Type) [Group N] [Finite N] (H : Subgroup N) (t : N) (L : Subgroup N),
    ShapeInCent H t L → GHList ↥H → PuTarget ↥H

@[expose] def PumpupEmpty (P : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (N : Type) [Group N] [Finite N] (H : Subgroup N) (t : N) (L : Subgroup N),
    ShapeInCent H t L → P ↥H → False

@[expose] def PumpupEmptyIn (P : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (N : Type) [Group N] [Finite N] (H : Subgroup N) (t : N) (L : Subgroup N),
    ShapeInCent H t L → t ∈ H → P ↥H → False

@[expose] def PumpupEmptyOut (P : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (N : Type) [Group N] [Finite N] (H : Subgroup N) (t : N) (L : Subgroup N),
    ShapeInCent H t L → t ∉ H → P ↥H → False

theorem PumpupEmpty.of_in_out {P : ∀ (X : Type) [Group X], Prop} (hi : PumpupEmptyIn P)
    (ho : PumpupEmptyOut P) : PumpupEmpty P := by
  intro N _ _ H t L hs hP
  by_cases ht : t ∈ H
  · exact hi N H t L hs ht hP
  · exact ho N H t L hs ht hP

structure PumpupLeaves : Prop where
  alt : ∀ n : ℕ, 7 ≤ n → n ≤ 11 →
    PumpupEmpty (fun X _ => Nonempty (X ≃* alternatingGroup (Fin n)))
  m11 : PumpupEmpty (fun X _ => NativeSporadic.IsSporadic X .M11)
  m12 : PumpupEmpty (fun X _ => NativeSporadic.IsSporadic X .M12)
  m22 : PumpupEmpty (fun X _ => NativeSporadic.IsSporadic X .M22)
  m23 : PumpupEmpty (fun X _ => NativeSporadic.IsSporadic X .M23)
  j1 : PumpupEmpty (fun X _ => NativeSporadic.IsSporadic X .J1)
  j2 : PumpupEmpty (fun X _ => NativeSporadic.IsSporadic X .J2)
  j3 : PumpupEmpty (fun X _ => NativeSporadic.IsSporadic X .J3)
  mcl : PumpupEmpty (fun X _ => NativeSporadic.IsSporadic X .McL)
  ly : PumpupEmpty (fun X _ => NativeSporadic.IsSporadic X .Ly)
  l2 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → PumpupEmpty (fun X _ => LieModel X .PSL 2 p f)
  l3 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Odd f → PumpupEmpty (fun X _ => LieModel X .PSL 3 p f)
  u3 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → PumpupEmpty (fun X _ => LieModel X .PSU 3 p f)
  sp4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → PumpupEmpty (fun X _ => LieModel X .PSp 2 p f)
  g2 : ∀ p f : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → 1 ≤ f →
    PumpupEmpty (fun X _ => LieModel X .G2 0 p f)
  g2three : PumpupEmpty (fun X _ => LieModel X .G2 0 3 1)
  d4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    PumpupEmpty (fun X _ => LieModel X .trialityD4 0 p f)
  l4three : PumpupEmpty (fun X _ => LieModel X .PSL 4 3 1)
  u4three : PumpupEmpty (fun X _ => LieModel X .PSU 4 3 1)
  ree : ∀ f : ℕ, PumpupEmpty (fun X _ => LieModel X .twistedG2 0 3 f)
  l28 : PumpupEmpty (fun X _ => LieModel X .PSL 2 2 3)
  l216 : PumpupEmpty (fun X _ => LieModel X .PSL 2 2 4)
  l34 : PumpupEmpty (fun X _ => LieModel X .PSL 3 2 2)
  u34 : PumpupEmpty (fun X _ => LieModel X .PSU 3 2 2)
  sz8 : PumpupEmpty (fun X _ => LieModel X .twistedB2 0 2 3)

namespace PumpupTableAux

theorem ne_two_of_pow_mod_four {p f : ℕ} (hf : 1 ≤ f) (h : p ^ f % 4 = 3 ∨ p ^ f % 4 = 1) :
    p ≠ 2 := by
  rintro rfl
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rw [pow_succ] at h
  omega

theorem eq_three_of_pow_le_three {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (h : p ^ f ≤ 3) : p = 3 ∧ f = 1 := by
  have h2 := hp.two_le
  have hp3 : p ≤ p ^ f := Nat.le_self_pow (by omega) p
  have hp3' : p = 3 := by omega
  subst hp3'
  refine ⟨rfl, ?_⟩
  by_contra hne
  have : 3 ^ 2 ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

end PumpupTableAux

theorem pumpupTableU_of_leaves (hl : PumpupLeaves) : PumpupTableU := by
  intro N _ _ H t L hs hGH
  rcases hGH with ⟨n, h7, h11, he⟩ | hspor | ⟨p, f, hp, hf, hrow⟩
  · exact (hl.alt n h7 h11 N H t L hs he).elim
  · rcases hspor with h | h | h | h | h | h | h | h | h
    · exact (hl.m11 N H t L hs h).elim
    · exact (hl.m12 N H t L hs h).elim
    · exact (hl.m22 N H t L hs h).elim
    · exact (hl.m23 N H t L hs h).elim
    · exact (hl.j1 N H t L hs h).elim
    · exact (hl.j2 N H t L hs h).elim
    · exact (hl.j3 N H t L hs h).elim
    · exact (hl.mcl N H t L hs h).elim
    · exact (hl.ly N H t L hs h).elim
  · rcases hrow with ⟨hp2, hm | hm | hm | hm | hm | hm⟩ | ⟨hp2, hmod, hm⟩ | ⟨hp2, hmod, hm⟩ |
      ⟨hmod, hm⟩ | ⟨hmod, hm⟩ | hm | ⟨hp2, hm | hm | hm | hm | hm⟩
    · exact (hl.l2 p f hp hp2 hf N H t L hs hm).elim
    · by_cases hev : Even f
      · obtain ⟨g, hg⟩ := hev
        refine Or.inr (Or.inr (Or.inl ⟨p, g, hp, hp2, by omega, ?_⟩))
        have : 2 * g = f := by omega
        rwa [this]
      · exact (hl.l3 p f hp hp2 hf (Nat.not_even_iff_odd.mp hev) N H t L hs hm).elim
    · exact (hl.u3 p f hp hp2 hf N H t L hs hm).elim
    · exact (hl.sp4 p f hp hp2 hf N H t L hs hm).elim
    · by_cases h3 : p = 3 ∧ 2 ≤ f
      · obtain ⟨rfl, h2⟩ := h3
        exact Or.inr (Or.inr (Or.inr ⟨f, h2, hm⟩))
      · by_cases hp3 : p = 3
        · subst hp3
          have hf1 : f = 1 := by omega
          subst hf1
          exact (hl.g2three N H t L hs hm).elim
        · exact (hl.g2 p f hp hp2 hp3 hf N H t L hs hm).elim
    · exact (hl.d4 p f hp hp2 hf N H t L hs hm).elim
    · by_cases h3 : 3 < p ^ f
      · exact Or.inr (Or.inl ⟨p, f, hp, hp2, hf, h3, Or.inl ⟨hmod, hm⟩⟩)
      · obtain ⟨rfl, rfl⟩ := PumpupTableAux.eq_three_of_pow_le_three hp hp2 hf (by omega)
        exact (hl.l4three N H t L hs hm).elim
    · by_cases h3 : 3 < p ^ f
      · exact Or.inr (Or.inl ⟨p, f, hp, hp2, hf, h3, Or.inr ⟨hmod, hm⟩⟩)
      · obtain ⟨rfl, rfl⟩ := PumpupTableAux.eq_three_of_pow_le_three hp hp2 hf (by omega)
        exact (hl.u4three N H t L hs hm).elim
    · exact Or.inl ⟨p, f, hp, PumpupTableAux.ne_two_of_pow_mod_four hf (Or.inl hmod), hf,
        Or.inl ⟨hmod, hm⟩⟩
    · exact Or.inl ⟨p, f, hp, PumpupTableAux.ne_two_of_pow_mod_four hf (Or.inr hmod), hf,
        Or.inr ⟨hmod, hm⟩⟩
    · exact (hl.ree f N H t L hs hm).elim
    · exact (hl.l28 N H t L hs hm).elim
    · exact (hl.l216 N H t L hs hm).elim
    · exact (hl.l34 N H t L hs hm).elim
    · exact (hl.u34 N H t L hs hm).elim
    · exact (hl.sz8 N H t L hs hm).elim

end CFSG.GH74.Generic.BProg.B2
