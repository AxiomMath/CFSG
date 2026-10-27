module

public import CFSG.LieType.SpecialLinear.CurtisDatum

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.Quasithin.SmithCurtis
open CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw

noncomputable section

theorem exists_ne_one_of_not_mem_isCoverType {F : Type} [Field F] [Finite F] {p : ℕ}
    [Fact p.Prime] [CharP F p] {k : Type} [Field k] [CharP k p] {n : ℕ} {V : Type}
    [AddCommGroup V] [Module k V]
    {ρ : Representation k (SpecialLinearGroup (Fin (n + 1)) F) V} {y : V}
    {χ : SpecialLinearGroup (Fin (n + 1)) F → k} {J : Finset (Fin n)}
    (ht : IsCoverType (rankOne n F p) ρ y χ J) {s : Fin n} (hs : s ∉ J) :
    ∃ g, ρ g ≠ 1 := by
  by_contra hρ
  push Not at hρ
  apply hs
  rw [ht.2.2.2 s]
  have : Fintype F := Fintype.ofFinite F
  constructor
  · intro u
    have hchar := ht.2.2.1 ((rankOne n F p).hh s u) ((rankOne n F p).hh_mem s u)
    have hfix : ρ ((rankOne n F p).hh s u) y = y := by
      rw [hρ, Module.End.one_apply]
    rw [hfix] at hchar
    have hsub : (χ ((rankOne n F p).hh s u) - 1) • y = 0 := by
      rw [sub_smul, one_smul, ← hchar, sub_self]
    rcases smul_eq_zero.mp hsub with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h ht.2.1
  · have hterm : ∀ c : F,
        ρ ((rankOne n F p).x s c * (coverId n F p).nhat s) y = y := by
      intro c
      rw [hρ, Module.End.one_apply]
    rw [(rankOne n F p).heckeT_datum (C := coverId n F p) ρ s y]
    rw [Finset.sum_congr rfl fun c _ => hterm c, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul k]
    have hcard : (Fintype.card F : k) = 0 := by
      obtain ⟨m, -, hm⟩ := FiniteField.card F p
      rw [hm, Nat.cast_pow, CharP.cast_eq_zero, zero_pow m.ne_zero]
    rw [hcard, zero_smul]

theorem exists_ne_one_of_extendScalars {E k G X : Type*} [Field E] [Field k] [Algebra E k]
    [Group G] [AddCommGroup X] [Module E X] (σ : Representation E G X)
    (h : ∃ g, CFSG.Theory.Representation.extendScalars k σ g ≠ 1) :
    ∃ g, σ g ≠ 1 := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g, fun h1 => hg ?_⟩
  rw [CFSG.Theory.Representation.extendScalars_apply, h1, LinearMap.baseChange_one]

end

end CFSG.LieType.SpecialLinear
