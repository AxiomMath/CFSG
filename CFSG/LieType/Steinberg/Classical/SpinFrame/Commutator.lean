module

public import CFSG.LieType.Steinberg.Classical.SpinFrame.Basic

public noncomputable section

namespace CFSG.LieType.Steinberg.SpinFrame

open CFSG.LieType.Universal.Spin CliffordAlgebra QuadraticMap
open scoped commutatorElement

variable {n : ℕ}

@[ext] structure ChainRep (n : ℕ) where
  i : Fin n
  j : Fin n
  k : Fin n
  s : Bool
  t : Bool
  u : Bool

namespace ChainRep

variable (p : ChainRep n)

@[expose] def IsRep (a b : Fin n → ℤ) : Prop :=
  p.i ≠ p.j ∧ p.j ≠ p.k ∧ p.i ≠ p.k ∧
    a = Pi.single p.i (boolSign p.s) + Pi.single p.j (boolSign p.t) ∧
    b = Pi.single p.j (boolSign (!p.t)) + Pi.single p.k (boolSign p.u)

@[expose] def coeff : ℤ :=
  repSign p.i p.k p.s p.u * repSign p.i p.j p.s p.t * repSign p.j p.k (!p.t) p.u

theorem coeff_eq_one_or_eq_neg_one : p.coeff = 1 ∨ p.coeff = -1 := by
  unfold coeff
  rcases repSign_eq_one_or_eq_neg_one p.i p.k p.s p.u with h1 | h1 <;>
    rcases repSign_eq_one_or_eq_neg_one p.i p.j p.s p.t with h2 | h2 <;>
    rcases repSign_eq_one_or_eq_neg_one p.j p.k (!p.t) p.u with h3 | h3 <;>
    rw [h1, h2, h3] <;> simp

variable {p}

theorem IsRep.add_eq {a b : Fin n → ℤ} (hp : p.IsRep a b) :
    a + b = Pi.single p.i (boolSign p.s) + Pi.single p.k (boolSign p.u) := by
  obtain ⟨-, -, -, rfl, rfl⟩ := hp
  have h : (Pi.single p.j (boolSign p.t) + Pi.single p.j (boolSign (!p.t)) : Fin n → ℤ) = 0 := by
    rw [← Pi.single_add, boolSign_add_boolSign_not, Pi.single_zero]
  calc (Pi.single p.i (boolSign p.s) + Pi.single p.j (boolSign p.t) +
        (Pi.single p.j (boolSign (!p.t)) + Pi.single p.k (boolSign p.u)) : Fin n → ℤ)
      = Pi.single p.i (boolSign p.s) +
          (Pi.single p.j (boolSign p.t) + Pi.single p.j (boolSign (!p.t))) +
          Pi.single p.k (boolSign p.u) := by abel
    _ = _ := by rw [h, add_zero]

theorem IsRep.isLong_add {a b : Fin n → ℤ} (hp : p.IsRep a b) : IsLong (a + b) := by
  rw [hp.add_eq]
  exact isLong_single_add_single hp.2.2.1 _ _

theorem IsRep.unique {q : ChainRep n} {a b : Fin n → ℤ} (hp : p.IsRep a b) (hq : q.IsRep a b) :
    p = q := by
  obtain ⟨hij, hjk, hik, ha, hb⟩ := hp
  obtain ⟨hij', hjk', hik', ha', hb'⟩ := hq
  have h1 := (single_add_single_eq_iff hij hij' (boolSign_ne_zero p.s)
    (boolSign_ne_zero p.t)).mp (ha.symm.trans ha')
  have h2 := (single_add_single_eq_iff hjk hjk' (boolSign_ne_zero (!p.t))
    (boolSign_ne_zero p.u)).mp (hb.symm.trans hb')
  rcases h1 with ⟨e1, e2, e3, e4⟩ | ⟨e1, -, e3, -⟩ <;>
    rcases h2 with ⟨f1, -, f3, f4⟩ | ⟨f1, -, f3, -⟩
  · exact ChainRep.ext e1 e3 f3 (boolSign_injective e2) (boolSign_injective e4)
      (boolSign_injective f4)
  · exact absurd (e3.trans f3.symm) hjk
  · exact absurd (e3.symm.trans f1) hij'
  · exact absurd (e3.symm.trans f1) hik'

end ChainRep

open _root_.Classical in
@[expose] def chainSign (a b : Fin n → ℤ) : ℤ :=
  if h : ∃ p : ChainRep n, p.IsRep a b then h.choose.coeff else 1

theorem chainSign_eq {p : ChainRep n} {a b : Fin n → ℤ} (hp : p.IsRep a b) :
    chainSign a b = p.coeff := by
  have h : ∃ p : ChainRep n, p.IsRep a b := ⟨p, hp⟩
  rw [chainSign, dite_eq_left h, h.choose_spec.unique hp]

theorem chainSign_eq_one_or_eq_neg_one (a b : Fin n → ℤ) :
    chainSign a b = 1 ∨ chainSign a b = -1 := by
  unfold chainSign
  split_ifs with h
  · exact h.choose.coeff_eq_one_or_eq_neg_one
  · exact Or.inl rfl

theorem not_isLong_of_apply_ne_zero {e : Fin n → ℤ} {x y z : Fin n} (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) (hx : e x ≠ 0) (hy : e y ≠ 0) (hz : e z ≠ 0) : ¬IsLong e := by
  rintro ⟨i, j, -, s, t, rfl⟩
  rcases eq_or_eq_of_single_add_single_apply_ne_zero hx with rfl | rfl <;>
    rcases eq_or_eq_of_single_add_single_apply_ne_zero hy with rfl | rfl <;>
    rcases eq_or_eq_of_single_add_single_apply_ne_zero hz with rfl | rfl <;>
    simp_all

theorem not_isLong_of_apply_eq_add_self {e : Fin n → ℤ} {m : Fin n} {s : Bool}
    (h : e m = boolSign s + boolSign s) : ¬IsLong e := fun he => by
  rcases he.apply_mem m with h' | h' | h' <;> rw [h'] at h <;> cases s <;> simp [boolSign] at h

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  (F : HypFrame Q n)

theorem commutator_rootElt_of_isRep {p : ChainRep n} {a b : Fin n → ℤ} (hp : p.IsRep a b)
    (c d : K) :
    ⁅rootElt F a c, rootElt F b d⁆ = rootElt F (a + b) ((chainSign a b : K) * c * d) := by
  obtain ⟨hij, hjk, hik, ha, hb⟩ := hp
  rw [rootElt_eq F hij ha, rootElt_eq F hjk hb, F.commutator_longRoot_longRoot hij hjk hik,
    rootElt_eq F hik (ChainRep.IsRep.add_eq ⟨hij, hjk, hik, ha, hb⟩),
    chainSign_eq ⟨hij, hjk, hik, ha, hb⟩, ChainRep.coeff]
  congr 2
  push_cast
  have h := repSign_cast_mul_self (K := K) p.i p.k p.s p.u
  linear_combination (-(repSign p.i p.j p.s p.t * c * (repSign p.j p.k (!p.t) p.u * d)) : K) * h

theorem exists_isRep_or_commute {a b : Fin n → ℤ} (ha : IsLong a) (hb : IsLong b)
    (hab : a + b ≠ 0) :
    (∃ p : ChainRep n, p.IsRep a b) ∨
      (¬IsLong (a + b) ∧ ∀ c d : K, Commute (rootElt F a c) (rootElt F b d)) := by
  by_cases hov : ∃ m, a m ≠ 0 ∧ b m ≠ 0
  · obtain ⟨m, ham, hbm⟩ := hov
    obtain ⟨j, hmj, s, t, ha'⟩ := ha.exists_eq_of_apply_ne_zero ham
    obtain ⟨l, hml, u, v, hb'⟩ := hb.exists_eq_of_apply_ne_zero hbm
    have hsum : ∀ x, (a + b) x = a x + b x := fun x => rfl
    by_cases hsu : u = s
    · subst hsu
      right
      refine ⟨not_isLong_of_apply_eq_add_self (m := m) (s := u) ?_, fun c d => ?_⟩
      · rw [hsum, ha', hb', single_add_single_apply_left hmj, single_add_single_apply_left hml]
      · rw [rootElt_eq F hmj ha', rootElt_eq F hml hb']
        exact F.commute_longRoot_longRoot_left hmj hml u t v _ _
    · have hu : u = !s := by cases u <;> cases s <;> simp_all
      subst hu
      by_cases hjl : j = l
      · subst hjl
        by_cases htv : v = t
        · subst htv
          right
          refine ⟨not_isLong_of_apply_eq_add_self (m := j) (s := v) ?_, fun c d => ?_⟩
          · rw [hsum, ha', hb', single_add_single_apply_right hmj,
              single_add_single_apply_right hml]
          · rw [rootElt_eq F hmj ha', rootElt_eq F hml hb']
            exact F.commute_longRoot_longRoot_right hmj hml s v (!s) _ _
        · have hv : v = !t := by cases v <;> cases t <;> simp_all
          subst hv
          exfalso
          apply hab
          rw [ha', hb']
          calc (Pi.single m (boolSign s) + Pi.single j (boolSign t) +
                (Pi.single m (boolSign (!s)) + Pi.single j (boolSign (!t))) : Fin n → ℤ)
              = Pi.single m (boolSign s + boolSign (!s)) +
                  Pi.single j (boolSign t + boolSign (!t)) := by
                rw [Pi.single_add, Pi.single_add]
                abel
            _ = 0 := by
                rw [boolSign_add_boolSign_not, boolSign_add_boolSign_not, Pi.single_zero,
                  Pi.single_zero, add_zero]
      · left
        refine ⟨⟨j, m, l, t, s, v⟩, Ne.symm hmj, hml, hjl, ?_, hb'⟩
        rw [ha', add_comm]
  · push Not at hov
    right
    obtain ⟨i, j, hij, s, t, ha'⟩ := ha
    obtain ⟨k, l, hkl, u, v, hb'⟩ := hb
    have hai : a i ≠ 0 := by rw [ha', single_add_single_apply_left hij]; exact boolSign_ne_zero s
    have haj : a j ≠ 0 := by rw [ha', single_add_single_apply_right hij]; exact boolSign_ne_zero t
    have hbk : b k ≠ 0 := by rw [hb', single_add_single_apply_left hkl]; exact boolSign_ne_zero u
    have hbl : b l ≠ 0 := by rw [hb', single_add_single_apply_right hkl]; exact boolSign_ne_zero v
    have hik : i ≠ k := fun h => hbk (h ▸ hov i hai)
    have hil : i ≠ l := fun h => hbl (h ▸ hov i hai)
    have hjk : j ≠ k := fun h => hbk (h ▸ hov j haj)
    have hjl : j ≠ l := fun h => hbl (h ▸ hov j haj)
    have hbi : b i = 0 := hov i hai
    have hbj : b j = 0 := hov j haj
    have hak : a k = 0 := by
      by_contra h
      exact hbk (hov k h)
    refine ⟨not_isLong_of_apply_ne_zero hij hik hjk ?_ ?_ ?_, fun c d => ?_⟩
    · change a i + b i ≠ 0
      rw [hbi, add_zero]
      exact hai
    · change a j + b j ≠ 0
      rw [hbj, add_zero]
      exact haj
    · change a k + b k ≠ 0
      rw [hak, zero_add]
      exact hbk
    · rw [rootElt_eq F hij ha', rootElt_eq F hkl hb']
      exact F.commute_longRoot_longRoot_of_disjoint hij hkl hik hil hjk hjl s t u v _ _

theorem commutator_rootElt {a b : Fin n → ℤ} (ha : IsLong a) (hb : IsLong b) (hab : a + b ≠ 0)
    (hl : IsLong (a + b)) (c d : K) :
    ⁅rootElt F a c, rootElt F b d⁆ = rootElt F (a + b) ((chainSign a b : K) * c * d) := by
  rcases exists_isRep_or_commute F ha hb hab with ⟨p, hp⟩ | ⟨h, -⟩
  · exact commutator_rootElt_of_isRep F hp c d
  · exact absurd hl h

theorem commute_rootElt {a b : Fin n → ℤ} (ha : IsLong a) (hb : IsLong b) (hab : a + b ≠ 0)
    (hl : ¬IsLong (a + b)) (c d : K) : Commute (rootElt F a c) (rootElt F b d) := by
  rcases exists_isRep_or_commute F ha hb hab with ⟨p, hp⟩ | ⟨-, h⟩
  · exact absurd hp.isLong_add hl
  · exact h c d

end CFSG.LieType.Steinberg.SpinFrame
