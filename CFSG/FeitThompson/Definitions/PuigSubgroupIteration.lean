module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Order.CompletePartialOrder

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

variable {X : Type*} [Group X] {Y : Type*} [Group Y]

def puigLambda (U : Subgroup X) : Subgroup X :=
  sSup {A : Subgroup X | IsMulCommutative A ∧ U ≤ Subgroup.normalizer (A : Set X)}

theorem puigLambda_eq_sSup (U : Subgroup X) :
    puigLambda U =
      sSup {A : Subgroup X | IsMulCommutative A ∧ U ≤ normalizer (A : Set X)} := (rfl)

theorem le_puigLambda {U A : Subgroup X} (hA : IsMulCommutative A)
    (hU : U ≤ normalizer (A : Set X)) : A ≤ puigLambda U :=
  le_sSup ⟨hA, hU⟩

theorem le_puigLambda_of_conj {U A : Subgroup X} (hA : IsMulCommutative A)
    (hU : ∀ u ∈ U, ∀ a ∈ A, u * a * u⁻¹ ∈ A) : A ≤ puigLambda U :=
  le_puigLambda hA fun u hu => mem_normalizer_iff.2 fun a =>
    ⟨hU u hu a, fun ha => by simpa [mul_assoc] using hU u⁻¹ (inv_mem hu) _ ha⟩

theorem puigLambda_le {U K : Subgroup X}
    (h : ∀ A : Subgroup X, IsMulCommutative A → U ≤ normalizer (A : Set X) → A ≤ K) :
    puigLambda U ≤ K :=
  sSup_le fun _ hA => h _ hA.1 hA.2

theorem puigLambda_antitone : Antitone (puigLambda (X := X)) := fun _ _ h =>
  puigLambda_le fun _ hA hV => le_puigLambda hA (h.trans hV)

theorem center_le_puigLambda (U : Subgroup X) : center X ≤ puigLambda U :=
  le_puigLambda inferInstance (by rw [normalizer_eq_top]; exact le_top)

theorem puigLambda_bot : puigLambda (⊥ : Subgroup X) = ⊤ :=
  (eq_top_iff' _).2 fun g =>
    le_puigLambda (A := zpowers g) inferInstance bot_le (mem_zpowers g)

theorem map_puigLambda_le (f : X ≃* Y) (U : Subgroup X) :
    (puigLambda U).map f.toMonoidHom ≤ puigLambda (U.map f.toMonoidHom) := by
  rw [map_le_iff_le_comap]
  refine puigLambda_le fun A _ hU => ?_
  rw [← map_le_iff_le_comap]
  refine le_puigLambda (map_isMulCommutative A f.toMonoidHom) ?_
  calc U.map f.toMonoidHom ≤ (normalizer (A : Set X)).map f.toMonoidHom := map_mono hU
    _ = normalizer ((A.map f.toMonoidHom : Subgroup Y) : Set Y) := map_equiv_normalizer_eq A f

theorem puigLambda_map (f : X ≃* Y) (U : Subgroup X) :
    (puigLambda U).map f.toMonoidHom = puigLambda (U.map f.toMonoidHom) := by
  refine le_antisymm (map_puigLambda_le f U) ?_
  have h := map_puigLambda_le f.symm (U.map f.toMonoidHom)
  have hU : (U.map f.toMonoidHom).map f.symm.toMonoidHom = U := by ext x; simp
  rw [hU] at h
  calc puigLambda (U.map f.toMonoidHom)
      = ((puigLambda (U.map f.toMonoidHom)).map f.symm.toMonoidHom).map f.toMonoidHom := by
        ext x; simp
    _ ≤ (puigLambda U).map f.toMonoidHom := map_mono h

instance puigLambda_characteristic (U : Subgroup X) [U.Characteristic] :
    (puigLambda U).Characteristic :=
  characteristic_iff_map_eq.2 fun ϕ => by
    rw [puigLambda_map ϕ U, characteristic_iff_map_eq.1 ‹_› ϕ]

def puigSeries (X : Type*) [Group X] : ℕ → Subgroup X
  | 0 => ⊥
  | n + 1 => puigLambda (puigSeries X n)

@[simp] theorem puigSeries_zero : puigSeries X 0 = ⊥ := (rfl)

@[simp] theorem puigSeries_succ (n : ℕ) :
    puigSeries X (n + 1) = puigLambda (puigSeries X n) := (rfl)

theorem puigSeries_one : puigSeries X 1 = ⊤ := by
  rw [puigSeries_succ, puigSeries_zero, puigLambda_bot]

instance puigSeries_characteristic (n : ℕ) : (puigSeries X n).Characteristic := by
  induction n with
  | zero => rw [puigSeries_zero]; infer_instance
  | succ n _ => rw [puigSeries_succ]; exact puigLambda_characteristic _

theorem center_le_puigSeries_succ (n : ℕ) : center X ≤ puigSeries X (n + 1) := by
  rw [puigSeries_succ]; exact center_le_puigLambda _

private theorem puigSeries_alternating (k n : ℕ) :
    (Even n → puigSeries X n ≤ puigSeries X (n + k)) ∧
      (Odd n → puigSeries X (n + k) ≤ puigSeries X n) := by
  induction n with
  | zero => exact ⟨fun _ => by simp, fun h => absurd h (by simp)⟩
  | succ n ih =>
    have hk : n + 1 + k = n + k + 1 := by omega
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have hn : Odd n := Nat.Even.sub_odd (by omega) h odd_one
      rw [hk, puigSeries_succ, puigSeries_succ]
      exact puigLambda_antitone (ih.2 hn)
    · have hn : Even n := Nat.Odd.sub_odd h odd_one
      rw [hk, puigSeries_succ, puigSeries_succ]
      exact puigLambda_antitone (ih.1 hn)

theorem puigSeries_le_add_of_even {n : ℕ} (hn : Even n) (k : ℕ) :
    puigSeries X n ≤ puigSeries X (n + k) := (puigSeries_alternating k n).1 hn

theorem puigSeries_add_le_of_odd {n : ℕ} (hn : Odd n) (k : ℕ) :
    puigSeries X (n + k) ≤ puigSeries X n := (puigSeries_alternating k n).2 hn

theorem puigSeries_even_monotone : Monotone fun n : ℕ => puigSeries X (2 * n) :=
  monotone_nat_of_le_succ fun n => by
    have := puigSeries_le_add_of_even (X := X) (even_two_mul n) 2
    simpa [Nat.mul_succ] using this

theorem puigSeries_odd_antitone : Antitone fun n : ℕ => puigSeries X (2 * n + 1) :=
  antitone_nat_of_succ_le fun n => by
    have := puigSeries_add_le_of_odd (X := X) (n := 2 * n + 1) ⟨n, by ring⟩ 2
    simpa [Nat.mul_succ, show 2 * n + 1 + 2 = 2 * n + 2 + 1 by ring] using this

theorem puigSeries_even_le_odd (m n : ℕ) : puigSeries X (2 * m) ≤ puigSeries X (2 * n + 1) :=
  calc puigSeries X (2 * m) ≤ puigSeries X (2 * max m n) :=
        puigSeries_even_monotone (le_max_left m n)
    _ ≤ puigSeries X (2 * max m n + 1) := puigSeries_le_add_of_even (even_two_mul _) 1
    _ ≤ puigSeries X (2 * n + 1) := puigSeries_odd_antitone (le_max_right m n)

def puigUpper (X : Type*) [Group X] : Subgroup X := ⨅ n : ℕ, puigSeries X (2 * n + 1)

def puigLower (X : Type*) [Group X] : Subgroup X := ⨆ n : ℕ, puigSeries X (2 * n)

theorem puigUpper_eq_iInf : puigUpper X = ⨅ n : ℕ, puigSeries X (2 * n + 1) := (rfl)

theorem puigLower_eq_iSup : puigLower X = ⨆ n : ℕ, puigSeries X (2 * n) := (rfl)

theorem puigUpper_le (n : ℕ) : puigUpper X ≤ puigSeries X (2 * n + 1) := by
  rw [puigUpper_eq_iInf]
  exact iInf_le (fun n : ℕ => puigSeries X (2 * n + 1)) n

theorem le_puigLower (n : ℕ) : puigSeries X (2 * n) ≤ puigLower X := by
  rw [puigLower_eq_iSup]
  exact le_iSup (fun n : ℕ => puigSeries X (2 * n)) n

theorem puigLower_le_puigUpper : puigLower X ≤ puigUpper X := by
  rw [puigLower_eq_iSup, puigUpper_eq_iInf]
  exact iSup_le fun m => le_iInf fun n => puigSeries_even_le_odd m n

instance puigUpper_characteristic : (puigUpper X).Characteristic := by
  rw [puigUpper_eq_iInf]; infer_instance

instance puigLower_characteristic : (puigLower X).Characteristic := by
  rw [puigLower_eq_iSup]; infer_instance

def puigSubgroup (X : Type*) [Group X] : Subgroup X := puigUpper X

theorem puigSubgroup_eq_puigUpper : puigSubgroup X = puigUpper X := (rfl)

theorem puigSubgroup_le (n : ℕ) : puigSubgroup X ≤ puigSeries X (2 * n + 1) := puigUpper_le n

instance puigSubgroup_characteristic : (puigSubgroup X).Characteristic := by
  rw [puigSubgroup_eq_puigUpper]; infer_instance

theorem center_le_puigSubgroup : center X ≤ puigSubgroup X := by
  rw [puigSubgroup_eq_puigUpper, puigUpper_eq_iInf]
  exact le_iInf fun n => center_le_puigSeries_succ _

theorem puigSubgroup_ne_bot_of_center_ne_bot (h : center X ≠ ⊥) : puigSubgroup X ≠ ⊥ :=
  fun hb => h (le_bot_iff.1 (hb ▸ center_le_puigSubgroup))

theorem puigSubgroup_ne_bot {p : ℕ} [Fact p.Prime] [Nontrivial X] [Finite X]
    (hX : IsPGroup p X) : puigSubgroup X ≠ ⊥ :=
  puigSubgroup_ne_bot_of_center_ne_bot hX.bot_lt_center.ne'

def puigCenter (X : Type*) [Group X] : Subgroup X :=
  puigSubgroup X ⊓ centralizer (puigSubgroup X : Set X)

theorem puigCenter_eq_inf_centralizer :
    puigCenter X = puigSubgroup X ⊓ centralizer (puigSubgroup X : Set X) := (rfl)

theorem puigCenter_le_puigSubgroup : puigCenter X ≤ puigSubgroup X := by
  rw [puigCenter_eq_inf_centralizer]; exact inf_le_left

theorem puigCenter_eq_map_center :
    puigCenter X = (center (puigSubgroup X)).map (puigSubgroup X).subtype := by
  ext x
  simp only [puigCenter_eq_inf_centralizer, mem_map, mem_inf, mem_center_iff, mem_centralizer_iff,
    coe_subtype, Subtype.exists]
  constructor
  · rintro ⟨hx, hc⟩
    exact ⟨x, hx, fun g => Subtype.ext (hc g g.2), rfl⟩
  · rintro ⟨y, hy, h, rfl⟩
    exact ⟨hy, fun g hg => by simpa using congrArg Subtype.val (h ⟨g, hg⟩)⟩

instance puigCenter_isMulCommutative : IsMulCommutative (puigCenter X) := by
  rw [puigCenter_eq_inf_centralizer]
  refine IsMulCommutative.of_comm fun a b => Subtype.ext ?_
  push_cast
  exact (mem_centralizer_iff.1 (mem_inf.1 b.2).2) a (mem_inf.1 a.2).1

instance puigCenter_characteristic : (puigCenter X).Characteristic := by
  rw [puigCenter_eq_inf_centralizer]; infer_instance

end CFSG.FeitThompson

end
