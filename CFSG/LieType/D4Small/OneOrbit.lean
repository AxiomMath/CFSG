module

public import CFSG.LieType.D4Small.WeightBasic
public import CFSG.LieType.D4Small.Orbits
public import CFSG.RepresentationTheory.SL2NatSum.ChooseTwo
public import Mathlib.RepresentationTheory.Invariants

public section

namespace CFSG.LieType.D4Small.D4Datum

open Finset

attribute [local instance] Fintype.ofFinite Classical.propDecidable

variable {G : Type*} [Group G] {K : Type*} [Field K] [Finite K] [CharP K 2]
  {X : Type*} [AddCommGroup X] [Module K X] [FiniteDimensional K X]
  (D : D4Datum G K) (ρ : Representation K G X)

theorem odd_natCard_units (K : Type*) [Field K] [Finite K] [CharP K 2] :
    Odd (Nat.card Kˣ) := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hq⟩ := FiniteField.card K 2
  rw [Nat.card_units, Nat.card_eq_fintype_card, hq]
  obtain ⟨j, hj⟩ : ∃ j : ℕ, (n : ℕ) = j + 1 :=
    ⟨(n : ℕ) - 1, by have := n.pos; omega⟩
  rw [hj, pow_succ]
  have hp : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  exact ⟨2 ^ j - 1, by omega⟩

theorem three_le_natCard_units {K : Type*} [Field K] [Finite K] (hK : 4 ≤ Nat.card K) :
    3 ≤ Nat.card Kˣ := by
  rw [Nat.card_units]
  omega

private theorem natCast_natCard_units_ne_zero {k : ℕ} (hk0 : 0 < k)
    (hkN : k < Nat.card Kˣ) : ((k : ℕ) : ZMod (Nat.card Kˣ)) ≠ 0 := by
  rw [ne_eq, ZMod.natCast_eq_zero_iff]
  intro hdvd
  have := Nat.le_of_dvd hk0 hdvd
  omega

private theorem two_pow_lt_natCard_units (hK : 4 ≤ Nat.card K) {l : ℕ}
    (hl : 2 ^ l ≤ Nat.card Kˣ) : 2 ^ l < Nat.card Kˣ := by
  have hN := odd_natCard_units K
  have h3 := three_le_natCard_units hK
  rcases Nat.eq_or_lt_of_le hl with h | h
  · exfalso
    rcases hN with ⟨r, hr⟩
    rw [← h] at hr
    cases l with
    | zero => omega
    | succ j =>
        rw [pow_succ, mul_comm] at hr
        omega
  · exact h

@[expose] noncomputable def wts (D : D4Datum G K) (ρ : Representation K G X) :
    Finset (Fin 4 → ZMod (Nat.card Kˣ)) :=
  Finset.univ.filter fun a => D.wtSpace ρ a ≠ ⊥

theorem mem_wts {a : Fin 4 → ZMod (Nat.card Kˣ)} :
    a ∈ wts D ρ ↔ D.wtSpace ρ a ≠ ⊥ := by
  rw [wts]
  simp

theorem closed_wts : Closed (wts D ρ) := by
  intro β hβ a ha
  rw [mem_wts] at ha ⊢
  intro hbot
  have h0 : Module.finrank K (D.wtSpace ρ a) = 0 := by
    rw [← finrank_wtSpace_reflW D ρ β hβ a, hbot]
    simp
  exact ha (Submodule.finrank_eq_zero.mp h0)

theorem card_wts_le : (wts D ρ).card ≤ Module.finrank K X := by
  rw [finrank_eq_sum_finrank_wtSpace D ρ]
  calc (wts D ρ).card = ∑ a ∈ wts D ρ, 1 := by simp
    _ ≤ ∑ a ∈ wts D ρ, Module.finrank K (D.wtSpace ρ a) := by
        refine Finset.sum_le_sum fun a ha => ?_
        have hne : D.wtSpace ρ a ≠ ⊥ := (mem_wts D ρ).mp ha
        rw [Nat.one_le_iff_ne_zero]
        intro h0
        exact hne (Submodule.finrank_eq_zero.mp h0)
    _ ≤ ∑ a, Module.finrank K (D.wtSpace ρ a) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_
        intro a _ _
        exact Nat.zero_le _

theorem wts_nonempty (hnt : ∃ g : G, ρ g ≠ 1) : (wts D ρ).Nonempty := by
  by_contra hne
  have hbot : ∀ a, D.wtSpace ρ a = ⊥ := by
    intro a
    by_contra h
    exact hne ⟨a, (mem_wts D ρ).mpr h⟩
  have htopbot : (⊤ : Submodule K X) = ⊥ := by
    rw [← iSup_wtSpace D ρ]
    exact iSup_eq_bot.mpr hbot
  haveI : Subsingleton X := by
    refine ⟨fun x y => ?_⟩
    have hx : x = 0 := by
      have hmem : x ∈ (⊥ : Submodule K X) := by
        rw [← htopbot]
        exact Submodule.mem_top
      exact (Submodule.mem_bot K).mp hmem
    have hy : y = 0 := by
      have hmem : y ∈ (⊥ : Submodule K X) := by
        rw [← htopbot]
        exact Submodule.mem_top
      exact (Submodule.mem_bot K).mp hmem
    rw [hx, hy]
  obtain ⟨g, hg⟩ := hnt
  exact hg (Subsingleton.elim (ρ g) 1)

private theorem nsmul_castW_ne_zero {α : Fin 4 → ℤ} (hα : IsD4Root α) {k : ℕ}
    (hk0 : 0 < k) (hkN : k < Nat.card Kˣ) :
    (k : ZMod (Nat.card Kˣ)) • castW (Nat.card Kˣ) α ≠ 0 := by
  obtain ⟨i, -, -, hi, -, -⟩ := isD4Root_iff.mp hα
  intro hzero
  have hk : ((k : ℕ) : ZMod (Nat.card Kˣ)) ≠ 0 :=
    natCast_natCard_units_ne_zero hk0 hkN
  have hcoord : ((k : ZMod (Nat.card Kˣ)) • castW (Nat.card Kˣ) α) i =
      ((k : ℕ) : ZMod (Nat.card Kˣ)) * (α i : ZMod (Nat.card Kˣ)) := by
    simp [castW, Pi.smul_apply, smul_eq_mul]
  rw [hzero] at hcoord
  rcases hi with h | h <;> rw [h] at hcoord
  · exact hk (by simpa using hcoord.symm)
  · exact hk (by simpa using hcoord.symm)

private def StepClosed (D : D4Datum G K) (ρ : Representation K G X)
    (A : Finset (Fin 4 → ZMod (Nat.card Kˣ))) : Prop :=
  ∀ a ∈ A, ∀ α, IsD4Root α → ∀ k : ℕ, 1 ≤ k → k ≤ Nat.card Kˣ - 1 →
    a + (k : ZMod (Nat.card Kˣ)) • castW (Nat.card Kˣ) α ∈ wts D ρ →
      a + (k : ZMod (Nat.card Kˣ)) • castW (Nat.card Kˣ) α ∈ A

private theorem iSup_wtSpace_invariant {A : Finset (Fin 4 → ZMod (Nat.card Kˣ))}
    (hA : StepClosed D ρ A) :
    ∀ g : G, ∀ x ∈ ⨆ a ∈ A, D.wtSpace ρ a, ρ g x ∈ ⨆ a ∈ A, D.wtSpace ρ a := by
  refine forall_mem_of_rootElt D ρ ?_
  intro β hβ c
  have hM : (⨆ a ∈ A, D.wtSpace ρ a) ≤
      Submodule.comap (ρ (D.x β c)) (⨆ a ∈ A, D.wtSpace ρ a) := by
    refine iSup_le fun a => iSup_le fun ha => ?_
    intro x hx
    rw [rho_x_eq_sum D ρ β hβ c]
    change (∑ k ∈ Finset.range (Nat.card Kˣ + 1), c ^ k • rootOp D ρ β k) x ∈
      ⨆ a ∈ A, D.wtSpace ρ a
    rw [LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun k hk => ?_
    rw [LinearMap.smul_apply]
    by_cases hk0 : k = 0
    · rw [hk0, rootOp_zero D ρ β hβ, Module.End.one_apply, pow_zero, one_smul]
      exact Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem ha hx)
    · by_cases hkN : k = Nat.card Kˣ
      · rw [hkN]
        have hw : a + (Nat.card Kˣ : ZMod (Nat.card Kˣ)) • castW (Nat.card Kˣ) β = a := by
          rw [ZMod.natCast_self, zero_smul, add_zero]
        have hmem := rootOp_mem_wtSpace D ρ β hβ a hx (Nat.card Kˣ)
        rw [hw] at hmem
        exact Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem a
          (Submodule.mem_iSup_of_mem ha hmem))
      · have hkpos : 1 ≤ k := by
          have := Finset.mem_range.mp hk
          omega
        have hklt : k ≤ Nat.card Kˣ - 1 := by
          have := Finset.mem_range.mp hk
          omega
        by_cases hmem : a + (k : ZMod (Nat.card Kˣ)) • castW (Nat.card Kˣ) β ∈ wts D ρ
        · have hA' := hA a ha β hβ k hkpos hklt hmem
          exact Submodule.smul_mem _ _
            (Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem hA'
              (rootOp_mem_wtSpace D ρ β hβ a hx k)))
        · have hzero := rootOp_apply_eq_zero (D := D) (ρ := ρ) (C := wts D ρ)
            (fun a => mem_wts (D := D) (ρ := ρ) (a := a)) hβ hx hmem
          rw [hzero, smul_zero]
          exact Submodule.zero_mem _
  intro x hx
  exact hM hx

private theorem wts_subset_of_stepClosed
    (hirr : ∀ S : Submodule K X, (∀ g, ∀ x ∈ S, ρ g x ∈ S) → S = ⊥ ∨ S = ⊤)
    {A : Finset (Fin 4 → ZMod (Nat.card Kˣ))} (hA : StepClosed D ρ A)
    {a₀ : Fin 4 → ZMod (Nat.card Kˣ)} (ha₀ : a₀ ∈ wts D ρ) (ha₀A : a₀ ∈ A) :
    wts D ρ ⊆ A := by
  intro a ha
  by_contra haA
  have hne : D.wtSpace ρ a ≠ ⊥ := (mem_wts D ρ).mp ha
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hinv := iSup_wtSpace_invariant D ρ hA
  have htop : (⨆ b ∈ A, D.wtSpace ρ b) = ⊤ := by
    rcases hirr (⨆ b ∈ A, D.wtSpace ρ b) hinv with hbot | htop
    · exfalso
      have hle : D.wtSpace ρ a₀ ≤ ⨆ b ∈ A, D.wtSpace ρ b := fun y hy =>
        Submodule.mem_iSup_of_mem a₀ (Submodule.mem_iSup_of_mem ha₀A hy)
      rw [hbot] at hle
      exact (mem_wts D ρ).mp ha₀ (le_bot_iff.mp hle)
    · exact htop
  have hxM : x ∈ ⨆ b ∈ A, D.wtSpace ρ b := by
    rw [htop]
    exact Submodule.mem_top
  have hproj := (mem_iSup_wtSpace_finset (D := D) (ρ := ρ) (A := A)).mp hxM a haA
  have hxa : wtProj D ρ a x = x := by
    rw [wtProj_of_mem D ρ (a := a) hx, if_pos rfl]
  exact hx0 (by rw [← hxa]; exact hproj)

private theorem rho_x_eq_self_of_rootOp_eq_zero {α : Fin 4 → ℤ} (hα : IsD4Root α) {x : X}
    (hx : ∀ k : ℕ, 1 ≤ k → k ≤ Nat.card Kˣ → rootOp D ρ α k x = 0) (c : K) :
    ρ (D.x α c) x = x := by
  rw [rho_x_eq_sum D ρ α hα c]
  change (∑ k ∈ Finset.range (Nat.card Kˣ + 1), c ^ k • rootOp D ρ α k) x = x
  rw [LinearMap.sum_apply, Finset.sum_eq_single 0]
  · rw [rootOp_zero D ρ α hα, LinearMap.smul_apply, Module.End.one_apply, pow_zero,
      one_smul]
  · intro k hk hk0
    have hk1 : 1 ≤ k := by
      have := Finset.mem_range.mp hk
      omega
    have hkN : k ≤ Nat.card Kˣ := by
      have := Finset.mem_range.mp hk
      omega
    rw [LinearMap.smul_apply, hx k hk1 hkN, smul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

theorem eq_fixed_of_rootOp_eq_zero {x : X}
    (hx : ∀ α, IsD4Root α → ∀ k : ℕ, 1 ≤ k → k ≤ Nat.card Kˣ → rootOp D ρ α k x = 0) :
    ∀ g : G, ρ g x = x := by
  have key : ∀ g ∈ Subgroup.closure {g | ∃ α, IsD4Root α ∧ ∃ c, D.x α c = g}, ρ g x = x := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
        obtain ⟨α, hα, c, rfl⟩ := hg
        exact rho_x_eq_self_of_rootOp_eq_zero D ρ hα (fun k hk1 hkN => hx α hα k hk1 hkN) c
    | one => simp
    | mul g h _ _ ihg ihh => rw [map_mul, Module.End.mul_apply, ihh, ihg]
    | inv g _ ihg =>
        calc ρ g⁻¹ x = ρ g⁻¹ (ρ g x) := by rw [ihg]
          _ = x := by
              rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
                Module.End.one_apply]
  intro g
  exact key g (by rw [D.closure_eq]; exact Subgroup.mem_top g)

theorem eq_zero_of_rootOp_eq_zero
    (hirr : ∀ S : Submodule K X, (∀ g, ∀ x ∈ S, ρ g x ∈ S) → S = ⊥ ∨ S = ⊤)
    (hnt : ∃ g : G, ρ g ≠ 1) {x : X}
    (hx : ∀ α, IsD4Root α → ∀ k : ℕ, 1 ≤ k → k ≤ Nat.card Kˣ → rootOp D ρ α k x = 0) :
    x = 0 := by
  have hxfix : x ∈ ρ.invariants :=
    (Representation.mem_invariants ρ x).mpr (eq_fixed_of_rootOp_eq_zero D ρ hx)
  have hne : ρ.invariants ≠ ⊤ := by
    intro htop
    obtain ⟨g, hg⟩ := hnt
    apply hg
    ext y
    have hy : y ∈ ρ.invariants := by rw [htop]; exact Submodule.mem_top
    exact (Representation.mem_invariants ρ y).mp hy g
  have hinv : ∀ g, ∀ y ∈ ρ.invariants, ρ g y ∈ ρ.invariants := fun g y hy => by
    rw [(Representation.mem_invariants ρ y).mp hy g]
    exact hy
  rcases hirr ρ.invariants hinv with hbot | htop
  · rw [hbot] at hxfix
    exact (Submodule.mem_bot K).mp hxfix
  · exact absurd htop hne

theorem rootOp_eq_zero_of_pow_two {α : Fin 4 → ℤ} (hα : IsD4Root α) {k : ℕ}
    (hk0 : 1 ≤ k) (hkN : k ≤ Nat.card Kˣ) {x : X}
    (hpow : ∀ l : ℕ, 2 ^ l ≤ k → rootOp D ρ α (2 ^ l) x = 0) :
    rootOp D ρ α k x = 0 := by
  obtain ⟨l, u, hu, hk⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : k ≠ 0)
  have hple : 2 ^ l ≤ k := by
    rw [hk]
    have hu1 : 1 ≤ u := by
      rcases hu with ⟨w, rfl⟩
      omega
    simpa using Nat.mul_le_mul_left (2 ^ l) hu1
  obtain ⟨v, hv⟩ := hu
  have hr : k - 2 ^ l = 2 ^ (l + 1) * v := by
    rw [hk, hv, pow_succ]
    have hsub : 2 ^ l * (2 * v + 1) - 2 ^ l = 2 ^ l * (2 * v) := by
      rw [Nat.mul_add, Nat.mul_one, Nat.add_sub_cancel]
    rw [hsub]
    ring
  have hkadd : k = 2 ^ l + (k - 2 ^ l) := by omega
  have hbit : 2 ^ l &&& (k - 2 ^ l) = 0 := by
    rw [hr, Nat.two_pow_and]
    have hb : (2 ^ (l + 1) * v).testBit l = false := by
      rw [Nat.testBit, Nat.shiftRight_eq_div_pow, pow_succ]
      rw [show 2 ^ l * 2 * v = 2 ^ l * (2 * v) by ring]
      rw [Nat.mul_div_right _ (by positivity)]
      simp
    rw [hb]
    simp
  have hodd : Odd (k.choose (k - 2 ^ l)) := by
    have h := CFSG.RepresentationTheory.SL2NatSum.odd_choose_add_iff
      (i := k - 2 ^ l) (k := 2 ^ l)
    rw [Nat.sub_add_cancel hple] at h
    exact h.mpr (by rw [Nat.land_comm]; exact hbit)
  have hcoeff : (((k.choose (k - 2 ^ l) : ℕ)) : K) = 1 :=
    natCast_eq_one_of_odd_of_two_eq_zero hodd CharTwo.two_eq_zero
  have hmul := rootOp_mul D ρ α hα (k - 2 ^ l) (2 ^ l)
  rw [if_pos (by omega : k - 2 ^ l + 2 ^ l ≤ Nat.card Kˣ),
    Nat.sub_add_cancel hple, hcoeff, one_smul] at hmul
  calc rootOp D ρ α k x
      = (rootOp D ρ α (k - 2 ^ l) * rootOp D ρ α (2 ^ l)) x := by rw [hmul]
    _ = rootOp D ρ α (k - 2 ^ l) (rootOp D ρ α (2 ^ l) x) := rfl
    _ = 0 := by rw [hpow l hple, map_zero]

private theorem wts_eq_vwt_of_mem
    (hirr : ∀ S : Submodule K X, (∀ g, ∀ x ∈ S, ρ g x ∈ S) → S = ⊥ ∨ S = ⊤)
    {b : ZMod (Nat.card Kˣ)} (hb : b ≠ 0)
    {a₀ : Fin 4 → ZMod (Nat.card Kˣ)} (ha₀ : a₀ ∈ wts D ρ) (ha₀V : IsVWt b a₀)
    (hsmall : ∀ a ∈ wts D ρ, IsSmallWt a) :
    ∀ a, a ∈ wts D ρ ↔ IsVWt b a := by
  let A := (wts D ρ).filter fun a => IsVWt b a
  have hA : StepClosed D ρ A := by
    intro a ha α hα k hk1 hklt hmem
    dsimp only [A] at ha ⊢
    rw [Finset.mem_filter] at ha ⊢
    exact ⟨hmem, isVWt_of_step (odd_natCard_units K) hα
      (natCast_natCard_units_ne_zero (K := K) (by omega) (by omega)) hb ha.2 rfl
      (hsmall _ hmem)⟩
  have ha₀A : a₀ ∈ A := by
    rw [Finset.mem_filter]
    exact ⟨ha₀, ha₀V⟩
  have hsub := wts_subset_of_stepClosed D ρ hirr hA ha₀ ha₀A
  intro a
  constructor
  · intro ha
    have haA : a ∈ A := hsub ha
    dsimp only [A] at haA
    exact (Finset.mem_filter.mp haA).2
  · intro haV
    exact isVWt_mem (closed_wts D ρ) hb ha₀V ha₀ haV

private theorem wts_eq_swt_of_mem
    (hirr : ∀ S : Submodule K X, (∀ g, ∀ x ∈ S, ρ g x ∈ S) → S = ⊥ ∨ S = ⊤)
    {b : ZMod (Nat.card Kˣ)} {e : ℕ} (hb : b ≠ 0)
    {a₀ : Fin 4 → ZMod (Nat.card Kˣ)} (ha₀ : a₀ ∈ wts D ρ) (ha₀S : IsSWt b a₀)
    (he : e = negCount b a₀ % 2)
    (hsmall : ∀ a ∈ wts D ρ, IsSmallWt a) :
    ∀ a, a ∈ wts D ρ ↔ IsSWt b a ∧ negCount b a % 2 = e := by
  let A := (wts D ρ).filter fun a => IsSWt b a ∧ negCount b a % 2 = e
  have hA : StepClosed D ρ A := by
    intro a ha α hα k hk1 hklt hmem
    dsimp only [A] at ha ⊢
    rw [Finset.mem_filter] at ha ⊢
    obtain ⟨hSW, hpar⟩ := isSWt_of_step (odd_natCard_units K) hα
      (natCast_natCard_units_ne_zero (K := K) (by omega) (by omega)) hb ha.2.1 rfl
      (hsmall _ hmem)
    exact ⟨hmem, hSW, by rw [hpar]; exact ha.2.2⟩
  have ha₀A : a₀ ∈ A := by
    rw [Finset.mem_filter]
    exact ⟨ha₀, ha₀S, by rw [he]⟩
  have hsub := wts_subset_of_stepClosed D ρ hirr hA ha₀ ha₀A
  intro a
  constructor
  · intro ha
    have haA : a ∈ A := hsub ha
    dsimp only [A] at haA
    exact (Finset.mem_filter.mp haA).2
  · rintro ⟨haS, hpar⟩
    exact isSWt_mem (odd_natCard_units K) (closed_wts D ρ) hb ha₀S ha₀ haS
      (by rw [hpar, he])

private theorem wts_eq_singleton_zero_of_zero_mem
    (hsmall : ∀ a ∈ wts D ρ, IsSmallWt a)
    (hirr : ∀ S : Submodule K X, (∀ g, ∀ x ∈ S, ρ g x ∈ S) → S = ⊥ ∨ S = ⊤)
    (h0 : (0 : Fin 4 → ZMod (Nat.card Kˣ)) ∈ wts D ρ) :
    wts D ρ = {0} := by
  let A : Finset (Fin 4 → ZMod (Nat.card Kˣ)) := {0}
  have hA : StepClosed D ρ A := by
    intro a ha α hα k hk1 hklt hmem
    rw [Finset.mem_singleton] at ha
    subst ha
    have hkne : ((k : ℕ) : ZMod (Nat.card Kˣ)) ≠ 0 :=
      natCast_natCard_units_ne_zero (by omega) (by omega)
    have hsmall' : IsSmallWt ((k : ZMod (Nat.card Kˣ)) • castW (Nat.card Kˣ) α) := by
      simpa using hsmall _ hmem
    exact absurd hsmall' (not_isSmallWt_step_zero hα hkne)
  have ha₀A : (0 : Fin 4 → ZMod (Nat.card Kˣ)) ∈ A := by simp [A]
  have hsub := wts_subset_of_stepClosed D ρ hirr hA h0 ha₀A
  refine Finset.Subset.antisymm hsub ?_
  intro a ha
  rw [Finset.mem_singleton] at ha
  rw [ha]
  exact h0

private theorem rootOp_eq_zero_of_wts_singleton_zero (hK : 4 ≤ Nat.card K)
    (hzero : wts D ρ = {0}) :
    ∀ α, IsD4Root α → ∀ k : ℕ, 1 ≤ k → k ≤ Nat.card Kˣ → rootOp D ρ α k = 0 := by
  have h3 : 3 ≤ Nat.card Kˣ := three_le_natCard_units hK
  intro α hα k hk1 hkN
  refine ext_of_wtSpace (C := wts D ρ)
    (fun a => mem_wts (D := D) (ρ := ρ) (a := a)) ?_
  intro a ha x hx
  rw [hzero, Finset.mem_singleton] at ha
  subst ha
  by_cases hkN' : k = Nat.card Kˣ
  · subst hkN'
    have hkill : rootOp D ρ α (Nat.card Kˣ - 1) x = 0 := by
      refine rootOp_apply_eq_zero (D := D) (ρ := ρ) (C := wts D ρ)
        (fun a => mem_wts (D := D) (ρ := ρ) (a := a)) hα hx ?_
      rw [hzero]
      simp only [Finset.mem_singleton]
      intro hstep
      exact (nsmul_castW_ne_zero (K := K) hα (k := Nat.card Kˣ - 1) (by omega) (by omega))
        (by simpa using hstep)
    have hmul := rootOp_mul D ρ α hα 1 (Nat.card Kˣ - 1)
    have hsum : 1 + (Nat.card Kˣ - 1) = Nat.card Kˣ := by omega
    rw [if_pos (by omega : 1 + (Nat.card Kˣ - 1) ≤ Nat.card Kˣ), hsum,
      Nat.choose_one_right, natCard_units_cast_eq_one, one_smul] at hmul
    calc rootOp D ρ α (Nat.card Kˣ) x
        = (rootOp D ρ α 1 * rootOp D ρ α (Nat.card Kˣ - 1)) x := by rw [hmul]
      _ = rootOp D ρ α 1 (rootOp D ρ α (Nat.card Kˣ - 1) x) := rfl
      _ = 0 := by rw [hkill, map_zero]
  · have hkNlt : k < Nat.card Kˣ := lt_of_le_of_ne hkN hkN'
    refine rootOp_apply_eq_zero (D := D) (ρ := ρ) (C := wts D ρ)
      (fun a => mem_wts (D := D) (ρ := ρ) (a := a)) hα hx ?_
    rw [hzero]
    simp only [Finset.mem_singleton]
    intro hstep
    exact (nsmul_castW_ne_zero (K := K) hα (k := k) (by omega) hkNlt) (by simpa using hstep)

private theorem not_wts_eq_singleton_zero (hK : 4 ≤ Nat.card K)
    (hirr : ∀ S : Submodule K X, (∀ g, ∀ x ∈ S, ρ g x ∈ S) → S = ⊥ ∨ S = ⊤)
    (hnt : ∃ g : G, ρ g ≠ 1) : wts D ρ ≠ {0} := by
  intro hzero
  have hkill := rootOp_eq_zero_of_wts_singleton_zero D ρ hK hzero
  obtain ⟨g, hg⟩ := hnt
  apply hg
  ext x
  exact eq_fixed_of_rootOp_eq_zero D ρ (fun α hα k hk1 hkN => by
    rw [hkill α hα k hk1 hkN, LinearMap.zero_apply]) g

theorem zero_not_mem_wts (hK : 4 ≤ Nat.card K)
    (hirr : ∀ S : Submodule K X, (∀ g, ∀ x ∈ S, ρ g x ∈ S) → S = ⊥ ∨ S = ⊤)
    (hnt : ∃ g : G, ρ g ≠ 1) (hdim : Module.finrank K X ≤ 16) :
    (0 : Fin 4 → ZMod (Nat.card Kˣ)) ∉ wts D ρ := by
  intro h0
  have hsmall : ∀ a ∈ wts D ρ, IsSmallWt a := fun a ha =>
    isSmallWt_of_closed (odd_natCard_units K) (closed_wts D ρ)
      (le_trans (card_wts_le D ρ) hdim) ha
  exact not_wts_eq_singleton_zero D ρ hK hirr hnt
    (wts_eq_singleton_zero_of_zero_mem D ρ hsmall hirr h0)

private theorem exists_pow_two_of_wts_eq_vwt (hK : 4 ≤ Nat.card K)
    (hirr : ∀ S : Submodule K X, (∀ g, ∀ x ∈ S, ρ g x ∈ S) → S = ⊥ ∨ S = ⊤)
    (hnt : ∃ g : G, ρ g ≠ 1) {b : ZMod (Nat.card Kˣ)} (hb : b ≠ 0)
    (hclass : ∀ a, a ∈ wts D ρ ↔ IsVWt b a) :
    ∃ l : ℕ, 2 ^ l ≤ Nat.card Kˣ ∧
      (b = (2 : ZMod (Nat.card Kˣ)) ^ l ∨
        b = -((2 : ZMod (Nat.card Kˣ)) ^ l)) := by
  by_contra hcon
  have hno : ∀ l : ℕ, 2 ^ l ≤ Nat.card Kˣ →
      b ≠ (2 : ZMod (Nat.card Kˣ)) ^ l ∧
        b ≠ -((2 : ZMod (Nat.card Kˣ)) ^ l) := by
    intro l hl
    constructor
    · intro h
      exact hcon ⟨l, hl, Or.inl h⟩
    · intro h
      exact hcon ⟨l, hl, Or.inr h⟩
  obtain ⟨a, ha⟩ := wts_nonempty D ρ hnt
  have hane : D.wtSpace ρ a ≠ ⊥ := (mem_wts D ρ).mp ha
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hane
  have hkill : ∀ α, IsD4Root α → ∀ k : ℕ, 1 ≤ k → k ≤ Nat.card Kˣ →
      rootOp D ρ α k x = 0 := by
    intro α hα k hk1 hkN
    refine rootOp_eq_zero_of_pow_two (D := D) (ρ := ρ) hα hk1 hkN ?_
    intro l hl
    have hle : 2 ^ l ≤ Nat.card Kˣ := le_trans hl hkN
    have hlt : 2 ^ l < Nat.card Kˣ := two_pow_lt_natCard_units hK hle
    have hkne : ((2 ^ l : ℕ) : ZMod (Nat.card Kˣ)) ≠ 0 :=
      natCast_natCard_units_ne_zero (K := K) (by positivity) hlt
    have hcast : ((2 ^ l : ℕ) : ZMod (Nat.card Kˣ)) = (2 : ZMod (Nat.card Kˣ)) ^ l := by
      rw [Nat.cast_pow]
      norm_num
    refine rootOp_apply_eq_zero (D := D) (ρ := ρ) (C := wts D ρ)
      (fun a => mem_wts (D := D) (ρ := ρ) (a := a)) hα hx ?_
    intro hmem
    have haV : IsVWt b a := (hclass a).mp ha
    have ha'V : IsVWt b (a + ((2 ^ l : ℕ) : ZMod (Nat.card Kˣ)) •
      castW (Nat.card Kˣ) α) := (hclass _).mp hmem
    rcases step_eq_of_isVWt hα hkne hb haV rfl ha'V with h | h
    · exact (hno l hle).1 (by rw [hcast] at h; exact h.symm)
    · exact (hno l hle).2 (by rw [hcast] at h; rw [h]; simp)
  exact hx0 (eq_zero_of_rootOp_eq_zero D ρ hirr hnt hkill)

private theorem exists_pow_two_of_wts_eq_swt (hK : 4 ≤ Nat.card K)
    (hirr : ∀ S : Submodule K X, (∀ g, ∀ x ∈ S, ρ g x ∈ S) → S = ⊥ ∨ S = ⊤)
    (hnt : ∃ g : G, ρ g ≠ 1) {b : ZMod (Nat.card Kˣ)} {e : ℕ}
    (hclass : ∀ a, a ∈ wts D ρ ↔ IsSWt b a ∧ negCount b a % 2 = e) :
    ∃ l : ℕ, 2 ^ l ≤ Nat.card Kˣ ∧
      (2 * b = (2 : ZMod (Nat.card Kˣ)) ^ l ∨
        2 * b = -((2 : ZMod (Nat.card Kˣ)) ^ l)) := by
  by_contra hcon
  have hno : ∀ l : ℕ, 2 ^ l ≤ Nat.card Kˣ →
      2 * b ≠ (2 : ZMod (Nat.card Kˣ)) ^ l ∧
        2 * b ≠ -((2 : ZMod (Nat.card Kˣ)) ^ l) := by
    intro l hl
    constructor
    · intro h
      exact hcon ⟨l, hl, Or.inl h⟩
    · intro h
      exact hcon ⟨l, hl, Or.inr h⟩
  obtain ⟨a, ha⟩ := wts_nonempty D ρ hnt
  have hane : D.wtSpace ρ a ≠ ⊥ := (mem_wts D ρ).mp ha
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hane
  have hkill : ∀ α, IsD4Root α → ∀ k : ℕ, 1 ≤ k → k ≤ Nat.card Kˣ →
      rootOp D ρ α k x = 0 := by
    intro α hα k hk1 hkN
    refine rootOp_eq_zero_of_pow_two (D := D) (ρ := ρ) hα hk1 hkN ?_
    intro l hl
    have hle : 2 ^ l ≤ Nat.card Kˣ := le_trans hl hkN
    have hlt : 2 ^ l < Nat.card Kˣ := two_pow_lt_natCard_units hK hle
    have hkne : ((2 ^ l : ℕ) : ZMod (Nat.card Kˣ)) ≠ 0 :=
      natCast_natCard_units_ne_zero (K := K) (by positivity) hlt
    have hcast : ((2 ^ l : ℕ) : ZMod (Nat.card Kˣ)) = (2 : ZMod (Nat.card Kˣ)) ^ l := by
      rw [Nat.cast_pow]
      norm_num
    refine rootOp_apply_eq_zero (D := D) (ρ := ρ) (C := wts D ρ)
      (fun a => mem_wts (D := D) (ρ := ρ) (a := a)) hα hx ?_
    intro hmem
    have haS : IsSWt b a := ((hclass a).mp ha).1
    have ha'S : IsSWt b (a + ((2 ^ l : ℕ) : ZMod (Nat.card Kˣ)) •
      castW (Nat.card Kˣ) α) := ((hclass _).mp hmem).1
    rcases step_eq_of_isSWt hα hkne haS rfl ha'S with h | h
    · exact (hno l hle).1 (by rw [hcast] at h; exact h.symm)
    · exact (hno l hle).2 (by rw [hcast] at h; rw [h]; simp)
  exact hx0 (eq_zero_of_rootOp_eq_zero D ρ hirr hnt hkill)

private theorem swt_neg_parity (hN : Odd (Nat.card Kˣ)) {b : ZMod (Nat.card Kˣ)} (hb : b ≠ 0)
    (e : ℕ) (a : Fin 4 → ZMod (Nat.card Kˣ)) :
    (IsSWt (-b) a ∧ negCount (-b) a % 2 = e) ↔
      (IsSWt b a ∧ negCount b a % 2 = e) := by
  have hmod : ∀ m : ℕ, m ≤ 4 → (4 - m) % 2 = m % 2 := by
    intro m hm
    omega
  constructor
  · rintro ⟨ha, he⟩
    have hbS : IsSWt b a := isSWt_neg_iff.mp ha
    have hc := negCount_neg hN hb hbS
    refine ⟨hbS, ?_⟩
    have hle : negCount b a ≤ 4 := by
      rw [negCount]
      simpa using Finset.card_le_univ (Finset.univ.filter fun i => a i = -b)
    rw [hc, hmod _ hle] at he
    exact he
  · rintro ⟨ha, he⟩
    have hneg : IsSWt (-b) a := isSWt_neg_iff.mpr ha
    have hc := negCount_neg hN hb ha
    refine ⟨hneg, ?_⟩
    have hle : negCount b a ≤ 4 := by
      rw [negCount]
      simpa using Finset.card_le_univ (Finset.univ.filter fun i => a i = -b)
    rw [hc, hmod _ hle]
    exact he

theorem wts_classification (hK : 4 ≤ Nat.card K)
    (hirr : ∀ S : Submodule K X, (∀ g, ∀ x ∈ S, ρ g x ∈ S) → S = ⊥ ∨ S = ⊤)
    (hnt : ∃ g : G, ρ g ≠ 1) (hdim : Module.finrank K X ≤ 16) :
    (∃ l : ℕ, 2 ^ l < Nat.card Kˣ ∧
        ∀ a, a ∈ wts D ρ ↔ IsVWt ((2 : ZMod (Nat.card Kˣ)) ^ l) a) ∨
      (∃ (b : ZMod (Nat.card Kˣ)) (l e : ℕ), 2 ^ l < Nat.card Kˣ ∧
        2 * b = 2 ^ l ∧ e < 2 ∧
          ∀ a, a ∈ wts D ρ ↔ IsSWt b a ∧ negCount b a % 2 = e) := by
  have hsmall : ∀ a ∈ wts D ρ, IsSmallWt a := fun a ha =>
    isSmallWt_of_closed (odd_natCard_units K) (closed_wts D ρ)
      (le_trans (card_wts_le D ρ) hdim) ha
  obtain ⟨a₀, ha₀⟩ := wts_nonempty D ρ hnt
  have ha₀zero : a₀ ≠ 0 := fun h => zero_not_mem_wts D ρ hK hirr hnt hdim (h ▸ ha₀)
  rcases hsmall a₀ ha₀ with h0 | ⟨b, hb, hV⟩ | ⟨b, hb, hS⟩
  · exact absurd h0 ha₀zero
  · have hclass := wts_eq_vwt_of_mem D ρ hirr hb ha₀ hV hsmall
    obtain ⟨l, hl, hb_eq⟩ := exists_pow_two_of_wts_eq_vwt D ρ hK hirr hnt hb hclass
    left
    refine ⟨l, two_pow_lt_natCard_units hK hl, ?_⟩
    intro a
    rw [hclass a]
    rcases hb_eq with h | h
    · rw [h.symm]
    · rw [show (2 : ZMod (Nat.card Kˣ)) ^ l = -b by rw [h, neg_neg]]
      exact isVWt_neg_iff.symm
  · let e := negCount b a₀ % 2
    have hclass := wts_eq_swt_of_mem D ρ hirr hb ha₀ hS rfl hsmall
    obtain ⟨l, hl, hb_eq⟩ := exists_pow_two_of_wts_eq_swt D ρ hK hirr hnt hclass
    right
    rcases hb_eq with h | h
    · refine ⟨b, l, e, two_pow_lt_natCard_units hK hl, h, ?_, ?_⟩
      · exact Nat.mod_lt (negCount b a₀) (by norm_num)
      · intro a
        exact hclass a
    · refine ⟨-b, l, e, two_pow_lt_natCard_units hK hl, ?_, ?_, ?_⟩
      · rw [mul_neg, h, neg_neg]
      · exact Nat.mod_lt (negCount b a₀) (by norm_num)
      · intro a
        rw [hclass a]
        exact (swt_neg_parity (odd_natCard_units K) hb e a).symm

end CFSG.LieType.D4Small.D4Datum