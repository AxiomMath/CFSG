module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FSetup

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B : Subgroup G}
  {φ : (Fin 7 → ZMod 2) → G}

private lemma sec4F_permVec_add {n : ℕ} (σ : Equiv.Perm (Fin n)) (v w : Fin n → ZMod 2) :
    permVec σ (v + w) = permVec σ v + permVec σ w := by
  funext k
  simp only [permVec, Function.comp_apply, Pi.add_apply]

private lemma sec4F_permVec_single {n : ℕ} (σ : Equiv.Perm (Fin n)) (a : Fin n) :
    permVec σ (Pi.single a (1 : ZMod 2)) = Pi.single (σ a) 1 := by
  funext k
  simp only [permVec, Function.comp_apply, Pi.single_apply]
  by_cases h : k = σ a
  · rw [if_pos h, if_pos ((Equiv.symm_apply_eq σ).mpr h)]
  · rw [if_neg h, if_neg (fun hh => h ((Equiv.symm_apply_eq σ).mp hh))]

private lemma sec4F_sec4MV_pair (a b : Fin 7) :
    sec4MV (some a) + sec4MV (some b) = Pi.single a (1 : ZMod 2) + Pi.single b 1 := by
  decide +kernel +revert

private lemma sec4F_exists_single_add_single {v : Fin 7 → ZMod 2} (hv : vecWeight v = 2) :
    ∃ a b : Fin 7, a ≠ b ∧ v = Pi.single a (1 : ZMod 2) + Pi.single b 1 := by
  unfold vecWeight at hv
  obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.mp hv
  refine ⟨a, b, hab, ?_⟩
  funext k
  have hmem : k ∈ ({a, b} : Finset (Fin 7)) ↔ v k ≠ 0 := by
    rw [← hs, Finset.mem_filter]
    simp
  rw [Pi.add_apply]
  by_cases hka : k = a
  · rw [hka] at hmem ⊢
    have hva : v a ≠ 0 := hmem.mp (by simp)
    rw [zmod2_eq_one_of_ne_zero hva, Pi.single_eq_same, Pi.single_eq_of_ne hab, add_zero]
  · by_cases hkb : k = b
    · rw [hkb] at hmem ⊢
      have hvb : v b ≠ 0 := hmem.mp (by simp)
      rw [zmod2_eq_one_of_ne_zero hvb, Pi.single_eq_of_ne (Ne.symm hab), Pi.single_eq_same,
        zero_add]
    · have hvk : v k = 0 := by
        by_contra h
        have hkab : k ∈ ({a, b} : Finset (Fin 7)) := hmem.mpr h
        exact (by simp [hka, hkb] : ¬ (k ∈ ({a, b} : Finset (Fin 7)))) hkab
      rw [hvk, Pi.single_eq_of_ne hka, Pi.single_eq_of_ne hkb, add_zero]

theorem Sec4FSetup.conj_phi_of_realizes_swap (h : Sec4FSetup t L S z A B φ) {μ : G}
    {i j : Fin 7} (hμ : Sec4MRealizes t φ μ (Equiv.swap (some i) (some j))) :
    ∀ v : Fin 7 → ZMod 2, IsEvenVec v →
      μ * φ v * μ⁻¹ = φ (permVec (Equiv.swap i j) v) := by
  classical
  let P : (Fin 7 → ZMod 2) → Prop := fun v =>
    μ * φ v * μ⁻¹ = φ (permVec (Equiv.swap i j) v)
  have hphi : ∀ a b : Fin 7, sec4MPt t φ (some a) * sec4MPt t φ (some b) =
      φ (Pi.single a (1 : ZMod 2) + Pi.single b 1) := by
    intro a b
    rw [sec4MPt_mul h.data (some a) (some b), sec4F_sec4MV_pair]
  have hpt : ∀ c : Fin 7, μ * sec4MPt t φ (some c) * μ⁻¹ =
      sec4MPt t φ (some (Equiv.swap i j c)) := by
    intro c
    have hc : μ * sec4MPt t φ (some c) * μ⁻¹ =
        sec4MPt t φ (Equiv.optionCongr (Equiv.swap i j) (some c)) := by
      simpa only [← Equiv.optionCongr_swap] using hμ (some c)
    simpa only [Equiv.optionCongr_apply, Option.map_some] using hc
  have hP0 : P 0 := by
    dsimp only [P]
    have h0 : permVec (Equiv.swap i j) (0 : Fin 7 → ZMod 2) = 0 := by
      funext k
      rfl
    rw [h0, IsPermModuleVia.map_zero h.data.bdata.perm]
    group
  have hPadd : ∀ v w, IsEvenVec v → IsEvenVec w → P v → P w → P (v + w) := by
    intro v w hv hw hPv hPw
    dsimp only [P] at hPv hPw ⊢
    rw [h.data.bdata.perm.1 v w hv hw, sec4F_permVec_add,
      h.data.bdata.perm.1 (permVec (Equiv.swap i j) v) (permVec (Equiv.swap i j) w)
        (isEvenVec_permVec (Equiv.swap i j) hv) (isEvenVec_permVec (Equiv.swap i j) hw)]
    rw [← hPv, ← hPw]
    group
  have hPgen : ∀ a b : Fin 7, P (Pi.single a (1 : ZMod 2) + Pi.single b 1) := by
    intro a b
    dsimp only [P]
    rw [sec4F_permVec_add, sec4F_permVec_single, sec4F_permVec_single,
      ← hphi a b, ← hphi (Equiv.swap i j a) (Equiv.swap i j b)]
    rw [show μ * (sec4MPt t φ (some a) * sec4MPt t φ (some b)) * μ⁻¹ =
        (μ * sec4MPt t φ (some a) * μ⁻¹) * (μ * sec4MPt t φ (some b) * μ⁻¹)
        by group]
    rw [hpt a, hpt b]
  have hUeven : ∀ v, v ∈ AddSubgroup.closure {u : Fin 7 → ZMod 2 | IsEvenVec u ∧
      vecWeight u = 2} → IsEvenVec v := by
    intro v hv
    refine AddSubgroup.closure_induction (p := fun v _ => IsEvenVec v) ?_ ?_ ?_ ?_ hv
    · rintro x ⟨hx, -⟩
      exact hx
    · unfold IsEvenVec
      simp
    · intro x y _ _ hx hy
      exact isEvenVec_add hx hy
    · intro x _ hx
      rwa [CharTwo.neg_eq x]
  have hUP : ∀ v, v ∈ AddSubgroup.closure {u : Fin 7 → ZMod 2 | IsEvenVec u ∧
      vecWeight u = 2} → P v := by
    intro v hv
    refine AddSubgroup.closure_induction (p := fun v _ => P v) ?_ hP0 ?_ ?_ hv
    · rintro x ⟨-, hxw⟩
      obtain ⟨a, b, -, hvab⟩ := sec4F_exists_single_add_single hxw
      rw [hvab]
      exact hPgen a b
    · intro x y hx hy hPx hPy
      exact hPadd x y (hUeven x hx) (hUeven y hy) hPx hPy
    · intro x _ hPx
      rwa [CharTwo.neg_eq x]
  intro v hv
  exact hUP v (isEvenVec_mem_closure_weight (k := 2) (Or.inl rfl) hv)

end CFSG.OddStandard.SmallF3.Omega
