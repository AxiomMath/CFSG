module

public import CFSG.Alternating.Multipliers.Main
public import CFSG.GH74.Uniqueness.SU.SU13TA1Invol

public noncomputable section

namespace CFSG.Alternating.Multipliers.Spin

open Equiv Equiv.Perm Subgroup CFSG.RankThree.PerfectCover CFSG.GH74.Uniqueness.SU.SU13.TA
open scoped commutatorElement

variable {n : ℕ}

theorem exists_negOneE {m : ℕ} (hm : 2 ≤ m) :
    ∃ z : E (m + 2), ((z : H (m + 2)) : monomial (m + 2)) = negOne := by
  set p₀ : Fin (m + 2) := ⟨0, by omega⟩
  set p₁ : Fin (m + 2) := ⟨1, by omega⟩
  set p₂ : Fin (m + 2) := ⟨2, by omega⟩
  set p₃ : Fin (m + 2) := ⟨3, by omega⟩
  have h01 : p₀ ≠ p₁ := by simp [p₀, p₁]
  have h02 : p₀ ≠ p₂ := by simp [p₀, p₂, Fin.ext_iff]
  have h03 : p₀ ≠ p₃ := by simp [p₀, p₃, Fin.ext_iff]
  have h12 : p₁ ≠ p₂ := by simp [p₁, p₂, Fin.ext_iff]
  have h13 : p₁ ≠ p₃ := by simp [p₁, p₃, Fin.ext_iff]
  have h23 : p₂ ≠ p₃ := by simp [p₂, p₃, Fin.ext_iff]
  set x : H (m + 2) := ⟨dd h01 h23, subset_closure ⟨_, _, _, _, _, _, rfl⟩⟩
  set y : H (m + 2) := ⟨dd h02 h13, subset_closure ⟨_, _, _, _, _, _, rfl⟩⟩
  set w : E (m + 2) := ⟨⁅x, y⁆, commutator_mem_commutator (mem_top x) (mem_top y)⟩
  have hw : ((w : H (m + 2)) : monomial (m + 2)) = negOne :=
    commutator_dd h01 h02 h03 h12 h13 h23
  exact ⟨w, hw⟩

noncomputable def negOneE {m : ℕ} (hm : 2 ≤ m) : E (m + 2) :=
  (exists_negOneE hm).choose

theorem negOneE_val {m : ℕ} (hm : 2 ≤ m) :
    ((negOneE hm : H (m + 2)) : monomial (m + 2)) = negOne :=
  (exists_negOneE hm).choose_spec

theorem negOneE_ne_one {m : ℕ} (hm : 2 ≤ m) : negOneE hm ≠ 1 := by
  intro h
  have h1 : ((negOneE hm : H (m + 2)) : monomial (m + 2)) = 1 := by
    rw [h]
    rfl
  rw [negOneE_val hm] at h1
  exact negOne_ne_one h1

theorem psi_negOneE {m : ℕ} (hm : 2 ≤ m) : psi (m := m) (negOneE hm) = 1 := by
  apply Subtype.ext
  change perm (((negOneE hm : E (m + 2)) : H (m + 2)) : monomial (m + 2)) = 1
  rw [negOneE_val hm]
  exact perm_negOne

theorem card_ker_psi {m : ℕ} (hm : 6 ≤ m) : Nat.card (psi (m := m)).ker = 2 := by
  haveI : Group.IsPerfect (E (m + 2)) := E_isPerfect (by omega)
  have hMcard : Nat.card (hopfMultiplier (alternatingGroup (Fin (m + 2)))) = 2 :=
    card_hopfMultiplier_alternatingGroup (by omega)
  have hmap := map_hopfMultiplier_hopfLift (psi (m := m)) (psi_surjective (by omega))
    (ker_psi_le_center (m := m))
  have hdvd : Nat.card (psi (m := m)).ker ∣ 2 := by
    have h := Subgroup.card_map_dvd (hopfMultiplier (alternatingGroup (Fin (m + 2))))
      (hopfLift (psi (m := m)) (psi_surjective (by omega)) (ker_psi_le_center (m := m)))
    rw [hMcard] at h
    rwa [hmap] at h
  have hne : Nat.card (psi (m := m)).ker ≠ 1 := by
    intro hcard
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (ker_psi_ne_bot (by omega : 2 ≤ m))
    haveI : Subsingleton (psi (m := m)).ker := (Nat.card_eq_one_iff_unique.mp hcard).1
    exact ha (Subsingleton.elim a 1)
  have hle : Nat.card (psi (m := m)).ker ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have h0 : Nat.card (psi (m := m)).ker ≠ 0 := by
    intro h
    rw [h] at hdvd
    norm_num at hdvd
  omega

theorem ker_psi_eq {m : ℕ} (hm : 6 ≤ m) {x : E (m + 2)} :
    psi (m := m) x = 1 ↔ x = 1 ∨ x = negOneE (by omega : 2 ≤ m) := by
  have hcard := card_ker_psi hm
  have hmem : (⟨negOneE (by omega : 2 ≤ m), psi_negOneE (by omega : 2 ≤ m)⟩ :
      (psi (m := m)).ker) ≠ 1 := by
    intro h
    exact negOneE_ne_one (by omega : 2 ≤ m) (Subtype.ext_iff.mp h)
  obtain ⟨z, -, hzu⟩ := (Nat.card_eq_two_iff' (1 : (psi (m := m)).ker)).mp hcard
  have hz : z = ⟨negOneE (by omega : 2 ≤ m), psi_negOneE (by omega : 2 ≤ m)⟩ :=
    (hzu _ hmem).symm
  constructor
  · intro hx
    let x' : (psi (m := m)).ker := ⟨x, hx⟩
    by_cases hx1 : x' = 1
    · left
      exact congrArg Subtype.val hx1
    · right
      calc x = (x' : E (m + 2)) := rfl
        _ = (z : E (m + 2)) := congrArg Subtype.val (hzu x' hx1)
        _ = negOneE (by omega : 2 ≤ m) := congrArg Subtype.val hz
  · rintro (rfl | rfl)
    · exact map_one _
    · exact psi_negOneE (by omega : 2 ≤ m)

theorem twoCover_psi {m : ℕ} (hm : 6 ≤ m) : TwoCover (psi (m := m)) where
  surj := psi_surjective (by omega)
  ker_le_center := ker_psi_le_center
  card_ker := card_ker_psi hm
  perfect := E_isPerfect (by omega)

theorem E_sq_eq_negOne_of_cycleType_two_two {m : ℕ} (hm : 6 ≤ m) {x : E (m + 2)}
    (hx : ((psi (m := m) x : alternatingGroup (Fin (m + 2))) :
      Equiv.Perm (Fin (m + 2))).cycleType = {2, 2}) :
    x ^ 2 = negOneE (by omega : 2 ≤ m) := by
  have h := TwoCover.sq_mem_ker_ne_one_of_cycleType_two_two (twoCover_psi hm)
    (by omega : 5 ≤ m + 2) hx
  rcases (ker_psi_eq hm).mp h.1 with h1 | hζ
  · exact absurd h1 h.2
  · exact hζ

theorem E_sq_eq_one_of_cycleType_two_two_two_two {m : ℕ} (hm : 6 ≤ m) {x : E (m + 2)}
    (hx : ((psi (m := m) x : alternatingGroup (Fin (m + 2))) :
      Equiv.Perm (Fin (m + 2))).cycleType = {2, 2, 2, 2}) :
    x ^ 2 = 1 :=
  TwoCover.sq_eq_one_of_cycleType_two_two_two_two (twoCover_psi hm) (by omega : 8 ≤ m + 2) hx

theorem map_eq_zpowers_of_unique_nontrivial {G H : Type*} [Group G] [Group H]
    (M : Subgroup G) (f : G →* H) (m : M) (hm : ∀ c : M, c ≠ 1 → c = m) :
    M.map f = Subgroup.zpowers (f (m : G)) := by
  have hM : M = Subgroup.zpowers (m : G) := by
    ext x
    constructor
    · intro hx
      by_cases hx1 : (⟨x, hx⟩ : M) = 1
      · rw [show x = 1 by exact congrArg Subtype.val hx1]
        exact Subgroup.one_mem _
      · rw [show x = (m : G) by exact congrArg Subtype.val (hm _ hx1)]
        exact Subgroup.mem_zpowers _
    · intro hx
      rw [Subgroup.mem_zpowers_iff] at hx
      obtain ⟨k, rfl⟩ := hx
      exact Subgroup.zpow_mem M m.2 k
  conv_lhs => rw [hM]
  exact MonoidHom.map_zpowers f (m : G)

theorem sq_eq_of_perfect_double_cover {n : ℕ} (hn : 8 ≤ n) {E : Type*} [Group E]
    [Group.IsPerfect E] (π : E →* alternatingGroup (Fin n)) (hπ : Function.Surjective π) {ζ : E}
    (hker : ∀ x, π x = 1 ↔ x = 1 ∨ x = ζ) (hζ : ζ ∈ Subgroup.center E) (hζ1 : ζ ≠ 1) :
    (∀ x : E, ((π x : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)).cycleType = {2, 2} →
      x ^ 2 = ζ) ∧
    (∀ x : E, ((π x : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)).cycleType = {2, 2, 2, 2} →
      x ^ 2 = 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hm : 6 ≤ m := by omega
  let S := alternatingGroup (Fin (m + 2))
  have hζker : ζ ∈ π.ker := (hker ζ).mpr (Or.inr rfl)
  have hcardπ : Nat.card π.ker = 2 := by
    refine (Nat.card_eq_two_iff' (1 : π.ker)).mpr ⟨⟨ζ, hζker⟩, ?_, ?_⟩
    · intro h
      exact hζ1 (congrArg Subtype.val h)
    · intro c hc
      apply Subtype.ext
      have hc1 : (c : E) ≠ 1 := fun h => hc (Subtype.ext h)
      rcases (hker (c : E)).mp c.2 with h | h
      · exact absurd h hc1
      · exact h
  have hcenter : π.ker ≤ Subgroup.center E := by
    intro x hx
    rcases (hker x).mp hx with rfl | rfl
    · exact Subgroup.one_mem _
    · exact hζ
  haveI : Group.IsPerfect (CFSG.Alternating.Multipliers.Spin.E (m + 2)) := E_isPerfect (by omega)
  let M := hopfMultiplier S
  have hMcard : Nat.card M = 2 := card_hopfMultiplier_alternatingGroup (by omega)
  let h1 := hopfLift π hπ hcenter
  let h2 := hopfLift (psi (m := m)) (psi_surjective (by omega)) (ker_psi_le_center (m := m))
  have h1comp : π.comp h1 = hopfCoverMap S := comp_hopfLift π hπ hcenter
  have h2comp : (psi (m := m)).comp h2 = hopfCoverMap S :=
    comp_hopfLift (psi (m := m)) (psi_surjective (by omega)) (ker_psi_le_center (m := m))
  have h1map : M.map h1 = π.ker := map_hopfMultiplier_hopfLift π hπ hcenter
  have h2map : M.map h2 = (psi (m := m)).ker :=
    map_hopfMultiplier_hopfLift (psi (m := m)) (psi_surjective (by omega))
      (ker_psi_le_center (m := m))
  obtain ⟨m₀, hm₀1, hm₀u⟩ := (Nat.card_eq_two_iff' (1 : M)).mp hMcard
  have h2map_zp : M.map h2 = Subgroup.zpowers (h2 (m₀ : HopfCover S)) :=
    map_eq_zpowers_of_unique_nontrivial M h2 m₀ hm₀u
  have h2m₀ : h2 (m₀ : HopfCover S) ≠ 1 := by
    intro h
    have hbot : M.map h2 = ⊥ := by rw [h2map_zp, h, Subgroup.zpowers_one_eq_bot]
    have hcard1 : Nat.card (M.map h2) = 1 := by rw [hbot, Subgroup.card_bot]
    rw [h2map, card_ker_psi hm] at hcard1
    omega
  have h1map_zp : M.map h1 = Subgroup.zpowers (h1 (m₀ : HopfCover S)) :=
    map_eq_zpowers_of_unique_nontrivial M h1 m₀ hm₀u
  have h1m₀ : h1 (m₀ : HopfCover S) = ζ := by
    have hne : h1 (m₀ : HopfCover S) ≠ 1 := by
      intro h
      have hbot : M.map h1 = ⊥ := by rw [h1map_zp, h, Subgroup.zpowers_one_eq_bot]
      have hcard1 : Nat.card (M.map h1) = 1 := by rw [hbot, Subgroup.card_bot]
      rw [h1map, hcardπ] at hcard1
      omega
    have hmem : h1 (m₀ : HopfCover S) ∈ π.ker := by
      rw [← h1map]
      exact Subgroup.mem_map_of_mem h1 m₀.2
    rcases (hker _).mp hmem with h | h
    · exact absurd h hne
    · exact h
  have h1surj : Function.Surjective h1 := hopfLift_surjective π hπ hcenter
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨xhat, rfl⟩ := h1surj x
    have hpsi_eq : psi (m := m) (h2 xhat) = π (h1 xhat) := by
      rw [← MonoidHom.comp_apply, h2comp, ← h1comp, MonoidHom.comp_apply]
    have htype : ((psi (m := m) (h2 xhat) : alternatingGroup (Fin (m + 2))) :
        Equiv.Perm (Fin (m + 2))).cycleType = {2, 2} := by
      rw [hpsi_eq]
      exact hx
    have hsq2 : (h2 xhat) ^ 2 = negOneE (by omega : 2 ≤ m) :=
      E_sq_eq_negOne_of_cycleType_two_two hm htype
    have hsq : (π (h1 xhat)) ^ 2 = 1 :=
      TwoCover.sq_eq_one_of_cycleType_eq (c := {2, 2}) (by simp) hx
    have hcov : hopfCoverMap S xhat = π (h1 xhat) := by
      rw [← h1comp, MonoidHom.comp_apply]
    have hxhat2M : xhat ^ 2 ∈ M := by
      show hopfCoverMap S (xhat ^ 2) = 1
      rw [map_pow, hcov, hsq]
    have hne : xhat ^ 2 ≠ 1 := by
      intro h
      have h1' : h2 (xhat ^ 2) = 1 := by rw [h, map_one]
      rw [map_pow, hsq2] at h1'
      exact negOneE_ne_one (by omega : 2 ≤ m) h1'
    have hxhat2 : xhat ^ 2 = (m₀ : HopfCover S) := by
      have hx' : (⟨xhat ^ 2, hxhat2M⟩ : M) ≠ 1 := fun h => hne (Subtype.ext_iff.mp h)
      exact congrArg Subtype.val (hm₀u _ hx')
    calc (h1 xhat) ^ 2 = h1 (xhat ^ 2) := by rw [map_pow]
      _ = h1 (m₀ : HopfCover S) := by rw [hxhat2]
      _ = ζ := h1m₀
  · intro x hx
    obtain ⟨xhat, rfl⟩ := h1surj x
    have hpsi_eq : psi (m := m) (h2 xhat) = π (h1 xhat) := by
      rw [← MonoidHom.comp_apply, h2comp, ← h1comp, MonoidHom.comp_apply]
    have htype : ((psi (m := m) (h2 xhat) : alternatingGroup (Fin (m + 2))) :
        Equiv.Perm (Fin (m + 2))).cycleType = {2, 2, 2, 2} := by
      rw [hpsi_eq]
      exact hx
    have hsq2 : (h2 xhat) ^ 2 = 1 :=
      E_sq_eq_one_of_cycleType_two_two_two_two hm htype
    have hsq : (π (h1 xhat)) ^ 2 = 1 :=
      TwoCover.sq_eq_one_of_cycleType_eq (c := {2, 2, 2, 2}) (by simp) hx
    have hcov : hopfCoverMap S xhat = π (h1 xhat) := by
      rw [← h1comp, MonoidHom.comp_apply]
    have hxhat2M : xhat ^ 2 ∈ M := by
      show hopfCoverMap S (xhat ^ 2) = 1
      rw [map_pow, hcov, hsq]
    have hxhat2 : xhat ^ 2 = 1 := by
      by_contra hne
      have hx' : (⟨xhat ^ 2, hxhat2M⟩ : M) ≠ 1 := fun h => hne (Subtype.ext_iff.mp h)
      have hxhat2m : xhat ^ 2 = (m₀ : HopfCover S) := congrArg Subtype.val (hm₀u _ hx')
      have h1' : h2 (xhat ^ 2) = 1 := by rw [map_pow, hsq2]
      rw [hxhat2m] at h1'
      exact h2m₀ h1'
    calc (h1 xhat) ^ 2 = h1 (xhat ^ 2) := by rw [map_pow]
      _ = 1 := by rw [hxhat2, map_one]

theorem sq_eq_of_perfect_double_cover_nine {E : Type*} [Group E] [Group.IsPerfect E]
    (π : E →* alternatingGroup (Fin 9)) (hπ : Function.Surjective π) {ζ : E}
    (hker : ∀ x, π x = 1 ↔ x = 1 ∨ x = ζ) (hζ : ζ ∈ Subgroup.center E) (hζ1 : ζ ≠ 1) :
    (∀ x : E, ((π x : alternatingGroup (Fin 9)) : Equiv.Perm (Fin 9)).cycleType = {2, 2} →
      x ^ 2 = ζ) ∧
    (∀ x : E, ((π x : alternatingGroup (Fin 9)) : Equiv.Perm (Fin 9)).cycleType =
      {2, 2, 2, 2} → x ^ 2 = 1) :=
  sq_eq_of_perfect_double_cover (by norm_num) π hπ hker hζ hζ1

end CFSG.Alternating.Multipliers.Spin
