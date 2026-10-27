module

public import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCover

public section

namespace CFSG.ComponentClassification.GSThmB.Cov

open Equiv Equiv.Perm CFSG.LocalAnalysis.ComponentInitial

variable {P : Type*} [Group P] [Finite P]

theorem sq_ne_one_of_lift_c01 [Group.IsPerfect P] {m : ℕ} (hm : 3 ≤ m)
    (η : P →* alternatingGroup (Fin (m + 2))) (hη : Function.Surjective η)
    (hK : η.ker ≤ Subgroup.center P) (hK2 : Nat.card η.ker = 2) {y : P}
    (hy : η y = altThreeCycle (⟨0, by omega⟩ : Fin m) * altThreeCycle (⟨1, by omega⟩ : Fin m)) :
    y ^ 2 ≠ 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK2' : IsPGroup 2 η.ker := IsPGroup.of_card (n := 1) (by rw [hK2, pow_one])
  have hlift : ∀ i : Fin m, ∃ x : P, η x = altThreeCycle i ∧ x ^ 3 = 1 := fun i => by
    obtain ⟨y, hy⟩ := hη (altThreeCycle i)
    obtain ⟨x, hx, hx3⟩ := exists_lift_pow_three_eq_one hK hK2'
      (by rw [hy]; exact altThreeCycle_pow_three i)
    exact ⟨x, hx.trans hy, hx3⟩
  choose x hxη hx3 using hlift
  have hL : Subgroup.closure (Set.range x) = ⊤ := by
    have hmap : (Subgroup.closure (Set.range x)).map η = ⊤ := by
      rw [MonoidHom.map_closure, ← Set.range_comp]
      have : η ∘ x = altThreeCycle := funext hxη
      rw [this, closure_altThreeCycle]
    have hsup : Subgroup.closure (Set.range x) ⊔ η.ker = ⊤ := by
      rw [← Subgroup.comap_map_eq, hmap, Subgroup.comap_top]
    have h := CFSG.ComponentClassification.CentralExtensions.commutator_sup_central
      (Subgroup.closure (Set.range x)) η.ker hK
    rw [hsup, ← _root_.commutator_def, Group.IsPerfect.commutator_eq_top] at h
    exact eq_top_iff.mpr (h.le.trans (Subgroup.commutator_le_self _))
  set i₀ : Fin m := ⟨0, by omega⟩ with hi₀
  set i₁ : Fin m := ⟨1, by omega⟩ with hi₁
  have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  set z := (x i₀ * x i₁) ^ 2 with hzdef
  have hzij : ∀ i j, i ≠ j → (x i * x j) ^ 2 = z := fun i j hij =>
    lift_sq_eq η hη hK hK2' hxη hx3 hij h01
  have hz1 : z ≠ 1 := by
    intro hz
    have hcard := card_closure_le_of_carmichael m x hx3 (fun i j hij => by rw [hzij i j hij, hz])
    rw [hL, Subgroup.card_top] at hcard
    have hP2 : Nat.card P = Nat.card (alternatingGroup (Fin (m + 2))) * Nat.card η.ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup η.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective η hη).toEquiv]
    have hA : Nat.card (alternatingGroup (Fin (m + 2))) = (m + 2).factorial / 2 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    have hApos : 0 < (m + 2).factorial / 2 := by
      rw [← hA]
      exact Nat.card_pos
    rw [hP2, hA, hK2] at hcard
    omega
  have hk : (x i₀ * x i₁)⁻¹ * y ∈ η.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, hxη, hxη, hy, inv_mul_cancel]
  obtain ⟨k, hkdef⟩ : ∃ k : P, k = (x i₀ * x i₁)⁻¹ * y := ⟨_, rfl⟩
  rw [← hkdef] at hk
  have hk2 : k ^ 2 = 1 := by
    have h1 := orderOf_dvd_natCard (⟨k, hk⟩ : η.ker)
    rw [hK2, Subgroup.orderOf_mk] at h1
    exact orderOf_dvd_iff_pow_eq_one.mp h1
  have hkc : (x i₀ * x i₁) * k = k * (x i₀ * x i₁) :=
    (Subgroup.mem_center_iff.mp (hK hk) (x i₀ * x i₁))
  have hyk : y = (x i₀ * x i₁) * k := by rw [hkdef]; group
  intro hy2
  apply hz1
  rw [hyk] at hy2
  have hsq : ((x i₀ * x i₁) * k) ^ 2 = (x i₀ * x i₁) ^ 2 * k ^ 2 := by
    rw [sq, sq, sq]
    calc x i₀ * x i₁ * k * (x i₀ * x i₁ * k) = x i₀ * x i₁ * (k * (x i₀ * x i₁)) * k := by
          group
      _ = x i₀ * x i₁ * ((x i₀ * x i₁) * k) * k := by rw [hkc]
      _ = x i₀ * x i₁ * (x i₀ * x i₁) * (k * k) := by group
  rw [hsq, hk2, mul_one] at hy2
  exact hy2

theorem isConj_dt {m : ℕ} (hm : 4 ≤ m) {a b c d : Fin (m + 2)} (h : [a, b, c, d].Nodup)
    (hmem : swap a b * swap c d ∈ alternatingGroup (Fin (m + 2))) :
    IsConj (⟨swap a b * swap c d, hmem⟩ : alternatingGroup (Fin (m + 2)))
      (altThreeCycle (⟨0, by omega⟩ : Fin m) * altThreeCycle (⟨1, by omega⟩ : Fin m)) := by
  have h01 : (⟨0, by omega⟩ : Fin m) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have hnd : [(0 : Fin (m + 2)), (⟨0, by omega⟩ : Fin m).addNat 2, 1,
      (⟨1, by omega⟩ : Fin m).addNat 2].Nodup := by
    have e0 : (⟨0, by omega⟩ : Fin m).addNat 2 = (⟨2, by omega⟩ : Fin (m + 2)) := Fin.ext rfl
    have e1 : (⟨1, by omega⟩ : Fin m).addNat 2 = (⟨3, by omega⟩ : Fin (m + 2)) := Fin.ext rfl
    have e2 : (1 : Fin (m + 2)) = (⟨1, by omega⟩ : Fin (m + 2)) := Fin.ext (Fin.val_one _)
    rw [e0, e1, e2]
    simp [List.nodup_cons, Fin.ext_iff]
  apply alternatingGroup.isConj_of
  · rw [Equiv.Perm.isConj_iff_cycleType_eq]
    change (swap a b * swap c d).cycleType = ((altThreeCycle (⟨0, by omega⟩ : Fin m) *
      altThreeCycle (⟨1, by omega⟩ : Fin m) : alternatingGroup (Fin (m + 2))) :
        Perm (Fin (m + 2))).cycleType
    rw [coe_altThreeCycle_mul h01, cycleType_swap_mul_swap_of_nodup h,
      cycleType_swap_mul_swap_of_nodup hnd]
  · change (swap a b * swap c d).support.card + 2 ≤ Fintype.card (Fin (m + 2))
    rw [← Equiv.Perm.sum_cycleType, cycleType_swap_mul_swap_of_nodup h, Fintype.card_fin]
    simp
    omega

theorem sq_ne_one_of_map_eq_dt [Group.IsPerfect P] {m : ℕ} (hm : 4 ≤ m)
    (η : P →* alternatingGroup (Fin (m + 2))) (hη : Function.Surjective η)
    (hK : η.ker ≤ Subgroup.center P) (hK2 : Nat.card η.ker = 2) {a b c d : Fin (m + 2)}
    (h : [a, b, c, d].Nodup) (hmem : swap a b * swap c d ∈ alternatingGroup (Fin (m + 2)))
    {y : P} (hy : η y = ⟨swap a b * swap c d, hmem⟩) : y ^ 2 ≠ 1 := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_dt hm h hmem)
  obtain ⟨ĝ, hĝ⟩ := hη g
  have h1 : η (ĝ * y * ĝ⁻¹) =
      altThreeCycle (⟨0, by omega⟩ : Fin m) * altThreeCycle (⟨1, by omega⟩ : Fin m) := by
    rw [map_mul, map_mul, map_inv, hĝ, hy, hg]
  have h2 := sq_ne_one_of_lift_c01 (by omega) η hη hK hK2 h1
  intro hy2
  apply h2
  rw [conj_pow, hy2, mul_one, mul_inv_cancel]

end CFSG.ComponentClassification.GSThmB.Cov
