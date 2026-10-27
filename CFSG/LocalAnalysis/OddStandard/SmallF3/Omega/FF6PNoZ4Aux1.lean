module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PD8

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

theorem ffOutFF6PNoZ4_conj_cases {G : Type*} [Group G] {z c : G} (hz4 : z ^ 4 = 1)
    (hz2 : z ^ 2 ≠ 1) (hc : c * z * c⁻¹ ∈ Subgroup.zpowers z) :
    c * z * c⁻¹ = z ∨ c * z * c⁻¹ = z * z ^ 2 := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc
  have hmod : z ^ (k % 4) = c * z * c⁻¹ := (zpow_eq_zpow_emod' k hz4).symm.trans hk
  have hcases : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by
    have h1 := Int.emod_nonneg k (by norm_num : (4 : ℤ) ≠ 0)
    have h2 := Int.emod_lt_of_pos k (by norm_num : (0 : ℤ) < 4)
    omega
  rcases hcases with h | h | h | h
  · exfalso
    have hz1 : c * z * c⁻¹ = 1 := by rw [← hmod, h, zpow_zero]
    have hz_eq1 : z = 1 := by
      calc z = c⁻¹ * (c * z * c⁻¹) * c := by group
        _ = c⁻¹ * 1 * c := by rw [hz1]
        _ = 1 := by group
    exact hz2 (by rw [hz_eq1]; simp)
  · left
    rw [← hmod, h, zpow_one]
  · exfalso
    have hz' : c * z * c⁻¹ = z ^ 2 := by rw [← hmod, h]; simp
    have h1 : c * z ^ 2 * c⁻¹ = 1 := by
      rw [show c * z ^ 2 * c⁻¹ = (c * z * c⁻¹) ^ 2 from (conj_pow (i := 2)).symm, hz',
        show (z ^ 2) ^ 2 = z ^ 4 from by group, hz4]
    have hz2eq : z ^ 2 = 1 := by
      calc z ^ 2 = c⁻¹ * (c * z ^ 2 * c⁻¹) * c := by group
        _ = 1 := by rw [h1]; group
    exact hz2 hz2eq
  · right
    rw [← hmod, h]
    show z ^ ((3 : ℕ) : ℤ) = z * z ^ 2
    rw [zpow_natCast, show (3 : ℕ) = 1 + 2 from rfl, pow_add, pow_one]

theorem ffOutFF6PNoZ4_sq_conj {G : Type*} [Group G] {z c : G} (hz2 : z ^ 2 ≠ 1)
    (hz4 : z ^ 4 = 1) (hc : c * z * c⁻¹ ∈ Subgroup.zpowers z) :
    c * z ^ 2 * c⁻¹ = z ^ 2 := by
  rcases ffOutFF6PNoZ4_conj_cases hz4 hz2 hc with h | h
  · rw [show c * z ^ 2 * c⁻¹ = (c * z * c⁻¹) ^ 2 from (conj_pow (i := 2)).symm, h]
  · rw [show c * z ^ 2 * c⁻¹ = (c * z * c⁻¹) ^ 2 from (conj_pow (i := 2)).symm, h]
    calc (z * z ^ 2) ^ 2 = z ^ 2 * z ^ 4 := by group
      _ = z ^ 2 := by rw [hz4, mul_one]

theorem ffOutFF6PNoZ4_sq_of_dich {G : Type*} [Group G] {z p : G} (hz2 : z ^ 2 ≠ 1)
    (hz4 : z ^ 4 = 1)
    (hp : MulAut.conj p z = z ∨ MulAut.conj p z = z * z ^ 2) :
    MulAut.conj p (z ^ 2) = z ^ 2 := by
  rw [MulAut.conj_apply] at hp
  have hmem : p * z * p⁻¹ ∈ Subgroup.zpowers z := by
    rcases hp with h | h
    · rw [h]; exact Subgroup.mem_zpowers z
    · rw [h, show z * z ^ 2 = z ^ 3 from by group]
      exact Subgroup.npow_mem_zpowers z 3
  rw [MulAut.conj_apply]
  exact ffOutFF6PNoZ4_sq_conj hz2 hz4 hmem

theorem ffOutFF6PNoZ4_flip_iff_not {G : Type*} [Group G] {z p : G} (hz2 : z ^ 2 ≠ 1)
    (h : MulAut.conj p z = z ∨ MulAut.conj p z = z * z ^ 2) :
    MulAut.conj p z = z * z ^ 2 ↔ ¬ MulAut.conj p z = z := by
  constructor
  · intro hf hn
    exact hz2 (mul_left_cancel (show z * z ^ 2 = z * 1 by rw [← hf, hn, mul_one]))
  · intro hn
    rcases h with h | h
    · exact absurd h hn
    · exact h

theorem ffOutFF6PNoZ4_parity_mul {G : Type*} [Group G] {z p q : G} (hz2 : z ^ 2 ≠ 1)
    (hz4 : z ^ 4 = 1)
    (hp : MulAut.conj p z = z ∨ MulAut.conj p z = z * z ^ 2)
    (hq : MulAut.conj q z = z ∨ MulAut.conj q z = z * z ^ 2) :
    MulAut.conj (p * q) z = z ↔ (MulAut.conj p z = z ↔ MulAut.conj q z = z) := by
  have hzv : z * z ^ 2 ≠ z := fun h => hz2 (mul_left_cancel (by rw [h, mul_one]))
  have hpv : MulAut.conj p (z ^ 2) = z ^ 2 := ffOutFF6PNoZ4_sq_of_dich hz2 hz4 hp
  have hpq : MulAut.conj (p * q) z = MulAut.conj p (MulAut.conj q z) := by
    rw [map_mul]; rfl
  rw [hpq]
  rcases hp with hp | hp <;> rcases hq with hq | hq
  · rw [hq, hp]; simp
  · have hL : MulAut.conj p (MulAut.conj q z) = z * z ^ 2 := by
      rw [hq, map_mul, hp, hpv]
    rw [hL, hp, hq]; simp [hzv]
  · have hL : MulAut.conj p (MulAut.conj q z) = z * z ^ 2 := by rw [hq, hp]
    rw [hL, hp, hq]; simp [hzv]
  · have hL : MulAut.conj p (MulAut.conj q z) = z := by
      rw [hq, map_mul, hp, hpv]
      calc (z * z ^ 2) * z ^ 2 = z * z ^ 4 := by group
        _ = z := by rw [hz4, mul_one]
    rw [hL, hp, hq]; simp [hzv]

theorem ffOutFF6PNoZ4_conj_inv_iff {G : Type*} [Group G] {z h : G} :
    MulAut.conj h⁻¹ z = z ↔ MulAut.conj h z = z := by
  rw [map_inv]
  constructor
  · intro hh
    calc MulAut.conj h z = MulAut.conj h ((MulAut.conj h)⁻¹ z) := by rw [hh]
      _ = z := MulAut.apply_inv_self G (MulAut.conj h) z
  · intro hh
    apply (MulAut.conj h).injective
    rw [MulAut.apply_inv_self]
    exact hh.symm

theorem ffOutFF6PNoZ4_parity_conj {M G : Type*} [Group M] [Group G] (ι : M →* G) {z : G}
    (P : Subgroup M) (hz2 : z ^ 2 ≠ 1) (hz4 : z ^ 4 = 1)
    (hdich : ∀ p ∈ P, MulAut.conj (ι p) z = z ∨ MulAut.conj (ι p) z = z * z ^ 2)
    {h p : M} (hh : h ∈ P) (hp : p ∈ P) :
    MulAut.conj (ι (h * p * h⁻¹)) z = z ↔ MulAut.conj (ι p) z = z := by
  have hpm : h * p ∈ P := P.mul_mem hh hp
  have hih : h⁻¹ ∈ P := P.inv_mem hh
  have h1 : MulAut.conj (ι (h * p)) z = z ↔
      (MulAut.conj (ι h) z = z ↔ MulAut.conj (ι p) z = z) := by
    rw [map_mul]
    exact ffOutFF6PNoZ4_parity_mul hz2 hz4 (hdich h hh) (hdich p hp)
  have h2 : MulAut.conj (ι ((h * p) * h⁻¹)) z = z ↔
      (MulAut.conj (ι (h * p)) z = z ↔ MulAut.conj (ι h⁻¹) z = z) := by
    rw [map_mul]
    exact ffOutFF6PNoZ4_parity_mul hz2 hz4 (hdich (h * p) hpm) (hdich h⁻¹ hih)
  have hinv : (MulAut.conj (ι h⁻¹) z = z) ↔ (MulAut.conj (ι h) z = z) := by
    rw [map_inv]; exact ffOutFF6PNoZ4_conj_inv_iff
  rw [h1, hinv] at h2
  exact h2.trans (by tauto)

theorem ffOutFF6PNoZ4_comm_of_conj {G : Type*} [Group G] {a z : G} (h : MulAut.conj a z = z) :
    z * a = a * z := by
  rw [MulAut.conj_apply] at h
  calc z * a = (a * z * a⁻¹) * a := by rw [h]
    _ = a * z := by group

theorem ffOutFF6PNoZ4_even_symmDiff :
    ∀ (J : Finset (Fin 5)) (i : Fin 5), Even J.card → i ∈ J → i ≠ 4 →
      Even (symmDiff J {i, 4}).card ∧
        ((symmDiff J {i, 4}).erase 4).card = (J.erase 4).card - 1 := by
  decide +kernel

theorem ffOutFF6PNoZ4_rot_act :
    ∀ (i : Fin 5), i ∈ ({0, 1, 2, 3} : Finset (Fin 5)) →
      ffAct (ffRot ^ i.val) {0, 4} = {i, 4} := by
  decide +kernel

theorem ffOutFF6PNoZ4_four_mem_symmDiff (J : Finset (Fin 5)) (i : Fin 5) :
    ((4 : Fin 5) ∈ symmDiff J {i, 4} ↔ (4 : Fin 5) ∉ J) := by
  rw [Finset.mem_symmDiff]
  simp

theorem ffOutFF6PNoZ4_mem0123 :
    ∀ i : Fin 5, i ≠ 4 → i ∈ ({0, 1, 2, 3} : Finset (Fin 5)) := by
  decide +kernel

theorem ffOutFF6PNoZ4_ne_four :
    ∀ i : Fin 5, i ∈ ({0, 1, 2, 3} : Finset (Fin 5)) → i ≠ 4 := by
  decide +kernel

theorem ffOutFF6PNoZ4_even_pair (i : Fin 5) (hi : i ≠ 4) :
    Even ({i, 4} : Finset (Fin 5)).card := by
  rw [Finset.card_insert_of_notMem (by simpa [Finset.mem_singleton] using hi),
    Finset.card_singleton]
  exact ⟨1, rfl⟩

theorem ffOutFF6PNoZ4_master (f : Finset (Fin 5) → Prop) {β : Prop} (h0 : ¬ f ∅)
    (hbasis : ∀ i : Fin 5, i ∈ ({0, 1, 2, 3} : Finset (Fin 5)) → (f {i, 4} ↔ β))
    (hstep : ∀ (J : Finset (Fin 5)) (i : Fin 5), Even J.card → i ∈ J → i ≠ 4 →
      (f (symmDiff J {i, 4}) ↔ ¬ (f J ↔ f {i, 4}))) :
    ∀ J : Finset (Fin 5), Even J.card → (f J ↔ ((4 : Fin 5) ∈ J ∧ β)) := by
  have main : ∀ n, ∀ J : Finset (Fin 5), Even J.card → (J.erase 4).card = n →
      (f J ↔ ((4 : Fin 5) ∈ J ∧ β)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro J hJ hcard
      by_cases hempty : (J.erase (4 : Fin 5)) = ∅
      · rcases (Finset.erase_eq_empty_iff J (4 : Fin 5)).mp hempty with hJ0 | hJ4
        · subst hJ0
          simp only [Finset.notMem_empty, false_and]
          exact ⟨fun hf => (h0 hf).elim, fun h => h.elim⟩
        · exfalso
          obtain ⟨k, hk⟩ := hJ
          rw [hJ4] at hk
          simp only [Finset.card_singleton] at hk
          omega
      · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
        have hJi : i ∈ J := Finset.mem_of_mem_erase hi
        have hi4 : i ≠ 4 := Finset.ne_of_mem_erase hi
        have hfacts := ffOutFF6PNoZ4_even_symmDiff J i hJ hJi hi4
        set K : Finset (Fin 5) := symmDiff J {i, 4} with hK
        have hKeven : Even K.card := hfacts.1
        have hKcard : (K.erase 4).card = n - 1 := by rw [hK, hfacts.2, hcard]
        have hnpos : 0 < n := by
          have hpos : 0 < (J.erase (4 : Fin 5)).card :=
            Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hempty)
          omega
        have hlt : (K.erase 4).card < n := by omega
        have ihK : f K ↔ ((4 : Fin 5) ∈ K ∧ β) := ih (K.erase 4).card hlt K hKeven rfl
        have hi0123 : i ∈ ({0, 1, 2, 3} : Finset (Fin 5)) :=
          ffOutFF6PNoZ4_mem0123 i hi4
        have hstepi : f K ↔ ¬ (f J ↔ f {i, 4}) := by
          rw [hK]; exact hstep J i hJ hJi hi4
        have h4K : ((4 : Fin 5) ∈ K ↔ (4 : Fin 5) ∉ J) := by
          rw [hK]; exact ffOutFF6PNoZ4_four_mem_symmDiff J i
        rw [ihK, hbasis i hi0123, h4K] at hstepi
        tauto
  intro J hJ
  exact main (J.erase 4).card J hJ rfl

end CFSG.OddStandard.SmallF3.Omega
