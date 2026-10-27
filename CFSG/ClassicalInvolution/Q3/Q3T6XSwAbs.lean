module

public import CFSG.ClassicalInvolution.Q3.Q3T6BSubN
public import CFSG.ClassicalInvolution.Q3.Q3T6BOddFix

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6X

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3.Q3T6B

section Join

variable {X : Type} [Group X] [Finite X]

theorem isPGroup_sup_of_commutes {A B : Subgroup X} (hA : IsPGroup 2 A) (hB : IsPGroup 2 B)
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : IsPGroup 2 (A ⊔ B : Subgroup X) := by
  have hAc : A ≤ Subgroup.centralizer (B : Set X) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (h a ha b hb).symm
  have hAN := hAc.trans (Subgroup.centralizer_le_normalizer (B : Set X))
  rintro ⟨x, hx⟩
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right A B hAN] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  obtain ⟨m, hm⟩ := hA ⟨a, ha⟩
  obtain ⟨n, hn⟩ := hB ⟨b, hb⟩
  refine ⟨m + n, ?_⟩
  have ham : a ^ 2 ^ m = 1 := congrArg Subtype.val hm
  have hbn : b ^ 2 ^ n = 1 := congrArg Subtype.val hn
  apply Subtype.ext
  show (a * b) ^ 2 ^ (m + n) = 1
  have hcomm : Commute a b := h a ha b hb
  rw [hcomm.mul_pow]
  have h1 : a ^ 2 ^ (m + n) = 1 := by rw [pow_add, pow_mul, ham, one_pow]
  have h2 : b ^ 2 ^ (m + n) = 1 := by rw [add_comm, pow_add, pow_mul, hbn, one_pow]
  rw [h1, h2, one_mul]

theorem isPGroup_iSup_of_commutes {ι : Type*} [Finite ι] (H : ι → Subgroup X)
    (hH : ∀ i, IsPGroup 2 (H i))
    (hc : ∀ i j, i ≠ j → ∀ a ∈ H i, ∀ b ∈ H j, a * b = b * a) :
    IsPGroup 2 (⨆ i, H i : Subgroup X) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have key : ∀ s : Finset ι, IsPGroup 2 (⨆ i ∈ s, H i : Subgroup X) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have h0 : (⨆ i ∈ (∅ : Finset ι), H i : Subgroup X) = ⊥ := by simp
      rw [h0]
      exact IsPGroup.of_card (n := 0) (by simp)
    | insert j s hj ih =>
      rw [Finset.iSup_insert]
      refine isPGroup_sup_of_commutes (hH j) ih ?_
      intro a ha b hb
      have hle : (⨆ i ∈ s, H i : Subgroup X) ≤ Subgroup.centralizer (H j : Set X) := by
        refine iSup₂_le fun i hi => ?_
        intro y hy
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        exact hc j i (fun h => hj (h ▸ hi)) x hx y hy
      have hb' := Subgroup.mem_centralizer_iff.mp (hle hb)
      exact hb' a ha
  have e : (⨆ i ∈ (Finset.univ : Finset ι), H i : Subgroup X) = ⨆ i, H i :=
    le_antisymm (iSup₂_le fun i _ => le_iSup H i)
      (iSup_le fun i => le_iSup₂ (f := fun i (_ : i ∈ (Finset.univ : Finset ι)) => H i) i
        (Finset.mem_univ i))
  rw [← e]
  exact key Finset.univ

end Join

section Abs

variable {X : Type} [Group X] [Finite X]

theorem isSubnormal_of_le_of_le' {K C M : Subgroup X} (h : IsSubnormal K C) (hM : M ≤ C)
    (hKM : K ≤ M) : IsSubnormal K M := by
  have h1 := isSubnormal_subgroupOf h M
  rw [Subgroup.subgroupOf_eq_top.mpr hM] at h1
  have h2 := CFSG.ComponentClassification.Components.chain_map M.subtype h1
  rw [Subgroup.map_top, Subgroup.range_subtype, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr hKM] at h2
  exact h2

theorem swap_contra {Kb Db W Qb : Subgroup X} {ub δb : X} {𝒯 : Set (Subgroup X)}
    (hKD : Kb ≤ Db) (hsub : IsSubnormal Kb Db)
    (hKgen : Kb ≤ Subgroup.closure {g : X | g ∈ Kb ∧ Odd (orderOf g)})
    (hub : ub ∈ Kb) (hub2 : ub * ub = 1) (hub1 : ub ≠ 1)
    (huniq : ∀ x ∈ Kb, x * x = 1 → x = 1 ∨ x = ub)
    (hQ : Qb ∈ 𝒯) (hperm : ∀ k ∈ Kb, conjSub k Qb ∈ 𝒯)
    (hWnorm : ∀ k ∈ Kb, ∀ w ∈ W, k * w * k⁻¹ ∈ W)
    (hWfix : ∀ w ∈ W, ∀ Y ∈ 𝒯, conjSub w Y = Y) (hW2 : IsPGroup 2 W)
    (hQu : conjSub ub Qb ≠ Qb)
    (hδW : δb ∈ W) (hδD : δb ∈ Db) (hΘ : ∀ Y ∈ 𝒯, (∃ y ∈ Y, δb * y ≠ y * δb) →
      Y = Qb ∨ Y = conjSub ub Qb)
    (hΘQ : ∃ y ∈ Qb, δb * y ≠ y * δb) : False := by
  classical
  set A : Subgroup X := W ⊓ Db with hA
  have hA2 : IsPGroup 2 A := hW2.to_le inf_le_left
  have hfwd : ∀ k ∈ Kb, ∀ a ∈ A, k * a * k⁻¹ ∈ A := fun k hk a ha =>
    ⟨hWnorm k hk a ha.1, Db.mul_mem (Db.mul_mem (hKD hk) ha.2) (Db.inv_mem (hKD hk))⟩
  have hKA : Kb ≤ Subgroup.normalizer (A : Set X) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro a
    refine ⟨fun ha => hfwd k hk a ha, fun ha => ?_⟩
    have := hfwd k⁻¹ (Kb.inv_mem hk) _ ha
    simpa [mul_assoc] using this
  have hM : ∀ m ∈ Kb ⊔ A, ∃ k ∈ Kb, ∃ a ∈ A, m = k * a := by
    intro m hm
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right Kb A hKA] at hm
    obtain ⟨k, hk, a, ha, hka⟩ := hm
    exact ⟨k, hk, a, ha, hka.symm⟩
  have hsub' : IsSubnormal Kb (Kb ⊔ A) :=
    isSubnormal_of_le_of_le' hsub (sup_le hKD inf_le_right) le_sup_left
  have hAN : A ≤ Subgroup.normalizer (Kb : Set X) :=
    subnormal_odd_normalizer hKgen hA2 hsub' le_sup_right hM
  have hubc : ∀ k ∈ Kb, k * ub = ub * k := by
    intro k hk
    have h1 : k * ub * k⁻¹ ∈ Kb := Kb.mul_mem (Kb.mul_mem hk hub) (Kb.inv_mem hk)
    have h2 : (k * ub * k⁻¹) * (k * ub * k⁻¹) = 1 := by
      calc (k * ub * k⁻¹) * (k * ub * k⁻¹) = k * (ub * ub) * k⁻¹ := by group
        _ = 1 := by rw [hub2]; group
    rcases huniq _ h1 h2 with h | h
    · exfalso
      apply hub1
      have : ub = k⁻¹ * (k * ub * k⁻¹) * k := by group
      rw [this, h]
      group
    · calc k * ub = (k * ub * k⁻¹) * k := by group
        _ = ub * k := by rw [h]
  have hcomm : ∀ a ∈ A, ∀ k ∈ Kb, a * k = k * a := by
    intro a ha k hk
    have h1 : a * k * a⁻¹ ∈ Kb := (Subgroup.mem_normalizer_iff.mp (hAN ha) k).mp hk
    have hcK : a * k * a⁻¹ * k⁻¹ ∈ Kb := Kb.mul_mem h1 (Kb.inv_mem hk)
    have hcA : a * k * a⁻¹ * k⁻¹ ∈ A := by
      have h2 : k * a⁻¹ * k⁻¹ ∈ A := hfwd k hk a⁻¹ (A.inv_mem ha)
      have := A.mul_mem ha h2
      simpa [mul_assoc] using this
    have hc1 : a * k * a⁻¹ * k⁻¹ = 1 := by
      by_contra hne
      obtain ⟨n, hn⟩ := CFSG.ClassicalInvolution.exists_pow_orderOf_eq_two (P := ↥A) hA2
        (x := ⟨_, hcA⟩) (fun h => hne (congrArg Subtype.val h))
      have hn' : orderOf ((a * k * a⁻¹ * k⁻¹) ^ n) = 2 := by
        have := Subgroup.orderOf_coe ((⟨_, hcA⟩ : ↥A) ^ n)
        rw [← this] at hn
        exact hn
      have hxsq : (a * k * a⁻¹ * k⁻¹) ^ n * (a * k * a⁻¹ * k⁻¹) ^ n = 1 := by
        have := pow_orderOf_eq_one ((a * k * a⁻¹ * k⁻¹) ^ n)
        rwa [hn', pow_two] at this
      have hx1 : (a * k * a⁻¹ * k⁻¹) ^ n ≠ 1 := fun h => by
        have := orderOf_eq_one_iff.mpr h
        omega
      have hxK : (a * k * a⁻¹ * k⁻¹) ^ n ∈ Kb := Kb.pow_mem hcK n
      have hxW : (a * k * a⁻¹ * k⁻¹) ^ n ∈ W := W.pow_mem hcA.1 n
      rcases huniq _ hxK hxsq with h | h
      · exact hx1 h
      · rw [h] at hxW
        exact hQu (hWfix ub hxW Qb hQ)
    exact commutatorElement_eq_one_iff_mul_comm.mp (by rw [commutatorElement_def]; exact hc1)
  have hδk : ∀ k ∈ Kb, δb * k = k * δb := fun k hk => hcomm δb ⟨hδW, hδD⟩ k hk
  have hfix : ∀ k ∈ Kb, Odd (orderOf k) → conjSub k Qb = Qb := by
    intro k hk hodd
    have hkT : conjSub k Qb ∈ 𝒯 := hperm k hk
    have hkΘ : ∃ y ∈ conjSub k Qb, δb * y ≠ y * δb := by
      obtain ⟨y, hy, hne⟩ := hΘQ
      refine ⟨k * y * k⁻¹, conj_mem_conjSub hy, fun h => hne ?_⟩
      have hk' : δb * k = k * δb := hδk k hk
      have e1 : δb * (k * y * k⁻¹) = k * (δb * y) * k⁻¹ := by
        calc δb * (k * y * k⁻¹) = (δb * k) * y * k⁻¹ := by group
          _ = (k * δb) * y * k⁻¹ := by rw [hk']
          _ = k * (δb * y) * k⁻¹ := by group
      have e2 : (k * y * k⁻¹) * δb = k * (y * δb) * k⁻¹ := by
        calc (k * y * k⁻¹) * δb = k * y * (k⁻¹ * δb) := by group
          _ = k * y * (δb * k⁻¹) := by
            rw [show k⁻¹ * δb = δb * k⁻¹ by
              calc k⁻¹ * δb = k⁻¹ * (δb * k) * k⁻¹ := by group
                _ = k⁻¹ * (k * δb) * k⁻¹ := by rw [hk']
                _ = δb * k⁻¹ := by group]
          _ = k * (y * δb) * k⁻¹ := by group
      rw [e1, e2] at h
      have := mul_left_cancel (mul_right_cancel h)
      exact this
    rcases hΘ _ hkT hkΘ with h | h
    · exact h
    · exfalso
      have hkub : k * ub = ub * k := hubc k hk
      have h1 : conjSub (k * k) Qb = Qb := by
        calc conjSub (k * k) Qb = conjSub k (conjSub k Qb) := conjSub_mul k k Qb
          _ = conjSub k (conjSub ub Qb) := by rw [h]
          _ = conjSub (k * ub) Qb := (conjSub_mul k ub Qb).symm
          _ = conjSub (ub * k) Qb := by rw [hkub]
          _ = conjSub ub (conjSub k Qb) := conjSub_mul ub k Qb
          _ = conjSub ub (conjSub ub Qb) := by rw [h]
          _ = conjSub (ub * ub) Qb := (conjSub_mul ub ub Qb).symm
          _ = Qb := by rw [hub2, conjSub_one]
      have hkk : k * k ∈ Subgroup.normalizer (Qb : Set X) :=
        mem_normalizer_iff_conjSub_eq.mpr h1
      obtain ⟨j, hj⟩ := hodd
      have hkpow : k = (k * k) ^ (j + 1) := by
        calc k = k ^ (orderOf k) * k := by rw [pow_orderOf_eq_one, one_mul]
          _ = k ^ (orderOf k + 1) := (pow_succ k (orderOf k)).symm
          _ = k ^ (2 * (j + 1)) := by congr 1; omega
          _ = (k * k) ^ (j + 1) := by rw [pow_mul, pow_two]
      have hkN : k ∈ Subgroup.normalizer (Qb : Set X) := by
        rw [hkpow]
        exact (Subgroup.normalizer (Qb : Set X)).pow_mem hkk _
      have : conjSub k Qb = Qb := mem_normalizer_iff_conjSub_eq.mp hkN
      rw [this] at h
      exact hQu h.symm
  have hKN : Kb ≤ Subgroup.normalizer (Qb : Set X) := by
    refine hKgen.trans ((Subgroup.closure_le _).mpr fun g hg => ?_)
    exact mem_normalizer_iff_conjSub_eq.mpr (hfix g hg.1 hg.2)
  exact hQu (mem_normalizer_iff_conjSub_eq.mp (hKN hub))

end Abs

end CFSG.ClassicalInvolution.Q3.Q3T6X
