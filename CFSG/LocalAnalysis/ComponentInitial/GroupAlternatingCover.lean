module

public import CFSG.LocalAnalysis.ComponentClassification.CentralExtensions
public import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCoverLocal
public import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCoverPerm

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Equiv Equiv.Perm

variable {P : Type*} [Group P]

theorem sq_sq_lift_eq_one [Finite P] {m : ℕ} (η : P →* alternatingGroup (Fin (m + 2)))
    (hK : η.ker ≤ Subgroup.center P) (hK2 : IsPGroup 2 η.ker) {i j : Fin m} (hij : i ≠ j)
    {xi xj : P} (hxi : η xi = altThreeCycle i) (hxj : η xj = altThreeCycle j)
    (hxi3 : xi ^ 3 = 1) (hxj3 : xj ^ 3 = 1) : ((xi * xj) ^ 2) ^ 2 = 1 := by
  classical
  set L := Subgroup.closure ({xi, xj} : Set P)
  set a : L := ⟨xi, Subgroup.subset_closure (Set.mem_insert _ _)⟩
  set b : L := ⟨xj, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩
  set ψ := η.comp L.subtype
  have hψa : ψ a = altThreeCycle i := hxi
  have hψb : ψ b = altThreeCycle j := hxj
  have hgen : Subgroup.closure {a, b} = ⊤ := by
    have h := Subgroup.closure_closure_coe_preimage (k := ({xi, xj} : Set P))
    convert h using 2
    ext g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage]
    exact ⟨fun h => h.imp (fun h' => by rw [h']) (fun h' => by rw [h']),
      fun h => h.imp (fun h' => Subtype.ext h') (fun h' => Subtype.ext h')⟩
  have hDZ : ψ.ker ≤ Subgroup.center L := fun g hg =>
    Subgroup.mem_center_iff.mpr fun h => Subtype.ext (Subgroup.mem_center_iff.mp (hK hg) h)
  have hD2 : IsPGroup 2 ψ.ker := fun g => by
    obtain ⟨k, hk⟩ := hK2 ⟨((g : L) : P), g.2⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
  have hab : ψ (a * b) = altThreeCycle i * altThreeCycle j := by rw [map_mul, hψa, hψb]
  have hba : ψ (b * a) = altThreeCycle j * altThreeCycle i := by rw [map_mul, hψa, hψb]
  have hrange : ψ.range = altPairGroup i j := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, MonoidHom.map_closure, altPairGroup]
    congr 1
    ext w
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range,
      Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor
    · rintro ⟨g, rfl | rfl, rfl⟩
      · exact Or.inl hxi.symm
      · exact Or.inr hxj.symm
    · rintro (h | h)
      · exact ⟨xi, Or.inl rfl, h.symm ▸ hxi⟩
      · exact ⟨xj, Or.inr rfl, h.symm ▸ hxj⟩
  have hS3 : ((altKleinFour hij).comap ψ).index = 3 := by
    rw [Subgroup.index_comap, hrange]
    have h := Subgroup.relIndex_mul_card (altKleinFour hij) (altPairGroup i j)
    rw [inf_of_le_left (altKleinFour_le hij), card_altKleinFour hij,
      card_altPairGroup hij] at h
    omega
  have hcard := card_ker_le_two_of_index_three (x := a) (y := b)
    (Subtype.ext (by simpa using hxi3)) (Subtype.ext (by simpa using hxj3)) hgen ψ hDZ hD2
    (W := altKleinFour hij) (by rw [hab]; exact Or.inr (Or.inl rfl))
    (by rw [hba]; exact Or.inr (Or.inr (Or.inl rfl)))
    (fun w hw => by rw [hab, hba]; exact hw)
    (fun w hw => by
      rcases hw with rfl | rfl | rfl | rfl
      · exact one_pow 2
      · exact altThreeCycle_mul_sq hij
      · exact altThreeCycle_mul_sq (Ne.symm hij)
      · rw [sq]
        have t := altThreeCycle_mul_comm hij
        have h1 := altThreeCycle_mul_self_mul hij
        have h2 := altThreeCycle_mul_self_mul (Ne.symm hij)
        set w1 := altThreeCycle i * altThreeCycle j
        set w2 := altThreeCycle j * altThreeCycle i
        calc w1 * w2 * (w1 * w2) = w1 * (w2 * w1) * w2 := by group
          _ = w1 * (w1 * w2) * w2 := by rw [← t]
          _ = w1 * w1 * (w2 * w2) := by group
          _ = 1 := by rw [h1, h2, one_mul])
    hS3
  have htK : (a * b) ^ 2 ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_pow, hab, altThreeCycle_mul_sq hij]
  set t : ψ.ker := ⟨(a * b) ^ 2, htK⟩
  have ht2 : t ^ 2 = 1 := by
    have hpow := pow_card_eq_one' (G := ψ.ker) (x := t)
    have hpos : 0 < Nat.card ψ.ker := Nat.card_pos
    interval_cases h : Nat.card ψ.ker
    · rw [pow_one] at hpow
      rw [hpow, one_pow]
    · exact hpow
  have := congrArg (fun g : ψ.ker => ((g : L) : P)) ht2
  simpa [t] using this

theorem lift_sq_eq {m : ℕ} (η : P →* alternatingGroup (Fin (m + 2))) (hη : Function.Surjective η)
    (hK : η.ker ≤ Subgroup.center P) (hK2 : IsPGroup 2 η.ker) {x : Fin m → P}
    (hxη : ∀ i, η (x i) = altThreeCycle i) (hx3 : ∀ i, x i ^ 3 = 1) {i j i' j' : Fin m}
    (hij : i ≠ j) (hij' : i' ≠ j') : (x i * x j) ^ 2 = (x i' * x j') ^ 2 := by
  obtain ⟨σ, hσ, h0, h1, hσab⟩ := exists_mem_alternatingGroup_pair (addNat_two_ne_zero i)
    (addNat_two_ne_one i) (addNat_two_ne_zero j) (addNat_two_ne_one j) (addNat_two_ne_zero i')
    (addNat_two_ne_one i') (addNat_two_ne_zero j') (addNat_two_ne_one j') (addNat_two_ne hij)
    (addNat_two_ne hij')
  obtain ⟨h, hh⟩ := hη ⟨σ, hσ⟩
  have hconj : ∀ k k' : Fin m, σ (k.addNat 2) = k'.addNat 2 → h * x k * h⁻¹ = x k' := by
    intro k k' hk
    refine eq_of_pow_three_eq_one_of_map_eq hK hK2 ?_ (hx3 k') ?_
    · rw [conj_pow, hx3, mul_one, mul_inv_cancel]
    · rw [map_mul, map_mul, map_inv, hh, hxη, hxη]
      exact Subtype.ext (conj_altThreeCyclePerm h0 h1 hk)
  have hcentral : ∀ k l : Fin m, k ≠ l → h * (x k * x l) ^ 2 * h⁻¹ = (x k * x l) ^ 2 := by
    intro k l hkl
    have hm : (x k * x l) ^ 2 ∈ Subgroup.center P := hK (by
      rw [MonoidHom.mem_ker, map_pow, map_mul, hxη, hxη, altThreeCycle_mul_sq hkl])
    rw [Subgroup.mem_center_iff.mp hm h, mul_inv_cancel_right]
  have hsq : ∀ k l : Fin m, h * (x k * x l) ^ 2 * h⁻¹ = (h * x k * h⁻¹ * (h * x l * h⁻¹)) ^ 2 := by
    intro k l
    simp only [sq]
    group
  have hswap : (x j' * x i') ^ 2 = (x i' * x j') ^ 2 := by
    have hm : (x i' * x j') ^ 2 ∈ Subgroup.center P := hK (by
      rw [MonoidHom.mem_ker, map_pow, map_mul, hxη, hxη, altThreeCycle_mul_sq hij'])
    have e : (x j' * x i') ^ 2 = (x i')⁻¹ * (x i' * x j') ^ 2 * x i' := by
      simp only [sq]
      group
    rw [e, mul_assoc, ← Subgroup.mem_center_iff.mp hm, inv_mul_cancel_left]
  rcases hσab with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [← hcentral i j hij, hsq, hconj i i' ha, hconj j j' hb]
  · rw [← hcentral i j hij, hsq, hconj i j' ha, hconj j i' hb, hswap]

theorem card_ker_le_two_of_alternating [Finite P] [Group.IsPerfect P] {m : ℕ} (hm : 3 ≤ m)
    (η : P →* alternatingGroup (Fin (m + 2))) (hη : Function.Surjective η)
    (hK : η.ker ≤ Subgroup.center P) (hK2 : IsPGroup 2 η.ker) : Nat.card η.ker ≤ 2 := by
  classical
  have hlift : ∀ i : Fin m, ∃ x : P, η x = altThreeCycle i ∧ x ^ 3 = 1 := fun i => by
    obtain ⟨y, hy⟩ := hη (altThreeCycle i)
    obtain ⟨x, hx, hx3⟩ := exists_lift_pow_three_eq_one hK hK2
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
    rw [hsup, ← commutator_def, Group.IsPerfect.commutator_eq_top] at h
    exact eq_top_iff.mpr (h.le.trans (Subgroup.commutator_le_self _))
  let i₀ : Fin m := ⟨0, by omega⟩
  let i₁ : Fin m := ⟨1, by omega⟩
  have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  set z := (x i₀ * x i₁) ^ 2 with hzdef
  have hzc : z ∈ Subgroup.center P := hK (by
    rw [MonoidHom.mem_ker, map_pow, map_mul, hxη, hxη, altThreeCycle_mul_sq h01])
  have hz2 : z ^ 2 = 1 := sq_sq_lift_eq_one η hK hK2 h01 (hxη i₀) (hxη i₁) (hx3 i₀) (hx3 i₁)
  have hzij : ∀ i j, i ≠ j → (x i * x j) ^ 2 = z := fun i j hij =>
    lift_sq_eq η hη hK hK2 hxη hx3 hij h01
  set K₀ := Subgroup.zpowers z
  have : K₀.Normal := ⟨fun k hk g => by
    obtain ⟨e, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    have hc := Subgroup.mem_center_iff.mp (Subgroup.zpow_mem _ hzc e) g
    rw [hc, mul_inv_cancel_right]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) e⟩
  have hcardQ : Nat.card (P ⧸ K₀) ≤ (m + 2).factorial / 2 := by
    have h := card_closure_le_of_carmichael m (QuotientGroup.mk' K₀ ∘ x)
      (fun i => by rw [Function.comp_apply, ← map_pow, hx3, map_one])
      (fun i j hij => by
        rw [Function.comp_apply, Function.comp_apply, ← map_mul, ← map_pow, hzij i j hij]
        exact (QuotientGroup.eq_one_iff z).mpr (Subgroup.mem_zpowers z))
    have hgen : Subgroup.closure (Set.range (QuotientGroup.mk' K₀ ∘ x)) = ⊤ := by
      rw [Set.range_comp, ← MonoidHom.map_closure, hL,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    rw [hgen, Subgroup.card_top] at h
    exact h
  have hP1 : Nat.card P = Nat.card (P ⧸ K₀) * Nat.card K₀ :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup K₀
  have hP2 : Nat.card P = Nat.card (alternatingGroup (Fin (m + 2))) * Nat.card η.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup η.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective η hη).toEquiv]
  have hA : Nat.card (alternatingGroup (Fin (m + 2))) = (m + 2).factorial / 2 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hApos : 0 < (m + 2).factorial / 2 := by
    rw [← hA]
    exact Nat.card_pos
  have hK₀ : Nat.card K₀ ≤ 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by norm_num) hz2
  have hle : (m + 2).factorial / 2 * Nat.card η.ker ≤ (m + 2).factorial / 2 * Nat.card K₀ := by
    calc (m + 2).factorial / 2 * Nat.card η.ker = Nat.card P := by rw [hP2, hA]
      _ = Nat.card (P ⧸ K₀) * Nat.card K₀ := hP1
      _ ≤ (m + 2).factorial / 2 * Nat.card K₀ := Nat.mul_le_mul_right _ hcardQ
  exact (Nat.le_of_mul_le_mul_left hle hApos).trans hK₀

theorem alternating_perfect_central_two_kernel_order_at_most_two {n : ℕ} (hn : 5 ≤ n)
    [Finite P] [Group.IsPerfect P] (η : P →* alternatingGroup (Fin n))
    (hη : Function.Surjective η) (hK : η.ker ≤ Subgroup.center P) (hK2 : IsPGroup 2 η.ker) :
    Nat.card η.ker ≤ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  exact card_ker_le_two_of_alternating (by omega) η hη hK hK2

end CFSG.LocalAnalysis.ComponentInitial
