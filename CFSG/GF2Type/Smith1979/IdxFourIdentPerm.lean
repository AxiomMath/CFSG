module

public import CFSG.GF2Type.Smith1979.IdxFourIdentMon
public import CFSG.GF2Type.Smith1979.IdxFourIdentLevi360

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.IdxFour

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.Case25.U43Weights

@[expose] def O20 : Finset T4 :=
  {(0, 1, 0, 0), (1, 1, 0, 1), (1, 1, 2, 0), (1, 1, 0, 2), (2, 1, 2, 1), (1, 2, 1, 1),
    (1, 1, 1, 0), (1, 2, 2, 1), (1, 0, 0, 0), (2, 1, 2, 2), (1, 2, 1, 2), (2, 1, 1, 1),
    (2, 2, 2, 0), (2, 2, 1, 0), (2, 2, 0, 1), (1, 2, 2, 2), (2, 1, 1, 2), (0, 2, 0, 0),
    (2, 0, 0, 0), (2, 2, 0, 2)}

theorem O20_card : O20.card = 20 := by decide +kernel

theorem O20_invariant : ∀ x ∈ O20, ∀ k : Gen, mAct k x ∈ O20 := by decide +kernel

theorem root_mem_O20 : ((1, 0, 0, 0) : T4) ∈ O20 := by decide +kernel

theorem not_mem_O20_mAct : ∀ x : T4, x ∉ O20 → ∀ k : Gen, mAct k x ∉ O20 := by
  decide +kernel

@[expose] def reachVec (f : Gen → T4 → T4) (x : T4) : ℕ → Finset T4
  | 0 => {x}
  | n + 1 => reachVec f x n ∪ (reachVec f x n).biUnion fun y => Finset.univ.image fun k => f k y

theorem reachVec_subset (f : Gen → T4 → T4) (S : Finset T4) (hS : ∀ x ∈ S, ∀ k : Gen, f k x ∈ S)
    {x : T4} (hx : x ∈ S) : ∀ n, reachVec f x n ⊆ S
  | 0 => by
    rw [reachVec, Finset.singleton_subset_iff]
    exact hx
  | n + 1 => by
    rw [reachVec, Finset.union_subset_iff, Finset.biUnion_subset]
    refine ⟨reachVec_subset f S hS hx n, fun y hy z hz => ?_⟩
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hz
    exact hS y (reachVec_subset f S hS hx n hy) k

theorem mem_of_mem_reachVec_nAct (S : Finset T4) (hS : ∀ x ∈ S, ∀ k : Gen, mAct k x ∈ S)
    (x : T4) : ∀ (n : ℕ) (y : T4), y ∈ reachVec nAct x n → y ∈ S → x ∈ S
  | 0, y, hy, hyS => by
    rw [reachVec, Finset.mem_singleton] at hy
    exact hy ▸ hyS
  | n + 1, y, hy, hyS => by
    rw [reachVec, Finset.mem_union, Finset.mem_biUnion] at hy
    rcases hy with hy | ⟨z, hz, hyz⟩
    · exact mem_of_mem_reachVec_nAct S hS x n y hy hyS
    · obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hyz
      exact mem_of_mem_reachVec_nAct S hS x n z hz (mAct_nAct k z ▸ hS _ hyS k)

@[expose] def levOrbitReps : Finset T4 := {(1, 1, 1, 0), (0, 0, 0, 1), (1, 1, 0, 0)}

theorem erase_zero_eq_biUnion_reachVec :
    Finset.univ.erase 0 = levOrbitReps.biUnion fun r => reachVec nAct r 4 := by
  decide +kernel

theorem twenty_le_card_reachVec : ∀ r ∈ levOrbitReps, 20 ≤ (reachVec mAct r 3).card := by
  decide +kernel

theorem orbit_min (S : Finset T4) (hS : ∀ x ∈ S, ∀ k : Gen, mAct k x ∈ S) (hne : S.Nonempty)
    (h0 : (0 : T4) ∉ S) : 20 ≤ S.card := by
  obtain ⟨x, hx⟩ := hne
  have hx0 : x ∈ Finset.univ.erase (0 : T4) := Finset.mem_erase.2 ⟨fun h => h0 (h ▸ hx), by simp⟩
  rw [erase_zero_eq_biUnion_reachVec, Finset.mem_biUnion] at hx0
  obtain ⟨r, hr, hxr⟩ := hx0
  exact (twenty_le_card_reachVec r hr).trans (Finset.card_le_card
    (reachVec_subset mAct S hS (mem_of_mem_reachVec_nAct S hS r 4 x hxr hx) 3))

theorem permE_conj_mem_D5 (σ : Equiv.Perm (Fin 6)) {d : G12} (hd : d ∈ D5) :
    permE σ * d * (permE σ)⁻¹ ∈ D5 :=
  mul_mem_D5_of_mem_monGamma (monLin_le_monGamma (permE_mem_monLin σ)) hd

@[expose] def permConjD5 (σ : Equiv.Perm (Fin 6)) : D5 →* D5 where
  toFun d := ⟨permE σ * d * (permE σ)⁻¹, permE_conj_mem_D5 σ d.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem coe_permConjD5 (σ : Equiv.Perm (Fin 6)) (d : D5) :
    (permConjD5 σ d : G12) = permE σ * d * (permE σ)⁻¹ := rfl

theorem permConjD5_mul (σ τ : Equiv.Perm (Fin 6)) (d : D5) :
    permConjD5 (σ * τ) d = permConjD5 σ (permConjD5 τ d) :=
  Subtype.ext (by simp only [coe_permConjD5, permE_mul]; group)

theorem permConjD5_one (d : D5) : permConjD5 1 d = d :=
  Subtype.ext (by simp only [coe_permConjD5, permE_one]; group)

theorem permConjD5_of_mem_zpowers (σ : Equiv.Perm (Fin 6)) {d : D5}
    (hd : (d : G12) ∈ Subgroup.zpowers theta0e) : permConjD5 σ d = d := by
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hd
  refine Subtype.ext ?_
  rw [coe_permConjD5, ← hn, (Commute.zpow_right (permE_mul_theta0e σ) n).eq, mul_inv_cancel_right]

theorem perm_mem_alternatingGroup_of_pow_three {π : Equiv.Perm (Fin 6)} (h : π ^ 3 = 1) :
    π ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  have h3 := congrArg Equiv.Perm.sign h
  rw [map_pow, map_one] at h3
  rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h1 | h1
  · exact h1
  · rw [h1] at h3
    exact absurd h3 (by decide)

section Action

variable (ψ' : D5 →* A4) (hψs : Function.Surjective ψ')
  (hψk : ∀ d : D5, ψ' d = 1 ↔ (d : G12) ∈ Subgroup.zpowers theta0e)

include hψk in
theorem ker_le_ker_permConjD5 (σ : Equiv.Perm (Fin 6)) :
    ψ'.ker ≤ (ψ'.comp (permConjD5 σ)).ker := by
  intro d hd
  rw [MonoidHom.mem_ker] at hd ⊢
  rw [MonoidHom.comp_apply, permConjD5_of_mem_zpowers σ ((hψk d).1 hd)]
  exact hd

@[expose] noncomputable def permActA (σ : Equiv.Perm (Fin 6)) : A4 →* A4 :=
  ψ'.liftOfSurjective hψs ⟨ψ'.comp (permConjD5 σ), ker_le_ker_permConjD5 ψ' hψk σ⟩

theorem permActA_apply (σ : Equiv.Perm (Fin 6)) (d : D5) :
    permActA ψ' hψs hψk σ (ψ' d) = ψ' (permConjD5 σ d) :=
  ψ'.liftOfRightInverse_comp_apply _ _ _ d

theorem permActA_mul (σ τ : Equiv.Perm (Fin 6)) (x : A4) :
    permActA ψ' hψs hψk (σ * τ) x = permActA ψ' hψs hψk σ (permActA ψ' hψs hψk τ x) := by
  obtain ⟨d, rfl⟩ := hψs x
  rw [permActA_apply, permActA_apply, permActA_apply, permConjD5_mul]

theorem permActA_one (x : A4) : permActA ψ' hψs hψk 1 x = x := by
  obtain ⟨d, rfl⟩ := hψs x
  rw [permActA_apply, permConjD5_one]

@[expose] noncomputable def permActHom : Equiv.Perm (Fin 6) →* (A4 ≃* A4) where
  toFun σ := (permActA ψ' hψs hψk σ).toMulEquiv (permActA ψ' hψs hψk σ⁻¹)
    (MonoidHom.ext fun x => by
      rw [MonoidHom.comp_apply, ← permActA_mul, inv_mul_cancel, permActA_one, MonoidHom.id_apply])
    (MonoidHom.ext fun x => by
      rw [MonoidHom.comp_apply, ← permActA_mul, mul_inv_cancel, permActA_one, MonoidHom.id_apply])
  map_one' := MulEquiv.ext fun x => permActA_one ψ' hψs hψk x
  map_mul' σ τ := MulEquiv.ext fun x => permActA_mul ψ' hψs hψk σ τ x

theorem permActHom_apply (σ : Equiv.Perm (Fin 6)) (d : D5) :
    permActHom ψ' hψs hψk σ (ψ' d) = ψ' (permConjD5 σ d) :=
  permActA_apply ψ' hψs hψk σ d

end Action

theorem perm_closure_eq_alternating
    (p : Gen → Equiv.Perm (Fin 6)) (hp3 : ∀ k, p k ^ 3 = 1) (ψ' : D5 →* A4)
    (hψs : Function.Surjective ψ')
    (hψk : ∀ d : D5, ψ' d = 1 ↔ (d : G12) ∈ Subgroup.zpowers theta0e)
    (hequiv : ∀ (k : Gen) (d : D5) (h : permE (p k) * (d : G12) * (permE (p k))⁻¹ ∈ D5),
      ψ' ⟨permE (p k) * (d : G12) * (permE (p k))⁻¹, h⟩ = sg k (ψ' d)) :
    Subgroup.closure (Set.range p) = alternatingGroup (Fin 6) := by
  have hle : Subgroup.closure (Set.range p) ≤ alternatingGroup (Fin 6) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    exact perm_mem_alternatingGroup_of_pow_three (hp3 k)
  have hΦ : ⇑(permActHom ψ' hψs hψk) ∘ p = sg := funext fun k => MulEquiv.ext fun x => by
    obtain ⟨d, rfl⟩ := hψs x
    exact (permActHom_apply ψ' hψs hψk (p k) d).trans (hequiv k d _)
  have hmap : (Subgroup.closure (Set.range p)).map (permActHom ψ' hψs hψk) =
      Subgroup.closure (Set.range sg) := by
    rw [MonoidHom.map_closure, ← Set.range_comp, hΦ]
  have hcard : 360 ≤ Nat.card (Subgroup.closure (Set.range p)) := by
    refine card_closure_sg_ge.trans ?_
    rw [← hmap]
    exact Nat.card_le_card_of_surjective _ ((permActHom ψ' hψs hψk).subgroupMap_surjective _)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  exact hcard

@[expose] def expSqSum (c : Fin 6 → ZMod 3) : ZMod 3 := ∑ i, c i ^ 2

@[expose] def expLift (v : T4) : Fin 6 → ZMod 3 :=
  ![v.1, v.2.1, v.2.2.1, v.2.2.2, -(v.1 + v.2.1 + v.2.2.1 + v.2.2.2), 0]

@[expose] def expRed (c : Fin 6 → ZMod 3) : T4 := (c 0 - c 5, c 1 - c 5, c 2 - c 5, c 3 - c 5)

theorem card_filter_expSqSum : ∀ u : ZMod 3, u ≠ 0 →
    (Finset.univ.filter fun v : T4 => expSqSum (expLift v) = u).card = 30 := by
  decide +kernel

theorem split_of_expSqSum_eq_zero : ∀ v : T4, expSqSum (expLift v) = 0 → v ≠ 0 →
    ∃ S : Finset (Fin 6), S.card = 3 ∧ ∃ e : ZMod 3, e ≠ 0 ∧
      ∀ i, expLift v i = expLift v 0 + if i ∈ S then e else 0 := by
  decide +kernel

theorem expSqSum_add_const (c : Fin 6 → ZMod 3) (hc : ∑ i, c i = 0) (m : ZMod 3) :
    expSqSum (c + fun _ => m) = expSqSum c := by
  have h3 : (3 : ZMod 3) = 0 := by decide
  simp only [expSqSum, Pi.add_apply, Fin.sum_univ_six] at hc ⊢
  linear_combination (2 * m) * hc + (2 * m ^ 2) * h3

theorem expSqSum_perm (c : Fin 6 → ZMod 3) (σ : Equiv.Perm (Fin 6)) :
    expSqSum (fun i => c (σ.symm i)) = expSqSum c :=
  Equiv.sum_comp σ.symm fun i => c i ^ 2

theorem sum_expLift (v : T4) : ∑ i, expLift v i = 0 := by
  simp only [expLift, Fin.sum_univ_six]
  simp

theorem expLift_expRed_add (c : Fin 6 → ZMod 3) (hc : ∑ i, c i = 0) :
    expLift (expRed c) + (fun _ => c 5) = c := by
  have h3 : (3 : ZMod 3) = 0 := by decide
  rw [Fin.sum_univ_six] at hc
  funext i
  fin_cases i <;> simp [expLift, expRed]
  linear_combination (-1 : ZMod 3) * hc + (2 * c 5) * h3

theorem expLift_zero : expLift 0 = 0 := by decide

theorem expSqSum_expLift_expRed (c : Fin 6 → ZMod 3) (hc : ∑ i, c i = 0) :
    expSqSum (expLift (expRed c)) = expSqSum c := by
  conv_rhs => rw [← expLift_expRed_add c hc]
  exact (expSqSum_add_const _ (sum_expLift _) _).symm

@[expose] def expPerm (π : Equiv.Perm (Fin 6)) (v : T4) : T4 :=
  expRed fun i => expLift v (π.symm i)

theorem sum_expLift_perm (π : Equiv.Perm (Fin 6)) (v : T4) : ∑ i, expLift v (π.symm i) = 0 :=
  (Equiv.sum_comp π.symm (expLift v)).trans (sum_expLift v)

theorem expSqSum_expLift_expPerm (π : Equiv.Perm (Fin 6)) (v : T4) :
    expSqSum (expLift (expPerm π v)) = expSqSum (expLift v) := by
  rw [expPerm, expSqSum_expLift_expRed _ (sum_expLift_perm π v), expSqSum_perm]

theorem diagE_mem_D5 {c : Fin 6 → ZMod 3} (hc : ∑ i, c i = 0) : diagE c ∈ D5 := ⟨c, hc, rfl⟩

theorem sum_const_six : ∀ m : ZMod 3, ∑ _i : Fin 6, m = 0 := by decide

theorem diagE_const_mem_zpowers (m : ZMod 3) :
    diagE (fun _ => m) ∈ Subgroup.zpowers theta0e := by
  have hm : ∀ m : ZMod 3, m = 0 ∨ m = 1 ∨ m = 2 := by decide
  rcases hm m with rfl | rfl | rfl
  · exact diagE_zero ▸ one_mem _
  · exact diagE_const_one ▸ Subgroup.mem_zpowers _
  · have h2 : (fun _ : Fin 6 => (2 : ZMod 3)) = (fun _ => 1) + fun _ => 1 := by decide
    rw [h2, diagE_add, diagE_const_one]
    exact mul_mem (Subgroup.mem_zpowers _) (Subgroup.mem_zpowers _)

section Coords

variable (ψ' : D5 →* A4)

@[expose] def expCoord (v : T4) : T4 :=
  (ψ' ⟨diagE (expLift v), diagE_mem_D5 (sum_expLift v)⟩).toAdd

theorem expCoord_zero : expCoord ψ' 0 = 0 := by
  have h : (⟨diagE (expLift 0), diagE_mem_D5 (sum_expLift 0)⟩ : D5) = 1 :=
    Subtype.ext (by
      show diagE (expLift 0) = 1
      rw [expLift_zero, diagE_zero])
  simp only [expCoord, h, map_one, toAdd_one]

variable {ψ'} (hψk : ∀ d : D5, ψ' d = 1 ↔ (d : G12) ∈ Subgroup.zpowers theta0e)
include hψk

theorem toAdd_diagE_eq_expCoord (c : Fin 6 → ZMod 3) (hc : ∑ i, c i = 0) :
    (ψ' ⟨diagE c, diagE_mem_D5 hc⟩).toAdd = expCoord ψ' (expRed c) := by
  have h : (⟨diagE c, diagE_mem_D5 hc⟩ : D5) =
      ⟨diagE (expLift (expRed c)), diagE_mem_D5 (sum_expLift _)⟩ *
        ⟨diagE (fun _ => c 5), diagE_mem_D5 (sum_const_six _)⟩ :=
    Subtype.ext (by
      show diagE c = diagE (expLift (expRed c)) * diagE (fun _ => c 5)
      rw [← diagE_add, expLift_expRed_add c hc])
  have h1 : ψ' ⟨diagE (fun _ => c 5), diagE_mem_D5 (sum_const_six _)⟩ = 1 :=
    (hψk _).2 (diagE_const_mem_zpowers _)
  rw [h, map_mul, h1, mul_one]
  rfl

theorem expCoord_surjective (hψs : Function.Surjective ψ') : Function.Surjective (expCoord ψ') := by
  intro y
  obtain ⟨d, hd⟩ := hψs (Multiplicative.ofAdd y)
  obtain ⟨c, hc, hdc⟩ := d.2
  have hdeq : d = ⟨diagE c, diagE_mem_D5 hc⟩ := Subtype.ext hdc
  refine ⟨expRed c, ?_⟩
  rw [← toAdd_diagE_eq_expCoord hψk c hc, ← hdeq, hd]
  rfl

theorem expCoord_injective (hψs : Function.Surjective ψ') : Function.Injective (expCoord ψ') :=
  Finite.injective_iff_surjective.2 (expCoord_surjective hψk hψs)

theorem mAct_expCoord (p : Gen → Equiv.Perm (Fin 6))
    (hequiv : ∀ (k : Gen) (d : D5) (h : permE (p k) * (d : G12) * (permE (p k))⁻¹ ∈ D5),
      ψ' ⟨permE (p k) * (d : G12) * (permE (p k))⁻¹, h⟩ = sg k (ψ' d)) (k : Gen) (v : T4) :
    mAct k (expCoord ψ' v) = expCoord ψ' (expPerm (p k) v) := by
  have h := hequiv k ⟨diagE (expLift v), diagE_mem_D5 (sum_expLift v)⟩
    (permE_conj_mem_D5 _ (diagE_mem_D5 (sum_expLift v)))
  have h2 : (⟨permE (p k) * diagE (expLift v) * (permE (p k))⁻¹,
      permE_conj_mem_D5 _ (diagE_mem_D5 (sum_expLift v))⟩ : D5) =
      ⟨diagE (fun i => expLift v ((p k).symm i)), diagE_mem_D5 (sum_expLift_perm _ v)⟩ :=
    Subtype.ext (permE_mul_diagE_mul_inv _ _)
  rw [h2] at h
  show (sg k (ψ' ⟨diagE (expLift v), diagE_mem_D5 (sum_expLift v)⟩)).toAdd = _
  rw [← h, toAdd_diagE_eq_expCoord hψk _ (sum_expLift_perm _ v)]
  rfl

end Coords

theorem root_type
    (p : Gen → Equiv.Perm (Fin 6)) (ψ' : D5 →* A4) (hψs : Function.Surjective ψ')
    (hψk : ∀ d : D5, ψ' d = 1 ↔ (d : G12) ∈ Subgroup.zpowers theta0e)
    (hequiv : ∀ (k : Gen) (d : D5) (h : permE (p k) * (d : G12) * (permE (p k))⁻¹ ∈ D5),
      ψ' ⟨permE (p k) * (d : G12) * (permE (p k))⁻¹, h⟩ = sg k (ψ' d))
    (d : D5) (hd : ψ' d = Multiplicative.ofAdd ((1, 0, 0, 0) : T4)) :
    ∃ (S : Finset (Fin 6)) (j e : ZMod 3) (c : Fin 6 → ZMod 3), S.card = 3 ∧ e ≠ 0 ∧
      (d : G12) = diagE c ∧ ∀ i, c i = j + if i ∈ S then e else 0 := by
  obtain ⟨c, hc, hdc⟩ := d.2
  have hdeq : d = ⟨diagE c, diagE_mem_D5 hc⟩ := Subtype.ext hdc
  have hx₀ : expCoord ψ' (expRed c) = (1, 0, 0, 0) := by
    rw [← toAdd_diagE_eq_expCoord hψk c hc, ← hdeq, hd]
    rfl
  have hu : expSqSum c = 0 := by
    by_contra hu
    set W := (Finset.univ.filter fun v : T4 => expSqSum (expLift v) = expSqSum c).image
      (expCoord ψ')
    have hWcard : W.card = 30 := by
      rw [Finset.card_image_of_injective _ (expCoord_injective hψk hψs)]
      exact card_filter_expSqSum _ hu
    have hW : ∀ x ∈ W, ∀ k, mAct k x ∈ W := by
      intro x hx k
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hx
      rw [mAct_expCoord hψk p hequiv]
      refine Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩)
      rw [expSqSum_expLift_expPerm]
      exact (Finset.mem_filter.1 hv).2
    have h1W : ((1, 0, 0, 0) : T4) ∈ W := by
      rw [← hx₀]
      exact Finset.mem_image_of_mem _
        (Finset.mem_filter.2 ⟨Finset.mem_univ _, expSqSum_expLift_expRed c hc⟩)
    have h0W : (0 : T4) ∉ W := by
      intro h0
      obtain ⟨v, hv, hv0⟩ := Finset.mem_image.1 h0
      rw [← expCoord_zero ψ'] at hv0
      have hv0' := expCoord_injective hψk hψs hv0
      subst hv0'
      exact hu ((Finset.mem_filter.1 hv).2.symm.trans (by decide))
    have hA := orbit_min (W.filter (· ∈ O20)) (fun x hx k => by
        rw [Finset.mem_filter] at hx ⊢
        exact ⟨hW x hx.1 k, O20_invariant x hx.2 k⟩)
      ⟨_, Finset.mem_filter.2 ⟨h1W, root_mem_O20⟩⟩ (fun h => h0W (Finset.mem_filter.1 h).1)
    have hA' : (W.filter (· ∈ O20)).card ≤ 20 :=
      O20_card ▸ Finset.card_le_card fun x hx => (Finset.mem_filter.1 hx).2
    have hsplit := Finset.card_filter_add_card_filter_not (s := W) (· ∈ O20)
    have hB := orbit_min (W.filter fun x => ¬ x ∈ O20) (fun x hx k => by
        rw [Finset.mem_filter] at hx ⊢
        exact ⟨hW x hx.1 k, not_mem_O20_mAct x hx.2 k⟩)
      (Finset.card_pos.1 (by omega)) (fun h => h0W (Finset.mem_filter.1 h).1)
    omega
  have hv0 : expRed c ≠ 0 := by
    intro h0
    have hconst : c = fun _ => c 5 := by
      have h1 := expLift_expRed_add c hc
      rw [h0, expLift_zero, zero_add] at h1
      exact h1.symm
    have hmem : (d : G12) ∈ Subgroup.zpowers theta0e := by
      rw [hdc, hconst]
      exact diagE_const_mem_zpowers _
    have h1 := (hψk d).2 hmem
    rw [hd] at h1
    exact absurd (congrArg Multiplicative.toAdd h1) (by decide)
  obtain ⟨S, hS, e, he, hSe⟩ :=
    split_of_expSqSum_eq_zero (expRed c) ((expSqSum_expLift_expRed c hc).trans hu) hv0
  refine ⟨S, c 0, e, c, hS, he, hdc, fun i => ?_⟩
  have h1 := congrFun (expLift_expRed_add c hc) i
  have h2 := congrFun (expLift_expRed_add c hc) 0
  simp only [Pi.add_apply] at h1 h2
  rw [← h1, ← h2, hSe i]
  ring

end CFSG.GF2Type.Smith1979.IdxFour
