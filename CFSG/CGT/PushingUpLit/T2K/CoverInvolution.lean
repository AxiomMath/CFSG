module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LinearCentralCover

public section

namespace CFSG.CGT.PushingUpLit.T2K

open CFSG.ShultStronglyClosedTI
open scoped commutatorElement

variable {K : Type} [Field K] [Finite K] [CharP K 2] {E : Type} [Group E]
  {η : E →* Matrix.SpecialLinearGroup (Fin 2) K}

omit [Finite K] in
theorem cover_commutator_zero_left (hsurj : Function.Surjective η)
    (hcentral : η.ker ≤ Subgroup.center E) (t : K) :
    (linearCoverCommutator η hsurj 0 t : E) = 1 := by
  have h := linearCoverCommutator_eq_of_lifts η hsurj hcentral (a := (1 : E))
    (b := linearCoverRootLift η hsurj t) (x := 0) (y := t)
    (by rw [map_one, AddChar.map_zero_eq_one]) (linearCoverRootLift_image η hsurj t)
  rw [h, commutatorElement_one_left]

omit [Finite K] in
theorem cover_commutator_zero_right (hsurj : Function.Surjective η)
    (hcentral : η.ker ≤ Subgroup.center E) (s : K) :
    (linearCoverCommutator η hsurj s 0 : E) = 1 := by
  have h := linearCoverCommutator_eq_of_lifts η hsurj hcentral
    (a := linearCoverRootLift η hsurj s) (b := (1 : E)) (x := s) (y := 0)
    (linearCoverRootLift_image η hsurj s) (by rw [map_one, AddChar.map_zero_eq_one])
  rw [h, commutatorElement_one_right]

omit [Finite K] in
theorem cover_commutator_sq (hsurj : Function.Surjective η)
    (hcentral : η.ker ≤ Subgroup.center E) (s t : K) :
    (linearCoverCommutator η hsurj s t : E) ^ 2 = 1 := by
  have h1 := linearCoverCommutator_add_left η hsurj hcentral s s t
  rw [CharTwo.add_self_eq_zero] at h1
  have h2 := congrArg (fun c : η.ker => (c : E)) h1
  simp only [Subgroup.coe_mul] at h2
  rw [pow_two, ← h2]
  exact cover_commutator_zero_left hsurj hcentral t

theorem cover_ker_sq_eq_one [Finite E] [Group.IsPerfect E] {f : ℕ} (hcard : Nat.card K = 2 ^ f)
    (hsurj : Function.Surjective η) (hcentral : η.ker ≤ Subgroup.center E)
    (hp : IsPGroup 2 η.ker) : ∀ z ∈ η.ker, z ^ 2 = 1 := by
  let Z₂ : Subgroup E :=
    { carrier := {z | z ∈ η.ker ∧ z ^ 2 = 1}
      one_mem' := ⟨one_mem _, one_pow 2⟩
      mul_mem' := by
        rintro a b ⟨ha, ha2⟩ ⟨hb, hb2⟩
        refine ⟨mul_mem ha hb, ?_⟩
        have hcomm : Commute a b := (Subgroup.mem_center_iff.mp (hcentral ha) b).symm
        rw [hcomm.mul_pow, ha2, hb2, one_mul]
      inv_mem' := by
        rintro a ⟨ha, ha2⟩
        refine ⟨inv_mem ha, ?_⟩
        rw [inv_pow, ha2, inv_one] }
  have heq := linearCover_sylow_derived_eq_kernel f hcard η hsurj hcentral hp
  have hle : (commutator (linearCoverPreimageSylow f hcard η hsurj hp : Subgroup E)).map
      (linearCoverPreimageSylow f hcard η hsurj hp : Subgroup E).subtype ≤ Z₂ := by
    apply Subgroup.map_le_iff_le_comap.mpr
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    obtain ⟨sx, hsx⟩ := x.property
    obtain ⟨sy, hsy⟩ := y.property
    have hc := linearCoverCommutator_eq_of_lifts η hsurj hcentral (x := sx.toAdd) (y := sy.toAdd)
      (a := (x : E)) (b := (y : E)) hsx.symm hsy.symm
    refine ⟨linearCover_root_commutator_mem_kernel η x.property y.property, ?_⟩
    show ⁅(x : E), (y : E)⁆ ^ 2 = 1
    rw [← hc]
    exact cover_commutator_sq hsurj hcentral _ _
  intro z hz
  have hz' : z ∈ (commutator (linearCoverPreimageSylow f hcard η hsurj hp : Subgroup E)).map
      (linearCoverPreimageSylow f hcard η hsurj hp : Subgroup E).subtype := by
    rw [heq]
    exact hz
  exact (hle hz').2

theorem cover_ker_eq_bot_of_involution [Finite E] [Group.IsPerfect E] {f : ℕ}
    (hcard : Nat.card K = 2 ^ f) (hsurj : Function.Surjective η)
    (hcentral : η.ker ≤ Subgroup.center E) (hp : IsPGroup 2 η.ker) {x : E}
    (hx : η x ∈ linearCoverRootSubgroup K) (hx1 : η x ≠ 1) (hx2 : x ^ 2 = 1) :
    η.ker = ⊥ := by
  obtain ⟨t₀, ht₀⟩ := hx
  have hsq := cover_ker_sq_eq_one hcard hsurj hcentral hp
  have ht0 : t₀.toAdd ≠ 0 := by
    intro h0
    apply hx1
    rw [← ht₀]
    show linearCoverRoot t₀.toAdd = 1
    rw [h0, AddChar.map_zero_eq_one]
  have hlift : ∀ s : K, s ≠ 0 → ∃ y : E, η y = linearCoverRoot s ∧ y ^ 2 = 1 := by
    intro s hs
    obtain ⟨h, hh⟩ := linearCover_scalar_conjugator (s / t₀.toAdd) (div_ne_zero hs ht0)
    obtain ⟨e, he⟩ := hsurj h
    refine ⟨e * x * e⁻¹, ?_, ?_⟩
    · have h1 := hh t₀.toAdd
      rw [MulAut.conj_apply, div_mul_cancel₀ _ ht0] at h1
      rw [map_mul, map_mul, map_inv, he, ← ht₀]
      exact h1
    · rw [conj_pow, hx2]
      group
  have hc1 : ∀ s t : K, (linearCoverCommutator η hsurj s t : E) = 1 := by
    intro s t
    by_cases hs : s = 0
    · rw [hs]
      exact cover_commutator_zero_left hsurj hcentral t
    by_cases ht : t = 0
    · rw [ht]
      exact cover_commutator_zero_right hsurj hcentral s
    by_cases hst : s = t
    · have h := linearCoverCommutator_eq_of_lifts η hsurj hcentral
        (a := linearCoverRootLift η hsurj s) (b := linearCoverRootLift η hsurj s) (x := s)
        (y := t) (linearCoverRootLift_image η hsurj s)
        (by rw [← hst]; exact linearCoverRootLift_image η hsurj s)
      rw [h, commutatorElement_self]
    have hst' : s + t ≠ 0 := by
      intro h0
      apply hst
      have : s = -t := eq_neg_of_add_eq_zero_left h0
      rw [this, CharTwo.neg_eq]
    obtain ⟨ys, hys, hys2⟩ := hlift s hs
    obtain ⟨yt, hyt, hyt2⟩ := hlift t ht
    obtain ⟨yst, hyst, hyst2⟩ := hlift (s + t) hst'
    have hz : yst⁻¹ * (ys * yt) ∈ η.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, hys, hyt, hyst,
        ← AddChar.map_add_eq_mul]
      exact inv_mul_cancel _
    have hzc : ∀ g : E, g * (yst⁻¹ * (ys * yt)) = (yst⁻¹ * (ys * yt)) * g := fun g =>
      Subgroup.mem_center_iff.mp (hcentral hz) g
    have h1 := linearCoverCommutator_eq_of_lifts η hsurj hcentral hys hyt
    have hi1 : ys⁻¹ = ys := inv_eq_of_mul_eq_one_right (by rw [← pow_two, hys2])
    have hi2 : yt⁻¹ = yt := inv_eq_of_mul_eq_one_right (by rw [← pow_two, hyt2])
    have h2 : ⁅ys, yt⁆ = (yst * (yst⁻¹ * (ys * yt))) ^ 2 := by
      rw [mul_inv_cancel_left, pow_two, commutatorElement_def, hi1, hi2]
      simp only [mul_assoc]
    have h3 : (yst * (yst⁻¹ * (ys * yt))) ^ 2 = yst ^ 2 * (yst⁻¹ * (ys * yt)) ^ 2 := by
      have hcomm : Commute yst (yst⁻¹ * (ys * yt)) := hzc yst
      exact hcomm.mul_pow 2
    rw [h1, h2, h3, hyst2, one_mul]
    exact hsq _ hz
  have hcomm : ∀ a b : E, η a ∈ linearCoverRootSubgroup K → η b ∈ linearCoverRootSubgroup K →
      ⁅a, b⁆ = 1 := by
    intro a b ha hb
    obtain ⟨sa, hsa⟩ := ha
    obtain ⟨sb, hsb⟩ := hb
    have h := linearCoverCommutator_eq_of_lifts η hsurj hcentral (x := sa.toAdd) (y := sb.toAdd)
      (a := a) (b := b) hsa.symm hsb.symm
    rw [← h]
    exact hc1 _ _
  have heq := linearCover_sylow_derived_eq_kernel f hcard η hsurj hcentral hp
  have hle : (commutator (linearCoverPreimageSylow f hcard η hsurj hp : Subgroup E)).map
      (linearCoverPreimageSylow f hcard η hsurj hp : Subgroup E).subtype ≤ ⊥ := by
    apply Subgroup.map_le_iff_le_comap.mpr
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    exact hcomm x y x.property y.property
  rw [← heq]
  exact le_bot_iff.mp hle

theorem cover_ker_eq_bot_of_sq_eq_one [Finite E] [Group.IsPerfect E] {f : ℕ}
    (hcard : Nat.card K = 2 ^ f) (hsurj : Function.Surjective η)
    (hcentral : η.ker ≤ Subgroup.center E) (hp : IsPGroup 2 η.ker) {x : E} (hx1 : η x ≠ 1)
    (hx2 : x ^ 2 = 1) : η.ker = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu2 : (η x) ^ 2 = 1 := by rw [← map_pow, hx2, map_one]
  have hord : orderOf (η x) = 2 := orderOf_eq_prime hu2 hx1
  have hP : IsPGroup 2 (Subgroup.zpowers (η x)) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hord, pow_one]
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Matrix.SpecialLinearGroup (Fin 2) K) Q
    (linearCoverRootSylow f hcard)
  have hmem : g * η x * g⁻¹ ∈ linearCoverRootSubgroup K := by
    have h1 : η x ∈ (Q : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)) :=
      hQ (Subgroup.mem_zpowers _)
    have h2 : (MulAut.conj g) (η x) ∈ ((g • Q : Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) K)) :
        Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)) := by
      rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ h1
    rw [hg] at h2
    exact h2
  obtain ⟨e, he⟩ := hsurj g
  refine cover_ker_eq_bot_of_involution hcard hsurj hcentral hp (x := e * x * e⁻¹) ?_ ?_ ?_
  · rw [map_mul, map_mul, map_inv, he]
    exact hmem
  · intro h1
    apply hx1
    rw [map_mul, map_mul, map_inv, he] at h1
    have h2 : η x = g⁻¹ * (g * η x * g⁻¹) * g := by group
    rw [h2, h1]
    group
  · rw [conj_pow, hx2]
    group

end CFSG.CGT.PushingUpLit.T2K
