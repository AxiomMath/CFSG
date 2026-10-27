module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Inputs47
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Lemma43
public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneQuaternionRecognition

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem commute_of_mem_coreActionKernel {S J : Subgroup G} (hS : IsPGroup 2 S)
    {p q : G} (hp : p ∈ S ⊓ J)
    (hq : q ∈ S ⊓ coreActionKernel J) : p * q = q * p := by
  obtain ⟨hpS, hpJ⟩ := mem_inf.mp hp
  obtain ⟨hqS, hqK⟩ := mem_inf.mp hq
  have h1 : p⁻¹ * q⁻¹ * p * q ∈ oddIn J := (mem_coreActionKernel.mp hqK).2 p hpJ
  have h2 : p⁻¹ * q⁻¹ * p * q ∈ S :=
    mul_mem (mul_mem (mul_mem (inv_mem hpS) (inv_mem hqS)) hpS) hqS
  have h0 := eq_bot_of_le_two_group_of_le_odd hS (odd_card_map_pPrimeCore J)
    (zpowers_le.mpr h2) (zpowers_le.mpr h1)
  have h3 : p⁻¹ * q⁻¹ * p * q = 1 := by
    have := mem_zpowers (p⁻¹ * q⁻¹ * p * q)
    rw [h0] at this
    exact this
  calc p * q = q * p * (p⁻¹ * q⁻¹ * p * q) := by group
    _ = q * p := by rw [h3, mul_one]

theorem sq_eq_one_of_central_quaternionGroup {k : ℕ} (hk : 1 ≤ k) {w : QuaternionGroup (2 ^ k)}
    (hw : ∀ g, w * g = g * w) : w ^ 2 = 1 := by
  have h2 : (2 : ZMod (2 * 2 ^ k)) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod (2 * 2 ^ k)) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have h4 : 4 ≤ 2 * 2 ^ k := by
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hk
      omega
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  cases w with
  | a i =>
    have h := hw (QuaternionGroup.xa 0)
    simp only [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a, zero_sub, zero_add,
      QuaternionGroup.xa.injEq] at h
    rw [sq, QuaternionGroup.a_mul_a]
    have hi : i + i = 0 := by linear_combination -h
    rw [hi, QuaternionGroup.a_zero]
  | xa i =>
    have h := hw (QuaternionGroup.a 1)
    simp only [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a,
      QuaternionGroup.xa.injEq] at h
    exact absurd (by linear_combination h) h2

theorem isCyclic_of_involutions_mem {Q Z : Subgroup G} (hQ : IsPGroup 2 Q) (hZQ : Z ≤ Q)
    (hZc : IsCyclic ↥Z) (hZ4 : Nat.card Z = 4) (hZcen : ∀ z ∈ Z, ∀ q ∈ Q, z * q = q * z)
    (hinv : ∀ y ∈ Q, y * y = 1 → y ∈ Z) : IsCyclic ↥Q := by
  classical
  have hrank : DisconnectedInvolutionGraph.Helpers.NoCommutingDistinctInvolutions ↥Q := by
    rintro ⟨s, hs⟩ ⟨t, ht⟩ -
    by_contra hst
    have hs2 : s * s = 1 := by rw [← pow_two, ← hs, pow_orderOf_eq_one]
    have ht2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
    have hsZ : (s : G) ∈ Z := hinv s s.2 (congrArg Subtype.val hs2)
    have htZ : (t : G) ∈ Z := hinv t t.2 (congrArg Subtype.val ht2)
    have : Fintype ↥Z := Fintype.ofFinite _
    set s' : ↥Z := ⟨s, hsZ⟩
    set t' : ↥Z := ⟨t, htZ⟩
    have hle := IsCyclic.card_pow_eq_one_le (α := ↥Z) (n := 2) (by norm_num)
    have hs1 : s' ≠ 1 := fun h => by
      have : (s : G) = 1 := congrArg Subtype.val h
      have hs1 : s = 1 := Subtype.ext this
      rw [hs1, orderOf_one] at hs
      exact absurd hs (by norm_num)
    have ht1 : t' ≠ 1 := fun h => by
      have : (t : G) = 1 := congrArg Subtype.val h
      have ht1 : t = 1 := Subtype.ext this
      rw [ht1, orderOf_one] at ht
      exact absurd ht (by norm_num)
    have hst' : s' ≠ t' := by
      intro h
      apply hst
      have h1 : ((s' : ↥Z) : G) = ((t' : ↥Z) : G) := congrArg (fun w : ↥Z => (w : G)) h
      have h2 : s = t := Subtype.ext h1
      subst h2
      rfl
    have hsub : ({1, s', t'} : Finset ↥Z) ⊆ Finset.univ.filter (fun y : ↥Z => y ^ 2 = 1) := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hy with rfl | rfl | rfl
      · exact one_pow 2
      · exact Subtype.ext (by simpa [pow_two] using congrArg Subtype.val hs2)
      · exact Subtype.ext (by simpa [pow_two] using congrArg Subtype.val ht2)
    have h3 : ({1, s', t'} : Finset ↥Z).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hs1.symm, ht1.symm]),
        Finset.card_pair hst']
    have := Finset.card_le_card hsub
    omega
  rcases DisconnectedInvolutionGraph.Helpers.rank_one_two_cyclic_or_quaternion
    (hQ.of_equiv (MulEquiv.refl _)) hrank with h | ⟨k, hk, ⟨e⟩⟩
  · exact h
  · exfalso
    obtain ⟨z, hz⟩ := hZc.exists_generator
    have hzo : orderOf z = 4 := by rw [← hZ4]; exact orderOf_eq_card_of_forall_mem_zpowers hz
    set z' : ↥Q := ⟨z, hZQ z.2⟩
    have hz'c : ∀ g : QuaternionGroup (2 ^ k), e.symm z' * g = g * e.symm z' := by
      intro g
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact Subtype.ext (hZcen z z.2 (e g) (e g).2)
    have hsq := sq_eq_one_of_central_quaternionGroup hk hz'c
    have hz2 : z ^ 2 = 1 := by
      have h1 : z' ^ 2 = 1 := by
        apply e.symm.injective
        rw [map_pow, hsq, map_one]
      have h2 : ((z' ^ 2 : ↥Q) : G) = 1 := by rw [h1]; rfl
      exact Subtype.ext (by simpa [z'] using h2)
    have := orderOf_dvd_of_pow_eq_one hz2
    rw [hzo] at this
    exact absurd this (by norm_num)

theorem mem_of_pow_four_eq_one_of_cyclic {Q Z : Subgroup G} (hQc : IsCyclic ↥Q) (hZQ : Z ≤ Q)
    (hZ4 : Nat.card Z = 4) {v : G} (hvQ : v ∈ Q) (hv : v ^ 4 = 1) : v ∈ Z := by
  classical
  have : Fintype ↥Q := Fintype.ofFinite _
  have hle := IsCyclic.card_pow_eq_one_le (α := ↥Q) (n := 4) (by norm_num)
  set T := Finset.univ.filter (fun y : ↥Q => y ^ 4 = 1) with hT
  set Zf := Finset.univ.filter (fun y : ↥Q => (y : G) ∈ Z) with hZf
  have hsub : Zf ⊆ T := by
    intro y hy
    simp only [hZf, hT, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    have h1 : (⟨y, hy⟩ : ↥Z) ^ 4 = 1 := by
      rw [← hZ4]
      exact pow_card_eq_one'
    exact Subtype.ext (by simpa using congrArg Subtype.val h1)
  have hZcard : Zf.card = 4 := by
    rw [hZf, ← Fintype.card_subtype, ← hZ4, Fintype.card_eq_nat_card]
    exact Nat.card_congr ((Equiv.subtypeEquivRight fun y => mem_subgroupOf.symm).trans
      (subgroupOfEquivOfLe hZQ).toEquiv)
  have heq : Zf = T := Finset.eq_of_subset_of_card_le hsub (by omega)
  have hvT : (⟨v, hvQ⟩ : ↥Q) ∈ T := by
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Subtype.ext (by simpa using hv)
  rw [← heq] at hvT
  simpa [hZf] using hvT

end CFSG.ComponentClassification.GrSLit.GrS4

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS GrS4
open scoped Pointwise

theorem l34_involution_mem_left_of_cyclic_right
    {G : Type} [Group G] [Finite G] {P Q Z : Subgroup G}
    (hcomm : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p)
    (hPQ : P ⊓ Q = Z) (hZleP : Z ≤ P) (hZleQ : Z ≤ Q)
    (hZ4 : Nat.card Z = 4) (hQc : IsCyclic ↥Q)
    (hno : ∀ p ∈ P, p * p ∈ Z → p ^ 4 = 1) :
    ∀ y ∈ P ⊔ Q, y * y = 1 → y ∈ P := by
  intro y hy hy2
  have hPN : P ≤ normalizer (Q : Set G) := fun p hp =>
    mem_normalizer_of_forall_commute fun q hq => hcomm p hp q hq
  have hy' : y ∈ (P : Set G) * (Q : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right P Q hPN]
    exact hy
  obtain ⟨u, hu, v, hv, rfl⟩ := hy'
  have huv := hcomm u hu v hv
  have hu2 : u * u = (v * v)⁻¹ := by
    have h1 : u * v * (u * v) = u * u * (v * v) := by
      calc u * v * (u * v) = u * (v * u) * v := by group
        _ = u * (u * v) * v := by rw [huv]
        _ = u * u * (v * v) := by group
    rw [h1] at hy2
    exact eq_inv_of_mul_eq_one_left hy2
  have huuZ : u * u ∈ Z := by
    rw [← hPQ]
    refine mem_inf.mpr ⟨mul_mem hu hu, ?_⟩
    rw [hu2]
    exact inv_mem (mul_mem hv hv)
  have hu4 : u ^ 4 = 1 := hno u hu huuZ
  have hv4 : v ^ 4 = 1 := by
    have h1 : u ^ 4 = ((v * v) * (v * v))⁻¹ := by
      rw [show u ^ 4 = (u * u) * (u * u) by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two],
        hu2, ← mul_inv_rev]
    rw [hu4] at h1
    have h2 : (v * v) * (v * v) = 1 := (inv_eq_one.mp h1.symm)
    rw [show v ^ 4 = (v * v) * (v * v) by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two],
      h2]
  have hvZ : v ∈ Z := mem_of_pow_four_eq_one_of_cyclic hQc hZleQ hZ4 hv hv4
  exact mul_mem hu (hZleP hvZ)

theorem l34Lemma47_of_inputs (h43 : L34Lemma43) (h46 : L34Lemma46)
    (hConn : L34Lemma47ConnectStep) (hSq : L34NoSquareRootFact) : L34Lemma47 := by
  intro G _ _ a x J S A hset hcent hZ hrun
  obtain ⟨h3, -⟩ := h43 G a x J S A hset hcent hZ hrun
  obtain ⟨hZc, hZ4⟩ := h46 G a x J S A hset hcent hZ hrun
  obtain ⟨-, hU3, hL34, -, hS, -, -⟩ := id hset
  have hJa : J ≤ centralizer ({a} : Set G) := hU3.2.2.2.1
  have hJper : ⁅J, J⁆ = J := commutator_eq_of_isPComponent hJa hU3.2.2.2.2.1
  have hSN : S ≤ normalizer (J : Set G) := hS.1
  have hS2 : IsPGroup 2 S := isPGroup_of_isSylowTwoIn hS
  set P : Subgroup G := S ⊓ J with hPdef
  set Q : Subgroup G := S ⊓ coreActionKernel J with hQdef
  set Z : Subgroup G := S ⊓ zStarIn J with hZdef
  have hP : IsSylowTwoIn P J := isSylowTwoIn_inf hS
  have hZJ : zStarIn J ≤ J := map_subtype_le _
  have hZP : P ⊓ zStarIn J = Z := by rw [hPdef, inf_assoc, inf_eq_right.mpr hZJ]
  have hzK : zStarIn J = J ⊓ coreActionKernel J := GSThmB.map_fusionZStar_eq J
  have hZQ : Z ≤ Q := inf_le_inf_left S (hzK ▸ inf_le_right)
  have hZPle : Z ≤ P := inf_le_inf_left S hZJ
  have hPQ : P ⊓ Q = Z := by
    rw [hPdef, hQdef, hZdef, hzK]
    ext y
    simp only [mem_inf]
    tauto
  have hcomm : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p := fun p hp q hq =>
    commute_of_mem_coreActionKernel hS2 hp hq
  have hinv : ∀ y ∈ Q, y * y = 1 → y ∈ Z := by
    intro y hyQ hy2
    by_contra hyZ
    exact h3 (hConn G a x J S A hset hrun hZc hZ4 y hyQ hy2 fun h =>
      hyZ (mem_inf.mpr ⟨(mem_inf.mp hyQ).1, h⟩))
  have hQc : IsCyclic ↥Q := isCyclic_of_involutions_mem (hS2.to_le inf_le_left) hZQ hZc hZ4
    (fun z hz q hq => hcomm z (hZPle hz) q hq) hinv
  refine ⟨hQc, l34_involution_mem_left_of_cyclic_right hcomm hPQ hZPle hZQ hZ4 hQc ?_⟩
  intro u hu huuZ
  exact hSq G J P hJper hL34 hP (by rwa [hZP]) (by rw [hZP]; exact hZ4) u hu
    (mem_inf.mp huuZ).2

end CFSG.ComponentClassification.GrSLit
