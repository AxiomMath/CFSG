module

public import CFSG.GH74.GLS.SP.GlueBN

public section

open CFSG.GH74.BNPair
open scoped Pointwise

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

section Generic

variable {X : Type*} [Group X] {B N : Subgroup X} [(cartan B N).Normal]
  {s t : WeylGroup B N}

open Classical in
theorem rank_two_lengths (h : IsTitsSystem B N {s, t}) (hst : s ≠ t) (hcomm : s * t ≠ t * s) :
    wordLength (({s, t} : Finset (WeylGroup B N)) : Set (WeylGroup B N)) s = 1 ∧
    wordLength (({s, t} : Finset (WeylGroup B N)) : Set (WeylGroup B N)) t = 1 ∧
    wordLength (({s, t} : Finset (WeylGroup B N)) : Set (WeylGroup B N)) (s * t) = 2 ∧
    wordLength (({s, t} : Finset (WeylGroup B N)) : Set (WeylGroup B N)) (t * (s * t)) = 3 := by
  set S : Set (WeylGroup B N) := (({s, t} : Finset (WeylGroup B N)) : Set (WeylGroup B N)) with hS
  have hsS : s ∈ S := by simp [hS]
  have htS : t ∈ S := by simp [hS]
  have hcore := h.bnCore
  have hJ : ∀ x ∈ S, x * x = 1 := hcore.mul_self_eq_one
  have hs1 : s ≠ 1 := hcore.ne_one s hsS
  have ht1 : t ≠ 1 := hcore.ne_one t htS
  have hss : s * s = 1 := hJ s hsS
  have htt : t * t = 1 := hJ t htS
  have hmem : ∀ x : WeylGroup B N, x ∈ Subgroup.closure S := fun x => h.mem_closure x
  have hℓs : wordLength S s = 1 := by
    have h1 := wordLength_gen_le_one hsS
    have h2 : wordLength S s ≠ 0 := fun h0 =>
      hs1 ((wordLength_eq_zero_iff hJ (hmem s)).1 h0)
    omega
  have hℓt : wordLength S t = 1 := by
    have h1 := wordLength_gen_le_one htS
    have h2 : wordLength S t ≠ 0 := fun h0 =>
      ht1 ((wordLength_eq_zero_iff hJ (hmem t)).1 h0)
    omega
  have hlen1 : ∀ x : WeylGroup B N, wordLength S x = 1 → x ∈ S := by
    intro x hx
    obtain ⟨l, hl, hlen, hprod⟩ := exists_list_length_eq_wordLength hJ (hmem x)
    rw [hx] at hlen
    obtain ⟨y, rfl⟩ := List.length_eq_one_iff.1 hlen
    simp only [List.prod_cons, List.prod_nil, mul_one] at hprod
    exact hprod ▸ hl y (by simp)
  have hinv_t : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hℓst : wordLength S (s * t) = 2 := by
    have h1 := wordLength_gen_mul_le hJ hsS (hmem t)
    have h2 : wordLength S (s * t) ≠ 0 := fun h0 => by
      have := (wordLength_eq_zero_iff hJ (hmem _)).1 h0
      have h3 : s = t⁻¹ := eq_inv_of_mul_eq_one_left this
      exact hst (h3.trans hinv_t)
    have h3 : wordLength S (s * t) ≠ 1 := fun h0 => by
      have h4 := hlen1 _ h0
      simp only [hS, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at h4
      rcases h4 with h5 | h5
      · exact ht1 (mul_eq_left.1 h5)
      · exact hs1 (mul_eq_right.1 h5)
    omega
  have hne1 : t * (s * t) ≠ 1 := fun h0 => by
    have h3 : s * t = t⁻¹ := eq_inv_of_mul_eq_one_right h0
    rw [hinv_t] at h3
    exact hs1 (mul_eq_right.1 h3)
  have hℓtst : wordLength S (t * (s * t)) = 3 := by
    have h1 := wordLength_gen_mul_le hJ htS (hmem (s * t))
    have h2 : wordLength S (t * (s * t)) ≠ 0 := fun h0 =>
      hne1 ((wordLength_eq_zero_iff hJ (hmem _)).1 h0)
    have h3 : wordLength S (t * (s * t)) ≠ 1 := fun h0 => by
      have h4 := hlen1 _ h0
      simp only [hS, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at h4
      rcases h4 with h5 | h5
      · apply hcomm
        calc s * t = (t * t) * (s * t) := by rw [htt, one_mul]
          _ = t * (t * (s * t)) := by rw [mul_assoc]
          _ = t * s := by rw [h5]
      · have h6 : s * t = 1 := mul_left_cancel (h5.trans (mul_one t).symm)
        have h7 : s = t⁻¹ := eq_inv_of_mul_eq_one_left h6
        exact hst (h7.trans hinv_t)
    have h4 : wordLength S (t * (s * t)) ≠ 2 := fun h0 => by
      obtain ⟨l, hl, hlen, hprod⟩ := exists_list_length_eq_wordLength hJ (hmem (t * (s * t)))
      rw [h0] at hlen
      obtain ⟨x, y, rfl⟩ := List.length_eq_two.1 hlen
      simp only [List.prod_cons, List.prod_nil, mul_one] at hprod
      have hx : x ∈ S := hl x (by simp)
      have hy : y ∈ S := hl y (by simp)
      simp only [hS, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hx hy
      rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy] at hprod
      · exact hne1 (hprod.symm.trans hss)
      · have h6 : s * t = t * s * t := by rw [hprod, mul_assoc]
        have h5 : s = t * s := mul_right_cancel h6
        exact ht1 (right_eq_mul.1 h5)
      · have h6 : t * s = t * (s * t) := hprod
        have h5 : s = s * t := mul_left_cancel h6
        exact ht1 (left_eq_mul.1 h5)
      · exact hne1 (hprod.symm.trans htt)
    omega
  exact ⟨hℓs, hℓt, hℓst, hℓtst⟩

open Classical in
theorem rank_two_normal_le_of_single (h : IsTitsSystem B N {s, t}) (hst : s ≠ t)
    (hcomm : s * t ≠ t * s) (A : Subgroup X) [A.Normal]
    (hA : A ⊔ B = parabolic B N (({s} : Finset (WeylGroup B N)) : Set (WeylGroup B N))) :
    A ≤ B := by
  obtain ⟨hℓs, hℓt, hℓst, hℓtst⟩ := rank_two_lengths h hst hcomm
  have hsS : s ∈ (({s, t} : Finset (WeylGroup B N)) : Set (WeylGroup B N)) := by simp
  have htS : t ∈ (({s, t} : Finset (WeylGroup B N)) : Set (WeylGroup B N)) := by simp
  have hcore := h.bnCore
  have hJ : ∀ x ∈ (({s, t} : Finset (WeylGroup B N)) : Set (WeylGroup B N)), x * x = 1 :=
    hcore.mul_self_eq_one
  have hss : s * s = 1 := hJ s hsS
  have htt : t * t = 1 := hJ t htS
  have hinv_t : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hsub : ({s} : Set (WeylGroup B N)) ⊆
      (({s, t} : Finset (WeylGroup B N)) : Set (WeylGroup B N)) := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact hsS
  have hcoreS := hcore.mono hsub
  intro a ha
  have haP : a ∈ parabolic B N (({s} : Finset (WeylGroup B N)) : Set (WeylGroup B N)) := by
    rw [← hA]
    exact Subgroup.mem_sup_left ha
  rw [Finset.coe_singleton] at haP
  obtain ⟨w, hw, haw⟩ := hcoreS.mem_parabolic_iff.1 haP
  rcases eq_one_or_eq_of_mem_closure_singleton hss hw with hw1 | hw1
  · rw [hw1] at haw
    exact mem_dc_one.1 haw
  · rw [hw1] at haw
    exfalso
    obtain ⟨nt, hnt⟩ := QuotientGroup.mk_surjective t
    have h1 : (nt : X) ∈ dc B N t := hnt ▸ coe_mem_dc nt
    have h2 : (nt : X)⁻¹ ∈ dc B N t := by
      have := inv_mem_dc h1
      rwa [hinv_t] at this
    have hmul1 : dc B N s * dc B N t ⊆ dc B N (s * t) :=
      hcore.mul_subset_of_lt hsS (h.mem_closure t) (by omega)
    have hmul2 : dc B N t * dc B N (s * t) ⊆ dc B N (t * (s * t)) :=
      hcore.mul_subset_of_lt htS (h.mem_closure _) (by omega)
    have hx1 : a * (nt : X)⁻¹ ∈ dc B N (s * t) :=
      hmul1 (Set.mul_mem_mul haw h2)
    have hx2 : (nt : X) * (a * (nt : X)⁻¹) ∈ dc B N (t * (s * t)) :=
      hmul2 (Set.mul_mem_mul h1 hx1)
    have hxA : (nt : X) * (a * (nt : X)⁻¹) ∈ A := by
      have := (inferInstance : A.Normal).conj_mem a ha (nt : X)
      simpa [mul_assoc] using this
    have hxP : (nt : X) * (a * (nt : X)⁻¹) ∈
        parabolic B N (({s} : Finset (WeylGroup B N)) : Set (WeylGroup B N)) := by
      rw [← hA]
      exact Subgroup.mem_sup_left hxA
    rw [Finset.coe_singleton] at hxP
    obtain ⟨w', hw', hxw'⟩ := hcoreS.mem_parabolic_iff.1 hxP
    have hw'eq : w' = t * (s * t) := h.dc_injective (dc_eq_of_mem hxw' hx2)
    rw [hw'eq] at hw'
    rcases eq_one_or_eq_of_mem_closure_singleton hss hw' with h5 | h5
    · rw [h5, wordLength_one] at hℓtst
      omega
    · rw [h5] at hℓtst
      omega

open Classical in
theorem rank_two_normal_sup_eq_top_or_le (h : IsTitsSystem B N {s, t}) (hst : s ≠ t)
    (hcomm : s * t ≠ t * s) (A : Subgroup X) [A.Normal] : A ⊔ B = ⊤ ∨ A ≤ B := by
  obtain ⟨J, hJ, hAJ⟩ := h.exists_parabolic (le_sup_right : B ≤ A ⊔ B)
  by_cases hsJ : s ∈ J <;> by_cases htJ : t ∈ J
  · left
    have : J = {s, t} := Finset.Subset.antisymm hJ (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption)
    rw [hAJ, this]
    exact h.parabolic_univ
  · right
    have hJs : J = {s} := by
      apply Finset.Subset.antisymm
      · intro x hx
        have := hJ hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with rfl | rfl
        · simp
        · exact absurd hx htJ
      · simpa using hsJ
    exact rank_two_normal_le_of_single h hst hcomm A (by rw [hAJ, hJs])
  · right
    have hJt : J = {t} := by
      apply Finset.Subset.antisymm
      · intro x hx
        have := hJ hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with rfl | rfl
        · exact absurd hx hsJ
        · simp
      · simpa using htJ
    have h' : IsTitsSystem B N {t, s} := by rwa [Finset.pair_comm] at h
    exact rank_two_normal_le_of_single h' hst.symm (Ne.symm hcomm) A (by rw [hAJ, hJt])
  · right
    have hJe : J = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro x hx
      have := hJ hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with rfl | rfl
      · exact hsJ hx
      · exact htJ hx
    have : A ≤ A ⊔ B := le_sup_left
    rw [hAJ, hJe, Finset.coe_empty, parabolic_empty] at this
    exact this

end Generic

end CFSG.GH74.GLS.Stage2.Bender.Thm1

namespace CFSG.GH74.GLS.SP

open CFSG.GH74.GLS.Stage2.Bender.Thm1

section RGD

variable {X : Type*} [Group X] {n : ℕ} {H : Subgroup X} {r₁ r₂ : X} {U : Subgroup X}
  {root : ℤ → Subgroup X} (R : RGD2 n H r₁ r₂ U root)

include R in
theorem RGD2.orderOf_w₁_mul_w₂ [(cartan (H ⊔ U) R.N).Normal] : orderOf (R.w₁ * R.w₂) = n := by
  have := R.normal_H_subgroupOf
  have h3 := R.three_le
  have hn : 0 < n := by omega
  have hmk : ∀ m : ℕ, (R.w₁ * R.w₂) ^ m =
      (((⟨r₁, R.r₁_mem_N⟩ * ⟨r₂, R.r₂_mem_N⟩ : R.N) ^ m : R.N) : WeylGroup (H ⊔ U) R.N) := by
    intro m
    rfl
  have hpow : ∀ m : ℕ, (R.w₁ * R.w₂) ^ m = 1 ↔ (r₁ * r₂) ^ m ∈ H := by
    intro m
    rw [hmk m, mk_eq_one_iff]
    have hN : (r₁ * r₂) ^ m ∈ R.N := R.N.pow_mem (R.N.mul_mem R.r₁_mem_N R.r₂_mem_N) m
    have hBN := R.B_inf_N
    constructor
    · intro h
      have : (r₁ * r₂) ^ m ∈ (H ⊔ U) ⊓ R.N := ⟨h, hN⟩
      rwa [hBN] at this
    · intro h
      exact (le_sup_left : H ≤ H ⊔ U) h
  rw [orderOf_eq_iff hn]
  refine ⟨(hpow n).2 R.pow, fun m hmn hm0 hone => ?_⟩
  have hmH := (hpow m).1 hone
  have hB : (r₁ * r₂) ^ m ∈ H ⊔ U := (le_sup_left : H ≤ H ⊔ U) hmH
  have h1 := R.pos_of_mem_B hB (R.actsPos_pow m) (p := 0)
    ⟨by rw [Rt_zero hn], by rw [Rt_zero hn]; omega⟩
  have h2 := R.pos_of_mem_B hB (R.actsPos_pow m) (p := (n : ℤ) - 1)
    ⟨by rw [Rt_pred hn]; omega, by rw [Rt_pred hn]⟩
  have h4 := rot_pos h3 h1 h2
  have h5 : (m : ℤ) % n = m := Int.emod_eq_of_lt (by omega) (by omega)
  omega

include R in
theorem RGD2.isSolvable_B : Group.IsSolvable ↥(H ⊔ U) := by
  have : Group.IsNilpotent U := R.nilpotent
  have hUB : U ≤ H ⊔ U := le_sup_right
  have hnormal : (U.subgroupOf (H ⊔ U)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hUB]
    intro u b hu hb
    exact (Subgroup.mem_normalizer_iff.1 (R.B_le_normalizer_U hb) u).1 hu
  have hUsolv : Group.IsSolvable ↥(U.subgroupOf (H ⊔ U)) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hUB).toMonoidHom) (MulEquiv.injective _)
  have key : ∀ x : ↥(H ⊔ U), ∃ h ∈ H, ∃ hB : h ∈ H ⊔ U,
      (QuotientGroup.mk x : ↥(H ⊔ U) ⧸ U.subgroupOf (H ⊔ U)) = QuotientGroup.mk ⟨h, hB⟩ := by
    rintro ⟨x, hx⟩
    have hx' : x ∈ (H : Set X) * (U : Set X) := by rw [← R.coe_sup_HU]; exact hx
    obtain ⟨h, hh, u, hu, rfl⟩ := hx'
    refine ⟨h, hh, (le_sup_left : H ≤ H ⊔ U) hh, ?_⟩
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    change (h * u)⁻¹ * h ∈ U
    rw [show (h * u)⁻¹ * h = u⁻¹ by group]
    exact U.inv_mem hu
  have hquot : Group.IsSolvable (↥(H ⊔ U) ⧸ U.subgroupOf (H ⊔ U)) :=
    Group.isSolvable_of_comm fun a b => by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
      obtain ⟨h, hh, hB, hxh⟩ := key x
      obtain ⟨h', hh', hB', hyh⟩ := key y
      rw [hxh, hyh, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      exact congrArg _ (Subtype.ext (R.comm_H h hh h' hh'))
  exact Group.isSolvable_of_subgroup_quotient (U.subgroupOf (H ⊔ U))

include R in
theorem RGD2.eq_bot_of_normal_abelian [(cartan (H ⊔ U) R.N).Normal]
    (hgen : (H ⊔ U) ⊔ R.N = ⊤) (hns : ¬ Group.IsSolvable X)
    (hC : ∀ h ∈ H, (∀ u ∈ U, h * u = u * h) → h = 1)
    (A : Subgroup X) [A.Normal] (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) : A = ⊥ := by
  have hT := R.isTitsSystem hgen
  have hst : R.w₁ ≠ R.w₂ := R.weyl_ne
  have h3 := R.three_le
  have hcomm : R.w₁ * R.w₂ ≠ R.w₂ * R.w₁ := by
    intro hc
    have hw1 : R.w₁ * R.w₁ = 1 := by
      have := R.orderOf_w 0
      have h' := pow_orderOf_eq_one R.w₁
      rwa [show orderOf R.w₁ = 2 from this, sq] at h'
    have hw2 : R.w₂ * R.w₂ = 1 := by
      have := R.orderOf_w 1
      have h' := pow_orderOf_eq_one R.w₂
      rwa [show orderOf R.w₂ = 2 from this, sq] at h'
    have h2 : (R.w₁ * R.w₂) ^ 2 = 1 := by
      calc (R.w₁ * R.w₂) ^ 2 = R.w₁ * (R.w₂ * R.w₁) * R.w₂ := by rw [sq]; group
        _ = R.w₁ * (R.w₁ * R.w₂) * R.w₂ := by rw [← hc]
        _ = (R.w₁ * R.w₁) * (R.w₂ * R.w₂) := by group
        _ = 1 := by rw [hw1, hw2, one_mul]
    have := orderOf_dvd_of_pow_eq_one h2
    rw [R.orderOf_w₁_mul_w₂] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  rcases rank_two_normal_sup_eq_top_or_le hT hst hcomm A with hAtop | hAB
  ·
    exfalso
    apply hns
    have hBsolv := R.isSolvable_B
    have hAsolv : Group.IsSolvable ↥A := Group.isSolvable_of_comm fun a b => Subtype.ext (hA a a.2 b b.2)
    have hsurj : Function.Surjective ((QuotientGroup.mk' A).comp (H ⊔ U).subtype) := by
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      have hx : x ∈ A ⊔ (H ⊔ U) := by rw [hAtop]; trivial
      have hx' : x ∈ (A : Set X) * ((H ⊔ U : Subgroup X) : Set X) := by
        rw [← Subgroup.normal_mul]
        exact hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hx'
      refine ⟨⟨b, hb⟩, ?_⟩
      show QuotientGroup.mk b = (QuotientGroup.mk (a * b) : X ⧸ A)
      rw [QuotientGroup.eq]
      have : b⁻¹ * (a * b) ∈ A := by
        have := (inferInstance : A.Normal).conj_mem a ha b⁻¹
        simpa [mul_assoc] using this
      exact this
    have hquot : Group.IsSolvable (X ⧸ A) := Group.isSolvable_of_surjective hsurj
    exact Group.isSolvable_of_subgroup_quotient A
  ·
    have hsat := R.isSaturated
    have hAH : A ≤ H := by
      intro a ha
      have : a ∈ (H ⊔ U) ⊓ R.N := by
        rw [IsSaturated] at hsat
        rw [hsat, Subgroup.mem_iInf]
        intro m
        refine ⟨(m : X) * a * (m : X)⁻¹, hAB ((inferInstance : A.Normal).conj_mem a ha m), ?_⟩
        simp [mul_assoc]
      rwa [R.B_inf_N] at this
    rw [eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_bot]
    refine hC a (hAH ha) fun u hu => ?_
    have h1 : a * u * a⁻¹ ∈ U := R.conj_mem_U (hAH ha) hu
    have h2 : u * a⁻¹ * u⁻¹ ∈ A := (inferInstance : A.Normal).conj_mem a⁻¹ (A.inv_mem ha) u
    have h3 : a * (u * a⁻¹ * u⁻¹) ∈ A := A.mul_mem ha h2
    have h4 : a * (u * a⁻¹ * u⁻¹) = (a * u * a⁻¹) * u⁻¹ := by group
    have h5 : (a * u * a⁻¹) * u⁻¹ ∈ U := U.mul_mem h1 (U.inv_mem hu)
    have h6 : (a * u * a⁻¹) * u⁻¹ ∈ U ⊓ H := ⟨h5, hAH (h4 ▸ h3)⟩
    rw [R.U_inf_H, Subgroup.mem_bot] at h6
    have h7 : a * u * a⁻¹ = u := mul_inv_eq_one.1 h6
    calc a * u = a * u * a⁻¹ * a := by group
      _ = u * a := by rw [h7]

end RGD

end CFSG.GH74.GLS.SP
