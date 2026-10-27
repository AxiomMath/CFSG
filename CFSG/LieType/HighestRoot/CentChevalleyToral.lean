module

public import CFSG.LieType.Chevalley.OddToralInvolutionComponents

public section

namespace CFSG.LieType.HighestRoot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem commutator_self_eq_of_isPerfect {G : Type*} [Group G] {H : Subgroup G}
    (hH : Group.IsPerfect H) : ⁅H, H⁆ = H := by
  have h := congrArg (Subgroup.map H.subtype) hH.commutator_eq_top
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h
  exact h

theorem le_derivedSeries_of_isPerfect {G : Type*} [Group G] {H : Subgroup G}
    (hH : Group.IsPerfect H) : ∀ n, H ≤ derivedSeries G n
  | 0 => by rw [derivedSeries_zero]; exact le_top
  | n + 1 => by
    rw [derivedSeries_succ, ← commutator_self_eq_of_isPerfect hH]
    exact Subgroup.commutator_mono (le_derivedSeries_of_isPerfect hH n)
      (le_derivedSeries_of_isPerfect hH n)

variable {τ : Tag} {K : Type} [Field K]

theorem le_rootSpan_of_isPerfect
    (hK : ringChar K ≠ 2) {a : Fin τ.rank → Kˣ}
    (ha : ∀ i, a i = 1 ∨ a i = -1) {P : Subgroup (ModGL τ K)} (hP : P ≤ toralCentralizer τ K a)
    (hperf : Group.IsPerfect P) : P ≤ rootSpan τ K (rootCharKernel a) := by
  set X := toralCentralizer τ K a
  set N := (rootSpan τ K (rootCharKernel a)).subgroupOf X
  have hperf' : Group.IsPerfect (P.subgroupOf X) :=
    ⟨by
      have e := Subgroup.subgroupOfEquivOfLe hP
      have h := congrArg (Subgroup.map e.symm.toMonoidHom) hperf.commutator_eq_top
      rw [commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ e.symm.surjective] at h
      rw [commutator_def]
      exact h⟩
  have h2 := le_derivedSeries_of_isPerfect hperf' 2
  have hD : (derivedSeries X 2).map (QuotientGroup.mk' N) = ⊥ :=
    eq_bot_iff.2 ((map_derivedSeries_le_derivedSeries _ 2).trans
      (derivedSeries_two_toralCentralizer_quotient hK ha).le)
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hD
  intro x hx
  have h := hD (h2 (Subgroup.mem_subgroupOf.2 (show ((⟨x, hP hx⟩ : X) : ModGL τ K) ∈ P from hx)))
  exact Subgroup.mem_subgroupOf.1 h

theorem sq_mem_toralRootGroup
    (hK : ringChar K ≠ 2) {a : Fin τ.rank → Kˣ}
    (ha : ∀ i, a i = 1 ∨ a i = -1) {x : ModGL τ K} (hx : x ∈ toralCentralizer τ K a) :
    x ^ 2 ∈ toralRootGroup τ K a := by
  obtain ⟨-, -, -, -, φ, hφ, hφw⟩ := Chevalley_toral_centralizer_root_generated_quotient τ K a
  obtain ⟨q, hq⟩ := hφ (QuotientGroup.mk ⟨x, hx⟩)
  obtain ⟨⟨w, hw⟩, rfl⟩ := QuotientGroup.mk_surjective q
  have hw2 : (QuotientGroup.mk ⟨w, hw⟩ : rootCharStabilizerSubgroup a ⧸
      (kernelReflectionGroup a).subgroupOf (rootCharStabilizerSubgroup a)) ^ 2 = 1 := by
    have h := orderOf_dvd_two_of_charQuotient (maskChar (signTupleBits a))
      (QuotientGroup.mk ⟨w, (mem_rootCharStabilizer_iff hK ha).1 hw⟩)
    have h1 := orderOf_dvd_iff_pow_eq_one.1 h
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1 ⊢
    rw [kernelReflectionGroup_eq_kernelWeylGroup hK ha]
    exact h1
  have h := congrArg (· ^ 2) hq
  rw [← map_pow, hw2, map_one, ← QuotientGroup.mk_pow, eq_comm, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at h
  exact h

variable [Finite K]

theorem sq_eq_one_of_mem_torusGroup
    (hK3 : Nat.card K = 3) {h : ModGL τ K}
    (hh : h ∈ torusGroup τ K) : h ^ 2 = 1 := by
  have := pow_card_sub_one_eq_one_of_mem_diagonalGroup (torusGroup_le_diagonalGroup hh)
  rwa [hK3] at this

theorem sq_mem_rootSpan_of_mem_toralRootGroup
    (hK3 : Nat.card K = 3) {a : Fin τ.rank → Kˣ}
    {x : ModGL τ K} (hx : x ∈ toralRootGroup τ K a) :
    x ^ 2 ∈ rootSpan τ K (rootCharKernel a) := by
  have hT := torusGroup_le_normalizer_rootSpan (K := K) (S := rootCharKernel a)
    fun _ hα => hα.1
  have hx' : x ∈ ((torusGroup τ K ⊔ rootSpan τ K (rootCharKernel a) : Subgroup (ModGL τ K)) :
      Set (ModGL τ K)) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hT] at hx'
  obtain ⟨t, ht, s, hs, rfl⟩ := hx'
  have hst : t⁻¹ * s * t ∈ rootSpan τ K (rootCharKernel a) := by
    have := (Subgroup.mem_normalizer_iff.1 (hT (inv_mem ht)) s).1 hs
    simpa using this
  have e : (t * s) ^ 2 = t ^ 2 * (t⁻¹ * s * t) * s := by
    rw [sq, sq]
    group
  rw [e, sq_eq_one_of_mem_torusGroup hK3 ht, one_mul]
  exact mul_mem hst hs

theorem mem_rootSpan_of_orderOf_eq_three
    (hK3 : Nat.card K = 3) (hK : ringChar K ≠ 2)
    {a : Fin τ.rank → Kˣ} (ha : ∀ i, a i = 1 ∨ a i = -1) {x : ModGL τ K}
    (hx : x ∈ toralCentralizer τ K a) (h3 : orderOf x = 3) :
    x ∈ rootSpan τ K (rootCharKernel a) := by
  have hx3 : x ^ 3 = 1 := by rw [← h3]; exact pow_orderOf_eq_one x
  have hinv : x = (x ^ 2)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ']
    exact hx3
  have hM : x ∈ toralRootGroup τ K a := by
    rw [hinv]
    exact inv_mem (sq_mem_toralRootGroup hK ha hx)
  rw [hinv]
  exact inv_mem (sq_mem_rootSpan_of_mem_toralRootGroup hK3 hM)

theorem le_rootSpan_of_closure_eq_top
    (hK3 : Nat.card K = 3) (hK : ringChar K ≠ 2)
    {a : Fin τ.rank → Kˣ} (ha : ∀ i, a i = 1 ∨ a i = -1) {L : Subgroup (ModGL τ K)}
    (hL : L ≤ toralCentralizer τ K a) (hgen : Subgroup.closure {y : L | orderOf y = 3} = ⊤) :
    L ≤ rootSpan τ K (rootCharKernel a) := by
  intro x hx
  have hle : Subgroup.closure {y : L | orderOf y = 3} ≤
      (rootSpan τ K (rootCharKernel a)).subgroupOf L :=
    (Subgroup.closure_le _).2 fun y hy => Subgroup.mem_subgroupOf.2
      (mem_rootSpan_of_orderOf_eq_three hK3 hK ha (hL y.2)
        (by rw [Subgroup.orderOf_coe]; exact hy))
  exact Subgroup.mem_subgroupOf.1 (hle (hgen ▸ Subgroup.mem_top (⟨x, hx⟩ : L)))

theorem mem_rootSpan_of_mem_toralRootGroup_of_coprime
    (hK3 : Nat.Coprime 3 (Nat.card K - 1))
    {a : Fin τ.rank → Kˣ} {x : ModGL τ K} (hx : x ∈ toralRootGroup τ K a) (hx3 : x ^ 3 = 1) :
    x ∈ rootSpan τ K (rootCharKernel a) := by
  have hT := torusGroup_le_normalizer_rootSpan (K := K) (S := rootCharKernel a)
    fun _ hα => hα.1
  have hx' : x ∈ ((torusGroup τ K ⊔ rootSpan τ K (rootCharKernel a) : Subgroup (ModGL τ K)) :
      Set (ModGL τ K)) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hT] at hx'
  obtain ⟨t, ht, s, hs, rfl⟩ := hx'
  have hconj : ∀ n : ℕ, t⁻¹ ^ n * s * t ^ n ∈ rootSpan τ K (rootCharKernel a) := by
    intro n
    have h := (Subgroup.mem_normalizer_iff.1 (hT (pow_mem (inv_mem ht) n)) s).1 hs
    simpa [inv_pow] using h
  have e : (t * s) ^ 3 = t ^ 3 * ((t⁻¹ ^ 2 * s * t ^ 2) * (t⁻¹ ^ 1 * s * t ^ 1) * s) := by
    simp only [pow_succ, pow_zero, one_mul]
    group
  have ht3 : t ^ 3 ∈ rootSpan τ K (rootCharKernel a) := by
    have h := hx3
    rw [e] at h
    rw [eq_inv_of_mul_eq_one_left h]
    exact inv_mem (mul_mem (mul_mem (hconj 2) (hconj 1)) hs)
  have hcop : Nat.Coprime 3 (orderOf t) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one
      (pow_card_sub_one_eq_one_of_mem_diagonalGroup (torusGroup_le_diagonalGroup ht))) hK3
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have htS : t ∈ rootSpan τ K (rootCharKernel a) := by
    rw [← hm]
    exact pow_mem ht3 m
  exact mul_mem htS hs

theorem mem_rootSpan_of_pow_three_eq_one
    (hK3 : Nat.Coprime 3 (Nat.card K - 1))
    (hK : ringChar K ≠ 2) {a : Fin τ.rank → Kˣ} (ha : ∀ i, a i = 1 ∨ a i = -1) {x : ModGL τ K}
    (hx : x ∈ toralCentralizer τ K a) (h3 : x ^ 3 = 1) :
    x ∈ rootSpan τ K (rootCharKernel a) := by
  have hinv : x = (x ^ 2)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ']
    exact h3
  have hM : x ∈ toralRootGroup τ K a := by
    rw [hinv]
    exact inv_mem (sq_mem_toralRootGroup hK ha hx)
  exact mem_rootSpan_of_mem_toralRootGroup_of_coprime hK3 hM h3

theorem le_rootSpan_of_closure_eq_top_of_coprime
    (hK3 : Nat.Coprime 3 (Nat.card K - 1))
    (hK : ringChar K ≠ 2) {a : Fin τ.rank → Kˣ} (ha : ∀ i, a i = 1 ∨ a i = -1)
    {L : Subgroup (ModGL τ K)} (hL : L ≤ toralCentralizer τ K a)
    (hgen : Subgroup.closure {y : L | orderOf y = 3} = ⊤) :
    L ≤ rootSpan τ K (rootCharKernel a) := by
  intro x hx
  have hle : Subgroup.closure {y : L | orderOf y = 3} ≤
      (rootSpan τ K (rootCharKernel a)).subgroupOf L :=
    (Subgroup.closure_le _).2 fun y hy => Subgroup.mem_subgroupOf.2
      (mem_rootSpan_of_pow_three_eq_one hK3 hK ha (hL y.2) (by
        have hy' : orderOf (y : ModGL τ K) = 3 := by
          rw [Subgroup.orderOf_coe]
          exact hy
        rw [← hy']
        exact pow_orderOf_eq_one _))
  exact Subgroup.mem_subgroupOf.1 (hle (hgen ▸ Subgroup.mem_top (⟨x, hx⟩ : L)))

end CFSG.LieType.HighestRoot
