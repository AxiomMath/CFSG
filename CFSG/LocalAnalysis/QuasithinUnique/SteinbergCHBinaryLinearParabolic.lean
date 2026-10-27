module

public import CFSG.LocalAnalysis.QuasithinUnique.SteinbergCHBinaryFlagBlocks
public import Mathlib.Tactic.NormNum.Prime
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aOvergroup

public section

namespace CFSG.QuasithinUnique

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped Pointwise

namespace SteinbergCH

@[expose] def compositionCuts (a : List ℕ) : Set ℕ :=
  {c | ∃ j, 0 < j ∧ j < a.length ∧ c = (a.take j).sum}

variable {K : Type*} [Field K] {n : ℕ}

theorem coe_sup_eq_mul_of_permute {G : Type*} [Group G] (H L : Subgroup G)
    (h : (H : Set G) * L = L * H) : ((H ⊔ L : Subgroup G) : Set G) = H * L := by
  let T : Subgroup G :=
    { carrier := (H : Set G) * L
      one_mem' := ⟨1, H.one_mem, 1, L.one_mem, one_mul 1⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩
        have hbc : b * c ∈ (L : Set G) * H := ⟨b, hb, c, hc, rfl⟩
        rw [← h] at hbc
        obtain ⟨c', hc', b', hb', hcb⟩ := hbc
        have hcb : c' * b' = b * c := hcb
        refine ⟨a * c', H.mul_mem ha hc', b' * d, L.mul_mem hb' hd, ?_⟩
        calc a * c' * (b' * d) = a * (c' * b') * d := by group
          _ = a * (b * c) * d := by rw [hcb]
          _ = a * b * (c * d) := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        have hba : b⁻¹ * a⁻¹ ∈ (L : Set G) * H := ⟨b⁻¹, L.inv_mem hb, a⁻¹, H.inv_mem ha, rfl⟩
        rw [← h] at hba
        show (a * b)⁻¹ ∈ (H : Set G) * L
        rw [_root_.mul_inv_rev]
        exact hba }
  have hT : H ⊔ L = T := le_antisymm
    (sup_le (fun x hx => ⟨x, hx, 1, L.one_mem, mul_one x⟩)
      (fun x hx => ⟨1, H.one_mem, x, hx, one_mul x⟩))
    (fun x ⟨a, ha, b, hb, hab⟩ => hab ▸ Subgroup.mul_mem_sup ha hb)
  rw [hT]
  rfl

theorem card_sup_eq_mul_of_permute {G : Type*} [Group G] {H L : Subgroup G}
    (h : (H : Set G) * L = L * H) (hHL : H ⊓ L = ⊥) :
    Nat.card (H ⊔ L : Subgroup G) = Nat.card H * Nat.card L := by
  rw [← Nat.card_prod]
  have hc := congrArg (fun s : Set G => Nat.card s) (coe_sup_eq_mul_of_permute H L h)
  change Nat.card (H ⊔ L : Subgroup G) = Nat.card ((H : Set G) * L : Set G) at hc
  rw [hc]
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun q : H × L =>
    (⟨(q.1 : G) * q.2, Set.mul_mem_mul q.1.2 q.2.2⟩ : ((H : Set G) * L : Set G))) ⟨?_, ?_⟩)
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ hab
    have h' : a * b = a' * b' := congrArg Subtype.val hab
    have hm : a'⁻¹ * a = b' * b⁻¹ := by
      calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
        _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h']
        _ = b' * b⁻¹ := by group
    have hmem : a'⁻¹ * a ∈ H ⊓ L :=
      ⟨H.mul_mem (H.inv_mem ha') ha, hm ▸ L.mul_mem hb' (L.inv_mem hb)⟩
    rw [hHL, Subgroup.mem_bot] at hmem
    obtain rfl : a' = a := inv_mul_eq_one.mp hmem
    obtain rfl : b = b' := mul_left_cancel h'
    rfl
  · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩⟩
    exact ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, rfl⟩

theorem eq_flagStabilizer_borelOvergroupCuts [Finite K] (hK : Nat.card K = 2)
    {Y : Subgroup (SpecialLinearGroup (Fin n) K)} (hU : unitriangular n K ≤ Y) :
    Y = flagStabilizer n K (borelOvergroupCuts Y) := by
  refine le_antisymm (Setup.X7a.le_flagStabilizer_borelOvergroupCuts Y hU) ?_
  rw [(subflag_stabilizer_generation (borelOvergroupCuts Y)).1, Subgroup.closure_le]
  rintro g (hg | ⟨j, hj, hjn, hjI, rfl⟩)
  · rw [SetLike.mem_coe, upperTriangular_eq_unitriangular_of_card_two hK] at hg
    exact hU hg
  · by_contra hr
    exact hjI ⟨hj, hjn, hr⟩

theorem reflection_mem_of_not_mem_borelOvergroupCuts
    {Y : Subgroup (SpecialLinearGroup (Fin n) K)} {j : ℕ} (hj : 1 ≤ j) (hjn : j < n)
    (h : j ∉ borelOvergroupCuts Y) : reflection n K j hj hjn ∈ Y := by
  by_contra hr
  exact h ⟨hj, hjn, hr⟩

theorem reflection_mulVec_single [Finite K] (hK : Nat.card K = 2) (i : ℕ) (hi : 1 ≤ i)
    (hin : i < n) (x : Fin n) :
    (reflection n K i hi hin : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single x 1 =
      Pi.single (adjSwap n i x) 1 := by
  obtain ⟨u, hu⟩ := isMonomial_reflection (K := K) i hi hin
  rw [coe_reflection, hu x, eq_one_of_ne_zero_of_card_two hK (u x).ne_zero, one_smul]

theorem seven_dvd_card_of_reflections [Finite K] (hK : Nat.card K = 2)
    {Y : Subgroup (SpecialLinearGroup (Fin n) K)} (hU : unitriangular n K ≤ Y) {j : ℕ}
    (hj : 1 ≤ j) (hjn : j + 1 < n) (h1 : reflection n K j hj (by omega) ∈ Y)
    (h2 : reflection n K (j + 1) (by omega) hjn ∈ Y) : 7 ∣ Nat.card Y := by
  have : CharP K 2 := charP_two_of_card_two hK
  set a : Fin n := ⟨j - 1, by omega⟩ with ha
  set b : Fin n := ⟨j, by omega⟩ with hb
  set c : Fin n := ⟨j + 1, hjn⟩ with hc
  have hac : a < c := Fin.lt_def.mpr (by simp only [ha, hc]; omega)
  have hab : a ≠ b := fun h => by
    have := congrArg Fin.val h
    simp only [ha, hb] at this
    omega
  have hbc : b ≠ c := fun h => by
    have := congrArg Fin.val h
    simp only [hb, hc] at this
    omega
  set t : SpecialLinearGroup (Fin n) K := SpecialLinearGroup.transvection hac.ne (1 : K) with ht
  set C : SpecialLinearGroup (Fin n) K :=
    reflection n K j hj (by omega) * reflection n K (j + 1) (by omega) hjn * t with hC
  have hCY : C ∈ Y := mul_mem (mul_mem h1 h2) (hU (transvection_mem_unitriangular hac 1))
  set M : Matrix (Fin n) (Fin n) K := (C : Matrix (Fin n) (Fin n) K) with hM
  have hs1 : adjSwap n j = Equiv.swap a b := by rw [adjSwap_of_lt hj (by omega)]
  have hs2 : adjSwap n (j + 1) = Equiv.swap b c := by
    rw [adjSwap_of_lt (by omega) hjn]
    congr 1
  have hMv : ∀ v : Fin n → K, M *ᵥ v =
      (reflection n K j hj (by omega) : Matrix (Fin n) (Fin n) K) *ᵥ
        ((reflection n K (j + 1) (by omega) hjn : Matrix (Fin n) (Fin n) K) *ᵥ
          (v + Pi.single a (1 * v c))) := by
    intro v
    rw [hM, hC, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, ← mulVec_mulVec,
      ← mulVec_mulVec, ht, SpecialLinearGroup.transvection_coe, ← transvection,
      transvection_mulVec]
  have hr1 := reflection_mulVec_single (K := K) (n := n) hK j hj (by omega)
  have hr2 := reflection_mulVec_single (K := K) (n := n) hK (j + 1) (by omega) hjn
  have hMa : M *ᵥ Pi.single a 1 = Pi.single b 1 := by
    rw [hMv, Pi.single_eq_of_ne (Ne.symm hac.ne), mul_zero, Pi.single_zero, add_zero, hr2, hs2,
      Equiv.swap_apply_of_ne_of_ne hab hac.ne, hr1, hs1, Equiv.swap_apply_left]
  have hMb : M *ᵥ Pi.single b 1 = Pi.single c 1 := by
    rw [hMv, Pi.single_eq_of_ne hbc.symm, mul_zero, Pi.single_zero, add_zero, hr2, hs2,
      Equiv.swap_apply_left, hr1, hs1, Equiv.swap_apply_of_ne_of_ne hac.ne' hbc.symm]
  have hMc : M *ᵥ Pi.single c 1 = Pi.single a 1 + Pi.single b 1 := by
    rw [hMv, Pi.single_eq_same, mul_one, mulVec_add, mulVec_add, hr2, hr2, hs2,
      Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hab hac.ne, hr1, hr1, hs1,
      Equiv.swap_apply_right, Equiv.swap_apply_left, add_comm]
  have hMx : ∀ x : Fin n, x ≠ a → x ≠ b → x ≠ c → M *ᵥ Pi.single x 1 = Pi.single x 1 := by
    intro x hxa hxb hxc
    rw [hMv, Pi.single_eq_of_ne hxc.symm, mul_zero, Pi.single_zero, add_zero, hr2, hs2,
      Equiv.swap_apply_of_ne_of_ne hxb hxc, hr1, hs1, Equiv.swap_apply_of_ne_of_ne hxa hxb]
  have hstep : ∀ α β γ : K, M *ᵥ (α • Pi.single a 1 + β • Pi.single b 1 + γ • Pi.single c 1) =
      γ • Pi.single a 1 + (α + γ) • Pi.single b 1 + β • Pi.single c 1 := by
    intro α β γ
    rw [mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, mulVec_smul, hMa, hMb, hMc, smul_add,
      add_smul]
    abel
  have hpow : ∀ v : Fin n → K, (M ^ 7) *ᵥ v =
      M *ᵥ (M *ᵥ (M *ᵥ (M *ᵥ (M *ᵥ (M *ᵥ (M *ᵥ v)))))) := by
    intro v
    simp only [pow_succ', ← mulVec_mulVec, pow_zero, one_mulVec]
  have h11 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  have hea : (M ^ 7) *ᵥ Pi.single a 1 = Pi.single a 1 := by
    have h0 : (Pi.single a 1 : Fin n → K) =
        (1 : K) • Pi.single a 1 + (0 : K) • Pi.single b 1 + (0 : K) • Pi.single c 1 := by
      simp
    rw [hpow, h0, hstep, hstep, hstep, hstep, hstep, hstep, hstep]
    simp [h11]
  have hcomm : ∀ v : Fin n → K, (M ^ 7) *ᵥ (M *ᵥ v) = M *ᵥ ((M ^ 7) *ᵥ v) := by
    intro v
    rw [mulVec_mulVec, mulVec_mulVec, ← pow_succ, ← pow_succ']
  have heb : (M ^ 7) *ᵥ Pi.single b 1 = Pi.single b 1 := by
    rw [← hMa, hcomm, hea]
  have hec : (M ^ 7) *ᵥ Pi.single c 1 = Pi.single c 1 := by
    rw [← hMb, hcomm, heb]
  have hex : ∀ x : Fin n, (M ^ 7) *ᵥ Pi.single x 1 = Pi.single x 1 := by
    intro x
    by_cases hxa : x = a
    · rw [hxa, hea]
    by_cases hxb : x = b
    · rw [hxb, heb]
    by_cases hxc : x = c
    · rw [hxc, hec]
    rw [hpow]
    simp only [hMx x hxa hxb hxc]
  have hC7 : C ^ 7 = 1 := by
    apply Subtype.ext
    rw [SpecialLinearGroup.coe_pow, SpecialLinearGroup.coe_one]
    ext u x
    have := congrFun (hex x) u
    rw [mulVec_single_one, col_apply] at this
    rw [← hM, this, one_apply, Pi.single_apply]
  have hC1 : C ≠ 1 := by
    intro h
    have h' : M *ᵥ Pi.single a 1 = Pi.single a 1 := by
      rw [hM, h, SpecialLinearGroup.coe_one, one_mulVec]
    rw [hMa] at h'
    have := congrFun h' b
    simp [hab.symm] at this
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hord : orderOf (⟨C, hCY⟩ : Y) = 7 :=
    orderOf_eq_prime (Subtype.ext (by simpa using hC7)) (fun h => hC1 (congrArg Subtype.val h))
  rw [← hord]
  exact orderOf_dvd_natCard _

theorem card_GL_two_of_card_two [Finite K] (hK : Nat.card K = 2) :
    Nat.card (GL (Fin 2) K) = 6 := by
  have := Fintype.ofFinite K
  rw [Matrix.card_GL_field, ← Nat.card_eq_fintype_card, hK, Fin.prod_univ_two]
  rfl

theorem false_of_le_joinCuts_singleton [Finite K] (hK : Nat.card K = 2)
    {D : Subgroup (SpecialLinearGroup (Fin n) K)} (hD : Nat.card D = 9)
    (hDU : D ⊓ unitriangular n K = ⊥) {j : ℕ} (hj : 1 ≤ j) (hjn : j < n)
    (hDQ : D ≤ flagStabilizer n K (joinCuts n {j})) : False := by
  have hJ : ∀ x ∈ ({j} : Set ℕ), x + 1 ∉ ({j} : Set ℕ) := by
    intro x hx hx1
    rw [Set.mem_singleton_iff] at hx hx1
    omega
  have hJn : ∀ x ∈ ({j} : Set ℕ), 1 ≤ x ∧ x < n := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    omega
  have hpJ : j - 1 + 1 ∈ ({j} : Set ℕ) := by
    rw [Set.mem_singleton_iff]
    omega
  have hp : j - 1 + 2 ≤ n := by omega
  let β := (blockHom K hJ hpJ hp).comp (Subgroup.inclusion hDQ)
  have hinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro d hd
    have hdR : (d : SpecialLinearGroup (Fin n) K) ∈ blockRadical n K (joinCuts n {j}) := by
      rw [mem_blockRadical_joinCuts_iff hK hJ hJn (hDQ d.2)]
      intro p hp'
      have hpj : p = j - 1 := by
        rw [Set.mem_singleton_iff] at hp'
        omega
      subst hpj
      have := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K)) hd
      simpa [β, coe_blockHom] using this
    have hdU := blockRadical_le_unitriangular _ hdR
    have : (d : SpecialLinearGroup (Fin n) K) ∈ D ⊓ unitriangular n K := ⟨d.2, hdU⟩
    rw [hDU, Subgroup.mem_bot] at this
    exact Subtype.ext this
  have := Nat.card_le_card_of_injective β hinj
  rw [hD, card_GL_two_of_card_two hK] at this
  omega

theorem mem_compositionCuts {a : List ℕ} {c : ℕ} :
    c ∈ compositionCuts a ↔ ∃ j, 0 < j ∧ j < a.length ∧ c = (a.take j).sum :=
  Iff.rfl

theorem cuts_cases {n : ℕ} (hn : n = 4 ∨ n = 5) {I : Set ℕ} (hI : ∀ c ∈ I, 1 ≤ c ∧ c < n)
    (h1 : ∀ c, 1 ≤ c → c + 1 < n → c ∈ I ∨ c + 1 ∈ I)
    (h2 : ∀ j, 1 ≤ j → j < n → ¬ ∀ c, 1 ≤ c → c < n → c ≠ j → c ∈ I) :
    ∃ p₁ p₂ : ℕ, ∃ a : List ℕ, p₁ + 2 ≤ p₂ ∧ p₂ + 2 ≤ n ∧ I = joinCuts n {p₁ + 1, p₂ + 1} ∧
      a.sum = n ∧ (∀ x ∈ a, x = 1 ∨ x = 2) ∧ a.count 2 = 2 ∧ compositionCuts a = I := by
  have hIe : ∀ S : Set ℕ, (∀ c, 1 ≤ c → c < n → (c ∈ I ↔ c ∈ S)) → (∀ c ∈ S, 1 ≤ c ∧ c < n) →
      I = S := fun S hS hSn => Set.ext fun c => ⟨fun h => (hS c (hI c h).1 (hI c h).2).mp h,
        fun h => (hS c (hSn c h).1 (hSn c h).2).mpr h⟩
  rcases hn with rfl | rfl
  · by_cases a1 : 1 ∈ I <;> by_cases a2 : 2 ∈ I <;> by_cases a3 : 3 ∈ I
    all_goals first
      | (exfalso; have h := h1 1 le_rfl (by norm_num); norm_num at h; tauto)
      | (exfalso; have h := h1 2 (by norm_num) (by norm_num); norm_num at h; tauto)
      | (exfalso; apply h2 1 le_rfl (by norm_num); intro c hc1 hcn hcj
         interval_cases c <;> first | assumption | exact absurd rfl hcj)
      | (exfalso; apply h2 2 (by norm_num) (by norm_num); intro c hc1 hcn hcj
         interval_cases c <;> first | assumption | exact absurd rfl hcj)
      | (exfalso; apply h2 3 (by norm_num) (by norm_num); intro c hc1 hcn hcj
         interval_cases c <;> first | assumption | exact absurd rfl hcj)
      | skip
    have hI2 : I = {2} := hIe _ (fun c hc1 hcn => by interval_cases c <;> simp [*])
      (fun c hc => by rw [Set.mem_singleton_iff] at hc; omega)
    refine ⟨0, 2, [2, 2], le_rfl, le_rfl, ?_, rfl, by simp, rfl, ?_⟩
    · rw [hI2]
      ext c
      simp only [joinCuts, Set.mem_singleton_iff, Set.mem_ofPred_eq, Set.mem_insert_iff]
      omega
    · rw [hI2]
      ext c
      rw [mem_compositionCuts, Set.mem_singleton_iff]
      constructor
      · rintro ⟨j, hj0, hjl, rfl⟩
        simp only [List.length_cons, List.length_nil] at hjl
        interval_cases j
        simp
      · rintro rfl
        exact ⟨1, by norm_num, by simp, by simp⟩
  · by_cases a1 : 1 ∈ I <;> by_cases a2 : 2 ∈ I <;> by_cases a3 : 3 ∈ I <;>
      by_cases a4 : 4 ∈ I
    all_goals first
      | (exfalso; have h := h1 1 le_rfl (by norm_num); norm_num at h; tauto)
      | (exfalso; have h := h1 2 (by norm_num) (by norm_num); norm_num at h; tauto)
      | (exfalso; have h := h1 3 (by norm_num) (by norm_num); norm_num at h; tauto)
      | (exfalso; apply h2 1 le_rfl (by norm_num); intro c hc1 hcn hcj
         interval_cases c <;> first | assumption | exact absurd rfl hcj)
      | (exfalso; apply h2 2 (by norm_num) (by norm_num); intro c hc1 hcn hcj
         interval_cases c <;> first | assumption | exact absurd rfl hcj)
      | (exfalso; apply h2 3 (by norm_num) (by norm_num); intro c hc1 hcn hcj
         interval_cases c <;> first | assumption | exact absurd rfl hcj)
      | (exfalso; apply h2 4 (by norm_num) (by norm_num); intro c hc1 hcn hcj
         interval_cases c <;> first | assumption | exact absurd rfl hcj)
      | skip
    ·
      have hI2 : I = {1, 3} := hIe _ (fun c hc1 hcn => by interval_cases c <;> simp [*])
        (fun c hc => by
          rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
          omega)
      refine ⟨1, 3, [1, 2, 2], le_rfl, le_rfl, ?_, rfl, by simp, rfl, ?_⟩
      · rw [hI2]
        ext c
        simp only [joinCuts, Set.mem_singleton_iff, Set.mem_ofPred_eq, Set.mem_insert_iff]
        omega
      · rw [hI2]
        ext c
        rw [mem_compositionCuts, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨j, hj0, hjl, rfl⟩
          simp only [List.length_cons, List.length_nil] at hjl
          interval_cases j <;> simp
        · rintro (rfl | rfl)
          · exact ⟨1, by norm_num, by simp, by simp⟩
          · exact ⟨2, by norm_num, by simp, by simp⟩
    ·
      have hI2 : I = {2, 3} := hIe _ (fun c hc1 hcn => by interval_cases c <;> simp [*])
        (fun c hc => by
          rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
          omega)
      refine ⟨0, 3, [2, 1, 2], by norm_num, le_rfl, ?_, rfl, by simp, rfl, ?_⟩
      · rw [hI2]
        ext c
        simp only [joinCuts, Set.mem_singleton_iff, Set.mem_ofPred_eq, Set.mem_insert_iff]
        omega
      · rw [hI2]
        ext c
        rw [mem_compositionCuts, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨j, hj0, hjl, rfl⟩
          simp only [List.length_cons, List.length_nil] at hjl
          interval_cases j <;> simp
        · rintro (rfl | rfl)
          · exact ⟨1, by norm_num, by simp, by simp⟩
          · exact ⟨2, by norm_num, by simp, by simp⟩
    ·
      have hI2 : I = {2, 4} := hIe _ (fun c hc1 hcn => by interval_cases c <;> simp [*])
        (fun c hc => by
          rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
          omega)
      refine ⟨0, 2, [2, 2, 1], le_rfl, by norm_num, ?_, rfl, by simp, rfl, ?_⟩
      · rw [hI2]
        ext c
        simp only [joinCuts, Set.mem_singleton_iff, Set.mem_ofPred_eq, Set.mem_insert_iff]
        omega
      · rw [hI2]
        ext c
        rw [mem_compositionCuts, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨j, hj0, hjl, rfl⟩
          simp only [List.length_cons, List.length_nil] at hjl
          interval_cases j <;> simp
        · rintro (rfl | rfl)
          · exact ⟨1, by norm_num, by simp, by simp⟩
          · exact ⟨2, by norm_num, by simp, by simp⟩

theorem exists_joinCuts_of_card_nine [Finite K] (hK : Nat.card K = 2) (hn : n = 4 ∨ n = 5)
    {D : Subgroup (SpecialLinearGroup (Fin n) K)} (hD : Nat.card D = 9)
    (hDU : (D : Set (SpecialLinearGroup (Fin n) K)) * (unitriangular n K) =
      (unitriangular n K) * (D : Set (SpecialLinearGroup (Fin n) K))) :
    D ⊓ unitriangular n K = ⊥ ∧ ∃ p₁ p₂ : ℕ, ∃ a : List ℕ, p₁ + 2 ≤ p₂ ∧ p₂ + 2 ≤ n ∧
      D ⊔ unitriangular n K = flagStabilizer n K (joinCuts n {p₁ + 1, p₂ + 1}) ∧
      a.sum = n ∧ (∀ x ∈ a, x = 1 ∨ x = 2) ∧ a.count 2 = 2 ∧
      compositionCuts a = joinCuts n {p₁ + 1, p₂ + 1} := by
  have hU2 : Nat.card (unitriangular n K) = 2 ^ (n * (n - 1) / 2) := by
    rw [card_unitriangular, hK]
  have hinf : D ⊓ unitriangular n K = ⊥ := by
    refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
    rw [hD, hU2]
    exact Nat.Coprime.pow_right _ (by norm_num)
  refine ⟨hinf, ?_⟩
  set Y := D ⊔ unitriangular n K with hY
  have hUY : unitriangular n K ≤ Y := le_sup_right
  have hcard : Nat.card Y = 9 * 2 ^ (n * (n - 1) / 2) := by
    rw [hY, card_sup_eq_mul_of_permute hDU hinf, hD, hU2]
  set I := borelOvergroupCuts Y with hI
  have hYQ : Y = flagStabilizer n K I := eq_flagStabilizer_borelOvergroupCuts hK hUY
  have h7 : ¬ 7 ∣ Nat.card Y := by
    rw [hcard]
    intro h
    rcases (Nat.Prime.dvd_mul (by norm_num)).mp h with h | h
    · norm_num at h
    · have := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).mp
        ((Nat.Prime.dvd_of_dvd_pow (by norm_num) h))
      omega
  have hIn : ∀ c ∈ I, 1 ≤ c ∧ c < n := fun c ⟨hc1, hcn, _⟩ => ⟨hc1, hcn⟩
  have hno7 : ∀ c, 1 ≤ c → c + 1 < n → c ∈ I ∨ c + 1 ∈ I := by
    intro c hc1 hcn
    by_contra h
    push Not at h
    exact h7 (seven_dvd_card_of_reflections hK hUY hc1 hcn
      (reflection_mem_of_not_mem_borelOvergroupCuts hc1 (by omega) h.1)
      (reflection_mem_of_not_mem_borelOvergroupCuts (by omega) hcn h.2))
  have hnoE2 : ∀ j, 1 ≤ j → j < n → ¬ ∀ c, 1 ≤ c → c < n → c ≠ j → c ∈ I := by
    intro j hj hjn h
    refine false_of_le_joinCuts_singleton hK hD hinf hj hjn ?_
    refine le_trans le_sup_left (hYQ.le.trans ?_)
    intro g hg
    rw [mem_flagStabilizer] at hg ⊢
    intro c ⟨hc1, hcn, hcj⟩
    exact hg c (h c hc1 hcn hcj)
  obtain ⟨p₁, p₂, a, hp, hpn, hIJ, ha⟩ := cuts_cases hn hIn hno7 hnoE2
  exact ⟨p₁, p₂, a, hp, hpn, hIJ ▸ hYQ, hIJ ▸ ha⟩

end SteinbergCH

end CFSG.QuasithinUnique
