module

public import CFSG.CGT.Stroth77.Extension22FourProof

public section

namespace CFSG.CGT.Stroth77

open scoped IsMulCommutative

variable {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S} {m : ℕ}

theorem zmod_castHom_eq_zero_iff_two_mul {k : ℕ} (hk : 1 ≤ k) (x : ZMod (2 ^ k)) :
    ZMod.castHom (n := 2 ^ k) (m := 2) (pow_dvd_pow 2 hk) (ZMod 2) x = 0 ↔
      ∃ y : ZMod (2 ^ k), 2 * y = x := by
  haveI : NeZero (2 ^ k) := ⟨by positivity⟩
  constructor
  · intro h
    have h' : ((x.val : ℕ) : ZMod 2) = 0 := by
      have h1 : (ZMod.cast x : ZMod 2) = 0 := by simpa [ZMod.castHom_apply] using h
      rw [ZMod.cast_eq_val] at h1
      exact h1
    obtain ⟨m, hm⟩ := ZMod.natCast_eq_zero_iff_even.mp h'
    refine ⟨(m : ZMod (2 ^ k)), ?_⟩
    rw [← ZMod.natCast_zmod_val x, hm]
    push_cast
    ring
  · rintro ⟨y, rfl⟩
    rw [map_mul, map_ofNat]
    have h2 : (2 : ZMod 2) = 0 := by decide
    rw [h2, zero_mul]

@[expose] noncomputable def parityTorus (k : Fin 3 → ℕ) (hk : ∀ i, 1 ≤ k i) :
    Torus k →+ (Fin 3 → ZMod 2) where
  toFun x i := ZMod.castHom (n := 2 ^ k i) (m := 2)
    (pow_dvd_pow 2 (hk i)) (ZMod 2) (x i)
  map_zero' := by
    funext i
    simp
  map_add' x y := by
    funext i
    simp [Pi.add_apply, map_add]

theorem parityTorus_surjective (k : Fin 3 → ℕ) (hk : ∀ i, 1 ≤ k i) :
    Function.Surjective (parityTorus k hk) := by
  intro v
  choose t ht using fun i =>
    ZMod.castHom_surjective (n := 2 ^ k i) (m := 2)
      (pow_dvd_pow 2 (hk i)) (v i)
  exact ⟨t, by funext i; exact ht i⟩

theorem parityTorus_gen (k : Fin 3 → ℕ) (hk : ∀ i, 1 ≤ k i) (j : Fin 3) :
    parityTorus k hk (gen k j) = Pi.single j 1 := by
  funext i
  by_cases h : i = j
  · subst h
    simp [parityTorus, gen, Pi.single_apply]
    exact ZMod.cast_one (m := 2) (pow_dvd_pow 2 (hk i))
  · simp [parityTorus, gen, Pi.single_apply, h]

section SquareSubgroup

@[expose] noncomputable def sqSubgroup (D : StrothTypeData B (StrothTypeIndex.t100 m)) :
    Subgroup B where
  carrier := {x | ∃ z : Torus (StrothTypeIndex.t100 m).k, D.ec x = 2 • z}
  one_mem' := ⟨0, by simp⟩
  mul_mem' := by
    rintro x y ⟨zx, hx⟩ ⟨zy, hy⟩
    refine ⟨zx + zy, ?_⟩
    rw [D.ec_mul, hx, hy, smul_add]
  inv_mem' := by
    rintro x ⟨z, hz⟩
    refine ⟨-z, ?_⟩
    rw [D.ec_inv, hz, smul_neg]

theorem mem_sqSubgroup_iff (D : StrothTypeData B (StrothTypeIndex.t100 m)) {x : B} :
    x ∈ sqSubgroup D ↔ ∃ z : Torus (StrothTypeIndex.t100 m).k, D.ec x = 2 • z :=
  Iff.rfl

theorem mem_sqSubgroup_iff_isSquare (D : StrothTypeData B (StrothTypeIndex.t100 m))
    {x : B} : x ∈ sqSubgroup D ↔ IsSquareInSubgroup B (x : S) := by
  rw [mem_sqSubgroup_iff]
  exact (isSquareInSubgroup_iff_even D x.2).symm

instance sqSubgroup_normal (D : StrothTypeData B (StrothTypeIndex.t100 m)) :
    (sqSubgroup D).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [mem_sqSubgroup_iff] at hn ⊢
  obtain ⟨z, hz⟩ := hn
  refine ⟨z, ?_⟩
  rw [D.ec_mul, D.ec_mul, D.ec_inv, hz]
  abel

theorem sq_mem_sqSubgroup (D : StrothTypeData B (StrothTypeIndex.t100 m)) (x : B) :
    x ^ 2 ∈ sqSubgroup D := by
  refine ⟨D.ec x, ?_⟩
  rw [ec_pow D x 2]

end SquareSubgroup

theorem t100_k_pos (hm : 1 ≤ m) (i : Fin 3) : 1 ≤ (StrothTypeIndex.t100 m).k i := by
  fin_cases i
  · simpa [StrothTypeIndex.k, Type100.k] using hm
  · simp [StrothTypeIndex.k, Type100.k]
  · simp [StrothTypeIndex.k, Type100.k]

theorem t100_two_dvd (hm : 1 ≤ m) (i : Fin 3) : 2 ∣ 2 ^ (StrothTypeIndex.t100 m).k i :=
  pow_dvd_pow 2 (t100_k_pos (m := m) hm i)

@[expose] noncomputable def cParity (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hm : 1 ≤ m)
    (x : B) : ZMod 2 :=
  ZMod.castHom (n := 2 ^ (StrothTypeIndex.t100 m).k 0) (m := 2)
    (t100_two_dvd (m := m) hm 0) (ZMod 2) (D.ec x 0)

@[expose] noncomputable def parityHom (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hm : 1 ≤ m) : B →* Multiplicative (Fin 3 → ZMod 2) where
  toFun x := Multiplicative.ofAdd fun i : Fin 3 =>
    ZMod.castHom (n := 2 ^ (StrothTypeIndex.t100 m).k i) (m := 2)
      (t100_two_dvd (m := m) hm i) (ZMod 2) (D.ec x i)
  map_one' := by
    apply Multiplicative.ext
    funext i
    simp
  map_mul' x y := by
    apply Multiplicative.ext
    funext i
    simp only [toAdd_mul, Pi.add_apply]
    rw [D.ec_mul]
    simp [Pi.add_apply, map_add]

theorem parityHom_apply (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hm : 1 ≤ m)
    (x : B) : parityHom D hm x =
      Multiplicative.ofAdd (parityTorus (StrothTypeIndex.t100 m).k
        (t100_k_pos (m := m) hm) (D.ec x)) := rfl

@[expose] noncomputable def cParityHom (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hm : 1 ≤ m) : B →* Multiplicative (ZMod 2) where
  toFun x := Multiplicative.ofAdd (cParity D hm x)
  map_one' := by
    apply Multiplicative.ext
    simp [cParity]
  map_mul' x y := by
    apply Multiplicative.ext
    simp only [toAdd_mul]
    simp [cParity, D.ec_mul, Pi.add_apply, map_add]

@[simp]
theorem cParityHom_apply (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hm : 1 ≤ m)
    (x : B) : cParityHom D hm x = Multiplicative.ofAdd (cParity D hm x) := rfl

theorem parityHom_a (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hm : 1 ≤ m) :
    parityHom D hm D.a = Multiplicative.ofAdd (Pi.single (1 : Fin 3) 1) := by
  rw [parityHom_apply, D.ec_a, parityTorus_gen]

theorem parityHom_b (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hm : 1 ≤ m) :
    parityHom D hm D.b = Multiplicative.ofAdd (Pi.single (2 : Fin 3) 1) := by
  rw [parityHom_apply, D.ec_b, parityTorus_gen]

theorem parityHom_c (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hm : 1 ≤ m) :
    parityHom D hm D.c = Multiplicative.ofAdd (Pi.single (0 : Fin 3) 1) := by
  rw [parityHom_apply, D.ec_c, parityTorus_gen]

theorem parityHom_a_mul_b (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hm : 1 ≤ m) :
    parityHom D hm (D.a * D.b) =
      Multiplicative.ofAdd (Pi.single (1 : Fin 3) 1 + Pi.single (2 : Fin 3) 1) := by
  rw [map_mul, parityHom_a, parityHom_b, ← ofAdd_add]

theorem parityHom_ker_eq_sqSubgroup (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hm : 1 ≤ m) : (parityHom D hm).ker = sqSubgroup D := by
  ext x
  rw [MonoidHom.mem_ker, mem_sqSubgroup_iff]
  constructor
  · intro h
    have hcoord : ∀ i : Fin 3,
        ZMod.castHom (n := 2 ^ (StrothTypeIndex.t100 m).k i) (m := 2)
          (t100_two_dvd (m := m) hm i) (ZMod 2) (D.ec x i) = 0 := by
      intro i
      have h' := congrArg (fun y : Multiplicative (Fin 3 → ZMod 2) => y.toAdd i) h
      simpa [parityHom, toAdd_one] using h'
    choose z hz using fun i =>
      (zmod_castHom_eq_zero_iff_two_mul (t100_k_pos (m := m) hm i) (D.ec x i)).mp
        (by simpa using hcoord i)
    exact ⟨z, by funext i; simpa [Pi.smul_apply] using (hz i).symm⟩
  · rintro ⟨z, hz⟩
    apply Multiplicative.ext
    funext i
    rw [toAdd_one, Pi.zero_apply]
    change ZMod.castHom (n := 2 ^ (StrothTypeIndex.t100 m).k i) (m := 2)
      (t100_two_dvd (m := m) hm i) (ZMod 2) (D.ec x i) = 0
    have hzi : D.ec x i = (2 : ZMod (2 ^ (StrothTypeIndex.t100 m).k i)) * z i := by
      have := congrFun hz i
      simpa [Pi.smul_apply] using this
    rw [hzi, map_mul, map_ofNat]
    have h2 : (2 : ZMod 2) = 0 := by decide
    rw [h2, zero_mul]

theorem parityHom_surjective (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hm : 1 ≤ m) :
    Function.Surjective (parityHom D hm) := by
  intro v
  obtain ⟨t, ht⟩ := parityTorus_surjective (StrothTypeIndex.t100 m).k
    (t100_k_pos (m := m) hm) v.toAdd
  refine ⟨Additive.toMul (D.e.symm t), ?_⟩
  apply Multiplicative.ext
  funext i
  have hDt : D.ec (Additive.toMul (D.e.symm t)) = t := by
    show D.e (Additive.ofMul (Additive.toMul (D.e.symm t))) = t
    rw [ofMul_toMul, AddEquiv.apply_symm_apply]
  change ZMod.castHom (n := 2 ^ (StrothTypeIndex.t100 m).k i) (m := 2)
    (t100_two_dvd (m := m) hm i) (ZMod 2)
    (D.ec (Additive.toMul (D.e.symm t)) i) = v.toAdd i
  rw [hDt]
  exact congrFun ht i

theorem sqSubgroup_index (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hm : 1 ≤ m) :
    (sqSubgroup D).index = 8 := by
  rw [← parityHom_ker_eq_sqSubgroup D hm, Subgroup.index_ker]
  rw [MonoidHom.range_eq_top.mpr (parityHom_surjective D hm)]
  simp [Nat.card_eq_fintype_card]













section Squaring

variable [hN : (B.subgroupOf C).Normal] (hcommC : IsMulCommutative C)

theorem sq_mem_of_not_cyclic_quotient_four
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hncyc : ¬ IsCyclic (C ⧸ B.subgroupOf C)) (x : C) :
    ((x : S) * (x : S)) ∈ B := by
  have hcardQ : Nat.card (C ⧸ B.subgroupOf C) = 4 := card_quotient_four hBC hC hrel
  have hexp : ∀ q : C ⧸ B.subgroupOf C, q * q = 1 := by
    rcases cyclic_or_sq_eq_one hcardQ with hcyc | h
    · exact absurd hcyc hncyc
    · exact h
  have hq : QuotientGroup.mk' (B.subgroupOf C) (x * x) = 1 := by
    rw [map_mul]
    exact hexp _
  have hx2 : x * x ∈ B.subgroupOf C := (QuotientGroup.eq_one_iff (x * x)).mp hq
  simpa [Subgroup.mem_subgroupOf] using hx2

theorem exists_sq_eq_of_mem_sqSubgroup
    (D : StrothTypeData B (StrothTypeIndex.t100 m)) {x : B}
    (hx : x ∈ sqSubgroup D) : ∃ b : B, b * b = x := by
  obtain ⟨z, hz⟩ := (mem_sqSubgroup_iff D).mp hx
  refine ⟨Additive.toMul (D.e.symm z), ?_⟩
  apply D.ec_injective
  rw [D.ec_mul]
  have hz' : D.ec (Additive.toMul (D.e.symm z)) = z := by
    show D.e (Additive.ofMul (Additive.toMul (D.e.symm z))) = z
    rw [ofMul_toMul, AddEquiv.apply_symm_apply]
  rw [hz', hz]
  simp [two_smul]

theorem mem_of_sq_mem_sq
    (hcommC : IsMulCommutative C)
    (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hncyc : ¬ IsCyclic (C ⧸ B.subgroupOf C))
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S')
    {x : C} (hx : IsSquareInSubgroup B ((x : S) * (x : S))) :
    (x : S) ∈ B := by
  have hx2B : ((x : S) * (x : S)) ∈ B :=
    sq_mem_of_not_cyclic_quotient_four hBC hC hrel hncyc x
  let x2B : B := ⟨(x : S) * (x : S), hx2B⟩
  have hx2 : x2B ∈ sqSubgroup D :=
    (mem_sqSubgroup_iff_isSquare D).mpr (by simpa [x2B] using hx)
  obtain ⟨b, hb⟩ := exists_sq_eq_of_mem_sqSubgroup D hx2
  let bC : C := ⟨b, hBC b.2⟩
  let y : C := x * bC⁻¹
  have hbC : bC * bC = x * x := by
    apply Subtype.ext
    simpa [bC, x2B] using congrArg (fun z : B => (z : S)) hb
  have hy2 : y * y = 1 := by
    calc
      y * y = (x * x) * (bC * bC)⁻¹ := by
        show (x * bC⁻¹) * (x * bC⁻¹) = (x * x) * (bC * bC)⁻¹
        have hcomm : bC⁻¹ * x = x * bC⁻¹ := hcommC.is_comm.comm bC⁻¹ x
        calc (x * bC⁻¹) * (x * bC⁻¹) = x * (bC⁻¹ * x) * bC⁻¹ := by group
          _ = x * (x * bC⁻¹) * bC⁻¹ := by rw [hcomm]
          _ = (x * x) * (bC * bC)⁻¹ := by group
      _ = 1 := by rw [hbC]; group
  have hy2S : (y : S) * (y : S) = 1 := by
    simpa using congrArg (fun z : C => (z : S)) hy2
  by_cases hyB : (y : S) ∈ B
  · have hx_eq : (x : S) = (y : S) * (b : S) := by
      simp only [y, bC, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk]
      group
    rw [hx_eq]
    exact B.mul_mem hyB b.2
  · exact (hyB (hH (y : S) (hcS y.2) hy2S (hC y.2))).elim

noncomputable def sqQuotientHom
    (hcommC : IsMulCommutative C)
    (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hncyc : ¬ IsCyclic (C ⧸ B.subgroupOf C)) :
    C →* B ⧸ sqSubgroup D :=
  { toFun := fun x =>
      QuotientGroup.mk' (sqSubgroup D)
        ⟨(x : S) * (x : S), sq_mem_of_not_cyclic_quotient_four hBC hC hrel hncyc x⟩
    map_one' := by
      change ((⟨(1 : S) * (1 : S), _⟩ : B) : B ⧸ sqSubgroup D) = 1
      rw [QuotientGroup.eq_one_iff]
      convert (sqSubgroup D).one_mem using 1
      ext
      simp
    map_mul' := by
      intro x y
      change QuotientGroup.mk' (sqSubgroup D)
          ⟨((x * y : C) : S) * ((x * y : C) : S), _⟩ =
        QuotientGroup.mk' (sqSubgroup D)
          ⟨(x : S) * (x : S), _⟩ *
        QuotientGroup.mk' (sqSubgroup D)
          ⟨(y : S) * (y : S), _⟩
      rw [← map_mul]
      congr 1
      apply Subtype.ext
      have hcomm : y * x = x * y := hcommC.is_comm.comm y x
      have h : (x * y : C) * (x * y) = (x * x) * (y * y) := by
        calc (x * y) * (x * y) = x * (y * x) * y := by group
          _ = x * (x * y) * y := by rw [hcomm]
          _ = (x * x) * (y * y) := by group
      simpa only [Subgroup.coe_mul, Subgroup.coe_mk] using congrArg (fun z : C => (z : S)) h }

theorem sqQuotientHom_ker
    (hcommC : IsMulCommutative C)
    (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hncyc : ¬ IsCyclic (C ⧸ B.subgroupOf C))
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') :
    (sqQuotientHom hcommC D hBC hC hrel hncyc).ker = B.subgroupOf C := by
  ext x
  change ((⟨(x : S) * (x : S), sq_mem_of_not_cyclic_quotient_four hBC hC hrel hncyc x⟩ : B) :
      B ⧸ sqSubgroup D) = 1 ↔ x ∈ B.subgroupOf C
  rw [QuotientGroup.eq_one_iff, mem_sqSubgroup_iff_isSquare]
  constructor
  · intro hx
    exact Subgroup.mem_subgroupOf.mpr
      (mem_of_sq_mem_sq hcommC D hBC hC hrel hncyc hH hcS hx)
  · intro hx
    simpa [pow_two] using (mem_sqSubgroup_iff_isSquare D).mp
      (sq_mem_sqSubgroup D ⟨x, Subgroup.mem_subgroupOf.mp hx⟩)

theorem sqQuotientHom_range_card
    (hcommC : IsMulCommutative C)
    (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hncyc : ¬ IsCyclic (C ⧸ B.subgroupOf C))
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') :
    Nat.card (sqQuotientHom hcommC D hBC hC hrel hncyc).range = 4 := by
  have hcard := Subgroup.card_ker_mul_card_range (sqQuotientHom hcommC D hBC hC hrel hncyc)
  rw [sqQuotientHom_ker hcommC D hBC hC hrel hncyc hH hcS] at hcard
  have hker : Nat.card (B.subgroupOf C) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBC).toEquiv
  rw [hker, hrel, mul_comm 4 (Nat.card B)] at hcard
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hcard

end Squaring


section ParityInvariance

theorem cParity_conj_u (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hm : 1 ≤ m)
    (y : B) : cParity D hm (conjBy D.u_mem y) = cParity D hm y := by
  obtain ⟨i, j, l, hy⟩ := torus_eq_zsmul_gens (StrothTypeIndex.t100 m).k (D.ec y)
  have h1 : D.ec (conjBy D.u_mem y) 0 =
      (i : ZMod (2 ^ (StrothTypeIndex.t100 m).k 0)) := by
    rw [ec_conj_u D y, hy, Φu_apply_gens]
    simp [gen, Pi.single_apply]
  have h2 : D.ec y 0 = (i : ZMod (2 ^ (StrothTypeIndex.t100 m).k 0)) := by
    rw [hy]
    simp [gen, Pi.single_apply]
  rw [cParity, cParity, h1, h2]

theorem cParity_conj_ρ (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hm : 1 ≤ m)
    (y : B) : cParity D hm (conjBy D.ρ_mem y) = cParity D hm y := by
  obtain ⟨i, j, l, hy⟩ := torus_eq_zsmul_gens (StrothTypeIndex.t100 m).k (D.ec y)
  have h1 : D.ec (conjBy D.ρ_mem y) 0 =
      ((i - 2 * l : ℤ) : ZMod (2 ^ (StrothTypeIndex.t100 m).k 0)) := by
    rw [ec_conj_ρ D y, hy, Φρ_apply_gens]
    simp [gen, Pi.single_apply]
  have h2 : D.ec y 0 = (i : ZMod (2 ^ (StrothTypeIndex.t100 m).k 0)) := by
    rw [hy]
    simp [gen, Pi.single_apply]
  rw [cParity, cParity, h1, h2]
  rw [Int.cast_sub, Int.cast_mul, Int.cast_ofNat]
  rw [map_sub, map_mul, map_ofNat]
  have h2z : (2 : ZMod 2) = 0 := by decide
  rw [h2z, zero_mul]
  exact sub_zero _

theorem cParityHom_conj_u (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hm : 1 ≤ m)
    (y : B) : cParityHom D hm (conjBy D.u_mem y) = cParityHom D hm y := by
  rw [cParityHom_apply, cParityHom_apply, cParity_conj_u]

theorem cParityHom_conj_ρ (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hm : 1 ≤ m)
    (y : B) : cParityHom D hm (conjBy D.ρ_mem y) = cParityHom D hm y := by
  rw [cParityHom_apply, cParityHom_apply, cParity_conj_ρ]

end ParityInvariance

section QuotientParity

theorem sqSubgroup_le_cParityHom_ker (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hm : 1 ≤ m) : sqSubgroup D ≤ (cParityHom D hm).ker := by
  intro x hx
  rw [MonoidHom.mem_ker]
  rw [mem_sqSubgroup_iff] at hx
  obtain ⟨z, hz⟩ := hx
  apply Multiplicative.ext
  rw [cParityHom_apply, toAdd_one, cParity]
  have h0 : D.ec x 0 = (2 : ZMod (2 ^ (StrothTypeIndex.t100 m).k 0)) * z 0 := by
    have := congrFun hz 0
    simpa [Pi.smul_apply] using this
  rw [h0, map_mul, map_ofNat]
  have h2 : (2 : ZMod 2) = 0 := by decide
  rw [h2, zero_mul]
  rfl

noncomputable def cParityQuotient (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hm : 1 ≤ m) : (B ⧸ sqSubgroup D) →* Multiplicative (ZMod 2) :=
  QuotientGroup.lift (sqSubgroup D) (cParityHom D hm) (sqSubgroup_le_cParityHom_ker D hm)

@[simp]
theorem cParityQuotient_mk (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hm : 1 ≤ m)
    (x : B) :
    cParityQuotient D hm (QuotientGroup.mk' (sqSubgroup D) x) = cParityHom D hm x :=
  QuotientGroup.lift_mk' _ _ x

theorem cParityHom_surjective (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hm : 1 ≤ m) :
    Function.Surjective (cParityHom D hm) := by
  intro w
  let v : Fin 3 → ZMod 2 := fun i => if i = 0 then w.toAdd else 0
  obtain ⟨x, hx⟩ := parityHom_surjective D hm (Multiplicative.ofAdd v)
  refine ⟨x, ?_⟩
  apply Multiplicative.ext
  have h := congrArg (fun y : Multiplicative (Fin 3 → ZMod 2) => y.toAdd 0) hx
  rw [cParityHom_apply, toAdd_ofAdd]
  have h' : (parityHom D hm x).toAdd 0 = cParity D hm x := rfl
  rw [← h', h]
  simp [v]

theorem cParityQuotient_surjective (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hm : 1 ≤ m) : Function.Surjective (cParityQuotient D hm) := by
  intro w
  obtain ⟨x, hx⟩ := cParityHom_surjective D hm w
  exact ⟨QuotientGroup.mk' (sqSubgroup D) x, by
    rw [cParityQuotient_mk]
    exact hx⟩

theorem cParityQuotient_ker_card (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hm : 1 ≤ m) : Nat.card (cParityQuotient D hm).ker = 4 := by
  have hsurj := cParityQuotient_surjective D hm
  have hcard := Subgroup.card_ker_mul_card_range (cParityQuotient D hm)
  rw [MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top] at hcard
  have hQ : Nat.card (B ⧸ sqSubgroup D) = 8 := by
    simpa [Subgroup.index] using sqSubgroup_index D hm
  rw [hQ] at hcard
  have htop : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    simp [Nat.card_eq_fintype_card]
  rw [htop] at hcard
  omega

end QuotientParity

section MainImage

theorem conjBy_inv_conjBy {g : S} (hg : g ∈ Subgroup.normalizer C) (x : C) :
    conjBy (Subgroup.inv_mem _ hg) (conjBy hg x) = x := by
  apply Subtype.ext
  simp only [conjBy, Subgroup.coe_mk]
  group

theorem conjBy_conjBy_of_sq {g : S} (hg : g ∈ Subgroup.normalizer C) (hg2 : g * g = 1)
    (x : C) : conjBy hg (conjBy hg x) = x := by
  apply Subtype.ext
  simp only [conjBy, Subgroup.coe_mk]
  rw [show g⁻¹ = g from inv_eq_of_mul_eq_one_right hg2]
  calc g * (g * (x : S) * g) * g = (g * g) * (x : S) * (g * g) := by group
    _ = x := by rw [hg2]; group

end MainImage

section TorusBasis

structure TorusBasisEquivFour (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (e f : C) where
  E : Torus (Type200.k m) ≃+ Additive C
  E_gen0 : E (gen (Type200.k m) 0) = Additive.ofMul ⟨D.c, hBC D.c.2⟩
  E_gen1 : E (gen (Type200.k m) 1) = Additive.ofMul e
  E_gen2 : E (gen (Type200.k m) 2) = Additive.ofMul f

theorem natCard_torus_type200_eq (hrel : Nat.card C = 4 * Nat.card B)
    (D : StrothTypeData B (StrothTypeIndex.t100 m)) :
    Nat.card (Torus (Type200.k m)) = Nat.card C := by
  rw [natCard_torus_t200, hrel, D.card_t100, natCard_torus]
  simp [Type100.k]
  ring

theorem torusBasisEquivFour_of_generators
    (hcommC : IsMulCommutative C)
    (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (hrel : Nat.card C = 4 * Nat.card B)
    {e f : C}
    (hgen : Subgroup.closure ({(D.c : S), (e : S), (f : S)} : Set S) = C)
    (he_order : orderOf e = 2 ^ (m + 2))
    (hf_order : orderOf f = 2 ^ (m + 2)) :
    Nonempty (TorusBasisEquivFour D hBC e f) := by
  classical
  let cC : C := ⟨D.c, hBC D.c.2⟩
  have hc_order : orderOf cC = 2 ^ m := by
    rw [show cC = Subgroup.inclusion hBC D.c from rfl,
      orderOf_injective (Subgroup.inclusion hBC) (Subgroup.inclusion_injective hBC) D.c,
      D.orderOf_c, m_t100]
  have hcN : cC ^ (2 ^ m) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hc_order]
  have heN : e ^ (2 ^ (m + 2)) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, he_order]
  have hfN : f ^ (2 ^ (m + 2)) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hf_order]
  let k := Type200.k m
  let x : (i : Fin 3) → Additive C :=
    ![Additive.ofMul cC, Additive.ofMul e, Additive.ofMul f]
  have hx : ∀ i, (2 ^ k i) • x i = 0 := by
    intro i
    fin_cases i
    · change (2 ^ k 0) • Additive.ofMul cC = 0
      rw [show k 0 = m by simp [k, Type200.k], ← ofMul_pow, hcN]
      simp
    · change (2 ^ k 1) • Additive.ofMul e = 0
      rw [show k 1 = m + 2 by simp [k, Type200.k], ← ofMul_pow, heN]
      simp
    · change (2 ^ k 2) • Additive.ofMul f = 0
      rw [show k 2 = m + 2 by simp [k, Type200.k], ← ofMul_pow, hfN]
      simp
  let F : Torus k →+ Additive C := torusHomOfGens k x hx
  have hFgen : ∀ i : Fin 3, F (gen k i) = x i := fun i => torusHomOfGens_gen x hx i
  have hsurj : Function.Surjective F := by
    have hK : F.range.toSubgroup' = ⊤ := by
      rw [Subgroup.eq_top_iff']
      intro z
      have hle : Subgroup.closure ({(D.c : S), (e : S), (f : S)} : Set S) ≤
          F.range.toSubgroup'.map C.subtype := by
        rw [Subgroup.closure_le]
        intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl | rfl
        · refine Subgroup.mem_map.mpr ⟨cC, ?_, rfl⟩
          rw [AddSubgroup.mem_toSubgroup']
          have hx0 : x 0 = Additive.ofMul cC := rfl
          rw [← hx0, ← hFgen 0]
          exact ⟨gen k 0, rfl⟩
        · refine Subgroup.mem_map.mpr ⟨e, ?_, rfl⟩
          rw [AddSubgroup.mem_toSubgroup']
          have hx1 : x 1 = Additive.ofMul e := rfl
          rw [← hx1, ← hFgen 1]
          exact ⟨gen k 1, rfl⟩
        · refine Subgroup.mem_map.mpr ⟨f, ?_, rfl⟩
          rw [AddSubgroup.mem_toSubgroup']
          have hx2 : x 2 = Additive.ofMul f := rfl
          rw [← hx2, ← hFgen 2]
          exact ⟨gen k 2, rfl⟩
      have hC : C ≤ F.range.toSubgroup'.map C.subtype := by
        conv_lhs => rw [← hgen]
        exact hle
      have hz : (z : S) ∈ F.range.toSubgroup'.map C.subtype := hC z.2
      rcases Subgroup.mem_map.mp hz with ⟨k', hk, hks⟩
      have hkz : k' = z := Subtype.ext hks
      simpa [hkz] using hk
    have hrange : F.range = ⊤ := by
      apply AddSubgroup.toSubgroup'.injective
      simpa using hK
    exact AddMonoidHom.range_eq_top.mp hrange
  have hcardT : Nat.card (Torus k) = Nat.card (Additive C) := by
    rw [natCard_torus_type200_eq hrel D]
    exact (Nat.card_congr Additive.ofMul).symm
  have hbij : Function.Bijective F :=
    hsurj.bijective_of_nat_card_le (le_of_eq hcardT)
  let E : Torus k ≃+ Additive C := AddEquiv.ofBijective F hbij
  have hE0 : E (gen k 0) = Additive.ofMul cC := by
    show F (gen k 0) = Additive.ofMul cC
    rw [hFgen 0]
    simp [x]
  have hE1 : E (gen k 1) = Additive.ofMul e := by
    show F (gen k 1) = Additive.ofMul e
    rw [hFgen 1]
    simp [x]
  have hE2 : E (gen k 2) = Additive.ofMul f := by
    show F (gen k 2) = Additive.ofMul f
    rw [hFgen 2]
    simp [x]
  exact ⟨{ E := E, E_gen0 := hE0, E_gen1 := hE1, E_gen2 := hE2 }⟩

end TorusBasis

end CFSG.CGT.Stroth77
