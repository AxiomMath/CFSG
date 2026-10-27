module

public import CFSG.LocalAnalysis.EvenBN.G2.Radicals
public import CFSG.LieType.Chevalley.KernelComponentRoots

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional

section Units

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem card_sub_one_odd : Odd (Nat.card K - 1) := by
  have := Fintype.ofFinite K
  have hq1 : 1 < Nat.card K := Finite.one_lt_card
  have h2q : 2 ∣ Nat.card K := by
    have h := FiniteField.cast_card_eq_zero K
    rw [Fintype.card_eq_nat_card] at h
    exact (CharP.cast_eq_zero_iff K 2 _).1 h
  obtain ⟨k, hk⟩ := h2q
  exact ⟨k - 1, by omega⟩

theorem units_eq_one_of_zpow_eq_one {β : Kˣ} {e : ℤ}
    (he : e = 1 ∨ e = -1 ∨ e = 2 ∨ e = -2 ∨ ((e = 3 ∨ e = -3) ∧ ¬ 3 ∣ Nat.card K - 1))
    (h : β ^ e = 1) : β = 1 := by
  have hdvd : orderOf β ∣ e.natAbs := Int.natCast_dvd.1 (orderOf_dvd_iff_zpow_eq_one.2 h)
  have hq : orderOf β ∣ Nat.card K - 1 := by
    rw [← Nat.card_units]
    exact orderOf_dvd_natCard β
  have hcop : Nat.Coprime e.natAbs (Nat.card K - 1) := by
    rcases he with rfl | rfl | rfl | rfl | ⟨he3 | he3, h3⟩
    · exact Nat.coprime_one_left _
    · exact Nat.coprime_one_left _
    · exact Nat.coprime_two_left.2 card_sub_one_odd
    · exact Nat.coprime_two_left.2 card_sub_one_odd
    · subst he3
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
    · subst he3
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop hdvd hq)

end Units

theorem eq_zero_of_units_mul_eq' {K : Type} [Field K] {c : Kˣ} (hc : c ≠ 1) {X : K}
    (h : (c : K) * X = X) : X = 0 := by
  have hc' : (c : K) - 1 ≠ 0 := fun h0 => hc (Units.ext (by simpa [sub_eq_zero] using h0))
  have : ((c : K) - 1) * X = 0 := by rw [sub_mul, h, one_mul, sub_self]
  exact (mul_eq_zero.1 this).resolve_left hc'

theorem nonempty_closure_pair_mulEquiv_dihedral {G : Type*} [Group G] {x y : G}
    (hx : x * x = 1) (hy : y * y = 1) (hn : ¬ orderOf (x * y) ∣ 2) :
    Nonempty (closure ({x, y} : Set G) ≃* DihedralGroup (orderOf (x * y))) := by
  classical
  set C := zpowers (x * y) with hC
  have hCc : Nat.card C = orderOf (x * y) := Nat.card_zpowers (x * y)
  let e : Multiplicative (ZMod (Nat.card C)) ≃* C := zmodCyclicMulEquiv inferInstance
  let rot : ZMod (Nat.card C) → G := fun i => (e (Multiplicative.ofAdd i) : C)
  have hrot_mem (i : ZMod (Nat.card C)) : rot i ∈ C := (e (Multiplicative.ofAdd i)).property
  have hrot_add (i j : ZMod (Nat.card C)) : rot (i + j) = rot i * rot j :=
    congrArg Subtype.val (e.map_mul (Multiplicative.ofAdd i) (Multiplicative.ofAdd j))
  have hrot_neg (i : ZMod (Nat.card C)) : rot (-i) = (rot i)⁻¹ :=
    congrArg Subtype.val (e.map_inv (Multiplicative.ofAdd i))
  have hrot_zero : rot 0 = 1 := congrArg Subtype.val e.map_one
  have hxinv : x⁻¹ = x := (eq_inv_of_mul_eq_one_left hx).symm
  have hyinv : y⁻¹ = y := (eq_inv_of_mul_eq_one_left hy).symm
  have hinv : ∀ c ∈ C, x * c * x⁻¹ = c⁻¹ := by
    rintro _ ⟨k, rfl⟩
    have h1 : x * (x * y) * x⁻¹ = (x * y)⁻¹ := by
      rw [mul_inv_rev, hxinv, hyinv, ← mul_assoc, hx, one_mul]
    simp only
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, h1, inv_zpow]
  have hxC : x ∉ C := by
    intro hxC'
    have hyC : y ∈ C := by
      have : x⁻¹ * (x * y) ∈ C := mul_mem (inv_mem hxC') (mem_zpowers _)
      rwa [inv_mul_cancel_left] at this
    have hc : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a := by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      exact (Commute.zpow_zpow_self (x * y) i j).eq
    have hcomm : x * y = y * x := hc x hxC' y hyC
    apply hn
    apply orderOf_dvd_of_pow_eq_one
    have h2 : x * y * (x * y) = x * x * (y * y) := by
      calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [hcomm]
        _ = x * x * (y * y) := by group
    rw [sq, h2, hx, hy, one_mul]
  have hw_mul_rot (i : ZMod (Nat.card C)) : x * rot i = rot (-i) * x := by
    calc x * rot i = (x * rot i * x⁻¹) * x := by rw [hxinv, mul_assoc, hx, mul_one]
      _ = (rot i)⁻¹ * x := by rw [hinv (rot i) (hrot_mem i)]
      _ = rot (-i) * x := by rw [hrot_neg]
  have hrot_mul_w (i : ZMod (Nat.card C)) : rot i * x = x * rot (-i) := by
    calc rot i * x = rot (-(-i)) * x := by rw [neg_neg]
      _ = x * rot (-i) := (hw_mul_rot (-i)).symm
  let hom : DihedralGroup (Nat.card C) →* G :=
    { toFun := fun g => match g with
        | DihedralGroup.r i => rot i
        | DihedralGroup.sr i => x * rot i
      map_one' := hrot_zero
      map_mul' := by
        rintro (i | i) (j | j)
        · change rot (i + j) = rot i * rot j
          exact hrot_add i j
        · change x * rot (j - i) = rot i * (x * rot j)
          calc x * rot (j - i) = x * rot (-i + j) := by rw [sub_eq_add_neg, add_comm]
            _ = x * (rot (-i) * rot j) := by rw [hrot_add]
            _ = (x * rot (-i)) * rot j := by rw [mul_assoc]
            _ = (rot i * x) * rot j := by rw [hrot_mul_w]
            _ = rot i * (x * rot j) := by rw [mul_assoc]
        · change x * rot (i + j) = (x * rot i) * rot j
          rw [hrot_add, mul_assoc]
        · change rot (j - i) = (x * rot i) * (x * rot j)
          calc rot (j - i) = rot (-i + j) := by rw [sub_eq_add_neg, add_comm]
            _ = rot (-i) * rot j := hrot_add (-i) j
            _ = (x * x) * (rot (-i) * rot j) := by rw [hx, one_mul]
            _ = (x * (x * rot (-i))) * rot j := by simp only [mul_assoc]
            _ = (x * (rot i * x)) * rot j := by rw [hrot_mul_w]
            _ = (x * rot i) * (x * rot j) := by simp only [mul_assoc] }
  have hinj : Function.Injective hom := by
    rintro (i | i) (j | j) hij
    · apply congrArg DihedralGroup.r
      change rot i = rot j at hij
      exact congrArg Multiplicative.toAdd (e.injective (Subtype.ext hij))
    · exfalso
      change rot i = x * rot j at hij
      have hwrj : x * rot j ∈ C := hij ▸ hrot_mem i
      exact hxC ((C.mul_mem_cancel_right (hrot_mem j)).mp hwrj)
    · exfalso
      change x * rot i = rot j at hij
      have hwri : x * rot i ∈ C := hij ▸ hrot_mem j
      exact hxC ((C.mul_mem_cancel_right (hrot_mem i)).mp hwri)
    · apply congrArg DihedralGroup.sr
      change x * rot i = x * rot j at hij
      exact congrArg Multiplicative.toAdd (e.injective (Subtype.ext (mul_left_cancel hij)))
  have hrange : hom.range = closure ({x, y} : Set G) := by
    apply le_antisymm
    · have hxm : x ∈ closure ({x, y} : Set G) := Subgroup.subset_closure (by simp)
      have hym : y ∈ closure ({x, y} : Set G) := Subgroup.subset_closure (by simp)
      have hCle : C ≤ closure ({x, y} : Set G) := zpowers_le.2 (mul_mem hxm hym)
      rintro _ ⟨(i | i), rfl⟩
      · exact hCle (hrot_mem i)
      · exact mul_mem hxm (hCle (hrot_mem i))
    · rw [closure_le]
      have hx' : x ∈ hom.range := ⟨DihedralGroup.sr 0, by
        change x * rot 0 = x
        rw [hrot_zero, mul_one]⟩
      have hxy : x * y ∈ hom.range := by
        refine ⟨DihedralGroup.r (Multiplicative.toAdd (e.symm ⟨x * y, mem_zpowers _⟩)), ?_⟩
        change ((e (Multiplicative.ofAdd (Multiplicative.toAdd
          (e.symm ⟨x * y, mem_zpowers _⟩))) : C) : G) = x * y
        rw [ofAdd_toAdd, MulEquiv.apply_symm_apply]
      rintro _ (rfl | rfl)
      · exact hx'
      · have := mul_mem (inv_mem hx') hxy
        rwa [inv_mul_cancel_left] at this
  rw [← hCc]
  exact ⟨(MulEquiv.subgroupCongr hrange.symm).trans (MonoidHom.ofInjective hinj).symm⟩

namespace Model

abbrev pairB (s : Fin Tag.G2.rank → ℤ) : ℤ := ∑ j, Tag.G2.cartan g2ia j * s j

abbrev pairA (s : Fin Tag.G2.rank → ℤ) : ℤ := ∑ j, Tag.G2.cartan g2ir j * s j

@[expose] def yamadaRoot : Fin 6 → Fin Tag.G2.rank → ℤ := ![g2c, g2v, g2r, g2a, g2b, g2u]

@[expose] def yamadaCoroot : Fin 6 → ℤ × ℤ := ![(0, 1), (1, 0), (2, 1), (3, 2), (3, 1), (1, 1)]

@[expose] def yamadaExp (i k : Fin 6) : ℤ :=
  (yamadaCoroot i).1 * pairB (yamadaRoot k) + (yamadaCoroot i).2 * pairA (yamadaRoot k)

theorem yamadaExp_cases (i k : Fin 6) :
    (i = k ∧ yamadaExp i k = 0) ∨
      (i ≠ k ∧ (yamadaExp i k = 1 ∨ yamadaExp i k = -1 ∨ yamadaExp i k = 2 ∨
        yamadaExp i k = -2) ∧ ¬ (i ∈ ({0, 3, 4} : Finset (Fin 6)) ∧
          k ∈ ({0, 3, 4} : Finset (Fin 6)))) ∨
      (i ≠ k ∧ (yamadaExp i k = 3 ∨ yamadaExp i k = -3) ∧ i ∈ ({0, 3, 4} : Finset (Fin 6)) ∧
        k ∈ ({0, 3, 4} : Finset (Fin 6))) := by
  revert i k
  decide

theorem yamadaExp_self : ∀ i : Fin 6, yamadaExp i i = 0 := by decide

theorem yamadaCoroot_cases : ∀ i : Fin 6,
    (yamadaCoroot i).1 = 1 ∨ (yamadaCoroot i).2 = 1 ∨ yamadaCoroot i = (3, 2) := by decide

theorem not_dvd_yamadaExp {K : Type} [Field K] [Finite K] (hK : 4 ≤ Nat.card K) {i : Fin 6}
    (hi : 8 ≤ Nat.card K ∨ i ∉ ({0, 3, 4} : Finset (Fin 6))) {k : Fin 6} (hk : k ≠ i) :
    ¬ ((Nat.card K - 1 : ℕ) : ℤ) ∣ yamadaExp i k := by
  intro hd
  have h0 : yamadaExp i k ≠ 0 := by
    rcases yamadaExp_cases i k with ⟨h, -⟩ | ⟨-, he, -⟩ | ⟨-, he, -⟩
    · exact absurd h.symm hk
    · rcases he with he | he | he | he <;> rw [he] <;> decide
    · rcases he with he | he <;> rw [he] <;> decide
  have hlt : (yamadaExp i k).natAbs < (((Nat.card K - 1 : ℕ) : ℤ)).natAbs := by
    rw [Int.natAbs_natCast]
    rcases yamadaExp_cases i k with ⟨h, -⟩ | ⟨-, he, -⟩ | ⟨-, he, hik⟩
    · exact absurd h.symm hk
    · rcases he with he | he | he | he <;> rw [he] <;> simp <;> omega
    · have h8 : 8 ≤ Nat.card K := hi.resolve_right (not_not.2 hik.1)
      rcases he with he | he <;> rw [he] <;> simp <;> omega
  exact h0 (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd hlt)

section TorusAlgebra

variable (K : Type) [Field K]

@[expose] def hCo (m n : ℤ) : Kˣ →* ModGL .G2 K where
  toFun β := torusElt .G2 K g2ia (β ^ m) * torusElt .G2 K g2ir (β ^ n)
  map_one' := by rw [one_zpow, one_zpow, torusElt_one, torusElt_one, mul_one]
  map_mul' β γ := by
    rw [mul_zpow, mul_zpow, torusElt_mul, torusElt_mul, mul_assoc, mul_assoc,
      ← mul_assoc (torusElt .G2 K g2ia (γ ^ m)), torusElt_mul_comm g2ia g2ir (γ ^ m) (β ^ n)]
    simp only [mul_assoc]

variable {K}

theorem hCo_apply (m n : ℤ) (β : Kˣ) :
    hCo K m n β = torusElt .G2 K g2ia (β ^ m) * torusElt .G2 K g2ir (β ^ n) := rfl

theorem hCo_mem_J (m n : ℤ) (β : Kˣ) : hCo K m n β ∈ J K :=
  mul_mem (torusElt_mem_torusGroup _ _) (torusElt_mem_torusGroup _ _)

theorem hCo_conj {t : Fin Tag.G2.rank → ℤ} (ht : IsRoot .G2 t) (m n : ℤ) (β : Kˣ) (x : K) :
    hCo K m n β * pinnedX .G2 K t x * (hCo K m n β)⁻¹ =
      pinnedX .G2 K t (((β ^ (m * pairB t + n * pairA t) : Kˣ) : K) * x) := by
  rw [hCo_apply, torus_conj ht, ← zpow_mul, ← zpow_mul, ← zpow_add]

theorem torus_coords_inj {t₁ t₂ u₁ u₂ : Kˣ}
    (h : torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂ =
      torusElt .G2 K g2ia u₁ * torusElt .G2 K g2ir u₂) : t₁ = u₁ ∧ t₂ = u₂ := by
  have hc := torus_conj (K := K) isRoot_g2c t₁ t₂ 1
  have hv := torus_conj (K := K) isRoot_g2v t₁ t₂ 1
  rw [h, torus_conj isRoot_g2c] at hc
  rw [h, torus_conj isRoot_g2v] at hv
  have ec1 : ∑ j, Tag.G2.cartan g2ia j * g2c j = 1 := by decide
  have ec2 : ∑ j, Tag.G2.cartan g2ir j * g2c j = 0 := by decide
  have ev1 : ∑ j, Tag.G2.cartan g2ia j * g2v j = 0 := by decide
  have ev2 : ∑ j, Tag.G2.cartan g2ir j * g2v j = 1 := by decide
  rw [ec1, ec2, zpow_one, zpow_zero, zpow_one, zpow_zero, mul_one, mul_one] at hc
  rw [ev1, ev2, zpow_one, zpow_zero, zpow_one, zpow_zero, one_mul, one_mul] at hv
  have hc' := pinnedX_injective .G2 K _ hc
  have hv' := pinnedX_injective .G2 K _ hv
  rw [mul_one, mul_one] at hc' hv'
  exact ⟨(Units.ext hc').symm, (Units.ext hv').symm⟩

variable (K) in
@[expose] def torusPairHom : Kˣ × Kˣ →* J K where
  toFun p := ⟨torusElt .G2 K g2ia p.1 * torusElt .G2 K g2ir p.2,
    mul_mem (torusElt_mem_torusGroup _ _) (torusElt_mem_torusGroup _ _)⟩
  map_one' := Subtype.ext (by
    change torusElt .G2 K g2ia 1 * torusElt .G2 K g2ir 1 = 1
    rw [torusElt_one, torusElt_one, mul_one])
  map_mul' p q := Subtype.ext (by
    change torusElt .G2 K g2ia (p.1 * q.1) * torusElt .G2 K g2ir (p.2 * q.2) =
      torusElt .G2 K g2ia p.1 * torusElt .G2 K g2ir p.2 *
        (torusElt .G2 K g2ia q.1 * torusElt .G2 K g2ir q.2)
    rw [torusElt_mul, torusElt_mul, mul_assoc, mul_assoc,
      ← mul_assoc (torusElt .G2 K g2ia q.1), torusElt_mul_comm g2ia g2ir q.1 p.2]
    simp only [mul_assoc])

theorem torusPairHom_bijective : Function.Bijective (torusPairHom K) := by
  refine ⟨fun p q h => ?_, fun h => ?_⟩
  · obtain ⟨h1, h2⟩ := torus_coords_inj (congrArg Subtype.val h)
    exact Prod.ext h1 h2
  · obtain ⟨t₁, t₂, ht⟩ := exists_eq_torusElt_mul h.2
    exact ⟨(t₁, t₂), Subtype.ext ht.symm⟩

variable (K) in
@[expose] def torusPairEquiv : Kˣ × Kˣ ≃* J K :=
  MulEquiv.ofBijective (torusPairHom K) torusPairHom_bijective

theorem coe_torusPairEquiv (p : Kˣ × Kˣ) :
    ((torusPairEquiv K p : J K) : ModGL .G2 K) =
      torusElt .G2 K g2ia p.1 * torusElt .G2 K g2ir p.2 := rfl

variable (K) in
@[expose] def cartanAut : Kˣ × Kˣ ≃* Kˣ × Kˣ where
  toFun p := (p.1 ^ (-1 : ℤ) * p.2 ^ (2 : ℤ), p.1 ^ (2 : ℤ) * p.2 ^ (-3 : ℤ))
  invFun p := (p.1 ^ (3 : ℤ) * p.2 ^ (2 : ℤ), p.1 ^ (2 : ℤ) * p.2)
  left_inv p := by
    refine Prod.ext ?_ ?_
    · change (p.1 ^ (-1 : ℤ) * p.2 ^ (2 : ℤ)) ^ (3 : ℤ) * (p.1 ^ (2 : ℤ) * p.2 ^ (-3 : ℤ)) ^ (2 : ℤ)
        = p.1
      simp only [mul_zpow, ← zpow_mul]
      rw [mul_mul_mul_comm, ← zpow_add, ← zpow_add]
      norm_num
    · change (p.1 ^ (-1 : ℤ) * p.2 ^ (2 : ℤ)) ^ (2 : ℤ) * (p.1 ^ (2 : ℤ) * p.2 ^ (-3 : ℤ)) = p.2
      simp only [mul_zpow, ← zpow_mul]
      rw [mul_mul_mul_comm, ← zpow_add, ← zpow_add]
      norm_num
  right_inv p := by
    refine Prod.ext ?_ ?_
    · change (p.1 ^ (3 : ℤ) * p.2 ^ (2 : ℤ)) ^ (-1 : ℤ) * (p.1 ^ (2 : ℤ) * p.2) ^ (2 : ℤ) = p.1
      simp only [mul_zpow, ← zpow_mul]
      rw [mul_mul_mul_comm, ← zpow_add, ← zpow_add]
      norm_num
    · change (p.1 ^ (3 : ℤ) * p.2 ^ (2 : ℤ)) ^ (2 : ℤ) * (p.1 ^ (2 : ℤ) * p.2) ^ (-3 : ℤ) = p.2
      simp only [mul_zpow, ← zpow_mul]
      rw [mul_mul_mul_comm, ← zpow_add, ← zpow_add]
      norm_num
  map_mul' p q := by
    refine Prod.ext ?_ ?_
    · change (p.1 * q.1) ^ (-1 : ℤ) * (p.2 * q.2) ^ (2 : ℤ) =
        p.1 ^ (-1 : ℤ) * p.2 ^ (2 : ℤ) * (q.1 ^ (-1 : ℤ) * q.2 ^ (2 : ℤ))
      rw [mul_zpow, mul_zpow, mul_mul_mul_comm]
    · change (p.1 * q.1) ^ (2 : ℤ) * (p.2 * q.2) ^ (-3 : ℤ) =
        p.1 ^ (2 : ℤ) * p.2 ^ (-3 : ℤ) * (q.1 ^ (2 : ℤ) * q.2 ^ (-3 : ℤ))
      rw [mul_zpow, mul_zpow, mul_mul_mul_comm]

variable (K) in
@[expose] def torusChars : J K ≃* Kˣ × Kˣ := (torusPairEquiv K).symm.trans (cartanAut K)

theorem torusChars_hA (β : Kˣ) :
    torusChars K ⟨torusElt .G2 K g2ir β, torusElt_mem_torusGroup _ _⟩ =
      (β ^ (2 : ℤ), β ^ (-3 : ℤ)) := by
  have h : (⟨torusElt .G2 K g2ir β, torusElt_mem_torusGroup _ _⟩ : J K) =
      torusPairEquiv K (1, β) :=
    Subtype.ext (by rw [coe_torusPairEquiv, torusElt_one, one_mul])
  rw [torusChars, MulEquiv.trans_apply, h, MulEquiv.symm_apply_apply]
  refine Prod.ext ?_ ?_
  · change (1 : Kˣ) ^ (-1 : ℤ) * β ^ (2 : ℤ) = β ^ (2 : ℤ)
    rw [one_zpow, one_mul]
  · change (1 : Kˣ) ^ (2 : ℤ) * β ^ (-3 : ℤ) = β ^ (-3 : ℤ)
    rw [one_zpow, one_mul]

variable (K) in
abbrev Ji (i : Fin 6) : Subgroup (ModGL .G2 K) := torusFix K (yamadaRoot i)

theorem isRoot_yamadaRoot (k : Fin 6) : IsRoot .G2 (yamadaRoot k) := by
  fin_cases k
  exacts [isRoot_g2c, isRoot_g2v, isRoot_g2r, isRoot_g2a, isRoot_g2b, isRoot_g2u]

theorem hCo_conj_yamadaRoot (i k : Fin 6) (β : Kˣ) (x : K) :
    hCo K (yamadaCoroot i).1 (yamadaCoroot i).2 β * pinnedX .G2 K (yamadaRoot k) x *
        (hCo K (yamadaCoroot i).1 (yamadaCoroot i).2 β)⁻¹ =
      pinnedX .G2 K (yamadaRoot k) (((β ^ yamadaExp i k : Kˣ) : K) * x) :=
  hCo_conj (isRoot_yamadaRoot k) _ _ β x

theorem mem_torusFix_of_commute {s : Fin Tag.G2.rank → ℤ} (hs : IsRoot .G2 s) {h : ModGL .G2 K}
    (hh : h ∈ J K) {α : K} (hα : α ≠ 0) (hc : h * pinnedX .G2 K s α = pinnedX .G2 K s α * h) :
    h ∈ torusFix K s := by
  obtain ⟨c, hcs⟩ := exists_torus_scale hh hs
  have hc1 : c = 1 := by
    have h1 := hcs α
    rw [hc, mul_inv_cancel_right] at h1
    have h2 := pinnedX_injective .G2 K _ h1
    exact Units.ext (by
      have : ((c : K) - 1) * α = 0 := by rw [sub_mul, ← h2, one_mul, sub_self]
      rw [Units.val_one]
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hα))
  refine ⟨hh, mem_centralizer_iff.2 fun x hx => ?_⟩
  obtain ⟨y, rfl⟩ := mem_rootSubgroup.1 hx
  have h1 := hcs y
  rw [hc1, Units.val_one, one_mul] at h1
  calc pinnedX .G2 K s y * h = h * pinnedX .G2 K s y * h⁻¹ * h := by rw [h1]
    _ = h * pinnedX .G2 K s y := by group

theorem hCo_mem_Ji (i : Fin 6) (β : Kˣ) :
    hCo K (yamadaCoroot i).1 (yamadaCoroot i).2 β ∈ Ji K i := by
  refine ⟨hCo_mem_J _ _ β, mem_centralizer_iff.2 fun x hx => ?_⟩
  obtain ⟨y, rfl⟩ := mem_rootSubgroup.1 hx
  have h1 := hCo_conj_yamadaRoot (K := K) i i β y
  rw [yamadaExp_self, zpow_zero, Units.val_one, one_mul] at h1
  calc pinnedX .G2 K (yamadaRoot i) y * hCo K (yamadaCoroot i).1 (yamadaCoroot i).2 β =
      hCo K (yamadaCoroot i).1 (yamadaCoroot i).2 β * pinnedX .G2 K (yamadaRoot i) y *
        (hCo K (yamadaCoroot i).1 (yamadaCoroot i).2 β)⁻¹ *
          hCo K (yamadaCoroot i).1 (yamadaCoroot i).2 β := by rw [h1]
    _ = _ := by group

theorem char_eq_one_of_mem_torusFix {s : Fin Tag.G2.rank → ℤ} (hs : IsRoot .G2 s) {t₁ t₂ : Kˣ}
    (h : torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂ ∈ torusFix K s) :
    t₁ ^ pairB s * t₂ ^ pairA s = 1 :=
  torus_char_eq_one hs t₁ t₂ rfl rfl
    (mem_centralizer_iff.1 h.2 _ (mem_rootSubgroup.2 ⟨1, rfl⟩))

theorem hCo_eq_of {m n : ℤ} {β t₁ t₂ : Kˣ} (h₁ : β ^ m = t₁) (h₂ : β ^ n = t₂) :
    hCo K m n β = torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂ := by
  rw [hCo_apply, h₁, h₂]

theorem mem_Ji_iff (i : Fin 6) {h : ModGL .G2 K} :
    h ∈ Ji K i ↔ ∃ β : Kˣ, hCo K (yamadaCoroot i).1 (yamadaCoroot i).2 β = h := by
  refine ⟨fun hh => ?_, fun ⟨β, hβ⟩ => hβ ▸ hCo_mem_Ji i β⟩
  obtain ⟨t₁, t₂, rfl⟩ := exists_eq_torusElt_mul hh.1
  have hχ := char_eq_one_of_mem_torusFix (isRoot_yamadaRoot i) hh
  fin_cases i
  ·
    have e : pairB (yamadaRoot 0) = 1 ∧ pairA (yamadaRoot 0) = 0 := by decide
    simp only [Fin.zero_eta] at hχ
    rw [e.1, e.2, zpow_one, zpow_zero, mul_one] at hχ
    exact ⟨t₂, hCo_eq_of (by rw [hχ]; exact zpow_zero t₂) (zpow_one t₂)⟩
  ·
    have e : pairB (yamadaRoot 1) = 0 ∧ pairA (yamadaRoot 1) = 1 := by decide
    simp only [Fin.mk_one] at hχ
    rw [e.1, e.2, zpow_one, zpow_zero, one_mul] at hχ
    exact ⟨t₁, hCo_eq_of (zpow_one t₁) (by rw [hχ]; exact zpow_zero t₁)⟩
  ·
    have e : pairB (yamadaRoot 2) = -1 ∧ pairA (yamadaRoot 2) = 2 := by decide
    rw [show (⟨2, by decide⟩ : Fin 6) = 2 from rfl, e.1, e.2] at hχ
    have h1 : t₂ ^ (2 : ℤ) = t₁ := by
      rw [zpow_neg_one] at hχ
      exact (inv_mul_eq_one.1 hχ).symm
    exact ⟨t₂, hCo_eq_of h1 (zpow_one t₂)⟩
  ·
    have e : pairB (yamadaRoot 3) = 2 ∧ pairA (yamadaRoot 3) = -3 := by decide
    rw [show (⟨3, by decide⟩ : Fin 6) = 3 from rfl, e.1, e.2] at hχ
    have hb : t₂ ^ (-3 : ℤ) = t₁ ^ (-2 : ℤ) := by
      rw [eq_inv_of_mul_eq_one_right hχ, ← zpow_neg]
    have ha : t₁ ^ (2 : ℤ) = t₂ ^ (3 : ℤ) := by
      rw [← inv_inv (t₂ ^ (3 : ℤ)), ← zpow_neg]
      exact eq_inv_of_mul_eq_one_left hχ
    refine ⟨t₁ * t₂⁻¹, hCo_eq_of ?_ ?_⟩
    · change (t₁ * t₂⁻¹) ^ (3 : ℤ) = t₁
      rw [mul_zpow, inv_zpow', hb, ← zpow_add]
      norm_num
    · change (t₁ * t₂⁻¹) ^ (2 : ℤ) = t₂
      rw [mul_zpow, inv_zpow', ha, ← zpow_add]
      norm_num
  ·
    have e : pairB (yamadaRoot 4) = -1 ∧ pairA (yamadaRoot 4) = 3 := by decide
    rw [show (⟨4, by decide⟩ : Fin 6) = 4 from rfl, e.1, e.2] at hχ
    have h1 : t₂ ^ (3 : ℤ) = t₁ := by
      rw [zpow_neg_one] at hχ
      exact (inv_mul_eq_one.1 hχ).symm
    exact ⟨t₂, hCo_eq_of h1 (zpow_one t₂)⟩
  ·
    have e : pairB (yamadaRoot 5) = 1 ∧ pairA (yamadaRoot 5) = -1 := by decide
    rw [show (⟨5, by decide⟩ : Fin 6) = 5 from rfl, e.1, e.2] at hχ
    have h1 : t₂ ^ (1 : ℤ) = t₁ := by
      rw [zpow_one, zpow_neg_one] at hχ
      rw [zpow_one]
      exact (mul_inv_eq_one.1 hχ).symm
    exact ⟨t₂, hCo_eq_of h1 (zpow_one t₂)⟩

theorem hCo_yamada_injective (i : Fin 6) :
    Function.Injective (hCo K (yamadaCoroot i).1 (yamadaCoroot i).2) := by
  refine (injective_iff_map_eq_one _).2 fun β hβ => ?_
  have h1 : torusElt .G2 K g2ia (β ^ (yamadaCoroot i).1) *
      torusElt .G2 K g2ir (β ^ (yamadaCoroot i).2) =
        torusElt .G2 K g2ia 1 * torusElt .G2 K g2ir 1 := by
    rw [← hCo_apply, hβ, torusElt_one, torusElt_one, one_mul]
  obtain ⟨hm, hn⟩ := torus_coords_inj h1
  rcases yamadaCoroot_cases i with h | h | h
  · rwa [h, zpow_one] at hm
  · rwa [h, zpow_one] at hn
  · rw [h] at hm hn
    have : β = β ^ ((3 : ℤ) - 2) := by norm_num
    rw [this, zpow_sub, hm, hn, mul_inv_cancel]

theorem Ji_eq_range (i : Fin 6) : Ji K i = (hCo K (yamadaCoroot i).1 (yamadaCoroot i).2).range := by
  ext h
  rw [mem_Ji_iff, MonoidHom.mem_range]

variable (K) in
@[expose] def unitsEquivJi (i : Fin 6) : Kˣ ≃* Ji K i :=
  (MonoidHom.ofInjective (hCo_yamada_injective (K := K) i)).trans
    (MulEquiv.subgroupCongr (Ji_eq_range i).symm)

theorem yamada_3_9_1 [Finite K] (i : Fin 6) :
    IsCyclic (Ji K i) ∧ Nat.card (Ji K i) = Nat.card K - 1 :=
  ⟨isCyclic_of_surjective (unitsEquivJi K i).toMonoidHom (unitsEquivJi K i).surjective,
    (Nat.card_congr (unitsEquivJi K i).toEquiv).symm.trans (Nat.card_units K)⟩

theorem mem_Ji_inf_Ji (i k : Fin 6) {h : ModGL .G2 K} :
    h ∈ Ji K i ⊓ Ji K k ↔ ∃ β : Kˣ, β ^ yamadaExp i k = 1 ∧
      hCo K (yamadaCoroot i).1 (yamadaCoroot i).2 β = h := by
  constructor
  · rintro ⟨hi, hk⟩
    obtain ⟨β, rfl⟩ := (mem_Ji_iff i).1 hi
    refine ⟨β, ?_, rfl⟩
    have h1 := hCo_conj_yamadaRoot (K := K) i k β 1
    rw [← mem_centralizer_iff.1 hk.2 _ (mem_rootSubgroup.2 ⟨1, rfl⟩), mul_inv_cancel_right]
      at h1
    have h2 := pinnedX_injective .G2 K _ h1
    rw [mul_one] at h2
    exact Units.ext h2.symm
  · rintro ⟨β, hβ, rfl⟩
    refine ⟨hCo_mem_Ji i β, hCo_mem_J _ _ β, mem_centralizer_iff.2 fun x hx => ?_⟩
    obtain ⟨y, rfl⟩ := mem_rootSubgroup.1 hx
    have h1 := hCo_conj_yamadaRoot (K := K) i k β y
    rw [hβ, Units.val_one, one_mul] at h1
    calc pinnedX .G2 K (yamadaRoot k) y * hCo K (yamadaCoroot i).1 (yamadaCoroot i).2 β =
        hCo K (yamadaCoroot i).1 (yamadaCoroot i).2 β * pinnedX .G2 K (yamadaRoot k) y *
          (hCo K (yamadaCoroot i).1 (yamadaCoroot i).2 β)⁻¹ *
            hCo K (yamadaCoroot i).1 (yamadaCoroot i).2 β := by rw [h1]
      _ = _ := by group

theorem Ji_inf_Ji_eq_bot [Finite K] [CharP K 2] {i k : Fin 6} (hik : i ≠ k)
    (h : ¬ 3 ∣ Nat.card K - 1 ∨
      ¬ (i ∈ ({0, 3, 4} : Finset (Fin 6)) ∧ k ∈ ({0, 3, 4} : Finset (Fin 6)))) :
    Ji K i ⊓ Ji K k = ⊥ := by
  refine eq_bot_iff.2 fun g hg => ?_
  obtain ⟨β, hβ, rfl⟩ := (mem_Ji_inf_Ji i k).1 hg
  have hβ1 : β = 1 := by
    rcases yamadaExp_cases i k with ⟨hik', -⟩ | ⟨-, he, -⟩ | ⟨-, he, hik3⟩
    · exact absurd hik' hik
    · rcases he with he | he | he | he
      · exact units_eq_one_of_zpow_eq_one (Or.inl he) hβ
      · exact units_eq_one_of_zpow_eq_one (Or.inr (Or.inl he)) hβ
      · exact units_eq_one_of_zpow_eq_one (Or.inr (Or.inr (Or.inl he))) hβ
      · exact units_eq_one_of_zpow_eq_one (Or.inr (Or.inr (Or.inr (Or.inl he)))) hβ
    · have h3 : ¬ 3 ∣ Nat.card K - 1 := h.resolve_right (not_not.2 hik3)
      exact units_eq_one_of_zpow_eq_one (Or.inr (Or.inr (Or.inr (Or.inr ⟨he, h3⟩)))) hβ
  rw [hβ1, map_one]
  exact one_mem _

theorem Ji_inf_centralizer_eq (i k : Fin 6) {x : ModGL .G2 K}
    (hx : x ∈ rootSubgroup .G2 K (yamadaRoot k)) (hx1 : x ≠ 1) :
    Ji K i ⊓ centralizer {x} = Ji K i ⊓ Ji K k := by
  obtain ⟨α, rfl⟩ := mem_rootSubgroup.1 hx
  have hα : α ≠ 0 := fun h0 => hx1 (by rw [h0, pinnedX_zero])
  apply le_antisymm
  · rintro h ⟨hi, hc⟩
    exact ⟨hi, mem_torusFix_of_commute (isRoot_yamadaRoot k) hi.1 hα
      (mem_centralizer_singleton_iff.1 hc)⟩
  · rintro h ⟨hi, hk⟩
    exact ⟨hi, mem_centralizer_singleton_iff.2
      (mem_centralizer_iff.1 hk.2 _ (mem_rootSubgroup.2 ⟨α, rfl⟩)).symm⟩

theorem exists_Ji_conj_eq [Finite K] {i k : Fin 6} (hik : Ji K i ⊓ Ji K k = ⊥)
    {x y : ModGL .G2 K} (hx : x ∈ rootSubgroup .G2 K (yamadaRoot k)) (hx1 : x ≠ 1)
    (hy : y ∈ rootSubgroup .G2 K (yamadaRoot k)) (hy1 : y ≠ 1) :
    ∃ h ∈ Ji K i, h * x * h⁻¹ = y := by
  obtain ⟨α, rfl⟩ := mem_rootSubgroup.1 hx
  obtain ⟨α', rfl⟩ := mem_rootSubgroup.1 hy
  have hα : α ≠ 0 := fun h0 => hx1 (by rw [h0, pinnedX_zero])
  have hα' : α' ≠ 0 := fun h0 => hy1 (by rw [h0, pinnedX_zero])
  have hinj : Function.Injective (zpowGroupHom (α := Kˣ) (yamadaExp i k)) := by
    refine (injective_iff_map_eq_one _).2 fun β hβ => ?_
    have hmem : hCo K (yamadaCoroot i).1 (yamadaCoroot i).2 β ∈ Ji K i ⊓ Ji K k :=
      (mem_Ji_inf_Ji i k).2 ⟨β, hβ, rfl⟩
    rw [hik, mem_bot] at hmem
    exact hCo_yamada_injective i (hmem.trans (map_one _).symm)
  obtain ⟨β, hβ⟩ := (Finite.injective_iff_surjective.1 hinj) (Units.mk0 α' hα' * (Units.mk0 α hα)⁻¹)
  refine ⟨_, hCo_mem_Ji i β, ?_⟩
  rw [hCo_conj_yamadaRoot]
  congr 1
  change ((zpowGroupHom (yamadaExp i k) β : Kˣ) : K) * α = α'
  rw [hβ, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, Units.val_mk0, mul_assoc,
    inv_mul_cancel₀ hα, mul_one]

theorem mem_Ji_inf_Ji_three {i k : Fin 6}
    (hik : (i = 0 ∧ k = 3) ∨ (i = 0 ∧ k = 4) ∨ (i = 3 ∧ k = 4)) {h : ModGL .G2 K} :
    h ∈ Ji K i ⊓ Ji K k ↔ ∃ ω : Kˣ, ω ^ 3 = 1 ∧ torusElt .G2 K g2ir ω = h := by
  have hA : ∀ ω : Kˣ, hCo K 0 1 ω = torusElt .G2 K g2ir ω := fun ω => by
    rw [hCo_apply, zpow_zero, zpow_one, torusElt_one, one_mul]
  rw [mem_Ji_inf_Ji]
  rcases hik with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have e : yamadaExp 0 3 = -3 := by decide
    rw [e]
    refine ⟨fun ⟨β, hβ, hβh⟩ => ⟨β, ?_, (hA β).symm.trans hβh⟩,
      fun ⟨ω, hω, hωh⟩ => ⟨ω, ?_, (hA ω).trans hωh⟩⟩
    · rw [zpow_neg, inv_eq_one] at hβ
      exact_mod_cast hβ
    · rw [zpow_neg, inv_eq_one]
      exact_mod_cast hω
  · have e : yamadaExp 0 4 = 3 := by decide
    rw [e]
    exact ⟨fun ⟨β, hβ, hβh⟩ => ⟨β, by exact_mod_cast hβ, (hA β).symm.trans hβh⟩,
      fun ⟨ω, hω, hωh⟩ => ⟨ω, by exact_mod_cast hω, (hA ω).trans hωh⟩⟩
  · have e : yamadaExp 3 4 = 3 := by decide
    rw [e]
    have hB : ∀ β : Kˣ, β ^ 3 = 1 → hCo K 3 2 β = torusElt .G2 K g2ir (β ^ 2) := fun β hβ => by
      rw [hCo_apply, show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, hβ, torusElt_one,
        one_mul, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]
    constructor
    · rintro ⟨β, hβ, rfl⟩
      have hβ' : β ^ 3 = 1 := by exact_mod_cast hβ
      refine ⟨β ^ 2, ?_, (hB β hβ').symm⟩
      rw [← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, hβ', one_pow]
    · rintro ⟨ω, hω, rfl⟩
      have hω2 : (ω ^ 2) ^ 3 = 1 := by
        rw [← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, hω, one_pow]
      refine ⟨ω ^ 2, by exact_mod_cast hω2, ?_⟩
      change hCo K 3 2 (ω ^ 2) = _
      rw [hB _ hω2, ← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hω, one_mul]

theorem torusElt_r_injective : Function.Injective (torusEltHom .G2 K g2ir) := by
  intro a b hab
  refine hCo_yamada_injective (K := K) 0 ?_
  change hCo K 0 1 a = hCo K 0 1 b
  rw [hCo_apply, hCo_apply, zpow_zero, zpow_zero, zpow_one, zpow_one]
  exact congrArg _ hab

theorem yamada_3_9_3 [Finite K] (h3 : 3 ∣ Nat.card K - 1) :
    J₁ K ⊓ J₄ K = J₁ K ⊓ J₅ K ∧ J₁ K ⊓ J₅ K = J₄ K ⊓ J₅ K ∧
      Nat.card (J₁ K ⊓ J₄ K : Subgroup (ModGL .G2 K)) = 3 ∧
      ∀ h : J K, (h : ModGL .G2 K) ∈ J₁ K ⊓ J₄ K ↔
        (torusChars K h).1 ^ (3 : ℤ) = 1 ∧ (torusChars K h).2 = 1 := by
  have e03 := fun h => mem_Ji_inf_Ji_three (K := K) (i := 0) (k := 3) (Or.inl ⟨rfl, rfl⟩) (h := h)
  have e04 := fun h => mem_Ji_inf_Ji_three (K := K) (i := 0) (k := 4)
    (Or.inr (Or.inl ⟨rfl, rfl⟩)) (h := h)
  have e34 := fun h => mem_Ji_inf_Ji_three (K := K) (i := 3) (k := 4)
    (Or.inr (Or.inr ⟨rfl, rfl⟩)) (h := h)
  have hT : J₁ K ⊓ J₄ K = (powMonoidHom 3 : Kˣ →* Kˣ).ker.map (torusEltHom .G2 K g2ir) := by
    ext h
    rw [show (J₁ K ⊓ J₄ K : Subgroup (ModGL .G2 K)) = Ji K 0 ⊓ Ji K 3 from rfl, e03,
      mem_map]
    simp only [MonoidHom.mem_ker, powMonoidHom_apply]
    rfl
  refine ⟨?_, ?_, ?_, fun h => ?_⟩
  · ext h
    exact (e03 h).trans (e04 h).symm
  · ext h
    exact (e04 h).trans (e34 h).symm
  · rw [hT, card_map_of_injective torusElt_r_injective, IsCyclic.card_powMonoidHom_ker,
      Nat.card_units]
    exact Nat.gcd_eq_right h3
  · change (h : ModGL .G2 K) ∈ Ji K 0 ⊓ Ji K 3 ↔ _
    rw [e03]
    constructor
    · rintro ⟨ω, hω, hωh⟩
      have hh : h = ⟨torusElt .G2 K g2ir ω, torusElt_mem_torusGroup _ _⟩ := Subtype.ext hωh.symm
      rw [hh, torusChars_hA]
      refine ⟨?_, ?_⟩
      · rw [← zpow_mul]
        change ω ^ ((2 * 3 : ℕ) : ℤ) = 1
        rw [zpow_natCast, show 2 * 3 = 3 * 2 from rfl, pow_mul, hω, one_pow]
      · rw [zpow_neg, inv_eq_one]
        exact_mod_cast hω
    · rintro ⟨hx, hy⟩
      set p := torusChars K h with hp
      have hh : h = torusPairEquiv K ((cartanAut K).symm p) := by
        rw [hp, torusChars, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
          MulEquiv.apply_symm_apply]
      have hp' : (cartanAut K).symm p = (1, p.1 ^ (2 : ℤ)) := by
        refine Prod.ext ?_ ?_
        · change p.1 ^ (3 : ℤ) * p.2 ^ (2 : ℤ) = 1
          rw [hx, hy, one_zpow, one_mul]
        · change p.1 ^ (2 : ℤ) * p.2 = p.1 ^ (2 : ℤ)
          rw [hy, mul_one]
      refine ⟨p.1 ^ 2, ?_, ?_⟩
      · rw [← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul]
        rw [show p.1 ^ 3 = 1 by exact_mod_cast hx, one_pow]
      · rw [hh, hp', coe_torusPairEquiv, torusElt_one, one_mul]
        exact_mod_cast rfl

theorem torus_g2N (t₁ t₂ : Kˣ) (A B C D E F : K) :
    (torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂) * g2N A B C D E F *
        (torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂)⁻¹ =
      g2N (((t₁ ^ pairB g2r * t₂ ^ pairA g2r : Kˣ) : K) * A)
        (((t₁ ^ pairB g2a * t₂ ^ pairA g2a : Kˣ) : K) * B)
        (((t₁ ^ pairB g2u * t₂ ^ pairA g2u : Kˣ) : K) * C)
        (((t₁ ^ pairB g2v * t₂ ^ pairA g2v : Kˣ) : K) * D)
        (((t₁ ^ pairB g2b * t₂ ^ pairA g2b : Kˣ) : K) * E)
        (((t₁ ^ pairB g2c * t₂ ^ pairA g2c : Kˣ) : K) * F) := by
  have e : ∀ x y : ModGL .G2 K,
      (torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂) * (x * y) *
          (torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂)⁻¹ =
        ((torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂) * x *
          (torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂)⁻¹) *
        ((torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂) * y *
          (torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂)⁻¹) := fun x y => by group
  simp only [g2N, e, torus_conj isRoot_g2r, torus_conj isRoot_g2a, torus_conj isRoot_g2u,
    torus_conj isRoot_g2v, torus_conj isRoot_g2b, torus_conj isRoot_g2c]

theorem hCo_g2N (i : Fin 6) (β : Kˣ) (A B C D E F : K) :
    hCo K (yamadaCoroot i).1 (yamadaCoroot i).2 β * g2N A B C D E F *
        (hCo K (yamadaCoroot i).1 (yamadaCoroot i).2 β)⁻¹ =
      g2N (((β ^ yamadaExp i 2 : Kˣ) : K) * A) (((β ^ yamadaExp i 3 : Kˣ) : K) * B)
        (((β ^ yamadaExp i 5 : Kˣ) : K) * C) (((β ^ yamadaExp i 1 : Kˣ) : K) * D)
        (((β ^ yamadaExp i 4 : Kˣ) : K) * E) (((β ^ yamadaExp i 0 : Kˣ) : K) * F) := by
  rw [hCo_apply, torus_g2N]
  simp only [← zpow_mul, ← zpow_add, yamadaExp]
  rfl

theorem rootSubgroup_yamadaRoot_le_centralizer (i : Fin 6) :
    rootSubgroup .G2 K (yamadaRoot i) ≤ centralizer (Ji K i : Set (ModGL .G2 K)) :=
  fun _ hx => mem_centralizer_iff.2 fun _ hz => (mem_centralizer_iff.1 hz.2 _ hx).symm

theorem map_conj_Ji {g : ModGL .G2 K} {i : Fin 6} {m n : ℤ}
    (h : ∀ β : Kˣ, g * hCo K (yamadaCoroot i).1 (yamadaCoroot i).2 β * g⁻¹ = hCo K m n β) :
    (Ji K i).map (MulAut.conj g).toMonoidHom = (hCo K m n).range := by
  rw [Ji_eq_range, ← MonoidHom.range_comp]
  exact congrArg MonoidHom.range (MonoidHom.ext h)

theorem monomialSubgroup_eq : monomialSubgroup .G2 K = J K ⊔ closure {wa K, wb K} := by
  rw [monomialSubgroup]
  congr 2
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Or.inr rfl
    · exact Or.inl rfl
  · rintro (rfl | rfl)
    exacts [⟨g2ir, rfl⟩, ⟨g2ia, rfl⟩]

variable (K) in
@[expose] def wRoot (s : Fin Tag.G2.rank → ℤ) : ModGL .G2 K :=
  pinnedX .G2 K s 1 * pinnedX .G2 K (-s) 1 * pinnedX .G2 K s 1

theorem weyl_ab_pow :
    (simple .G2 g2ir * simple .G2 g2ia) ^ 6 = 1 ∧
      (simple .G2 g2ir * simple .G2 g2ia) ^ 2 • g2a = -g2c ∧
      (simple .G2 g2ir * simple .G2 g2ia) ^ 3 • g2a = -g2a := by
  refine ⟨eq_one_of_smul ?_ ?_, ?_, ?_⟩ <;>
  · simp only [pow_succ, pow_zero, one_mul, mul_smul, simple_smul]
    exact List.ofFn_injective (by decide +kernel)

theorem pinnedX_a_ne_neg {γ : Fin Tag.G2.rank → ℤ}
    (hγ : γ = g2r ∨ γ = g2a ∨ γ = g2u ∨ γ = g2v ∨ γ = g2b ∨ γ = g2c) :
    pinnedX .G2 K g2a 1 ≠ pinnedX .G2 K (-γ) 1 := by
  intro h
  have h1 : pinnedX .G2 K g2a 1 = 1 := by
    refine eq_one_of_mem_borel_of_mem_neg (posUnipotent_le_borelGroup ?_) ?_
    · exact pinnedX_mem_rootSpan (S := {α | IsRoot .G2 α ∧ 0 < height α})
        ⟨isRoot_g2a, by decide⟩ 1
    · rw [h]
      exact pinnedX_neg_mem_negUnipotent hγ 1
  rw [← pinnedX_zero .G2 K g2a] at h1
  exact one_ne_zero (pinnedX_injective .G2 K _ h1)

section CharTwo

variable [CharP K 2]

theorem canonicalRep_simple_mul' (i : Fin Tag.G2.rank) (w : WeylGroup .G2) :
    canonicalRep (coxeterSystem .G2) K (simple .G2 i * w) =
      weylElt .G2 K i 1 * canonicalRep (coxeterSystem .G2) K w := by
  rw [weylElt_mul_canonicalRep]
  split_ifs
  · rfl
  · rw [show (-1 : Kˣ) = 1 from Units.ext (by simp [CharTwo.neg_eq]), torusElt_one, one_mul]

theorem canonicalRep_wordProd_mul (ω : List (Fin Tag.G2.rank)) (v : WeylGroup .G2) :
    canonicalRep (coxeterSystem .G2) K ((coxeterSystem .G2).wordProd ω * v) =
      (ω.map fun i => weylElt .G2 K i 1).prod * canonicalRep (coxeterSystem .G2) K v := by
  induction ω with
  | nil => rw [CoxeterSystem.wordProd_nil, one_mul, List.map_nil, List.prod_nil, one_mul]
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons, mul_assoc]
    change canonicalRep (coxeterSystem .G2) K (simple .G2 i * _) = _
    rw [canonicalRep_simple_mul', ih, List.map_cons, List.prod_cons, mul_assoc]

theorem canonicalRep_mul_two (w v : WeylGroup .G2) :
    canonicalRep (coxeterSystem .G2) K (w * v) =
      canonicalRep (coxeterSystem .G2) K w * canonicalRep (coxeterSystem .G2) K v := by
  obtain ⟨ω, -, rfl⟩ := (coxeterSystem .G2).exists_isReduced w
  have h := canonicalRep_wordProd_mul (K := K) ω 1
  rw [mul_one, canonicalRep_one, mul_one] at h
  rw [canonicalRep_wordProd_mul, h]

variable (K) in
@[expose] def canonicalRepHom : WeylGroup .G2 →* ModGL .G2 K where
  toFun w := canonicalRep (coxeterSystem .G2) K w
  map_one' := canonicalRep_one _ K
  map_mul' := canonicalRep_mul_two

theorem wa_mul_self : wa K * wa K = 1 := weylElt_mul_self g2ir

theorem wb_mul_self : wb K * wb K = 1 := weylElt_mul_self g2ia

theorem wa_hCo (m n : ℤ) (β : Kˣ) : wa K * hCo K m n β * wa K = hCo K m (m - n) β := by
  have e1 := weylElt_one_mul_torusElt_mul_inv .G2 K g2ir g2ia (β ^ m)
  have e2 := weylElt_mul_torusElt_mul_inv (K := K) g2ir (β ^ n)
  have hinv := ComponentClassification.UnbalancedCatalog.weylElt_inv (K := K) g2ir
  rw [hinv, show -Tag.G2.cartan g2ia g2ir = 1 from rfl, zpow_one] at e1
  rw [hinv] at e2
  rw [hCo_apply, hCo_apply, wa,
    show weylElt .G2 K g2ir 1 * (torusElt .G2 K g2ia (β ^ m) * torusElt .G2 K g2ir (β ^ n)) *
      weylElt .G2 K g2ir 1 = (weylElt .G2 K g2ir 1 * torusElt .G2 K g2ia (β ^ m) *
        weylElt .G2 K g2ir 1) * (weylElt .G2 K g2ir 1 * torusElt .G2 K g2ir (β ^ n) *
          weylElt .G2 K g2ir 1) by
      rw [show weylElt .G2 K g2ir 1 * torusElt .G2 K g2ia (β ^ m) * weylElt .G2 K g2ir 1 *
          (weylElt .G2 K g2ir 1 * torusElt .G2 K g2ir (β ^ n) * weylElt .G2 K g2ir 1) =
          weylElt .G2 K g2ir 1 * torusElt .G2 K g2ia (β ^ m) *
            (weylElt .G2 K g2ir 1 * weylElt .G2 K g2ir 1) * torusElt .G2 K g2ir (β ^ n) *
              weylElt .G2 K g2ir 1 by group,
        ComponentClassification.UnbalancedCatalog.weylElt_mul_self, mul_one]
      group, e1, e2, mul_assoc, ← torusElt_mul, ← zpow_neg, ← zpow_add, sub_eq_add_neg]

theorem wb_hCo (m n : ℤ) (β : Kˣ) : wb K * hCo K m n β * wb K = hCo K (3 * n - m) n β := by
  have e1 := weylElt_mul_torusElt_mul_inv (K := K) g2ia (β ^ m)
  have e2 := weylElt_one_mul_torusElt_mul_inv .G2 K g2ia g2ir (β ^ n)
  have hinv := ComponentClassification.UnbalancedCatalog.weylElt_inv (K := K) g2ia
  rw [hinv] at e1
  rw [hinv, show -Tag.G2.cartan g2ir g2ia = 3 from rfl] at e2
  rw [hCo_apply, hCo_apply, wb,
    show weylElt .G2 K g2ia 1 * (torusElt .G2 K g2ia (β ^ m) * torusElt .G2 K g2ir (β ^ n)) *
      weylElt .G2 K g2ia 1 = (weylElt .G2 K g2ia 1 * torusElt .G2 K g2ia (β ^ m) *
        weylElt .G2 K g2ia 1) * (weylElt .G2 K g2ia 1 * torusElt .G2 K g2ir (β ^ n) *
          weylElt .G2 K g2ia 1) by
      rw [show weylElt .G2 K g2ia 1 * torusElt .G2 K g2ia (β ^ m) * weylElt .G2 K g2ia 1 *
          (weylElt .G2 K g2ia 1 * torusElt .G2 K g2ir (β ^ n) * weylElt .G2 K g2ia 1) =
          weylElt .G2 K g2ia 1 * torusElt .G2 K g2ia (β ^ m) *
            (weylElt .G2 K g2ia 1 * weylElt .G2 K g2ia 1) * torusElt .G2 K g2ir (β ^ n) *
              weylElt .G2 K g2ia 1 by group,
        ComponentClassification.UnbalancedCatalog.weylElt_mul_self, mul_one]
      group, e1, e2, ← mul_assoc, torusElt_mul_comm g2ia g2ir, mul_assoc, ← torusElt_mul,
    ← zpow_neg, ← zpow_mul, ← zpow_add, sub_eq_add_neg, add_comm, mul_comm n 3]
  rw [torusElt_mul_comm g2ir g2ia]

theorem Ji_conj :
    (J₁ K).map (MulAut.conj (wb K)).toMonoidHom = J₅ K ∧
      (J₅ K).map (MulAut.conj (wa K)).toMonoidHom = J₄ K ∧
      (J₂ K).map (MulAut.conj (wa K)).toMonoidHom = J₆ K ∧
      (J₆ K).map (MulAut.conj (wb K)).toMonoidHom = J₃ K := by
  have ha : (wa K)⁻¹ = wa K := ComponentClassification.UnbalancedCatalog.weylElt_inv g2ir
  have hb : (wb K)⁻¹ = wb K := ComponentClassification.UnbalancedCatalog.weylElt_inv g2ia
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine (map_conj_Ji (i := 0) (m := 3) (n := 1) fun β => ?_).trans (Ji_eq_range 4).symm
    rw [hb]
    exact wb_hCo 0 1 β
  · refine (map_conj_Ji (i := 4) (m := 3) (n := 2) fun β => ?_).trans (Ji_eq_range 3).symm
    rw [ha]
    exact wa_hCo 3 1 β
  · refine (map_conj_Ji (i := 1) (m := 1) (n := 1) fun β => ?_).trans (Ji_eq_range 5).symm
    rw [ha]
    exact wa_hCo 1 0 β
  · refine (map_conj_Ji (i := 5) (m := 2) (n := 1) fun β => ?_).trans (Ji_eq_range 2).symm
    rw [hb]
    exact wb_hCo 1 1 β

theorem weylElt_eq_wRoot (i : Fin Tag.G2.rank) :
    weylElt .G2 K i 1 = wRoot K (Pi.single i 1) := by
  rw [weylElt_eq_xUnit_mul, wRoot, pinnedX_single, pinnedX_neg_single, inv_one, Units.val_one,
    CharTwo.neg_eq]

theorem wRoot_g2r_g2a : wRoot K g2r = wa K ∧ wRoot K g2a = wb K :=
  ⟨by rw [wa, weylElt_eq_wRoot, ← g2r_eq_single], by rw [wb, weylElt_eq_wRoot, ← g2a_eq_single]⟩

theorem wRoot_mul_self (s : Fin Tag.G2.rank → ℤ) : wRoot K s * wRoot K s = 1 := by
  rw [wRoot, show pinnedX .G2 K s 1 * pinnedX .G2 K (-s) 1 * pinnedX .G2 K s 1 *
      (pinnedX .G2 K s 1 * pinnedX .G2 K (-s) 1 * pinnedX .G2 K s 1) =
      pinnedX .G2 K s 1 * pinnedX .G2 K (-s) 1 * (pinnedX .G2 K s 1 * pinnedX .G2 K s 1) *
        pinnedX .G2 K (-s) 1 * pinnedX .G2 K s 1 by group, pinnedX_mul_self, mul_one,
    mul_assoc (pinnedX .G2 K s 1), pinnedX_mul_self, mul_one, pinnedX_mul_self]

theorem yamada_3_9_2 [Finite K] {i k : Fin 6} (hik : i ≠ k) :
    (∀ x ∈ rootSubgroup .G2 K (yamadaRoot k), x ≠ 1 →
      Ji K i ⊓ centralizer {x} = Ji K i ⊓ Ji K k) ∧
    ((¬ 3 ∣ Nat.card K - 1 ∨
        ¬ (i ∈ ({0, 3, 4} : Finset (Fin 6)) ∧ k ∈ ({0, 3, 4} : Finset (Fin 6)))) →
      Ji K i ⊓ Ji K k = ⊥ ∧ ∀ x ∈ rootSubgroup .G2 K (yamadaRoot k), x ≠ 1 →
        ∀ y ∈ rootSubgroup .G2 K (yamadaRoot k), y ≠ 1 → ∃ h ∈ Ji K i, h * x * h⁻¹ = y) :=
  ⟨fun _ hx hx1 => Ji_inf_centralizer_eq i k hx hx1, fun h =>
    ⟨Ji_inf_Ji_eq_bot hik h, fun _ hx hx1 _ hy hy1 =>
      exists_Ji_conj_eq (Ji_inf_Ji_eq_bot hik h) hx hx1 hy hy1⟩⟩

end CharTwo

end TorusAlgebra

section WeylConj

variable {K : Type} [Field K] [CharP K 2]

theorem wa_conj {s : Fin Tag.G2.rank → ℤ} (hs : IsRoot .G2 s) (x : K) :
    wa K * pinnedX .G2 K s x * wa K = pinnedX .G2 K (reflect .G2 g2ir s) x := by
  rw [← weylElt_conj g2ir hs x, wa, ComponentClassification.UnbalancedCatalog.weylElt_inv]

theorem wb_conj {s : Fin Tag.G2.rank → ℤ} (hs : IsRoot .G2 s) (x : K) :
    wb K * pinnedX .G2 K s x * wb K = pinnedX .G2 K (reflect .G2 g2ia s) x := by
  rw [← weylElt_conj g2ia hs x, wb, ComponentClassification.UnbalancedCatalog.weylElt_inv]

theorem canonicalRep_conj_wRoot (w : WeylGroup .G2) {s : Fin Tag.G2.rank → ℤ}
    (hs : IsRoot .G2 s) :
    canonicalRep (coxeterSystem .G2) K w * wRoot K s * (canonicalRep (coxeterSystem .G2) K w)⁻¹ =
      wRoot K (w • s) := by
  set n := canonicalRep (coxeterSystem .G2) K w
  rw [wRoot, wRoot, show n * (pinnedX .G2 K s 1 * pinnedX .G2 K (-s) 1 * pinnedX .G2 K s 1) * n⁻¹ =
      (n * pinnedX .G2 K s 1 * n⁻¹) * (n * pinnedX .G2 K (-s) 1 * n⁻¹) *
        (n * pinnedX .G2 K s 1 * n⁻¹) by group, canonicalRep_conj w hs,
    canonicalRep_conj w (IsRoot.neg hs), smul_neg]

theorem canonicalRep_rootReflection {s : Fin Tag.G2.rank → ℤ} (hs : IsRoot .G2 s) :
    canonicalRep (coxeterSystem .G2) K (rootReflection s) = wRoot K s := by
  obtain ⟨w, j, hwj⟩ := isRoot_iff_exists_smul_single.1 hs
  have hinv : canonicalRep (coxeterSystem .G2) K w⁻¹ =
      (canonicalRep (coxeterSystem .G2) K w)⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← canonicalRep_mul_two, mul_inv_cancel, canonicalRep_one]
  rw [rootReflection_eq_conj hwj, canonicalRep_mul_two, canonicalRep_mul_two, hinv,
    canonicalRep_simple, weylElt_eq_wRoot, canonicalRep_conj_wRoot w (isRoot_single .G2 j), hwj]

theorem yamada_3_8_conj {r s : Fin Tag.G2.rank → ℤ} (hr : IsRoot .G2 r) (hs : IsRoot .G2 s) :
    wRoot K r * wRoot K s * wRoot K r = wRoot K (rootReflection r • s) := by
  have hinv : (wRoot K r)⁻¹ = wRoot K r := inv_eq_of_mul_eq_one_right (wRoot_mul_self r)
  rw [← canonicalRep_conj_wRoot (K := K) (rootReflection r) hs, canonicalRep_rootReflection hr,
    hinv]

theorem orderOf_wa_mul_wb : orderOf (wa K * wb K) = 6 := by
  obtain ⟨h6, h2, h3⟩ := weyl_ab_pow
  have hpow : ∀ k : ℕ, (wa K * wb K) ^ k =
      canonicalRepHom K ((simple .G2 g2ir * simple .G2 g2ia) ^ k) := fun k => by
    rw [map_pow, map_mul]
    change _ = (canonicalRep _ K (simple .G2 g2ir) * canonicalRep _ K (simple .G2 g2ia)) ^ k
    rw [canonicalRep_simple, canonicalRep_simple]
    rfl
  have hne : ∀ (k : ℕ) {γ : Fin Tag.G2.rank → ℤ},
      (γ = g2r ∨ γ = g2a ∨ γ = g2u ∨ γ = g2v ∨ γ = g2b ∨ γ = g2c) →
        (simple .G2 g2ir * simple .G2 g2ia) ^ k • g2a = -γ → (wa K * wb K) ^ k ≠ 1 :=
    fun k γ hγ hk h1 => by
      have hc := canonicalRep_conj (K := K) ((simple .G2 g2ir * simple .G2 g2ia) ^ k)
        isRoot_g2a 1
      change canonicalRepHom K _ * _ * (canonicalRepHom K _)⁻¹ = _ at hc
      rw [← hpow, h1, one_mul, inv_one, mul_one, hk] at hc
      exact pinnedX_a_ne_neg hγ hc
  have hd : orderOf (wa K * wb K) ∣ 6 :=
    orderOf_dvd_of_pow_eq_one (by rw [hpow, h6, map_one])
  have hn2 : (wa K * wb K) ^ 2 ≠ 1 := hne 2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) h2
  have hn3 : (wa K * wb K) ^ 3 ≠ 1 := hne 3 (Or.inr (Or.inl rfl)) h3
  have hmem : orderOf (wa K * wb K) ∈ Nat.divisors 6 := Nat.mem_divisors.2 ⟨hd, by norm_num⟩
  have hdiv : Nat.divisors 6 = {1, 2, 3, 6} := by decide
  rw [hdiv] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h
  · exact absurd (by rw [orderOf_eq_one_iff.1 h, one_pow]) hn2
  · exact absurd (h ▸ pow_orderOf_eq_one _) hn2
  · exact absurd (h ▸ pow_orderOf_eq_one _) hn3
  · exact h

theorem yamada_3_8 :
    Nonempty (closure ({wa K, wb K} : Set (ModGL .G2 K)) ≃* DihedralGroup 6) ∧
      Nat.card (closure ({wa K, wb K} : Set (ModGL .G2 K))) = 12 := by
  obtain ⟨e⟩ := nonempty_closure_pair_mulEquiv_dihedral (wa_mul_self (K := K)) wb_mul_self
    (by rw [orderOf_wa_mul_wb]; decide)
  rw [orderOf_wa_mul_wb] at e
  exact ⟨⟨e⟩, (Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card⟩

end WeylConj

section Coordinates

variable {K : Type} [Field K]

theorem rootSubgroup_yamadaRoot_le_S (i : Fin 6) : rootSubgroup .G2 K (yamadaRoot i) ≤ S K := by
  intro x hx
  obtain ⟨y, rfl⟩ := mem_rootSubgroup.1 hx
  fin_cases i
  · exact (pinnedX_c_eq_g2N (K := K) y).symm ▸ g2N_mem_posUnipotent _ _ _ _ _ _
  · exact (pinnedX_v_eq_g2N (K := K) y).symm ▸ g2N_mem_posUnipotent _ _ _ _ _ _
  · exact (pinnedX_r_eq_g2N (K := K) y).symm ▸ g2N_mem_posUnipotent _ _ _ _ _ _
  · exact (pinnedX_a_eq_g2N (K := K) y).symm ▸ g2N_mem_posUnipotent _ _ _ _ _ _
  · exact (pinnedX_b_eq_g2N (K := K) y).symm ▸ g2N_mem_posUnipotent _ _ _ _ _ _
  · exact (pinnedX_u_eq_g2N (K := K) y).symm ▸ g2N_mem_posUnipotent _ _ _ _ _ _

theorem coords_of_mem_centralizer_Ji [Finite K] (i : Fin 6) {A B C D E F : K}
    (h : g2N A B C D E F ∈ centralizer (Ji K i : Set (ModGL .G2 K))) {k : Fin 6}
    (hk : ¬ ((Nat.card K - 1 : ℕ) : ℤ) ∣ yamadaExp i k) :
    (k = 2 → A = 0) ∧ (k = 3 → B = 0) ∧ (k = 5 → C = 0) ∧ (k = 1 → D = 0) ∧ (k = 4 → E = 0) ∧
      (k = 0 → F = 0) := by
  obtain ⟨β₀, hβ₀⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf β₀ = Nat.card K - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hβ₀, Nat.card_units]
  have hne : β₀ ^ yamadaExp i k ≠ 1 := fun h1 =>
    hk (hord ▸ orderOf_dvd_iff_zpow_eq_one.2 h1)
  have hc := mem_centralizer_iff.1 h _ (hCo_mem_Ji i β₀)
  have hconj : hCo K (yamadaCoroot i).1 (yamadaCoroot i).2 β₀ * g2N A B C D E F *
      (hCo K (yamadaCoroot i).1 (yamadaCoroot i).2 β₀)⁻¹ = g2N A B C D E F := by
    rw [hc, mul_inv_cancel_right]
  rw [hCo_g2N] at hconj
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := g2N_injective hconj
  refine ⟨fun hk' => ?_, fun hk' => ?_, fun hk' => ?_, fun hk' => ?_, fun hk' => ?_,
    fun hk' => ?_⟩ <;> subst hk'
  exacts [eq_zero_of_units_mul_eq' hne h1, eq_zero_of_units_mul_eq' hne h2,
    eq_zero_of_units_mul_eq' hne h3, eq_zero_of_units_mul_eq' hne h4,
    eq_zero_of_units_mul_eq' hne h5, eq_zero_of_units_mul_eq' hne h6]

end Coordinates

section Bruhat

variable {K : Type} [Field K]

theorem S_inf_centralizer_Ji [Finite K] (hK : 4 ≤ Nat.card K) (i : Fin 6)
    (hi : 8 ≤ Nat.card K ∨ i ∉ ({0, 3, 4} : Finset (Fin 6))) :
    S K ⊓ centralizer (Ji K i : Set (ModGL .G2 K)) = rootSubgroup .G2 K (yamadaRoot i) := by
  refine le_antisymm (fun x hx => ?_)
    (le_inf (rootSubgroup_yamadaRoot_le_S i) (rootSubgroup_yamadaRoot_le_centralizer i))
  obtain ⟨hxS, hxC⟩ := hx
  obtain ⟨A, B, C, D, E, F, rfl⟩ := mem_S.1 hxS
  have hz := fun k (hk : k ≠ i) =>
    coords_of_mem_centralizer_Ji i hxC (not_dvd_yamadaExp hK hi hk)
  fin_cases i
  · obtain rfl := (hz 2 (by decide)).1 rfl
    obtain rfl := (hz 3 (by decide)).2.1 rfl
    obtain rfl := (hz 5 (by decide)).2.2.1 rfl
    obtain rfl := (hz 1 (by decide)).2.2.2.1 rfl
    obtain rfl := (hz 4 (by decide)).2.2.2.2.1 rfl
    exact mem_rootSubgroup.2 ⟨F, pinnedX_c_eq_g2N F⟩
  · obtain rfl := (hz 2 (by decide)).1 rfl
    obtain rfl := (hz 3 (by decide)).2.1 rfl
    obtain rfl := (hz 5 (by decide)).2.2.1 rfl
    obtain rfl := (hz 4 (by decide)).2.2.2.2.1 rfl
    obtain rfl := (hz 0 (by decide)).2.2.2.2.2 rfl
    exact mem_rootSubgroup.2 ⟨D, pinnedX_v_eq_g2N D⟩
  · obtain rfl := (hz 3 (by decide)).2.1 rfl
    obtain rfl := (hz 5 (by decide)).2.2.1 rfl
    obtain rfl := (hz 1 (by decide)).2.2.2.1 rfl
    obtain rfl := (hz 4 (by decide)).2.2.2.2.1 rfl
    obtain rfl := (hz 0 (by decide)).2.2.2.2.2 rfl
    exact mem_rootSubgroup.2 ⟨A, pinnedX_r_eq_g2N A⟩
  · obtain rfl := (hz 2 (by decide)).1 rfl
    obtain rfl := (hz 5 (by decide)).2.2.1 rfl
    obtain rfl := (hz 1 (by decide)).2.2.2.1 rfl
    obtain rfl := (hz 4 (by decide)).2.2.2.2.1 rfl
    obtain rfl := (hz 0 (by decide)).2.2.2.2.2 rfl
    exact mem_rootSubgroup.2 ⟨B, pinnedX_a_eq_g2N B⟩
  · obtain rfl := (hz 2 (by decide)).1 rfl
    obtain rfl := (hz 3 (by decide)).2.1 rfl
    obtain rfl := (hz 5 (by decide)).2.2.1 rfl
    obtain rfl := (hz 1 (by decide)).2.2.2.1 rfl
    obtain rfl := (hz 0 (by decide)).2.2.2.2.2 rfl
    exact mem_rootSubgroup.2 ⟨E, pinnedX_b_eq_g2N E⟩
  · obtain rfl := (hz 2 (by decide)).1 rfl
    obtain rfl := (hz 3 (by decide)).2.1 rfl
    obtain rfl := (hz 1 (by decide)).2.2.2.1 rfl
    obtain rfl := (hz 4 (by decide)).2.2.2.2.1 rfl
    obtain rfl := (hz 0 (by decide)).2.2.2.2.2 rfl
    exact mem_rootSubgroup.2 ⟨C, pinnedX_u_eq_g2N C⟩

theorem S_inf_centralizer_J [Finite K] (hK : 4 ≤ Nat.card K) :
    S K ⊓ centralizer (J K : Set (ModGL .G2 K)) = ⊥ := by
  refine eq_bot_iff.2 fun x hx => ?_
  have hx2 : x ∈ S K ⊓ centralizer (Ji K 1 : Set (ModGL .G2 K)) :=
    ⟨hx.1, centralizer_le (fun _ hz => hz.1) hx.2⟩
  rw [S_inf_centralizer_Ji hK 1 (Or.inr (by decide))] at hx2
  obtain ⟨D, rfl⟩ := mem_rootSubgroup.1 hx2
  obtain ⟨β₀, hβ₀⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf β₀ = Nat.card K - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hβ₀, Nat.card_units]
  have hne : β₀ ^ yamadaExp 0 1 ≠ 1 := by
    have e : yamadaExp 0 1 = 1 := by decide
    rw [e, zpow_one]
    rintro rfl
    rw [orderOf_one] at hord
    omega
  have hc := mem_centralizer_iff.1 hx.2 _ (hCo_mem_J 0 1 β₀)
  have h1 := hCo_conj_yamadaRoot (K := K) 0 1 β₀ D
  change hCo K 0 1 β₀ * pinnedX .G2 K (yamadaRoot 1) D * (hCo K 0 1 β₀)⁻¹ = _ at h1
  rw [hc, mul_inv_cancel_right] at h1
  have h2 := pinnedX_injective .G2 K _ h1
  rw [eq_zero_of_units_mul_eq' hne h2.symm, pinnedX_zero]
  exact one_mem _

theorem adjointGroup_inf_normalizer_J [Finite K] (hK : 4 ≤ Nat.card K) :
    adjointGroup .G2 K ⊓ normalizer (J K : Set (ModGL .G2 K)) = monomialSubgroup .G2 K := by
  apply le_antisymm
  · rintro g ⟨hgC, hgN⟩
    have hg' : g ∈ (adjointGroup .G2 K : Set (ModGL .G2 K)) := hgC
    rw [adjointGroup_eq_iUnion_bruhatCell] at hg'
    obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hg'
    set n := canonicalRep (coxeterSystem .G2) K w with hn
    have hbij := bijOn_bruhatCell (τ := .G2) (K := K) w
    obtain ⟨⟨b, u⟩, ⟨hb, hu⟩, hbu⟩ := hbij.surjOn hw
    simp only at hbu hb hu
    have hnN : n ∈ normalizer (J K : Set (ModGL .G2 K)) :=
      (canonical_weyl_root_transport .G2 K).2.2 w
    have key : ∀ s' ∈ J K, b⁻¹ * (g * s' * g⁻¹) * b = n * s' * n⁻¹ ∧ s'⁻¹ * u * s' = u := by
      intro s' hs'
      have hs : g * s' * g⁻¹ ∈ J K := (mem_normalizer_iff.1 hgN s').1 hs'
      have hns : n * s' * n⁻¹ ∈ J K := (mem_normalizer_iff.1 hnN s').1 hs'
      have h1 : g * s' * g⁻¹ * b ∈ borelGroup .G2 K :=
        mul_mem (torusGroup_le_borelGroup hs) hb
      have h2 : b * (n * s' * n⁻¹) ∈ borelGroup .G2 K :=
        mul_mem hb (torusGroup_le_borelGroup hns)
      have h3 : s'⁻¹ * u * s' ∈ rootSpan .G2 K (inversionSet w) := by
        have := (mem_normalizer_iff.1 (torusGroup_le_normalizer_rootSpan
          (S := inversionSet w) (fun α h => h.1) (inv_mem hs')) u).1 hu
        rwa [inv_inv] at this
      have heq : (g * s' * g⁻¹ * b) * n * u = (b * (n * s' * n⁻¹)) * n * (s'⁻¹ * u * s') := by
        calc (g * s' * g⁻¹ * b) * n * u = g * s' * g⁻¹ * (b * n * u) := by group
          _ = (b * n * u) * s' := by rw [hbu]; group
          _ = (b * (n * s' * n⁻¹)) * n * (s'⁻¹ * u * s') := by group
      have hinj := hbij.injOn (x₁ := (g * s' * g⁻¹ * b, u)) (x₂ := (b * (n * s' * n⁻¹),
        s'⁻¹ * u * s')) ⟨h1, hu⟩ ⟨h2, h3⟩ heq
      simp only [Prod.mk.injEq] at hinj
      refine ⟨?_, hinj.2.symm⟩
      calc b⁻¹ * (g * s' * g⁻¹) * b = b⁻¹ * (g * s' * g⁻¹ * b) := by group
        _ = n * s' * n⁻¹ := by rw [hinj.1]; group
    have huS : u ∈ S K := rootSpan_le_posUnipotent (fun α h => inversionSet_pos (w := w) h) hu
    have hu1 : u = 1 := by
      have : u ∈ S K ⊓ centralizer (J K : Set (ModGL .G2 K)) := by
        refine ⟨huS, mem_centralizer_iff.2 fun s' hs' => ?_⟩
        have h := (key s' hs').2
        calc s' * u = s' * (s'⁻¹ * u * s') := by rw [h]
          _ = u * s' := by group
      rw [S_inf_centralizer_J hK] at this
      exact this
    obtain ⟨h₀, hh₀, u₀, hu₀, rfl⟩ := exists_torus_mul_of_mem_borel hb
    have hu₀1 : u₀ = 1 := by
      have : u₀ ∈ S K ⊓ centralizer (J K : Set (ModGL .G2 K)) := by
        refine ⟨hu₀, mem_centralizer_iff.2 fun s hs => ?_⟩
        have hs'' : g⁻¹ * s * g ∈ J K := by
          have := (mem_normalizer_iff.1 (inv_mem hgN) s).1 hs
          rwa [inv_inv] at this
        have hk := (key _ hs'').1
        rw [show g * (g⁻¹ * s * g) * g⁻¹ = s by group] at hk
        have hcomm : h₀⁻¹ * s * h₀ = s := by
          rw [show h₀⁻¹ * s * h₀ = h₀⁻¹ * (s * h₀) by group, ← J_comm hh₀ hs, inv_mul_cancel_left]
        have hJ : u₀⁻¹ * s * u₀ ∈ J K := by
          rw [show u₀⁻¹ * s * u₀ = (h₀ * u₀)⁻¹ * s * (h₀ * u₀) by
            rw [mul_inv_rev]
            calc u₀⁻¹ * s * u₀ = u₀⁻¹ * (h₀⁻¹ * s * h₀) * u₀ := by rw [hcomm]
              _ = _ := by group, hk]
          exact (mem_normalizer_iff.1 hnN _).1 hs''
        have hU : u₀⁻¹ * s * u₀ * s⁻¹ ∈ S K := by
          rw [show u₀⁻¹ * s * u₀ * s⁻¹ = u₀⁻¹ * (s * u₀ * s⁻¹) by group]
          exact mul_mem (inv_mem hu₀) (torus_conj_mem_posUnipotent hs hu₀)
        have h1 : u₀⁻¹ * s * u₀ * s⁻¹ = 1 := by
          have h := torusGroup_inf_posUnipotent (τ := .G2) (R := K)
          rw [eq_bot_iff] at h
          exact mem_bot.1 (h (mem_inf.2 ⟨mul_mem hJ (inv_mem hs), hU⟩))
        calc s * u₀ = u₀ * (u₀⁻¹ * s * u₀ * s⁻¹) * s := by group
          _ = u₀ * s := by rw [h1, mul_one]
      rw [S_inf_centralizer_J hK] at this
      exact this
    rw [← hbu, hu1, hu₀1, mul_one, mul_one]
    exact mul_mem (mem_sup_left hh₀) (mem_sup_right (canonicalRep_mem_closure _ K w))
  · refine le_inf (sup_le (J_le_adjointGroup K) ((closure_le _).2 ?_)) ?_
    · rintro _ ⟨i, rfl⟩
      exact weylElt_mem_adjointGroup i 1
    · exact (normal_subgroupOf_iff_le_normalizer le_sup_left).1
        (torusGroup_subgroupOf_monomialSubgroup_normal .G2 K)

theorem yamada_3_7 [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K) :
    adjointGroup .G2 K ⊓ normalizer (J K : Set (ModGL .G2 K)) = J K ⊔ closure {wa K, wb K} ∧
      (∀ r : Fin Tag.G2.rank → ℤ, IsRoot .G2 r →
        wRoot K r ∈ closure ({wa K, wb K} : Set (ModGL .G2 K))) ∧
      ∃ ψ : WeylGroup .G2 ≃*
          monomialSubgroup .G2 K ⧸ (J K).subgroupOf (monomialSubgroup .G2 K),
        ψ (simple .G2 g2ir) = QuotientGroup.mk ⟨wa K, weylElt_mem_monomialSubgroup g2ir⟩ ∧
        ψ (simple .G2 g2ia) = QuotientGroup.mk ⟨wb K, weylElt_mem_monomialSubgroup g2ia⟩ ∧
        ∀ r : Fin Tag.G2.rank → ℤ, IsRoot .G2 r → ∀ hw : wRoot K r ∈ monomialSubgroup .G2 K,
          ψ (rootReflection r) = QuotientGroup.mk ⟨wRoot K r, hw⟩ := by
  have hcl : ∀ w : WeylGroup .G2, canonicalRep (coxeterSystem .G2) K w ∈
      closure ({wa K, wb K} : Set (ModGL .G2 K)) := fun w => by
    have h := canonicalRep_mem_closure (coxeterSystem .G2) K w
    refine (closure_le _).2 ?_ h
    rintro _ ⟨i, rfl⟩
    fin_cases i
    exacts [subset_closure (Or.inr rfl), subset_closure (Or.inl rfl)]
  refine ⟨(adjointGroup_inf_normalizer_J hK).trans monomialSubgroup_eq, fun r hr => ?_, ?_⟩
  · rw [← canonicalRep_rootReflection hr]
    exact hcl _
  obtain ⟨ψ, hψ, -⟩ := (Weyl_normalizer_quotient .G2 K).2.2
  let χ : WeylGroup .G2 →* monomialSubgroup .G2 K ⧸ (J K).subgroupOf (monomialSubgroup .G2 K) :=
    (QuotientGroup.mk' _).comp ((canonicalRepHom K).codRestrict _ fun w =>
      mem_sup_right (canonicalRep_mem_closure (coxeterSystem .G2) K w))
  have hχ : ψ.toMonoidHom = χ := (coxeterSystem .G2).ext_simple fun i => by
    change ψ (simple .G2 i) = QuotientGroup.mk ⟨canonicalRep (coxeterSystem .G2) K
      (simple .G2 i), _⟩
    rw [hψ i]
    congr 1
    exact Subtype.ext (canonicalRep_simple _ _ i).symm
  refine ⟨ψ, hψ g2ir, hψ g2ia, fun r hr hw => ?_⟩
  have h1 := congrArg (fun f => f (rootReflection r)) hχ
  change ψ (rootReflection r) = QuotientGroup.mk ⟨canonicalRep (coxeterSystem .G2) K
    (rootReflection r), _⟩ at h1
  rw [h1]
  congr 1
  exact Subtype.ext (canonicalRep_rootReflection hr)

end Bruhat

end Model

namespace G2Data

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] (d : G2Data L K)

theorem emb_conj_eq_iff {g x y : adjointGroup .G2 K} :
    d.emb g * d.emb x * (d.emb g)⁻¹ = d.emb y ↔
      (g : ModGL .G2 K) * x * (g : ModGL .G2 K)⁻¹ = y := by
  rw [← map_inv, ← map_mul, ← map_mul, d.emb_injective.eq_iff, Subtype.ext_iff]
  rfl

section TorusG

@[expose] def Ji (i : Fin 6) : Subgroup G := d.image (Model.Ji K i)

@[expose] def torusChars : d.J ≃* Kˣ × Kˣ :=
  (d.imageEquiv (Model.J_le_adjointGroup K)).symm.trans (Model.torusChars K)

theorem image_closure_wa_wb :
    d.image (closure ({Model.wa K, Model.wb K} : Set (ModGL .G2 K))) =
      closure ({d.wa, d.wb} : Set G) := by
  have hcl : closure ({Model.wa K, Model.wb K} : Set (ModGL .G2 K)) ≤ adjointGroup .G2 K := by
    rw [closure_le]
    rintro _ (rfl | rfl)
    exacts [Model.wa_mem_adjointGroup K, Model.wb_mem_adjointGroup K]
  have hL : closure ({d.wa, d.wb} : Set G) ≤ L := by
    rw [closure_le]
    rintro _ (rfl | rfl)
    exacts [d.emb_mem _, d.emb_mem _]
  apply le_antisymm
  · rw [← d.image_preimage hL]
    refine d.image_mono ((closure_le _).2 ?_)
    rintro _ (rfl | rfl)
    · exact (d.mem_preimage (g := ⟨Model.wa K, Model.wa_mem_adjointGroup K⟩)).2
        (subset_closure (Or.inl rfl))
    · exact (d.mem_preimage (g := ⟨Model.wb K, Model.wb_mem_adjointGroup K⟩)).2
        (subset_closure (Or.inr rfl))
  · rw [closure_le]
    rintro _ (rfl | rfl)
    · exact d.emb_mem_image (g := ⟨Model.wa K, Model.wa_mem_adjointGroup K⟩)
        (subset_closure (Or.inl rfl))
    · exact d.emb_mem_image (g := ⟨Model.wb K, Model.wb_mem_adjointGroup K⟩)
        (subset_closure (Or.inr rfl))

instance normal_J_subgroupOf :
    (d.J.subgroupOf (L ⊓ normalizer (d.J : Set G))).Normal :=
  (normal_subgroupOf_iff_le_normalizer (le_inf (d.image_le _) le_normalizer)).2 inf_le_right

@[expose] def wRoot (s : Fin Tag.G2.rank → ℤ) : G :=
  d.emb ⟨Model.wRoot K s, mul_mem (mul_mem (pinnedX_mem_adjointGroup _ _)
    (pinnedX_mem_adjointGroup _ _)) (pinnedX_mem_adjointGroup _ _)⟩

section CharTwo

variable [CharP K 2]

theorem Ji_conj_G :
    d.J₁.map (MulAut.conj d.wb).toMonoidHom = d.J₅ ∧
      d.J₅.map (MulAut.conj d.wa).toMonoidHom = d.J₄ ∧
      d.J₂.map (MulAut.conj d.wa).toMonoidHom = d.J₆ ∧
      d.J₆.map (MulAut.conj d.wb).toMonoidHom = d.J₃ := by
  obtain ⟨h1, h2, h3, h4⟩ := Model.Ji_conj (K := K)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [G2Data.J₁, G2Data.J₅, G2Data.wb, ← d.image_map_conj, ← h1]
  · rw [G2Data.J₅, G2Data.J₄, G2Data.wa, ← d.image_map_conj, ← h2]
  · rw [G2Data.J₂, G2Data.J₆, G2Data.wa, ← d.image_map_conj, ← h3]
  · rw [G2Data.J₆, G2Data.J₃, G2Data.wb, ← d.image_map_conj, ← h4]

end CharTwo

end TorusG

section WeylConjG

variable [CharP K 2]

theorem yamada_3_8_G :
    (∀ {r s : Fin Tag.G2.rank → ℤ}, IsRoot .G2 r → IsRoot .G2 s →
      d.wRoot r * d.wRoot s * d.wRoot r = d.wRoot (rootReflection r • s)) ∧
      d.wRoot g2r = d.wa ∧ d.wRoot g2a = d.wb ∧ orderOf (d.wa * d.wb) = 6 ∧
      Nonempty (closure ({d.wa, d.wb} : Set G) ≃* DihedralGroup 6) ∧
      Nat.card (closure ({d.wa, d.wb} : Set G)) = 12 := by
  have hcl : closure ({Model.wa K, Model.wb K} : Set (ModGL .G2 K)) ≤ adjointGroup .G2 K := by
    rw [closure_le]
    rintro _ (rfl | rfl)
    exacts [Model.wa_mem_adjointGroup K, Model.wb_mem_adjointGroup K]
  obtain ⟨⟨e⟩, hc⟩ := Model.yamada_3_8 (K := K)
  have e' : closure ({d.wa, d.wb} : Set G) ≃* closure ({Model.wa K, Model.wb K} :
      Set (ModGL .G2 K)) :=
    (MulEquiv.subgroupCongr d.image_closure_wa_wb.symm).trans (d.imageEquiv hcl).symm
  refine ⟨fun hr hs => ?_, ?_, ?_, ?_, ⟨e'.trans e⟩, (Nat.card_congr e'.toEquiv).trans hc⟩
  · rw [G2Data.wRoot, G2Data.wRoot, ← map_mul, ← map_mul]
    exact congrArg d.emb (Subtype.ext (Model.yamada_3_8_conj hr hs))
  · exact congrArg d.emb (Subtype.ext (Model.wRoot_g2r_g2a (K := K)).1)
  · exact congrArg d.emb (Subtype.ext (Model.wRoot_g2r_g2a (K := K)).2)
  · rw [G2Data.wa, G2Data.wb, ← map_mul, orderOf_injective d.emb d.emb_injective,
      ← Subgroup.orderOf_coe]
    exact Model.orderOf_wa_mul_wb

end WeylConjG

section BruhatG

section CharTwo

variable [CharP K 2]

theorem yamada_3_7_G [Finite K] (hK : 4 ≤ Nat.card K) :
    L ⊓ normalizer (d.J : Set G) = d.J ⊔ closure ({d.wa, d.wb} : Set G) ∧
      (∀ r : Fin Tag.G2.rank → ℤ, IsRoot .G2 r → d.wRoot r ∈ closure ({d.wa, d.wb} : Set G)) ∧
      d.wa * d.wa = 1 ∧ d.wb * d.wb = 1 ∧
      (∀ {s : Fin Tag.G2.rank → ℤ}, IsRoot .G2 s → ∀ x : K,
        d.wa * d.emb ⟨pinnedX .G2 K s x, pinnedX_mem_adjointGroup s x⟩ * d.wa =
          d.emb ⟨pinnedX .G2 K (reflect .G2 g2ir s) x, pinnedX_mem_adjointGroup _ _⟩) ∧
      (∀ {s : Fin Tag.G2.rank → ℤ}, IsRoot .G2 s → ∀ x : K,
        d.wb * d.emb ⟨pinnedX .G2 K s x, pinnedX_mem_adjointGroup s x⟩ * d.wb =
          d.emb ⟨pinnedX .G2 K (reflect .G2 g2ia s) x, pinnedX_mem_adjointGroup _ _⟩) := by
  have hwa : d.wa * d.wa = 1 := by
    rw [G2Data.wa, ← map_mul, ← map_one d.emb]
    exact congrArg d.emb (Subtype.ext Model.wa_mul_self)
  have hwb : d.wb * d.wb = 1 := by
    rw [G2Data.wb, ← map_mul, ← map_one d.emb]
    exact congrArg d.emb (Subtype.ext Model.wb_mul_self)
  refine ⟨?_, fun r hr => ?_, hwa, hwb, fun hs x => ?_, fun hs x => ?_⟩
  · have hcl : closure ({Model.wa K, Model.wb K} : Set (ModGL .G2 K)) ≤ adjointGroup .G2 K := by
      rw [closure_le]
      rintro _ (rfl | rfl)
      exacts [Model.wa_mem_adjointGroup K, Model.wb_mem_adjointGroup K]
    rw [G2Data.J, ← d.image_inf_normalizer (Model.J_le_adjointGroup K),
      Model.adjointGroup_inf_normalizer_J hK, Model.monomialSubgroup_eq,
      d.image_sup (Model.J_le_adjointGroup K) hcl, d.image_closure_wa_wb]
  · rw [← d.image_closure_wa_wb]
    exact d.emb_mem_image ((Model.yamada_3_7 (K := K) hK).2.1 r hr)
  · rw [G2Data.wa, ← map_mul, ← map_mul]
    exact congrArg d.emb (Subtype.ext (Model.wa_conj hs x))
  · rw [G2Data.wb, ← map_mul, ← map_mul]
    exact congrArg d.emb (Subtype.ext (Model.wb_conj hs x))

end CharTwo

end BruhatG

end G2Data

end CFSG.LocalAnalysis.EvenBN.G2
