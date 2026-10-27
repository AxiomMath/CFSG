module

public import CFSG.LargeExtraspecial.S14SMELocal

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Subgroup CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14

variable {G : Type} [Group G] [Finite G]

@[expose] def OE34a (S : Setting G) : Prop :=
  ∀ x : G, IsConj S.z x → x ∈ S.M → x ∉ S.QG → ¬ IsConj S.z (x * S.z)

@[expose] def OE34b (S : Setting G) : Prop :=
  ∀ x x' : G, IsConj S.z x → IsConj S.z x' → x ∈ S.M → x ∉ S.QG → x⁻¹ * x' ∈ S.QG →
    ∃ q ∈ S.QG, x' = q⁻¹ * x * q

@[expose] def OE24 (S : Setting G) : Prop :=
  ∀ x h : G, IsConj S.z x → x ∈ S.M → x ∉ S.QG → h * S.z * h⁻¹ ∈ S.QG →
    x * (h * S.z * h⁻¹) * x⁻¹ ∈ S.Qa h

@[expose] def OE25 (S : Setting G) : Prop :=
  ∀ x y : G, IsConj S.z x → IsConj S.z y → x ∈ S.M → y ∈ S.M → x ∉ S.QG → y ∉ S.QG →
    x * y ∉ S.QG →
      ((x * y) ^ 2 ∈ S.QG → ∀ v ∈ S.commQt x ⊓ S.commQt y,
        ∃ c : G, IsConj S.z c ∧ c ∈ S.QG ∧ S.cl c = v) ∧
      ((x * y) ^ 3 ∈ S.QG → S.commQt x ⊓ S.commQt y = ⊥)

theorem sq_eq_one_of_mem_commutator' (S : Setting G) (h34a : OE34a S) {x : G}
    (hx : IsConj S.z x) (hxM : x ∈ S.M) (hxQ : x ∉ S.QG) {g : G}
    (hg : g ∈ (⁅zpowers x, S.QG⁆ : Subgroup G)) : g ^ 2 = 1 := by
  have hx2 : x ^ 2 = 1 := by
    rw [_root_.sq]
    exact SmithQ.mul_self_eq_one_of_isConj S hx
  have hfix : S.fixQt x = S.clSub (S.QG ⊓ centralizer ({x} : Set G)) := by
    by_contra hne
    obtain ⟨y, -, hy⟩ := S.lemma_3_2_1 hxM hne
    apply h34a x hx hxM hxQ
    rw [← hy]
    exact hx.trans (isConj_iff.mpr ⟨y, rfl⟩)
  obtain ⟨hel, -⟩ := S.aschbacher_3_6 hxM hxQ hx2 hfix (S.index_fixQt x hxM)
  have := hel
  exact CFSG.elemPow_eq_one_of_isElementaryAbelian g hg

theorem exists_commutator_of_coset' (S : Setting G) (h34b : OE34b S) {x x' : G}
    (hx : IsConj S.z x) (hx' : IsConj S.z x') (hxM : x ∈ S.M) (hxQ : x ∉ S.QG)
    (hQ : x⁻¹ * x' ∈ S.QG) : ∃ q ∈ S.QG, x⁻¹ * x' = x * q * x⁻¹ * q⁻¹ := by
  obtain ⟨q, hq, rfl⟩ := h34b x x' hx hx' hxM hxQ hQ
  refine ⟨q⁻¹, S.QG.inv_mem hq, ?_⟩
  rw [inv_inv, SME.inv_eq_of_isConj S hx]
  group

theorem local_of_mem_QG' (S : Setting G) (h34a : OE34a S) (h24 : OE24 S) {x y : G}
    (hx : IsConj S.z x) (hy : IsConj S.z y) (hxM : x ∈ S.M) (hxQ : x ∉ S.QG) (hyQ : y ∈ S.QG) :
    orderOf (x * y) ∈ ({1, 2, 3, 4} : Set ℕ) ∧
      (orderOf (x * y) = 4 → IsConj S.z ((x * y) ^ 2)) := by
  have hxi := SME.inv_eq_of_isConj S hx
  have hyi := SME.inv_eq_of_isConj S hy
  have he : (x * y) ^ 2 = x * y * x⁻¹ * y⁻¹ := by
    rw [hxi, hyi, sq]
    simp only [mul_assoc]
  have hsq : ((x * y) ^ 2) ^ 2 = 1 := by
    rw [he]
    exact sq_eq_one_of_mem_commutator' S h34a hx hxM hxQ (SME.commutator_mem S x hyQ)
  refine ⟨SME.orderOf_mem_of_sq_sq hsq, fun h4 => ?_⟩
  have hne := SME.sq_ne_one_of_orderOf_eq_four h4
  obtain ⟨h, rfl⟩ := isConj_iff.mp hy
  have hy' := (SME.mem_Qa_iff S h _).mp (h24 x h hx hxM hxQ hyQ)
  obtain ⟨y', hy'd⟩ : ∃ y', y' = x * (h * S.z * h⁻¹) * x⁻¹ := ⟨_, rfl⟩
  rw [← hy'd] at hy'
  have hy'c : IsConj S.z y' := hy.trans (isConj_iff.mpr ⟨x, hy'd.symm⟩)
  have he' : (x * (h * S.z * h⁻¹)) ^ 2 = y' * (h * S.z * h⁻¹) := by
    rw [he, hy'd, hyi]
  have hy'ne : y' ≠ h * S.z * h⁻¹ := by
    intro heq
    apply hne
    rw [he', heq]
    exact SmithQ.mul_self_eq_one_of_isConj S hy
  have hback : y' = h * (h⁻¹ * y' * h) * h⁻¹ := by group
  have hy''1 : h⁻¹ * y' * h ≠ 1 := by
    intro h1
    apply SME.ne_one_of_isConj S hy'c
    rw [hback, h1]
    group
  have hy''z : h⁻¹ * y' * h ≠ S.z := by
    intro h1
    apply hy'ne
    rw [hback, h1]
  obtain ⟨q, -, hq⟩ := SME.exists_conj_eq_mul_z S hy' hy''1 hy''z
  have hconj : (h * q * h⁻¹) * y' * (h * q * h⁻¹)⁻¹ = y' * (h * S.z * h⁻¹) := by
    have h1 : h * (q * (h⁻¹ * y' * h) * q⁻¹) * h⁻¹ = h * ((h⁻¹ * y' * h) * S.z) * h⁻¹ := by
      rw [hq]
    calc (h * q * h⁻¹) * y' * (h * q * h⁻¹)⁻¹ = h * (q * (h⁻¹ * y' * h) * q⁻¹) * h⁻¹ := by
          group
      _ = h * ((h⁻¹ * y' * h) * S.z) * h⁻¹ := h1
      _ = y' * (h * S.z * h⁻¹) := by group
  rw [he', ← hconj]
  exact hy'c.trans (isConj_iff.mpr ⟨_, rfl⟩)

theorem local_of_mul_mem' (S : Setting G) (h34a : OE34a S) (h34b : OE34b S) {x y : G}
    (hx : IsConj S.z x) (hy : IsConj S.z y) (hxM : x ∈ S.M) (hyM : y ∈ S.M) (hxQ : x ∉ S.QG)
    (hyQ : y ∉ S.QG) (hxy : x * y ∈ S.QG) :
    orderOf (x * y) ∈ ({1, 2, 3, 4} : Set ℕ) ∧
      (orderOf (x * y) = 4 → IsConj S.z ((x * y) ^ 2)) := by
  have hxi := SME.inv_eq_of_isConj S hx
  obtain ⟨q, hq, hqe⟩ := exists_commutator_of_coset' S h34b hx hy hxM hxQ
    (by rw [hxi]; exact hxy)
  have h2 : (x * y) ^ 2 = 1 := by
    rw [show x * y = x⁻¹ * y by rw [hxi], hqe]
    exact sq_eq_one_of_mem_commutator' S h34a hx hxM hxQ (SME.commutator_mem S x hq)
  obtain ⟨hmem, h4⟩ := SME.orderOf_mem_of_pow_two h2
  exact ⟨hmem, fun h => absurd h h4⟩

theorem local_of_sq_mem' (S : Setting G) (h34a : OE34a S) (h34b : OE34b S) (h25 : OE25 S)
    {x y : G} (hx : IsConj S.z x) (hy : IsConj S.z y) (hxM : x ∈ S.M) (hyM : y ∈ S.M)
    (hxQ : x ∉ S.QG) (hyQ : y ∉ S.QG) (h1 : x * y ∉ S.QG) (h2 : (x * y) ^ 2 ∈ S.QG) :
    orderOf (x * y) ∈ ({1, 2, 3, 4} : Set ℕ) ∧
      (orderOf (x * y) = 4 → IsConj S.z ((x * y) ^ 2)) := by
  have hxi := SME.inv_eq_of_isConj S hx
  have hyi := SME.inv_eq_of_isConj S hy
  have hx'c : IsConj S.z (y⁻¹ * x * y) := hx.trans (isConj_iff.mpr ⟨y⁻¹, by group⟩)
  have hx'e : x⁻¹ * (y⁻¹ * x * y) = (x * y) ^ 2 := by
    rw [hxi, hyi, sq]
    simp only [mul_assoc]
  obtain ⟨q, hq, hqe⟩ := exists_commutator_of_coset' S h34b hx hx'c hxM hxQ
    (by rw [hx'e]; exact h2)
  rw [hx'e] at hqe
  have hy'c : IsConj S.z (x⁻¹ * y * x) := hy.trans (isConj_iff.mpr ⟨x⁻¹, by group⟩)
  have hy'e : y⁻¹ * (x⁻¹ * y * x) = ((x * y) ^ 2)⁻¹ := by
    rw [sq, mul_inv_rev, mul_inv_rev, hxi, hyi]
    simp only [mul_assoc]
  obtain ⟨q', hq', hqe'⟩ := exists_commutator_of_coset' S h34b hy hy'c hyM hyQ
    (by rw [hy'e]; exact S.QG.inv_mem h2)
  rw [hy'e] at hqe'
  have hcl : S.cl ((x * y) ^ 2) ∈ S.commQt x ⊓ S.commQt y := by
    refine Submodule.mem_inf.mpr ⟨(S.mem_commQt_iff hxM).mpr ⟨q, hq, by rw [hqe]⟩, ?_⟩
    rw [← S.cl_inv h2, hqe']
    exact (S.mem_commQt_iff hyM).mpr ⟨q', hq', rfl⟩
  have hsq : ((x * y) ^ 2) ^ 2 = 1 := by
    rw [hqe]
    exact sq_eq_one_of_mem_commutator' S h34a hx hxM hxQ (SME.commutator_mem S x hq)
  refine ⟨SME.orderOf_mem_of_sq_sq hsq, fun h4 => ?_⟩
  obtain ⟨c, hc, hcQ, hcl'⟩ := (h25 x y hx hy hxM hyM hxQ hyQ h1).1 h2 _ hcl
  exact SME.isConj_of_cl_eq S hc hcQ h2 (SME.sq_ne_one_of_orderOf_eq_four h4) hcl'

theorem local_of_cube_mem' (S : Setting G) (h34a : OE34a S) (h34b : OE34b S) (h25 : OE25 S)
    {x y : G} (hx : IsConj S.z x) (hy : IsConj S.z y) (hxM : x ∈ S.M) (hyM : y ∈ S.M)
    (hxQ : x ∉ S.QG) (hyQ : y ∉ S.QG) (h1 : x * y ∉ S.QG) (h3 : (x * y) ^ 3 ∈ S.QG) :
    orderOf (x * y) ∈ ({1, 2, 3, 4} : Set ℕ) ∧
      (orderOf (x * y) = 4 → IsConj S.z ((x * y) ^ 2)) := by
  have hxi := SME.inv_eq_of_isConj S hx
  have hyi := SME.inv_eq_of_isConj S hy
  have hxx := SmithQ.mul_self_eq_one_of_isConj S hx
  have hc1 : IsConj S.z (x * (x * y) ^ 3) := by
    have h : (y * x) * y * (y * x)⁻¹ = x * (x * y) ^ 3 := by
      rw [mul_inv_rev, hxi, hyi, pow_succ, pow_succ, pow_one]
      simp only [← mul_assoc, hxx, one_mul]
    rw [← h]
    exact hy.trans (isConj_iff.mpr ⟨_, rfl⟩)
  have hc2 : IsConj S.z (y * (x * y) ^ 3) := by
    have h : (y * x * y) * x * (y * x * y)⁻¹ = y * (x * y) ^ 3 := by
      rw [mul_inv_rev, mul_inv_rev, hxi, hyi, pow_succ, pow_succ, pow_one]
      simp only [← mul_assoc]
    rw [← h]
    exact hx.trans (isConj_iff.mpr ⟨_, rfl⟩)
  obtain ⟨q, hq, hqe⟩ := exists_commutator_of_coset' S h34b hx hc1 hxM hxQ
    (by rw [inv_mul_cancel_left]; exact h3)
  obtain ⟨q', hq', hqe'⟩ := exists_commutator_of_coset' S h34b hy hc2 hyM hyQ
    (by rw [inv_mul_cancel_left]; exact h3)
  rw [inv_mul_cancel_left] at hqe hqe'
  have hbot := (h25 x y hx hy hxM hyM hxQ hyQ h1).2 h3
  have hmem : S.cl ((x * y) ^ 3) ∈ S.commQt x ⊓ S.commQt y :=
    Submodule.mem_inf.mpr ⟨(S.mem_commQt_iff hxM).mpr ⟨q, hq, by rw [hqe]⟩,
      (S.mem_commQt_iff hyM).mpr ⟨q', hq', by rw [hqe']⟩⟩
  rw [hbot] at hmem
  rcases (S.cl_eq_zero_iff h3).mp ((Submodule.mem_bot _).mp hmem) with h31 | h3z
  · obtain ⟨hm, h4⟩ := SME.orderOf_mem_of_pow_three h31
    exact ⟨hm, fun h => absurd h h4⟩
  · refine (h34a x hx hxM hxQ ?_).elim
    have h : x * S.z = x * (x * y) ^ 3 := by rw [h3z]
    rw [h]
    exact hc1

theorem oe34b_of (S : Setting G) (h34a : OE34a S) : OE34b S := by
  intro x x' hx hx' hxM hxQ hQ
  have hfix : ∀ {α : G}, IsConj S.z α → α ∈ S.M → α ∉ S.QG →
      S.fixQt α = S.clSub (S.QG ⊓ centralizer ({α} : Set G)) := by
    intro α hα hαM hαQ
    by_contra hne
    obtain ⟨y, -, hy⟩ := S.lemma_3_2_1 hαM hne
    apply h34a α hα hαM hαQ
    rw [← hy]
    exact hα.trans (isConj_iff.mpr ⟨y, rfl⟩)
  have hhQ : x' * x⁻¹ ∈ S.QG := by
    have e : x' * x⁻¹ = x * (x⁻¹ * x') * x⁻¹ := by group
    rw [e]
    exact S.conj_mem_QG hxM hQ
  set h := x' * x⁻¹ with hh
  have hx'eq : x' = h * x := by rw [hh]; group
  have hhM : h ∈ S.M := S.QG_le_M hhQ
  have hx'M : x' ∈ S.M := by
    rw [hx'eq]
    exact S.M.mul_mem hhM hxM
  have hx'Q : x' ∉ S.QG := by
    intro h'
    apply hxQ
    have e : x = h⁻¹ * x' := by rw [hx'eq]; group
    rw [e]
    exact S.QG.mul_mem (S.QG.inv_mem hhQ) h'
  have hfx := hfix hx hxM hxQ
  have hfx' := hfix hx' hx'M hx'Q
  have hρ : S.fixQt x' = S.fixQt x := by
    rw [S.fixQt_of_mem hx'M, S.fixQt_of_mem hxM]
    have e : S.ρ ⟨x', hx'M⟩ = S.ρ ⟨x, hxM⟩ := by
      rw [show (⟨x', hx'M⟩ : S.M) = ⟨h, hhM⟩ * ⟨x, hxM⟩ from Subtype.ext hx'eq, map_mul,
        (S.ρ_eq_one_iff _).mpr hhQ, one_mul]
    rw [e]
  set C := S.QG ⊓ centralizer ({x} : Set G) with hC
  set C' := S.QG ⊓ centralizer ({x'} : Set G) with hC'
  have hzC : S.z ∈ C := ⟨S.z_mem_QG, mem_centralizer_singleton_iff.mpr (S.z_comm hxM).symm⟩
  have hzC' : S.z ∈ C' := ⟨S.z_mem_QG, mem_centralizer_singleton_iff.mpr (S.z_comm hx'M).symm⟩
  have hCC : C' = C := by
    have e1 : S.clPre (S.clSub C') = C' := S.clPre_clSub inf_le_left hzC'
    have e2 : S.clPre (S.clSub C) = C := S.clPre_clSub inf_le_left hzC
    calc C' = S.clPre (S.clSub C') := e1.symm
      _ = S.clPre (S.clSub C) := by rw [← hfx', hρ, hfx]
      _ = C := e2
  have hhC : h ∈ S.QG ⊓ centralizer (C : Set G) := by
    refine ⟨hhQ, mem_centralizer_iff.mpr fun s hs => ?_⟩
    have hs1 : s * x = x * s := mem_centralizer_singleton_iff.mp hs.2
    have hs' : s ∈ C' := by
      rw [hCC]
      exact hs
    have hs2 : s * x' = x' * s := mem_centralizer_singleton_iff.mp hs'.2
    rw [hx'eq] at hs2
    calc s * h = s * (h * x) * x⁻¹ := by group
      _ = h * x * s * x⁻¹ := by rw [hs2]
      _ = h * (x * s) * x⁻¹ := by group
      _ = h * (s * x) * x⁻¹ := by rw [hs1]
      _ = h * s := by group
  have hx2 : x ^ 2 = 1 := by
    rw [sq]
    exact SmithQ.mul_self_eq_one_of_isConj S hx
  rw [S.centralizer_inf_QG_eq_clPre inf_le_left, ← hfx, ← S.commQt_eq_orthogonal hxM hx2] at hhC
  obtain ⟨y, hy, hyh⟩ := (S.mem_commQt_iff' hxM).mp hhC.2
  rcases (S.cl_eq_cl_iff (S.commutator_mem_QG' hxM hy) hhQ).mp hyh with h1 | h1
  · refine ⟨y⁻¹, S.QG.inv_mem hy, ?_⟩
    rw [hx'eq, h1]
    group
  · exfalso
    apply h34a x hx hxM hxQ
    have hzx : S.z * x = x * S.z := (S.z_comm hxM).symm
    have hzy : y⁻¹ * S.z = S.z * y⁻¹ := S.z_comm_QG (S.QG.inv_mem hy)
    have e : x' = y * (x * S.z) * y⁻¹ := by
      calc x' = h * x := hx'eq
        _ = y * x * y⁻¹ * x⁻¹ * S.z * x := by rw [h1]
        _ = y * x * y⁻¹ * x⁻¹ * (S.z * x) := by group
        _ = y * x * y⁻¹ * x⁻¹ * (x * S.z) := by rw [hzx]
        _ = y * x * (y⁻¹ * S.z) := by group
        _ = y * x * (S.z * y⁻¹) := by rw [hzy]
        _ = y * (x * S.z) * y⁻¹ := by group
    exact hx'.trans (isConj_iff.mpr ⟨y⁻¹, by rw [e]; group⟩)

end CFSG.GF2Type.Smith1980Orth
