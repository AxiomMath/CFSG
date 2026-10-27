module

import all CFSG.CGT.Stroth77.Extension22FourBasis
public import CFSG.CGT.Stroth77.Extension22FourBasis
public import CFSG.CGT.Stroth77.Extension22FourComm

public section

namespace CFSG.CGT.Stroth77

open scoped IsMulCommutative

variable {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S} {m : ℕ}

theorem t100_sqSubgroup_fixed_rho
    (D : StrothTypeData B (StrothTypeIndex.t100 m)) (y : B)
    (hy : conjBy D.ρ_mem y * y⁻¹ ∈ sqSubgroup D) :
    ∃ i : ℤ, y * D.c ^ (-i) ∈ sqSubgroup D := by
  classical
  obtain ⟨z, hz⟩ := (mem_sqSubgroup_iff D).mp hy
  obtain ⟨i, j, l, hy_eq⟩ := torus_eq_zsmul_gens (StrothTypeIndex.t100 m).k (D.ec y)
  have hmap : D.ec (conjBy D.ρ_mem y * y⁻¹) = Φρ D (D.ec y) - D.ec y := by
    rw [D.ec_mul, D.ec_inv, ec_conj_ρ]
    abel
  have hz' : Φρ D (D.ec y) - D.ec y = 2 • z := hmap.symm.trans hz
  have hρy : Φρ D (D.ec y) =
      (i - 2 * l) • gen (StrothTypeIndex.t100 m).k 0 +
        (-l) • gen (StrothTypeIndex.t100 m).k 1 +
        (j - l) • gen (StrothTypeIndex.t100 m).k 2 := by
    rw [hy_eq]
    exact type100_rho_apply_gens m i j l
  have hY1 : D.ec y 1 = (j : ZMod (2 ^ (StrothTypeIndex.t100 m).k 1)) := by
    rw [hy_eq]
    simp [gen, Pi.single_apply]
  have hY2 : D.ec y 2 = (l : ZMod (2 ^ (StrothTypeIndex.t100 m).k 2)) := by
    rw [hy_eq]
    simp [gen, Pi.single_apply]
  have hΦ1 : (Φρ D (D.ec y)) 1 = (-l : ZMod (2 ^ (StrothTypeIndex.t100 m).k 1)) := by
    rw [hρy]
    simp [gen, Pi.single_apply, zsmul_eq_mul]
  have hΦ2 : (Φρ D (D.ec y)) 2 =
      (j : ZMod (2 ^ (StrothTypeIndex.t100 m).k 2)) -
        (l : ZMod (2 ^ (StrothTypeIndex.t100 m).k 2)) := by
    rw [hρy]
    simp [gen, Pi.single_apply, zsmul_eq_mul]
  have hc1 : ((-l - j : ℤ) : ZMod (2 ^ (StrothTypeIndex.t100 m).k 1)) = 2 * z 1 := by
    have h := congrFun hz' 1
    simp only [Pi.sub_apply, hY1, hΦ1, Pi.smul_apply, zsmul_eq_mul] at h
    push_cast
    ring_nf at h ⊢
    exact h
  have hc2 : ((j - 2 * l : ℤ) : ZMod (2 ^ (StrothTypeIndex.t100 m).k 2)) = 2 * z 2 := by
    have h := congrFun hz' 2
    simp only [Pi.sub_apply, hY2, hΦ2, Pi.smul_apply, zsmul_eq_mul] at h
    push_cast
    ring_nf at h ⊢
    exact h
  have hc1' : Even (-l - j) :=
    even_of_intCast_eq_two_mul
      (N := (StrothTypeIndex.t100 m).k 1) (by simp [StrothTypeIndex.k, Type100.k]) hc1
  have hc2' : Even (j - 2 * l) :=
    even_of_intCast_eq_two_mul
      (N := (StrothTypeIndex.t100 m).k 2) (by simp [StrothTypeIndex.k, Type100.k]) hc2
  have h2l : Even (2 * l) := ⟨l, by ring⟩
  have hj : Even j := (Int.even_sub.mp hc2').mpr h2l
  have hsum : Even (l + j) := by
    have hneg : Even (-(l + j)) := by
      have h := hc1'
      convert h using 1
      ring
    rcases hneg with ⟨t, ht⟩
    refine ⟨-t, ?_⟩
    have hneg' := congrArg Neg.neg ht
    simp only [neg_neg, neg_mul] at hneg'
    rw [hneg']
    ring
  have hl : Even l := (Int.even_add.mp hsum).mpr hj
  obtain ⟨j', hj'⟩ := hj
  obtain ⟨l', hl'⟩ := hl
  have hj2 : j = 2 * j' := by rw [hj']; ring
  have hl2 : l = 2 * l' := by rw [hl']; ring
  refine ⟨i, (mem_sqSubgroup_iff D).mpr ⟨j' • gen (StrothTypeIndex.t100 m).k 1 +
    l' • gen (StrothTypeIndex.t100 m).k 2, ?_⟩⟩
  have hEc : D.ec (y * D.c ^ (-i)) = D.ec y - i • gen (StrothTypeIndex.t100 m).k 0 := by
    rw [D.ec_mul, D.ec_zpow, D.ec_c]
    rw [neg_zsmul, sub_eq_add_neg]
  rw [hEc, hy_eq, hj2, hl2, mul_zsmul, mul_zsmul, smul_add]
  abel


theorem sqQuotientHom_range_le_cParity_ker
    [hN : (B.subgroupOf C).Normal]
    (hcommC : IsMulCommutative C)
    (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hncyc : ¬ IsCyclic (C ⧸ B.subgroupOf C))
    (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S')
    (hm : 1 ≤ m) :
    (sqQuotientHom hcommC D hBC hC hrel hncyc).range ≤ (cParityQuotient D hm).ker := by
  classical
  let sq := sqQuotientHom hcommC D hBC hC hrel hncyc
  let cp := cParityQuotient D hm
  let φ : C →* Multiplicative (ZMod 2) := cp.comp sq
  have hkerSq : sq.ker = B.subgroupOf C :=
    sqQuotientHom_ker hcommC D hBC hC hrel hncyc hH hcS
  have hρC : D.ρ ∈ Subgroup.normalizer C := hL D.ρ_mem_L
  have hφ_apply : ∀ x : C, φ x = cParityHom D hm
      ⟨(x : S) * (x : S),
        sq_mem_of_not_cyclic_quotient_four hBC hC hrel hncyc x⟩ := by
    intro x
    show cp (sq x) = _
    rw [show sq x = QuotientGroup.mk' (sqSubgroup D)
        ⟨(x : S) * (x : S),
          sq_mem_of_not_cyclic_quotient_four hBC hC hrel hncyc x⟩ from rfl]
    rw [cParityQuotient_mk]
  have hφρ : ∀ x : C, φ (conjBy hρC x) = φ x := by
    intro x
    have hsc : (⟨((conjBy hρC x : C) : S) * ((conjBy hρC x : C) : S),
        sq_mem_of_not_cyclic_quotient_four hBC hC hrel hncyc (conjBy hρC x)⟩ : B) =
        conjBy D.ρ_mem ⟨(x : S) * (x : S),
          sq_mem_of_not_cyclic_quotient_four hBC hC hrel hncyc x⟩ := by
      apply Subtype.ext
      simp only [conjBy_val, Subgroup.coe_mk, Subgroup.coe_mul]
      group
    calc φ (conjBy hρC x)
        = cParityHom D hm ⟨_, _⟩ := hφ_apply _
      _ = cParityHom D hm (conjBy D.ρ_mem ⟨(x : S) * (x : S), _⟩) := by rw [hsc]
      _ = cParityHom D hm ⟨(x : S) * (x : S), _⟩ := cParityHom_conj_ρ D hm _
      _ = φ x := (hφ_apply x).symm
  by_contra hle
  have hφ_ne : ∃ x : C, φ x ≠ 1 := by
    by_contra h
    apply hle
    intro q hq
    obtain ⟨x, rfl⟩ := hq
    exact MonoidHom.mem_ker.mpr (by
      simpa [φ] using not_not.mp (not_exists.mp h x))
  obtain ⟨x0, hx0⟩ := hφ_ne
  have hsurj : Function.Surjective φ := by
    intro y
    by_cases hy : y = 1
    · exact ⟨1, by rw [hy, map_one]⟩
    · have huniq := (Nat.card_eq_two_iff' (1 : Multiplicative (ZMod 2))).mp (by
        simp [Nat.card_eq_fintype_card])
      exact ⟨x0, huniq.unique hx0 hy⟩
  have hKindex : φ.ker.index = 2 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj]
    simp [Nat.card_eq_fintype_card]
  have hBK : B.subgroupOf C ≤ φ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have hxsq : sq x = 1 := by
      rw [← MonoidHom.mem_ker, hkerSq]
      exact hx
    simp [φ, hxsq]
  let H' : Subgroup φ.ker := (B.subgroupOf C).subgroupOf φ.ker
  have hH'index : H'.index = 2 := by
    have hrelidx : (B.subgroupOf C).relIndex φ.ker * φ.ker.index = (B.subgroupOf C).index :=
      Subgroup.relIndex_mul_index hBK
    have hHidx : (B.subgroupOf C).index = 4 := index_four_of_relIndex hBC hrel
    have htwo : (B.subgroupOf C).relIndex φ.ker = 2 := by
      rw [hKindex, hHidx] at hrelidx
      omega
    simpa [H', Subgroup.relIndex] using htwo
  have hδK : ∀ x : C, conjBy hρC x * x⁻¹ ∈ φ.ker := by
    intro x
    rw [MonoidHom.mem_ker, map_mul, map_inv, hφρ x]
    exact mul_inv_cancel _
  have hfixK : ∀ k : C, k ∈ φ.ker → conjBy hρC k * k⁻¹ ∈ B.subgroupOf C := by
    intro k hk
    have hck : conjBy hρC k ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      rw [hφρ k, MonoidHom.mem_ker.mp hk]
    have hconjiff : (conjBy hρC k ∈ B.subgroupOf C) ↔ (k ∈ B.subgroupOf C) := by
      constructor
      · intro hmem
        let b : B := ⟨(conjBy hρC k : S), Subgroup.mem_subgroupOf.mp hmem⟩
        have hb_eq : Subgroup.inclusion hBC b = conjBy hρC k := rfl
        have hrec : conjBy (Subgroup.inv_mem _ hρC) (conjBy hρC k) = k :=
          conjBy_inv_conjBy hρC k
        have hincl : Subgroup.inclusion hBC (conjBy (Subgroup.inv_mem _ D.ρ_mem) b) ∈
            B.subgroupOf C := Subgroup.mem_subgroupOf.mpr (conjBy (Subgroup.inv_mem _ D.ρ_mem) b).2
        have hk_eq : k = Subgroup.inclusion hBC (conjBy (Subgroup.inv_mem _ D.ρ_mem) b) := by
          calc k = conjBy (Subgroup.inv_mem _ hρC) (conjBy hρC k) := hrec.symm
            _ = conjBy (Subgroup.inv_mem _ hρC) (Subgroup.inclusion hBC b) := by rw [hb_eq]
            _ = Subgroup.inclusion hBC (conjBy (Subgroup.inv_mem _ D.ρ_mem) b) :=
                conjBy_inclusion hBC (Subgroup.inv_mem _ hρC) (Subgroup.inv_mem _ D.ρ_mem) b
        rw [hk_eq]
        exact hincl
      · intro hmem
        obtain ⟨b, rfl⟩ : ∃ b : B, Subgroup.inclusion hBC b = k :=
          ⟨⟨(k : S), Subgroup.mem_subgroupOf.mp hmem⟩, rfl⟩
        rw [conjBy_inclusion hBC hρC D.ρ_mem b]
        exact Subgroup.mem_subgroupOf.mpr (conjBy D.ρ_mem b).2
    let ck : φ.ker := ⟨conjBy hρC k, hck⟩
    let ik : φ.ker := ⟨k⁻¹, φ.ker.inv_mem hk⟩
    have hiff : ck ∈ H' ↔ ik ∈ H' := by
      change (conjBy hρC k ∈ B.subgroupOf C) ↔ (k⁻¹ ∈ B.subgroupOf C)
      rw [inv_mem_iff]
      exact hconjiff
    have hprod : ck * ik ∈ H' := (Subgroup.mul_mem_iff_of_index_two hH'index).mpr hiff
    simpa [H', ck, ik, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
      using hprod
  have hδB : ∀ x : C, conjBy hρC x * x⁻¹ ∈ B.subgroupOf C := by
    intro x
    let k : C := conjBy hρC x * x⁻¹
    have hkK : k ∈ φ.ker := hδK x
    have hkB : conjBy hρC k * k⁻¹ ∈ B.subgroupOf C := hfixK k hkK
    have hk2H : (⟨k, hkK⟩ : φ.ker) ^ 2 ∈ H' := Subgroup.sq_mem_of_index_two hH'index _
    have hk2 : k * k ∈ B.subgroupOf C := by
      simpa [H', pow_two, Subgroup.mem_subgroupOf] using hk2H
    let bC : C := conjBy hρC k * k⁻¹
    let b'C : C := (k * k) * bC
    have hb'C : b'C ∈ B.subgroupOf C := (B.subgroupOf C).mul_mem hk2 hkB
    let b' : B := ⟨b'C, Subgroup.mem_subgroupOf.mp hb'C⟩
    have hxk : conjBy hρC x = x * k := by
      show conjBy hρC x = x * (conjBy hρC x * x⁻¹)
      rw [← mul_assoc, mul_comm x (conjBy hρC x), mul_assoc, mul_inv_cancel, mul_one]
    have hτk : conjBy hρC k = bC * k := by
      show conjBy hρC k = (conjBy hρC k * k⁻¹) * k
      rw [mul_assoc, inv_mul_cancel, mul_one]
    have hxρ2 : conjBy hρC (conjBy hρC x) = x * b'C := by
      calc conjBy hρC (conjBy hρC x)
          = conjBy hρC (x * k) := by rw [hxk]
        _ = conjBy hρC x * conjBy hρC k := conjBy_mul hρC x k
        _ = (x * k) * (bC * k) := by rw [hxk, hτk]
        _ = x * b'C := by
            show (x * k) * (bC * k) = x * ((k * k) * bC)
            rw [mul_mul_mul_comm, mul_assoc, mul_comm bC (k * k)]
    have hρinv3 : D.ρ⁻¹ * D.ρ⁻¹ * D.ρ⁻¹ = 1 := by
      calc D.ρ⁻¹ * D.ρ⁻¹ * D.ρ⁻¹ = (D.ρ * D.ρ * D.ρ)⁻¹ := by group
        _ = 1 := by rw [D.rho_cube, inv_one]
    have hτ3 : ∀ z : C, conjBy hρC (conjBy hρC (conjBy hρC z)) = z := by
      intro z
      apply Subtype.ext
      simp only [conjBy_val]
      calc D.ρ⁻¹ * (D.ρ⁻¹ * (D.ρ⁻¹ * (z : S) * D.ρ) * D.ρ) * D.ρ
          = (D.ρ⁻¹ * D.ρ⁻¹ * D.ρ⁻¹) * (z : S) * (D.ρ * D.ρ * D.ρ) := by group
        _ = z := by rw [hρinv3, D.rho_cube]; group
    have hτb'B : conjBy hρC b'C ∈ B.subgroupOf C := by
      have hb'eq : b'C = Subgroup.inclusion hBC b' := rfl
      rw [hb'eq, conjBy_inclusion hBC hρC D.ρ_mem b']
      exact Subgroup.mem_subgroupOf.mpr (conjBy D.ρ_mem b').2
    have hcancel : k * conjBy hρC b'C = 1 := by
      have h := hτ3 x
      rw [show conjBy hρC (conjBy hρC (conjBy hρC x)) =
          conjBy hρC (x * b'C) from by rw [hxρ2]] at h
      rw [conjBy_mul, hxk] at h
      have h' : x * (k * conjBy hρC b'C) = x * 1 := by
        calc x * (k * conjBy hρC b'C) = (x * k) * conjBy hρC b'C := by group
          _ = x := h
          _ = x * 1 := by group
      exact mul_left_cancel h'
    have hk : k ∈ B.subgroupOf C := by
      have hk_eq : k = (conjBy hρC b'C)⁻¹ := eq_inv_of_mul_eq_one_left hcancel
      rw [hk_eq]
      exact (B.subgroupOf C).inv_mem hτb'B
    exact hk
  have hrange : sq.range ≤ Subgroup.zpowers (QuotientGroup.mk' (sqSubgroup D) D.c) := by
    intro q hq
    obtain ⟨x, rfl⟩ := hq
    let y : B := ⟨(x : S) * (x : S),
      sq_mem_of_not_cyclic_quotient_four hBC hC hrel hncyc x⟩
    have hkH : conjBy hρC x * x⁻¹ ∈ B.subgroupOf C := hδB x
    let kB : B := ⟨conjBy hρC x * x⁻¹, Subgroup.mem_subgroupOf.mp hkH⟩
    have hy_fixed : conjBy D.ρ_mem y * y⁻¹ ∈ sqSubgroup D := by
      have hEqC : Subgroup.inclusion hBC (conjBy D.ρ_mem y * y⁻¹) =
          Subgroup.inclusion hBC (kB * kB) := by
        rw [map_mul, map_inv, map_mul]
        have hy_eq : Subgroup.inclusion hBC y = x * x := rfl
        have hkB_eq : Subgroup.inclusion hBC kB = conjBy hρC x * x⁻¹ := rfl
        have hconj_eq : Subgroup.inclusion hBC (conjBy D.ρ_mem y) =
            conjBy hρC (Subgroup.inclusion hBC y) :=
          (conjBy_inclusion hBC hρC D.ρ_mem y).symm
        rw [hconj_eq, hy_eq, hkB_eq, conjBy_mul]
        rw [mul_inv_rev]
        exact mul_mul_mul_comm _ _ _ _
      have hEq : conjBy D.ρ_mem y * y⁻¹ = kB * kB :=
        Subgroup.inclusion_injective hBC hEqC
      rw [hEq]
      simpa [pow_two] using sq_mem_sqSubgroup D kB
    obtain ⟨i, hi⟩ := t100_sqSubgroup_fixed_rho D y hy_fixed
    have hclass : QuotientGroup.mk' (sqSubgroup D) y =
        (QuotientGroup.mk' (sqSubgroup D) D.c) ^ i := by
      have h1 : QuotientGroup.mk' (sqSubgroup D) (y * D.c ^ (-i)) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr hi
      rw [map_mul, map_zpow] at h1
      calc QuotientGroup.mk' (sqSubgroup D) y
          = ((QuotientGroup.mk' (sqSubgroup D) D.c) ^ (-i))⁻¹ :=
              eq_inv_of_mul_eq_one_left h1
        _ = (QuotientGroup.mk' (sqSubgroup D) D.c) ^ i := by rw [zpow_neg, inv_inv]
    have hsq_eq : sq x = QuotientGroup.mk' (sqSubgroup D) y := rfl
    rw [hsq_eq, hclass]
    exact Subgroup.zpow_mem_zpowers (QuotientGroup.mk' (sqSubgroup D) D.c) i
  have hcard_range : Nat.card sq.range = 4 :=
    sqQuotientHom_range_card hcommC D hBC hC hrel hncyc hH hcS
  have hq2 : (QuotientGroup.mk' (sqSubgroup D) D.c) ^ 2 = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (by simpa [pow_two] using sq_mem_sqSubgroup D D.c)
  have hdvd : orderOf (QuotientGroup.mk' (sqSubgroup D) D.c) ∣ 2 :=
    orderOf_dvd_iff_pow_eq_one.mpr (by simpa [pow_two] using hq2)
  have hcard_zp :
      Nat.card (Subgroup.zpowers (QuotientGroup.mk' (sqSubgroup D) D.c)) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) hdvd
  have hle_card : Nat.card sq.range ≤
      Nat.card (Subgroup.zpowers (QuotientGroup.mk' (sqSubgroup D) D.c)) :=
    Subgroup.card_le_of_le hrange
  rw [hcard_range] at hle_card
  omega

theorem sq_range_eq_ab
    [hN : (B.subgroupOf C).Normal]
    (hB : HasStrothType B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hL : hB.data.L ≤ Subgroup.normalizer C)
    (hncyc : ¬ IsCyclic (C ⧸ B.subgroupOf C))
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S')
    (hm : 1 ≤ m) :
    (sqQuotientHom (isMulCommutative_of_relIndex_four_of_not_cyclic hB hBC hC hrel hL hncyc)
        hB.data hBC hC hrel hncyc).range = (cParityQuotient hB.data hm).ker := by
  have hcommC : IsMulCommutative C :=
    isMulCommutative_of_relIndex_four_of_not_cyclic hB hBC hC hrel hL hncyc
  refine Subgroup.eq_of_le_of_card_ge
    (sqQuotientHom_range_le_cParity_ker hcommC hB.data hBC hC hrel hncyc hL hH hcS hm) ?_
  rw [sqQuotientHom_range_card hcommC hB.data hBC hC hrel hncyc hH hcS,
    cParityQuotient_ker_card hB.data hm]


theorem t100_a_not_mem_sqSubgroup
    (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hm : 1 ≤ m) :
    D.a ∉ sqSubgroup D := by
  intro h
  have hker : D.a ∈ (parityHom D hm).ker := by
    rw [parityHom_ker_eq_sqSubgroup D hm]
    exact h
  have hval := MonoidHom.mem_ker.mp hker
  rw [parityHom_a] at hval
  have hsingle : (Pi.single (1 : Fin 3) (1 : ZMod 2) : Fin 3 → ZMod 2) ≠ 0 := by
    intro h0
    have h1 := congrFun h0 1
    norm_num at h1
  exact hsingle (Multiplicative.ofAdd.injective (by simpa using hval))

theorem t100_b_not_mem_sqSubgroup
    (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hm : 1 ≤ m) :
    D.b ∉ sqSubgroup D := by
  intro h
  have hker : D.b ∈ (parityHom D hm).ker := by
    rw [parityHom_ker_eq_sqSubgroup D hm]
    exact h
  have hval := MonoidHom.mem_ker.mp hker
  rw [parityHom_b] at hval
  have hsingle : (Pi.single (2 : Fin 3) (1 : ZMod 2) : Fin 3 → ZMod 2) ≠ 0 := by
    intro h0
    have h1 := congrFun h0 2
    norm_num at h1
  exact hsingle (Multiplicative.ofAdd.injective (by simpa using hval))

theorem t100_ab_not_mem_sqSubgroup
    (D : StrothTypeData B (StrothTypeIndex.t100 m)) (hm : 1 ≤ m) :
    D.a * D.b⁻¹ ∉ sqSubgroup D := by
  intro h
  have hker : D.a * D.b⁻¹ ∈ (parityHom D hm).ker := by
    rw [parityHom_ker_eq_sqSubgroup D hm]
    exact h
  have hval := MonoidHom.mem_ker.mp hker
  rw [map_mul, map_inv, parityHom_a, parityHom_b] at hval
  have h' := congrArg Multiplicative.toAdd hval
  simp only [toAdd_mul, toAdd_inv, toAdd_ofAdd, toAdd_one] at h'
  have h1 := congrFun h' 1
  simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply, Pi.single_eq_same,
    Pi.single_eq_of_ne (by decide : (2 : Fin 3) ≠ 1), neg_zero, add_zero] at h1
  exact one_ne_zero h1

theorem exists_sq_eq_a_b
    [hN : (B.subgroupOf C).Normal]
    (hB : HasStrothType B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hL : hB.data.L ≤ Subgroup.normalizer C)
    (hncyc : ¬ IsCyclic (C ⧸ B.subgroupOf C))
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S')
    (hm : 1 ≤ m) :
    ∃ e f : C, e * e = ⟨hB.data.a, hBC hB.data.a.2⟩ ∧
      f * f = ⟨hB.data.b, hBC hB.data.b.2⟩ := by
  classical
  let D := hB.data
  let hcommC : IsMulCommutative C :=
    isMulCommutative_of_relIndex_four_of_not_cyclic hB hBC hC hrel hL hncyc
  let sq := sqQuotientHom hcommC D hBC hC hrel hncyc
  have hca : cParity D hm D.a = 0 := by
    rw [cParity, D.ec_a]
    simp [Torus.a, gen, Pi.single_apply]
  have hcb : cParity D hm D.b = 0 := by
    rw [cParity, D.ec_b]
    simp [Torus.b, gen, Pi.single_apply]
  have ha_range : QuotientGroup.mk' (sqSubgroup D) D.a ∈ sq.range := by
    have hreq := sq_range_eq_ab hB hBC hC hrel hL hncyc hH hcS hm
    rw [show sq.range = (cParityQuotient D hm).ker from hreq]
    rw [MonoidHom.mem_ker, cParityQuotient_mk, cParityHom_apply, hca]
    rfl
  have hb_range : QuotientGroup.mk' (sqSubgroup D) D.b ∈ sq.range := by
    have hreq := sq_range_eq_ab hB hBC hC hrel hL hncyc hH hcS hm
    rw [show sq.range = (cParityQuotient D hm).ker from hreq]
    rw [MonoidHom.mem_ker, cParityQuotient_mk, cParityHom_apply, hcb]
    rfl
  obtain ⟨e0, he0⟩ := MonoidHom.mem_range.mp ha_range
  obtain ⟨f0, hf0⟩ := MonoidHom.mem_range.mp hb_range
  have haC : (⟨D.a, hBC D.a.2⟩ : C) = Subgroup.inclusion hBC D.a := rfl
  have hbC : (⟨D.b, hBC D.b.2⟩ : C) = Subgroup.inclusion hBC D.b := rfl
  let ea : B := ⟨(e0 : S) * (e0 : S),
    sq_mem_of_not_cyclic_quotient_four hBC hC hrel hncyc e0⟩
  have hsq_e0 : sq e0 = QuotientGroup.mk' (sqSubgroup D) ea := rfl
  have hza : ea⁻¹ * D.a ∈ sqSubgroup D := by
    have h := (QuotientGroup.eq (s := sqSubgroup D)).mp (by simpa [hsq_e0] using he0)
    simpa using h
  obtain ⟨sa, hsa⟩ := exists_sq_eq_of_mem_sqSubgroup D hza
  let saC : C := Subgroup.inclusion hBC sa
  have hsaC : saC * saC = (Subgroup.inclusion hBC ea)⁻¹ * (⟨D.a, hBC D.a.2⟩ : C) := by
    apply Subtype.ext
    have h := congrArg (fun z : B => (z : S)) hsa
    simpa [saC, ea] using h
  have he_sq : (e0 * saC) * (e0 * saC) = ⟨D.a, hBC D.a.2⟩ := by
    calc (e0 * saC) * (e0 * saC) = (e0 * e0) * (saC * saC) := by
          rw [mul_mul_mul_comm]
      _ = (e0 * e0) * ((Subgroup.inclusion hBC ea)⁻¹ * ⟨D.a, hBC D.a.2⟩) := by rw [hsaC]
      _ = ⟨D.a, hBC D.a.2⟩ := by
          rw [show (e0 * e0 : C) = Subgroup.inclusion hBC ea from rfl]
          rw [← mul_assoc, mul_inv_cancel, one_mul]
  let fb : B := ⟨(f0 : S) * (f0 : S),
    sq_mem_of_not_cyclic_quotient_four hBC hC hrel hncyc f0⟩
  have hsq_f0 : sq f0 = QuotientGroup.mk' (sqSubgroup D) fb := rfl
  have hzb : fb⁻¹ * D.b ∈ sqSubgroup D := by
    have h := (QuotientGroup.eq (s := sqSubgroup D)).mp (by simpa [hsq_f0] using hf0)
    simpa using h
  obtain ⟨sb, hsb⟩ := exists_sq_eq_of_mem_sqSubgroup D hzb
  let sbC : C := Subgroup.inclusion hBC sb
  have hsbC : sbC * sbC = (Subgroup.inclusion hBC fb)⁻¹ * (⟨D.b, hBC D.b.2⟩ : C) := by
    apply Subtype.ext
    have h := congrArg (fun z : B => (z : S)) hsb
    simpa [sbC, fb] using h
  have hf_sq : (f0 * sbC) * (f0 * sbC) = ⟨D.b, hBC D.b.2⟩ := by
    calc (f0 * sbC) * (f0 * sbC) = (f0 * f0) * (sbC * sbC) := by
          rw [mul_mul_mul_comm]
      _ = (f0 * f0) * ((Subgroup.inclusion hBC fb)⁻¹ * ⟨D.b, hBC D.b.2⟩) := by rw [hsbC]
      _ = ⟨D.b, hBC D.b.2⟩ := by
          rw [show (f0 * f0 : C) = Subgroup.inclusion hBC fb from rfl]
          rw [← mul_assoc, mul_inv_cancel, one_mul]
  exact ⟨e0 * saC, f0 * sbC, he_sq, hf_sq⟩

theorem closure_c_e_f_of_comm
    (hcommC : IsMulCommutative C)
    (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (hrel : Nat.card C = 4 * Nat.card B) (hm : 1 ≤ m)
    {e f : C}
    (he : e * e = ⟨D.a, hBC D.a.2⟩) (hf : f * f = ⟨D.b, hBC D.b.2⟩) :
    Subgroup.closure ({⟨D.c, hBC D.c.2⟩, e, f} : Set C) = ⊤ := by
  classical
  let cC : C := ⟨D.c, hBC D.c.2⟩
  let aC : C := ⟨D.a, hBC D.a.2⟩
  let bC : C := ⟨D.b, hBC D.b.2⟩
  let K : Subgroup C := Subgroup.closure ({cC, e, f} : Set C)
  have hcK : cC ∈ K := Subgroup.subset_closure (by simp [K])
  have heK : e ∈ K := Subgroup.subset_closure (by simp [K])
  have hfK : f ∈ K := Subgroup.subset_closure (by simp [K])
  have haK : aC ∈ K := by
    have h : aC = e * e := he.symm
    rw [h]
    exact K.mul_mem heK heK
  have hbK : bC ∈ K := by
    have h : bC = f * f := hf.symm
    rw [h]
    exact K.mul_mem hfK hfK
  have hBgenB : Subgroup.closure ({(D.c : B), (D.a : B), (D.b : B)} : Set B) = ⊤ := by
    apply Subgroup.map_injective (Subgroup.subtype_injective B)
    rw [MonoidHom.map_closure, Subgroup.map_top, Subgroup.range_subtype]
    have himg : B.subtype '' ({(D.c : B), (D.a : B), (D.b : B)} : Set B) =
        ({(D.c : S), (D.a : S), (D.b : S)} : Set S) := by
      ext y
      simp
    rw [himg, D.closure_c_a_b]
  have hBgenC : B.subgroupOf C = Subgroup.closure ({cC, aC, bC} : Set C) := by
    calc B.subgroupOf C = (⊤ : Subgroup B).map (Subgroup.inclusion hBC) := by
          rw [Subgroup.map_top, Subgroup.inclusion_range]
      _ = (Subgroup.closure ({(D.c : B), (D.a : B), (D.b : B)} : Set B)).map
            (Subgroup.inclusion hBC) := by rw [hBgenB]
      _ = Subgroup.closure ((Subgroup.inclusion hBC) ''
            ({(D.c : B), (D.a : B), (D.b : B)} : Set B)) :=
          MonoidHom.map_closure (Subgroup.inclusion hBC) _
      _ = Subgroup.closure ({cC, aC, bC} : Set C) := by
          have hc_eq : (Subgroup.inclusion hBC D.c : C) = cC := Subtype.ext rfl
          have ha_eq : (Subgroup.inclusion hBC D.a : C) = aC := Subtype.ext rfl
          have hb_eq : (Subgroup.inclusion hBC D.b : C) = bC := Subtype.ext rfl
          congr 1
          ext y
          simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
          constructor
          · rintro ⟨b, hb, hby⟩
            rcases hb with rfl | rfl | rfl
            · exact Or.inl (hby.symm.trans hc_eq)
            · exact Or.inr (Or.inl (hby.symm.trans ha_eq))
            · exact Or.inr (Or.inr (hby.symm.trans hb_eq))
          · rintro (h | h | h)
            · exact ⟨D.c, Or.inl rfl, hc_eq.trans h.symm⟩
            · exact ⟨D.a, Or.inr (Or.inl rfl), ha_eq.trans h.symm⟩
            · exact ⟨D.b, Or.inr (Or.inr rfl), hb_eq.trans h.symm⟩
  have hB_le_K : B.subgroupOf C ≤ K := by
    rw [hBgenC]
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact hcK
    · exact haK
    · exact hbK
  have ha_not : D.a ∉ sqSubgroup D := t100_a_not_mem_sqSubgroup D hm
  have hb_not : D.b ∉ sqSubgroup D := t100_b_not_mem_sqSubgroup D hm
  have hab_not : D.a * D.b⁻¹ ∉ sqSubgroup D := t100_ab_not_mem_sqSubgroup D hm
  have he_notH : e ∉ B.subgroupOf C := by
    intro heH
    have heB : (e : S) ∈ B := Subgroup.mem_subgroupOf.mp heH
    let eB : B := ⟨(e : S), heB⟩
    have heB_sq : eB * eB = D.a := by
      apply Subtype.ext
      have h := congrArg (fun z : C => (z : S)) he
      simpa [eB, aC] using h
    have hmem : D.a ∈ sqSubgroup D := by
      rw [← heB_sq]
      simpa [pow_two] using sq_mem_sqSubgroup D eB
    exact ha_not hmem
  have hf_notH : f ∉ B.subgroupOf C := by
    intro hfH
    have hfB : (f : S) ∈ B := Subgroup.mem_subgroupOf.mp hfH
    let fB : B := ⟨(f : S), hfB⟩
    have hfB_sq : fB * fB = D.b := by
      apply Subtype.ext
      have h := congrArg (fun z : C => (z : S)) hf
      simpa [fB, bC] using h
    have hmem : D.b ∈ sqSubgroup D := by
      rw [← hfB_sq]
      simpa [pow_two] using sq_mem_sqSubgroup D fB
    exact hb_not hmem
  have hef_notH : e * f⁻¹ ∉ B.subgroupOf C := by
    intro hefH
    have hefB : ((e * f⁻¹ : C) : S) ∈ B := Subgroup.mem_subgroupOf.mp hefH
    let y : B := ⟨((e * f⁻¹ : C) : S), hefB⟩
    have hy_sqC : (e * f⁻¹) * (e * f⁻¹) = aC * bC⁻¹ := by
      calc (e * f⁻¹) * (e * f⁻¹) = (e * e) * (f⁻¹ * f⁻¹) :=
            mul_mul_mul_comm _ _ _ _
        _ = (e * e) * (f * f)⁻¹ := by rw [← mul_inv_rev]
        _ = aC * bC⁻¹ := by rw [he, hf]
    have hy_sq : y * y = D.a * D.b⁻¹ := by
      apply Subtype.ext
      have h := congrArg (fun z : C => (z : S)) hy_sqC
      simpa [y, aC, bC] using h
    have hmem : D.a * D.b⁻¹ ∈ sqSubgroup D := by
      rw [← hy_sq]
      simpa [pow_two] using sq_mem_sqSubgroup D y
    exact hab_not hmem
  have hHindex : (B.subgroupOf C).index = 4 := index_four_of_relIndex hBC hrel
  have hrel_dvd : (B.subgroupOf C).relIndex K ∣ 4 := by
    have h := Subgroup.relIndex_mul_index hB_le_K
    rw [hHindex] at h
    exact ⟨K.index, h.symm⟩
  have hrel_ne1 : (B.subgroupOf C).relIndex K ≠ 1 := by
    intro h1
    rw [Subgroup.relIndex_eq_one] at h1
    exact he_notH (h1 heK)
  have hrel_ne2 : (B.subgroupOf C).relIndex K ≠ 2 := by
    intro h2
    have hH'index : ((B.subgroupOf C).subgroupOf K).index = 2 := by
      simpa [Subgroup.relIndex] using h2
    have heK' : (⟨e, heK⟩ : K) ∉ (B.subgroupOf C).subgroupOf K := by
      intro hmem
      exact he_notH (Subgroup.mem_subgroupOf.mp hmem)
    have hfK' : (⟨f⁻¹, K.inv_mem hfK⟩ : K) ∉ (B.subgroupOf C).subgroupOf K := by
      intro hmem
      exact hf_notH (inv_mem_iff.mp (Subgroup.mem_subgroupOf.mp hmem))
    have hprod : (⟨e, heK⟩ : K) * (⟨f⁻¹, K.inv_mem hfK⟩ : K) ∈
        (B.subgroupOf C).subgroupOf K :=
      (Subgroup.mul_mem_iff_of_index_two hH'index).mpr (by simp [heK', hfK'])
    have : e * f⁻¹ ∈ B.subgroupOf C := by
      simpa [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] using hprod
    exact hef_notH this
  have hrel4 : (B.subgroupOf C).relIndex K = 4 := by
    have hpos : 0 < (B.subgroupOf C).relIndex K :=
      Nat.pos_of_dvd_of_pos hrel_dvd (by norm_num)
    have hle : (B.subgroupOf C).relIndex K ≤ 4 := Nat.le_of_dvd (by norm_num) hrel_dvd
    interval_cases (B.subgroupOf C).relIndex K <;> simp_all
  have hKindex : K.index = 1 := by
    have h := Subgroup.relIndex_mul_index hB_le_K
    rw [hrel4, hHindex] at h
    omega
  exact Subgroup.index_eq_one.mp hKindex

theorem orderOf_eq_two_pow_succ_of_sq {G : Type*} [Group G] [Finite G]
    {m : ℕ} {x a : G} (hx : x * x = a) (ha : orderOf a = 2 ^ (m + 1)) :
    orderOf x = 2 ^ (m + 2) := by
  have hx2 : x ^ 2 = a := by rw [pow_two]; exact hx
  have hx_dvd : orderOf x ∣ 2 ^ (m + 2) := by
    rw [orderOf_dvd_iff_pow_eq_one]
    rw [show 2 ^ (m + 2) = 2 * 2 ^ (m + 1) by rw [pow_succ]; ring]
    rw [pow_mul, hx2, ← ha, pow_orderOf_eq_one]
  have hx_not_dvd : ¬ orderOf x ∣ 2 ^ (m + 1) := by
    intro hd
    have hxpow : x ^ (2 ^ (m + 1)) = 1 := (orderOf_dvd_iff_pow_eq_one).mp hd
    have hapow : a ^ (2 ^ m) = 1 := by
      rw [← hxpow]
      rw [show 2 ^ (m + 1) = 2 * 2 ^ m by rw [pow_succ]; ring]
      rw [pow_mul, hx2]
    have hdvd : orderOf a ∣ 2 ^ m := (orderOf_dvd_iff_pow_eq_one).mpr hapow
    rw [ha] at hdvd
    have hle : 2 ^ (m + 1) ≤ 2 ^ m := Nat.le_of_dvd (by positivity) hdvd
    have hlt : 2 ^ m < 2 ^ (m + 1) :=
      Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega : m < m + 1)
    omega
  obtain ⟨k, hk_le, hk_eq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hx_dvd
  have hk_not_le : ¬ k ≤ m + 1 := by
    intro hk
    apply hx_not_dvd
    rw [hk_eq]
    exact pow_dvd_pow 2 hk
  have hk : k = m + 2 := by omega
  rw [hk_eq, hk]

theorem closure_c_e_f
    [hN : (B.subgroupOf C).Normal]
    (hB : HasStrothType B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hL : hB.data.L ≤ Subgroup.normalizer C)
    (hncyc : ¬ IsCyclic (C ⧸ B.subgroupOf C))
    (hm : 1 ≤ m) {e f : C}
    (he : e * e = ⟨hB.data.a, hBC hB.data.a.2⟩)
    (hf : f * f = ⟨hB.data.b, hBC hB.data.b.2⟩) :
    Subgroup.closure ({⟨hB.data.c, hBC hB.data.c.2⟩, e, f} : Set C) = ⊤ :=
  closure_c_e_f_of_comm
    (isMulCommutative_of_relIndex_four_of_not_cyclic hB hBC hC hrel hL hncyc)
    hB.data hBC hrel hm he hf

theorem torusBasisEquivFour_of_sq
    [hN : (B.subgroupOf C).Normal]
    (hcommC : IsMulCommutative C)
    (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (hrel : Nat.card C = 4 * Nat.card B) (hm : 1 ≤ m)
    {e f : C}
    (he : e * e = ⟨D.a, hBC D.a.2⟩) (hf : f * f = ⟨D.b, hBC D.b.2⟩) :
    Nonempty (TorusBasisEquivFour D hBC e f) := by
  classical
  let cC : C := ⟨D.c, hBC D.c.2⟩
  have hgenC : Subgroup.closure ({cC, e, f} : Set C) = ⊤ :=
    closure_c_e_f_of_comm hcommC D hBC hrel hm he hf
  have hgenS : Subgroup.closure ({(D.c : S), (e : S), (f : S)} : Set S) = C := by
    have himg : C.subtype '' ({cC, e, f} : Set C) =
        ({(D.c : S), (e : S), (f : S)} : Set S) := by
      ext y
      simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨z, hz, rfl⟩
        rcases hz with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      · rintro (rfl | rfl | rfl)
        · exact ⟨cC, Or.inl rfl, rfl⟩
        · exact ⟨e, Or.inr (Or.inl rfl), rfl⟩
        · exact ⟨f, Or.inr (Or.inr rfl), rfl⟩
    calc Subgroup.closure ({(D.c : S), (e : S), (f : S)} : Set S)
        = Subgroup.closure (C.subtype '' ({cC, e, f} : Set C)) := by rw [himg]
      _ = (Subgroup.closure ({cC, e, f} : Set C)).map C.subtype :=
          (MonoidHom.map_closure C.subtype _).symm
      _ = (⊤ : Subgroup C).map C.subtype := by rw [hgenC]
      _ = C := by rw [Subgroup.map_top, Subgroup.range_subtype]
  have haC_order : orderOf (⟨D.a, hBC D.a.2⟩ : C) = 2 ^ (m + 1) := by
    rw [show (⟨D.a, hBC D.a.2⟩ : C) = Subgroup.inclusion hBC D.a from rfl,
      orderOf_injective (Subgroup.inclusion hBC) (Subgroup.inclusion_injective hBC) D.a,
      D.orderOf_a, n_t100]
  have hbC_order : orderOf (⟨D.b, hBC D.b.2⟩ : C) = 2 ^ (m + 1) := by
    rw [show (⟨D.b, hBC D.b.2⟩ : C) = Subgroup.inclusion hBC D.b from rfl,
      orderOf_injective (Subgroup.inclusion hBC) (Subgroup.inclusion_injective hBC) D.b,
      D.orderOf_b, n_t100]
  have he_order : orderOf e = 2 ^ (m + 2) :=
    orderOf_eq_two_pow_succ_of_sq he haC_order
  have hf_order : orderOf f = 2 ^ (m + 2) :=
    orderOf_eq_two_pow_succ_of_sq hf hbC_order
  exact torusBasisEquivFour_of_generators hcommC D hBC hrel hgenS he_order hf_order

theorem torusBasisEquivFour
    [hN : (B.subgroupOf C).Normal]
    (hB : HasStrothType B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hL : hB.data.L ≤ Subgroup.normalizer C)
    (hncyc : ¬ IsCyclic (C ⧸ B.subgroupOf C))
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S')
    (hm : 1 ≤ m) :
    ∃ e f : C, e * e = ⟨hB.data.a, hBC hB.data.a.2⟩ ∧
      f * f = ⟨hB.data.b, hBC hB.data.b.2⟩ ∧
      Nonempty (TorusBasisEquivFour hB.data hBC e f) := by
  have hcommC : IsMulCommutative C :=
    isMulCommutative_of_relIndex_four_of_not_cyclic hB hBC hC hrel hL hncyc
  obtain ⟨e, f, he, hf⟩ := exists_sq_eq_a_b hB hBC hC hrel hL hncyc hH hcS hm
  exact ⟨e, f, he, hf, torusBasisEquivFour_of_sq hcommC hB.data hBC hrel hm he hf⟩
