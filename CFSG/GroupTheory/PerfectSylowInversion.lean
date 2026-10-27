module

public import Mathlib.GroupTheory.IsPerfect

import CFSG.RankThree.PartOne.K1214.PGroupCyclic
import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.L3YC.AbelianSylowCentre
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Topology.Sheaves.Presheaf

public section

open scoped Pointwise

namespace CFSG.GroupTheory

theorem exists_conj_eq_inv_of_isPerfect {Q : Type*} [Group Q] [Finite Q] {Y : Subgroup Q}
    (hY : Group.IsPerfect ↥Y) {x : Q} (hxY : x ∈ Y) (hx : orderOf x = 3)
    (h3 : ∀ y ∈ Y, y * x = x * y → y ^ 3 = 1 → y ∈ Subgroup.zpowers x) :
    ∃ n ∈ Y, n * x * n⁻¹ = x⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let X := ↥Y
  let x' : X := ⟨x, hxY⟩
  have hx'3 : orderOf x' = 3 := by
    rw [← Subgroup.orderOf_coe x']
    exact hx
  have hx'ne : x' ≠ 1 := by
    intro h
    have h1 : orderOf x' = 1 := by rw [h, orderOf_one]
    omega
  have hxp : IsPGroup 3 (Subgroup.zpowers x') := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hx'3, pow_one]
  obtain ⟨P, hxP⟩ := hxp.exists_le_sylow
  have hx'P : x' ∈ (P : Subgroup X) := hxP (Subgroup.mem_zpowers x')
  have hP3 : IsPGroup 3 (P : Subgroup X) := P.isPGroup'
  haveI hPnt : Nontrivial ↥(P : Subgroup X) :=
    ⟨⟨x', hx'P⟩, ⟨1, (P : Subgroup X).one_mem⟩, by
      intro h; exact hx'ne (congrArg Subtype.val h)⟩
  let x'P : ↥(P : Subgroup X) := ⟨x', hx'P⟩
  have hZnt : Nontrivial (Subgroup.center ↥(P : Subgroup X)) := hP3.center_nontrivial
  have hZ3 : IsPGroup 3 (Subgroup.center ↥(P : Subgroup X)) := hP3.to_subgroup _
  have h3dvdZ : 3 ∣ Nat.card (Subgroup.center ↥(P : Subgroup X)) := by
    rcases (IsPGroup.nontrivial_iff_card (p := 3) (G := Subgroup.center ↥(P : Subgroup X))
      hZ3).mp hZnt with ⟨n, hn, hcard⟩
    rw [hcard]
    exact dvd_pow_self 3 (Nat.pos_iff_ne_zero.mp hn)
  obtain ⟨zC, hzC3⟩ :=
    exists_prime_orderOf_dvd_card' (G := Subgroup.center ↥(P : Subgroup X)) 3 h3dvdZ
  let zP : ↥(P : Subgroup X) := (zC : ↥(P : Subgroup X))
  let zX : X := (zP : X)
  have hzP3 : orderOf zP = 3 := (Subgroup.orderOf_coe zC).trans hzC3
  have hz3 : orderOf zX = 3 := (Subgroup.orderOf_coe zP).trans hzP3
  have hzpow : zX ^ 3 = 1 := by
    rw [← hz3]
    exact pow_orderOf_eq_one zX
  have hcommP : zP * x'P = x'P * zP := ((Subgroup.mem_center_iff.mp zC.2) x'P).symm
  have hcommX : zX * x' = x' * zX := by
    have h := congrArg (Subgroup.subtype (P : Subgroup X)) hcommP
    simpa [zX, zP, x'P] using h
  have hcommQ : (zX : Q) * x = x * (zX : Q) := by
    simpa [X, x'] using congrArg Subtype.val hcommX
  have hzmem : (zX : Q) ∈ Subgroup.zpowers x :=
    h3 (zX : Q) zX.2 hcommQ (by simpa [X] using congrArg Subtype.val hzpow)
  have hz3Q : orderOf (zX : Q) = 3 := (Subgroup.orderOf_coe zX).trans hz3
  have hzp_eq : Subgroup.zpowers (zX : Q) = Subgroup.zpowers x := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzmem) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hz3Q, hx]
  have hxmemZ : x ∈ Subgroup.zpowers (zX : Q) := by
    rw [hzp_eq]
    exact Subgroup.mem_zpowers x
  have hx'zP : x'P ∈ Subgroup.zpowers zP := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxmemZ
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨k, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    simpa [X, zX, zP, x', x'P] using hk
  have hx'Pcenter : x'P ∈ Subgroup.center ↥(P : Subgroup X) := by
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx'zP
    rw [← hk]
    have hcomm : Commute w zP := Subgroup.mem_center_iff.mp zC.2 w
    exact hcomm.zpow_right k
  have h3' : ∀ z ∈ (P : Subgroup X), z ^ 3 = 1 → z ∈ Subgroup.zpowers x' := by
    intro z hzP hz3
    have hcommP' : Commute (⟨z, hzP⟩ : ↥(P : Subgroup X)) x'P :=
      (Subgroup.mem_center_iff.mp hx'Pcenter) ⟨z, hzP⟩
    have hcommX : z * x' = x' * z := by
      have h := congrArg (Subgroup.subtype (P : Subgroup X)) hcommP'.eq
      simpa [x'P] using h
    have hcommQ : (z : Q) * x = x * (z : Q) := by
      simpa [X, x'] using congrArg Subtype.val hcommX
    have hz3Q : (z : Q) ^ 3 = 1 := by
      simpa [X] using congrArg Subtype.val hz3
    have hmem := h3 (z : Q) z.2 hcommQ hz3Q
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨k, ?_⟩
    apply Subtype.ext
    simpa [X, x'] using hk
  have hPcyc : IsCyclic ↥(P : Subgroup X) :=
    CFSG.RankThree.PartOne.K1214.isCyclic_subgroup_of_pow_eq_one_subset
      (p := 3) Nat.prime_three (by norm_num) (Z := (P : Subgroup X)) hP3 hx'P hx'3 h3'
  haveI : IsMulCommutative ↥(P : Subgroup X) := hPcyc.isMulCommutative
  have hcomm_top : _root_.commutator X = ⊤ := by
    letI : Group.IsPerfect X := hY
    exact Group.IsPerfect.commutator_eq_top
  have hex : ∃ n ∈ Subgroup.normalizer (P : Set X), n⁻¹ * x' * n ≠ x' := by
    by_contra h
    push Not at h
    have h1 : x' = 1 := by
      open CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.L3YC in
      exact AbelianSylowCentre.eq_one_of_normalizer_fixed (p := 3) hcomm_top P x' hx'P h
    exact hx'ne h1
  obtain ⟨n, hnN, hnne⟩ := hex
  have hnyP : n⁻¹ * x' * n ∈ (P : Subgroup X) := by
    have hninvN : n⁻¹ ∈ Subgroup.normalizer (P : Set X) := Subgroup.inv_mem _ hnN
    have hmem := (Subgroup.mem_normalizer_iff.mp hninvN x').mp hx'P
    have hii : (n⁻¹)⁻¹ = n := inv_inv n
    rw [hii] at hmem
    exact hmem
  have hy3 : orderOf (n⁻¹ * x' * n) = 3 := by
    have h := MulEquiv.orderOf_eq (MulAut.conj n⁻¹) x'
    have hconj : (MulAut.conj n⁻¹) x' = n⁻¹ * x' * n := by
      rw [MulAut.conj_apply, inv_inv]
    rw [hconj, hx'3] at h
    exact h
  have hyne1 : n⁻¹ * x' * n ≠ 1 := by
    intro h
    have h1 : orderOf (n⁻¹ * x' * n) = 1 := by rw [h, orderOf_one]
    omega
  have hy3pow : (n⁻¹ * x' * n) ^ 3 = 1 := by
    rw [← hy3]
    exact pow_orderOf_eq_one _
  have hmem : n⁻¹ * x' * n ∈ Subgroup.zpowers x' := h3' _ hnyP hy3pow
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hmod : x' ^ (k % 3) = x' ^ k := by
    have h := zpow_mod_orderOf x' k
    rwa [hx'3] at h
  have hy' : x' ^ (k % 3) = n⁻¹ * x' * n := by rw [hmod, hk]
  have hk0 : k % 3 ≠ 0 := by
    intro h0
    apply hyne1
    rw [← hy', h0, zpow_zero]
  have hk1 : k % 3 ≠ 1 := by
    intro h1
    apply hnne
    rw [← hy', h1, zpow_one]
  have hk2 : k % 3 = 2 := by
    have h0 := Int.emod_nonneg k (by norm_num : (3 : ℤ) ≠ 0)
    have hlt := Int.emod_lt_of_pos k (by norm_num : (0 : ℤ) < 3)
    omega
  have hyinv : n⁻¹ * x' * n = x'⁻¹ := by
    rw [← hy', hk2]
    have h2 : (2 : ℤ) = ((2 : ℕ) : ℤ) := by norm_num
    rw [h2, zpow_natCast, pow_two, eq_inv_iff_mul_eq_one]
    simpa [hx'3, pow_succ, mul_assoc] using pow_orderOf_eq_one x'
  refine ⟨((n⁻¹ : X) : Q), (n⁻¹ : X).2, ?_⟩
  simpa [X, x'] using congrArg Subtype.val hyinv

theorem exists_mem_normalizer_mk'_eq {M : Type*} [Group M] [Finite M] {p : ℕ} [Fact p.Prime]
    (N : Subgroup M) [N.Normal] (hN : ¬ p ∣ Nat.card N) {A : Subgroup M} (hA : IsPGroup p A)
    {r : M ⧸ N}
    (hr : r ∈ Subgroup.normalizer
      ((A.map (QuotientGroup.mk' N) : Subgroup (M ⧸ N)) : Set (M ⧸ N))) :
    ∃ s ∈ Subgroup.normalizer (A : Set M), QuotientGroup.mk' N s = r := by
  classical
  obtain ⟨m, hm⟩ := QuotientGroup.mk'_surjective N r
  let B : Subgroup M := A ⊔ N
  let C : Subgroup M := A.map (MulAut.conj m).toMonoidHom
  have hAN : A ⊓ N = ⊥ := by
    apply Subgroup.inf_eq_bot_of_coprime
    obtain ⟨k, hk⟩ := hA.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr hN)
  have hBcard : Nat.card B = Nat.card A * Nat.card N := by
    have h1 := Subgroup.relIndex_mul_card N B
    rw [inf_eq_left.mpr (le_sup_right : N ≤ B)] at h1
    have h2 : N.relIndex B = N.relIndex A := Subgroup.relIndex_sup_right A N
    rw [h2] at h1
    have h3 := Subgroup.relIndex_mul_card N A
    rw [inf_comm, hAN, Subgroup.card_bot, mul_one] at h3
    rw [h3] at h1
    exact h1.symm
  have hABcard : Nat.card (A.subgroupOf B) = Nat.card A := by
    have h := Subgroup.card_subtype B (A.subgroupOf B)
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (le_sup_left : A ≤ B)] at h
    exact h.symm
  have hABidx : ¬ p ∣ (A.subgroupOf B).index := by
    have h1 := Subgroup.card_mul_index (A.subgroupOf B)
    rw [hABcard, hBcard] at h1
    have h2 : (A.subgroupOf B).index = Nat.card N := Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
    rw [h2]
    exact hN
  have hCB : C ≤ B := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
    have hq : QuotientGroup.mk' N (m * a * m⁻¹) ∈ A.map (QuotientGroup.mk' N) := by
      have h1 : QuotientGroup.mk' N (m * a * m⁻¹)
          = r * QuotientGroup.mk' N a * r⁻¹ := by
        rw [map_mul, map_mul, map_inv, hm]
      rw [h1]
      exact (Subgroup.mem_normalizer_iff.mp hr (QuotientGroup.mk' N a)).mp
        (Subgroup.mem_map_of_mem _ ha)
    have h2 : m * a * m⁻¹ ∈ (A.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) := hq
    rw [QuotientGroup.comap_map_mk' N A] at h2
    simpa [B, sup_comm] using h2
  have hCcard : Nat.card C = Nat.card A := by
    have h := Subgroup.card_map_of_injective (K := A)
      (f := (MulAut.conj m).toMonoidHom) (MulAut.conj m).injective
    simpa [C] using h
  have hCsubcard : Nat.card (C.subgroupOf B) = Nat.card A := by
    have h := Subgroup.card_subtype B (C.subgroupOf B)
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hCB] at h
    rw [← h, hCcard]
  have hCBidx : ¬ p ∣ (C.subgroupOf B).index := by
    have h1 := Subgroup.card_mul_index (C.subgroupOf B)
    rw [hCsubcard, hBcard] at h1
    have h2 : (C.subgroupOf B).index = Nat.card N := Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
    rw [h2]
    exact hN
  have hABp : IsPGroup p (A.subgroupOf B) := hA.comap_subtype
  have hCBp : IsPGroup p (C.subgroupOf B) := by
    have h : IsPGroup p C := by
      simpa [C] using hA.map (MulAut.conj m).toMonoidHom
    exact h.comap_subtype
  let S : Sylow p B := hABp.toSylow hABidx
  let T : Sylow p B := hCBp.toSylow hCBidx
  have hScoe : (S : Subgroup B) = A.subgroupOf B := IsPGroup.toSylow_coe hABp hABidx
  have hTcoe : (T : Subgroup B) = C.subgroupOf B := IsPGroup.toSylow_coe hCBp hCBidx
  obtain ⟨b, hb⟩ := MulAction.exists_smul_eq B S T
  have hb_sub : MulAut.conj b • (A.subgroupOf B) = C.subgroupOf B := by
    have h := congrArg (fun Q : Sylow p B => (Q : Subgroup B)) hb
    rw [Sylow.coe_subgroup_smul, hScoe, hTcoe] at h
    exact h
  have hbA_le : A.map (MulAut.conj (b : M)).toMonoidHom ≤ C := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
    let aB : B := ⟨a, Subgroup.mem_sup_left ha⟩
    have haBsub : aB ∈ A.subgroupOf B := Subgroup.mem_subgroupOf.mpr ha
    have hmem_smul : (MulAut.conj b) aB ∈ (MulAut.conj b • (A.subgroupOf B) : Subgroup B) := by
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      have h : (MulAut.conj b)⁻¹ • ((MulAut.conj b) aB) = aB := by
        simpa using inv_smul_smul (MulAut.conj b) aB
      rw [h]
      exact haBsub
    rw [hb_sub] at hmem_smul
    have hCmem : ((MulAut.conj b) aB : M) ∈ C := Subgroup.mem_subgroupOf.mp hmem_smul
    simpa [MulAut.conj_apply] using hCmem
  have hbA_eq : A.map (MulAut.conj (b : M)).toMonoidHom = C := by
    refine Subgroup.eq_of_le_of_card_ge hbA_le ?_
    rw [Subgroup.card_map_of_injective (K := A)
      (f := (MulAut.conj (b : M)).toMonoidHom) (MulAut.conj (b : M)).injective, hCcard]
  have hmb_norm : (m⁻¹ * (b : M)) ∈ Subgroup.normalizer (A : Set M) := by
    apply Subgroup.mem_normalizer_fintype
    intro x hx
    have hxC : (b : M) * x * (b : M)⁻¹ ∈ C := by
      have hmem : (MulAut.conj (b : M)) x ∈ A.map (MulAut.conj (b : M)).toMonoidHom :=
        Subgroup.mem_map_of_mem (MulAut.conj (b : M)).toMonoidHom hx
      rw [hbA_eq] at hmem
      simpa [MulAut.conj_apply] using hmem
    obtain ⟨a', ha', haeq⟩ := Subgroup.mem_map.mp hxC
    have h : m⁻¹ * (b : M) * x * (m⁻¹ * (b : M))⁻¹ = a' := by
      have h1 : m⁻¹ * (b : M) * x * (m⁻¹ * (b : M))⁻¹
          = m⁻¹ * ((b : M) * x * (b : M)⁻¹) * m := by group
      rw [h1]
      have h2 : (b : M) * x * (b : M)⁻¹ = m * a' * m⁻¹ := by
        have haeq' : (MulAut.conj m) a' = (b : M) * x * (b : M)⁻¹ := haeq
        rw [← haeq', MulAut.conj_apply]
      rw [h2]
      group
    rw [h]
    exact ha'
  have hbmb_norm : ((b : M)⁻¹ * m) ∈ Subgroup.normalizer (A : Set M) := by
    have h := Subgroup.inv_mem _ hmb_norm
    simpa using h
  have hbB : (b : M) ∈ A ⊔ N := by
    simpa [B] using b.2
  obtain ⟨a, haA, n', hnN, hdecomp⟩ :=
    (Subgroup.mem_sup_of_normal_right (s := A) (t := N)).mp hbB
  let s : M := a * ((b : M)⁻¹ * m)
  have hs_norm : s ∈ Subgroup.normalizer (A : Set M) :=
    Subgroup.mul_mem _ (Subgroup.le_normalizer haA) hbmb_norm
  refine ⟨s, hs_norm, ?_⟩
  have hbinv : (b : M)⁻¹ = n'⁻¹ * a⁻¹ := by
    rw [← hdecomp, mul_inv_rev]
  have hs_eq : s = (a * n'⁻¹ * a⁻¹) * m := by
    simp [s, hbinv, mul_assoc]
  have hqn : QuotientGroup.mk' N n' = 1 := (QuotientGroup.eq_one_iff n').mpr hnN
  calc QuotientGroup.mk' N s
      = QuotientGroup.mk' N ((a * n'⁻¹ * a⁻¹) * m) := by rw [hs_eq]
    _ = QuotientGroup.mk' N (a * n'⁻¹ * a⁻¹) * QuotientGroup.mk' N m := map_mul _ _ _
    _ = 1 * r := by
          congr 1
          simp [map_mul, map_inv, hqn, hm]
    _ = r := one_mul r

end CFSG.GroupTheory
