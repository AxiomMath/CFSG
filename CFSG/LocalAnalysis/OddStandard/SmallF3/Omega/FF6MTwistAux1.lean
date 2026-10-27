module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFTransLayer

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

section Abstract

variable {N : Type} [Group N] [Finite N]

theorem ff6m_solvable_of_sq_mem (A : Subgroup N) [A.Normal] (hA : Group.IsSolvable ↥A)
    (hsq : ∀ g : N, g * g ∈ A) : Group.IsSolvable N := by
  have hzz : ∀ z : N ⧸ A, z * z = 1 := by
    intro z
    refine QuotientGroup.induction_on z (fun n => ?_)
    change (QuotientGroup.mk' A n) * (QuotientGroup.mk' A n) = 1
    rw [← map_mul, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hsq n
  have hcomm : ∀ x y : N ⧸ A, x * y = y * x := by
    intro x y
    have hx : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hzz x)
    have hy : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hzz y)
    calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right (hzz (x * y))).symm
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by rw [hx, hy]
  haveI : Group.IsSolvable (N ⧸ A) := Group.isSolvable_of_comm hcomm
  exact Group.isSolvable_of_ker_le_range A.subtype (QuotientGroup.mk' A) (by
    rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem ff6m_xTwoCore_of_sq_mem (A : Subgroup N) [A.Normal] (hA : XTwoCore ↥A)
    (hsq : ∀ g : N, g * g ∈ A) : XTwoCore N := by
  unfold XTwoCore at hA ⊢
  have htwoRes : twoRes (⊤ : Subgroup N) = twoRes A := by
    apply le_antisymm
    · unfold twoRes
      apply Subgroup.closure_mono
      rintro g ⟨-, hodd⟩
      refine ⟨?_, hodd⟩
      obtain ⟨k, hk⟩ := hodd
      have hpow : (g * g) ^ (k + 1) = g := by
        calc (g * g) ^ (k + 1) = (g ^ 2) ^ (k + 1) := by rw [pow_two]
          _ = g ^ (2 * (k + 1)) := (pow_mul g 2 (k + 1)).symm
          _ = g ^ (2 * k + 1 + 1) := by ring
          _ = g ^ (2 * k + 1) * g := by rw [pow_succ]
          _ = g ^ orderOf g * g := by rw [hk]
          _ = 1 * g := by rw [pow_orderOf_eq_one]
          _ = g := one_mul g
      rw [← hpow]
      exact pow_mem (hsq g) (k + 1)
    · unfold twoRes
      exact Subgroup.closure_mono fun g hg => ⟨trivial, hg.2⟩
  have hTA : (twoRes (⊤ : Subgroup ↥A)).map A.subtype = twoRes A := by
    rw [ff_map_twoRes A.subtype A.subtype_injective, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hmap1 : (ffX ↥A).map A.subtype = CFSG.inSubgroup (CFSG.pCore 2) (twoRes A) := by
    rw [hA, ff_inSubgroup_map (CFSG.pCore 2) (fun _ _ _ _ ε => CFSG.pCore_map_iso 2 ε)
      A.subtype A.subtype_injective (twoRes (⊤ : Subgroup ↥A)), hTA]
  have hffN : ffX N = (ffX ↥A).map A.subtype := by
    change twoPrimeRes (twoRes (⊤ : Subgroup N)) = (ffX ↥A).map A.subtype
    rw [htwoRes]
    exact ff_XOut_eq_map A
  rw [hffN, hmap1, htwoRes]

theorem ff6m_xTwoCore_of_surj_two_ker {B : Type} [Group B] (φ : N →* B)
    (hφ : Function.Surjective φ) (hk : IsPGroup 2 φ.ker) (hX : XTwoCore N) : XTwoCore B := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold XTwoCore at hX ⊢
  have hS : twoRes (⊤ : Subgroup B) = (twoRes (⊤ : Subgroup N)).map φ := by
    apply le_antisymm
    · unfold twoRes
      rw [Subgroup.closure_le]
      rintro b ⟨-, hbodd⟩
      obtain ⟨n, rfl⟩ := hφ b
      have hker : n ^ orderOf (φ n) ∈ φ.ker := by
        rw [MonoidHom.mem_ker, map_pow, pow_orderOf_eq_one]
      obtain ⟨s, hs⟩ := hk.exists_orderOf_eq_pow ⟨n ^ orderOf (φ n), hker⟩
      rw [Subgroup.orderOf_mk] at hs
      set t : N := n ^ (2 ^ s) with ht_def
      have htT : t ∈ twoRes (⊤ : Subgroup N) := by
        apply Subgroup.subset_closure
        refine ⟨trivial, ?_⟩
        refine Odd.of_dvd_nat hbodd (orderOf_dvd_of_pow_eq_one ?_)
        show t ^ orderOf (φ n) = 1
        have ht2 : t ^ orderOf (φ n) = (n ^ orderOf (φ n)) ^ (2 ^ s) := by
          rw [ht_def, ← pow_mul, Nat.mul_comm, pow_mul]
        rw [ht2, ← hs, pow_orderOf_eq_one]
      have hφt : φ t = (φ n) ^ (2 ^ s) := by rw [ht_def, map_pow]
      have hmem : (φ n) ∈ Subgroup.zpowers (φ t) := by
        rw [hφt]
        exact mem_zpowers_pow_iff.mpr ((Nat.coprime_two_left.mpr hbodd).pow_left s)
      exact (Subgroup.zpowers_le.mpr (Subgroup.mem_map.mpr ⟨t, htT, rfl⟩)) hmem
    · unfold twoRes
      rw [MonoidHom.map_closure]
      rw [Subgroup.closure_le]
      rintro b ⟨a, ⟨-, haodd⟩, rfl⟩
      exact Subgroup.subset_closure ⟨trivial, Odd.of_dvd_nat haodd (orderOf_map_dvd φ a)⟩
  have hXimg : ffX B = (ffX N).map φ := by
    unfold ffX
    rw [hS]
    apply le_antisymm
    · rw [twoPrimeRes]
      rw [Subgroup.closure_le]
      rintro y ⟨⟨t, htT, rfl⟩, k, hkord⟩
      apply Subgroup.mem_map.mpr
      refine ⟨t, ?_, rfl⟩
      apply Subgroup.subset_closure
      refine ⟨htT, ?_⟩
      have hker : t ^ (2 ^ k) ∈ φ.ker := by
        rw [MonoidHom.mem_ker, map_pow, ← hkord, pow_orderOf_eq_one]
      obtain ⟨s, hs⟩ := hk.exists_orderOf_eq_pow ⟨t ^ (2 ^ k), hker⟩
      rw [Subgroup.orderOf_mk] at hs
      have hdvd : orderOf t ∣ 2 ^ (k + s) := by
        apply orderOf_dvd_of_pow_eq_one
        show t ^ 2 ^ (k + s) = 1
        rw [show t ^ 2 ^ (k + s) = (t ^ 2 ^ k) ^ 2 ^ s by rw [← pow_mul, pow_add]]
        rw [← hs, pow_orderOf_eq_one]
      obtain ⟨l, -, hl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      exact ⟨l, hl⟩
    · rw [twoPrimeRes, MonoidHom.map_closure]
      rw [Subgroup.closure_le]
      rintro y ⟨t, ⟨htT, k, hkord⟩, rfl⟩
      obtain ⟨l, -, hl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
        (hkord ▸ orderOf_map_dvd φ t)
      exact Subgroup.subset_closure ⟨Subgroup.mem_map_of_mem φ htT, ⟨l, hl⟩⟩
  have hrange : ∀ t : ↥(twoRes (⊤ : Subgroup N)),
      φ (t : N) ∈ twoRes (⊤ : Subgroup B) := by
    intro t
    rw [hS]
    exact Subgroup.mem_map_of_mem φ t.2
  let ψ : ↥(twoRes (⊤ : Subgroup N)) →* ↥(twoRes (⊤ : Subgroup B)) :=
    (φ.comp (twoRes (⊤ : Subgroup N)).subtype).codRestrict _ hrange
  have hψsurj : Function.Surjective ψ := by
    intro x
    have hx : (x : B) ∈ (twoRes (⊤ : Subgroup N)).map φ := by
      rw [← hS]
      exact x.2
    obtain ⟨t, htT, htx⟩ := Subgroup.mem_map.mp hx
    exact ⟨⟨t, htT⟩, Subtype.ext htx⟩
  have hpCore_le : (CFSG.pCore 2 ↥(twoRes (⊤ : Subgroup N))).map ψ ≤
      CFSG.pCore 2 ↥(twoRes (⊤ : Subgroup B)) := by
    rw [show CFSG.pCore 2 ↥(twoRes (⊤ : Subgroup B)) =
        sSup {K : Subgroup ↥(twoRes (⊤ : Subgroup B)) | K.Normal ∧ IsPGroup 2 K} from rfl]
    exact le_sSup
      ⟨Subgroup.Normal.map (inferInstance) ψ hψsurj,
        IsPGroup.map (CFSG.pCore_isPGroup (p := 2) (G := ↥(twoRes (⊤ : Subgroup N))))
          ψ⟩
  have hforward : (CFSG.inSubgroup (CFSG.pCore 2) (twoRes (⊤ : Subgroup N))).map φ ≤
      CFSG.inSubgroup (CFSG.pCore 2) (twoRes (⊤ : Subgroup B)) := by
    have hmap : (CFSG.inSubgroup (CFSG.pCore 2) (twoRes (⊤ : Subgroup N))).map φ =
        ((CFSG.pCore 2 ↥(twoRes (⊤ : Subgroup N))).map ψ).map
          (twoRes (⊤ : Subgroup B)).subtype := by
      unfold CFSG.inSubgroup
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
    rw [hmap]
    exact Subgroup.map_mono hpCore_le
  have hreverse : CFSG.inSubgroup (CFSG.pCore 2) (twoRes (⊤ : Subgroup B)) ≤
      (CFSG.inSubgroup (CFSG.pCore 2) (twoRes (⊤ : Subgroup N))).map φ := by
    rw [← hX, ← hXimg]
    rintro x ⟨a, ha, rfl⟩
    unfold ffX
    rw [twoPrimeRes]
    obtain ⟨k, hk⟩ :=
      (CFSG.pCore_isPGroup (p := 2) (G := ↥(twoRes (⊤ : Subgroup B)))).exists_orderOf_eq_pow
        ⟨a, ha⟩
    refine Subgroup.subset_closure ⟨a.2, ⟨k, ?_⟩⟩
    change orderOf (a : B) = 2 ^ k
    rw [Subgroup.orderOf_coe]
    rwa [Subgroup.orderOf_mk] at hk
  rw [hXimg, hX]
  exact le_antisymm hforward hreverse

end Abstract

end CFSG.OddStandard.SmallF3.Omega
