module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step37Syl
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step38Tau

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.Sporadic.SuzOddCore Sec3

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G}
  {x : G} {Zs P T Q B₀ : Subgroup G} {z y : G}

theorem centQCommX_of
    (hS : Sec3Suz G A A₁ R g E F x Zs P T Q B₀ z y) : CentQCommX A₁ Q x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKB : sec3B A₁ x ⊓ centralizer ({z} : Set G) ≤ sec3B A₁ x := inf_le_left
  obtain ⟨e₀⟩ := hS.B_suz
  obtain ⟨c, hcT, π, hπs, hπk, hπe⟩ := exists_hom_invE hS e₀
  have hQ₁8 : IsQ8Cube (SuzB0.coord_qVec.Q.subgroupOf (invE 1)) := by
    rw [← isQ8Cube_map_iff (invE 1).subtype (invE 1).subtype_injective, subgroupOf_map_subtype,
      inf_eq_left.mpr SuzB0.Q_le_invE]
    exact SuzB0.coord_qVec.isQ8Cube SuzB0.b0_parts.2.2.2.2.2.2
  have hQ₁n : (SuzB0.coord_qVec.Q.subgroupOf (invE 1)).Normal :=
    ⟨fun a ha w => mem_subgroupOf.mpr
      ((mem_normalizer_iff.mp (SuzB0.invE_le w.2).1 a).mp (mem_subgroupOf.mp ha))⟩
  have hCcard : Nat.card ↥(invE 1) = 3317760 := by
    rw [card_invE (by norm_num)]
    rfl
  obtain ⟨L, -, -, -, hQL, hLQ⟩ := exists_lift_eq_Q hS hQ₁8 hQ₁n hCcard rfl hπs hπk
  have hQ₁Q : ∀ q ∈ SuzB0.coord_qVec.Q, ∃ k : ↥(sec3B A₁ x ⊓ centralizer ({z} : Set G)),
      (k : G) ∈ Q ∧ (π k : Equiv.Perm (Fin 1782)) = q := by
    intro q hq
    obtain ⟨a, ha⟩ := hπs ⟨q, SuzB0.Q_le_invE hq⟩
    obtain ⟨l, hl, m, hm, rfl⟩ := hQL a (by rw [ha]; exact mem_subgroupOf.mpr hq)
    refine ⟨l, by rw [← hLQ]; exact mem_map_of_mem _ hl, ?_⟩
    rw [map_mul, MonoidHom.mem_ker.mp hm, mul_one] at ha
    rw [ha]
  obtain ⟨ψ, hψ, hψk⟩ := exists_suzT_hom hS.B_perf (e₀.trans suzEquivM)
  intro w hwB hwQ
  have hg : c⁻¹ * (ψ ⟨w, hwB⟩ : Equiv.Perm (Fin 1782)) * c ∈ zpowers (suzInv 1) := by
    refine SuzB0.mem_zpowers_of_mem_centralizer_Q
      (mul_mem (mul_mem (inv_mem hcT) (ψ _).2) hcT) (mem_centralizer_iff.mpr fun q hq => ?_)
    obtain ⟨k, hkQ, hkq⟩ := hQ₁Q q hq
    have hkB : (k : G) ∈ sec3B A₁ x := hKB k.2
    set u := (ψ ⟨k, le_normalizer hkB⟩ : Equiv.Perm (Fin 1782)) with hu
    set v := (ψ ⟨w, hwB⟩ : Equiv.Perm (Fin 1782)) with hv
    have hq : q = c⁻¹ * u * c := by
      rw [← hkq, hπe k, hu, hψ k hkB]
      rfl
    have huv : v * u = u * v := by
      have hwk : (⟨w, hwB⟩ : normalizer (sec3B A₁ x : Set G)) * ⟨k, le_normalizer hkB⟩ =
          ⟨k, le_normalizer hkB⟩ * ⟨w, hwB⟩ :=
        Subtype.ext (mem_centralizer_iff.mp hwQ k hkQ).symm
      rw [hu, hv, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hwk]
    rw [hq]
    calc c⁻¹ * u * c * (c⁻¹ * v * c) = c⁻¹ * (u * v) * c := by group
      _ = c⁻¹ * (v * u) * c := by rw [huv]
      _ = c⁻¹ * v * c * (c⁻¹ * u * c) := by group
  have ht₁ : suzInv 1 ∈ invE 1 := SuzB0.Q_le_invE SuzB0.coord_qVec.t_mem
  obtain ⟨k₁, hk₁⟩ := hπs ⟨suzInv 1, ht₁⟩
  have hk₁B : (k₁ : G) ∈ sec3B A₁ x := hKB k₁.2
  have hk₁t : c⁻¹ * (ψ ⟨k₁, le_normalizer hk₁B⟩ : Equiv.Perm (Fin 1782)) * c = suzInv 1 := by
    have h1 : ((π k₁ : ↥(invE 1)) : Equiv.Perm (Fin 1782)) = suzInv 1 := congrArg Subtype.val hk₁
    rw [hπe k₁] at h1
    rw [← h1, hψ k₁ hk₁B]
    rfl
  obtain ⟨m, hm⟩ := mem_zpowers_iff.mp hg
  have hψeq : ψ ⟨w, hwB⟩ =
      ψ ((⟨k₁, le_normalizer hk₁B⟩ : normalizer (sec3B A₁ x : Set G)) ^ m) := by
    apply Subtype.ext
    rw [map_zpow, SubgroupClass.coe_zpow]
    have h1 : (MulAut.conj c⁻¹) (ψ ⟨w, hwB⟩ : Equiv.Perm (Fin 1782)) =
        (MulAut.conj c⁻¹) ((ψ ⟨k₁, le_normalizer hk₁B⟩ : Equiv.Perm (Fin 1782)) ^ m) := by
      rw [map_zpow, MulAut.conj_apply, MulAut.conj_apply, inv_inv, hk₁t, hm]
    exact (MulAut.conj c⁻¹).injective h1
  have hker : ψ ((⟨w, hwB⟩ : normalizer (sec3B A₁ x : Set G)) *
      ((⟨k₁, le_normalizer hk₁B⟩ : normalizer (sec3B A₁ x : Set G)) ^ m)⁻¹) = 1 := by
    rw [map_mul, map_inv, hψeq, mul_inv_cancel]
  have hC := (hψk _).mp hker
  have hxZ : x ∈ centerIn (sec3B A₁ x) := by
    rw [hS.B_center]
    exact mem_zpowers x
  have hxB : x ∈ sec3B A₁ x := (mem_inf.mp hxZ).1
  have hkm : (k₁ : G) ^ m ∈ sec3B A₁ x := zpow_mem hk₁B m
  have h1 : x * (w * ((k₁ : G) ^ m)⁻¹) = (w * ((k₁ : G) ^ m)⁻¹) * x := by
    have := mem_centralizer_iff.mp hC x hxB
    simpa using this
  have h2 : (k₁ : G) ^ m * x = x * (k₁ : G) ^ m :=
    mem_centralizer_iff.mp (mem_inf.mp hxZ).2 _ hkm
  calc w * x = (w * ((k₁ : G) ^ m)⁻¹) * ((k₁ : G) ^ m * x) := by group
    _ = (w * ((k₁ : G) ^ m)⁻¹) * (x * (k₁ : G) ^ m) := by rw [h2]
    _ = ((w * ((k₁ : G) ^ m)⁻¹) * x) * (k₁ : G) ^ m := by group
    _ = (x * (w * ((k₁ : G) ^ m)⁻¹)) * (k₁ : G) ^ m := by rw [h1]
    _ = x * w := by group

end CFSG.ComponentClassification.AS81
