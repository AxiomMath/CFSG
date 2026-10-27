module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step37Syl

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.Sporadic.SuzOddCore

namespace Sec3

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G}
  {x : G} {Zs P T Q B₀ : Subgroup G} {z y : G}

theorem mem_centralizer_sec3B_of_odd
    (hS : Sec3Suz G A A₁ R g E F x Zs P T Q B₀ z y) {w : G}
    (hwB : w ∈ normalizer (sec3B A₁ x : Set G)) (hwQ : w ∈ centralizer (Q : Set G))
    (hw : Odd (orderOf w)) : w ∈ centralizer (sec3B A₁ x : Set G) := by
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
  have hwm : (⟨w, hwB⟩ : normalizer (sec3B A₁ x : Set G)) ^ orderOf w = 1 :=
    Subtype.ext (by rw [SubgroupClass.coe_pow]; exact pow_orderOf_eq_one w)
  have hpow : (c⁻¹ * (ψ ⟨w, hwB⟩ : Equiv.Perm (Fin 1782)) * c) ^ orderOf w = 1 := by
    have h1 : c⁻¹ * (ψ ⟨w, hwB⟩ : Equiv.Perm (Fin 1782)) * c =
        MulAut.conj c⁻¹ (ψ ⟨w, hwB⟩ : Equiv.Perm (Fin 1782)) := by
      rw [MulAut.conj_apply, inv_inv]
    rw [h1, ← map_pow, ← SubgroupClass.coe_pow, ← map_pow, hwm, map_one, OneMemClass.coe_one,
      map_one]
  have h2 : orderOf (c⁻¹ * (ψ ⟨w, hwB⟩ : Equiv.Perm (Fin 1782)) * c) ∣ 2 := by
    rw [← orderOf_suzInv (i := 1) (by norm_num)]
    exact orderOf_dvd_of_mem_zpowers hg
  have h3 := orderOf_dvd_of_pow_eq_one hpow
  have hcop : Nat.Coprime 2 (orderOf w) := Nat.coprime_two_left.mpr hw
  have h1 : c⁻¹ * (ψ ⟨w, hwB⟩ : Equiv.Perm (Fin 1782)) * c = 1 :=
    orderOf_eq_one_iff.mp (Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd h2 h3))
  have hψ1 : ψ ⟨w, hwB⟩ = 1 := by
    apply Subtype.ext
    rw [OneMemClass.coe_one]
    calc (ψ ⟨w, hwB⟩ : Equiv.Perm (Fin 1782)) =
        c * (c⁻¹ * (ψ ⟨w, hwB⟩ : Equiv.Perm (Fin 1782)) * c) * c⁻¹ := by group
      _ = 1 := by rw [h1]; group
  exact (hψk _).mp hψ1

theorem mem_normalizer_sec3B_of_conj
    (hS : Sec3Suz G A A₁ R g E F x Zs P T Q B₀ z y) {h : G}
    (hh : ∀ b ∈ sec3B A₁ x, h * b * h⁻¹ ∈ centralizer ({x} : Set G)) {w : G}
    (hwB : w ∈ sec3B A₁ x) (hwh : h * w * h⁻¹ = w) (hwZ : w ∉ centerIn (sec3B A₁ x)) :
    h ∈ normalizer (sec3B A₁ x : Set G) := by
  set B := sec3B A₁ x with hBdef
  set N₀ : Subgroup G := B ⊓ B.comap (MulAut.conj h).toMonoidHom with hN₀def
  have hmem : ∀ b : G, b ∈ N₀ ↔ b ∈ B ∧ h * b * h⁻¹ ∈ B := fun b => by
    rw [hN₀def, mem_inf, mem_comap]
    rfl
  have hN₀n : (N₀.subgroupOf B).Normal := by
    refine ⟨fun a ha c => mem_subgroupOf.mpr ?_⟩
    have ha' := (hmem a).mp (mem_subgroupOf.mp ha)
    have hcN : h * (c : G) * h⁻¹ ∈ normalizer (B : Set G) :=
      centralizer_le_normalizer_sec3B A₁ x (hh c c.2)
    refine (hmem _).mpr ⟨mul_mem (mul_mem c.2 ha'.1) (inv_mem c.2), ?_⟩
    have e : h * ((c : G) * a * (c : G)⁻¹) * h⁻¹ =
        (h * (c : G) * h⁻¹) * (h * a * h⁻¹) * (h * (c : G) * h⁻¹)⁻¹ := by group
    show h * ((c : G) * a * (c : G)⁻¹) * h⁻¹ ∈ B
    rw [e]
    exact (mem_normalizer_iff.mp hcN _).mp ha'.2
  have hq := isQuasisimple_sec3B hS.B_perf hS.B_suz
  rcases le_center_or_eq_top_of_perfect hq.1 hq.2 (N₀.subgroupOf B) with hc | ht
  ·
    exfalso
    apply hwZ
    have hwN : (⟨w, hwB⟩ : B) ∈ N₀.subgroupOf B :=
      mem_subgroupOf.mpr ((hmem w).mpr ⟨hwB, by rw [hwh]; exact hwB⟩)
    rw [← map_center_eq_centerIn]
    exact ⟨_, hc hwN, rfl⟩
  · refine AS76b.mem_normalizer_of_map_conj_le ?_
    rintro _ ⟨b, hb, rfl⟩
    have hb' : (⟨b, hb⟩ : B) ∈ N₀.subgroupOf B := by
      rw [ht]
      exact mem_top _
    exact ((hmem b).mp (mem_subgroupOf.mp hb')).2

end Sec3

end CFSG.ComponentClassification.AS81
