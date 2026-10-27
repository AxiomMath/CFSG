module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutCover
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutLayer

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

@[expose] def conjAut (Y : Subgroup G) {s : G} (hs : s * s = 1)
    (hsN : s ∈ normalizer (Y : Set G)) : MulAut ↥Y where
  toFun y := ⟨s * y * s⁻¹, (hsN y).mp y.2⟩
  invFun y := ⟨s * y * s⁻¹, (hsN y).mp y.2⟩
  left_inv y := by
    have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
    apply Subtype.ext
    change s * (s * (y : G) * s⁻¹) * s⁻¹ = y
    rw [hsi]
    calc s * (s * (y : G) * s) * s = (s * s) * (y : G) * (s * s) := by group
      _ = y := by rw [hs]; group
  right_inv y := by
    have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
    apply Subtype.ext
    change s * (s * (y : G) * s⁻¹) * s⁻¹ = y
    rw [hsi]
    calc s * (s * (y : G) * s) * s = (s * s) * (y : G) * (s * s) := by group
      _ = y := by rw [hs]; group
  map_mul' a b := Subtype.ext (by
    change s * ((a : G) * (b : G)) * s⁻¹ = (s * (a : G) * s⁻¹) * (s * (b : G) * s⁻¹)
    group)

theorem coe_conjAut (Y : Subgroup G) {s : G} (hs : s * s = 1)
    (hsN : s ∈ normalizer (Y : Set G)) (y : ↥Y) :
    ((conjAut Y hs hsN y : ↥Y) : G) = s * y * s⁻¹ := rfl

theorem conjAut_mul_self (Y : Subgroup G) {s : G} (hs : s * s = 1)
    (hsN : s ∈ normalizer (Y : Set G)) : conjAut Y hs hsN * conjAut Y hs hsN = 1 := by
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  ext y
  change s * (s * (y : G) * s⁻¹) * s⁻¹ = y
  rw [hsi]
  calc s * (s * (y : G) * s) * s = (s * s) * (y : G) * (s * s) := by group
    _ = y := by rw [hs]; group

theorem mem_fixSub_conjAut_iff (Y : Subgroup G) {s : G} (hs : s * s = 1)
    (hsN : s ∈ normalizer (Y : Set G)) (p : ↥Y) :
    p ∈ fixSub (conjAut Y hs hsN) ↔ s * (p : G) = (p : G) * s := by
  rw [mem_fixSub_iff]
  constructor
  · intro h
    exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext (mul_inv_eq_iff_eq_mul.mpr h)

@[expose] def fixConjEquiv (Y : Subgroup G) {s : G} (hs : s * s = 1)
    (hsN : s ∈ normalizer (Y : Set G)) :
    ↥(fixSub (conjAut Y hs hsN)) ≃* ↥(Y ⊓ centralizer ({s} : Set G)) where
  toFun p := ⟨((p : ↥Y) : G), p.1.2, Subgroup.mem_centralizer_singleton_iff.mpr
    ((mem_fixSub_conjAut_iff Y hs hsN p.1).mp p.2).symm⟩
  invFun q := ⟨⟨(q : G), q.2.1⟩, (mem_fixSub_conjAut_iff Y hs hsN ⟨(q : G), q.2.1⟩).mpr
    (Subgroup.mem_centralizer_singleton_iff.mp (show (q : G) ∈ centralizer ({s} : Set G) from
      q.2.2)).symm⟩
  left_inv p := rfl
  right_inv q := rfl
  map_mul' a b := rfl

theorem exists_outer_of_outerData (Y : Subgroup G) {P : Type} [Group P] (ρ : ↥Y →* P)
    (hρ : OddCentralCover ρ) {s : G} (hs : s * s = 1) (hsN : s ∈ normalizer (Y : Set G))
    (α : MulAut P) (hα : ∀ y : ↥Y, ρ (conjAut Y hs hsN y) = α (ρ y)) (hdata : OuterData P α) :
    ∃ u : G, u ∈ CFSG.inSubgroup CFSG.layer (Y ⊓ centralizer ({s} : Set G)) ∧ orderOf u = 2 ∧
      ∃ a ∈ Y, a⁻¹ * s * a = u * s := by
  set σ : MulAut ↥Y := conjAut Y hs hsN with hσdef
  have hσ2 : σ * σ = 1 := conjAut_mul_self Y hs hsN
  have hcov := hρ.oddCentralCover_fixHom hσ2 hα
  obtain ⟨a₀, u₀, hu₀u₀, hu₀1, hu₀L, ha₀⟩ := hdata
  obtain ⟨uF, huF, rfl⟩ := hu₀L
  have huFF : uF * uF = 1 := Subtype.ext hu₀u₀
  obtain ⟨û, hûL, hûû, hûF⟩ := hcov.exists_involution_layer_lift huF huFF
  have hρû : ρ ((û : ↥Y)) = (uF : P) := congrArg Subtype.val hûF
  have hûσ : σ (û : ↥Y) = û := û.2
  have hûû' : (û : ↥Y) * û = 1 := congrArg Subtype.val hûû
  have hû1 : (û : ↥Y) ≠ 1 := by
    intro h1
    rw [h1, map_one] at hρû
    exact hu₀1 hρû.symm
  obtain ⟨b, hb⟩ := hρ.surjective a₀
  obtain ⟨t, htdef⟩ : ∃ t : ↥Y, t = b⁻¹ * σ b := ⟨_, rfl⟩
  have hρt : ρ t = (uF : P) := by
    rw [htdef, map_mul, map_inv, hα, hb]
    exact ha₀
  obtain ⟨n, hndef⟩ : ∃ n : ↥Y, n = (û : ↥Y)⁻¹ * t := ⟨_, rfl⟩
  have hn : n ∈ ρ.ker := by
    rw [hndef, MonoidHom.mem_ker, map_mul, map_inv, hρû, hρt, inv_mul_cancel]
  have hnc : n ∈ center ↥Y := hρ.ker_le_center hn
  have hσt : σ t = t⁻¹ := by
    rw [htdef, map_mul, map_inv, aut_apply_apply hσ2, mul_inv_rev, inv_inv]
  have hûi : (û : ↥Y)⁻¹ = û := inv_eq_of_mul_eq_one_right hûû'
  have htn : t = (û : ↥Y) * n := by rw [hndef, hûi, ← mul_assoc, hûû', one_mul]
  have hût : (û : ↥Y) * t = t * û := by
    have hc := Subgroup.mem_center_iff.mp hnc (û : ↥Y)
    calc (û : ↥Y) * t = û * (û * n) := by rw [← htn]
      _ = û * (n * û) := by rw [hc]
      _ = (û * n) * û := by rw [mul_assoc]
      _ = t * û := by rw [← htn]
  have hσn : σ n = n⁻¹ := by
    have h1 : σ n = (û : ↥Y) * t⁻¹ := by
      rw [hndef, map_mul, map_inv, hûσ, hσt, hûi]
    have h2 : n⁻¹ = t⁻¹ * û := by
      rw [hndef, mul_inv_rev, inv_inv]
    rw [h1, h2]
    calc (û : ↥Y) * t⁻¹ = t⁻¹ * (t * û) * t⁻¹ := by group
      _ = t⁻¹ * (û * t) * t⁻¹ := by rw [hût]
      _ = t⁻¹ * û := by group
  obtain ⟨k, hk⟩ := hρ.exists_sqrt hn
  obtain ⟨m, hmdef⟩ : ∃ m : ↥Y, m = n ^ k := ⟨_, rfl⟩
  have hmk : m ∈ ρ.ker := by rw [hmdef]; exact Subgroup.pow_mem _ hn k
  have hmc : m ∈ center ↥Y := hρ.ker_le_center hmk
  have hσm : σ m = m⁻¹ := by rw [hmdef, map_pow, hσn, inv_pow]
  have hmm : m * m = n := by rw [hmdef]; exact hk
  have hkey : (b * m)⁻¹ * σ (b * m) = (û : ↥Y) := by
    have hcomm : ∀ z : ↥Y, m * z = z * m := fun z => (Subgroup.mem_center_iff.mp hmc z).symm
    have hmi : m⁻¹ * t = t * m⁻¹ := by
      calc m⁻¹ * t = m⁻¹ * (t * m) * m⁻¹ := by group
        _ = m⁻¹ * (m * t) * m⁻¹ := by rw [hcomm t]
        _ = t * m⁻¹ := by group
    calc (b * m)⁻¹ * σ (b * m) = m⁻¹ * (b⁻¹ * σ b) * σ m := by rw [map_mul]; group
      _ = m⁻¹ * t * m⁻¹ := by rw [← htdef, hσm]
      _ = t * (m * m)⁻¹ := by rw [hmi]; group
      _ = t * n⁻¹ := by rw [hmm]
      _ = (û : ↥Y) := by rw [hndef, mul_inv_rev, inv_inv]; group
  refine ⟨((û : ↥Y) : G), ?_, ?_, ((b * m : ↥Y) : G), (b * m).2, ?_⟩
  · have h1 := CFSG.WholeGroup.layer_map_mulEquiv (fixConjEquiv Y hs hsN)
    have h2 : fixConjEquiv Y hs hsN û ∈
        CFSG.layer ↥(Y ⊓ centralizer ({s} : Set G)) := by
      rw [← h1]
      exact ⟨û, hûL, rfl⟩
    exact ⟨_, h2, rfl⟩
  · have hu1 : ((û : ↥Y) : G) ≠ 1 := fun h => hû1 (Subtype.ext h)
    have hu2 : ((û : ↥Y) : G) ^ 2 = 1 := by
      rw [pow_two, ← Subgroup.coe_mul, hûû']
      rfl
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime hu2 hu1
  · have h1 := congrArg Subtype.val hkey
    have h2 : ((((b * m)⁻¹ * σ (b * m) : ↥Y)) : G) =
        ((b * m : ↥Y) : G)⁻¹ * (s * ((b * m : ↥Y) : G) * s⁻¹) := rfl
    rw [h2] at h1
    calc ((b * m : ↥Y) : G)⁻¹ * s * ((b * m : ↥Y) : G) =
        (((b * m : ↥Y) : G)⁻¹ * (s * ((b * m : ↥Y) : G) * s⁻¹)) * s := by group
      _ = ((û : ↥Y) : G) * s := by rw [h1]

end CFSG.OddStandard.SmallF3.Omega
