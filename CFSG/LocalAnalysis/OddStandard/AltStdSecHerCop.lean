module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecStdAlt
public import CFSG.ClassicalInvolution.QuaternionStructure.OddCoreQuotient
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup

section Cop

variable {H : Type*} [Group H]

theorem exists_sq_root_inverted {t p : H} (hp : Odd (orderOf p)) (hinv : t * p * t⁻¹ = p⁻¹) :
    ∃ r ∈ zpowers p, r * r = p ∧ t * r * t⁻¹ = r⁻¹ := by
  obtain ⟨j, hj⟩ := hp
  refine ⟨p ^ (j + 1), Subgroup.pow_mem _ (mem_zpowers p) _, ?_, ?_⟩
  · rw [← pow_add, show j + 1 + (j + 1) = orderOf p + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  · have : t * p ^ (j + 1) * t⁻¹ = (t * p * t⁻¹) ^ (j + 1) := by
      simp
    rw [this, hinv, inv_pow]

theorem exists_mul_mem_centralizer {P : Subgroup H} (hP : ∀ x ∈ P, Odd (orderOf x)) {t : H}
    (ht : t * t = 1) {h : H} (hmem : h * t * h⁻¹ * t⁻¹ ∈ P) :
    ∃ p ∈ P, p * h ∈ centralizer ({t} : Set H) := by
  have ht1 : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  set p₁ := h * t * h⁻¹ * t⁻¹ with hp₁
  have hu : h * t * h⁻¹ = p₁ * t := by rw [hp₁]; group
  have hinv : t * p₁ * t⁻¹ = p₁⁻¹ := by
    have h1 : (p₁ * t) * (p₁ * t) = 1 := by
      rw [← hu]
      calc h * t * h⁻¹ * (h * t * h⁻¹) = h * (t * t) * h⁻¹ := by group
        _ = 1 := by rw [ht]; group
    have h2 : t * p₁ * t = p₁⁻¹ := by
      have : p₁ * (t * p₁ * t) = 1 := by rw [← h1]; group
      exact (eq_inv_of_mul_eq_one_right this)
    rw [ht1]
    exact h2
  obtain ⟨r, hr, hrr, htr⟩ := exists_sq_root_inverted (hP p₁ hmem) hinv
  have hrP : r ∈ P := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hr
    exact Subgroup.zpow_mem _ hmem k
  have htr' : t * r⁻¹ = r * t := by
    have h3 : t * r⁻¹ * t⁻¹ = r := by
      have := congrArg (fun w => w⁻¹) htr
      simpa [mul_assoc] using this
    calc t * r⁻¹ = (t * r⁻¹ * t⁻¹) * t := by group
      _ = r * t := by rw [h3]
  have hu' : h * t * h⁻¹ = r * t * r⁻¹ := by
    rw [hu]
    calc p₁ * t = (r * r) * t := by rw [hrr]
      _ = r * (r * t) := by group
      _ = r * (t * r⁻¹) := by rw [htr']
      _ = r * t * r⁻¹ := by group
  refine ⟨r⁻¹, inv_mem hrP, ?_⟩
  rw [mem_centralizer_singleton_iff]
  calc r⁻¹ * h * t = r⁻¹ * (h * t * h⁻¹) * h := by group
    _ = r⁻¹ * (r * t * r⁻¹) * h := by rw [hu']
    _ = t * (r⁻¹ * h) := by group

theorem exists_centralizer_preimage {P : Subgroup H} [P.Normal] (hP : ∀ x ∈ P, Odd (orderOf x))
    {t : H} (ht : t * t = 1) {x : H ⧸ P}
    (hx : x ∈ centralizer ({(t : H ⧸ P)} : Set (H ⧸ P))) :
    ∃ c ∈ centralizer ({t} : Set H), (c : H ⧸ P) = x := by
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
  rw [mem_centralizer_singleton_iff] at hx
  have hmem : h * t * h⁻¹ * t⁻¹ ∈ P := by
    rw [← QuotientGroup.eq_one_iff]
    have : ((h * t * h⁻¹ * t⁻¹ : H) : H ⧸ P) = (h : H ⧸ P) * t * (h : H ⧸ P)⁻¹ * (t : H ⧸ P)⁻¹ := by
      simp
    rw [this, hx]
    group
  obtain ⟨p, hpP, hpc⟩ := exists_mul_mem_centralizer hP ht hmem
  refine ⟨p * h, hpc, ?_⟩
  have : (p : H ⧸ P) = 1 := (QuotientGroup.eq_one_iff p).2 hpP
  simp [this]

end Cop

section OddCore

variable {H : Type*} [Group H] [Finite H]

theorem orderOf_odd_of_mem_oddCore {x : H} (hx : x ∈ CFSG.oddCore H) : Odd (orderOf x) :=
  (ClassicalInvolution.QuaternionStructure.odd_natCard_oddCore H).of_dvd_nat
    (Subgroup.orderOf_dvd_natCard _ hx)

theorem inf_oddCore_eq_bot_of_alt {B : Subgroup H} {m : ℕ} (hm : 5 ≤ m)
    (e : B ≃* alternatingGroup (Fin m)) : B ⊓ CFSG.oddCore H = ⊥ := by
  have hsimple : IsSimpleGroup B := isSimpleGroup_of_alt hm e
  have hnormal : ((B ⊓ CFSG.oddCore H).subgroupOf B).Normal := by
    refine ⟨fun n hn b => ?_⟩
    have hn' : (n : H) ∈ B ⊓ CFSG.oddCore H := hn
    obtain ⟨hnB, hnO⟩ := Subgroup.mem_inf.1 hn'
    exact Subgroup.mem_inf.2 ⟨mul_mem (mul_mem b.2 hnB) (inv_mem b.2),
      (inferInstance : (CFSG.oddCore H).Normal).conj_mem _ hnO _⟩
  rcases hsimple.eq_bot_or_eq_top_of_normal ((B ⊓ CFSG.oddCore H).subgroupOf B) with hD | hD
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxB, hxO⟩ := Subgroup.mem_inf.1 hx
    have : (⟨x, hxB⟩ : B) ∈ (B ⊓ CFSG.oddCore H).subgroupOf B := hx
    rw [hD] at this
    have h1 : (⟨x, hxB⟩ : B) = 1 := this
    simpa using congrArg Subtype.val h1
  · exfalso
    obtain ⟨x, -, -, -, hx2, -⟩ := exists_two_involutions_of_alt (by omega) e
    have hxO : (x : H) ∈ CFSG.oddCore H := by
      have : x ∈ (B ⊓ CFSG.oddCore H).subgroupOf B := by rw [hD]; trivial
      exact (Subgroup.mem_inf.1 this).2
    have h1 := orderOf_odd_of_mem_oddCore hxO
    rw [Subgroup.orderOf_coe, hx2] at h1
    exact (Nat.not_odd_iff_even.2 even_two) h1

end OddCore

end CFSG.OddStandard.AltStdSec
