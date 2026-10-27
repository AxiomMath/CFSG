module

public import CFSG.ClassicalInvolution.Asc77.AscFusionS4
import CFSG.ClassicalInvolution.Uniform.U4Basic
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Tight

public section

namespace CFSG.ClassicalInvolution.A7Core

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Hat2A7
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

variable {F : Type} [Group F] [Finite F]

theorem isUniqueInvolution {K : Subgroup F} {z : F} (hK : IsClassical2A7 ⊤ K z) :
    IsUniqueInvolution K z where
  mem := hK.mem
  ne_one := by
    intro h
    have h2 := hK.orderOf_eq_two
    rw [h, orderOf_one] at h2
    omega
  sq := hK.mul_self
  unique := by
    intro y hy hy2
    by_cases h1 : y = 1
    · exact Or.inl h1
    · exact Or.inr (hK.eq_of_orderOf_eq_two hy (orderOf_eq_prime (by rw [pow_two]; exact hy2) h1))

omit [Finite F] in
theorem classical_conjSub {K : Subgroup F} {z : F} (hK : IsClassical2A7 ⊤ K z) (g : F) :
    IsClassical2A7 ⊤ (conjSub g K) (g * z * g⁻¹) := by
  have h1 := hK.conj g
  rwa [Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective] at h1

omit [Finite F] in
theorem classical_conjSub_of_commute {K : Subgroup F} {z c : F} (hK : IsClassical2A7 ⊤ K z)
    (hc : c * z = z * c) : IsClassical2A7 ⊤ (conjSub c K) z := by
  have h1 := classical_conjSub hK c
  have h2 : c * z * c⁻¹ = z := by rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  rwa [h2] at h1

omit [Finite F] in
theorem isSubnormal_centralizer {K : Subgroup F} {z : F} (hK : IsClassical2A7 ⊤ K z) :
    IsSubnormal K (Subgroup.centralizer ({z} : Set F)) := by
  have h1 := hK.subnormal
  rwa [top_inf_eq] at h1

theorem isTwoComponent {K : Subgroup F} {z : F} (hK : IsClassical2A7 ⊤ K z) :
    CFSG.ComponentClassification.TwoComponents.IsTwoComponent
      (K.subgroupOf (Subgroup.centralizer ({z} : Set F))) :=
  isTwoComponent_subgroupOf_of_perfect (isSubnormal_centralizer hK)
    hK.perfect.commutator_eq_top hK.witness.1

theorem twin_facts {K₁ K₂ : Subgroup F} {z : F} (h₁ : IsClassical2A7 ⊤ K₁ z)
    (h₂ : IsClassical2A7 ⊤ K₂ z) (hne : K₁ ≠ K₂) :
    K₂ ≤ Subgroup.normalizer (K₁ : Set F) ∧ K₁ ≤ Subgroup.normalizer (K₂ : Set F) ∧
      ⁅K₁, K₂⁆ ≤ oddCoreOf K₁ ⊓ oddCoreOf K₂ := by
  obtain ⟨a, b, c, -⟩ := twoComponents_interaction h₁.le_centralizer h₂.le_centralizer
    (isTwoComponent h₁) (isTwoComponent h₂) hne
  exact ⟨a, b, c⟩

theorem commutator_mem_of_twin {K₁ K₂ : Subgroup F} {z : F} (h₁ : IsClassical2A7 ⊤ K₁ z)
    (h₂ : IsClassical2A7 ⊤ K₂ z) (hne : K₁ ≠ K₂) {x : F} (hx : x ∈ K₂) :
    ∀ u ∈ K₁, ⁅x, u⁆ ∈ oddCoreOf K₁ := by
  intro u hu
  obtain ⟨-, -, hc⟩ := twin_facts h₁ h₂ hne
  rw [← commutatorElement_inv]
  exact (oddCoreOf K₁).inv_mem (hc (Subgroup.commutator_mem_commutator hu hx)).1

omit [Finite F] in
theorem mk_mem_center {K : Subgroup F} {z : F} (hK : IsClassical2A7 ⊤ K z) :
    (QuotientGroup.mk (⟨z, hK.mem⟩ : ↥K) : OddQuot K) ∈ Subgroup.center (OddQuot K) := by
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (hK.mul_comm_of_mem x.2)

theorem mk_ne_one {K : Subgroup F} {z : F} (hK : IsClassical2A7 ⊤ K z) :
    (QuotientGroup.mk (⟨z, hK.mem⟩ : ↥K) : OddQuot K) ≠ 1 := by
  intro h
  rw [QuotientGroup.eq_one_iff] at h
  have hz1 : z ≠ 1 := by
    intro h1
    have h2 := hK.orderOf_eq_two
    rw [h1, orderOf_one] at h2
    omega
  exact hz1 (eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K)
    (mem_oddCoreOf_iff.mpr ⟨hK.mem, h⟩) (isPGroup_zpowers_of_mul_self_eq_one hK.mul_self hz1))

theorem mem_center_oddQuot_iff {K : Subgroup F} {z : F} (hK : IsClassical2A7 ⊤ K z)
    (w : OddQuot K) : w ∈ Subgroup.center (OddQuot K) ↔
      w = 1 ∨ w = (QuotientGroup.mk (⟨z, hK.mem⟩ : ↥K) : OddQuot K) := by
  obtain ⟨π, z', -, hcen⟩ := exists_cover_of_witness hK.witness
  have hz' : (QuotientGroup.mk (⟨z, hK.mem⟩ : ↥K) : OddQuot K) = z' :=
    ((hcen _).mp (mk_mem_center hK)).resolve_left (mk_ne_one hK)
  rw [hz']
  exact hcen w

omit [Finite F] in
theorem mk_mem_center_of_forall {K : Subgroup F} {a : F} (haK : a ∈ K)
    (h : ∀ u ∈ K, ⁅a, u⁆ ∈ oddCoreOf K) :
    (QuotientGroup.mk (⟨a, haK⟩ : ↥K) : OddQuot K) ∈ Subgroup.center (OddQuot K) :=
  CFSG.ClassicalInvolution.Uniform.U4.mk_mem_center_of_forall haK h

theorem eq_one_or_eq_of_forall_comm {K : Subgroup F} {z : F} (hK : IsClassical2A7 ⊤ K z) {a : F}
    (haK : a ∈ K) (ha2 : IsPGroup 2 (Subgroup.zpowers a)) (h : ∀ u ∈ K, ⁅a, u⁆ ∈ oddCoreOf K) :
    a = 1 ∨ a = z := by
  rcases (mem_center_oddQuot_iff hK _).mp (mk_mem_center_of_forall haK h) with h1 | h1
  · left
    rw [QuotientGroup.eq_one_iff] at h1
    exact eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K)
      (mem_oddCoreOf_iff.mpr ⟨haK, h1⟩) ha2
  · right
    rw [QuotientGroup.eq] at h1
    have hza : a * z = z * a := hK.mul_comm_of_mem haK
    have hz2 : IsPGroup 2 (Subgroup.zpowers z) := by
      by_cases hz1 : z = 1
      · rw [hz1, Subgroup.zpowers_one_eq_bot]
        exact IsPGroup.of_bot
      · exact isPGroup_zpowers_of_mul_self_eq_one hK.mul_self hz1
    have hainv : IsPGroup 2 (Subgroup.zpowers a⁻¹) := by rwa [Subgroup.zpowers_inv]
    have hcomm : Commute a⁻¹ z := (Commute.inv_left (show Commute a z from hza))
    have hmem : a⁻¹ * z ∈ oddCoreOf K :=
      mem_oddCoreOf_iff.mpr ⟨K.mul_mem (K.inv_mem haK) hK.mem, h1⟩
    have h2 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K) hmem
      (isPGroup_zpowers_mul hcomm hainv hz2)
    exact (inv_mul_eq_one.mp h2)

theorem not_forall_comm_of_sq_eq {K : Subgroup F} {z : F} (hK : IsClassical2A7 ⊤ K z) {a : F}
    (haK : a ∈ K) (ha2 : a * a = z) : ¬ ∀ u ∈ K, ⁅a, u⁆ ∈ oddCoreOf K := by
  intro h
  have hz1 : z ≠ 1 := by
    intro h1
    have h2 := hK.orderOf_eq_two
    rw [h1, orderOf_one] at h2
    omega
  rcases eq_one_or_eq_of_forall_comm hK haK
      (AscFusion.isPGroup_zpowers_of_sq_eq hK.mul_self ha2) h with h1 | h1
  · rw [h1, one_mul] at ha2
    exact hz1 ha2.symm
  · rw [h1, hK.mul_self] at ha2
    exact hz1 ha2.symm

theorem eq_of_mem_of_mem {K₁ K₂ : Subgroup F} {z : F} (h₁ : IsClassical2A7 ⊤ K₁ z)
    (h₂ : IsClassical2A7 ⊤ K₂ z) {a : F} (ha₁ : a ∈ K₁) (ha₂ : a ∈ K₂)
    (ha2 : IsPGroup 2 (Subgroup.zpowers a)) (ha4 : 4 ≤ orderOf a) : K₁ = K₂ := by
  by_contra hne
  rcases eq_one_or_eq_of_forall_comm h₁ ha₁ ha2 (commutator_mem_of_twin h₁ h₂ hne ha₂) with
    h | h
  · rw [h, orderOf_one] at ha4
    omega
  · rw [h, h₁.orderOf_eq_two] at ha4
    omega

end CFSG.ClassicalInvolution.A7Core
