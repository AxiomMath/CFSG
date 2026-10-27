module

public import CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialTwistOmega
public import CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialTwistSec
public import CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialTwistAlg

public section

namespace CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialTwist

open Subgroup

namespace Data

variable {G : Type*} [Group G] [Finite G] {k : Type} [Field k] [Finite k] [CharP k 2] {m : ℕ}
  (d : Data G k m)

theorem odd_orderOf_of_cube {ω : G} (hω3 : ω * ω * ω = 1) : Odd (orderOf ω) := by
  have h : ω ^ 3 = 1 := by rw [pow_three']; exact hω3
  exact (by decide : Odd 3).of_dvd_nat (orderOf_dvd_of_pow_eq_one h)

theorem exists_mem_X₂_not_mem_F : ∃ x ∈ d.X₂, x ∉ d.F := by
  by_contra hcon
  push Not at hcon
  have h1 := Subgroup.card_le_of_le (fun x hx => hcon x hx : d.X₂ ≤ d.F)
  rw [d.card_X₂, d.card_F] at h1
  have h4 := d.two_pow_ge
  nlinarith

include d in
theorem impossible : False := by
  obtain ⟨c1, c2, -, c4, ω, hωN, hωS, hωX, hω3⟩ := d.module_facts
  have hωX₁ : ω ∈ normalizer (d.X₁ : Set G) := d.N_le_norm hωN
  have hωX₂ := d.omega_mem_normalizer_X₂ hωN hωS hω3
  have hωF := d.mem_normalizer_F hωS
  have hωZ := d.mem_normalizer_Z hωX₁
  have hω₂S := d.omega₂_mem_normalizer_S hωS
  have hω₂X₁ := d.omega₂_mem_normalizer_X₁ hωN hωS hω3
  have hω₂X₂ := d.omega₂_mem_normalizer_X₂ hωX₁
  have hω₂F := d.mem_normalizer_F hω₂S
  have hω₂Z := d.mem_normalizer_Z hω₂X₁
  have hω₂3 := d.omega₂_cube hω3
  have hcomm := d.commutator_omega_mem_S hωN hωS hω3
  have hodd : Odd (orderOf ω) := odd_orderOf_of_cube hω3
  obtain ⟨x₀, hx₀, hx₀F⟩ := d.exists_mem_X₂_not_mem_F
  have hω1 : ω ≠ 1 := fun h => hωX (h ▸ one_mem _)
  haveI n₂ : (d.F.subgroupOf d.X₂).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer d.X₂_le_normalizer_F
  haveI n₁ : (d.F.subgroupOf d.X₁).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer d.X₁_le_normalizer_F
  haveI nF : (d.Z.subgroupOf d.F).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer d.F_le_normalizer_Z
  have hmem : ∀ x ∈ d.X₂, ∀ y ∈ d.X₁, x * y * x⁻¹ * y⁻¹ ∈ d.F := fun x hx y hy =>
    d.comm_mem_F x (d.X₂_le hx) y (d.X₁_le hy)
  have hc₂F : ∀ f ∈ d.F, ∀ x ∈ d.X₂, x * f = f * x := fun f hf x hx =>
    d.F_central f hf x (d.X₂_le hx)
  have hc₁F : ∀ f ∈ d.F, ∀ y ∈ d.X₁, y * f = f * y := fun f hf y hy =>
    d.F_central f hf y (d.X₁_le hy)
  have hu₂ : ∀ y ∈ d.X₂, d.u * y * d.u⁻¹ ∈ d.X₁ := d.u_X₂
  have hu₂' : ∀ y ∈ d.X₁, d.u⁻¹ * y * d.u ∈ d.X₂ := fun _ hy => d.conj_inv_u_X₂ hy
  have huF : ∀ z ∈ d.F, d.u * z * d.u⁻¹ ∈ d.F := fun z hz => d.conj_mem_F d.u_norm hz
  have huF' : ∀ z ∈ d.F, d.u⁻¹ * z * d.u ∈ d.F := fun z hz => d.conj_inv_u_F hz
  have hSX₂ : ∀ c ∈ d.S, ∀ y ∈ d.X₂, c * y * c⁻¹ * y⁻¹ ∈ d.F := fun c hc y hy =>
    d.comm_mem_F c hc y (d.X₂_le hy)
  have hSX₁ : ∀ c ∈ d.S, ∀ y ∈ d.X₁, c * y * c⁻¹ * y⁻¹ ∈ d.F := fun c hc y hy =>
    d.comm_mem_F c hc y (d.X₁_le hy)
  have hc'S : ω * (d.u * ω * d.u⁻¹) * ω⁻¹ * (d.u * ω * d.u⁻¹)⁻¹ ∈ d.S := by
    have := inv_mem hcomm
    rwa [show ((d.u * ω * d.u⁻¹) * ω * (d.u * ω * d.u⁻¹)⁻¹ * ω⁻¹)⁻¹ =
      ω * (d.u * ω * d.u⁻¹) * ω⁻¹ * (d.u * ω * d.u⁻¹)⁻¹ by group] at this
  have hrel : ω * (d.u * ω * d.u⁻¹) = (ω * (d.u * ω * d.u⁻¹) * ω⁻¹ * (d.u * ω * d.u⁻¹)⁻¹) *
      ((d.u * ω * d.u⁻¹) * ω) := by group
  have hss : d.u * d.u ∈ d.S := d.u_sq
  have hsX₁ := d.S_mem_normalizer_X₁ hss
  have hsF := d.mem_normalizer_F (le_normalizer hss)
  have hcX₁ := d.S_mem_normalizer_X₁ hc'S
  have hcX₂ := d.S_mem_normalizer_X₂ hc'S
  have hcF := d.mem_normalizer_F (le_normalizer hc'S)
  have hY₁' : d.u * (d.u * ω * d.u⁻¹) * d.u⁻¹ ∈ normalizer (d.X₁ : Set G) := by
    have := mul_mem (mul_mem hsX₁ hωX₁) (inv_mem hsX₁)
    rwa [show d.u * d.u * ω * (d.u * d.u)⁻¹ = d.u * (d.u * ω * d.u⁻¹) * d.u⁻¹ by group] at this
  have hZ₁' : d.u * (d.u * ω * d.u⁻¹) * d.u⁻¹ ∈ normalizer (d.F : Set G) := by
    have := mul_mem (mul_mem hsF hωF) (inv_mem hsF)
    rwa [show d.u * d.u * ω * (d.u * d.u)⁻¹ = d.u * (d.u * ω * d.u⁻¹) * d.u⁻¹ by group] at this
  have hY₁'' : (d.u * d.u) * ω * (d.u * d.u)⁻¹ ∈ normalizer (d.X₁ : Set G) :=
    mul_mem (mul_mem hsX₁ hωX₁) (inv_mem hsX₁)
  have hZ₁'' : (d.u * d.u) * ω * (d.u * d.u)⁻¹ ∈ normalizer (d.F : Set G) :=
    mul_mem (mul_mem hsF hωF) (inv_mem hsF)
  refine core_false_of_comm
    (V₂ := ↥d.X₂ ⧸ d.F.subgroupOf d.X₂) (V₁ := ↥d.X₁ ⧸ d.F.subgroupOf d.X₁)
    (M := ↥d.F ⧸ d.Z.subgroupOf d.F)
    (quot_mul_comm d.X₂_ab) (quot_mul_comm d.X₁_ab)
    (quot_mul_comm fun a ha b hb => d.X₁_ab a (d.F_le₁ ha) b (d.F_le₁ hb))
    (quot_mul_self d.X₂_sq)
    (secAut ω hωX₂ hωF) (secAut (d.u * ω * d.u⁻¹) hω₂X₂ hω₂F)
    (secAut ω hωX₁ hωF) (secAut (d.u * ω * d.u⁻¹) hω₂X₁ hω₂F)
    (secAut ω hωF hωZ) (secAut (d.u * ω * d.u⁻¹) hω₂F hω₂Z)
    (fun v => secAut_cube hωX₂ hωF hω3 v) (fun v => secAut_cube hω₂X₂ hω₂F hω₂3 v)
    (fun v => ?_) (fun v => ?_)
    (secPair (Z := d.Z) hmem)
    (fun v w => (secPair_secAut hmem d.F_le₂ hc₂F hc₁F hωX₂ hωX₁ hωF hωZ v w).symm)
    (fun v w => (secPair_secAut hmem d.F_le₂ hc₂F hc₁F hω₂X₂ hω₂X₁ hω₂F hω₂Z v w).symm)
    (fun v w w' => secPair_mul_right hmem d.F_le₂ hc₂F hc₁F v w w')
    ?_
    (secMap d.u hu₂ hu₂' huF huF')
    (fun v => secMap_secAut d.u ω hu₂ hu₂' huF huF' hωX₂ hωF hω₂X₁ hω₂F v)
    (fun v => ?_) ?_ ?_ ?_ ((⟨x₀, hx₀⟩ : d.X₂) : ↥d.X₂ ⧸ d.F.subgroupOf d.X₂) ?_
  ·
    exact secAut_mul_comm_of_triv d.X₂_le_normalizer_F hωX₂ hωF hω₂X₂ hω₂F hcX₂ hcF
      (fun y hy => hSX₂ _ hc'S y hy) hrel v
  · exact secAut_mul_comm_of_triv d.X₁_le_normalizer_F hωX₁ hωF hω₂X₁ hω₂F hcX₁ hcF
      (fun y hy => hSX₁ _ hc'S y hy) hrel v
  ·
    intro v w hvw
    induction v using QuotientGroup.induction_on with
    | H x =>
      induction w using QuotientGroup.induction_on with
      | H y =>
        rw [secPair_mk hmem d.F_le₂ hc₂F hc₁F] at hvw
        have hZmem : (x : G) * y * (x : G)⁻¹ * (y : G)⁻¹ ∈ d.Z :=
          mem_subgroupOf.mp ((QuotientGroup.eq_one_iff (N := d.Z.subgroupOf d.F) _).mp hvw)
        by_cases hxF : (x : G) ∈ d.F
        · exact Or.inl ((QuotientGroup.eq_one_iff (N := d.F.subgroupOf d.X₂) _).mpr
            (mem_subgroupOf.mpr hxF))
        · have hxX₁ : (x : G) ∉ d.X₁ := fun h => hxF (d.X₁_inf_X₂ x h x.2)
          have hyF := c2 x (d.X₂_le x.2) hxX₁ y y.2 hZmem
          exact Or.inr ((QuotientGroup.eq_one_iff (N := d.F.subgroupOf d.X₁) _).mpr
            (mem_subgroupOf.mpr hyF))
  ·
    rw [secMap_secAut d.u (d.u * ω * d.u⁻¹) hu₂ hu₂' huF huF' hω₂X₂ hω₂F hY₁' hZ₁' v,
      secAut_of_eq (show d.u * (d.u * ω * d.u⁻¹) * d.u⁻¹ = (d.u * d.u) * ω * (d.u * d.u)⁻¹ by
        group) hY₁' hZ₁' hY₁'' hZ₁'']
    exact secAut_conj_triv d.X₁_le_normalizer_F hωX₁ hωF hsX₁ hsF (inv_mem hsX₁) (inv_mem hsF)
      hY₁'' hZ₁'' (fun y hy => hSX₁ _ hss y hy) (fun y hy => hSX₁ _ (inv_mem hss) y hy) _
  ·
    intro v hv
    induction v using QuotientGroup.induction_on with
    | H x =>
      rw [secAut_apply_eq_iff d.X₂_le_normalizer_F hωX₂ hωF x] at hv
      have hxX₁ : (x : G) ∈ d.X₁ := c4 ω hωN hωX hodd x (d.X₂_le x.2) (d.F_le₁ hv)
      exact (QuotientGroup.eq_one_iff (N := d.F.subgroupOf d.X₂) _).mpr
        (mem_subgroupOf.mpr (d.X₁_inf_X₂ x hxX₁ x.2))
  ·
    intro m hm
    induction m using QuotientGroup.induction_on with
    | H f =>
      rw [secAut_apply_eq_iff d.F_le_normalizer_Z hωF hωZ f] at hm
      have hfZ : (f : G) ∈ d.Z := c1 ω hωN hω1 hodd f (d.F_le₁ f.2) hm
      exact (QuotientGroup.eq_one_iff (N := d.Z.subgroupOf d.F) _).mpr (mem_subgroupOf.mpr hfZ)
  ·
    intro m
    induction m using QuotientGroup.induction_on with
    | H f =>
      exact (secAut_apply_eq_iff d.F_le_normalizer_Z hω₂F hω₂Z f).mpr
        (d.omega₂_triv_F hωN hωS hω3 f.2)
  · exact fun h => hx₀F (mem_subgroupOf.mp
      ((QuotientGroup.eq_one_iff (N := d.F.subgroupOf d.X₂) _).mp h))

end Data

end CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialTwist
