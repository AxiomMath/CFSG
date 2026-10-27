module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z2A5QuotC
public import CFSG.ClassicalInvolution.QuaternionStructure.OddCoreQuotient
public import CFSG.GH74.GLS.Stage1.Thm4.L96Norm

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {Y : Type} [Group Y] {τ : Y}

private theorem z2a5_quot_oTwoRes_le (H : Subgroup Y) : oTwoRes H ≤ H :=
  (Subgroup.closure_le _).2 fun _ hx => hx.1

private theorem z2a5_ne_one_quot [Finite Y] (h : Z2A5Hyp Y τ) :
    (τ : Y ⧸ oddCore Y) ≠ 1 := fun hc =>
  CFSG.ClassicalInvolution.QuaternionStructure.not_mem_oddCore_of_orderOf_eq_two h.1
    ((QuotientGroup.eq_one_iff τ).mp hc)

private theorem z2a5_quot_injective [Finite Y] (h : Z2A5Hyp Y τ) :
    Function.Injective ((QuotientGroup.mk' (oddCore Y)).domRestrict
      (centralizer ({τ} : Set Y))) := by
  refine (injective_iff_map_eq_one _).2 fun x hx => ?_
  have hxO : (x : Y) ∈ oddCore Y := by
    have h1 : QuotientGroup.mk' (oddCore Y) (x : Y) = 1 := hx
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hmem : (x : Y) ∈ centralizer ({τ} : Set Y) ⊓ oddCore Y := ⟨x.2, hxO⟩
  rw [z2a5_cent_inf_oddCore h] at hmem
  exact Subtype.ext (Subgroup.mem_bot.mp hmem)

private theorem z2a5_quot_orderOf [Finite Y] (h : Z2A5Hyp Y τ) :
    orderOf (τ : Y ⧸ oddCore Y) = 2 := by
  have hτC : τ ∈ centralizer ({τ} : Set Y) := mem_centralizer_singleton_iff.mpr rfl
  have h1 := orderOf_injective ((QuotientGroup.mk' (oddCore Y)).domRestrict
    (centralizer ({τ} : Set Y))) (z2a5_quot_injective h) ⟨τ, hτC⟩
  rw [Subgroup.orderOf_mk, h.1] at h1
  simpa [MonoidHom.domRestrict_apply] using h1

private theorem z2a5_quot_nonempty [Finite Y] (h : Z2A5Hyp Y τ) :
    Nonempty (↥(centralizer ({(τ : Y ⧸ oddCore Y)} : Set (Y ⧸ oddCore Y))) ≃*
      (Multiplicative (ZMod 2) × ↥(alternatingGroup (Fin 5)))) := by
  obtain ⟨e⟩ := h.2.1
  exact ⟨((MulEquiv.subgroupCongr (z2a5_quot_cent h)).trans
    ((CFSG.ClassicalInvolution.QuaternionStructure.mulEquivMapOfInjective
      (QuotientGroup.mk' (oddCore Y)) (centralizer ({τ} : Set Y))
      (z2a5_quot_injective h)).symm)).trans e⟩

private theorem z2a5_quot_conjClassIn {u : Y}
    (hu : u ∈ conjClassIn (⊤ : Subgroup Y) τ) :
    (u : Y ⧸ oddCore Y) ∈
      conjClassIn (⊤ : Subgroup (Y ⧸ oddCore Y)) (τ : Y ⧸ oddCore Y) := by
  obtain ⟨g, -, rfl⟩ := hu
  exact ⟨(g : Y ⧸ oddCore Y), Subgroup.mem_top _, by simp⟩

private theorem z2a5_quot_fusion_forward [Finite Y] (h : Z2A5Hyp Y τ)
    {y : Y ⧸ oddCore Y}
    (hy : y ∈ conjClassIn (⊤ : Subgroup (Y ⧸ oddCore Y)) (τ : Y ⧸ oddCore Y) ∧
      y ∈ centralizer ({(τ : Y ⧸ oddCore Y)} : Set (Y ⧸ oddCore Y))) :
    ∃ x ∈ oTwoRes (centralizer ({(τ : Y ⧸ oddCore Y)} : Set (Y ⧸ oddCore Y))),
      y = (τ : Y ⧸ oddCore Y) * x ∧ y * y = 1 := by
  set π := QuotientGroup.mk' (oddCore Y)
  have hτ2 : orderOf τ = 2 := h.1
  have hττ : (τ : Y ⧸ oddCore Y) * (τ : Y ⧸ oddCore Y) = 1 := by
    rw [← sq, ← QuotientGroup.mk_pow,
      show τ ^ 2 = 1 by rw [← hτ2, pow_orderOf_eq_one], QuotientGroup.mk_one]
  have hy_ne : y ≠ 1 := by
    obtain ⟨g, -, hg⟩ := hy.1
    rw [hg]
    intro hc
    have h2 := congrArg (fun z => g⁻¹ * z * g) hc
    have h3 : g⁻¹ * (g * (τ : Y ⧸ oddCore Y) * g⁻¹) * g = (τ : Y ⧸ oddCore Y) := by
      group
    rw [h3] at h2
    exact z2a5_ne_one_quot h (by simpa using h2)
  have hyy : y * y = 1 := by
    obtain ⟨g, -, hg⟩ := hy.1
    rw [hg]
    calc (g * (τ : Y ⧸ oddCore Y) * g⁻¹) * (g * (τ : Y ⧸ oddCore Y) * g⁻¹)
        = g * ((τ : Y ⧸ oddCore Y) * (τ : Y ⧸ oddCore Y)) * g⁻¹ := by group
      _ = 1 := by rw [hττ, mul_one, mul_inv_cancel]
  have hyC : y ∈ (centralizer ({τ} : Set Y)).map π := by
    rw [← z2a5_quot_cent h]
    exact hy.2
  obtain ⟨u, huC, hu_eq⟩ := Subgroup.mem_map.mp hyC
  obtain ⟨g, -, hg⟩ := hy.1
  obtain ⟨g0, hg0⟩ := QuotientGroup.mk'_surjective (oddCore Y) g
  have hpg : π (g0 * τ * g0⁻¹) = y := by
    simp only [π, map_mul, map_inv, hg0, hg, QuotientGroup.mk'_apply]
  have hmemO : u⁻¹ * (g0 * τ * g0⁻¹) ∈ oddCore Y := by
    apply (QuotientGroup.eq_one_iff _).mp
    have h1 : π (u⁻¹ * (g0 * τ * g0⁻¹)) = 1 := by
      simp only [map_mul, map_inv, hu_eq, hpg, inv_mul_cancel]
    simpa only [π, QuotientGroup.mk'_apply] using h1
  have hu2 : u * u = 1 := by
    have h1 : π (u * u) = 1 := by simp only [map_mul, hu_eq, hyy]
    have h2 : u * u ∈ oddCore Y :=
      (QuotientGroup.eq_one_iff _).mp (by simpa only [π, QuotientGroup.mk'_apply] using h1)
    have h3 : u * u ∈ centralizer ({τ} : Set Y) ⊓ oddCore Y :=
      ⟨(centralizer ({τ} : Set Y)).mul_mem huC huC, h2⟩
    rw [z2a5_cent_inf_oddCore h] at h3
    exact Subgroup.mem_bot.mp h3
  have hune : u ≠ 1 := fun hu1 => hy_ne (by rw [← hu_eq, hu1, map_one])
  have horder_u : orderOf u = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hu2) hune
  have hp2 : orderOf (g0 * τ * g0⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hτ2]
  have hmemO' : (g0 * τ * g0⁻¹)⁻¹ * u ∈ oddCore Y := by
    have h1 := (oddCore Y).inv_mem hmemO
    rwa [mul_inv_rev, inv_inv] at h1
  obtain ⟨n, -, hn⟩ := CFSG.GH74.GLS.Stage1.Thm4.L96.exists_conj_in_odd_normal
    (show Odd (Nat.card (oddCore Y)) from
      CFSG.ClassicalInvolution.QuaternionStructure.odd_natCard_oddCore Y) hp2 horder_u hmemO'
  have hconju : u ∈ conjClassIn (⊤ : Subgroup Y) τ := by
    refine ⟨n * g0, Subgroup.mem_top _, ?_⟩
    rw [← hn]
    group
  obtain ⟨x, hxX, hux, -⟩ := (h.2.2 u).1 ⟨hconju, huC⟩
  have hf : centralizer ({τ} : Set Y) ⊓ π.ker = ⊥ := by
    rw [show π.ker = oddCore Y from QuotientGroup.ker_mk' (oddCore Y)]
    exact z2a5_cent_inf_oddCore h
  refine ⟨π x, ?_, ?_, hyy⟩
  · have hxmap : π x ∈ (oTwoRes (centralizer ({τ} : Set Y))).map π := ⟨x, hxX, rfl⟩
    rw [z2a5_map_oTwoRes π hf] at hxmap
    rw [← z2a5_quot_cent h] at hxmap
    exact hxmap
  · rw [← hu_eq, hux, map_mul, QuotientGroup.mk'_apply]

private theorem z2a5_quot_fusion_backward [Finite Y] (h : Z2A5Hyp Y τ)
    {y : Y ⧸ oddCore Y}
    (hy : ∃ x ∈ oTwoRes (centralizer ({(τ : Y ⧸ oddCore Y)} : Set (Y ⧸ oddCore Y))),
      y = (τ : Y ⧸ oddCore Y) * x ∧ y * y = 1) :
    y ∈ conjClassIn (⊤ : Subgroup (Y ⧸ oddCore Y)) (τ : Y ⧸ oddCore Y) ∧
      y ∈ centralizer ({(τ : Y ⧸ oddCore Y)} : Set (Y ⧸ oddCore Y)) := by
  set π := QuotientGroup.mk' (oddCore Y)
  obtain ⟨x, hx, hyx, hyy⟩ := hy
  have hf : centralizer ({τ} : Set Y) ⊓ π.ker = ⊥ := by
    rw [show π.ker = oddCore Y from QuotientGroup.ker_mk' (oddCore Y)]
    exact z2a5_cent_inf_oddCore h
  have hxmap : x ∈ (oTwoRes (centralizer ({τ} : Set Y))).map π := by
    rw [z2a5_map_oTwoRes π hf, ← z2a5_quot_cent h]
    exact hx
  obtain ⟨x0, hx0, hx0eq⟩ := Subgroup.mem_map.mp hxmap
  have hx0C : x0 ∈ centralizer ({τ} : Set Y) := z2a5_quot_oTwoRes_le _ hx0
  have huC : τ * x0 ∈ centralizer ({τ} : Set Y) :=
    (centralizer ({τ} : Set Y)).mul_mem (mem_centralizer_singleton_iff.mpr rfl) hx0C
  have hu_eq : π (τ * x0) = y := by
    rw [map_mul, hx0eq, hyx]
    simp only [π, QuotientGroup.mk'_apply]
  have hu2 : (τ * x0) * (τ * x0) = 1 := by
    have h1 : π ((τ * x0) * (τ * x0)) = 1 := by rw [map_mul, hu_eq, hyy]
    have h2 : (τ * x0) * (τ * x0) ∈ oddCore Y :=
      (QuotientGroup.eq_one_iff _).mp (by simpa only [π, QuotientGroup.mk'_apply] using h1)
    have h3 : (τ * x0) * (τ * x0) ∈ centralizer ({τ} : Set Y) ⊓ oddCore Y :=
      ⟨(centralizer ({τ} : Set Y)).mul_mem huC huC, h2⟩
    rw [z2a5_cent_inf_oddCore h] at h3
    exact Subgroup.mem_bot.mp h3
  have hconju : τ * x0 ∈ conjClassIn (⊤ : Subgroup Y) τ :=
    ((h.2.2 (τ * x0)).2 ⟨x0, hx0, rfl, hu2⟩).1
  have hu_eq' : ((τ * x0 : Y) : Y ⧸ oddCore Y) = y := by
    simpa only [π, QuotientGroup.mk'_apply] using hu_eq
  have hconjy : y ∈ conjClassIn (⊤ : Subgroup (Y ⧸ oddCore Y)) (τ : Y ⧸ oddCore Y) := by
    have h1 := z2a5_quot_conjClassIn hconju
    rwa [hu_eq'] at h1
  refine ⟨hconjy, ?_⟩
  rw [z2a5_quot_cent h]
  exact ⟨τ * x0, huC, hu_eq⟩

theorem z2a5Hyp_quot [Finite Y] (h : Z2A5Hyp Y τ) :
    Z2A5Hyp (Y ⧸ oddCore Y) (τ : Y ⧸ oddCore Y) := by
  refine ⟨z2a5_quot_orderOf h, z2a5_quot_nonempty h, ?_⟩
  intro y
  exact ⟨z2a5_quot_fusion_forward h, z2a5_quot_fusion_backward h⟩

theorem z2a5_oddCore_quot [Finite Y] : oddCore (Y ⧸ oddCore Y) = ⊥ :=
  CFSG.ClassicalInvolution.QuaternionStructure.oddCore_quotient_oddCore_eq_bot Y

theorem z2a5_kgroup_quot (hK : CFSG.SectionRank.IsKGroupCat Y) :
    CFSG.SectionRank.IsKGroupCat (Y ⧸ oddCore Y) :=
  hK.quotient _

end CFSG.OddStandard.SmallF3.Omega
