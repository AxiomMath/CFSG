module

public import CFSG.ClassicalInvolution.Asc77.AscE184Quot
public import CFSG.ClassicalInvolution.Asc77.AscE184Sub
public import CFSG.ClassicalInvolution.AschTight.S1911Facts
public import CFSG.ClassicalInvolution.AschTight.S1911FusF
public import CFSG.ClassicalInvolution.Uniform.UFacade

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

theorem false_of_inv_mul_mem_odd {H : Type} [Group H] [Finite H] {N : Subgroup H}
    (hN : Odd (Nat.card N)) {x y : H} (h : x⁻¹ * y ∈ N) (hx2 : x * x = 1) (hy2 : y * y = 1)
    (hxy : x * y = y * x) (hne : x ≠ y) : False := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hw2 : x⁻¹ * y * (x⁻¹ * y) = 1 := by
    rw [hxi]
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * x * (y * y) := by rw [← hxy]; group
      _ = 1 := by rw [hx2, hy2, one_mul]
  have hw1 : x⁻¹ * y ≠ 1 := fun h1 => hne (inv_mul_eq_one.mp h1)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine hw1 (eq_one_of_isPGroup_of_mem_odd hN h ?_)
  exact IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, pow_one, orderOf_eq_prime (by rw [sq]; exact hw2) hw1])

variable {G : Type} [Group G] [Finite G] {K C : Subgroup G} {z : G}

theorem top_not_mem_sectionFamily_sec (hzC : z ∈ C)
    (hL : Q3.IsClassicalMember3 ((K ⊓ C).subgroupOf C) (⟨z, hzC⟩ : C)) (c : ↥C)
    (hne : (c : G) * z * (c : G)⁻¹ ≠ z)
    (hcomm : (c : G) * z * (c : G)⁻¹ * z = z * ((c : G) * z * (c : G)⁻¹)) :
    (⊤ : Subgroup (↥(conjGen ((K ⊓ C).subgroupOf C)) ⧸
      classicalInvolutionOddCore ↥(conjGen ((K ⊓ C).subgroupOf C)))) ∉
      oddQuotientFamily (restrictFamily (conjFamily ((K ⊓ C).subgroupOf C))
        (conjGen ((K ⊓ C).subgroupOf C))) := by
  intro hTop
  set L := (K ⊓ C).subgroupOf C with hLdef
  set Y₁ := conjGen L with hY₁
  set N := classicalInvolutionOddCore ↥Y₁ with hN
  have hNodd : Odd (Nat.card N) := CFSG.ComponentClassification.OddCore.odd_card ↥Y₁
  have hI : IsUniqueInvolution L (⟨z, hzC⟩ : C) :=
    (isClassicalMember3_iff_U.mp hL).isUniqueInvolution (MemberType.cert_sl2 3 1)
  have key : ∀ d : ↥C, IsUniqueInvolution (((conjSub d L).subgroupOf Y₁).map
      (QuotientGroup.mk' N))
      (QuotientGroup.mk' N ⟨d * (⟨z, hzC⟩ : C) * d⁻¹, le_conjGen ⟨d, rfl⟩
        (conj_mem_conjSub hL.mem)⟩) := fun d =>
    isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hNodd _)
      (isUniqueInvolution_subgroupOf (hI.conj d) (le_conjGen ⟨d, rfl⟩))
  obtain ⟨_, ⟨M, ⟨d, rfl⟩, hMY, rfl⟩, hdT⟩ := hTop
  have hU := key d
  rw [hdT] at hU
  have h1 := key 1
  have hc := key c
  have e1 := (hU.unique _ (Subgroup.mem_top _) h1.sq).resolve_left h1.ne_one
  have ec := (hU.unique _ (Subgroup.mem_top _) hc.sq).resolve_left hc.ne_one
  have e := e1.trans ec.symm
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at e
  refine false_of_inv_mul_mem_odd hNodd e ?_ ?_ ?_ ?_
  · apply Subtype.ext
    apply Subtype.ext
    simp [hI.sq]
  · apply Subtype.ext
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
    calc (c : G) * z * (c : G)⁻¹ * ((c : G) * z * (c : G)⁻¹) = (c : G) * (z * z) * (c : G)⁻¹ := by
          group
      _ = 1 := by
        have := congrArg Subtype.val hI.sq
        simp only [Subgroup.coe_mul, Subgroup.coe_one] at this
        rw [this]; group
  · apply Subtype.ext
    apply Subtype.ext
    simpa using hcomm.symm
  · intro h
    apply hne
    have h' := congrArg (fun x : ↥Y₁ => ((x : ↥C) : G)) h
    simpa using h'.symm

end CFSG.ClassicalInvolution.Q3.Q3T6
