module

public import CFSG.ClassicalInvolution.AschTight.S1911P3h

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19C

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
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

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W : Subgroup G}

theorem top_not_mem_secFamily (hd : Sec19Data p f K z S W) {a : G}
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hzKa : z ∈ perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G)))
    (c : ↥(Subgroup.centralizer ({a} : Set G))) (hne : (c : G) * z * (c : G)⁻¹ ≠ z)
    (hcomm : (c : G) * z * (c : G)⁻¹ * z = z * ((c : G) * z * (c : G)⁻¹)) :
    (⊤ : Subgroup (↥(conjGen (perfectCoreIn K a)) ⧸
      classicalInvolutionOddCore ↥(conjGen (perfectCoreIn K a)))) ∉
      oddQuotientFamily (restrictFamily (conjFamily (perfectCoreIn K a))
        (conjGen (perfectCoreIn K a))) := by
  intro hTop
  obtain ⟨d, hdT⟩ := (mem_secFamily_iff _ _).mp hTop
  have hU := isUniqueInvolution_secImg hd hzA hzKa d
  rw [← hdT] at hU
  have h1 := isUniqueInvolution_secImg hd hzA hzKa 1
  have hc := isUniqueInvolution_secImg hd hzA hzKa c
  have e1 := (hU.unique _ (Subgroup.mem_top _) h1.sq).resolve_left h1.ne_one
  have ec := (hU.unique _ (Subgroup.mem_top _) hc.sq).resolve_left hc.ne_one
  have e := e1.trans ec.symm
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at e
  have hI := isUniqueInvolution_of_tight hd.tight.toTightBranch
  refine false_of_inv_mul_mem_odd (CFSG.ComponentClassification.OddCore.odd_card _) e ?_ ?_ ?_ ?_
  · apply Subtype.ext
    apply Subtype.ext
    simp [hI.sq]
  · apply Subtype.ext
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
    calc (c : G) * z * (c : G)⁻¹ * ((c : G) * z * (c : G)⁻¹) = (c : G) * (z * z) * (c : G)⁻¹ := by
          group
      _ = 1 := by rw [hI.sq]; group
  · apply Subtype.ext
    apply Subtype.ext
    simpa using hcomm.symm
  · intro h
    apply hne
    have h' := congrArg (fun x : ↥(conjGen (perfectCoreIn K a)) =>
      ((x : ↥(Subgroup.centralizer ({a} : Set G))) : G)) h
    simpa using h'.symm

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19C
