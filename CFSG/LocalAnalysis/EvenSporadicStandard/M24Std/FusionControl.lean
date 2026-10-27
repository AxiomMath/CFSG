module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.TransferParity

public section

namespace CFSG.EvenSporadicStandard

open MulAction Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem false_of_fusion_control (hG : ∀ ψ : G →* ℤˣ, ψ = 1) {z : G} (hz : z * z = 1)
    (H : Subgroup G) (hzH : z ∈ H) (φ : H →* ℤˣ) (hφz : φ ⟨z, hzH⟩ = -1)
    (hfuse : ∀ y : H, φ y = -1 → (∃ g : G, g * z * g⁻¹ = y) → ∃ h ∈ H, h * z * h⁻¹ = y)
    (hodd : ¬ 2 ∣ H.relIndex (centralizer ({z} : Set G))) : False := by
  classical
  have hTL := even_nat_card_fixed_neg φ hz hG
  let C : Subgroup G := centralizer ({z} : Set G)
  let base : G ⧸ H := ((1 : G) : G ⧸ H)
  have hmkc : ∀ c : C, c • base = ((c : G) : G ⧸ H) := fun c => by
    rw [Subgroup.smul_def]
    show (c : G) • ((1 : G) : G ⧸ H) = _
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
  have hset : {q : G ⧸ H | z • q = q ∧ valAt H φ q.out (z * q.out) = -1} =
      MulAction.orbit C base := by
    ext q
    constructor
    · rintro ⟨hz1, hval⟩
      have h1 := out_inv_mul_mem_of_smul_eq hz1
      have hy : φ ⟨q.out⁻¹ * (z * q.out), h1⟩ = -1 := by
        rw [← valAt_of_mem φ h1]
        exact hval
      obtain ⟨h, hh, hhz⟩ := hfuse ⟨q.out⁻¹ * (z * q.out), h1⟩ hy
        ⟨q.out⁻¹, by simp [mul_assoc]⟩
      have hc : q.out * h ∈ C := by
        rw [mem_centralizer_singleton_iff]
        have : h * z * h⁻¹ = q.out⁻¹ * (z * q.out) := hhz
        calc q.out * h * z = q.out * (h * z * h⁻¹) * h := by group
          _ = q.out * (q.out⁻¹ * (z * q.out)) * h := by rw [this]
          _ = z * (q.out * h) := by group
      refine ⟨⟨q.out * h, hc⟩, ?_⟩
      show (⟨q.out * h, hc⟩ : C) • base = q
      rw [hmkc]
      show ((q.out * h : G) : G ⧸ H) = q
      calc ((q.out * h : G) : G ⧸ H) = ((q.out : G) : G ⧸ H) :=
            QuotientGroup.eq.2 (by simpa using H.inv_mem hh)
        _ = q := QuotientGroup.out_eq' q
    · rintro ⟨c', rfl⟩
      have hq : c' • base = ((c' : G) : G ⧸ H) := hmkc c'
      have hcz : (c' : G) * z = z * (c' : G) := mem_centralizer_singleton_iff.1 c'.2
      have hfz : z • ((c' : G) : G ⧸ H) = ((c' : G) : G ⧸ H) := by
        rw [MulAction.Quotient.smul_mk, smul_eq_mul, ← hcz]
        exact QuotientGroup.eq.2 (by simpa using H.inv_mem hzH)
      refine ⟨?_, ?_⟩
      · show z • (c' • base) = c' • base
        rw [hq]
        exact hfz
      · show valAt H φ (c' • base).out (z * (c' • base).out) = -1
        rw [hq]
        have h1 := out_inv_mul_mem_of_smul_eq hfz
        rw [valAt_of_mem φ h1]
        have h2 : (↑(((c' : G) : G ⧸ H).out) : G ⧸ H) = ((c' : G) : G ⧸ H) :=
          QuotientGroup.out_eq' _
        have hm : (((c' : G) : G ⧸ H).out)⁻¹ * (c' : G) ∈ H := QuotientGroup.eq.mp h2
        have key : (⟨(((c' : G) : G ⧸ H).out)⁻¹ * (z * ((c' : G) : G ⧸ H).out), h1⟩ : H) =
            ⟨_, hm⟩ * ⟨z, hzH⟩ * (⟨_, hm⟩ : H)⁻¹ := by
          ext
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          have hcz' : (c' : G)⁻¹ * z * c' = z := by
            calc (c' : G)⁻¹ * z * c' = (c' : G)⁻¹ * (z * c') := by group
              _ = (c' : G)⁻¹ * (c' * z) := by rw [← hcz]
              _ = z := by group
          calc (((c' : G) : G ⧸ H).out)⁻¹ * (z * ((c' : G) : G ⧸ H).out)
              = ((((c' : G) : G ⧸ H).out)⁻¹ * c') * ((c' : G)⁻¹ * z * c') *
                ((((c' : G) : G ⧸ H).out)⁻¹ * c')⁻¹ := by group
            _ = _ := by rw [hcz']
        rw [key, map_mul, map_mul, map_inv, mul_comm (φ _) (φ _), mul_assoc, mul_inv_cancel,
          mul_one]
        exact hφz
  have hcard : Nat.card {q : G ⧸ H // z • q = q ∧ valAt H φ q.out (z * q.out) = -1} =
      H.relIndex C := by
    have h1 : Nat.card {q : G ⧸ H // z • q = q ∧ valAt H φ q.out (z * q.out) = -1} =
        Nat.card (MulAction.orbit C base) := by
      rw [← hset]
      rfl
    have hstab : MulAction.stabilizer C base = H.subgroupOf C := by
      ext c
      rw [MulAction.mem_stabilizer_iff, hmkc, Subgroup.mem_subgroupOf]
      constructor
      · intro h
        have := QuotientGroup.eq.mp h
        simpa using H.inv_mem this
      · intro h
        exact QuotientGroup.eq.2 (by simpa using H.inv_mem h)
    rw [h1, Nat.card_coe_set_eq, ← MulAction.index_stabilizer C base, hstab]
    rfl
  rw [hcard] at hTL
  exact hodd (even_iff_two_dvd.1 hTL)

end CFSG.EvenSporadicStandard
