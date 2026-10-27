module

public import CFSG.ClassicalInvolution.Asc77.AscE184SecA

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem sec5pk_comm_sup {R K O : Subgroup G}
    (hOn : ∀ m ∈ K ⊔ O, ∀ o ∈ O, m * o * m⁻¹ ∈ O)
    (hRO : ∀ x ∈ R, ∀ o ∈ O, x * o * x⁻¹ ∈ O)
    (hRK : ∀ x ∈ R, ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ O) :
    ∀ x ∈ R, ∀ m ∈ K ⊔ O, x * m * x⁻¹ * m⁻¹ ∈ O := by
  let D : Subgroup G :=
    { carrier := {m | m ∈ K ⊔ O ∧ ∀ x ∈ R, x * m * x⁻¹ * m⁻¹ ∈ O}
      one_mem' := ⟨(K ⊔ O).one_mem, fun x _ => by simp⟩
      mul_mem' := by
        rintro m m' ⟨hm, hm'⟩ ⟨hn, hn'⟩
        refine ⟨(K ⊔ O).mul_mem hm hn, fun x hx => ?_⟩
        have h1 : x * (m * m') * x⁻¹ * (m * m')⁻¹ =
            (x * m * x⁻¹ * m⁻¹) * (m * (x * m' * x⁻¹ * m'⁻¹) * m⁻¹) := by group
        rw [h1]
        exact O.mul_mem (hm' x hx) (hOn m hm _ (hn' x hx))
      inv_mem' := by
        rintro m ⟨hm, hm'⟩
        refine ⟨(K ⊔ O).inv_mem hm, fun x hx => ?_⟩
        have h1 : x * m⁻¹ * x⁻¹ * (m⁻¹)⁻¹ = m⁻¹ * (x * m * x⁻¹ * m⁻¹)⁻¹ * m := by
          group
        rw [h1]
        simpa using hOn m⁻¹ ((K ⊔ O).inv_mem hm) _ (O.inv_mem (hm' x hx)) }
  have hK : K ≤ D := fun k hk => ⟨Subgroup.mem_sup_left hk, fun x hx => hRK x hx k hk⟩
  have hO' : O ≤ D := by
    intro o ho
    refine ⟨Subgroup.mem_sup_right ho, fun x hx => ?_⟩
    have h1 : x * o * x⁻¹ * o⁻¹ = (x * o * x⁻¹) * o⁻¹ := by group
    rw [h1]
    exact O.mul_mem (hRO x hx o ho) (O.inv_mem ho)
  intro x hx m hm
  exact (sup_le hK hO' hm).2 x hx

theorem sec5pk_lift {R M O : Subgroup G} (hR : IsPGroup 2 R) (hO : Odd (Nat.card O))
    (hOM : O ≤ M) (hOn : ∀ m ∈ M, ∀ o ∈ O, m * o * m⁻¹ ∈ O)
    (hRM : ∀ x ∈ R, ∀ m ∈ M, x * m * x⁻¹ * m⁻¹ ∈ O) :
    ∀ m ∈ M, ∃ c ∈ M ⊓ centralizer (R : Set G), c⁻¹ * m ∈ O := by
  intro m hm
  have hAN : ∀ a ∈ R, ∀ n ∈ O, a * n * a⁻¹ ∈ O := by
    intro a ha n hn
    have h1 : a * n * a⁻¹ = (a * n * a⁻¹ * n⁻¹) * n := by group
    rw [h1]
    exact O.mul_mem (hRM a ha n (hOM hn)) hn
  have hx : ∀ a ∈ R, m⁻¹ * (a * m * a⁻¹) ∈ O := by
    intro a ha
    have h1 : m⁻¹ * (a * m * a⁻¹) = m⁻¹ * (a * m * a⁻¹ * m⁻¹) * m := by group
    rw [h1]
    simpa using hOn m⁻¹ (M.inv_mem hm) (a * m * a⁻¹ * m⁻¹) (hRM a ha m hm)
  obtain ⟨n, hn, hfix⟩ :=
    CFSG.ClassicalInvolution.Asc77.AscE184Sect.exists_fixed_mem_coset
      (A := R) (N := O) hR hO hAN (x := m) hx
  refine ⟨m * n, ⟨M.mul_mem hm (hOM hn), ?_⟩, ?_⟩
  · refine Subgroup.mem_centralizer_iff.mpr ?_
    intro a ha
    calc a * (m * n) = (a * (m * n) * a⁻¹) * a := by group
      _ = (m * n) * a := by rw [hfix a ha]
  · have h3 : (m * n)⁻¹ * m = n⁻¹ := by group
    rw [h3]
    exact O.inv_mem hn

end CFSG.OddStandard.SmallF3.Omega
