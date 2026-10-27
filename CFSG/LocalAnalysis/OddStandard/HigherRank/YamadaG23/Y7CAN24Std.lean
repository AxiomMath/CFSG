module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CAN24El
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CAN24H1

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Matrix CFSG.OddStandard.AltStdSmall4.GL62

theorem n24_std (D : Subgroup (GL (Fin 6) (ZMod 2)))
    (hD : Nonempty (↥D ≃* GL (Fin 3) (ZMod 2))) (hc : ∀ d ∈ D, d * z₀ = z₀ * d) :
    ∃ u : GL (Fin 6) (ZMod 2), u * z₀ = z₀ * u ∧
      ∀ x : GL (Fin 6) (ZMod 2), x ∈ D ↔
        u * x * u⁻¹ ∈ (dg : GL (Fin 3) (ZMod 2) →* GL (Fin 6) (ZMod 2)).range := by
  classical
  let F : ↥D → GL (Fin 3) (ZMod 2) × N24Mat3 := fun d =>
    ⟨(exists_n24El_of_comm (d : GL (Fin 6) (ZMod 2)) (hc d d.2)).choose,
      (exists_n24El_of_comm (d : GL (Fin 6) (ZMod 2)) (hc d d.2)).choose_spec.choose⟩
  have hF (d : ↥D) : (d : GL (Fin 6) (ZMod 2)) = n24El (F d).1 (F d).2 :=
    (exists_n24El_of_comm (d : GL (Fin 6) (ZMod 2)) (hc d d.2)).choose_spec.choose_spec
  let P0 : ↥D → GL (Fin 3) (ZMod 2) := fun d => (F d).1
  let Q : ↥D → N24Mat3 := fun d => (F d).2
  have hF0 (d : ↥D) : (d : GL (Fin 6) (ZMod 2)) = n24El (P0 d) (Q d) := hF d
  have hPmul (d e : ↥D) : P0 (d * e) = P0 d * P0 e := by
    have h : n24El (P0 (d * e)) (Q (d * e)) =
        n24El (P0 d * P0 e) ((P0 d : N24Mat3) * Q e + Q d * (P0 e : N24Mat3)) := by
      rw [← hF0 (d * e), Subgroup.coe_mul, hF0 d, hF0 e, n24El_mul]
    exact (n24El_inj.mp h).1
  have hPone : P0 1 = 1 := by
    have h : n24El (P0 1) (Q 1) = n24El (1 : GL (Fin 3) (ZMod 2)) 0 := by
      rw [← hF0 1, n24El_one]
      simp
    exact (n24El_inj.mp h).1
  let P : ↥D →* GL (Fin 3) (ZMod 2) :=
    { toFun := P0, map_one' := hPone, map_mul' := hPmul }
  have hFP (d : ↥D) : (d : GL (Fin 6) (ZMod 2)) = n24El (P d) (Q d) := hF0 d
  haveI : IsSimpleGroup (GL (Fin 3) (ZMod 2)) :=
    CFSG.ComponentClassification.GHarris.isSimpleGroup_GL32_gh
  haveI : IsSimpleGroup ↥D := hD.some.isSimpleGroup
  have hinj : Function.Injective P := by
    rw [← MonoidHom.ker_eq_bot_iff P]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P.ker with h | h
    · exact h
    · exfalso
      have htriv (d : ↥D) : P d = 1 := by
        have hd : d ∈ P.ker := by rw [h]; exact Subgroup.mem_top d
        simpa [MonoidHom.mem_ker] using hd
      have hd_one (d : ↥D) : (d : GL (Fin 6) (ZMod 2)) = n24El 1 (Q d) := by
        rw [hFP d, htriv d]
      have hcommD (d e : ↥D) : d * e = e * d := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul, hd_one d, hd_one e, n24El_mul,
          n24El_mul]
        refine n24El_inj.mpr ⟨rfl, ?_⟩
        simp only [Units.val_one, Matrix.one_mul, Matrix.mul_one]
        exact add_comm _ _
      have hcommGL (A B : GL (Fin 3) (ZMod 2)) : A * B = B * A := by
        have h' := congrArg hD.some (hcommD (hD.some.symm A) (hD.some.symm B))
        simpa using h'
      have hne : n24A * n24B ≠ n24B * n24A := by
        intro heq
        have h00 := congrFun (congrFun (congrArg (fun g : GL (Fin 3) (ZMod 2) =>
          (g : Matrix (Fin 3) (Fin 3) (ZMod 2))) heq) 0) 0
        have hl : ((n24A * n24B : GL (Fin 3) (ZMod 2)) :
            Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 0 = 1 := by
          rw [Units.val_mul]
          decide
        have hr : ((n24B * n24A : GL (Fin 3) (ZMod 2)) :
            Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 0 = 0 := by
          rw [Units.val_mul]
          decide
        rw [hl, hr] at h00
        exact one_ne_zero h00
      exact hne (hcommGL n24A n24B)
  have hcard : Nat.card ↥D = 168 :=
    (Nat.card_congr hD.some.toEquiv).trans CFSG.ComponentClassification.GHarris.card_GL32_gh
  have hbij : Function.Bijective P :=
    hinj.bijective_of_nat_card_le
      (by rw [hcard, CFSG.ComponentClassification.GHarris.card_GL32_gh])
  have hsurj : Function.Surjective P := hbij.2
  let dA : GL (Fin 3) (ZMod 2) → ↥D := fun A => Classical.choose (hsurj A)
  have hdA (A : GL (Fin 3) (ZMod 2)) : P (dA A) = A := Classical.choose_spec (hsurj A)
  let q : GL (Fin 3) (ZMod 2) → N24Mat3 := fun A => Q (dA A)
  have hdAmul (A B : GL (Fin 3) (ZMod 2)) : dA (A * B) = dA A * dA B := by
    refine hinj ?_
    rw [hdA, map_mul, hdA, hdA]
  have hqmul (A B : GL (Fin 3) (ZMod 2)) :
      q (A * B) = (A : N24Mat3) * q B + q A * (B : N24Mat3) := by
    have h1 : ((dA (A * B) : ↥D) : GL (Fin 6) (ZMod 2)) =
        n24El (A * B) (q (A * B)) := by
      rw [hFP (dA (A * B)), hdA (A * B)]
    have h2 : ((dA (A * B) : ↥D) : GL (Fin 6) (ZMod 2)) =
        n24El (A * B) ((A : N24Mat3) * q B + q A * (B : N24Mat3)) := by
      have hAB : dA (A * B) = dA A * dA B := hdAmul A B
      rw [hAB, Subgroup.coe_mul, hFP (dA A), hFP (dA B), hdA A, hdA B, n24El_mul]
    exact (n24El_inj.mp (h1.symm.trans h2)).2
  let f : GL (Fin 3) (ZMod 2) → N24Mat3 := fun A =>
    q A * ((A⁻¹ : GL (Fin 3) (ZMod 2)) : N24Mat3)
  have hfdef (A : GL (Fin 3) (ZMod 2)) :
      f A = q A * ((A⁻¹ : GL (Fin 3) (ZMod 2)) : N24Mat3) := rfl
  have hf : ∀ A B : GL (Fin 3) (ZMod 2), f (A * B) = f A +
      (A : N24Mat3) * f B * ((A⁻¹ : GL (Fin 3) (ZMod 2)) : N24Mat3) := by
    intro A B
    calc
      f (A * B) = q (A * B) * (((A * B)⁻¹ : GL (Fin 3) (ZMod 2)) : N24Mat3) :=
        hfdef (A * B)
      _ = ((A : N24Mat3) * q B + q A * (B : N24Mat3)) *
            (((A * B)⁻¹ : GL (Fin 3) (ZMod 2)) : N24Mat3) := by rw [hqmul A B]
      _ = ((A : N24Mat3) * q B + q A * (B : N24Mat3)) *
            (((B⁻¹ : GL (Fin 3) (ZMod 2)) : N24Mat3) *
              ((A⁻¹ : GL (Fin 3) (ZMod 2)) : N24Mat3)) := by
            rw [_root_.mul_inv_rev, Units.val_mul]
      _ = ((A : N24Mat3) * q B) *
              (((B⁻¹ : GL (Fin 3) (ZMod 2)) : N24Mat3) *
                ((A⁻¹ : GL (Fin 3) (ZMod 2)) : N24Mat3)) +
            (q A * (B : N24Mat3)) *
              (((B⁻¹ : GL (Fin 3) (ZMod 2)) : N24Mat3) *
                ((A⁻¹ : GL (Fin 3) (ZMod 2)) : N24Mat3)) := by rw [add_mul]
      _ = ((A : N24Mat3) * (q B * ((B⁻¹ : GL (Fin 3) (ZMod 2)) : N24Mat3))) *
              ((A⁻¹ : GL (Fin 3) (ZMod 2)) : N24Mat3) +
            (q A * ((B : N24Mat3) * ((B⁻¹ : GL (Fin 3) (ZMod 2)) : N24Mat3))) *
              ((A⁻¹ : GL (Fin 3) (ZMod 2)) : N24Mat3) := by
            congr 1 <;> noncomm_ring
      _ = ((A : N24Mat3) * (q B * ((B⁻¹ : GL (Fin 3) (ZMod 2)) : N24Mat3))) *
              ((A⁻¹ : GL (Fin 3) (ZMod 2)) : N24Mat3) +
            q A * ((A⁻¹ : GL (Fin 3) (ZMod 2)) : N24Mat3) := by
            rw [Units.mul_inv B, Matrix.mul_one]
      _ = f A + (A : N24Mat3) * f B *
              ((A⁻¹ : GL (Fin 3) (ZMod 2)) : N24Mat3) := by
            rw [hfdef A, hfdef B]
            exact add_comm _ _
  obtain ⟨m, hm⟩ := y7c_n24_h1 f hf
  have hq_m (A : GL (Fin 3) (ZMod 2)) :
      q A = (A : N24Mat3) * m + m * (A : N24Mat3) := by
    have h2 : q A = ((A : N24Mat3) * m *
        ((A⁻¹ : GL (Fin 3) (ZMod 2)) : N24Mat3) + m) * (A : N24Mat3) := by
      calc
        q A = (q A * ((A⁻¹ : GL (Fin 3) (ZMod 2)) : N24Mat3)) * (A : N24Mat3) := by
          rw [mul_assoc, Units.inv_mul, Matrix.mul_one]
        _ = ((A : N24Mat3) * m *
              ((A⁻¹ : GL (Fin 3) (ZMod 2)) : N24Mat3) + m) * (A : N24Mat3) := by
            rw [← hfdef A, hm A]
    rw [h2, Matrix.add_mul]
    calc
      ((A : N24Mat3) * m * ((A⁻¹ : GL (Fin 3) (ZMod 2)) : N24Mat3)) *
            (A : N24Mat3) + m * (A : N24Mat3)
          = (A : N24Mat3) * m *
              (((A⁻¹ : GL (Fin 3) (ZMod 2)) : N24Mat3) * (A : N24Mat3)) +
            m * (A : N24Mat3) := by
            congr 1
            noncomm_ring
      _ = (A : N24Mat3) * m + m * (A : N24Mat3) := by
            rw [Units.inv_mul A, Matrix.mul_one]
  let u : GL (Fin 6) (ZMod 2) := n24El 1 m
  have hu_inv : u⁻¹ = u := by
    change (n24El 1 m)⁻¹ = n24El 1 m
    rw [n24El_inv]
    simp
  have hu_comm : u * z₀ = z₀ * u := by
    simpa only [u] using n24El_comm_z0 1 m
  have hconj (A : GL (Fin 3) (ZMod 2)) :
      u * (dA A : GL (Fin 6) (ZMod 2)) * u⁻¹ = dg A := by
    have hd : (dA A : GL (Fin 6) (ZMod 2)) = n24El A (q A) := by
      rw [hFP (dA A), hdA A]
    rw [hd, hu_inv, dg_eq_n24El]
    simp only [u]
    rw [n24El_mul, n24El_mul]
    refine n24El_inj.mpr ⟨by simp, ?_⟩
    simp only [Units.val_one, one_mul, mul_one, Matrix.one_mul, Matrix.mul_one]
    calc
      (A : N24Mat3) * m + (q A + m * (A : N24Mat3))
          = ((A : N24Mat3) * m + (A : N24Mat3) * m) +
              (m * (A : N24Mat3) + m * (A : N24Mat3)) := by
            rw [hq_m A]
            abel
      _ = 0 := by
            simp [n24_add_self]
  refine ⟨u, hu_comm, ?_⟩
  intro x
  constructor
  · intro hx
    have hxd : (dA (P ⟨x, hx⟩) : ↥D) = ⟨x, hx⟩ := by
      refine hinj ?_
      rw [hdA]
    have hxval : (dA (P ⟨x, hx⟩) : GL (Fin 6) (ZMod 2)) = x := by
      simpa using congrArg (fun d : ↥D => (d : GL (Fin 6) (ZMod 2))) hxd
    rw [← hxval, hconj]
    exact MonoidHom.mem_range.mpr ⟨P ⟨x, hx⟩, rfl⟩
  · intro hx
    obtain ⟨A, hA⟩ := MonoidHom.mem_range.mp hx
    have heq : u * (dA A : GL (Fin 6) (ZMod 2)) * u⁻¹ = u * x * u⁻¹ := by
      rw [hconj A, hA]
    have h1 : (dA A : GL (Fin 6) (ZMod 2)) * u⁻¹ = x * u⁻¹ := by
      have h' := congrArg (fun g : GL (Fin 6) (ZMod 2) => u⁻¹ * g) heq
      calc
        (dA A : GL (Fin 6) (ZMod 2)) * u⁻¹
            = u⁻¹ * (u * (dA A : GL (Fin 6) (ZMod 2)) * u⁻¹) := by group
        _ = u⁻¹ * (u * x * u⁻¹) := h'
        _ = x * u⁻¹ := by group
    have hxd : (dA A : GL (Fin 6) (ZMod 2)) = x := mul_right_cancel h1
    rw [← hxd]
    exact (dA A).2

end CFSG.OddStandard.HigherRank.YamadaG23
