module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y52Abs
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y52ExclD

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma mk'_conj_eq_of_mem {Q : Type} [Group Q] (N : Subgroup Q) [N.Normal] {x y : Q}
    (h : x * y * x⁻¹ * y⁻¹ ∈ N) :
    (QuotientGroup.mk' N) x * (QuotientGroup.mk' N) y * ((QuotientGroup.mk' N) x)⁻¹ =
      (QuotientGroup.mk' N) y := by
  have h1 : (QuotientGroup.mk' N) (x * y * x⁻¹ * y⁻¹) = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact h
  simp only [map_mul, map_inv] at h1
  exact mul_inv_eq_one.mp h1

theorem y52_excl {c : Ctx5 G L} (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T) :
    c.g * c.d ∉ c.s.C₂ := by
  intro hu
  obtain ⟨v, v', hvC, hv'C, hu2, hv2, hv'2, hcovG, huvv'G, hauG, havG, hav'G⟩ :=
    y52_excl_data hH hRT hu
  let X : Subgroup G := c.s.X
  let N0 : Subgroup G := y52N0 c.s
  have hN0leX : N0 ≤ X :=
    (y52_N0_le_P hH).trans ((f3_P_le_C₂ hH).trans (f3_C₂_le_X hH))
  haveI hN0normal : (N0.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff hN0leX).mpr
      (fun h k hh hk => y52_N0_normal hH k hk h hh)
  let π : ↥X →* (↥X ⧸ N0.subgroupOf X) := QuotientGroup.mk' (N0.subgroupOf X)
  have hπ1 : ∀ x : ↥X, π x = 1 ↔ (x : G) ∈ N0 := by
    intro x
    change QuotientGroup.mk' (N0.subgroupOf X) x = 1 ↔ (x : G) ∈ N0
    simp only [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hbC2 : y52b c.s ∈ c.s.C₂ := f3_P_le_C₂ hH (y52_b_mem_P hH)
  have hbX : y52b c.s ∈ X := f3_C₂_le_X hH hbC2
  have huX : c.g * c.d ∈ X := f3_C₂_le_X hH hu
  have hvX : v ∈ X := f3_C₂_le_X hH hvC
  have hv'X : v' ∈ X := f3_C₂_le_X hH hv'C
  have haX : y5a c.s ∈ X :=
    f3_N_le_X c.s (Subgroup.mem_inf.mpr
      ⟨s3_L_le_H c.s hH.hS (s3_S_le_L c.s (y5a_mem_S c.s)),
       (Subgroup.mem_inf.mp (y5a_mem_normB hH)).2⟩)
  let xa : ↥X := ⟨y5a c.s, haX⟩
  let xb : ↥X := ⟨y52b c.s, hbX⟩
  let xu : ↥X := ⟨c.g * c.d, huX⟩
  let xv : ↥X := ⟨v, hvX⟩
  let xv' : ↥X := ⟨v', hv'X⟩
  let C : Subgroup (↥X ⧸ N0.subgroupOf X) := (c.s.C₂.subgroupOf X).map π
  have hsq : ∀ x : ↥X, ((x : G) * (x : G) = 1) → π x * π x = 1 := by
    intro x h
    rw [← map_mul, show x * x = 1 from Subtype.ext h, map_one]
  have hb2 : π xb * π xb = 1 := hsq xb (y52_b_sq hH)
  have hu2q : π xu * π xu = 1 := hsq xu hu2
  have hv2q : π xv * π xv = 1 := hsq xv hv2
  have hv'2q : π xv' * π xv' = 1 := hsq xv' hv'2
  have ha2 : π xa * π xa = 1 := hsq xa (by simpa [pow_two] using y5a_sq hH)
  have hb1 : π xb ≠ 1 := fun h => y52_b_not_mem_N0 hH ((hπ1 xb).mp h)
  have hbC : π xb ∈ C := Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hbC2)
  have huC : π xu ∈ C := Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hu)
  have hvCin : π xv ∈ C := Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hvC)
  have hv'Cin : π xv' ∈ C := Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hv'C)
  have hbc : ∀ x ∈ C, x * π xb = π xb * x := by
    intro x hx
    obtain ⟨xw, hxw, rfl⟩ := Subgroup.mem_map.mp hx
    have hxwC2 : (xw : G) ∈ c.s.C₂ := Subgroup.mem_subgroupOf.mp hxw
    have hmem : xw * xb * xw⁻¹ * xb⁻¹ ∈ N0.subgroupOf X := by
      rw [Subgroup.mem_subgroupOf]
      change (xw : G) * y52b c.s * (xw : G)⁻¹ * (y52b c.s)⁻¹ ∈ y52N0 c.s
      exact y52_C₂_cent_b hH (xw : G) hxwC2
    have hconj : π xw * π xb * (π xw)⁻¹ = π xb :=
      mk'_conj_eq_of_mem (N0.subgroupOf X) hmem
    calc π xw * π xb = (π xw * π xb * (π xw)⁻¹) * π xw := by group
      _ = π xb * π xw := by rw [hconj]
  have hPcoset : ∀ (p : G) (hpX : p ∈ X), p ∈ f3P c.s →
      π ⟨p, hpX⟩ = 1 ∨ π ⟨p, hpX⟩ = π xb := by
    intro p hpX hp
    rcases y52_P_two_cosets hH p hp with hpN0 | hbpN0
    · exact Or.inl ((hπ1 ⟨p, hpX⟩).mpr hpN0)
    · have hbp : π xb * π ⟨p, hpX⟩ = 1 := by
        have h1 : π (xb * ⟨p, hpX⟩) = 1 := (hπ1 (xb * ⟨p, hpX⟩)).mpr hbpN0
        rwa [map_mul] at h1
      exact Or.inr (mul_left_cancel (hbp.trans hb2.symm))
  have hcov : ∀ x ∈ C, ∃ i : ℕ,
      ∃ y ∈ ({1, π xu, π xv, π xv'} : Set (↥X ⧸ N0.subgroupOf X)),
        x = (π xb) ^ i * y := by
    intro x hx
    obtain ⟨xw, hxw, rfl⟩ := Subgroup.mem_map.mp hx
    have hxwC2 : (xw : G) ∈ c.s.C₂ := Subgroup.mem_subgroupOf.mp hxw
    obtain ⟨p, hpP, hp | hp | hp | hp⟩ := hcovG (xw : G) hxwC2
    · have hpX : p ∈ X := f3_C₂_le_X hH (f3_P_le_C₂ hH hpP)
      rw [show xw = (⟨p, hpX⟩ : ↥X) from Subtype.ext hp]
      rcases hPcoset p hpX hpP with h1 | hb'
      · exact ⟨0, 1, by simp, by rw [h1]; simp⟩
      · exact ⟨1, 1, by simp, by rw [hb']; simp⟩
    · have hpX : p ∈ X := f3_C₂_le_X hH (f3_P_le_C₂ hH hpP)
      rw [show xw = (⟨p, hpX⟩ : ↥X) * xu from Subtype.ext hp, map_mul]
      rcases hPcoset p hpX hpP with h1 | hb'
      · exact ⟨0, π xu, by simp, by rw [h1]; simp⟩
      · exact ⟨1, π xu, by simp, by rw [hb']; simp⟩
    · have hpX : p ∈ X := f3_C₂_le_X hH (f3_P_le_C₂ hH hpP)
      rw [show xw = (⟨p, hpX⟩ : ↥X) * xv from Subtype.ext hp, map_mul]
      rcases hPcoset p hpX hpP with h1 | hb'
      · exact ⟨0, π xv, by simp, by rw [h1]; simp⟩
      · exact ⟨1, π xv, by simp, by rw [hb']; simp⟩
    · have hpX : p ∈ X := f3_C₂_le_X hH (f3_P_le_C₂ hH hpP)
      rw [show xw = (⟨p, hpX⟩ : ↥X) * xv' from Subtype.ext hp, map_mul]
      rcases hPcoset p hpX hpP with h1 | hb'
      · exact ⟨0, π xv', by simp, by rw [h1]; simp⟩
      · exact ⟨1, π xv', by simp, by rw [hb']; simp⟩
  have huvv' : π xu * π xv * π xv' = 1 ∨ π xu * π xv * π xv' = π xb := by
    have hqX : (c.g * c.d) * v * v' ∈ X := f3_C₂_le_X hH (f3_P_le_C₂ hH huvv'G)
    have hqeq : π (⟨(c.g * c.d) * v * v', hqX⟩ : ↥X) = π xu * π xv * π xv' := by
      rw [show (⟨(c.g * c.d) * v * v', hqX⟩ : ↥X) = xu * xv * xv' from Subtype.ext rfl,
        map_mul, map_mul]
    rcases hPcoset ((c.g * c.d) * v * v') hqX huvv'G with h1 | hb'
    · exact Or.inl (by rw [← hqeq, h1])
    · exact Or.inr (by rw [← hqeq, hb'])
  have hau : π xa * π xu * (π xa)⁻¹ = π xb * π xu := by
    have h1 : (xa * xu * xa⁻¹ : ↥X) = xb * xu := Subtype.ext hauG
    have h2 := congrArg π h1
    simpa only [map_mul, map_inv] using h2
  have hab : π xa * π xb * (π xa)⁻¹ = π xb := by
    have hmem : xa * xb * xa⁻¹ * xb⁻¹ ∈ N0.subgroupOf X := by
      rw [Subgroup.mem_subgroupOf]
      change y5a c.s * y52b c.s * (y5a c.s)⁻¹ * (y52b c.s)⁻¹ ∈ y52N0 c.s
      exact y52_a_b hH
    exact mk'_conj_eq_of_mem (N0.subgroupOf X) hmem
  have hact : ∀ (w w' : ↥X),
      (y5a c.s * (w : G) * (y5a c.s)⁻¹ * (w' : G)⁻¹ ∈ f3P c.s) →
      π xa * π w * (π xa)⁻¹ = π w' ∨ π xa * π w * (π xa)⁻¹ = π xb * π w' := by
    intro w w' h
    have hrX : y5a c.s * (w : G) * (y5a c.s)⁻¹ * (w' : G)⁻¹ ∈ X :=
      f3_C₂_le_X hH (f3_P_le_C₂ hH h)
    have hreq : π (⟨y5a c.s * (w : G) * (y5a c.s)⁻¹ * (w' : G)⁻¹, hrX⟩ : ↥X) =
        π xa * π w * (π xa)⁻¹ * (π w')⁻¹ := by
      rw [show (⟨y5a c.s * (w : G) * (y5a c.s)⁻¹ * (w' : G)⁻¹, hrX⟩ : ↥X) =
          xa * w * xa⁻¹ * w'⁻¹ from Subtype.ext rfl]
      simp only [map_mul, map_inv]
    rcases hPcoset (y5a c.s * (w : G) * (y5a c.s)⁻¹ * (w' : G)⁻¹) hrX h with h1 | hb'
    · have h2 : π xa * π w * (π xa)⁻¹ * (π w')⁻¹ = 1 := by rw [← hreq, h1]
      exact Or.inl (mul_inv_eq_one.mp h2)
    · have h2 : π xa * π w * (π xa)⁻¹ * (π w')⁻¹ = π xb := by rw [← hreq, hb']
      exact Or.inr (by rw [← h2]; group)
  have hav : π xa * π xv * (π xa)⁻¹ = π xv' ∨ π xa * π xv * (π xa)⁻¹ = π xb * π xv' :=
    hact xv xv' havG
  have hav' : π xa * π xv' * (π xa)⁻¹ = π xv ∨ π xa * π xv' * (π xa)⁻¹ = π xb * π xv :=
    hact xv' xv hav'G
  exact y52_abs C (π xb) (π xu) (π xv) (π xv') (π xa)
    hb1 hb2 hbC hbc huC hvCin hv'Cin hu2q hv2q hv'2q hcov huvv' ha2 hab hau hav hav'

end CFSG.OddStandard.HigherRank.YamadaG23
