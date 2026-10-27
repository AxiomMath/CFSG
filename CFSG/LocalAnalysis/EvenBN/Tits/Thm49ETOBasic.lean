module

public import CFSG.LocalAnalysis.EvenBN.Tits.Thm49ETOHyps

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.Thm49E

open Certificates.Thm49E CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native

variable {g ml : Array E} {ig : Array ℕ} {mact : Array (Array ℕ)}
  {steps psteps : Array (ℕ × ℕ × ℕ)} {cov : Array ℕ} {kg kl kinv : Array E}
  {kw : Array (List ℕ)} {kact : Array (Array ℕ)} {kconj : Array (Array E)} {ih0 ih1 : ℕ}
  {y0E y0iE : E} {zp y0 : Equiv.Perm (Fin 1755)} {s : Cm → Cm}

theorem SHyp.one (hs : SHyp zp s) : s 1 = 1 := by
  have h := hs.mul 1 GammaH.one_mem 1 GammaH.one_mem
  rw [mul_one] at h
  exact mul_left_cancel (h.symm.trans (mul_one _).symm)

theorem SHyp.inv (hs : SHyp zp s) {x : Cm} (hx : x ∈ GammaH) : s x⁻¹ = (s x)⁻¹ := by
  have h := hs.mul x hx x⁻¹ (GammaH.inv_mem hx)
  rw [mul_inv_cancel, hs.one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

private theorem tauH_comm (x : Cm) : tauH * x = x * tauH := by
  refine Prod.ext ?_ ?_
  · simp [tauH, mul_comm]
  · simp [tauH]

private theorem inA_mul_tob (a b : Equiv.Perm (Fin 1755)) : inA a * inA b = inA (a * b) := by
  refine Prod.ext ?_ rfl
  simp [inA]

private theorem inA_inv_tob (a : Equiv.Perm (Fin 1755)) : (inA a)⁻¹ = inA a⁻¹ := by
  refine Prod.ext ?_ rfl
  simp [inA]

private theorem inA_mem_Am_tob {a : Equiv.Perm (Fin 1755)} (ha : a ∈ titsA) : inA a ∈ Am :=
  Subgroup.mem_prod.2 ⟨Subgroup.mem_top _, ha⟩

private theorem inA_mem_gamma {a : Equiv.Perm (Fin 1755)} (ha : a ∈ titsA)
    (hc : titsZ * a = a * titsZ) : inA a ∈ GammaH := by
  refine Subgroup.mem_inf.2 ⟨inA_mem_Am_tob ha, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  rw [inA_mul_tob, inA_mul_tob, hc]

private theorem tauH_mem_gamma : tauH ∈ GammaH := by
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_prod.2 ⟨Subgroup.mem_top _, one_mem _⟩, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  exact (tauH_comm _).symm

private theorem R_mem_gamma (hF : F6Facts zp y0) : tauH * inA zp ∈ GammaH :=
  GammaH.mul_mem tauH_mem_gamma (inA_mem_gamma hF.zp_mem hF.zp_comm)

theorem SHyp.mem_KH (hF : F6Facts zp y0) (hs : SHyp zp s) {x : Cm} (hx : x ∈ KH zp) :
    s x ∈ KH zp := by
  obtain ⟨hxG, hxC⟩ := Subgroup.mem_inf.1 hx
  have hRG := R_mem_gamma hF
  refine Subgroup.mem_inf.2 ⟨hs.maps x hxG, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  have hc : tauH * inA zp * x = x * (tauH * inA zp) :=
    (Subgroup.mem_centralizer_iff.1 hxC) _ (Set.mem_singleton _)
  have h2 := congrArg s hc
  rw [hs.mul _ hRG _ hxG, hs.mul _ hxG _ hRG, hs.R] at h2
  exact h2

private theorem conj_comm_tob {u w a b : Cm} (hu : u⁻¹ * a * u = b) (hw : b * w = w * b) :
    a * (u * w * u⁻¹) = (u * w * u⁻¹) * a := by
  have ha : a = u * b * u⁻¹ := by
    rw [← hu]
    group
  subst ha
  calc u * b * u⁻¹ * (u * w * u⁻¹) = u * (b * w) * u⁻¹ := by group
    _ = u * (w * b) * u⁻¹ := by rw [hw]
    _ = u * w * u⁻¹ * (u * b * u⁻¹) := by group

theorem SHyp.theta_mem_KH (hF : F6Facts zp y0) (hs : SHyp zp s) {θ : Cm → Cm}
    (hθ : ∀ x, θ x = inA y0 * s x * (inA y0)⁻¹) {x : Cm} (hx : x ∈ KH zp) : θ x ∈ KH zp := by
  have hsx := hs.mem_KH hF hx
  obtain ⟨hsG, hsC⟩ := Subgroup.mem_inf.1 hsx
  obtain ⟨hsAm, hsZ⟩ := Subgroup.mem_inf.1 hsG
  have hZ : inA titsZ * s x = s x * inA titsZ :=
    (Subgroup.mem_centralizer_iff.1 hsZ) _ (Set.mem_singleton _)
  have hR : tauH * inA zp * s x = s x * (tauH * inA zp) :=
    (Subgroup.mem_centralizer_iff.1 hsC) _ (Set.mem_singleton _)
  have hZp : inA zp * s x = s x * inA zp := by
    apply mul_left_cancel (a := tauH)
    calc tauH * (inA zp * s x) = tauH * inA zp * s x := (mul_assoc _ _ _).symm
      _ = s x * (tauH * inA zp) := hR
      _ = s x * tauH * inA zp := (mul_assoc _ _ _).symm
      _ = tauH * s x * inA zp := by rw [tauH_comm (s x)]
      _ = tauH * (s x * inA zp) := mul_assoc _ _ _
  have hu1 : (inA y0)⁻¹ * inA titsZ * inA y0 = inA zp := by
    rw [inA_inv_tob, inA_mul_tob, inA_mul_tob]
    congr 1
    rw [← hF.y0_zp]
    group
  have hu2 : (inA y0)⁻¹ * inA zp * inA y0 = inA titsZ := by
    rw [inA_inv_tob, inA_mul_tob, inA_mul_tob]
    congr 1
    rw [← hF.y0_z]
    group
  have hc1 : inA titsZ * (inA y0 * s x * (inA y0)⁻¹) = (inA y0 * s x * (inA y0)⁻¹) * inA titsZ :=
    conj_comm_tob hu1 hZp
  have hc2 : inA zp * (inA y0 * s x * (inA y0)⁻¹) = (inA y0 * s x * (inA y0)⁻¹) * inA zp :=
    conj_comm_tob hu2 hZ
  rw [hθ x]
  have hAm : inA y0 * s x * (inA y0)⁻¹ ∈ Am :=
    Am.mul_mem (Am.mul_mem (inA_mem_Am_tob hF.y0_mem) hsAm) (Am.inv_mem (inA_mem_Am_tob hF.y0_mem))
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hAm, ?_⟩, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact hc1
  · rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    calc tauH * inA zp * (inA y0 * s x * (inA y0)⁻¹)
        = tauH * (inA zp * (inA y0 * s x * (inA y0)⁻¹)) := mul_assoc _ _ _
      _ = tauH * ((inA y0 * s x * (inA y0)⁻¹) * inA zp) := by rw [hc2]
      _ = (tauH * (inA y0 * s x * (inA y0)⁻¹)) * inA zp := (mul_assoc _ _ _).symm
      _ = ((inA y0 * s x * (inA y0)⁻¹) * tauH) * inA zp := by rw [tauH_comm]
      _ = (inA y0 * s x * (inA y0)⁻¹) * (tauH * inA zp) := mul_assoc _ _ _

end CFSG.LocalAnalysis.EvenBN.Tits.Thm49E
