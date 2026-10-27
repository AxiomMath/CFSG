module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11SingleXChi
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11SingleXDihA

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

namespace S11sCtx

variable {G : Type} [Group G] [Finite G] {t z : G} {K1 K2 T R : Subgroup G}
  {ρ : ↥R →* MulAut ↥(K1 ⊔ K2)} {a x : G} (c : S11sCtx t z K1 K2 T R ρ a x)

include c

theorem caseA_sigma {s σ : G} (hsR : s ∈ R) (ha : a ∈ R) (hσ : σ = a * s * a⁻¹) (hσR : σ ∈ R)
    (hA : ∀ y ∈ K1.subgroupOf (K1 ⊔ K2), ρ ⟨s, hsR⟩ y ∈ K1.subgroupOf (K1 ⊔ K2))
    (hB : ∀ y ∈ K2.subgroupOf (K1 ⊔ K2), ρ ⟨s, hsR⟩ y = y) :
    (∀ y ∈ K1.subgroupOf (K1 ⊔ K2), ρ ⟨σ, hσR⟩ y = y) ∧
      ρ ⟨s, hsR⟩ * ρ ⟨σ, hσR⟩ = ρ ⟨σ, hσR⟩ * ρ ⟨s, hsR⟩ := by
  have hσ_eq : (⟨σ, hσR⟩ : ↥R) = ⟨a, ha⟩ * ⟨s, hsR⟩ * (⟨a, ha⟩ : ↥R)⁻¹ := by
    apply Subtype.ext
    show σ = ↑(⟨a, ha⟩ * ⟨s, hsR⟩ * (⟨a, ha⟩ : ↥R)⁻¹)
    rw [hσ]
    simp [Subgroup.coe_mul, Subgroup.coe_inv]
  have hρσ : ρ ⟨σ, hσR⟩ = ρ ⟨a, ha⟩ * ρ ⟨s, hsR⟩ * (ρ ⟨a, ha⟩)⁻¹ := by
    rw [hσ_eq, map_mul, map_mul, map_inv]
  have hαinv : (ρ ⟨a, ha⟩)⁻¹ = ρ ⟨a, ha⟩ :=
    inv_eq_of_mul_eq_one_right (c.rho_a_sq ha)
  have hαα : ∀ y, ρ ⟨a, ha⟩ (ρ ⟨a, ha⟩ y) = y := by
    intro y
    have h := congrArg (fun f : MulAut ↥(K1 ⊔ K2) => f y) (c.rho_a_sq ha)
    simpa [MulAut.mul_apply, MulAut.one_apply] using h
  have hφA : ∀ y ∈ K1.subgroupOf (K1 ⊔ K2), ρ ⟨σ, hσR⟩ y = y := by
    intro y hy
    have hyB : ρ ⟨a, ha⟩ y ∈ K2.subgroupOf (K1 ⊔ K2) := c.rho_a12 ha y hy
    have h1 : ρ ⟨s, hsR⟩ (ρ ⟨a, ha⟩ y) = ρ ⟨a, ha⟩ y := hB _ hyB
    calc ρ ⟨σ, hσR⟩ y = (ρ ⟨a, ha⟩ * ρ ⟨s, hsR⟩ * (ρ ⟨a, ha⟩)⁻¹) y := by rw [hρσ]
      _ = ρ ⟨a, ha⟩ (ρ ⟨s, hsR⟩ ((ρ ⟨a, ha⟩)⁻¹ y)) := by
            rw [MulAut.mul_apply, MulAut.mul_apply]
      _ = ρ ⟨a, ha⟩ (ρ ⟨s, hsR⟩ (ρ ⟨a, ha⟩ y)) := by rw [hαinv]
      _ = ρ ⟨a, ha⟩ (ρ ⟨a, ha⟩ y) := by rw [h1]
      _ = y := hαα y
  have hφB : ∀ y ∈ K2.subgroupOf (K1 ⊔ K2),
      ρ ⟨σ, hσR⟩ y ∈ K2.subgroupOf (K1 ⊔ K2) := by
    intro y hy
    have hyA : ρ ⟨a, ha⟩ y ∈ K1.subgroupOf (K1 ⊔ K2) := c.rho_a21 ha y hy
    have h1 : ρ ⟨s, hsR⟩ (ρ ⟨a, ha⟩ y) ∈ K1.subgroupOf (K1 ⊔ K2) := hA _ hyA
    have h2 : ρ ⟨a, ha⟩ (ρ ⟨s, hsR⟩ (ρ ⟨a, ha⟩ y)) ∈ K2.subgroupOf (K1 ⊔ K2) :=
      c.rho_a12 ha _ h1
    have h3 : ρ ⟨σ, hσR⟩ y = ρ ⟨a, ha⟩ (ρ ⟨s, hsR⟩ ((ρ ⟨a, ha⟩)⁻¹ y)) := by
      rw [hρσ, MulAut.mul_apply, MulAut.mul_apply]
    rw [h3, hαinv]
    exact h2
  refine ⟨hφA, ?_⟩
  apply MulEquiv.ext
  intro k
  obtain ⟨y1, hy1, y2, hy2, rfl⟩ := c.pair.exists_mul k
  simp only [MulAut.mul_apply, map_mul]
  rw [hφA y1 hy1, hB _ (hφB y2 hy2), hφA _ (hA y1 hy1), hB y2 hy2]

theorem caseA_sq_mem_D {s σ : G} (hsR : s ∈ R) (hs2 : s * s = 1) (ha : a ∈ R)
    (hσ : σ = a * s * a⁻¹) (hσR : σ ∈ R)
    (hA : ∀ y ∈ K1.subgroupOf (K1 ⊔ K2), ρ ⟨s, hsR⟩ y ∈ K1.subgroupOf (K1 ⊔ K2))
    (hB : ∀ y ∈ K2.subgroupOf (K1 ⊔ K2), ρ ⟨s, hsR⟩ y = y) :
    s * σ * (s * σ) ∈ secD K1 K2 R := by
  have hσ2 : σ * σ = 1 := by
    rw [hσ]
    calc a * s * a⁻¹ * (a * s * a⁻¹) = a * (s * s) * a⁻¹ := by group
      _ = 1 := by rw [hs2]; group
  have hψψ : ρ ⟨s, hsR⟩ * ρ ⟨s, hsR⟩ = 1 := by
    have h1 : (⟨s, hsR⟩ : ↥R) * ⟨s, hsR⟩ = 1 := Subtype.ext (by simpa using hs2)
    rw [← map_mul ρ, h1, map_one ρ]
  have hφφ : ρ ⟨σ, hσR⟩ * ρ ⟨σ, hσR⟩ = 1 := by
    have h1 : (⟨σ, hσR⟩ : ↥R) * ⟨σ, hσR⟩ = 1 := Subtype.ext (by simpa using hσ2)
    rw [← map_mul ρ, h1, map_one ρ]
  have hcomm := (c.caseA_sigma hsR ha hσ hσR hA hB).2
  have hprod : (ρ ⟨s, hsR⟩ * ρ ⟨σ, hσR⟩) * (ρ ⟨s, hsR⟩ * ρ ⟨σ, hσR⟩) = 1 := by
    calc (ρ ⟨s, hsR⟩ * ρ ⟨σ, hσR⟩) * (ρ ⟨s, hsR⟩ * ρ ⟨σ, hσR⟩)
        = ρ ⟨s, hsR⟩ * (ρ ⟨σ, hσR⟩ * ρ ⟨s, hsR⟩) * ρ ⟨σ, hσR⟩ := by group
      _ = ρ ⟨s, hsR⟩ * (ρ ⟨s, hsR⟩ * ρ ⟨σ, hσR⟩) * ρ ⟨σ, hσR⟩ := by rw [← hcomm]
      _ = (ρ ⟨s, hsR⟩ * ρ ⟨s, hsR⟩) * (ρ ⟨σ, hσR⟩ * ρ ⟨σ, hσR⟩) := by group
      _ = 1 := by rw [hψψ, hφφ, one_mul]
  have hxx : ρ (⟨s, hsR⟩ * ⟨σ, hσR⟩ * (⟨s, hsR⟩ * ⟨σ, hσR⟩)) =
      (ρ ⟨s, hsR⟩ * ρ ⟨σ, hσR⟩) * (ρ ⟨s, hsR⟩ * ρ ⟨σ, hσR⟩) := by
    simp only [map_mul]
  have hy : ((⟨s, hsR⟩ * ⟨σ, hσR⟩ * (⟨s, hsR⟩ * ⟨σ, hσR⟩) : ↥R) : G) =
      s * σ * (s * σ) := by
    simp [Subgroup.coe_mul]
  rw [← hy]
  exact c.mem_D (⟨s, hsR⟩ * ⟨σ, hσR⟩ * (⟨s, hsR⟩ * ⟨σ, hσR⟩))
    (by rw [hxx]; exact hprod)

theorem caseA_star1 {h s σ : G} (hh : h ∈ centralizer ({z} : Set G)) (hs : s = h⁻¹ * t * h)
    (hσR : σ ∈ R) (hσ2 : σ * σ = 1) :
    σ * s * σ * s = s * (σ * s * σ) → σ * s * σ = s ∨ σ * s * σ = s * z := by
  intro hc
  have hh' : h * σ ∈ centralizer ({z} : Set G) := mul_mem hh (c.R_H hσR)
  have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ2
  have hconj : (h * σ)⁻¹ * t * (h * σ) = σ * s * σ := by
    calc (h * σ)⁻¹ * t * (h * σ) = σ⁻¹ * (h⁻¹ * t * h) * σ := by group
      _ = σ * (h⁻¹ * t * h) * σ := by rw [hσinv]
      _ = σ * s * σ := by rw [← hs]
  have hstar : ((h * σ)⁻¹ * t * (h * σ)) * (h⁻¹ * t * h)
      = (h⁻¹ * t * h) * ((h * σ)⁻¹ * t * (h * σ)) := by
    rw [hconj, ← hs]
    exact hc
  rcases c.star h hh (h * σ) hh' hstar with hcase | hcase
  · left
    rw [hconj, ← hs] at hcase
    exact hcase
  · right
    rw [hconj, ← hs] at hcase
    exact hcase

theorem caseA_star2 {h s σ b : G} (hh : h ∈ centralizer ({z} : Set G)) (hs : s = h⁻¹ * t * h)
    (hsR : s ∈ R) (ha : a ∈ R) (hσ : σ = a * s * a⁻¹) (hσR : σ ∈ R) (hb : b ∈ twoCoreIn K1)
    (hsb : s * b * s⁻¹ * b⁻¹ ∉ zpowers z)
    (hσA : ∀ y ∈ K1.subgroupOf (K1 ⊔ K2), ρ ⟨σ, hσR⟩ y = y) :
    ∀ d ∈ secD K1 K2 R, d⁻¹ * σ * d * s ≠ s * (d⁻¹ * σ * d) := by
  intro d hd heq
  have hh'' : h * a⁻¹ * d ∈ centralizer ({z} : Set G) :=
    mul_mem (mul_mem hh (c.R_H (R.inv_mem ha))) (c.R_H hd.2)
  have hconj'' : (h * a⁻¹ * d)⁻¹ * t * (h * a⁻¹ * d) = d⁻¹ * σ * d := by
    calc (h * a⁻¹ * d)⁻¹ * t * (h * a⁻¹ * d)
        = d⁻¹ * a * (h⁻¹ * t * h) * a⁻¹ * d := by group
      _ = d⁻¹ * a * s * a⁻¹ * d := by rw [← hs]
      _ = d⁻¹ * (a * s * a⁻¹) * d := by group
      _ = d⁻¹ * σ * d := by rw [← hσ]
  have hstar : ((h * a⁻¹ * d)⁻¹ * t * (h * a⁻¹ * d)) * (h⁻¹ * t * h)
      = (h⁻¹ * t * h) * ((h * a⁻¹ * d)⁻¹ * t * (h * a⁻¹ * d)) := by
    rw [hconj'', ← hs]
    exact heq
  have hcase' : d⁻¹ * σ * d = s ∨ d⁻¹ * σ * d = s * z := by
    rcases c.star h hh (h * a⁻¹ * d) hh'' hstar with hcase | hcase
    · left
      rw [hconj'', ← hs] at hcase
      exact hcase
    · right
      rw [hconj'', ← hs] at hcase
      exact hcase
  have hmem : d⁻¹ * σ * d ∈ R := R.mul_mem (R.mul_mem (R.inv_mem hd.2) hσR) hd.2
  have hdconj : ρ ((⟨d, hd.2⟩ : ↥R)⁻¹ * ⟨σ, hσR⟩ * ⟨d, hd.2⟩) = ρ ⟨σ, hσR⟩ := by
    rw [map_mul, map_mul, map_inv, c.rho_D ⟨d, hd.2⟩ hd, inv_one, one_mul, mul_one]
  have hdconj' : ρ ⟨d⁻¹ * σ * d, hmem⟩ = ρ ⟨σ, hσR⟩ := by
    have hel : (⟨d⁻¹ * σ * d, hmem⟩ : ↥R)
        = (⟨d, hd.2⟩ : ↥R)⁻¹ * ⟨σ, hσR⟩ * ⟨d, hd.2⟩ :=
      Subtype.ext (by simp [Subgroup.coe_mul, Subgroup.coe_inv])
    rw [hel, hdconj]
  have hszR : s * z ∈ R := R.mul_mem hsR c.z_D.2
  have hsz_rho : ρ ⟨s * z, hszR⟩ = ρ ⟨s, hsR⟩ := by
    have hel : (⟨s * z, hszR⟩ : ↥R) = ⟨s, hsR⟩ * ⟨z, c.z_D.2⟩ :=
      Subtype.ext (by simp)
    rw [hel, map_mul, c.rho_D ⟨z, c.z_D.2⟩ c.z_D, mul_one]
  have hφψ : ρ ⟨σ, hσR⟩ = ρ ⟨s, hsR⟩ := by
    rcases hcase' with hcase | hcase
    · have hel : (⟨d⁻¹ * σ * d, hmem⟩ : ↥R) = ⟨s, hsR⟩ := Subtype.ext hcase
      rw [← hdconj', hel]
    · have hel : (⟨d⁻¹ * σ * d, hmem⟩ : ↥R) = ⟨s * z, hszR⟩ := Subtype.ext hcase
      rw [← hdconj', hel, hsz_rho]
  set b' : ↥(K1 ⊔ K2) := ⟨b, Subgroup.mem_sup_left (twoCoreIn_le_self K1 hb)⟩ with hb'def
  have hb'A : b' ∈ K1.subgroupOf (K1 ⊔ K2) :=
    Subgroup.mem_subgroupOf.mpr (twoCoreIn_le_self K1 hb)
  have hφb : ρ ⟨σ, hσR⟩ b' = b' := hσA b' hb'A
  have hψb : ((ρ ⟨s, hsR⟩ b' : ↥(K1 ⊔ K2)) : G) = s * b * s⁻¹ := by
    have h := c.rho_Q ⟨s, hsR⟩ b' (c.Q1_le_Q hb)
    simpa [hb'def] using h
  have hsb_eq : s * b * s⁻¹ = b := by
    have h1 : ρ ⟨s, hsR⟩ b' = b' := by rw [← hφψ]; exact hφb
    calc s * b * s⁻¹ = ((ρ ⟨s, hsR⟩ b' : ↥(K1 ⊔ K2)) : G) := hψb.symm
      _ = (b' : G) := congrArg (fun y : ↥(K1 ⊔ K2) => (y : G)) h1
      _ = b := by rw [hb'def]
  exact hsb (by simpa [hsb_eq] using (Subgroup.one_mem (zpowers z)))

theorem caseA {h s b : G} (hh : h ∈ centralizer ({z} : Set G)) (hs : s = h⁻¹ * t * h)
    (hsR : s ∈ R) (hb : b ∈ twoCoreIn K1) (hsb : s * b * s⁻¹ * b⁻¹ ∉ zpowers z)
    (hA : ∀ y ∈ K1.subgroupOf (K1 ⊔ K2), ρ ⟨s, hsR⟩ y ∈ K1.subgroupOf (K1 ⊔ K2))
    (hB : ∀ y ∈ K2.subgroupOf (K1 ⊔ K2), ρ ⟨s, hsR⟩ y = y)
    (hsign : Equiv.Perm.sign (c.pair.theta (ρ ⟨s, hsR⟩)) = -1) : False := by
  have hs2 : s * s = 1 := by
    rw [hs]
    calc h⁻¹ * t * h * (h⁻¹ * t * h) = h⁻¹ * (t * t) * h := by group
      _ = 1 := by rw [c.t_sq]; group
  have hsTD : s ∉ T ⊔ secD K1 K2 R := by
    intro hmem
    have h1 := c.sign_TD hsR hmem
    rw [hsign] at h1
    exact (by decide : (-1 : ℤˣ) ≠ 1) h1
  have ha : a ∈ R := c.T_R c.a_T
  obtain ⟨σ, hσ⟩ : ∃ σ : G, σ = a * s * a⁻¹ := ⟨_, rfl⟩
  have hσR : σ ∈ R := by
    rw [hσ]
    exact R.mul_mem (R.mul_mem ha hsR) (R.inv_mem ha)
  have hσ2 : σ * σ = 1 := by
    rw [hσ]
    calc a * s * a⁻¹ * (a * s * a⁻¹) = a * (s * s) * a⁻¹ := by group
      _ = 1 := by rw [hs2]; group
  have hσTD : σ ∉ T ⊔ secD K1 K2 R := by
    intro hmem
    apply hsTD
    have haTD : a ∈ T ⊔ secD K1 K2 R := Subgroup.mem_sup_left c.a_T
    have hmem' : a⁻¹ * σ * a ∈ T ⊔ secD K1 K2 R :=
      mul_mem (mul_mem (inv_mem haTD) hmem) haTD
    have hs_eq : s = a⁻¹ * σ * a := by rw [hσ]; group
    rwa [hs_eq]
  obtain ⟨hDs, w, hw, hw4⟩ := c.dih s hsR hsTD
  obtain ⟨hDσ, -⟩ := c.dih σ hσR hσTD
  have hwD : w ∈ secD K1 K2 R := ⟨hw.1, c.T_R hw.2⟩
  have haw : a * w = w * a := c.a_CTQ w hw
  obtain ⟨hσA, -⟩ := c.caseA_sigma hsR ha hσ hσR hA hB
  have hcD := c.caseA_sq_mem_D hsR hs2 ha hσ hσR hA hB
  have hac : a * (s * σ * (s * σ)) * a⁻¹ = (s * σ * (s * σ))⁻¹ := by
    have has : a * s * a⁻¹ = σ := hσ.symm
    have haσ : a * σ * a⁻¹ = s := by
      rw [hσ, inv_eq_of_mul_eq_one_right c.a_sq]
      calc a * (a * s * a) * a = (a * a) * s * (a * a) := by group
        _ = s := by rw [c.a_sq]; group
    calc a * (s * σ * (s * σ)) * a⁻¹
        = (a * s * a⁻¹) * (a * σ * a⁻¹) * (a * s * a⁻¹) * (a * σ * a⁻¹) := by group
      _ = σ * s * σ * s := by rw [has, haσ]
      _ = (s * σ * (s * σ))⁻¹ := by
            have h : (s * σ * (s * σ))⁻¹ = σ * s * σ * s := by
              simp only [mul_inv_rev, inv_eq_of_mul_eq_one_right hs2,
                inv_eq_of_mul_eq_one_right hσ2]
              group
            exact h.symm
  exact s11s_caseA_core c.t_sq hs2 hσ2 hDσ hDs c.D2 hwD hw4 haw hcD hac c.z_D
    (fun d hd => c.z_comm_D hd)
    (c.caseA_star1 hh hs hσR hσ2)
    (c.caseA_star2 hh hs hsR ha hσ hσR hb hsb hσA)

end S11sCtx

end CFSG.OddStandard.SmallF3.Omega
