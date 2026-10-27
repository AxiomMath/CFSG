module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13a3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13aS3c

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private theorem conj_eq_of_comm {g x : G} (h : g * x = x * g) : g * x * g⁻¹ = x := by
  rw [h, mul_assoc, mul_inv_cancel, mul_one]

private theorem conj_inv_eq {g x : G} (h : g * x = x * g) : g * x⁻¹ * g⁻¹ = x⁻¹ := by
  have hx : g * x * g⁻¹ = x := conj_eq_of_comm h
  calc g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    _ = x⁻¹ := by rw [hx]

private theorem q13a_tau_centralizes_A (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ∀ a ∈ q13A t tau x₁ x₂ rho, tau * a * tau⁻¹ = a := by
  intro a ha
  have hcomm : a * tau = tau * a :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp ha).2
  rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]

private theorem q13a_om_t_aux (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    om * t = t * tau * om := by
  have hom_inv : om⁻¹ = om := inv_eq_of_mul_eq_one_right h.om_sq
  have h1 : om * t * om = t * tau := by simpa [hom_inv] using h.t_om
  have h2 : (om * t * om) * om = om * t := by rw [mul_assoc, h.om_sq, mul_one]
  rw [← h2, h1]

private theorem q13a_tom_sq_aux (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    (t * om) * (t * om) = tau := by
  have ht2 : t * t = 1 := q13a_t_mul_self h
  calc (t * om) * (t * om) = t * (om * t) * om := by group
    _ = t * (t * tau * om) * om := by rw [q13a_om_t_aux h]
    _ = (t * t) * tau * (om * om) := by group
    _ = tau := by rw [ht2, h.om_sq]; group

private theorem q13a_tom_cube_aux (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    (t * om) * (t * om) * (t * om) = t * om * tau := by
  have hsq : (t * om) * (t * om) = tau := q13a_tom_sq_aux h
  have hcomm : tau * (t * om) = (t * om) * tau := by
    have htτ : t * tau = tau * t := (q13a_t_comm h).2.2
    have homτ : om * tau = tau * om := (q13a_om_comm h).1
    calc tau * (t * om) = tau * t * om := by rw [mul_assoc]
      _ = t * tau * om := by rw [htτ]
      _ = t * (tau * om) := by rw [mul_assoc]
      _ = t * (om * tau) := by rw [homτ]
      _ = (t * om) * tau := by rw [mul_assoc]
  calc (t * om) * (t * om) * (t * om) = tau * (t * om) := by rw [hsq]
    _ = (t * om) * tau := hcomm

theorem q13a_t_inv_A (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ∀ a ∈ q13A t tau x₁ x₂ rho, t * a * t⁻¹ = a⁻¹ := by
  have hA : IsZ4pow 2 (q13A t tau x₁ x₂ rho) := q13a_A_iso h
  have hr : rho ∈ normalizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) :=
    Subgroup.mem_normalizer_fintype (fun a ha => (q13a_A_inv h a ha).1)
  have hl : lam ∈ normalizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) :=
    Subgroup.mem_normalizer_fintype (fun a ha => (q13a_A_inv h a ha).2.1)
  have hp : t ∈ normalizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) :=
    Subgroup.mem_normalizer_fintype (fun a ha => q13a_t_norm_A h a ha)
  have hfpf : ∀ a ∈ q13A t tau x₁ x₂ rho, rho * a * rho⁻¹ = a → a = 1 := by
    intro a ha hfix
    exact l12_cent_Q_rho h.c11 a (Subgroup.mem_inf.mp ha).1
      (mul_inv_eq_iff_eq_mul.mp hfix).symm
  have hpr : ∀ a ∈ q13A t tau x₁ x₂ rho,
      t * (rho * a * rho⁻¹) * t⁻¹ = rho * (t * a * t⁻¹) * rho⁻¹ := by
    intro a ha
    have htr : t * rho = rho * t := (q13a_t_comm h).2.1
    have hfac : t * (rho * a * rho⁻¹) * t⁻¹
        = (t * rho * t⁻¹) * (t * a * t⁻¹) * (t * rho⁻¹ * t⁻¹) := by group
    rw [hfac, conj_eq_of_comm htr, conj_inv_eq htr]
  have hpl : ∀ a ∈ q13A t tau x₁ x₂ rho,
      t * (lam * a * lam⁻¹) * t⁻¹ = lam * (t * a * t⁻¹) * lam⁻¹ := by
    intro a ha
    have htl : t * lam = lam * t := (q13a_t_comm h).1
    have hfac : t * (lam * a * lam⁻¹) * t⁻¹
        = (t * lam * t⁻¹) * (t * a * t⁻¹) * (t * lam⁻¹ * t⁻¹) := by group
    rw [hfac, conj_eq_of_comm htl, conj_inv_eq htl]
  rcases s3_dichotomy (A := q13A t tau x₁ x₂ rho) hA hr hl hp (q13a_rho_cube h) hfpf
    h.c11.lam_rho hpr hpl with hid | hinv
  · exfalso
    have hAle : q13A t tau x₁ x₂ rho ≤ baseGrp x₁ x₂ := by
      intro a ha
      have haQ : a ∈ ctxQ t tau x₁ x₂ rho := (Subgroup.mem_inf.mp ha).1
      have hacent : a ∈ centralizer ({t} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (mul_inv_eq_iff_eq_mul.mp (hid a ha)).symm
      have : a ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) := ⟨haQ, hacent⟩
      rwa [l12_CQ_t h.c11] at this
    have hcardA : Nat.card ↥(q13A t tau x₁ x₂ rho) = 16 := by
      rw [q13a_card_A h]; norm_num
    have hcardB : Nat.card ↥(baseGrp x₁ x₂) = 16 := (h.c11.wreath.baseGrp_eq).2.2
    have hEq : q13A t tau x₁ x₂ rho = baseGrp x₁ x₂ :=
      Subgroup.eq_of_le_of_card_ge hAle (by rw [hcardA, hcardB])
    exact q13a_x₁_not_mem_A h (hEq ▸ (Subgroup.subset_closure (by simp)))
  · exact hinv

theorem q13a_om_dich (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    (∀ a ∈ q13A t tau x₁ x₂ rho, om * a * om⁻¹ = a) ∨
      (∀ a ∈ q13A t tau x₁ x₂ rho, om * a * om⁻¹ = a⁻¹) := by
  have hA : IsZ4pow 2 (q13A t tau x₁ x₂ rho) := q13a_A_iso h
  have hr : rho ∈ normalizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) :=
    Subgroup.mem_normalizer_fintype (fun a ha => (q13a_A_inv h a ha).1)
  have hl : lam ∈ normalizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) :=
    Subgroup.mem_normalizer_fintype (fun a ha => (q13a_A_inv h a ha).2.1)
  have hp : om ∈ normalizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) :=
    Subgroup.mem_normalizer_fintype (fun a ha => (q13a_A_inv h a ha).2.2)
  have hfpf : ∀ a ∈ q13A t tau x₁ x₂ rho, rho * a * rho⁻¹ = a → a = 1 := by
    intro a ha hfix
    exact l12_cent_Q_rho h.c11 a (Subgroup.mem_inf.mp ha).1
      (mul_inv_eq_iff_eq_mul.mp hfix).symm
  have hpr : ∀ a ∈ q13A t tau x₁ x₂ rho,
      om * (rho * a * rho⁻¹) * om⁻¹ = rho * (om * a * om⁻¹) * rho⁻¹ := by
    intro a ha
    have homr : om * rho = rho * om := (q13a_om_comm h).2.1
    have hfac : om * (rho * a * rho⁻¹) * om⁻¹
        = (om * rho * om⁻¹) * (om * a * om⁻¹) * (om * rho⁻¹ * om⁻¹) := by group
    rw [hfac, conj_eq_of_comm homr, conj_inv_eq homr]
  have hpl : ∀ a ∈ q13A t tau x₁ x₂ rho,
      om * (lam * a * lam⁻¹) * om⁻¹ = lam * (om * a * om⁻¹) * lam⁻¹ := by
    intro a ha
    have hlam_inv : lam⁻¹ = lam := inv_eq_of_mul_eq_one_right (q13a_lam_mul_self h)
    have hcase : lam⁻¹ * om * lam = om ∨ lam⁻¹ * om * lam = om * tau := by
      simpa [hlam_inv] using q13a_lam_om h
    have hkey : (lam⁻¹ * om * lam) * a * (lam⁻¹ * om * lam)⁻¹ = om * a * om⁻¹ := by
      rcases hcase with hc | hc
      · rw [hc]
      · rw [hc]
        have htau : tau * a * tau⁻¹ = a := by
          have hcomm : a * tau = tau * a :=
            Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp ha).2
          rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
        calc (om * tau) * a * (om * tau)⁻¹ = om * (tau * a * tau⁻¹) * om⁻¹ := by group
          _ = om * a * om⁻¹ := by rw [htau]
    calc om * (lam * a * lam⁻¹) * om⁻¹
        = lam * ((lam⁻¹ * om * lam) * a * (lam⁻¹ * om * lam)⁻¹) * lam⁻¹ := by group
      _ = lam * (om * a * om⁻¹) * lam⁻¹ := by rw [hkey]
  rcases s3_dichotomy (A := q13A t tau x₁ x₂ rho) hA hr hl hp (q13a_rho_cube h) hfpf
    h.c11.lam_rho hpr hpl with hid | hinv
  · exact Or.inl hid
  · exact Or.inr hinv

private theorem q13a_conj_t_a0 (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    t * (x₁ * (om * x₁ * om⁻¹)) * t⁻¹ = (x₁ * (om * x₁ * om⁻¹))⁻¹ :=
  q13a_t_inv_A h _ (q13a_elt_mem_A h)

private theorem q13a_conj_tau_a0 (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    tau * (x₁ * (om * x₁ * om⁻¹)) * tau⁻¹ = x₁ * (om * x₁ * om⁻¹) :=
  q13a_tau_centralizes_A h _ (q13a_elt_mem_A h)

private theorem q13a_not_cent_a0 (h : Q13Om t L S x₁ x₂ lam rho tau om) {g : G}
    (hg : g * (x₁ * (om * x₁ * om⁻¹)) * g⁻¹ = (x₁ * (om * x₁ * om⁻¹))⁻¹)
    (hgcent : g ∈ centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G)) : False := by
  have hmem : x₁ * (om * x₁ * om⁻¹) ∈ q13A t tau x₁ x₂ rho := q13a_elt_mem_A h
  have hfix : g * (x₁ * (om * x₁ * om⁻¹)) * g⁻¹ = x₁ * (om * x₁ * om⁻¹) := by
    have hc := (Subgroup.mem_centralizer_iff.mp hgcent) _ hmem
    rw [← hc, mul_assoc, mul_inv_cancel, mul_one]
  have heq : x₁ * (om * x₁ * om⁻¹) = (x₁ * (om * x₁ * om⁻¹))⁻¹ :=
    hfix.symm.trans hg
  have hsq : (x₁ * (om * x₁ * om⁻¹)) ^ 2 = 1 := by
    have h1 : (x₁ * (om * x₁ * om⁻¹)) * (x₁ * (om * x₁ * om⁻¹))
        = (x₁ * (om * x₁ * om⁻¹)) * (x₁ * (om * x₁ * om⁻¹))⁻¹ :=
      congrArg (fun x => (x₁ * (om * x₁ * om⁻¹)) * x) heq
    rw [pow_two, h1, mul_inv_cancel]
  exact q13a_elt_sq_ne h hsq

theorem q13a_A_dich (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    closure {t, om} ⊓ centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) =
        closure {tau, om} ∨
      closure {t, om} ⊓ centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) =
        zpowers (t * om) := by
  set A : Subgroup G := q13A t tau x₁ x₂ rho with hA
  have ha0 : x₁ * (om * x₁ * om⁻¹) ∈ A := by rw [hA]; exact q13a_elt_mem_A h
  have htsq : (t * om) * (t * om) = tau := q13a_tom_sq_aux h
  have htcube : (t * om) * (t * om) * (t * om) = t * om * tau := q13a_tom_cube_aux h
  have htom_mem : t * om ∈ zpowers (t * om) := Subgroup.mem_zpowers _
  have htau_mem_z : tau ∈ zpowers (t * om) := by
    rw [← htsq]; exact Subgroup.mul_mem _ htom_mem htom_mem
  have htomtau_mem_z : t * om * tau ∈ zpowers (t * om) := by
    rw [← htcube]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ htom_mem htom_mem) htom_mem
  rcases q13a_om_dich h with hom | hom
  · left
    apply le_antisymm
    · intro g hg
      have hgcl : g ∈ closure {t, om} := hg.1
      have hgcent : g ∈ centralizer ((A : Subgroup G) : Set G) := hg.2
      rcases q13a_D8_cases h hgcl with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
      · rw [h1]; exact one_mem _
      · rw [h1]; exact Subgroup.subset_closure (by simp)
      · exact (q13a_not_cent_a0 h (by rw [h1]; exact q13a_conj_t_a0 h) hgcent).elim
      · exact (q13a_not_cent_a0 h (by
          rw [h1]
          calc (t * tau) * (x₁ * (om * x₁ * om⁻¹)) * (t * tau)⁻¹
              = t * (tau * (x₁ * (om * x₁ * om⁻¹)) * tau⁻¹) * t⁻¹ := by group
            _ = t * (x₁ * (om * x₁ * om⁻¹)) * t⁻¹ := by rw [q13a_conj_tau_a0 h]
            _ = (x₁ * (om * x₁ * om⁻¹))⁻¹ := q13a_conj_t_a0 h) hgcent).elim
      · rw [h1]; exact Subgroup.subset_closure (by simp)
      · rw [h1]
        exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))
      · exact (q13a_not_cent_a0 h (by
          rw [h1]
          calc (t * om) * (x₁ * (om * x₁ * om⁻¹)) * (t * om)⁻¹
              = t * (om * (x₁ * (om * x₁ * om⁻¹)) * om⁻¹) * t⁻¹ := by group
            _ = t * (x₁ * (om * x₁ * om⁻¹)) * t⁻¹ := by rw [hom _ ha0]
            _ = (x₁ * (om * x₁ * om⁻¹))⁻¹ := q13a_conj_t_a0 h) hgcent).elim
      · exact (q13a_not_cent_a0 h (by
          rw [h1]
          calc (t * om * tau) * (x₁ * (om * x₁ * om⁻¹)) * (t * om * tau)⁻¹
              = t * (om * (tau * (x₁ * (om * x₁ * om⁻¹)) * tau⁻¹) * om⁻¹) * t⁻¹ := by
                group
            _ = t * (om * (x₁ * (om * x₁ * om⁻¹)) * om⁻¹) * t⁻¹ := by
                rw [q13a_conj_tau_a0 h]
            _ = t * (x₁ * (om * x₁ * om⁻¹)) * t⁻¹ := by rw [hom _ ha0]
            _ = (x₁ * (om * x₁ * om⁻¹))⁻¹ := q13a_conj_t_a0 h) hgcent).elim
    · rw [Subgroup.closure_le]
      intro x hx
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx
      · rw [hx]
        refine ⟨?_, ?_⟩
        · have htau_eq : tau = t * (om * t * om⁻¹) := by
            rw [h.t_om, ← mul_assoc, q13a_t_mul_self h, one_mul]
          rw [htau_eq]
          exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp : t ∈ ({t, om} : Set G)))
            (Subgroup.mul_mem _
              (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp : om ∈ ({t, om} : Set G)))
                (Subgroup.subset_closure (by simp : t ∈ ({t, om} : Set G))))
              (Subgroup.inv_mem _
                (Subgroup.subset_closure (by simp : om ∈ ({t, om} : Set G)))))
        · exact Subgroup.mem_centralizer_iff.mpr (fun a ha => by
            rw [hA] at ha
            exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp ha).2)
      · rw [hx]
        refine ⟨Subgroup.subset_closure (by simp : om ∈ ({t, om} : Set G)), ?_⟩
        exact Subgroup.mem_centralizer_iff.mpr (fun a ha => by
          rw [hA] at ha
          exact (mul_inv_eq_iff_eq_mul.mp (hom a ha)).symm)
  · right
    apply le_antisymm
    · intro g hg
      have hgcl : g ∈ closure {t, om} := hg.1
      have hgcent : g ∈ centralizer ((A : Subgroup G) : Set G) := hg.2
      rcases q13a_D8_cases h hgcl with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
      · rw [h1]; exact one_mem _
      · rw [h1]; exact htau_mem_z
      · exact (q13a_not_cent_a0 h (by rw [h1]; exact q13a_conj_t_a0 h) hgcent).elim
      · exact (q13a_not_cent_a0 h (by
          rw [h1]
          calc (t * tau) * (x₁ * (om * x₁ * om⁻¹)) * (t * tau)⁻¹
              = t * (tau * (x₁ * (om * x₁ * om⁻¹)) * tau⁻¹) * t⁻¹ := by group
            _ = t * (x₁ * (om * x₁ * om⁻¹)) * t⁻¹ := by rw [q13a_conj_tau_a0 h]
            _ = (x₁ * (om * x₁ * om⁻¹))⁻¹ := q13a_conj_t_a0 h) hgcent).elim
      · exact (q13a_not_cent_a0 h (by rw [h1]; exact hom _ ha0) hgcent).elim
      · exact (q13a_not_cent_a0 h (by
          rw [h1]
          calc (om * tau) * (x₁ * (om * x₁ * om⁻¹)) * (om * tau)⁻¹
              = om * (tau * (x₁ * (om * x₁ * om⁻¹)) * tau⁻¹) * om⁻¹ := by group
            _ = om * (x₁ * (om * x₁ * om⁻¹)) * om⁻¹ := by rw [q13a_conj_tau_a0 h]
            _ = (x₁ * (om * x₁ * om⁻¹))⁻¹ := hom _ ha0) hgcent).elim
      · rw [h1]; exact htom_mem
      · rw [h1]; exact htomtau_mem_z
    · rw [Subgroup.zpowers_le]
      refine ⟨Subgroup.mul_mem _ (Subgroup.subset_closure (by simp : t ∈ ({t, om} : Set G)))
        (Subgroup.subset_closure (by simp : om ∈ ({t, om} : Set G))), ?_⟩
      exact Subgroup.mem_centralizer_iff.mpr (fun a ha => by
        rw [hA] at ha
        have hconj : (t * om) * a * (t * om)⁻¹ = a := by
          calc (t * om) * a * (t * om)⁻¹ = t * (om * a * om⁻¹) * t⁻¹ := by group
            _ = t * a⁻¹ * t⁻¹ := by rw [hom a ha]
            _ = (t * a * t⁻¹)⁻¹ := by group
            _ = (a⁻¹)⁻¹ := by rw [q13a_t_inv_A h a ha]
            _ = a := inv_inv a
        exact (mul_inv_eq_iff_eq_mul.mp hconj).symm)

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
