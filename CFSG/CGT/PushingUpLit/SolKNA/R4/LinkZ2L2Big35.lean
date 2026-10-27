module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big34

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W
open CFSG.Blueprint

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y} {R₀ T₀ : Subgroup Y} {P : Sylow 2 Y}

theorem Z2SetR.inter_R₀_T₀ (hs : Z2SetR r n R S t J u R₀ T₀ P) {y : Y} (hyR : y ∈ R₀)
    (hyT : y ∈ T₀) : y = 1 := by
  have ht := hs.large.datum.isUniqueInvolution_core
  by_contra hy1
  have hR2 : IsPGroup 2 ↥(R₀ ⊓ T₀) := hs.hR₀.2.1.to_le inf_le_left
  have hne : R₀ ⊓ T₀ ≠ ⊥ := by
    intro e
    have hy : y ∈ R₀ ⊓ T₀ := ⟨hyR, hyT⟩
    rw [e] at hy
    exact hy1 (Subgroup.mem_bot.mp hy)
  have hcard := (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
  have htT : t ∈ R₀ ⊓ T₀ :=
    AscL62.mem_of_uniqueInvolution_of_pGroup ht (inf_le_left.trans hs.hR₀.1) hR2 (by omega)
  exact hs.aux_t_ne_u ((hs.hu.unique t (hs.hT₀.1 htT.2) ht.sq).resolve_left ht.ne_one)

theorem z2BigNotConjTU_holds (r n : ℕ) : Z2BigNotConjTU r n := by
  intro hr Y _ _ R S t J u R₀ T₀ P hs b hbP hbA hb2 g hgb
  obtain ⟨hsw, -⟩ := hs.aux_swap hbP hbA
  have hc := hs.aux_commutes
  have hT : ∀ x ∈ R₀, b * x * b⁻¹ ∈ T₀ := fun x hx => by
    rw [← hs.aux_conj_R₀ hbP hsw]
    exact conj_mem_conjSub hx b
  have hQ2 : IsPGroup 2 ↥((MulAut.conj g).toMonoidHom.comp (aux_diag R₀ T₀ b hT hc)).range :=
    hs.hR₀.2.1.of_surjective _ (MonoidHom.rangeRestrict_surjective _)
  have hQa : ((MulAut.conj g).toMonoidHom.comp (aux_diag R₀ T₀ b hT hc)).range ≤
      Subgroup.centralizer ({t * u} : Set Y) := by
    rintro _ ⟨x, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← hgb]
    have h := aux_diag_comm hT hc hb2 x
    change g * aux_diag R₀ T₀ b hT hc x * g⁻¹ * (g * b * g⁻¹) =
      g * b * g⁻¹ * (g * aux_diag R₀ T₀ b hT hc x * g⁻¹)
    calc g * aux_diag R₀ T₀ b hT hc x * g⁻¹ * (g * b * g⁻¹)
        = g * (aux_diag R₀ T₀ b hT hc x * b) * g⁻¹ := by group
      _ = g * (b * aux_diag R₀ T₀ b hT hc x) * g⁻¹ := by rw [h]
      _ = g * b * g⁻¹ * (g * aux_diag R₀ T₀ b hT hc x * g⁻¹) := by group
  obtain ⟨c, hc', hcQ⟩ := hs.exists_conj_le hQ2 hQa
  obtain ⟨θ, hθ⟩ : ∃ θ : ↥R₀ →* Y,
      ∀ x, θ x = c * (g * aux_diag R₀ T₀ b hT hc x * g⁻¹) * c⁻¹ :=
    ⟨(MulAut.conj c).toMonoidHom.comp
      ((MulAut.conj g).toMonoidHom.comp (aux_diag R₀ T₀ b hT hc)), fun _ => rfl⟩
  have hθP : ∀ x, θ x ∈ (P : Subgroup Y) := fun x => by
    have hmem : g * aux_diag R₀ T₀ b hT hc x * g⁻¹ ∈
        ((MulAut.conj g).toMonoidHom.comp (aux_diag R₀ T₀ b hT hc)).range := ⟨x, rfl⟩
    rw [hθ]
    exact hcQ (conj_mem_conjSub hmem c)
  have hθinj : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro z hz
    have h1 : g * aux_diag R₀ T₀ b hT hc z * g⁻¹ = 1 := by
      have h := hz
      rw [hθ z] at h
      calc g * aux_diag R₀ T₀ b hT hc z * g⁻¹
          = c⁻¹ * (c * (g * aux_diag R₀ T₀ b hT hc z * g⁻¹) * c⁻¹) * c := by group
        _ = c⁻¹ * 1 * c := by rw [h]
        _ = 1 := by group
    have hd : aux_diag R₀ T₀ b hT hc z = 1 := by
      calc aux_diag R₀ T₀ b hT hc z
          = g⁻¹ * (g * aux_diag R₀ T₀ b hT hc z * g⁻¹) * g := by group
        _ = g⁻¹ * 1 * g := by rw [h1]
        _ = 1 := by group
    have hzT : (z : Y) ∈ T₀ := by
      have hbT : b * (z : Y) * b⁻¹ ∈ T₀ := hT z z.2
      have h2 : (z : Y) * (b * (z : Y) * b⁻¹) = 1 := by
        rw [← aux_diag_apply hT hc z]
        exact hd
      have h4 : (z : Y) = (b * (z : Y) * b⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left h2
      rw [h4]
      exact inv_mem hbT
    exact Subtype.ext (hs.inter_R₀_T₀ z.2 hzT)
  have hθt : θ ⟨t, hs.t_mem_R₀⟩ = c * (g * (t * u) * g⁻¹) * c⁻¹ := by
    rw [hθ, aux_diag_apply, hsw]
  have hE := hs.theta_center_mem_E hr θ hθinj hθP
  rw [hθt] at hE
  have htu := hs.aux_tu
  rcases T8.mem_closure_pair_involutions hs.large.datum.isUniqueInvolution_core.sq hs.hu.sq htu
    hE with h | h | h | h
  · have h' : t * u = 1 := by
      calc t * u = (c * g)⁻¹ * (c * (g * (t * u) * g⁻¹) * c⁻¹) * (c * g) := by group
        _ = 1 := by rw [h]; group
    have h'' := mul_eq_one_iff_eq_inv.mp h'
    rw [inv_eq_of_mul_eq_one_right hs.hu.sq] at h''
    exact hs.aux_t_ne_u h''
  · exact hs.tu_not_conj (c * g)
      ((by group : c * g * (t * u) * (c * g)⁻¹ = c * (g * (t * u) * g⁻¹) * c⁻¹).trans h)
  · obtain ⟨k, hk⟩ := hs.exists_conj_u
    refine hs.tu_not_conj (k⁻¹ * (c * g)) ?_
    calc k⁻¹ * (c * g) * (t * u) * (k⁻¹ * (c * g))⁻¹
        = k⁻¹ * (c * (g * (t * u) * g⁻¹) * c⁻¹) * k := by group
      _ = k⁻¹ * u * k := by rw [h]
      _ = t := by rw [← hk]; group
  · apply hbA
    have hca : c * (t * u) * c⁻¹ = t * u := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp hc']
      group
    have e1 : b = (c * g)⁻¹ * (c * (g * b * g⁻¹) * c⁻¹) * (c * g) := by group
    have e2 : t * u = (c * g)⁻¹ * (c * (g * (t * u) * g⁻¹) * c⁻¹) * (c * g) := by group
    rw [hgb, hca] at e1
    rw [h] at e2
    rw [e1.trans e2.symm]
    exact hs.aux_E_le (mul_mem (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp)))

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
