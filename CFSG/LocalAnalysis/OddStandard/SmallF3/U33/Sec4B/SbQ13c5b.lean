module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13c0

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private lemma z_mem_centralizer_S (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    (x₁ * x₂) ^ 2 ∈ centralizer (S : Set G) :=
  (h.c11.center_ge (Subgroup.subset_closure (by simp))).2

private lemma map_conj_S_le_cent (h : Q13Om t L S x₁ x₂ lam rho tau om) {c : G}
    (hcL : c ∈ L) (hcz : c * (x₁ * x₂) ^ 2 * c⁻¹ = lam) :
    S.map (MulAut.conj c).toMonoidHom ≤ invCent t ⊓ centralizer ({lam} : Set G) := by
  intro y hy
  rw [Subgroup.mem_map] at hy
  obtain ⟨s, hs, rfl⟩ := hy
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [Subgroup.mem_inf]
  refine ⟨?_, ?_⟩
  · have hcH : c ∈ invCent t := S4A.L_le_invCent h.c11.hyp hcL
    have hsH : s ∈ invCent t := h.c11.le_invCent hs
    exact (invCent t).mul_mem ((invCent t).mul_mem hcH hsH) ((invCent t).inv_mem hcH)
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have hsz : s * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * s :=
      (Subgroup.mem_centralizer_iff.mp (z_mem_centralizer_S h)) s hs
    calc (c * s * c⁻¹) * lam = (c * s * c⁻¹) * (c * (x₁ * x₂) ^ 2 * c⁻¹) := by rw [hcz]
      _ = c * (s * (x₁ * x₂) ^ 2) * c⁻¹ := by group
      _ = c * ((x₁ * x₂) ^ 2 * s) * c⁻¹ := by rw [hsz]
      _ = (c * (x₁ * x₂) ^ 2 * c⁻¹) * (c * s * c⁻¹) := by group
      _ = lam * (c * s * c⁻¹) := by rw [hcz]

private lemma map_conj_eq_cent_of_conj (ht : t * t = 1) {g : G}
    (hg : g * t * g⁻¹ = t * lam) :
    (invCent t ⊓ centralizer ({g⁻¹ * t * g} : Set G)).map (MulAut.conj g).toMonoidHom =
      invCent t ⊓ centralizer ({lam} : Set G) := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [Subgroup.mem_inf] at hx ⊢
    obtain ⟨hxH, hxC⟩ := hx
    have hxcomm : x * (g⁻¹ * t * g) = (g⁻¹ * t * g) * x :=
      Subgroup.mem_centralizer_singleton_iff.mp hxC
    have hxt : x * t = t * x := S4A.mem_invCent_iff.mp hxH
    have hyt : (g * x * g⁻¹) * t = t * (g * x * g⁻¹) := by
      calc (g * x * g⁻¹) * t = g * (x * (g⁻¹ * t * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * t * g) * x) * g⁻¹ := by rw [hxcomm]
        _ = t * (g * x * g⁻¹) := by
              have e : g * (g⁻¹ * t * g) * g⁻¹ = t := by group
              calc g * ((g⁻¹ * t * g) * x) * g⁻¹
                  = (g * (g⁻¹ * t * g) * g⁻¹) * (g * x * g⁻¹) := by group
                _ = t * (g * x * g⁻¹) := by rw [e]
    have hygt : (g * x * g⁻¹) * (g * t * g⁻¹) = (g * t * g⁻¹) * (g * x * g⁻¹) := by
      calc (g * x * g⁻¹) * (g * t * g⁻¹) = g * (x * t) * g⁻¹ := by group
        _ = g * (t * x) * g⁻¹ := by rw [hxt]
        _ = (g * t * g⁻¹) * (g * x * g⁻¹) := by group
    refine ⟨S4A.mem_invCent_iff.mpr hyt, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hlam : lam = t * (g * t * g⁻¹) := by
      rw [hg, ← mul_assoc, ht, one_mul]
    rw [hlam]
    calc (g * x * g⁻¹) * (t * (g * t * g⁻¹))
        = ((g * x * g⁻¹) * t) * (g * t * g⁻¹) := by group
      _ = (t * (g * x * g⁻¹)) * (g * t * g⁻¹) := by rw [hyt]
      _ = t * ((g * x * g⁻¹) * (g * t * g⁻¹)) := by group
      _ = t * ((g * t * g⁻¹) * (g * x * g⁻¹)) := by rw [hygt]
      _ = (t * (g * t * g⁻¹)) * (g * x * g⁻¹) := by group
  · intro hy
    refine ⟨g⁻¹ * y * g, ?_, ?_⟩
    · rw [Subgroup.mem_inf] at hy ⊢
      obtain ⟨hyH, hyC⟩ := hy
      have hyt : y * t = t * y := S4A.mem_invCent_iff.mp hyH
      have hycomm : y * lam = lam * y :=
        Subgroup.mem_centralizer_singleton_iff.mp hyC
      have hygt : y * (g * t * g⁻¹) = (g * t * g⁻¹) * y := by
        rw [hg]
        calc y * (t * lam) = (y * t) * lam := by group
          _ = (t * y) * lam := by rw [hyt]
          _ = t * (y * lam) := by group
          _ = t * (lam * y) := by rw [hycomm]
          _ = (t * lam) * y := by group
      refine ⟨?_, ?_⟩
      · rw [S4A.mem_invCent_iff]
        calc (g⁻¹ * y * g) * t = g⁻¹ * (y * (g * t * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * t * g⁻¹) * y) * g := by rw [hygt]
          _ = t * (g⁻¹ * y * g) := by
                have e : g⁻¹ * (g * t * g⁻¹) * g = t := by group
                calc g⁻¹ * ((g * t * g⁻¹) * y) * g
                    = (g⁻¹ * (g * t * g⁻¹) * g) * (g⁻¹ * y * g) := by group
                  _ = t * (g⁻¹ * y * g) := by rw [e]
      · rw [Subgroup.mem_centralizer_singleton_iff]
        calc (g⁻¹ * y * g) * (g⁻¹ * t * g) = g⁻¹ * (y * t) * g := by group
          _ = g⁻¹ * (t * y) * g := by rw [hyt]
          _ = (g⁻¹ * t * g) * (g⁻¹ * y * g) := by group
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

theorem q13c_card_cent_lam_ge (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    2 ^ 7 ≤ Nat.card ↥(invCent t ⊓ centralizer ({lam} : Set G)) := by
  obtain ⟨c, hcL, hcz⟩ :=
    h.c11.invol_L lam (q13c_lam_mem_L h) (q13a_lam_mul_self h) (q13c_lam_ne_one h)
  have hle := map_conj_S_le_cent h hcL hcz
  have hcard : Nat.card ↥(S.map (MulAut.conj c).toMonoidHom) = 2 ^ 7 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj c).injective,
      Ctx4.card_S_seven h.c11.toCtx10.toCtx4]
  calc 2 ^ 7 = Nat.card ↥(S.map (MulAut.conj c).toMonoidHom) := hcard.symm
    _ ≤ Nat.card ↥(invCent t ⊓ centralizer ({lam} : Set G)) := Subgroup.card_le_of_le hle

theorem q13c_card_cent_conj (h : Q13Om t L S x₁ x₂ lam rho tau om) {g : G}
    (hg : g * t * g⁻¹ = t * lam) :
    Nat.card ↥(invCent t ⊓ centralizer ({g⁻¹ * t * g} : Set G)) =
      Nat.card ↥(invCent t ⊓ centralizer ({lam} : Set G)) := by
  have heq := map_conj_eq_cent_of_conj (t := t) (lam := lam) (q13a_t_mul_self h) hg
  calc Nat.card ↥(invCent t ⊓ centralizer ({g⁻¹ * t * g} : Set G))
      = Nat.card ↥((invCent t ⊓ centralizer ({g⁻¹ * t * g} : Set G)).map
          (MulAut.conj g).toMonoidHom) :=
        (Subgroup.card_map_of_injective (K := _) (MulAut.conj g).injective).symm
    _ = Nat.card ↥(invCent t ⊓ centralizer ({lam} : Set G)) := by rw [heq]

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
