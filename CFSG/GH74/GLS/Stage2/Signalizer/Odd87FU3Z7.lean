module

public import CFSG.GH74.Generic.S3.L3Class
public import CFSG.GH74.KGroups.L3EpsUniInv

public section

open CFSG.GH74.KGroups.L3Eps.Uni CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank CFSG.GH74.Generic.S3

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem no_seven_centralizes_involution {p f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData p f F)
    (hp : p ≠ 2) (hq3 : p ^ f = 3) {K : Type} [Group K] (e₀ : K ≃* StatedProj (StatedSU 3 (p ^ f) F))
    {y t : K} (hy : y ^ 7 = 1) (ht : t * t = 1) (ht1 : t ≠ 1) (hyt : y * t = t * y) : y = 1 := by
  classical
  have hq : Odd (p ^ f) := by rw [hq3]; decide
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_pow h hq
  obtain ⟨θ₀, hθ₀⟩ := exists_cover_of_equiv h e₀
  have hS : SingleInv K := SingleInv.of_mulEquiv e₀.symm (singleInv_psu h hp)
  obtain ⟨g, hg⟩ := hS (θ₀ (dU hq)) t (theta_dU_sq hq θ₀) (theta_dU_ne_one h hq hθ₀) ht ht1
  set θ : ↥(unitarySU p f F 3) →* K := (MulAut.conj g).toMonoidHom.comp θ₀ with hθdef
  have hθ : IsCover h θ := hθ₀.comp_equiv (MulAut.conj g)
  have hθdU : θ (dU hq) = t := by simpa [hθdef, MulAut.conj_apply] using hg
  have hycen : y ∈ Subgroup.centralizer ({θ (dU hq)} : Set K) := by
    rw [Subgroup.mem_centralizer_singleton_iff, hθdU]
    exact hyt
  obtain ⟨g0, hg0, hg0c⟩ := cen_lift h θ hθ.ker hθ.surj h2 hq hycen
  have hscal : g0 ^ 7 = 1 := by
    have h1 : θ (g0 ^ 7) = 1 := by rw [map_pow, hg0, hy]
    have h2' : g0 ^ 7 ∈ θ.ker := h1
    rw [hθ.ker, mem_unitaryScalars] at h2'
    obtain ⟨c, hc, hc3, hcg⟩ := h2'
    have hbar : h.bar (c : F) = (c : F) ^ 3 := by rw [UnitaryFieldData.bar_apply, hq3]
    have hc4 : (c : F) ^ 4 = 1 := by
      have := hc
      rw [UnitaryFieldData.norm, hbar] at this
      linear_combination this
    have hc3' : (c : F) ^ 3 = 1 := by simpa using congrArg (fun u : Fˣ => (u : F)) hc3
    have hc1 : (c : F) = 1 := by linear_combination hc4 - (c : F) * hc3'
    have hc1' : c = 1 := Units.ext hc1
    apply Subtype.ext
    rw [hcg, hc1', map_one]
    rfl
  have hmem : g0 ∈ Subgroup.centralizer ({dU hq} : Set ↥(unitarySU p f F 3)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hg0c
  set g0' : ↥(Subgroup.centralizer ({dU hq} : Set ↥(unitarySU p f F 3))) := ⟨g0, hmem⟩ with hg0'
  have h7 : (cenHomU h hq g0') ^ 7 = 1 := by
    rw [← map_pow]
    have : g0' ^ 7 = 1 := Subtype.ext hscal
    rw [this, map_one]
  have hu4 : (cenHomU h hq g0') ^ 4 = 1 := by
    have hL := isLevi_of_mem_centralizer h hq hmem
    have hu := ((mem_unitarySU_iff h).1 g0.2).2
    have e22 := congrFun (congrFun hu 2) 2
    simp [Matrix.mul_apply, Fin.sum_univ_three, hL.1, hL.2.1] at e22
    have hbar : h.bar (matU g0 2 2) = (matU g0 2 2) ^ 3 := by rw [UnitaryFieldData.bar_apply, hq3]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, cenHomU_apply, Units.val_one]
    rw [hbar] at e22
    show (matU g0 2 2) ^ 4 = 1
    linear_combination e22
  have hu1 : cenHomU h hq g0' = 1 := by
    have := pow_gcd_eq_one.2 ⟨h7, hu4⟩
    simpa using this
  obtain ⟨B, hB⟩ := mem_range_levU_of_cenHomU h hq g0' hu1
  have hymem : y ∈ levS hq θ := by
    have hB' : levU hq.pos B = g0 := hB
    rw [← hg0, ← hB']
    exact θ_levU_mem_levS hq B
  have hcard : Nat.card ↥(levS hq θ) = 24 := by
    rw [card_levS h hθ hq, hq3]
    norm_num
  let yy : ↥(levS hq θ) := ⟨y, hymem⟩
  have hyy7 : yy ^ 7 = 1 := Subtype.ext hy
  have hdvd24 : orderOf yy ∣ 24 := hcard ▸ orderOf_dvd_natCard yy
  have hdvd7 : orderOf yy ∣ 7 := orderOf_dvd_of_pow_eq_one hyy7
  have hord : orderOf yy = 1 := by
    have := Nat.dvd_gcd hdvd24 hdvd7
    simpa using this
  have : yy = 1 := orderOf_eq_one_iff.mp hord
  exact congrArg Subtype.val this

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
