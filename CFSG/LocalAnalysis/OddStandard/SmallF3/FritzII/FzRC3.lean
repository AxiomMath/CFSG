module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzRC1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AOuter
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzRS3C

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33 CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem fzr_nc_lam_s
    (h : Ctx t L S x₁ x₂ lam rho tau) {T₂ P X : Subgroup G}
    {s : G}
    (hT₂ : IsPGroup 2 T₂) (hST : S ≤ T₂) (hPT : P ≤ T₂)
    (hnP : ∀ g ∈ T₂, ∀ p ∈ P, g * p * g⁻¹ ∈ P) (hrP : ∀ p ∈ P, rho * p * rho⁻¹ ∈ P)
    (hr3 : rho ^ 3 = 1) (hfpf : ∀ p ∈ P, rho * p * rho⁻¹ = p → p = 1)
    (hlT : lam ∈ T₂) (hl2 : lam * lam = 1) (hlr : lam * rho * lam⁻¹ = rho⁻¹)
    (hsT : s ∈ T₂) (hs2 : s * s = 1) (hst : s * t = t * s) (hsl : s * lam = lam * s)
    (hsr : s * rho = rho * s) (hsL : s ∉ twoCore t ⊔ L) (hls1 : lam * s ≠ 1)
    (hXT : X ≤ T₂) (hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (hXsq : ∀ x ∈ X, x * x = 1)
    (hX16 : Nat.card X = 16) (hsX : ∀ x ∈ X, s * x = x * s) (hsXn : s ∉ X)
    {p : G} (hp : p ∈ P) :
    ¬ ∃ g : G, g⁻¹ * t * g = p * (lam * s) := by
  rintro ⟨g, hg⟩
  have ht2 : t * t = 1 := by
    rw [← pow_two, ← h.hyp.ord_t]
    exact pow_orderOf_eq_one t
  have ht1 : t ≠ 1 := by
    intro h1
    have := h.hyp.ord_t
    rw [h1, orderOf_one] at this
    norm_num at this
  have hu2 : (p * (lam * s)) * (p * (lam * s)) = 1 := by
    rw [← hg]
    calc (g⁻¹ * t * g) * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [ht2]; group
  have hu1 : p * (lam * s) ≠ 1 := by
    intro h1
    apply ht1
    have h2 : g⁻¹ * t * g = 1 := by rw [hg, h1]
    have h3 := congrArg (fun z => g * z * g⁻¹) h2
    rw [show g * (g⁻¹ * t * g) * g⁻¹ = t by group,
        show g * 1 * g⁻¹ = 1 by group] at h3
    exact h3
  have hu_ord : orderOf (p * (lam * s)) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (p := 2) (by rw [pow_two]; exact hu2) hu1
  have hy2 : (lam * s) * (lam * s) = 1 := by
    calc (lam * s) * (lam * s) = lam * (s * lam) * s := by group
      _ = lam * (lam * s) * s := by rw [hsl]
      _ = (lam * lam) * (s * s) := by group
      _ = 1 := by rw [hl2, hs2, one_mul]
  have hy_ord : orderOf (lam * s) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (p := 2) (by rw [pow_two]; exact hy2) hls1
  have hyT : lam * s ∈ T₂ := T₂.mul_mem hlT hsT
  have hs_rho : s * rho * s⁻¹ = rho := by
    rw [hsr]; group
  have hyr : (lam * s) * rho * (lam * s)⁻¹ = rho⁻¹ := by
    calc (lam * s) * rho * (lam * s)⁻¹ = lam * (s * rho * s⁻¹) * lam⁻¹ := by group
      _ = lam * rho * lam⁻¹ := by rw [hs_rho]
      _ = rho⁻¹ := hlr
  obtain ⟨w, hwP, hwy⟩ := fzr_conj_of_invol_mul (X := P) (rho := rho) (y := lam * s)
    (hT₂.to_le hPT) hrP (hnP (lam * s) hyT) hr3 hy_ord hyr hfpf hp hu_ord
  have hlamL : lam ∈ L := by
    have hl : lam ∈ wreathGrp x₁ x₂ lam := Subgroup.subset_closure (by simp)
    rw [← h.inf_eq] at hl
    exact hl.2
  have hlamC : lam ∈ invCent t := by
    rw [invCent, Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp h.hyp.mem_centralizer) lam hlamL
  have hsC : s ∈ invCent t := by
    rw [invCent, Subgroup.mem_centralizer_singleton_iff]
    exact hst
  have hyC : lam * s ∈ invCent t := (invCent t).mul_mem hlamC hsC
  have hys : (lam * s) * s⁻¹ = lam := by group
  have hysL : (lam * s) * s⁻¹ ∈ L := by rw [hys]; exact hlamL
  have houter : ∃ l ∈ L, lam * s = l * s * l⁻¹ := by
    exact S4A.outer_coset_conj h.hyp hsC hs2 hsL hyC hy2 hysL
  obtain ⟨l, hlL, hly⟩ := houter
  refine fzr_nc_of_cent_X h hT₂ hST hXT hXc hXsq hX16 hsT hs2 hsX hsXn ⟨g * w * l, ?_⟩
  calc (g * w * l)⁻¹ * t * (g * w * l)
      = l⁻¹ * w⁻¹ * (g⁻¹ * t * g) * w * l := by group
    _ = l⁻¹ * w⁻¹ * (p * (lam * s)) * w * l := by rw [hg]
    _ = l⁻¹ * w⁻¹ * (w * (lam * s) * w⁻¹) * w * l := by rw [hwy]
    _ = l⁻¹ * (lam * s) * l := by group
    _ = l⁻¹ * (l * s * l⁻¹) * l := by rw [hly]
    _ = s := by group

end CFSG.OddStandard.SmallF3.FritzII
