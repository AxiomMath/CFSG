module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.UHSNorm
import CFSG.LocalAnalysis.OddStandard.SwapPartner.LemmaGCent
import CFSG.LocalAnalysis.OddStandard.SwapPartner.WpGTypes
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.UD8B

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern

variable {G : Type} [Group G] {z : G} {ι ιd : Perm (Fin 10) →* G} {Kh : Subgroup G}

private theorem u_eq_of_card_le_two {H : Type} [Group H] [Finite H] (hcard : Nat.card H ≤ 2)
    {a b : H} (ha : a ≠ 1) (hb : b ≠ 1) : a = b := by
  by_contra hab
  have hinj : Function.Injective (fun k : Fin 3 => ![1, a, b] k) := by
    intro p q hpq
    fin_cases p <;> fin_cases q <;> simp_all
  have hle := Nat.card_le_card_of_injective (fun k : Fin 3 => ![1, a, b] k) hinj
  simp only [Nat.card_fin] at hle
  omega

theorem HSCtx.center_eq_bot_of_g (C : HSCtx z ι ιd Kh) [Finite G]
    (hg : ∀ k ∈ Kh, gElt ιd * k = k * gElt ιd) : center ↥Kh = ⊥ := by
  classical
  have hF := C.frame
  have hC := hF.cent
  by_contra hne
  obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  let c : ↥Kh := a.1
  have hcZ : c ∈ center ↥Kh := a.2
  have hcne : c ≠ 1 := by
    intro h
    exact ha (Subtype.ext h)
  have hcGmem : (c : G) ∈ Kh := c.2
  have hcGne : (c : G) ≠ 1 := fun h => hcne (Subtype.ext h)
  have hcentral : ∀ h : G, h ∈ centralizer ({z * ι τ₀} : Set G) →
      h * (c : G) = (c : G) * h := by
    intro h hh
    have hdmem : h * (c : G) * h⁻¹ ∈ Kh := C.conj_mem hh hcGmem
    let d : ↥Kh := ⟨h * (c : G) * h⁻¹, hdmem⟩
    have hdcenter : d ∈ center ↥Kh := by
      rw [Subgroup.mem_center_iff]
      intro k
      apply Subtype.ext
      show (k : G) * (h * (c : G) * h⁻¹) = (h * (c : G) * h⁻¹) * (k : G)
      have hk'mem : h⁻¹ * (k : G) * h ∈ Kh := by
        have hh' : h⁻¹ ∈ centralizer ({z * ι τ₀} : Set G) := inv_mem hh
        simpa using C.conj_mem hh' k.2
      have hck' : (h⁻¹ * (k : G) * h) * (c : G) = (c : G) * (h⁻¹ * (k : G) * h) :=
        congrArg (fun x : ↥Kh => (x : G))
          (Subgroup.mem_center_iff.mp hcZ ⟨h⁻¹ * (k : G) * h, hk'mem⟩)
      calc (k : G) * (h * (c : G) * h⁻¹)
          = h * ((h⁻¹ * (k : G) * h) * (c : G)) * h⁻¹ := by group
        _ = h * ((c : G) * (h⁻¹ * (k : G) * h)) * h⁻¹ := by rw [hck']
        _ = (h * (c : G) * h⁻¹) * (k : G) := by group
    have hdne : d ≠ 1 := by
      intro hd
      apply hcGne
      have h1 : h * (c : G) * h⁻¹ = 1 := congrArg (fun x : ↥Kh => (x : G)) hd
      calc (c : G) = h⁻¹ * (h * (c : G) * h⁻¹) * h := by group
        _ = h⁻¹ * 1 * h := by rw [h1]
        _ = 1 := by group
    have huniq := u_eq_of_card_le_two (H := ↥(center ↥Kh)) C.card_center_le_two
      (a := (⟨d, hdcenter⟩ : ↥(center ↥Kh))) (b := (⟨c, hcZ⟩ : ↥(center ↥Kh)))
      (by intro hh; exact hdne (congrArg (fun x : ↥(center ↥Kh) => (x : ↥Kh)) hh))
      (by intro hh; exact hcne (congrArg (fun x : ↥(center ↥Kh) => (x : ↥Kh)) hh))
    have hdc : d = c := congrArg (fun x : ↥(center ↥Kh) => (x : ↥Kh)) huniq
    calc h * (c : G) = (h * (c : G) * h⁻¹) * h := by group
      _ = (d : G) * h := rfl
      _ = (c : G) * h := by rw [hdc]
  have hcE : (c : G) ∈ Egrp z ι := by
    rw [← centralizer_Agrp_inf_centralizer_z hC]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [mem_centralizer_iff]
      intro e he
      have heKh : e ∈ Kh := C.khat.agrp_le he
      exact congrArg (fun x : ↥Kh => (x : G))
        (Subgroup.mem_center_iff.mp hcZ ⟨e, heKh⟩)
    · rw [mem_centralizer_singleton_iff]
      exact (hcentral z (z_mem_centralizer_x₂ hC)).symm
  obtain ⟨i, j, hij⟩ := (mem_Egrp_iff hC).mp hcE
  have hcg : gElt ιd * (c : G) = (c : G) * gElt ιd := hg (c : G) hcGmem
  have hcx2 : (c : G) = z * ι τ₀ := by
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_mul, mul_one] at hij
    · exact absurd hij hcGne
    · exfalso
      have hgx : gElt ιd * (ι τ₀) = (ι τ₀) * gElt ιd := by rw [← hij]; exact hcg
      have hz : z = ι τ₀ := by
        have h1 : gElt ιd * z = gElt ιd * (ι τ₀) := by
          calc gElt ιd * z = (gElt ιd * z * gElt ιd) * gElt ιd := by
                rw [mul_assoc, hF.g_sq, mul_one]
            _ = (ι τ₀) * gElt ιd := by rw [hF.g_z_g]
            _ = gElt ιd * (ι τ₀) := hgx.symm
        exact mul_left_cancel h1
      exact hC.ne_z τ₀ hz.symm
    · exfalso
      have hgz : gElt ιd * z = z * gElt ιd := by rw [← hij]; exact hcg
      have hx1 : ι τ₀ = z := by
        calc ι τ₀ = gElt ιd * z * gElt ιd := hF.g_z_g.symm
          _ = (gElt ιd * z) * gElt ιd := by group
          _ = (z * gElt ιd) * gElt ιd := by rw [hgz]
          _ = z := by rw [mul_assoc, hF.g_sq, mul_one]
      exact hC.ne_z τ₀ hx1
    · exact hij
  have hgKh : gElt ιd ∈ Kh := by
    have h := C.conj_y_mem hg hcGmem
    rw [hcx2, hF.y_conj] at h
    exact h
  have hgcenter : (⟨gElt ιd, hgKh⟩ : ↥Kh) ∈ center ↥Kh := by
    rw [Subgroup.mem_center_iff]
    intro k
    apply Subtype.ext
    show (k : G) * gElt ιd = gElt ιd * (k : G)
    exact (hg (k : G) k.2).symm
  have hcontra := u_eq_of_card_le_two (H := ↥(center ↥Kh)) C.card_center_le_two
    (a := (⟨⟨gElt ιd, hgKh⟩, hgcenter⟩ : ↥(center ↥Kh)))
    (b := (⟨c, hcZ⟩ : ↥(center ↥Kh)))
    (by intro hh
        exact D8Rel.u_g_ne_one hF.d8
          (congrArg (fun x : ↥(center ↥Kh) => ((x : ↥Kh) : G)) hh))
    (by intro hh; exact hcne (congrArg (fun x : ↥(center ↥Kh) => (x : ↥Kh)) hh))
  have hgeq : gElt ιd = (c : G) :=
    congrArg (fun x : ↥(center ↥Kh) => ((x : ↥Kh) : G)) hcontra
  rw [hcx2] at hgeq
  exact D8Rel.u_g_ne_x hF.d8 hgeq

end CFSG.OddStandard.AltStdSec.SwapPartner
