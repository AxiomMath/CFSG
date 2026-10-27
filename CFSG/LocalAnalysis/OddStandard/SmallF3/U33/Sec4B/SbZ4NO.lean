module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4NN

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem isElemAbelian_inf_centralizer_one {A : Subgroup G} {t : G}
    (hA : CFSG.Open.IsElemAbelian 2 A) :
    CFSG.Open.IsElemAbelian 2 (A ⊓ centralizer ({t} : Set G)) := by
  refine ⟨IsMulCommutative.of_comm fun x y => Subtype.ext ?_,
    fun x hx => hA.2 x (Subgroup.mem_inf.mp hx).1⟩
  haveI : IsMulCommutative ↥A := hA.1
  exact congrArg (Subtype.val : ↥A → G) (mul_comm'
    (⟨(x : G), (Subgroup.mem_inf.mp x.2).1⟩ : ↥A)
    (⟨(y : G), (Subgroup.mem_inf.mp y.2).1⟩ : ↥A))


namespace ZNW4

variable (hw : ZNW4 t L S x₁ x₂ lam rho tau)
include hw

theorem U_CA_normal {R A : Subgroup G} (hR : IsPGroup 2 R)
    (hVR : ctxVN t tau x₁ x₂ lam rho ≤ R) (hA : IsE16In R A) (hAN : NormalIn A R) :
    NormalIn (A ⊓ centralizer ({t} : Set G)) S := by
  have hSR : S ≤ R := hw.S_le_ctxVN.trans hVR
  have hcent : R ⊓ centralizer ({t} : Set G) = S :=
    S4B.c17_cent_eq hw.toCtx10 hR hSR
  refine ⟨?_, ?_⟩
  · intro w hw'
    rw [← hcent]
    exact ⟨hA.1 (Subgroup.mem_inf.mp hw').1, (Subgroup.mem_inf.mp hw').2⟩
  · intro s hs w hx
    rw [Subgroup.mem_inf] at hx ⊢
    have hs' : s ∈ centralizer ({t} : Set G) := hw.le_invCent hs
    exact ⟨hAN.2 s (hSR hs) w hx.1,
      mul_mem (mul_mem hs' hx.2) (inv_mem hs')⟩

theorem U_card_CA {R A : Subgroup G} (hR : IsPGroup 2 R)
    (hVR : ctxVN t tau x₁ x₂ lam rho ≤ R) (hA : IsE16In R A) (hAN : NormalIn A R) :
    4 ≤ Nat.card ↥(A ⊓ centralizer ({t} : Set G)) := by
  have ht2 : t * t = 1 := hw.t_mul_self
  have htR : t ∈ R := hVR (hw.E8_le_ctxVN (Subgroup.subset_closure (by simp)))
  have htA : ∀ a ∈ A, t * a * t⁻¹ ∈ A := fun a ha => hAN.2 t htR a ha
  have h := S4B.card_le_sq_card_centralizer (A := A) hA.2.1 ht2 htA
  rw [hA.2.2] at h
  nlinarith

theorem U_card_CA_ne_sixteen {R A : Subgroup G} (hR : IsPGroup 2 R)
    (hVR : ctxVN t tau x₁ x₂ lam rho ≤ R) (hA : IsE16In R A) (hAN : NormalIn A R) :
    Nat.card ↥(A ⊓ centralizer ({t} : Set G)) ≠ 16 := by
  intro h16
  have hWS : A ⊓ centralizer ({t} : Set G) ≤ S :=
    (U_CA_normal hw hR hVR hA hAN).1
  have hWA : A ⊓ centralizer ({t} : Set G) ≤ A := inf_le_left
  have hWeq : A ⊓ centralizer ({t} : Set G) = A :=
    Subgroup.eq_of_le_of_card_ge hWA (by rw [h16, hA.2.2])
  have hA_le_S : A ≤ S := hWeq ▸ hWS
  have hA16S : IsE16In S A := ⟨hA_le_S, hA.2.1, hA.2.2⟩
  have htA : t ∈ A := (hw.l47.1 A hA16S).2.1 (Subgroup.subset_closure (by simp))
  exact (hw.U_tG hR hVR hA hAN 1) (by simpa using htA)

theorem U_card_CA_ne_eight {R A : Subgroup G} (hR : IsPGroup 2 R)
    (hVR : ctxVN t tau x₁ x₂ lam rho ≤ R) (hA : IsE16In R A) (hAN : NormalIn A R) :
    Nat.card ↥(A ⊓ centralizer ({t} : Set G)) ≠ 8 := by
  intro h8
  have hnorm := U_CA_normal hw hR hVR hA hAN
  have helem := isElemAbelian_inf_centralizer_one (t := t) hA.2.1
  have hWA : A ⊓ centralizer ({t} : Set G) ≤ A := inf_le_left
  have hx₁ : x₁ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hx₂ : x₂ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hq : x₁ * x₂ ∈ ctxQ t tau x₁ x₂ rho := hw.base_le_Q (mul_mem hx₁ hx₂)
  rcases hw.l46 (A ⊓ centralizer ({t} : Set G)) hnorm helem h8 with
    hcase | hcase | hcase | hcase | hcase
  · exact (hw.U_tG hR hVR hA hAN 1)
      (by simpa using hWA (hcase.symm ▸ Subgroup.subset_closure (by simp)))
  · exact (hw.U_tauQ hR hVR hA hAN (q := 1) (by simp))
      (by simpa using hWA (hcase.symm ▸ Subgroup.subset_closure (by simp)))
  · exact (hw.U_ttauQ hR hVR hA hAN (q := 1) (by simp))
      (by simpa using hWA (hcase.symm ▸ Subgroup.subset_closure (by simp)))
  · exact (hw.U_tauQ hR hVR hA hAN hq)
      (by simpa using hWA (hcase.symm ▸ Subgroup.subset_closure (by simp)))
  · exact (hw.U_ttauQ hR hVR hA hAN hq)
      (by simpa using hWA (hcase.symm ▸ Subgroup.subset_closure (by simp)))

theorem U_card_CA_four {R A : Subgroup G} (hR : IsPGroup 2 R)
    (hVR : ctxVN t tau x₁ x₂ lam rho ≤ R) (hA : IsE16In R A) (hAN : NormalIn A R) :
    Nat.card ↥(A ⊓ centralizer ({t} : Set G)) = 4 := by
  have hdvd : Nat.card ↥(A ⊓ centralizer ({t} : Set G)) ∣ 2 ^ 4 := by
    have h := Subgroup.card_dvd_of_le (inf_le_left : A ⊓ centralizer ({t} : Set G) ≤ A)
    simpa [hA.2.2] using h
  obtain ⟨k, hk4, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rw [hk]
  have hge : 4 ≤ 2 ^ k := by
    have := U_card_CA hw hR hVR hA hAN
    rwa [hk] at this
  have hne8 : 2 ^ k ≠ 8 := by
    have := U_card_CA_ne_eight hw hR hVR hA hAN
    rwa [hk] at this
  have hne16 : 2 ^ k ≠ 16 := by
    have := U_card_CA_ne_sixteen hw hR hVR hA hAN
    rwa [hk] at this
  have hk2 : 2 ≤ k := by
    by_contra h
    have hk1 : k ≤ 1 := by omega
    interval_cases k <;> norm_num at hge
  have hk3 : k ≠ 3 := by
    intro h; exact hne8 (by rw [h]; norm_num)
  have hk4 : k ≠ 4 := by
    intro h; exact hne16 (by rw [h]; norm_num)
  have hk_eq : k = 2 := by omega
  rw [hk_eq]; norm_num

private theorem U_CA_no_conj {R A : Subgroup G} (hR : IsPGroup 2 R)
    (hVR : ctxVN t tau x₁ x₂ lam rho ≤ R) (hA : IsE16In R A) (hAN : NormalIn A R) :
    ∀ g : G, ∀ v ∈ (A ⊓ centralizer ({t} : Set G)), g * t * g⁻¹ ≠ v := by
  intro g v hv h
  exact (hw.U_tG hR hVR hA hAN g)
    (h.symm ▸ (inf_le_left : A ⊓ centralizer ({t} : Set G) ≤ A) hv)

theorem U_CA_eq {R A : Subgroup G} (hR : IsPGroup 2 R)
    (hVR : ctxVN t tau x₁ x₂ lam rho ≤ R) (hA : IsE16In R A) (hAN : NormalIn A R) :
    A ⊓ centralizer ({t} : Set G) = fourGrp x₁ x₂ := by
  have hnorm := U_CA_normal hw hR hVR hA hAN
  have helem := isElemAbelian_inf_centralizer_one (t := t) hA.2.1
  exact (hw.l45 (A ⊓ centralizer ({t} : Set G)) hnorm helem
    (U_card_CA_four hw hR hVR hA hAN) (U_CA_no_conj hw hR hVR hA hAN)).1

theorem U_CS_V {R A : Subgroup G} (hR : IsPGroup 2 R)
    (hVR : ctxVN t tau x₁ x₂ lam rho ≤ R) (hA : IsE16In R A) (hAN : NormalIn A R) :
    S ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) =
      zpowers t ⊔ closure ({x₁, x₂, tau} : Set G) := by
  have hnorm := U_CA_normal hw hR hVR hA hAN
  have helem := isElemAbelian_inf_centralizer_one (t := t) hA.2.1
  have hCS := (hw.l45 (A ⊓ centralizer ({t} : Set G)) hnorm helem
    (U_card_CA_four hw hR hVR hA hAN) (U_CA_no_conj hw hR hVR hA hAN)).2.1
  rw [← U_CA_eq hw hR hVR hA hAN]
  exact hCS

theorem U_VA {R A : Subgroup G} (hR : IsPGroup 2 R)
    (hVR : ctxVN t tau x₁ x₂ lam rho ≤ R) (hA : IsE16In R A) (hAN : NormalIn A R) :
    fourGrp x₁ x₂ ≤ A ∧ ∀ a ∈ A, a * t * a⁻¹ * t⁻¹ ∈ fourGrp x₁ x₂ := by
  have hWV : A ⊓ centralizer ({t} : Set G) = fourGrp x₁ x₂ :=
    U_CA_eq hw hR hVR hA hAN
  have hWA : A ⊓ centralizer ({t} : Set G) ≤ A := inf_le_left
  have htR : t ∈ R := hVR (hw.E8_le_ctxVN (Subgroup.subset_closure (by simp)))
  have ht2 : t * t = 1 := hw.t_mul_self
  refine ⟨hWV ▸ hWA, ?_⟩
  intro a ha
  have hbA : t * a * t⁻¹ ∈ A := hAN.2 t htR a ha
  have ha2 : a * a = 1 := by simpa [pow_two] using hA.2.1.2 a ha
  have ha_inv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hb2 : (t * a * t⁻¹) * (t * a * t⁻¹) = 1 :=
    by simpa [pow_two] using hA.2.1.2 (t * a * t⁻¹) hbA
  have hb_inv : (t * a * t⁻¹)⁻¹ = t * a * t⁻¹ := inv_eq_of_mul_eq_one_right hb2
  haveI : IsMulCommutative ↥A := hA.2.1.1
  have hcomm : (t * a * t⁻¹) * a = a * (t * a * t⁻¹) :=
    congrArg Subtype.val (mul_comm'
      (⟨t * a * t⁻¹, hbA⟩ : ↥A) (⟨a, ha⟩ : ↥A))
  have hceq : a * t * a⁻¹ * t⁻¹ = a * (t * a * t⁻¹)⁻¹ := by
    rw [hb_inv, ha_inv]; group
  have hbc : t * (t * a * t⁻¹) * t⁻¹ = a := by
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    calc t * (t * a * t⁻¹) * t⁻¹ = (t * t) * a * (t⁻¹ * t⁻¹) := by group
      _ = a := by rw [htinv, ht2]; group
  have hconj : t * (a * t * a⁻¹ * t⁻¹) * t⁻¹ = a * t * a⁻¹ * t⁻¹ := by
    rw [hceq]
    calc t * (a * (t * a * t⁻¹)⁻¹) * t⁻¹
        = (t * a * t⁻¹) * (t * (t * a * t⁻¹) * t⁻¹)⁻¹ := by group
      _ = (t * a * t⁻¹) * a⁻¹ := by rw [hbc]
      _ = (t * a * t⁻¹) * a := by rw [ha_inv]
      _ = a * (t * a * t⁻¹) := hcomm
      _ = a * (t * a * t⁻¹)⁻¹ := by rw [hb_inv]
  have hcA : a * t * a⁻¹ * t⁻¹ ∈ A := by
    rw [hceq]
    exact A.mul_mem ha (A.inv_mem hbA)
  have hcent : a * t * a⁻¹ * t⁻¹ ∈ centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc (a * t * a⁻¹ * t⁻¹) * t = (t * (a * t * a⁻¹ * t⁻¹) * t⁻¹) * t := by rw [hconj]
        _ = t * (a * t * a⁻¹ * t⁻¹) := by group)
  rw [← hWV]
  exact ⟨hcA, hcent⟩

end ZNW4

end CFSG.OddStandard.SmallF3.HarrisU33
