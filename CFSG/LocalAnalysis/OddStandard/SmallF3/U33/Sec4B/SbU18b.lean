module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbU18a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Sq

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

private lemma isElemAbelian_inf_centralizer {A : Subgroup G}
    (hA : CFSG.Open.IsElemAbelian 2 A) :
    CFSG.Open.IsElemAbelian 2 (A ⊓ centralizer ({t} : Set G)) := by
  refine ⟨IsMulCommutative.of_comm fun x y => Subtype.ext ?_,
    fun x hx => hA.2 x (Subgroup.mem_inf.mp hx).1⟩
  haveI : IsMulCommutative ↥A := hA.1
  exact congrArg (Subtype.val : ↥A → G) (mul_comm'
    (⟨(x : G), (Subgroup.mem_inf.mp x.2).1⟩ : ↥A)
    (⟨(y : G), (Subgroup.mem_inf.mp y.2).1⟩ : ↥A))

theorem l18_U_W_normal (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) {R A : Subgroup G}
    (hR : IsPGroup 2 R) (h𝒮R : 𝒮 ≤ R) (hA : IsE16In R A) (hAN : NormalIn A R) :
    NormalIn (A ⊓ centralizer ({t} : Set G)) S := by
  obtain ⟨-, -, hSS, -⟩ := l18_le_sylow hc.toCtx18S
  have hSR : S ≤ R := hSS.trans h𝒮R
  have hcent : R ⊓ centralizer ({t} : Set G) = S :=
    c17_cent_eq hc.toCtx13.toCtx11.toCtx10 hR hSR
  refine ⟨?_, ?_⟩
  · intro w hw
    rw [← hcent]
    exact ⟨hA.1 (Subgroup.mem_inf.mp hw).1, (Subgroup.mem_inf.mp hw).2⟩
  · intro s hs w hw
    rw [Subgroup.mem_inf] at hw ⊢
    have hs' : s ∈ centralizer ({t} : Set G) := hc.le_invCent hs
    exact ⟨hAN.2 s (hSR hs) w hw.1,
      mul_mem (mul_mem hs' hw.2) (inv_mem hs')⟩

theorem l18_U_card_W (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) {R A : Subgroup G}
    (hR : IsPGroup 2 R) (h𝒮R : 𝒮 ≤ R) (hA : IsE16In R A) (hAN : NormalIn A R) :
    4 ≤ Nat.card ↥(A ⊓ centralizer ({t} : Set G)) := by
  have ht2 : t * t = 1 := S4A.t_mul_self hc.hyp
  have htR : t ∈ R := h𝒮R (l18_T_le_sylow hc.toCtx18S).1
  have htA : ∀ a ∈ A, t * a * t⁻¹ ∈ A := fun a ha => hAN.2 t htR a ha
  have h := card_le_sq_card_centralizer (A := A) hA.2.1 ht2 htA
  rw [hA.2.2] at h
  nlinarith

theorem l18_U_card_W_ne_sixteen (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) {R A : Subgroup G}
    (hR : IsPGroup 2 R) (h𝒮R : 𝒮 ≤ R) (hA : IsE16In R A) (hAN : NormalIn A R) :
    Nat.card ↥(A ⊓ centralizer ({t} : Set G)) ≠ 16 := by
  intro h16
  have hWS : A ⊓ centralizer ({t} : Set G) ≤ S := (l18_U_W_normal hc hR h𝒮R hA hAN).1
  have hWA : A ⊓ centralizer ({t} : Set G) ≤ A := inf_le_left
  have hWeq : A ⊓ centralizer ({t} : Set G) = A :=
    Subgroup.eq_of_le_of_card_ge hWA (by rw [h16, hA.2.2])
  have hA_le_S : A ≤ S := hWeq ▸ hWS
  have hA16S : IsE16In S A := ⟨hA_le_S, hA.2.1, hA.2.2⟩
  have htA : t ∈ A := (hc.l47.1 A hA16S).2.1 (Subgroup.subset_closure (by simp))
  exact (l18_U_tG hc hR h𝒮R hA hAN 1) (by simpa using htA)

theorem l18_U_card_W_ne_eight (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) {R A : Subgroup G}
    (hR : IsPGroup 2 R) (h𝒮R : 𝒮 ≤ R) (hA : IsE16In R A) (hAN : NormalIn A R) :
    Nat.card ↥(A ⊓ centralizer ({t} : Set G)) ≠ 8 := by
  intro h8
  have hnorm := l18_U_W_normal hc hR h𝒮R hA hAN
  have helem := isElemAbelian_inf_centralizer (t := t) hA.2.1
  have hWA : A ⊓ centralizer ({t} : Set G) ≤ A := inf_le_left
  have hx₁ : x₁ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hx₂ : x₂ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hq : x₁ * x₂ ∈ ctxQ t tau x₁ x₂ rho := hc.base_le_Q (mul_mem hx₁ hx₂)
  rcases hc.l46 (A ⊓ centralizer ({t} : Set G)) hnorm helem h8 with
    hcase | hcase | hcase | hcase | hcase
  · exact (l18_U_tG hc hR h𝒮R hA hAN 1)
      (by simpa using hWA (hcase.symm ▸ Subgroup.subset_closure (by simp)))
  · exact (l18_U_tauQ hc hR h𝒮R hA hAN (q := 1) (by simp))
      (by simpa using hWA (hcase.symm ▸ Subgroup.subset_closure (by simp)))
  · exact (l18_U_tQ hc hR h𝒮R hA hAN (q := 1) (by simp)).2
      (by simpa using hWA (hcase.symm ▸ Subgroup.subset_closure (by simp)))
  · exact (l18_U_tauQ hc hR h𝒮R hA hAN hq)
      (by simpa using hWA (hcase.symm ▸ Subgroup.subset_closure (by simp)))
  · exact (l18_U_tQ hc hR h𝒮R hA hAN hq).2
      (by simpa using hWA (hcase.symm ▸ Subgroup.subset_closure (by simp)))

private lemma l18_W_card_four (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) {R A : Subgroup G}
    (hR : IsPGroup 2 R) (h𝒮R : 𝒮 ≤ R) (hA : IsE16In R A) (hAN : NormalIn A R) :
    Nat.card ↥(A ⊓ centralizer ({t} : Set G)) = 4 := by
  have hdvd : Nat.card ↥(A ⊓ centralizer ({t} : Set G)) ∣ 2 ^ 4 := by
    have h := Subgroup.card_dvd_of_le (inf_le_left : A ⊓ centralizer ({t} : Set G) ≤ A)
    simpa [hA.2.2] using h
  obtain ⟨k, hk4, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rw [hk]
  have hge : 4 ≤ 2 ^ k := by
    have := l18_U_card_W hc hR h𝒮R hA hAN
    rwa [hk] at this
  have hne8 : 2 ^ k ≠ 8 := by
    have := l18_U_card_W_ne_eight hc hR h𝒮R hA hAN
    rwa [hk] at this
  have hne16 : 2 ^ k ≠ 16 := by
    have := l18_U_card_W_ne_sixteen hc hR h𝒮R hA hAN
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

private lemma l18_W_no_conj (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) {R A : Subgroup G}
    (hR : IsPGroup 2 R) (h𝒮R : 𝒮 ≤ R) (hA : IsE16In R A) (hAN : NormalIn A R) :
    ∀ g : G, ∀ v ∈ (A ⊓ centralizer ({t} : Set G)), g * t * g⁻¹ ≠ v := by
  intro g v hv h
  exact (l18_U_tG hc hR h𝒮R hA hAN g)
    (h.symm ▸ (inf_le_left : A ⊓ centralizer ({t} : Set G) ≤ A) hv)

theorem l18_U_W_eq (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) {R A : Subgroup G}
    (hR : IsPGroup 2 R) (h𝒮R : 𝒮 ≤ R) (hA : IsE16In R A) (hAN : NormalIn A R) :
    A ⊓ centralizer ({t} : Set G) = fourGrp x₁ x₂ := by
  have hnorm := l18_U_W_normal hc hR h𝒮R hA hAN
  have helem := isElemAbelian_inf_centralizer (t := t) hA.2.1
  exact (hc.l45 (A ⊓ centralizer ({t} : Set G)) hnorm helem
    (l18_W_card_four hc hR h𝒮R hA hAN) (l18_W_no_conj hc hR h𝒮R hA hAN)).1

theorem l18_U_CS_V (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) {R A : Subgroup G}
    (hR : IsPGroup 2 R) (h𝒮R : 𝒮 ≤ R) (hA : IsE16In R A) (hAN : NormalIn A R) :
    S ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) =
      zpowers t ⊔ closure ({x₁, x₂, tau} : Set G) := by
  have hnorm := l18_U_W_normal hc hR h𝒮R hA hAN
  have helem := isElemAbelian_inf_centralizer (t := t) hA.2.1
  have hCS := (hc.l45 (A ⊓ centralizer ({t} : Set G)) hnorm helem
    (l18_W_card_four hc hR h𝒮R hA hAN) (l18_W_no_conj hc hR h𝒮R hA hAN)).2.1
  rw [← l18_U_W_eq hc hR h𝒮R hA hAN]
  exact hCS

theorem l18_U_VA (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) {R A : Subgroup G}
    (hR : IsPGroup 2 R) (h𝒮R : 𝒮 ≤ R) (hA : IsE16In R A) (hAN : NormalIn A R) :
    fourGrp x₁ x₂ ≤ A ∧ ∀ a ∈ A, a * t * a⁻¹ * t⁻¹ ∈ fourGrp x₁ x₂ := by
  have hWV : A ⊓ centralizer ({t} : Set G) = fourGrp x₁ x₂ :=
    l18_U_W_eq hc hR h𝒮R hA hAN
  have hWA : A ⊓ centralizer ({t} : Set G) ≤ A := inf_le_left
  have htR : t ∈ R := h𝒮R (l18_T_le_sylow hc.toCtx18S).1
  have ht2 : t * t = 1 := S4A.t_mul_self hc.hyp
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

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
