module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarCentre
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Iso
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporAutHS

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore
  CFSG.ComponentClassification.PerfectAutomorphisms
open scoped commutatorElement

section Construction

variable {E : Type} [Group E]

@[expose] noncomputable def CoverMaps.centerQuotEquiv (M : CoverMaps E) : (E ⧸ center E) ≃* ↥hsP :=
  (QuotientGroup.quotientMulEquivOfEq M.ker_pi_eq.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective M.π M.π_surj)

variable {H : Type} [Group H] (E' : Subgroup H) [E'.Normal]

@[expose] noncomputable def thetaAut (M : CoverMaps ↥E') : H →* MulAut ↥hsP :=
  (MulAut.congr M.centerQuotEquiv).toMonoidHom.comp
    ((centerQuotientHom ↥E').comp MulAut.conjNormal)

theorem thetaAut_apply (M : CoverMaps ↥E') (h : H) (x : ↥E') :
    thetaAut E' M h (M.π x) = M.π (MulAut.conjNormal h x) := by
  change M.centerQuotEquiv (onCenterQuotient (MulAut.conjNormal h)
    (M.centerQuotEquiv.symm (M.π x))) = _
  have h1 : M.centerQuotEquiv.symm (M.π x) = QuotientGroup.mk' (center ↥E') x :=
    (MulEquiv.symm_apply_eq _).2 rfl
  rw [h1, onCenterQuotient_apply_mk]
  rfl

end Construction

section Data

variable {H : Type} [Group H] {E : Subgroup H} [E.Normal]

structure ThetaData (E : Subgroup H) [E.Normal] (M : CoverMaps ↥E) where
  θ : H →* hsR
  e : hsR ≃* MulAut ↥hsP
  he : ∀ (x : hsR) (p : ↥hsP), ((e x p : ↥hsP) : Equiv.Perm (Fin 3850)) =
    (x : Equiv.Perm (Fin 3850)) * (p : Equiv.Perm (Fin 3850)) * (x : Equiv.Perm (Fin 3850))⁻¹
  conj : ∀ (h : H) (x : ↥E), (θ h : Equiv.Perm (Fin 3850)) * (M.π x : Equiv.Perm (Fin 3850)) *
    (θ h : Equiv.Perm (Fin 3850))⁻¹ = (M.π (MulAut.conjNormal h x) : Equiv.Perm (Fin 3850))

theorem exists_thetaData
    (M : CoverMaps ↥E) :
    Nonempty (ThetaData E M) := by
  obtain ⟨e, he, -⟩ := hs_full_automorphism_model
  refine ⟨⟨e.symm.toMonoidHom.comp (thetaAut E M), e, he, fun h x => ?_⟩⟩
  have h1 := he (e.symm (thetaAut E M h)) (M.π x)
  rw [MulEquiv.apply_symm_apply, thetaAut_apply] at h1
  exact h1.symm

variable {M : CoverMaps ↥E} (D : ThetaData E M)

theorem conjNormal_eq_of_comm {h : H} {x : ↥E} (hc : h * (x : H) = (x : H) * h) :
    MulAut.conjNormal h x = x := by
  apply Subtype.ext
  rw [MulAut.conjNormal_apply, hc]
  group

theorem ThetaData.theta_inner
    (x : ↥E) :
    ((D.θ (x : H) : hsR) : Equiv.Perm (Fin 3850)) = (M.π x : Equiv.Perm (Fin 3850)) := by
  have hcent : ((M.π x : ↥hsP) : Equiv.Perm (Fin 3850))⁻¹ * (D.θ (x : H) : Equiv.Perm (Fin 3850)) ∈
      centralizer (hsP : Set (Equiv.Perm (Fin 3850))) := by
    rw [mem_centralizer_iff]
    intro p hp
    obtain ⟨y, hy⟩ := M.π_surj ⟨p, hp⟩
    have h1 := D.conj (x : H) y
    have h2 : M.π (MulAut.conjNormal (x : H) y) = M.π x * M.π y * (M.π x)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
    rw [h2] at h1
    have hy' : ((M.π y : ↥hsP) : Equiv.Perm (Fin 3850)) = p := congrArg Subtype.val hy
    have h3 : (D.θ (x : H) : Equiv.Perm (Fin 3850)) * p * (D.θ (x : H) : Equiv.Perm (Fin 3850))⁻¹ =
        ((M.π x : ↥hsP) : Equiv.Perm (Fin 3850)) * p *
          ((M.π x : ↥hsP) : Equiv.Perm (Fin 3850))⁻¹ := by
      rw [← hy']
      simpa using h1
    calc p * (((M.π x : ↥hsP) : Equiv.Perm (Fin 3850))⁻¹ * (D.θ (x : H) : Equiv.Perm (Fin 3850)))
        = ((M.π x : ↥hsP) : Equiv.Perm (Fin 3850))⁻¹ * (((M.π x : ↥hsP) : Equiv.Perm (Fin 3850)) *
            p * ((M.π x : ↥hsP) : Equiv.Perm (Fin 3850))⁻¹) *
            (D.θ (x : H) : Equiv.Perm (Fin 3850)) := by group
      _ = ((M.π x : ↥hsP) : Equiv.Perm (Fin 3850))⁻¹ * ((D.θ (x : H) : Equiv.Perm (Fin 3850)) * p *
            (D.θ (x : H) : Equiv.Perm (Fin 3850))⁻¹) * (D.θ (x : H) : Equiv.Perm (Fin 3850)) := by
          rw [h3]
      _ = _ := by group
  rw [hs_centralizer_eq_bot, mem_bot, inv_mul_eq_one] at hcent
  exact hcent.symm

theorem ThetaData.mem_of_ker (hE : IsHSCover H E) {h : H} (h1 : D.θ h = 1) : h ∈ E := by
  have := hE.perfect
  have key : ∀ x : ↥E, x⁻¹ * (MulAut.conjNormal h x) ∈ center ↥E := by
    intro x
    rw [← M.ker_pi_eq, MonoidHom.mem_ker, map_mul, map_inv]
    have h2 := D.conj h x
    rw [h1] at h2
    have h3 : M.π x = M.π (MulAut.conjNormal h x) := Subtype.ext (by simpa using h2)
    rw [← h3, inv_mul_cancel]
  have hid := hom_eq_id_of_central_displacement (MulAut.conjNormal h).toMonoidHom key
  have hα : MulAut.conjNormal h = (1 : MulAut ↥E) :=
    MulEquiv.ext fun x => congrArg (fun f : ↥E →* ↥E => f x) hid
  have hker : h ∈ (MulAut.conjNormal : H →* MulAut ↥E).ker := hα
  rw [ker_conjNormal] at hker
  exact hE.centralizer_le hker

theorem ThetaData.mem_of_theta_mem
    (hE : IsHSCover H E) {h : H}
    (hh : (D.θ h : Equiv.Perm (Fin 3850)) ∈ hsP) : h ∈ E := by
  obtain ⟨y, hy⟩ := M.π_surj ⟨(D.θ h : Equiv.Perm (Fin 3850)), hh⟩
  have h1 : D.θ (y : H) = D.θ h := Subtype.ext (by
    rw [D.theta_inner y, hy])
  have h2 : h * (y : H)⁻¹ ∈ E := D.mem_of_ker hE (by rw [map_mul, map_inv, h1, mul_inv_cancel])
  have := E.mul_mem h2 y.2
  simpa using this

end Data

section Centralizer

theorem factorization_two_card_hsP : (44352000 : ℕ).factorization 2 = 9 := by
  have h : (44352000 : ℕ) = 2 ^ 9 * 86625 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

variable
  {H : Type} [Group H] [Finite H] {E : Subgroup H} [E.Normal]

theorem ThetaData.mem_of_centralizer (hE : IsHSCover H E) (M : CoverModel ↥E)
    (D : ThetaData E M.toCoverMaps) {h : H}
    (hc : ∀ y ∈ M.T0.map E.subtype, h * y = y * h) : h ∈ E := by
  have hZ := hE.card_center
  set β : MulAut ↥hsP := D.e (D.θ h) with hβ
  have hfix : ∀ p ∈ M.T0.map M.π, β p = p := by
    rintro _ ⟨x, hx, rfl⟩
    apply Subtype.ext
    rw [hβ, D.he, D.conj]
    have hxc : h * ((x : ↥E) : H) = ((x : ↥E) : H) * h := hc _ ⟨x, hx, rfl⟩
    rw [conjNormal_eq_of_comm hxc]
  have hcardP : Nat.card ↥(M.T0.map M.π) = 2 ^ (Nat.card ↥hsP).factorization 2 := by
    rw [M.card_map_pi_T0 hZ, card_hsP, factorization_two_card_hsP]
    norm_num
  obtain ⟨l, hl⟩ := CFSG.QuasithinUnique.Ch1.hsAutInner ↥hsP ⟨hsPermEquiv.symm⟩ β
    ⟨Sylow.ofCard (p := 2) (M.T0.map M.π) hcardP, hfix⟩
  have hPR : hsP ≤ hsR := le_sup_left
  let x₀ : hsR := ⟨((l : ↥hsP) : Equiv.Perm (Fin 3850))⁻¹, hPR (hsP.inv_mem l.2)⟩
  have hex : D.e x₀ = β := by
    apply MulEquiv.ext
    intro p
    apply Subtype.ext
    rw [D.he, hl p]
    simp [x₀]
  have hθ : D.θ h = x₀ := D.e.injective (hβ.symm.trans hex.symm)
  have hmem : (D.θ h : Equiv.Perm (Fin 3850)) ∈ hsP := by
    rw [hθ]
    exact hsP.inv_mem l.2
  exact D.mem_of_theta_mem hE hmem

end Centralizer

end CFSG.EvenSporadicStandard.TwoHS
