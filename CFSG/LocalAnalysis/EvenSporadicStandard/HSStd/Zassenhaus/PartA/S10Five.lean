module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S10Quot
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S10Wr

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup Wreath CFSG.EvenSporadicStandard.HSStd CFSG.Open

structure Five (G : Type) [Group G] (t u y : G) (σ : Equiv.Perm (Fin 5)) where
  tu : t * u = u * t
  t_sq : t * t = 1
  u_sq : u * u = 1
  T_ne : t * u ≠ 1
  y_cube : y * y * y = 1
  ty : t * y = y * t
  uy : u * y = y * u
  σ_sq : σ * σ = 1
  ι : OQuot (Cen y) →* Wr2 (Equiv.Perm (Fin 5))
  ι_inj : Function.Injective ι
  ι_t : ι (oMk (Cen y) ⟨t, mem_Cen.2 ty⟩) = tau
  ι_u : ι (oMk (Cen y) ⟨u, mem_Cen.2 uy⟩) = base σ σ
  ι_range : ι.range = DE4

section Sect

variable {G : Type} [Group G] [Finite G] {t u y : G} {σ : Equiv.Perm (Fin 5)}
variable (F : Five G t u y σ)
include F

theorem Five.T_sq : (t * u) * (t * u) = 1 := by
  calc t * u * (t * u) = t * (u * t) * u := by simp only [mul_assoc]
    _ = t * (t * u) * u := by rw [F.tu]
    _ = (t * t) * (u * u) := by simp only [mul_assoc]
    _ = 1 := by rw [F.t_sq, F.u_sq, one_mul]

theorem Five.yT : y * (t * u) = (t * u) * y := by
  calc y * (t * u) = (y * t) * u := (mul_assoc _ _ _).symm
    _ = (t * y) * u := by rw [F.ty]
    _ = t * (y * u) := mul_assoc _ _ _
    _ = t * (u * y) := by rw [F.uy]
    _ = (t * u) * y := (mul_assoc _ _ _).symm

theorem Five.T_mem_Cen_y : t * u ∈ Cen y := mem_Cen.2 (F.yT).symm

@[expose] def Five.yH : ↥(Cen (t * u)) := ⟨y, mem_Cen.2 F.yT⟩

@[expose] def Five.yBar : MulAut (QuotT (t * u)) := MulAut.conj (mkT (t * u) F.yH)

@[expose] def Five.TC : ↥(Cen y) := ⟨t * u, F.T_mem_Cen_y⟩

theorem Five.TC_sq : F.TC * F.TC = 1 := Subtype.ext F.T_sq

theorem Five.ι_T : F.ι (oMk (Cen y) F.TC) = xW σ := by
  have : F.TC = (⟨t, mem_Cen.2 F.ty⟩ : ↥(Cen y)) * ⟨u, mem_Cen.2 F.uy⟩ := rfl
  rw [this, map_mul, map_mul, F.ι_t, F.ι_u, xW_comm_tau_mul]

abbrev Bt (t u y : G) : Subgroup G := Cen y ⊓ Cen (t * u)

@[expose] def incC (t u y : G) : ↥(Bt t u y) →* ↥(Cen y) := Subgroup.inclusion inf_le_left

@[expose] def incH (t u y : G) : ↥(Bt t u y) →* ↥(Cen (t * u)) := Subgroup.inclusion inf_le_right

@[expose] def piX (t u y : G) : ↥(Bt t u y) →* QuotT (t * u) := (mkT (t * u)).comp (incH t u y)

theorem Five.piX_mem (b : ↥(Bt t u y)) : piX t u y b ∈ autCentralizer F.yBar := by
  show F.yBar (piX t u y b) = piX t u y b
  change mkT (t * u) F.yH * piX t u y b * (mkT (t * u) F.yH)⁻¹ = piX t u y b
  have hc : F.yH * incH t u y b = incH t u y b * F.yH := Subtype.ext (mem_Cen.1 b.2.1).symm
  rw [piX, MonoidHom.comp_apply, ← map_mul, hc, map_mul]
  group

@[expose] def Five.piY : ↥(Bt t u y) →* ↥(autCentralizer F.yBar) :=
  (piX t u y).codRestrict _ F.piX_mem

theorem Five.piY_val (b : ↥(Bt t u y)) : (F.piY b : QuotT (t * u)) = piX t u y b := rfl

theorem Five.comm_of_fix (h : ↥(Cen (t * u))) (hx : F.yBar (mkT (t * u) h) = mkT (t * u) h) :
    (h : G) * y = y * h := by
  have hx' := hx
  change mkT (t * u) F.yH * mkT (t * u) h * (mkT (t * u) F.yH)⁻¹ = mkT (t * u) h at hx'
  have hc : mkT (t * u) (F.yH * h) = mkT (t * u) (h * F.yH) := by
    rw [map_mul, map_mul]
    calc mkT (t * u) F.yH * mkT (t * u) h
        = mkT (t * u) F.yH * mkT (t * u) h * (mkT (t * u) F.yH)⁻¹ * mkT (t * u) F.yH := by group
      _ = mkT (t * u) h * mkT (t * u) F.yH := by rw [hx']
  rw [mkT_eq_mkT_iff F.T_sq] at hc
  have hhy : (h : G) * y = y * h := by
    rcases hc with h1 | h1
    · exact congrArg Subtype.val h1
    · exfalso
      have e1 : (h : G) * y = y * h * (t * u) := congrArg Subtype.val h1
      have hTy := F.yT
      have hTh : (h : G) * (t * u) = (t * u) * h := mem_Cen.1 h.2
      have e2 : (h : G) * (y * y) = (y * y) * h := by
        calc (h : G) * (y * y) = ((h : G) * y) * y := (mul_assoc _ _ _).symm
          _ = (y * h * (t * u)) * y := by rw [e1]
          _ = y * h * ((t * u) * y) := mul_assoc _ _ _
          _ = y * h * (y * (t * u)) := by rw [hTy]
          _ = y * (h * y) * (t * u) := by simp only [mul_assoc]
          _ = y * (y * h * (t * u)) * (t * u) := by rw [e1]
          _ = (y * y) * h * ((t * u) * (t * u)) := by simp only [mul_assoc]
          _ = (y * y) * h := by rw [F.T_sq, mul_one]
      have e3 : (h : G) = (h : G) * (t * u) := by
        calc (h : G) = (h : G) * (y * y * y) := by rw [F.y_cube, mul_one]
          _ = ((h : G) * (y * y)) * y := by simp only [mul_assoc]
          _ = ((y * y) * h) * y := by rw [e2]
          _ = (y * y) * ((h : G) * y) := mul_assoc _ _ _
          _ = (y * y) * (y * h * (t * u)) := by rw [e1]
          _ = (y * y * y) * h * (t * u) := by simp only [mul_assoc]
          _ = h * (t * u) := by rw [F.y_cube, one_mul]
      apply F.T_ne
      exact mul_left_cancel (a := (h : G)) (e3.symm.trans (mul_one _).symm)
  exact hhy

theorem Five.piY_surjective : Function.Surjective F.piY := by
  rintro ⟨x, hx⟩
  obtain ⟨h, rfl⟩ := mkT_surjective (t * u) x
  have hhy := F.comm_of_fix h hx
  refine ⟨⟨h, ⟨mem_Cen.2 hhy, h.2⟩⟩, ?_⟩
  exact Subtype.ext rfl

@[expose] def Five.psi : ↥(Bt t u y) →* Wr2 (Equiv.Perm (Fin 5)) :=
  F.ι.comp ((oMk (Cen y)).comp (incC t u y))

theorem Five.incC_comm (b : ↥(Bt t u y)) : incC t u y b * F.TC = F.TC * incC t u y b :=
  Subtype.ext (mem_Cen.1 b.2.2)

theorem Five.psi_mem (b : ↥(Bt t u y)) : F.psi b ∈ GW σ := by
  have hh : F.psi b * F.ι (oMk (Cen y) F.TC) = F.ι (oMk (Cen y) F.TC) * F.psi b := by
    rw [Five.psi]
    simp only [MonoidHom.comp_apply, ← map_mul]
    rw [F.incC_comm b]
  rw [mem_centralizer_singleton_iff, ← F.ι_T]
  exact hh

@[expose] def Five.phi : ↥(Bt t u y) →* ↥(GW σ) := F.psi.codRestrict _ F.psi_mem

@[expose] noncomputable def Five.lam : ↥(Bt t u y) →* Equiv.Perm (Fin 5) :=
  (kapW σ F.σ_sq).comp F.phi

theorem Five.phi_val (b : ↥(Bt t u y)) : (F.phi b : Wr2 (Equiv.Perm (Fin 5))) = F.psi b := rfl

theorem Five.lam_surjective : Function.Surjective F.lam := by
  intro a
  have hmem : ((nuW σ F.σ_sq a : GW σ) : Wr2 (Equiv.Perm (Fin 5))) ∈ F.ι.range := by
    rw [F.ι_range, mem_DE4]
    exact sgnProd_GW σ F.σ_sq _
  obtain ⟨d, hd⟩ := hmem
  have hdc : d ∈ centralizer ({oMk (Cen y) F.TC} : Set (OQuot (Cen y))) := by
    rw [mem_centralizer_singleton_iff]
    apply F.ι_inj
    rw [map_mul, map_mul, hd, F.ι_T]
    exact mem_centralizer_singleton_iff.1 (nuW σ F.σ_sq a).2
  have hO : Odd (Nat.card (fusionOddCore ↥(Cen y))) := natCard_fusionOddCore_odd' _
  have hmap := map_centralizer_eq_of_odd (fusionOddCore ↥(Cen y)) hO (t := F.TC) F.TC_sq
  have hdc' : d ∈ (centralizer ({F.TC} : Set ↥(Cen y))).map
      (QuotientGroup.mk' (fusionOddCore ↥(Cen y))) := by
    rw [hmap]
    exact hdc
  obtain ⟨b', hb', rfl⟩ := hdc'
  have hb'c : (b' : G) * (t * u) = (t * u) * b' :=
    congrArg Subtype.val (mem_centralizer_singleton_iff.1 hb')
  refine ⟨⟨b', ⟨b'.2, mem_Cen.2 hb'c⟩⟩, ?_⟩
  have h1 : F.phi ⟨b', ⟨b'.2, mem_Cen.2 hb'c⟩⟩ = nuW σ F.σ_sq a := by
    refine Subtype.ext ?_
    rw [F.phi_val, ← hd]
    rfl
  rw [Five.lam, MonoidHom.comp_apply, h1, kapW_nuW]

theorem Five.piY_ker_le : F.piY.ker ≤ F.lam.ker := by
  intro b hb
  rw [MonoidHom.mem_ker] at hb ⊢
  have h1 : mkT (t * u) (incH t u y b) = 1 := congrArg Subtype.val hb
  rw [← map_one (mkT (t * u)), mkT_eq_mkT_iff F.T_sq] at h1
  rcases h1 with h2 | h2
  · have : b = 1 := by
      refine Subtype.ext ?_
      exact (congrArg Subtype.val h2).symm
    rw [this, map_one]
  · have hb1 : (b : G) = t * u := by
      have h3 : (1 : G) = (b : G) * (t * u) := congrArg Subtype.val h2
      have := eq_inv_of_mul_eq_one_left h3.symm
      rw [this, inv_eq_of_mul_eq_one_right F.T_sq]
    have : F.phi b = zW σ := by
      refine Subtype.ext ?_
      rw [F.phi_val]
      change F.ι (oMk (Cen y) (incC t u y b)) = xW σ
      have : incC t u y b = F.TC := Subtype.ext hb1
      rw [this, F.ι_T]
    rw [Five.lam, MonoidHom.comp_apply, this, (kapW_eq_one_iff σ F.σ_sq _).2 (Or.inr rfl)]

theorem Five.ker_lam (b : ↥(Bt t u y)) (hb : F.lam b = 1) :
    ∃ b' : ↥(Bt t u y), oMk (Cen y) (incC t u y b') = 1 ∧ F.piY b' = F.piY b := by
  rw [Five.lam, MonoidHom.comp_apply, kapW_eq_one_iff] at hb
  have hι : ∀ w : Wr2 (Equiv.Perm (Fin 5)), w = F.ι (oMk (Cen y) (incC t u y b)) →
      (w = 1 ∨ w = xW σ) → oMk (Cen y) (incC t u y b) = 1 ∨
        oMk (Cen y) (incC t u y b) = oMk (Cen y) F.TC := by
    intro w hw h
    rcases h with h | h
    · left
      apply F.ι_inj
      rw [← hw, h, map_one]
    · right
      apply F.ι_inj
      rw [← hw, h, F.ι_T]
  have hc : (F.phi b : Wr2 (Equiv.Perm (Fin 5))) = 1 ∨ (F.phi b : Wr2 (Equiv.Perm (Fin 5))) =
      xW σ := by
    rcases hb with h | h
    · left; rw [h]; rfl
    · right; rw [h]; rfl
  rcases hι _ rfl hc with h | h
  · exact ⟨b, h, rfl⟩
  ·
    have hTB : t * u ∈ Bt t u y :=
      ⟨F.T_mem_Cen_y, mem_Cen.2 rfl⟩
    refine ⟨⟨t * u, hTB⟩ * b, ?_, ?_⟩
    · rw [map_mul, map_mul]
      have : incC t u y ⟨t * u, hTB⟩ = F.TC := rfl
      rw [this, h, ← map_mul, F.TC_sq, map_one]
    · apply Subtype.ext
      rw [Five.piY_val, Five.piY_val, map_mul]
      have : piX t u y ⟨t * u, hTB⟩ = 1 := by
        change mkT (t * u) (incH t u y ⟨t * u, hTB⟩) = 1
        exact mkT_wOf (t * u)
      rw [this, one_mul]

theorem five_nonempty_mulEquiv :
    Nonempty (↥(autCentralizer F.yBar) ⧸ fusionOddCore ↥(autCentralizer F.yBar) ≃*
      Equiv.Perm (Fin 5)) := by
  let lamBar : ↥(autCentralizer F.yBar) →* Equiv.Perm (Fin 5) :=
    F.piY.liftOfSurjective F.piY_surjective ⟨F.lam, F.piY_ker_le⟩
  have hcomp : ∀ b, lamBar (F.piY b) = F.lam b := fun b =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨F.lam, F.piY_ker_le⟩ b
  have hsurj : Function.Surjective lamBar := by
    intro a
    obtain ⟨b, hb⟩ := F.lam_surjective a
    exact ⟨F.piY b, by rw [hcomp, hb]⟩
  refine nonempty_mulEquiv_quotient_oddCore lamBar hsurj ?_
  set Oy : Subgroup ↥(Bt t u y) := (fusionOddCore ↥(Cen y)).comap (incC t u y) with hOy
  have hOyodd : Odd (Nat.card Oy) := by
    have hdvd : Nat.card Oy ∣ Nat.card (fusionOddCore ↥(Cen y)) :=
      Subgroup.card_comap_dvd_of_injective _ _ (Subgroup.inclusion_injective _)
    exact Odd.of_dvd_nat (natCard_fusionOddCore_odd' _) hdvd
  have hle : lamBar.ker ≤ Oy.map F.piY := by
    intro x hx
    obtain ⟨b, rfl⟩ := F.piY_surjective x
    rw [MonoidHom.mem_ker, hcomp] at hx
    obtain ⟨b', hb', hpi⟩ := F.ker_lam b hx
    refine ⟨b', ?_, hpi⟩
    show incC t u y b' ∈ fusionOddCore ↥(Cen y)
    exact (QuotientGroup.eq_one_iff _).1 hb'
  have h1 : Nat.card lamBar.ker ∣ Nat.card (Oy.map F.piY) := Subgroup.card_dvd_of_le hle
  have h2 : Nat.card (Oy.map F.piY) ∣ Nat.card Oy := Subgroup.card_map_dvd _ _
  exact Odd.of_dvd_nat hOyodd (h1.trans h2)

theorem Five.yBar_ne_one (hnc : ∃ h : ↥(Cen (t * u)), (h : G) * y ≠ y * h) : F.yBar ≠ 1 := by
  intro h1
  obtain ⟨h, hh⟩ := hnc
  apply hh
  apply F.comm_of_fix h
  rw [h1]
  rfl

theorem five_nonempty_mulEquiv_centralizer :
    Nonempty (↥(centralizer ({mkT (t * u) F.yH} : Set (QuotT (t * u)))) ⧸
      fusionOddCore ↥(centralizer ({mkT (t * u) F.yH} : Set (QuotT (t * u)))) ≃*
        Equiv.Perm (Fin 5)) := by
  have h := five_nonempty_mulEquiv F
  rwa [Five.yBar, autCentralizer_conj] at h

theorem Five.orderOf_mkT_yH (hnc : ∃ h : ↥(Cen (t * u)), (h : G) * y ≠ y * h) :
    orderOf (mkT (t * u) F.yH) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime ?_ fun h => F.yBar_ne_one hnc (by rw [Five.yBar, h, map_one])
  have h3 : F.yH ^ 3 = 1 := by
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, pow_succ, pow_succ, pow_one]
    have e : ((F.yH : ↥(Cen (t * u))) : G) = y := rfl
    rw [e]
    exact F.y_cube
  rw [← map_pow, h3, map_one]

end Sect

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
