module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.TwHSModel
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentSporHS

public section

open scoped commutatorElement

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open CFSG.QuasithinUnique.Id2519
open CFSG.QuasithinUnique.Id2519.SporHS
open CFSG.QuasithinUnique.Id2519.HSAut
open CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.Schreier

private theorem tw_congr_conj {G H : Type*} [Group G] [Group H] (e : G ≃* H) (x : G) :
    MulAut.congr e (MulAut.conj x) = MulAut.conj (e x) := by
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem twHSFusion_holds :
    TwHSFusion := by
  intro N _ _ hN τ hτ2 B eB hfixB g hg
  obtain ⟨e⟩ := hN
  let θ : N ≃* hsP := e.trans hsPermEquiv
  set b : N := ((eB.symm abType22 : B) : N) with hb
  set α : MulAut hsP := MulAut.congr θ τ with hα
  have hα2 : α * α = 1 := by
    rw [hα, ← map_mul, hτ2, map_one]
  obtain ⟨eAut, heAut, -⟩ := hs_full_automorphism_model
  have hPR : hsP ≤ hsR := le_sup_left
  have heAut_conj : MulAut.conj (θ b) = eAut ⟨θ b, hPR (θ b).2⟩ := by
    apply MulEquiv.ext
    intro p
    apply Subtype.ext
    rw [heAut]
    rfl
  by_cases hα1 : α = 1
  ·
    have hτ1 : τ = 1 := (MulAut.congr θ).injective (by rw [← hα, hα1, map_one])
    have hconj : MulAut.conj b = 1 := by
      simpa [hτ1] using hg.symm
    have hconj' : MulAut.conj (θ b) = 1 := by
      have h := congrArg (MulAut.congr θ) hconj
      rwa [tw_congr_conj θ b, map_one] at h
    have hθb1 : (⟨θ b, hPR (θ b).2⟩ : hsR) = 1 :=
      eAut.injective (by rw [← heAut_conj, hconj', map_one])
    have hθb_eq : θ b = 1 := by
      apply Subtype.ext
      simpa using congrArg (fun z : hsR => (z : Equiv.Perm (Fin 3850))) hθb1
    have hb1 : b = 1 := θ.injective (by rw [hθb_eq, map_one])
    have hbB1 : eB.symm abType22 = 1 := by
      apply Subtype.ext
      show (((eB.symm abType22 : B) : N)) = ((1 : B) : N)
      rw [← hb, hb1]
      rfl
    have hab1 : abType22 = 1 := by
      have h := congrArg (fun z : B => eB z) hbB1
      simpa using h
    exact abType22_ne_one hab1
  ·
    obtain ⟨r, hr, g₁, hg₁, x, hxform, hxg, hFmap⟩ := fix_data α hα2 hα1
    have hfix_θ : ∀ n : N, n ∈ B → α (θ n) = θ n := by
      intro n hn
      have h1 : τ n = n := hfixB ⟨n, hn⟩
      simpa [hα, MulAut.congr_apply, h1]
    let ρ : N →* Equiv.Perm (Fin 3850) :=
      (MulAut.conj g₁⁻¹).toMonoidHom.comp (hsP.subtype.comp θ.toMonoidHom)
    have hρinj : Function.Injective ρ := fun a b hab =>
      θ.injective (hsP.subtype_injective ((MulAut.conj g₁⁻¹).injective hab))
    have hmap_le : B.map ρ ≤ hsP ⊓ Subgroup.centralizer
        ({tp 3850 r.rep} : Set (Equiv.Perm (Fin 3850))) := by
      rintro _ ⟨n, hn, rfl⟩
      have hmem : (θ n : Equiv.Perm (Fin 3850)) ∈ (fixSubgroup α).map hsP.subtype :=
        ⟨θ n, mem_fixSubgroup.mpr (hfix_θ n hn), rfl⟩
      rw [hFmap] at hmem
      obtain ⟨c, hc, hc_eq⟩ := hmem
      have hρn : ρ n = c := by
        have hρ : ρ n = g₁⁻¹ * (θ n : Equiv.Perm (Fin 3850)) * g₁ := by
          simp [ρ, MulAut.conj_apply]
        rw [hρ, ← hc_eq]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        group
      rwa [hρn]
    have hA8perf : Group.IsPerfect ↥(alternatingGroup (Fin 8)) :=
      Subgroup.isPerfect_iff.mpr
        (commutator_alternatingGroup_eq_self (α := Fin 8) (by norm_num))
    have hcardA8 : Nat.card ↥(alternatingGroup (Fin 8)) = 20160 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
      norm_num
    have hcardB : Nat.card ↥B = 20160 := by
      rw [Nat.card_congr eB.toEquiv, hcardA8]
    have hcardBmap : Nat.card ↥(B.map ρ) = 20160 := by
      rw [Subgroup.card_map_of_injective (K := B) (f := ρ) hρinj, hcardB]
    have hBperf : Group.IsPerfect ↥B := by
      haveI : Group.IsPerfect ↥(alternatingGroup (Fin 8)) := hA8perf
      exact Group.IsPerfect.ofSurjective (f := eB.symm.toMonoidHom) eB.symm.surjective
    have hperfect : B.map ρ = ⁅B.map ρ, B.map ρ⁆ := by
      have hcomm : ⁅B, B⁆ = B := Subgroup.isPerfect_iff.mp hBperf
      calc B.map ρ = (⁅B, B⁆).map ρ := by rw [hcomm]
        _ = ⁅B.map ρ, B.map ρ⁆ := by rw [Subgroup.map_commutator]
    have hCr : Nat.card ↥(hsP ⊓ Subgroup.centralizer
        ({tp 3850 r.rep} : Set (Equiv.Perm (Fin 3850)))) = r.centOrder :=
      (hs_involution_centralizers.2.2.2.1 r hr).2.2.2.2.1
    have hdvd : 20160 ∣ r.centOrder := by
      rw [← hcardBmap, ← hCr]
      exact Subgroup.card_dvd_of_le hmap_le
    rcases hsRows_cases hr with h0 | ⟨hrep, -, hord, -⟩ | ⟨hrep, hord⟩ | h3
    · exfalso
      exact (by norm_num : ¬ (20160 ∣ 7680)) (h0 ▸ hdvd)
    · exfalso
      exact (by norm_num : ¬ (20160 ∣ 2880)) (hord ▸ hdvd)
    ·
      have hCU : hsP ⊓ Subgroup.centralizer
          ({tp 3850 r.rep} : Set (Equiv.Perm (Fin 3850))) = outerC := by
        rw [hrep]
        rfl
      have hle_outerE : B.map ρ ≤ outerE := by
        calc B.map ρ = ⁅B.map ρ, B.map ρ⁆ := hperfect
          _ ≤ ⁅hsP ⊓ Subgroup.centralizer
                ({tp 3850 r.rep} : Set (Equiv.Perm (Fin 3850))),
              hsP ⊓ Subgroup.centralizer
                ({tp 3850 r.rep} : Set (Equiv.Perm (Fin 3850)))⁆ :=
              Subgroup.commutator_mono hmap_le hmap_le
          _ = ⁅outerC, outerC⁆ := by rw [hCU]
          _ = outerE := commutator_outerC_eq
      have hcard_outerE : Nat.card ↥outerE = Nat.card ↥(B.map ρ) := by
        rw [card_outerE, hcardBmap]
      have hEq : B.map ρ = outerE :=
        Subgroup.eq_of_le_of_card_ge hle_outerE (le_of_eq hcard_outerE)
      let eE : ↥outerE ≃* alternatingGroup (Fin 8) :=
        (MulEquiv.subgroupCongr hEq).symm.trans
          ((Subgroup.equivMapOfInjective B ρ hρinj).symm.trans eB)
      have heE_symm : ((eE.symm abType22 : ↥outerE) : Equiv.Perm (Fin 3850)) = ρ b := by
        rw [hb]
        simp only [eE, MulEquiv.symm_trans_apply, MulEquiv.symm_symm, MulEquiv.trans_apply,
          MulEquiv.subgroupCongr_apply, Subgroup.coe_equivMapOfInjective_apply]
      set θg : MulAut hsP := MulAut.congr θ g with hθg
      have hg' : θg * α * θg⁻¹ = α * MulAut.conj (θ b) := by
        have h := congrArg (MulAut.congr θ) hg
        simp only [map_mul, map_inv, map_one, tw_congr_conj] at h
        rwa [← hα, ← hθg] at h
      have heAutx : eAut x = α := by
        apply MulEquiv.ext
        intro p
        apply Subtype.ext
        simpa only [heAut x p, hxform p, Subgroup.coe_inv]
      let xg : hsR := eAut.symm θg
      have heAut_xg : eAut xg = θg := eAut.apply_symm_apply θg
      have h1 : xg * x * xg⁻¹ = x * ⟨θ b, hPR (θ b).2⟩ := by
        apply eAut.injective
        simpa only [map_mul, map_inv, heAut_xg, heAutx, ← heAut_conj] using hg'
      have hperm_eq : (xg : Equiv.Perm (Fin 3850)) * (x : Equiv.Perm (Fin 3850)) *
          (xg : Equiv.Perm (Fin 3850))⁻¹ =
          (x : Equiv.Perm (Fin 3850)) * (θ b : Equiv.Perm (Fin 3850)) := by
        simpa using congrArg (fun z : hsR => (z : Equiv.Perm (Fin 3850))) h1
      have hxU : (x : Equiv.Perm (Fin 3850)) = g₁ * outerU * g₁⁻¹ := by
        rw [hxg, hrep]
        rfl
      have hkey : (g₁⁻¹ * (xg : Equiv.Perm (Fin 3850)) * g₁) * outerU *
          (g₁⁻¹ * (xg : Equiv.Perm (Fin 3850)) * g₁)⁻¹ =
          outerU * (g₁⁻¹ * (θ b : Equiv.Perm (Fin 3850)) * g₁) := by
        have hperm := congrArg (fun z : Equiv.Perm (Fin 3850) => g₁⁻¹ * z * g₁) hperm_eq
        rw [hxU] at hperm
        rw [show (g₁⁻¹ * (xg : Equiv.Perm (Fin 3850)) * g₁) * outerU *
              (g₁⁻¹ * (xg : Equiv.Perm (Fin 3850)) * g₁)⁻¹ =
              g₁⁻¹ * ((xg : Equiv.Perm (Fin 3850)) * (g₁ * outerU * g₁⁻¹) *
                (xg : Equiv.Perm (Fin 3850))⁻¹) * g₁ from by group,
          show outerU * (g₁⁻¹ * (θ b : Equiv.Perm (Fin 3850)) * g₁) =
              g₁⁻¹ * ((g₁ * outerU * g₁⁻¹) * (θ b : Equiv.Perm (Fin 3850))) * g₁
                from by group]
        exact hperm
      have hρb : ρ b = g₁⁻¹ * (θ b : Equiv.Perm (Fin 3850)) * g₁ := by
        simp [ρ, MulAut.conj_apply]
      have hfinal : (g₁⁻¹ * (xg : Equiv.Perm (Fin 3850)) * g₁) * outerU *
          (g₁⁻¹ * (xg : Equiv.Perm (Fin 3850)) * g₁)⁻¹ =
          outerU * ((eE.symm abType22 : ↥outerE) : Equiv.Perm (Fin 3850)) := by
        rw [hkey, ← hρb, ← heE_symm]
      exact not_conj_outerU_mul_of_equiv eE _ hfinal
    · exfalso
      exact (by norm_num : ¬ (20160 ∣ 1920)) (h3 ▸ hdvd)

end CFSG.OddStandard.AltStdSec.SwapPartner
