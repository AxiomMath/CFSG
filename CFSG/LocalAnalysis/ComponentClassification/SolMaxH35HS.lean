module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5CovHS
public import Certificates.Certificate23300

public section

namespace CFSG.ComponentClassification.SolMax.H35.HS

open Subgroup CFSG.Blueprint CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.GSThmB CFSG.ComponentClassification.GSThmB.CovHS
open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LocalAnalysis.ComponentInitial

theorem hs_h35_check : hsH35Check = true :=
  Certificates.certificate23300

theorem d_facts :
    hsDPerm 0 * hsDPerm 0 = 1 ∧ hsDPerm 0 ≠ 1 ∧ nfix (hsT2 * hsDPerm 0) = 30 := by
  have h := hs_h35_check
  simp only [hsH35Check, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨hdd, hd1⟩, hf⟩ := h
  have hd : TabRep dTab (hsDPerm 0) := tabRep_hsDGens 0 (by simp [hsDGens])
  have hk := covHS_klein_check
  simp only [kleinCheck, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, hp2⟩, hs2⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hk
  have ht2 : TabRep t2Tab hsT2 := tabRep_natArr hp2 hs2
  refine ⟨?_, ?_, ?_⟩
  · have h1 := hd.comp hd
    rw [hdd] at h1
    exact (TabRep.idTab.perm_eq h1).symm
  · intro h1
    rw [h1] at hd
    have := hd.tab_eq TabRep.idTab
    rw [this] at hd1
    exact absurd hd1 (by simp)
  · rw [nfix_of_tabRep (ht2.comp hd), hf]

theorem false_of_fixed
    {L : Type} [Group L] [Finite L] (hLq : CFSG.Assembly.IsQuasisimple L) {t : L}
    (ht : orderOf t = 2) (hZ : center L = zpowers t) (ρ : L →* hsP)
    (hρ : Function.Surjective ρ) (hker : ρ.ker = zpowers t) (α : MulAut L) (hα : α * α = 1)
    (β : MulAut hsP) (hβ : ∀ x, ρ (α x) = β (ρ x)) {Lt : Subgroup L}
    (hfix : ∀ y ∈ Lt, α y = y) (huniq : ∀ y ∈ Lt, y * y = 1 → y = 1 ∨ y = t)
    (hM : CFSG.Assembly.IsComponentOf (Lt.map ρ) (fixSub β))
    (hMt : Cov.SmallQ (↥(Lt.map ρ) ⧸ center ↥(Lt.map ρ))) : False := by
  set M := Lt.map ρ with hMdef
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hperf : Group.IsPerfect L := (Group.isPerfect_def).2 hLq.1
  have hι : Function.Injective hsP.subtype := Subtype.val_injective
  obtain ⟨eAut, heAut, -⟩ := hs_full_automorphism_model
  obtain ⟨x, hx⟩ := eAut.surjective β
  have hxι : ∀ z : hsP, ((β z : hsP) : Equiv.Perm (Fin 3850)) =
      (x : Equiv.Perm (Fin 3850)) * z * (x : Equiv.Perm (Fin 3850))⁻¹ := fun z => by
    rw [← hx, heAut x z, Subgroup.coe_inv]
  have hfixS : (fixSub β).map hsP.subtype =
      hsP ⊓ centralizer ({(x : Equiv.Perm (Fin 3850))} : Set (Equiv.Perm (Fin 3850))) := by
    ext w
    simp only [mem_map, mem_inf, mem_fixSub, coe_subtype, mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z.2, ?_⟩
      have h1 := hxι z
      rw [hz] at h1
      calc (z : Equiv.Perm (Fin 3850)) * x = (x * z * (x : Equiv.Perm (Fin 3850))⁻¹) * x := by
            rw [← h1]
        _ = x * z := by group
    · rintro ⟨hw, hwc⟩
      refine ⟨⟨w, hw⟩, Subtype.ext ?_, rfl⟩
      rw [hxι]
      calc (x : Equiv.Perm (Fin 3850)) * w * (x : Equiv.Perm (Fin 3850))⁻¹ =
          (w * x) * (x : Equiv.Perm (Fin 3850))⁻¹ := by rw [hwc]
        _ = w := by group
  have hM' : CFSG.Assembly.IsComponentOf (M.map hsP.subtype)
      (hsP ⊓ centralizer ({(x : Equiv.Perm (Fin 3850))} : Set (Equiv.Perm (Fin 3850)))) := by
    rw [← hfixS]
    exact (isComponentOf_map_iff hι).2 hM
  have hMt' : Cov.SmallQ (↥(M.map hsP.subtype) ⧸ center ↥(M.map hsP.subtype)) :=
    smallQ_of_equiv (quotCenterEquiv (M.equivMapOfInjective _ hι)) hMt
  have hββ : β * β = 1 := by
    refine MulEquiv.ext fun z => ?_
    obtain ⟨y, rfl⟩ := hρ z
    rw [MulAut.mul_apply, ← hβ, ← hβ, ← MulAut.mul_apply, hα, MulAut.one_apply,
      MulAut.one_apply]
  have hxx : x * x = 1 := eAut.injective (by rw [map_mul, hx, hββ, map_one])
  by_cases hx1 : x = 1
  · have hβ1 : ∀ z, β z = z := fun z => Subtype.ext (by
      rw [hxι, hx1, Subgroup.coe_one, one_mul, inv_one, mul_one])
    have hfix1 : fixSub β = ⊤ := eq_top_iff.mpr fun z _ => mem_fixSub.mpr (hβ1 z)
    rw [hfix1] at hM
    exact Cov.false_of_top' hLq ρ hρ (hker.trans hZ.symm) hM hMt
      (fun q => by rw [card_hsP]; exact ordA_one_ne_44352000 q) (by rw [card_hsP]; norm_num)
  have hxo : orderOf (x : Equiv.Perm (Fin 3850)) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [sq]; exact hxx) hx1
  obtain ⟨-, -, -, -, hcover, -, -, -⟩ := hs_involution_centralizers
  obtain ⟨r, hr, g, hg, hxg⟩ := hcover (x : Equiv.Perm (Fin 3850)) x.2 hxo
  have hfinj : Function.Injective (MulAut.conj g⁻¹).toMonoidHom := (MulAut.conj g⁻¹).injective
  have hfx : (MulAut.conj g⁻¹).toMonoidHom (x : Equiv.Perm (Fin 3850)) = tp 3850 r.rep := by
    rw [hxg, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hB : CFSG.Assembly.IsComponentOf ((M.map hsP.subtype).map (MulAut.conj g⁻¹).toMonoidHom)
      (hsP ⊓ centralizer ({tp 3850 r.rep} : Set (Equiv.Perm (Fin 3850)))) := by
    have h := (isComponentOf_map_iff hfinj).2 hM'
    rwa [map_conj_inf_centralizer hsP (hsP.inv_mem hg), Set.image_singleton, hfx] at h
  have hBt := smallQ_of_equiv
    (quotCenterEquiv ((M.map hsP.subtype).equivMapOfInjective _ hfinj)) hMt'
  simp only [hsRows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · dsimp only at hB
    exact hsC1_no_component hB
  · dsimp only at hxg hB
    have hxP : (x : Equiv.Perm (Fin 3850)) ∈ hsP := by
      rw [hxg]
      exact hsP.mul_mem (hsP.mul_mem hg t2_mem) (hsP.inv_mem hg)
    have hβc : ∀ z, β z = ⟨x, hxP⟩ * z * (⟨x, hxP⟩ : hsP)⁻¹ := fun z =>
      Subtype.ext (by rw [hxι, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv])
    obtain ⟨X, hX⟩ := hρ ⟨x, hxP⟩
    have hαX : α = MulAut.conj X :=
      Cov.eq_conj_of_comp hperf ρ (by rw [hker, hZ]) α X fun y => by rw [hβ, hβc, hX]
    have hXX : X * X = t := sq_lift hLq ht hZ ρ hρ hker hg (by rw [hX]; exact hxg)
    obtain ⟨hdd, hd1, hdf⟩ := d_facts
    obtain ⟨-, -, hDC2, -, -⟩ := hs_D_facts
    have hdD : hsDPerm 0 ∈ genGroup 3850 hsDGens hsDPerm :=
      subset_closure ⟨0, by simp [hsDGens], rfl⟩
    have hdC := hDC2 hdD
    rw [mem_inf, mem_centralizer_singleton_iff] at hdC
    obtain ⟨hdP, hdt⟩ := hdC
    rw [← hsC2_component hB] at hdD
    obtain ⟨_, ⟨m, ⟨ℓ, hℓ, hℓm⟩, rfl⟩, hmd⟩ := hdD
    have hmd' : (m : Equiv.Perm (Fin 3850)) = g * hsDPerm 0 * g⁻¹ := by
      rw [← hmd, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      change (m : Equiv.Perm (Fin 3850)) = g * (g⁻¹ * (m : Equiv.Perm (Fin 3850)) * g⁻¹⁻¹) * g⁻¹
      group
    have hρℓ : ((ρ ℓ : hsP) : Equiv.Perm (Fin 3850)) = g * hsDPerm 0 * g⁻¹ := by
      rw [hℓm]
      exact hmd'
    have hℓℓ : ℓ * ℓ = t := by
      have hk : ℓ * ℓ ∈ zpowers t := by
        rw [← hker, MonoidHom.mem_ker]
        apply Subtype.ext
        rw [map_mul, Subgroup.coe_mul, hρℓ, Subgroup.coe_one]
        calc g * hsDPerm 0 * g⁻¹ * (g * hsDPerm 0 * g⁻¹) = g * (hsDPerm 0 * hsDPerm 0) * g⁻¹ := by
              group
          _ = 1 := by rw [hdd]; group
      rcases Cov.eq_one_or_eq_of_mem_zpowers ht2 hk with h1 | h1
      · exfalso
        have htk : ρ t = 1 := by
          rw [← MonoidHom.mem_ker, hker]
          exact mem_zpowers t
        apply hd1
        have h2 : ((ρ ℓ : hsP) : Equiv.Perm (Fin 3850)) = 1 := by
          rcases huniq ℓ hℓ h1 with h3 | h3
          · rw [h3, map_one, Subgroup.coe_one]
          · rw [h3, htk, Subgroup.coe_one]
        rw [hρℓ] at h2
        calc hsDPerm 0 = g⁻¹ * (g * hsDPerm 0 * g⁻¹) * g := by group
          _ = 1 := by rw [h2]; group
      · exact h1
    have hXℓ : X * ℓ = ℓ * X := by
      have h1 := hfix ℓ hℓ
      rw [hαX, MulAut.conj_apply] at h1
      calc X * ℓ = X * ℓ * X⁻¹ * X := by group
        _ = ℓ * X := by rw [h1]
    have hsq : (X * ℓ) * (X * ℓ) = 1 := by
      calc (X * ℓ) * (X * ℓ) = X * (ℓ * X) * ℓ := by group
        _ = X * (X * ℓ) * ℓ := by rw [hXℓ]
        _ = (X * X) * (ℓ * ℓ) := by group
        _ = 1 := by rw [hXX, hℓℓ, ht2]
    have htd2 : (hsT2 * hsDPerm 0) * (hsT2 * hsDPerm 0) = 1 := by
      calc (hsT2 * hsDPerm 0) * (hsT2 * hsDPerm 0) = hsT2 * (hsDPerm 0 * hsT2) * hsDPerm 0 := by
            group
        _ = hsT2 * (hsT2 * hsDPerm 0) * hsDPerm 0 := by rw [hdt]
        _ = (hsT2 * hsT2) * (hsDPerm 0 * hsDPerm 0) := by group
        _ = 1 := by rw [t2_mul_self, hdd, one_mul]
    obtain ⟨g', hg', hg'eq⟩ := conj_t2_of_sq (hsP.mul_mem t2_mem hdP) htd2 hdf
    have hW : ((ρ (X * ℓ) : hsP) : Equiv.Perm (Fin 3850)) = (g * g') * hsT2 * (g * g')⁻¹ := by
      rw [map_mul, Subgroup.coe_mul, hX, hρℓ]
      change (x : Equiv.Perm (Fin 3850)) * (g * hsDPerm 0 * g⁻¹) = _
      rw [hxg]
      calc g * hsT2 * g⁻¹ * (g * hsDPerm 0 * g⁻¹) = g * (hsT2 * hsDPerm 0) * g⁻¹ := by group
        _ = g * (g' * hsT2 * g'⁻¹) * g⁻¹ := by rw [hg'eq]
        _ = (g * g') * hsT2 * (g * g')⁻¹ := by group
    have h1 := sq_lift hLq ht hZ ρ hρ hker (hsP.mul_mem hg hg') hW
    rw [hsq] at h1
    rw [← h1, orderOf_one] at ht
    exact absurd ht (by norm_num)
  · dsimp only at hB
    have hC : CFSG.QuasithinUnique.Id2519.HSAut.outerC =
        hsP ⊓ centralizer ({tp 3850 (hsCentTbl 21)} : Set (Equiv.Perm (Fin 3850))) := rfl
    rw [← hC] at hB
    exact outerC_no_small hB hBt
  · dsimp only at hB
    exact c4_no_component hB

end CFSG.ComponentClassification.SolMax.H35.HS
