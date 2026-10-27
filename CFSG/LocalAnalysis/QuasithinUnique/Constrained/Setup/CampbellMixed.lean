module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMixedTools
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellTwoElement

public section

namespace CFSG.QuasithinUnique.Setup.Campbell

open Subgroup CFSG CFSG.Quasithin CFSG.Quasithin.BlueprintB2
open scoped LinearAlgebra.Projectivization

section Mixed

variable {G : Type*} [Group G] {k : Type*} [Field k] {S : Sylow 2 G}
  {ρ : G →* Matrix.SpecialLinearGroup (Fin 2) k} {ψ : Ecore G →* Multiplicative (Fin 2 → k)}

namespace IsSeed

variable [Finite G] [Finite k] (h : IsSeed S ρ (Ecore G) ψ)
include h

theorem tr_commutator_central_eq_one (α : (S : Subgroup G) ≃* (S : Subgroup G)) (g : G) {s w : G}
    (hs : s ∈ cj (S : Subgroup G) g) (hw : w ∈ tr (S : Subgroup G) α g (Vmod G))
    (hc : s * w * s⁻¹ * w⁻¹ ∈ tr (S : Subgroup G) α g (Vmod G ⊓ Subgroup.center G)) :
    s * w * s⁻¹ * w⁻¹ = 1 := by
  have hs1 : g * s * g⁻¹ ∈ (S : Subgroup G) := mem_cj.mp hs
  have hw1 : g * w * g⁻¹ ∈ aimg (S : Subgroup G) α (Vmod G) := mem_cj.mp hw
  have hw1S : g * w * g⁻¹ ∈ (S : Subgroup G) := aimg_le hw1
  have hwV : ((α.symm ⟨g * w * g⁻¹, hw1S⟩ : (S : Subgroup G)) : G) ∈ Vmod G :=
    (mem_aimg_symm_iff hw1S).mp hw1
  have hcD : g * (s * w * s⁻¹ * w⁻¹) * g⁻¹ ∈
      aimg (S : Subgroup G) α (Vmod G ⊓ Subgroup.center G) := mem_cj.mp hc
  have hcS : g * (s * w * s⁻¹ * w⁻¹) * g⁻¹ ∈ (S : Subgroup G) := aimg_le hcD
  have hD := (mem_aimg_symm_iff hcS).mp hcD
  have key : α.symm ⟨g * s * g⁻¹, hs1⟩ * α.symm ⟨g * w * g⁻¹, hw1S⟩ *
      (α.symm ⟨g * s * g⁻¹, hs1⟩)⁻¹ * (α.symm ⟨g * w * g⁻¹, hw1S⟩)⁻¹ =
      α.symm ⟨g * (s * w * s⁻¹ * w⁻¹) * g⁻¹, hcS⟩ := by
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show g * s * g⁻¹ * (g * w * g⁻¹) * (g * s * g⁻¹)⁻¹ * (g * w * g⁻¹)⁻¹ =
      g * (s * w * s⁻¹ * w⁻¹) * g⁻¹
    group
  have key' := congrArg Subtype.val key
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at key'
  have h1 := h.commutator_eq_one_of_central (α.symm ⟨g * s * g⁻¹, hs1⟩).2 hwV
    (by rw [key']; exact hD.2)
  rw [key'] at h1
  have h2 : α.symm ⟨g * (s * w * s⁻¹ * w⁻¹) * g⁻¹, hcS⟩ = 1 := Subtype.ext h1
  have h3 : (⟨g * (s * w * s⁻¹ * w⁻¹) * g⁻¹, hcS⟩ : (S : Subgroup G)) = 1 := by
    apply α.symm.injective
    rw [h2, map_one]
  have h4 : g * (s * w * s⁻¹ * w⁻¹) * g⁻¹ = 1 := congrArg Subtype.val h3
  simpa using h4

theorem inf_cj_Zfix_le_D {hh : G} (hM : hh ∉ Mnorm S ρ) :
    Zfix S ⊓ cj (Zfix S) hh ≤ Vmod G ⊓ Subgroup.center G := by
  obtain ⟨ℓ, hℓ⟩ := h.exists_rootGrp_eq
  rintro z ⟨hzZ, hzZh⟩
  have hzV : z ∈ Vmod G := hzZ.1
  have hz'Z : hh * z * hh⁻¹ ∈ Zfix S := mem_cj.mp hzZh
  have hz'V : hh * z * hh⁻¹ ∈ Vmod G := hz'Z.1
  obtain ⟨s, hsS, hsQ⟩ := h.not_sylow_le_core
  have hT1 := (h.natural_module_facts hℓ).1 s hsS hsQ
  set e : Ecore G := ⟨z, Vmod_le_Ecore hzV⟩ with he
  set e' : Ecore G := ⟨hh * z * hh⁻¹, Vmod_le_Ecore hz'V⟩ with he'
  have hψz : Multiplicative.toAdd (ψ e) ∈ ℓ.submodule := by
    refine (hT1 e hzV).mp ?_
    have := IsSeed.Zfix_central hzZ hsS
    show s * z * s⁻¹ = z
    rw [this]; group
  have hψz' : Multiplicative.toAdd (ψ e') ∈ ℓ.submodule := by
    refine (hT1 e' hz'V).mp ?_
    have := IsSeed.Zfix_central hz'Z hsS
    show s * (hh * z * hh⁻¹) * s⁻¹ = hh * z * hh⁻¹
    rw [this]; group
  have h1 := h.ψ_equiv hh e e' rfl
  have h2 : Multiplicative.toAdd (ψ e') = ρ hh • Multiplicative.toAdd (ψ e) := by
    rw [Matrix.SpecialLinearGroup.smul_def]; exact h1
  have hmem : Multiplicative.toAdd (ψ e) ∈ ((ρ hh)⁻¹ • ℓ).submodule := by
    rw [PSL.smul_submodule]
    have := Submodule.smul_mem_pointwise_smul (ρ hh • Multiplicative.toAdd (ψ e)) (ρ hh)⁻¹
      ℓ.submodule (by rw [← h2]; exact hψz')
    simpa using this
  have hne : ℓ ≠ (ρ hh)⁻¹ • ℓ := by
    intro heq
    apply hM
    rw [mem_Mnorm_iff hℓ]
    rw [eq_inv_smul_iff] at heq
    exact heq
  have hz0 := submodule_inf_eq_bot hne hψz hmem
  have hψ1 : ψ e = 1 := by
    apply Multiplicative.toAdd.injective
    rw [hz0]; rfl
  exact ⟨hzV, h.ψ_eq_one_iff.mp hψ1⟩

theorem commutator_cj_Fa_R0_le (α : (S : Subgroup G) ≃* (S : Subgroup G))
    (hV : aimg (S : Subgroup G) α (Vmod G) ≤ CFSG.pCore 2 G)
    (hF : aimg (S : Subgroup G) α (Fcore G) ≠ Fcore G) (g : G) :
    ⁅cj (aimg (S : Subgroup G) α (Fcore G)) g, thompsonJ (CFSG.pCore 2 G)⁆ ≤
      aimg (S : Subgroup G) α (Zfix S) := by
  have hZc := h.aimg_Zfix_le_center α hV hF
  have hRT : thompsonJ (CFSG.pCore 2 G) ≤ thompsonJ (S : Subgroup G) :=
    h.thompsonJ_core_le_thompsonJ_sylow
  have e : ⁅cj (aimg (S : Subgroup G) α (Fcore G)) g, thompsonJ (CFSG.pCore 2 G)⁆ =
      cj ⁅aimg (S : Subgroup G) α (Fcore G), thompsonJ (CFSG.pCore 2 G)⁆ g := by
    rw [cj_commutator, cj_eq_self_of_normal (Y := thompsonJ (CFSG.pCore 2 G))]
  rw [e]
  calc cj ⁅aimg (S : Subgroup G) α (Fcore G), thompsonJ (CFSG.pCore 2 G)⁆ g
      ≤ cj (aimg (S : Subgroup G) α (Zfix S)) g := by
        refine cj_mono ?_
        calc ⁅aimg (S : Subgroup G) α (Fcore G), thompsonJ (CFSG.pCore 2 G)⁆
            ≤ ⁅aimg (S : Subgroup G) α (Fcore G), thompsonJ (S : Subgroup G)⁆ :=
              Subgroup.commutator_mono le_rfl hRT
          _ = ⁅thompsonJ (S : Subgroup G), aimg (S : Subgroup G) α (Fcore G)⁆ :=
              Subgroup.commutator_comm _ _
          _ = aimg (S : Subgroup G) α (Zfix S) := h.commutator_thompsonJ_aimg_Fcore α
    _ = aimg (S : Subgroup G) α (Zfix S) := cj_eq_of_le_center hZc g

theorem U_facts (α : (S : Subgroup G) ≃* (S : Subgroup G))
    (hV : aimg (S : Subgroup G) α (Vmod G) ≤ CFSG.pCore 2 G) {g : G} (hg : g * g = 1) :
    cj (aimg (S : Subgroup G) α (Fcore G)) g ≤ CFSG.pCore 2 G ∧
    Adm (CFSG.pCore 2 G) (cj (aimg (S : Subgroup G) α (Fcore G)) g) ∧
    ⁅aimg (S : Subgroup G) α.symm (cj (aimg (S : Subgroup G) α (Fcore G)) g), Fcore G⁆ = ⊥ ∧
    aimg (S : Subgroup G) α.symm (cj (aimg (S : Subgroup G) α (Fcore G)) g) ≤ CFSG.pCore 2 G ∧
    Adm (CFSG.pCore 2 G)
      (aimg (S : Subgroup G) α.symm (cj (aimg (S : Subgroup G) α (Fcore G)) g)) := by
  have hQS : CFSG.pCore 2 G ≤ (S : Subgroup G) := core_le_sylow S
  have hFaQ : aimg (S : Subgroup G) α (Fcore G) ≤ CFSG.pCore 2 G := h.aimg_Fcore_le_core α hV
  have hFaAdm : Adm (CFSG.pCore 2 G) (aimg (S : Subgroup G) α (Fcore G)) :=
    h.adm_core_aimg_Fcore α hV
  have hPQ := cj_le_core hFaQ g
  have hPAdm := adm_core_cj hFaAdm g
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  have hcomm := h.two_element_conjugate_commutation α hV g g⁻¹ ⟨1, by
    rw [hginv, pow_one, pow_two]; exact hg⟩
  rw [mul_inv_cancel, cj_one] at hcomm
  have hFaS : aimg (S : Subgroup G) α (Fcore G) ≤ (S : Subgroup G) := aimg_le
  have hPS : cj (aimg (S : Subgroup G) α (Fcore G)) g ≤ (S : Subgroup G) := hPQ.trans hQS
  have hUF : ⁅aimg (S : Subgroup G) α.symm (cj (aimg (S : Subgroup G) α (Fcore G)) g),
      Fcore G⁆ = ⊥ := by
    have h1 := aimg_commutator (S := (S : Subgroup G)) (α := α.symm) hPS hFaS
    rw [hcomm, aimg_bot, aimg_symm_aimg Fcore_le_sylow] at h1
    exact h1.symm
  have hUQ : aimg (S : Subgroup G) α.symm (cj (aimg (S : Subgroup G) α (Fcore G)) g) ≤
      CFSG.pCore 2 G := by
    intro x hx
    exact h.sylow_inf_centralizer_Fcore_le ⟨aimg_le hx, Subgroup.mem_centralizer_iff.mpr
      fun f hf => (mul_comm_of_commutator_eq_bot hUF hx hf).symm⟩
  refine ⟨hPQ, hPAdm, hUF, hUQ, ?_⟩
  exact h.adm_core_of_adm (adm_aimg α.symm (h.adm_sylow_of_adm_core hPAdm)) hUQ

theorem W_calculus (α : (S : Subgroup G) ≃* (S : Subgroup G))
    (hV : aimg (S : Subgroup G) α (Vmod G) ≤ CFSG.pCore 2 G)
    (hV' : aimg (S : Subgroup G) α.symm (Vmod G) ≤ CFSG.pCore 2 G)
    (hF : aimg (S : Subgroup G) α (Fcore G) ≠ Fcore G) {g hh : G} (hg : g * g = 1)
    (hhh : hh * hh = 1) (hM : hh ∉ Mnorm S ρ) :
    Adm (CFSG.pCore 2 G)
      (aimg (S : Subgroup G) α (cj (aimg (S : Subgroup G) α.symm
        (cj (aimg (S : Subgroup G) α (Fcore G)) g)) hh)) ∧
    aimg (S : Subgroup G) α (cj (aimg (S : Subgroup G) α.symm
        (cj (aimg (S : Subgroup G) α (Fcore G)) g)) hh) ≤ CFSG.pCore 2 G ∧
    ⁅aimg (S : Subgroup G) α (cj (aimg (S : Subgroup G) α.symm
        (cj (aimg (S : Subgroup G) α (Fcore G)) g)) hh), Fcore G⁆ = ⊥ ∧
    ⁅cj (aimg (S : Subgroup G) α.symm (cj (aimg (S : Subgroup G) α (Fcore G)) g)) hh,
      aimg (S : Subgroup G) α.symm (cj (aimg (S : Subgroup G) α (Fcore G)) g)⁆ = ⊥ := by
  classical
  have hQS : CFSG.pCore 2 G ≤ (S : Subgroup G) := core_le_sylow S
  have hZc := h.aimg_Zfix_le_center α hV hF
  have hFi : aimg (S : Subgroup G) α.symm (Fcore G) ≠ Fcore G := by
    intro e
    apply hF
    calc aimg (S : Subgroup G) α (Fcore G)
        = aimg (S : Subgroup G) α (aimg (S : Subgroup G) α.symm (Fcore G)) := by rw [e]
      _ = Fcore G := aimg_aimg_symm Fcore_le_sylow
  have hZic := h.aimg_Zfix_le_center α.symm hV' hFi
  obtain ⟨hPQ, hPAdm, hUF, hUQ, hUAdm⟩ := h.U_facts α hV hg
  obtain ⟨hFiQ, hFiAdm, -, hP'Q, hP'Adm⟩ := h.U_facts α.symm hV' hhh
  simp only [MulEquiv.symm_symm] at hP'Q hP'Adm
  set Fa := aimg (S : Subgroup G) α (Fcore G) with hFa
  set Va := aimg (S : Subgroup G) α (Vmod G) with hVa
  set Za := aimg (S : Subgroup G) α (Zfix S) with hZa
  set Fi := aimg (S : Subgroup G) α.symm (Fcore G) with hFi'
  set P := cj Fa g with hP
  set U := aimg (S : Subgroup G) α.symm P with hU
  set P' := aimg (S : Subgroup G) α (cj Fi hh) with hP'
  set W := aimg (S : Subgroup G) α (cj U hh) with hW
  have hFaQ : Fa ≤ CFSG.pCore 2 G := h.aimg_Fcore_le_core α hV
  have hVaFa : Va ≤ Fa := aimg_mono (Vmod_le_Ecore.trans h.Ecore_le_Fcore)
  have hZaC : Za ≤ Subgroup.center G := hZc
  have hFaAdm : Adm (CFSG.pCore 2 G) Fa := h.adm_core_aimg_Fcore α hV
  have hPS : P ≤ (S : Subgroup G) := hPQ.trans hQS
  have hUS : U ≤ (S : Subgroup G) := aimg_le
  have hP'S : P' ≤ (S : Subgroup G) := aimg_le
  have hFiHS : cj Fi hh ≤ (S : Subgroup G) := hFiQ.trans hQS
  have hDZ : Vmod G ⊓ Subgroup.center G ≤ Zfix S := fun d hd =>
    ⟨hd.1, Subgroup.mem_centralizer_iff.mpr fun s _ => (Subgroup.mem_center_iff.mp hd.2 s)⟩
  have hDS : Vmod G ⊓ Subgroup.center G ≤ (S : Subgroup G) := hDZ.trans Zfix_le_sylow
  have hDaZa : aimg (S : Subgroup G) α (Vmod G ⊓ Subgroup.center G) ≤ Za := aimg_mono hDZ
  have hDaC : aimg (S : Subgroup G) α (Vmod G ⊓ Subgroup.center G) ≤ Subgroup.center G :=
    hDaZa.trans hZaC
  have hdomP : aimg (S : Subgroup G) α.symm P ≤ CFSG.pCore 2 G := hUQ
  have hP'symm : aimg (S : Subgroup G) α.symm P' = cj Fi hh := aimg_symm_aimg hFiHS
  have hdomP' : aimg (S : Subgroup G) α.symm P' ≤ CFSG.pCore 2 G := by
    rw [hP'symm]; exact hFiQ
  have hP'R : P' ≤ thompsonJ (CFSG.pCore 2 G) := by
    obtain ⟨A, hA, hle⟩ := hP'Adm
    exact hle.trans (maxElem_le_thompsonJ hA)
  have S1 : ⁅P, P'⁆ ≤ Za :=
    (Subgroup.commutator_mono le_rfl hP'R).trans (h.commutator_cj_Fa_R0_le α hV hF g)
  have hdP : delta (S : Subgroup G) α hh P = W := rfl
  have hdP' : delta (S : Subgroup G) α hh P' = Fcore G := by
    unfold delta
    rw [hP'symm, cj_cj, hhh, cj_one, aimg_aimg_symm Fcore_le_sylow]
  have S2 : delta (S : Subgroup G) α hh ⁅P, P'⁆ = ⁅W, Fcore G⁆ := by
    rw [delta_commutator hQS α hh hPS hP'S hdomP hdomP', hdP, hdP']
  have hUhAdm : Adm (CFSG.pCore 2 G) (cj U hh) := adm_core_cj hUAdm hh
  have hWAdmS : Adm (S : Subgroup G) W :=
    adm_aimg α (h.adm_sylow_of_adm_core hUhAdm)
  have hWS : W ≤ (S : Subgroup G) := aimg_le
  have hWT : W ≤ thompsonJ (S : Subgroup G) := by
    obtain ⟨A, hA, hle⟩ := hWAdmS
    exact hle.trans (maxElem_le_thompsonJ hA)
  have hWFZ : ⁅W, Fcore G⁆ ≤ Zfix S := by
    rw [← h.commutator_thompsonJ_Fcore]; exact Subgroup.commutator_mono hWT le_rfl
  have hWFd : ⁅W, Fcore G⁆ ≤ delta (S : Subgroup G) α hh Za := by
    rw [← S2]; exact delta_mono α hh S1
  have hWFS : ⁅W, Fcore G⁆ ≤ (S : Subgroup G) := commutator_le_of_le hWS Fcore_le_sylow
  have hZaS : Za ≤ (S : Subgroup G) := aimg_le
  have hZQ : Zfix S ≤ CFSG.pCore 2 G :=
    (inf_le_left : Zfix S ≤ Vmod G).trans (Vmod_le_Ecore.trans Ecore_le_core)
  have hZhS : cj (Zfix S) hh ≤ (S : Subgroup G) := (cj_le_core hZQ hh).trans hQS
  have hD1 : aimg (S : Subgroup G) α.symm ⁅W, Fcore G⁆ ≤ Vmod G ⊓ Subgroup.center G := by
    refine le_inf ?_ ?_
    ·
      have h1 : aimg (S : Subgroup G) α.symm ⁅W, Fcore G⁆ ≤ cj (Zfix S) hh := by
        have := aimg_mono (S := (S : Subgroup G)) (α := α.symm) hWFd
        have e : aimg (S : Subgroup G) α.symm (delta (S : Subgroup G) α hh Za) = cj (Zfix S) hh := by
          unfold delta
          rw [aimg_symm_aimg Zfix_le_sylow]
          exact aimg_symm_aimg hZhS
        rwa [e] at this
      have h2 : cj (Zfix S) hh ≤ Vmod G := by
        have := cj_mono (g := hh) (inf_le_left : Zfix S ≤ Vmod G)
        rwa [cj_eq_self_of_normal (Y := Vmod G)] at this
      exact h1.trans h2
    ·
      have h1 : aimg (S : Subgroup G) α.symm ⁅W, Fcore G⁆ ≤ aimg (S : Subgroup G) α.symm (Zfix S) :=
        aimg_mono hWFZ
      exact h1.trans hZic
  have hWFDa : ⁅W, Fcore G⁆ ≤ aimg (S : Subgroup G) α (Vmod G ⊓ Subgroup.center G) := by
    have h1 := aimg_mono (S := (S : Subgroup G)) (α := α) hD1
    rwa [aimg_aimg_symm hWFS] at h1
  have hdDa : delta (S : Subgroup G) α hh
      (aimg (S : Subgroup G) α (Vmod G ⊓ Subgroup.center G)) =
      aimg (S : Subgroup G) α (Vmod G ⊓ Subgroup.center G) := by
    unfold delta
    rw [aimg_symm_aimg hDS, cj_eq_of_le_center inf_le_right hh]
  have hPP'S : ⁅P, P'⁆ ≤ (S : Subgroup G) := commutator_le_of_le hPS hP'S
  have hPP'dom : aimg (S : Subgroup G) α.symm ⁅P, P'⁆ ≤ CFSG.pCore 2 G := by
    rw [aimg_commutator hPS hP'S]
    exact commutator_le_of_le hdomP hdomP'
  have hPP' : ⁅P, P'⁆ = delta (S : Subgroup G) α hh ⁅W, Fcore G⁆ := by
    rw [← S2, delta_delta hQS α hh hPP'S hPP'dom hhh]
  have hPP'Da : ⁅P, P'⁆ ≤ aimg (S : Subgroup G) α (Vmod G ⊓ Subgroup.center G) := by
    rw [hPP']
    calc delta (S : Subgroup G) α hh ⁅W, Fcore G⁆
        ≤ delta (S : Subgroup G) α hh
            (aimg (S : Subgroup G) α (Vmod G ⊓ Subgroup.center G)) := delta_mono α hh hWFDa
      _ = _ := hdDa
  have hQcj : CFSG.pCore 2 G ≤ cj (S : Subgroup G) g := by
    have := cj_mono (g := g) hQS
    rwa [cj_eq_self_of_normal (Y := CFSG.pCore 2 G)] at this
  have hcjDa : cj (aimg (S : Subgroup G) α (Vmod G ⊓ Subgroup.center G)) g =
      aimg (S : Subgroup G) α (Vmod G ⊓ Subgroup.center G) := cj_eq_of_le_center hDaC g
  have S3 : ∀ s ∈ P', ∀ w ∈ cj Va g, s * w * s⁻¹ * w⁻¹ = 1 := by
    intro s hs w hw
    have hwP : w ∈ P := cj_mono hVaFa hw
    have hmem : s * w * s⁻¹ * w⁻¹ ∈ (⁅P', P⁆ : Subgroup G) :=
      Subgroup.commutator_mem_commutator hs hwP
    rw [Subgroup.commutator_comm] at hmem
    have hDa' : s * w * s⁻¹ * w⁻¹ ∈
        tr (S : Subgroup G) α g (Vmod G ⊓ Subgroup.center G) := by
      show _ ∈ cj (aimg (S : Subgroup G) α (Vmod G ⊓ Subgroup.center G)) g
      rw [hcjDa]; exact hPP'Da hmem
    exact h.tr_commutator_central_eq_one α g (hQcj (hP'Q hs)) hw hDa'
  have hrepP : P = cj Va g ⊔ (P ⊓ Subgroup.centralizer (P' : Set G)) :=
    h.tr_Fcore_rep α g (Y := P') (h.adm_cj_of_adm_core hP'Adm g)
  have hPC : P ≤ Subgroup.centralizer (P' : Set G) :=
    hrepP.le.trans (sup_le (fun w hw => Subgroup.mem_centralizer_iff.mpr fun s hs =>
      mul_comm_of_comm_eq_one (S3 s hs w hw)) inf_le_right)
  have hPP'bot : ⁅P, P'⁆ = ⊥ :=
    commutator_eq_bot_of_commute fun a ha b hb =>
      (Subgroup.mem_centralizer_iff.mp (hPC ha) b hb).symm
  have S5 : ⁅W, Fcore G⁆ = ⊥ := by rw [← S2, hPP'bot, delta_bot]
  have hWQ : W ≤ CFSG.pCore 2 G := fun x hx =>
    h.sylow_inf_centralizer_Fcore_le ⟨hWS hx, Subgroup.mem_centralizer_iff.mpr fun f hf =>
      (mul_comm_of_commutator_eq_bot S5 hx hf).symm⟩
  have hWAdm : Adm (CFSG.pCore 2 G) W := h.adm_core_of_adm hWAdmS hWQ
  have hUhS : cj U hh ≤ (S : Subgroup G) := (cj_le_core hUQ hh).trans hQS
  have hαL : aimg (S : Subgroup G) α ⁅cj U hh, U⁆ = ⁅W, P⁆ := by
    rw [aimg_commutator hUhS hUS]
    congr 1
    exact aimg_aimg_symm hPS
  have hWPZa : ⁅W, P⁆ ≤ Za := by
    have hWR : W ≤ thompsonJ (CFSG.pCore 2 G) := by
      obtain ⟨A, hA, hle⟩ := hWAdm
      exact hle.trans (maxElem_le_thompsonJ hA)
    calc ⁅W, P⁆ ≤ ⁅thompsonJ (CFSG.pCore 2 G), P⁆ := Subgroup.commutator_mono hWR le_rfl
      _ = ⁅P, thompsonJ (CFSG.pCore 2 G)⁆ := Subgroup.commutator_comm _ _
      _ ≤ Za := h.commutator_cj_Fa_R0_le α hV hF g
  have hLS : ⁅cj U hh, U⁆ ≤ (S : Subgroup G) := commutator_le_of_le hUhS hUS
  have hsZ : aimg (S : Subgroup G) α.symm Za = Zfix S := aimg_symm_aimg Zfix_le_sylow
  have hLZ : ⁅cj U hh, U⁆ ≤ Zfix S := by
    have h1 := aimg_mono (S := (S : Subgroup G)) (α := α.symm) (hαL.le.trans hWPZa)
    rwa [aimg_symm_aimg hLS, hsZ] at h1
  have hcjL : cj ⁅cj U hh, U⁆ hh = ⁅cj U hh, U⁆ := by
    rw [cj_commutator, cj_cj, hhh, cj_one, Subgroup.commutator_comm]
  have hLD : ⁅cj U hh, U⁆ ≤ Vmod G ⊓ Subgroup.center G := by
    have h1 : ⁅cj U hh, U⁆ ≤ cj (Zfix S) hh := by
      have := cj_mono (g := hh) hLZ
      rwa [hcjL] at this
    exact (le_inf hLZ h1).trans (h.inf_cj_Zfix_le_D hM)
  have hWPDa : ⁅W, P⁆ ≤ aimg (S : Subgroup G) α (Vmod G ⊓ Subgroup.center G) :=
    hαL.symm.le.trans (aimg_mono hLD)
  have S7 : ∀ s ∈ W, ∀ w ∈ cj Va g, s * w * s⁻¹ * w⁻¹ = 1 := by
    intro s hs w hw
    have hwP : w ∈ P := cj_mono hVaFa hw
    have hmem : s * w * s⁻¹ * w⁻¹ ∈ (⁅W, P⁆ : Subgroup G) :=
      Subgroup.commutator_mem_commutator hs hwP
    have hDa' : s * w * s⁻¹ * w⁻¹ ∈
        tr (S : Subgroup G) α g (Vmod G ⊓ Subgroup.center G) := by
      show _ ∈ cj (aimg (S : Subgroup G) α (Vmod G ⊓ Subgroup.center G)) g
      rw [hcjDa]; exact hWPDa hmem
    exact h.tr_commutator_central_eq_one α g (hQcj (hWQ hs)) hw hDa'
  have hrepW : P = cj Va g ⊔ (P ⊓ Subgroup.centralizer (W : Set G)) :=
    h.tr_Fcore_rep α g (Y := W) (h.adm_cj_of_adm_core hWAdm g)
  have hPCW : P ≤ Subgroup.centralizer (W : Set G) :=
    hrepW.le.trans (sup_le (fun w hw => Subgroup.mem_centralizer_iff.mpr fun s hs =>
      mul_comm_of_comm_eq_one (S7 s hs w hw)) inf_le_right)
  have hWPbot : ⁅W, P⁆ = ⊥ :=
    commutator_eq_bot_of_commute fun a ha b hb => Subgroup.mem_centralizer_iff.mp (hPCW hb) a ha
  have hLbot : ⁅cj U hh, U⁆ = ⊥ := (aimg_eq_bot_iff α hLS).mp (by rw [hαL, hWPbot])
  exact ⟨hWAdm, hWQ, S5, hLbot⟩

theorem mixed_conjugation_calculus (α : (S : Subgroup G) ≃* (S : Subgroup G))
    (hV : aimg (S : Subgroup G) α (Vmod G) ≤ CFSG.pCore 2 G)
    (hV' : aimg (S : Subgroup G) α.symm (Vmod G) ≤ CFSG.pCore 2 G) {g hh x : G}
    (_hgH : g ∈ Hone S) (hgM : g ∉ Mnorm S ρ) (hg2 : g ^ 2 = 1)
    (_hhH : hh ∈ Hone S) (hhM : hh ∉ Mnorm S ρ) (hh2 : hh ^ 2 = 1)
    (hxT : x ∈ thompsonJ (S : Subgroup G)) (hxQ : x ∉ CFSG.pCore 2 G) (hx2 : x ^ 2 = 1) :
    (Adm (CFSG.pCore 2 G) (cj (aimg (S : Subgroup G) α (Fcore G)) g) ∧
      Adm (CFSG.pCore 2 G)
        (aimg (S : Subgroup G) α.symm (cj (aimg (S : Subgroup G) α (Fcore G)) g)) ∧
      Adm (CFSG.pCore 2 G)
        (cj (aimg (S : Subgroup G) α.symm (cj (aimg (S : Subgroup G) α (Fcore G)) g)) hh) ∧
      Adm (CFSG.pCore 2 G)
        (aimg (S : Subgroup G) α (cj (aimg (S : Subgroup G) α.symm
          (cj (aimg (S : Subgroup G) α (Fcore G)) g)) hh))) ∧
    (cj (aimg (S : Subgroup G) α (Fcore G)) g ≤ (S : Subgroup G) ∧
      cj (aimg (S : Subgroup G) α.symm (cj (aimg (S : Subgroup G) α (Fcore G)) g)) hh ≤
        (S : Subgroup G)) ∧
    ⁅cj (aimg (S : Subgroup G) α.symm (cj (aimg (S : Subgroup G) α (Fcore G)) g)) hh,
      aimg (S : Subgroup G) α.symm (cj (aimg (S : Subgroup G) α (Fcore G)) g)⁆ = ⊥ ∧
    ⁅cj (aimg (S : Subgroup G) α.symm (cj (aimg (S : Subgroup G) α (Fcore G)) g)) (g * x),
      cj (aimg (S : Subgroup G) α.symm (cj (aimg (S : Subgroup G) α (Fcore G)) g)) g⁆ = ⊥ ∧
    ⁅cj (aimg (S : Subgroup G) α.symm (cj (aimg (S : Subgroup G) α (Fcore G)) g)) g,
      cj (aimg (S : Subgroup G) α.symm (Fcore G)) (g * x)⁆ = ⊥ := by
  classical
  have hQS : CFSG.pCore 2 G ≤ (S : Subgroup G) := core_le_sylow S
  have hg : g * g = 1 := by rw [← pow_two]; exact hg2
  have hhh : hh * hh = 1 := by rw [← pow_two]; exact hh2
  have hxx : x * x = 1 := by rw [← pow_two]; exact hx2
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  have hxS : x ∈ (S : Subgroup G) := thompsonJ_le_self' _ hxT
  by_cases hF : aimg (S : Subgroup G) α (Fcore G) = Fcore G
  · have hFi : aimg (S : Subgroup G) α.symm (Fcore G) = Fcore G := by
      calc aimg (S : Subgroup G) α.symm (Fcore G)
          = aimg (S : Subgroup G) α.symm (aimg (S : Subgroup G) α (Fcore G)) := by rw [hF]
        _ = Fcore G := aimg_symm_aimg Fcore_le_sylow
    have hAdm : Adm (CFSG.pCore 2 G) (Fcore G) := by
      have := h.adm_core_aimg_Fcore α hV
      rwa [hF] at this
    simp only [hF, hFi, cj_eq_self_of_normal (Y := Fcore G)]
    refine ⟨⟨hAdm, hAdm, hAdm, hAdm⟩, ⟨Fcore_le_sylow, Fcore_le_sylow⟩, ?_, ?_, ?_⟩ <;>
      exact commutator_eq_bot_of_commute fun a ha b hb =>
        (isElemAbelian_iff.mp (isElemAbelian_Fcore (G := G))).1 a ha b hb
  · obtain ⟨hWAdm, hWQ, hWF, hL⟩ := h.W_calculus α hV hV' hF hg hhh hhM
    obtain ⟨hPQ, hPAdm, hUF, hUQ, hUAdm⟩ := h.U_facts α hV hg
    have hFi : aimg (S : Subgroup G) α.symm (Fcore G) ≤ (S : Subgroup G) := aimg_le
    have hh₀ : (g * x * g) * (g * x * g) = 1 := by
      calc (g * x * g) * (g * x * g) = g * x * (g * g) * x * g := by group
        _ = 1 := by rw [hg, mul_one, mul_assoc g x x, hxx, mul_one, hg]
    have hM₀ : g * x * g ∉ Mnorm S ρ := by
      intro hM
      apply hgM
      refine h.mem_Mnorm_of_conj_mem hxS hxQ ?_
      rw [hginv]; exact hM
    obtain ⟨-, -, hWF₀, hL₀⟩ := h.W_calculus α hV hV' hF hg hh₀ hM₀
    refine ⟨⟨hPAdm, hUAdm, adm_core_cj hUAdm hh, hWAdm⟩,
      ⟨hPQ.trans hQS, (cj_le_core hUQ hh).trans hQS⟩, hL, ?_, ?_⟩
    ·
      have e1 : cj (aimg (S : Subgroup G) α.symm (cj (aimg (S : Subgroup G) α (Fcore G)) g))
          (g * x) = cj (cj (aimg (S : Subgroup G) α.symm
            (cj (aimg (S : Subgroup G) α (Fcore G)) g)) (g * x * g)) g := by
        rw [cj_cj]
        congr 1
        calc g * x = g * x * (g * g) := by rw [hg, mul_one]
          _ = g * x * g * g := by simp only [mul_assoc]
      rw [e1, ← cj_commutator, hL₀, cj_bot]
    ·
      have hFiQ : aimg (S : Subgroup G) α.symm (Fcore G) ≤ CFSG.pCore 2 G :=
        h.aimg_Fcore_le_core α.symm hV'
      have hUS : aimg (S : Subgroup G) α.symm (cj (aimg (S : Subgroup G) α (Fcore G)) g) ≤
          (S : Subgroup G) := aimg_le
      have hU₀S : cj (aimg (S : Subgroup G) α.symm (cj (aimg (S : Subgroup G) α (Fcore G)) g))
          (g * x * g) ≤ (S : Subgroup G) := (cj_le_core hUQ _).trans hQS
      have hcomm₀ : ⁅cj (aimg (S : Subgroup G) α.symm (cj (aimg (S : Subgroup G) α (Fcore G)) g))
          (g * x * g), aimg (S : Subgroup G) α.symm (Fcore G)⁆ = ⊥ := by
        have h1 := aimg_commutator (S := (S : Subgroup G)) (α := α) hU₀S hFi
        rw [aimg_aimg_symm Fcore_le_sylow, hWF₀] at h1
        exact (aimg_eq_bot_iff α (commutator_le_of_le hU₀S hFi)).mp h1
      have e1 : cj (cj (aimg (S : Subgroup G) α.symm
          (cj (aimg (S : Subgroup G) α (Fcore G)) g)) g) (x * g) =
          cj (aimg (S : Subgroup G) α.symm (cj (aimg (S : Subgroup G) α (Fcore G)) g))
            (g * x * g) := by
        rw [cj_cj, ← mul_assoc]
      have e2 : cj (cj (aimg (S : Subgroup G) α.symm (Fcore G)) (g * x)) (x * g) =
          aimg (S : Subgroup G) α.symm (Fcore G) := by
        rw [cj_cj]
        have : g * x * (x * g) = 1 := by
          calc g * x * (x * g) = g * (x * x) * g := by group
            _ = 1 := by rw [hxx, mul_one, hg]
        rw [this, cj_one]
      have e3 : cj ⁅cj (aimg (S : Subgroup G) α.symm
          (cj (aimg (S : Subgroup G) α (Fcore G)) g)) g,
          cj (aimg (S : Subgroup G) α.symm (Fcore G)) (g * x)⁆ (x * g) = ⊥ := by
        rw [cj_commutator, e1, e2, hcomm₀]
      calc ⁅cj (aimg (S : Subgroup G) α.symm (cj (aimg (S : Subgroup G) α (Fcore G)) g)) g,
          cj (aimg (S : Subgroup G) α.symm (Fcore G)) (g * x)⁆
          = cj (cj ⁅cj (aimg (S : Subgroup G) α.symm
              (cj (aimg (S : Subgroup G) α (Fcore G)) g)) g,
              cj (aimg (S : Subgroup G) α.symm (Fcore G)) (g * x)⁆ (x * g)) (x * g)⁻¹ :=
            cj_inv_cj.symm
        _ = ⊥ := by rw [e3, cj_bot]

end IsSeed

end Mixed

end CFSG.QuasithinUnique.Setup.Campbell
