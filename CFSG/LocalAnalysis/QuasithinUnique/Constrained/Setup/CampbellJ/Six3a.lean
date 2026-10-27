module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.Defs
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellTwoElement
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.JBasic
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.Cor56
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.Six1
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.Six2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellLocal

public section

namespace CFSG.QuasithinUnique.Setup.CampbellJ

open CFSG.QuasithinUnique.Setup.Campbell

variable {G : Type*} [Group G] [Finite G] {k : Type*} [Field k] [Finite k] {S : Sylow 2 G}
  {ρ : G →* Matrix.SpecialLinearGroup (Fin 2) k} {ψ : Ecore G →* Multiplicative (Fin 2 → k)}

private theorem cj_le_coreJ_Six3a [Finite G] {Y : Subgroup G}
    (hY : Y ≤ CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G)) (w : G) :
    cj Y w ≤ CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G) := by
  calc cj Y w ≤ cj (CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G)) w := cj_mono hY
    _ = CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G) := cj_eq_self_of_normal

private theorem cj_aimgJ_Zfix_eq_of_mem_Hone_Six3a (h : IsSeed S ρ (Ecore G) ψ)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))
    (hV : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G) ≤ CFSG.pCore 2 G)
    (hF : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) ≠ Fcore G) {u : G}
    (hu : u ∈ Hone S) :
    cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S)) u =
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S) := by
  apply cj_eq_of_forall_mem
  intro z hz
  have hZ := aimgJ_Zfix_le_center_Hone h α hV hF hz
  have hcomm : u * z = z * u := Subgroup.mem_centralizer_iff.mp hZ.2 u hu
  have hfix : u * z * u⁻¹ = z := by rw [hcomm]; group
  rw [hfix]; exact hz

private theorem hb1_Six3a (h : IsSeed S ρ (Ecore G) ψ)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))
    (hV : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G) ≤ CFSG.pCore 2 G)
    {u : G}
    (hne1 : ⁅aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G),
      cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) u⁆ ≠ ⊥) :
    ⁅Fcore G, aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
      (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) u)⁆ ≠ ⊥ := by
  intro hb
  apply hne1
  let T := CFSG.Quasithin.thompsonJ (S : Subgroup G)
  let R := CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G)
  set Fa := aimg T α (Fcore G) with hFa
  have hFaT : Fa ≤ T := aimg_le
  have hFaR : Fa ≤ R := aimgJ_Fcore_le_thompsonJ_core h α hV
  have hRaT : R ≤ T := h.thompsonJ_core_le_thompsonJ_sylow
  have hcjFaT : cj Fa u ≤ T := (cj_le_coreJ_Six3a hFaR u).trans hRaT
  have hsa : aimg T α.symm Fa = Fcore G := by
    rw [hFa]; exact aimg_symm_aimg (Fcore_le_JS h)
  have h1 := aimg_commutator (S := T) (α := α.symm) hFaT hcjFaT
  rw [hsa, hb] at h1
  exact (aimg_eq_bot_iff α.symm (commutator_le_of_le hFaT hcjFaT)).mp h1

private theorem aimg_symm_cj_Fa_Six3a (h : IsSeed S ρ (Ecore G) ψ)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))
    (hV : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G) ≤ CFSG.pCore 2 G)
    {u : G} :
    aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
        (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) u) =
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
          (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G)) u) ⊔
        (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
            (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) u) ⊓
          Subgroup.centralizer (Fcore G : Set G)) := by
  let T := CFSG.Quasithin.thompsonJ (S : Subgroup G)
  let R := CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G)
  set Fa := aimg T α (Fcore G) with hFa
  set Va := aimg T α (Vmod G) with hVa
  have hFaT : Fa ≤ T := aimg_le
  have hFaR : Fa ≤ R := aimgJ_Fcore_le_thompsonJ_core h α hV
  have hFaAdmQ : Adm (CFSG.pCore 2 G) Fa := adm_core_aimgJ_Fcore h α hV
  have hRaT : R ≤ T := h.thompsonJ_core_le_thompsonJ_sylow
  have hcjFaT : cj Fa u ≤ T := (cj_le_coreJ_Six3a hFaR u).trans hRaT
  have hVaR : Va ≤ R := (aimg_mono (Vmod_le_Ecore.trans h.Ecore_le_Fcore)).trans hFaR
  have hcjVaT : cj Va u ≤ T := (cj_le_coreJ_Six3a hVaR u).trans hRaT
  have hsa : aimg T α.symm Fa = Fcore G := by
    rw [hFa]; exact aimg_symm_aimg (Fcore_le_JS h)
  have hrep : cj Fa u = cj Va u ⊔ (cj Fa u ⊓ Subgroup.centralizer (Fa : Set G)) := by
    have h1 := tr_Fcore_repJ h α u (Y := Fa)
      ((adm_cj_thompsonJ_iff u).mpr (h.adm_cj_of_adm_core hFaAdmQ u))
    simpa only [tr, hFa, hVa] using h1
  have hint : cj Fa u ⊓ Subgroup.centralizer (Fa : Set G) ≤ T := inf_le_left.trans hcjFaT
  conv_lhs => rw [hrep]
  rw [aimg_sup hcjVaT hint, aimg_centralizer hFaT, hsa]

private theorem hb2_Six3a (h : IsSeed S ρ (Ecore G) ψ)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))
    (hV : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G) ≤ CFSG.pCore 2 G)
    {u : G}
    (hb1 : ⁅Fcore G, aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
      (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) u)⁆ ≠ ⊥) :
    ⁅Fcore G, aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
      (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G)) u)⁆ ≠ ⊥ := by
  let T := CFSG.Quasithin.thompsonJ (S : Subgroup G)
  set Fa := aimg T α (Fcore G) with hFa
  set Va := aimg T α (Vmod G) with hVa
  have hY := aimg_symm_cj_Fa_Six3a h α hV (u := u)
  have hYel : CFSG.Open.IsElemAbelian 2 (aimg T α.symm (cj Fa u)) :=
    isElemAbelian_aimg α.symm (isElemAbelian_cj (isElemAbelian_aimg α isElemAbelian_Fcore) u)
  intro hb
  apply hb1
  rw [Subgroup.commutator_comm]
  have hle : ⁅aimg T α.symm (cj Fa u), Fcore G⁆ ≤
      ⁅aimg T α.symm (cj Va u) ⊔
        (aimg T α.symm (cj Fa u) ⊓
          Subgroup.centralizer ((Fcore G : Subgroup G) : Set G)), Fcore G⁆ :=
    Subgroup.commutator_mono hY.le le_rfl
  have hle2 : ⁅aimg T α.symm (cj Va u) ⊔
        (aimg T α.symm (cj Fa u) ⊓
          Subgroup.centralizer ((Fcore G : Subgroup G) : Set G)), Fcore G⁆ ≤
      ⁅aimg T α.symm (cj Va u), Fcore G⁆ := by
    refine commutator_sup_of_commute (fun x hx c hc => ?_) (fun c hc w hw =>
      (Subgroup.mem_centralizer_iff.mp hc.2 w hw).symm)
    have hxY : x ∈ aimg T α.symm (cj Fa u) := by
      rw [hY]; exact Subgroup.mem_sup_left hx
    exact (isElemAbelian_iff.mp hYel).1 x hxY c hc.1
  rw [Subgroup.commutator_comm] at hb
  have hle3 := hle.trans hle2
  rw [hb] at hle3
  exact le_bot_iff.mp hle3

private theorem not_le_core_aimg_symm_cj_Va_Six3a (h : IsSeed S ρ (Ecore G) ψ)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))
    (hV : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G) ≤ CFSG.pCore 2 G)
    {u : G}
    (hb2 : ⁅Fcore G, aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
      (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G)) u)⁆ ≠ ⊥) :
    ¬ aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
      (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G)) u) ≤
        CFSG.pCore 2 G := by
  let T := CFSG.Quasithin.thompsonJ (S : Subgroup G)
  let R := CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G)
  set Fa := aimg T α (Fcore G) with hFa
  set Va := aimg T α (Vmod G) with hVa
  have hFaAdmQ : Adm (CFSG.pCore 2 G) Fa := adm_core_aimgJ_Fcore h α hV
  have hVaFa : Va ≤ Fa := aimg_mono (Vmod_le_Ecore.trans h.Ecore_le_Fcore)
  have hUT : aimg T α.symm (cj Va u) ≤ T := aimg_le
  have hUAdmT : Adm T (aimg T α.symm (cj Va u)) :=
    adm_aimg α.symm ((adm_thompsonJ_iff (Y := cj Va u)).mpr
      (h.adm_sylow_of_adm_core (adm_core_cj (hFaAdmQ.mono hVaFa) u)))
  have hUAdmS : Adm (S : Subgroup G) (aimg T α.symm (cj Va u)) :=
    (adm_thompsonJ_iff (Y := aimg T α.symm (cj Va u))).mp hUAdmT
  intro hUQ
  obtain ⟨A', hA', hUA'⟩ := h.adm_core_of_adm hUAdmS hUQ
  have hUR : aimg T α.symm (cj Va u) ≤ R := hUA'.trans (maxElem_le_thompsonJ hA')
  apply hb2
  exact commutator_eq_bot_of_commute fun f hf w hw =>
    (Fcore_commute_thompsonJ_core hf (hUR hw)).symm

private theorem exists_not_commute_pair_Six3a (h : IsSeed S ρ (Ecore G) ψ) {U : Subgroup G}
    (hUT : U ≤ CFSG.Quasithin.thompsonJ (S : Subgroup G))
    (hUQ : ¬ U ≤ CFSG.pCore 2 G) :
    ∃ v ∈ Vmod G, ∃ w ∈ U, v * w ≠ w * v := by
  have hCSV := h.sylow_inf_centralizer_Vmod
  by_contra hall
  push Not at hall
  apply hUQ
  intro w hw
  rw [← hCSV]
  exact ⟨thompsonJ_le_self' (S : Subgroup G) (hUT hw),
    Subgroup.mem_centralizer_iff.mpr fun v hv => hall v hv w hw⟩

private theorem mem_cj_T_and_not_tr_core_Six3a (h : IsSeed S ρ (Ecore G) ψ)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))
    (hV : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G) ≤ CFSG.pCore 2 G)
    {u v w : G} (hvV : v ∈ Vmod G)
    (hvT : v ∈ CFSG.Quasithin.thompsonJ (S : Subgroup G))
    (hwU : w ∈ aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
      (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G)) u))
    (hvw : v * w ≠ w * v) :
    ((α ⟨v, hvT⟩ : ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) : G) ∈
        cj (CFSG.Quasithin.thompsonJ (S : Subgroup G)) u ∧
      ((α ⟨v, hvT⟩ : ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) : G) ∉
        tr (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α u (CFSG.pCore 2 G) := by
  let T := CFSG.Quasithin.thompsonJ (S : Subgroup G)
  let R := CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G)
  set Fa := aimg T α (Fcore G) with hFa
  set Va := aimg T α (Vmod G) with hVa
  obtain ⟨y₁, hy₁, hwy₁⟩ := mem_aimg.mp hwU
  have haVa : ((α ⟨v, hvT⟩ : T) : G) ∈ Va := mem_aimg_of_mem (y := ⟨v, hvT⟩) hvV
  have hnc : ((α ⟨v, hvT⟩ : T) : G) * (y₁ : G) ≠
      (y₁ : G) * ((α ⟨v, hvT⟩ : T) : G) := by
    intro hc
    apply hvw
    have h1 : α ⟨v, hvT⟩ * y₁ = y₁ * α ⟨v, hvT⟩ := Subtype.ext hc
    have h2 : (⟨v, hvT⟩ : T) * α.symm y₁ = α.symm y₁ * ⟨v, hvT⟩ := by
      apply α.injective
      rw [map_mul, map_mul, α.apply_symm_apply]; exact h1
    have h3 := congrArg Subtype.val h2
    simp only [Subgroup.coe_mul] at h3
    rw [hwy₁] at h3
    exact h3
  have hVaFa : Va ≤ Fa := aimg_mono (Vmod_le_Ecore.trans h.Ecore_le_Fcore)
  have hFaR : Fa ≤ R := aimgJ_Fcore_le_thompsonJ_core h α hV
  have hVaR : Va ≤ R := hVaFa.trans hFaR
  have haR : ((α ⟨v, hvT⟩ : T) : G) ∈ R := hVaR haVa
  have hRaT : R ≤ T := h.thompsonJ_core_le_thompsonJ_sylow
  have haT_u : ((α ⟨v, hvT⟩ : T) : G) ∈ cj T u := by
    have h1 := cj_mono (g := u) hRaT
    rw [cj_eq_self_of_normal (Y := R)] at h1
    exact h1 haR
  exact ⟨haT_u, fun haQ => hnc (tr_core_commute_tr_VmodJ α u haQ hy₁)⟩

private theorem centralizer_inf_aimg_symm_cj_Va_le_Zfix_Six3a (h : IsSeed S ρ (Ecore G) ψ)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))
    (hV : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G) ≤ CFSG.pCore 2 G)
    (hF : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) ≠ Fcore G)
    {u v w : G} (huH : u ∈ Hone S) (hvV : v ∈ Vmod G)
    (hvT : v ∈ CFSG.Quasithin.thompsonJ (S : Subgroup G))
    (hwU : w ∈ aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
      (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G)) u))
    (hvw : v * w ≠ w * v) :
    ∀ x' ∈ aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
        (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G)) u),
      (∀ v' ∈ Vmod G, v' * x' = x' * v') → x' ∈ Zfix S := by
  obtain ⟨haT_u, ha_ntQ⟩ :=
    mem_cj_T_and_not_tr_core_Six3a h α hV hvV hvT hwU hvw
  let T := CFSG.Quasithin.thompsonJ (S : Subgroup G)
  set Va := aimg T α (Vmod G) with hVa
  set Za := aimg T α (Zfix S) with hZa
  have hZa_cj : ∀ u' ∈ Hone S, cj Za u' = Za := fun u' hu' =>
    cj_aimgJ_Zfix_eq_of_mem_Hone_Six3a h α hV hF hu'
  have hZaVa : Za ≤ Va := aimg_mono (inf_le_left : Zfix S ≤ Vmod G)
  intro x' hx' hcomm
  obtain ⟨y₂, hy₂, hy₂e⟩ := mem_aimg.mp hx'
  have hcomm2 : ((α ⟨v, hvT⟩ : T) : G) * (y₂ : G) =
      (y₂ : G) * ((α ⟨v, hvT⟩ : T) : G) := by
    have h1 : (⟨v, hvT⟩ : T) * α.symm y₂ = α.symm y₂ * ⟨v, hvT⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [hy₂e]; exact hcomm v hvV
    have h2 := congrArg α h1
    rw [map_mul, map_mul, α.apply_symm_apply] at h2
    exact congrArg Subtype.val h2
  have hZ1 := tr_sylow_not_core_comm_VmodJ h α u haT_u ha_ntQ hy₂ hcomm2
  have hZ2 : (y₂ : G) ∈ Za := by
    have hZeq : cj Za u = Za := hZa_cj u huH
    rw [← hZeq]; exact hZ1
  have h3 := (mem_aimg_symm_iff (S := T) (α := α) y₂.2).mp hZ2
  simpa [hy₂e] using h3

private theorem inf_aimg_symm_cj_Va_eq_Zfix_Six3a (h : IsSeed S ρ (Ecore G) ψ)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))
    (hV : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G) ≤ CFSG.pCore 2 G)
    (hF : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) ≠ Fcore G)
    {u v w : G} (huH : u ∈ Hone S) (hvV : v ∈ Vmod G)
    (hvT : v ∈ CFSG.Quasithin.thompsonJ (S : Subgroup G))
    (hwU : w ∈ aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
      (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G)) u))
    (hvw : v * w ≠ w * v) :
    aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
        (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G)) u) ⊓
      CFSG.pCore 2 G = Zfix S := by
  have hUC :=
    centralizer_inf_aimg_symm_cj_Va_le_Zfix_Six3a h α hV hF huH hvV hvT hwU hvw
  let T := CFSG.Quasithin.thompsonJ (S : Subgroup G)
  set Va := aimg T α (Vmod G) with hVa
  set Za := aimg T α (Zfix S) with hZa
  have hZaVa : Za ≤ Va := aimg_mono (inf_le_left : Zfix S ≤ Vmod G)
  have hZa_cj : ∀ u' ∈ Hone S, cj Za u' = Za := fun u' hu' =>
    cj_aimgJ_Zfix_eq_of_mem_Hone_Six3a h α hV hF hu'
  apply le_antisymm
  · rintro x' ⟨hxU, hxQ⟩
    exact hUC x' hxU fun v' hv' => (Ecore_commute_core hxQ (Vmod_le_Ecore hv')).symm
  · intro z hz
    refine ⟨?_, Ecore_le_core (Vmod_le_Ecore ((inf_le_left : Zfix S ≤ Vmod G) hz))⟩
    have hzT : z ∈ T := Zfix_le_JS h hz
    have h1 : ((α ⟨z, hzT⟩ : T) : G) ∈ Za := mem_aimg_of_mem hz
    have h2 : ((α ⟨z, hzT⟩ : T) : G) ∈ cj Va u := by
      have hZeq : cj Za u = Za := hZa_cj u huH
      have h3 : ((α ⟨z, hzT⟩ : T) : G) ∈ cj Za u := by rw [hZeq]; exact h1
      exact cj_mono hZaVa h3
    exact mem_aimg.mpr ⟨α ⟨z, hzT⟩, h2, by simp⟩

private theorem exists_x_Six3a (h : IsSeed S ρ (Ecore G) ψ)
    {Λ : Subgroup (MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))} (hΛ : LamHyp S Λ)
    {α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))} (hα : α ∈ Λ)
    (hV : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G) ≤ CFSG.pCore 2 G)
    {g t : G} (ht : t ∈ (S : Subgroup G) ⊓ Hone S)
    (hUQeq : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
        (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G))
          (g * t * g⁻¹)) ⊓ CFSG.pCore 2 G = Zfix S) :
    ∃ x ∈ aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
        (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G)) (g * t * g⁻¹)),
      x * x = 1 ∧
        cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) (g * t) =
          cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) (g * x) := by
  let T := CFSG.Quasithin.thompsonJ (S : Subgroup G)
  let R := CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G)
  set Fa := aimg T α (Fcore G) with hFa
  set Va := aimg T α (Vmod G) with hVa
  set u : G := g * t * g⁻¹ with hu
  have hRaT : R ≤ T := h.thompsonJ_core_le_thompsonJ_sylow
  have hFaR : Fa ≤ R := aimgJ_Fcore_le_thompsonJ_core h α hV
  have hVaFa : Va ≤ Fa := aimg_mono (Vmod_le_Ecore.trans h.Ecore_le_Fcore)
  have hVaR : Va ≤ R := hVaFa.trans hFaR
  have hcjVaT : cj Va u ≤ T := (cj_le_coreJ_Six3a hVaR u).trans hRaT
  have hcardU : Nat.card (aimg T α.symm (cj Va u)) = Nat.card (Vmod G) := by
    rw [card_aimg hcjVaT, card_cj, card_aimg (Vmod_le_JS h)]
  have hUT : aimg T α.symm (cj Va u) ≤ T := aimg_le
  have hUS : aimg T α.symm (cj Va u) ≤ (S : Subgroup G) :=
    hUT.trans (thompsonJ_le_self' (S : Subgroup G))
  have hSUQ := h.sylow_eq_sup_of_card hUS hcardU (by rw [hUQeq])
  have htS : t ∈ (S : Subgroup G) := ht.1
  have ht' : t ∈ CFSG.pCore 2 G ⊔ aimg T α.symm (cj Va u) := by
    rw [sup_comm, ← hSUQ]; exact htS
  obtain ⟨q₀, hq₀, x, hxU, hqx⟩ := Subgroup.mem_sup_of_normal_left.mp ht'
  have hxH : x ∈ Hone S := Subgroup.le_normalClosure (hUT hxU)
  have hq₀H : q₀ ∈ Hone S := by
    have hqx' : q₀ = t * x⁻¹ := by rw [← hqx]; group
    rw [hqx']; exact (Hone S).mul_mem ht.2 ((Hone S).inv_mem hxH)
  have ht_comm : cj Fa (g * t) = cj Fa (g * x) := by
    have e1 : g * t = (g * q₀ * g⁻¹) * (g * x) := by rw [← hqx]; group
    rw [e1, ← cj_cj]
    have hthis : cj Fa (g * q₀ * g⁻¹) = Fa :=
      aimgJ_Fcore_normal_of_lamHyp h hΛ hα
        ⟨core_le_sylow S ((CFSG.pCore_normal (p := 2) (G := G)).conj_mem q₀ hq₀ g),
          (inferInstance : (Hone S).Normal).conj_mem q₀ hq₀H g⟩
    rw [hthis]
  have hUel : CFSG.Open.IsElemAbelian 2 (aimg T α.symm (cj Va u)) :=
    isElemAbelian_aimg α.symm (isElemAbelian_cj (isElemAbelian_aimg α isElemAbelian_Vmod) u)
  have hx2 : x * x = 1 := by rw [← pow_two]; exact (isElemAbelian_iff.mp hUel).2 x hxU
  exact ⟨x, hxU, hx2, ht_comm⟩

private theorem exists_y_not_Za_Six3a (h : IsSeed S ρ (Ecore G) ψ)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) {g : G} (hg : g ∈ Hone S) :
    ∃ y ∈ cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G)) g,
      y ∉ aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S) ∧
        y ^ 2 = 1 ∧ y ∈ WJ S α := by
  let T := CFSG.Quasithin.thompsonJ (S : Subgroup G)
  set Va := aimg T α (Vmod G) with hVa
  set Za := aimg T α (Zfix S) with hZa
  have hex_y : ∃ y ∈ cj Va g, y ∉ Za := by
    by_contra hall
    push Not at hall
    have h1 := Subgroup.card_le_of_le (show cj Va g ≤ Za from hall)
    rw [card_cj, card_aimg (Vmod_le_JS h), ← h.card_k_mul_card_Zfix,
      card_aimg (Zfix_le_JS h)] at h1
    obtain ⟨n, hn, hk⟩ := h.card_k
    have hpos : 0 < Nat.card (Zfix S) := Nat.card_pos
    have h2 : 2 ≤ Nat.card k := by
      rw [hk]
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h3 := Nat.mul_le_mul_right (Nat.card (Zfix S)) h2
    linarith
  obtain ⟨y, hyVa, hyZa⟩ := hex_y
  have hyFa : y ∈ cj (aimg T α (Fcore G)) g :=
    cj_mono (aimg_mono (Vmod_le_Ecore.trans h.Ecore_le_Fcore)) hyVa
  have hyW : y ∈ WJ S α := by
    have h1 : y ∈ ⨆ u' ∈ Hone S, cj (aimg T α (Fcore G)) u' :=
      Subgroup.mem_iSup_of_mem g (Subgroup.mem_iSup_of_mem hg hyFa)
    simpa only [WJ] using h1
  have hy2 : y ^ 2 = 1 :=
    (isElemAbelian_iff.mp (isElemAbelian_cj (isElemAbelian_aimg α isElemAbelian_Vmod) g)).2
      y hyVa
  exact ⟨y, hyVa, hyZa, hy2, hyW⟩

private theorem commute_conj_Va_aux_Six3a (h : IsSeed S ρ (Ecore G) ψ)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))
    (hV : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G) ≤ CFSG.pCore 2 G)
    (hF : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) ≠ Fcore G)
    {g y : G} (hg : g ∈ Hone S)
    (hyVa : y ∈ cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G)) g)
    (hyZa : y ∉ aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S)) :
    ∀ r ∈ CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G), r * y = y * r →
      ∀ w' ∈ cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G)) g,
        r * w' = w' * r := by
  let T := CFSG.Quasithin.thompsonJ (S : Subgroup G)
  let R := CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G)
  set Va := aimg T α (Vmod G) with hVa
  set Za := aimg T α (Zfix S) with hZa
  have hVaFa : Va ≤ aimg T α (Fcore G) := aimg_mono (Vmod_le_Ecore.trans h.Ecore_le_Fcore)
  have hFaR : aimg T α (Fcore G) ≤ R := aimgJ_Fcore_le_thompsonJ_core h α hV
  have hVaR : Va ≤ R := hVaFa.trans hFaR
  have hRaT : R ≤ T := h.thompsonJ_core_le_thompsonJ_sylow
  have hZa_cj : ∀ u' ∈ Hone S, cj Za u' = Za := fun u' hu' =>
    cj_aimgJ_Zfix_eq_of_mem_Hone_Six3a h α hV hF hu'
  intro r hr hry w' hw'
  have hrT : r ∈ cj T g := by
    have h1 := cj_mono (g := g) hRaT
    rw [cj_eq_self_of_normal (Y := R)] at h1
    exact h1 hr
  have hrQ : r ∈ tr T α g (CFSG.pCore 2 G) := by
    by_contra hrQ
    have hZy := tr_sylow_not_core_comm_VmodJ h α g hrT hrQ hyVa hry
    have hZeq : cj Za g = Za := hZa_cj g hg
    apply hyZa
    rw [← hZeq]; exact hZy
  exact tr_core_commute_tr_VmodJ α g hrQ hw'

private theorem commute_conj_Va_Six3a (h : IsSeed S ρ (Ecore G) ψ)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))
    (hV : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G) ≤ CFSG.pCore 2 G)
    (hF : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) ≠ Fcore G)
    {g x y : G} (hg : g ∈ Hone S)
    (hyVa : y ∈ cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G)) g)
    (hyZa : y ∉ aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S))
    (hy2 : y ^ 2 = 1) (hyW : y ∈ WJ S α)
    {u : G}
    (hxU : x ∈ aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
      (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G)) u)) (hx2 : x * x = 1)
    (hdih : y * (x⁻¹ * y * x) = (x⁻¹ * y * x) * y) :
    ∀ w ∈ cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G)) (g * x),
      ∀ w' ∈ cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G)) g,
        w * w' = w' * w := by
  let T := CFSG.Quasithin.thompsonJ (S : Subgroup G)
  let R := CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G)
  set Va := aimg T α (Vmod G) with hVa
  have hCR := commute_conj_Va_aux_Six3a h α hV hF hg hyVa hyZa
  have hFaR : aimg T α (Fcore G) ≤ R := aimgJ_Fcore_le_thompsonJ_core h α hV
  have hVaFa : Va ≤ aimg T α (Fcore G) := aimg_mono (Vmod_le_Ecore.trans h.Ecore_le_Fcore)
  have hVaR : Va ≤ R := hVaFa.trans hFaR
  have hyR : y ∈ R := (WJ_facts h α hV hF).1 hyW
  have hrR : x⁻¹ * y * x ∈ R := by
    have h1 := thompsonJ_conj_mem hyR x⁻¹
    simpa using h1
  have hrW := hCR _ hrR hdih.symm
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hVagx : ∀ w ∈ cj Va (g * x), y * w = w * y := by
    intro w hw
    have hw' : x * w * x⁻¹ ∈ cj Va g := by
      have h1 : cj Va (g * x) = cj (cj Va g) x := by rw [cj_cj]
      rw [h1] at hw; exact mem_cj.mp hw
    have h1 := hrW _ hw'
    have hxxz : ∀ z : G, x * (x * z) = z := fun z => by rw [← mul_assoc, hx2, one_mul]
    rw [hxinv] at h1
    simp only [mul_assoc, hxxz] at h1
    have h2 := mul_left_cancel h1
    have h3 : y * w * x = w * y * x := by simpa only [mul_assoc] using h2
    exact mul_right_cancel h3
  have hVagxR : cj Va (g * x) ≤ R := by
    have h1 := cj_mono (g := g * x) hVaR
    rwa [cj_eq_self_of_normal (Y := R)] at h1
  exact fun w hw w' hw' => hCR w (hVagxR hw) (hVagx w hw).symm w' hw'

private theorem conj_commute_of_commute_Va_Six3a (h : IsSeed S ρ (Ecore G) ψ)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))
    (hV : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G) ≤ CFSG.pCore 2 G)
    {g x : G}
    (hVV : ∀ w ∈ cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G)) (g * x),
      ∀ w' ∈ cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G)) g,
        w * w' = w' * w) :
    ⁅cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g,
      cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) (g * x)⁆ = ⊥ := by
  let T := CFSG.Quasithin.thompsonJ (S : Subgroup G)
  set Fa := aimg T α (Fcore G) with hFa
  set Va := aimg T α (Vmod G) with hVa
  have hFaAdmQ : Adm (CFSG.pCore 2 G) Fa := adm_core_aimgJ_Fcore h α hV
  have hVaFa : Va ≤ Fa := aimg_mono (Vmod_le_Ecore.trans h.Ecore_le_Fcore)
  have hrep2 : cj Fa (g * x) = cj Va (g * x) ⊔
      (cj Fa (g * x) ⊓ Subgroup.centralizer ((cj Va g : Subgroup G) : Set G)) := by
    have h1 := tr_Fcore_repJ h α (g * x) (Y := cj Va g)
      ((adm_cj_thompsonJ_iff (g * x)).mpr
        (h.adm_cj_of_adm_core (adm_core_cj (hFaAdmQ.mono hVaFa) g) (g * x)))
    simpa only [tr, hFa, hVa] using h1
  have hFaVa : cj Fa (g * x) ≤ Subgroup.centralizer ((cj Va g : Subgroup G) : Set G) := by
    rw [hrep2]
    exact sup_le (fun w hw => Subgroup.mem_centralizer_iff.mpr fun w' hw' =>
      (hVV w hw w' hw').symm) inf_le_right
  have hrep3 : cj Fa g = cj Va g ⊔
      (cj Fa g ⊓ Subgroup.centralizer ((cj Fa (g * x) : Subgroup G) : Set G)) := by
    have h1 := tr_Fcore_repJ h α g (Y := cj Fa (g * x))
      ((adm_cj_thompsonJ_iff g).mpr
        (h.adm_cj_of_adm_core (adm_core_cj hFaAdmQ (g * x)) g))
    simpa only [tr, hFa, hVa] using h1
  have hfinal : cj Fa g ≤ Subgroup.centralizer ((cj Fa (g * x) : Subgroup G) : Set G) := by
    rw [hrep3]
    exact sup_le (Subgroup.le_centralizer_iff.mp hFaVa) inf_le_right
  exact commutator_eq_bot_of_commute fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (hfinal ha) b hb).symm

theorem conj_commute_of_mem_sylowJ (h : IsSeed S ρ (Ecore G) ψ)
    {Λ : Subgroup (MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))} (hΛ : LamHyp S Λ)
    {α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))} (hα : α ∈ Λ)
    {g t : G} (hg : g ∈ Hone S) (ht : t ∈ (S : Subgroup G) ⊓ Hone S) :
    ⁅cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g,
      cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) (g * t)⁆ = ⊥ := by
  classical
  let T := CFSG.Quasithin.thompsonJ (S : Subgroup G)
  set Fa := aimg T α (Fcore G) with hFa
  set Va := aimg T α (Vmod G) with hVa
  set u : G := g * t * g⁻¹ with hu
  by_cases hF : Fa = Fcore G
  · rw [hF, cj_eq_self_of_normal (Y := Fcore G), cj_eq_self_of_normal (Y := Fcore G)]
    exact commutator_eq_bot_of_commute fun a ha b hb =>
      (isElemAbelian_iff.mp (isElemAbelian_Fcore (G := G))).1 a ha b hb
  · by_contra hne
    have hV : aimg T α (Vmod G) ≤ CFSG.pCore 2 G := hΛ.vmod α hα
    have huH : u ∈ Hone S := by
      rw [hu]
      exact (inferInstance : (Hone S).Normal).conj_mem t ht.2 g
    have hFg : cj Fa (g * t) = cj (cj Fa u) g := by
      rw [cj_cj]; congr 1; rw [hu]; group
    have hne1 : ⁅Fa, cj Fa u⁆ ≠ ⊥ := by
      intro hb; apply hne; rw [hFg, ← cj_commutator, hb, cj_bot]
    have hb1 := hb1_Six3a h α hV hne1
    have hb2 := hb2_Six3a h α hV hb1
    have hUQ := not_le_core_aimg_symm_cj_Va_Six3a h α hV hb2
    have hUT : aimg T α.symm (cj Va u) ≤ T := aimg_le
    obtain ⟨v, hvV, w, hwU, hvw⟩ := exists_not_commute_pair_Six3a h hUT hUQ
    have hvT : v ∈ T := Vmod_le_JS h hvV
    have hUQeq := inf_aimg_symm_cj_Va_eq_Zfix_Six3a h α hV hF huH hvV hvT hwU hvw
    obtain ⟨x, hxU, hx2, ht_comm⟩ := exists_x_Six3a h hΛ hα hV ht hUQeq
    rw [ht_comm] at hne
    obtain ⟨y, hyVa, hyZa, hy2, hyW⟩ := exists_y_not_Za_Six3a h α hg
    have hdih := dihedral_commuteJ h α hV hF huH (v := x) hxU hyW hy2
    have hVV := commute_conj_Va_Six3a h α hV hF hg hyVa hyZa hy2 hyW hxU hx2 hdih
    exact hne (conj_commute_of_commute_Va_Six3a h α hV hVV)

end CFSG.QuasithinUnique.Setup.CampbellJ

end
