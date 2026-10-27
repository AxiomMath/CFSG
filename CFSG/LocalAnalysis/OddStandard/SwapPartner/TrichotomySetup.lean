module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.InputLShape
public import CFSG.Foundations.Basic
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
import CFSG.GH74.GLS.IVK.Proofs2.GHInvAltCent

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup

open scoped commutatorElement

variable {X : Type*} [Group X] {t : X} {Sg V : Subgroup X}

namespace SwapShape

private noncomputable def wt_mulHom (h : SwapShape t Sg V) : V × Sg →* X :=
  MonoidHom.noncommCoprod V.subtype Sg.subtype
    (fun v s => (commute_iff_eq _ _).mpr (h.mul_comm_of_mem_v_of_mem_sg v.2 s.2))

private theorem wt_mulHom_range (h : SwapShape t Sg V) : (wt_mulHom h).range = V ⊔ Sg := by
  rw [wt_mulHom, MonoidHom.noncommCoprod_range, Subgroup.range_subtype,
    Subgroup.range_subtype]

private theorem wt_exists_mul_of_mem_centralizer (h : SwapShape t Sg V) {c : X}
    (hc : c ∈ centralizer ({t} : Set X)) : ∃ v ∈ V, ∃ s ∈ Sg, c = v * s := by
  have hc' : c ∈ (wt_mulHom h).range := by
    rw [wt_mulHom_range h, ← h.cent_eq]
    exact hc
  obtain ⟨⟨v, s⟩, hvs⟩ := MonoidHom.mem_range.mp hc'
  refine ⟨v, v.2, s, s.2, ?_⟩
  rw [← hvs]
  simp [wt_mulHom]

private theorem wt_commutator_map_eq (h : SwapShape t Sg V) :
    (_root_.commutator Sg).map (Classical.choice h.iso_sg).toMonoidHom =
      alternatingGroup (Fin 8) := by
  let eS : Sg ≃* Equiv.Perm (Fin 8) := Classical.choice h.iso_sg
  have hmap : (_root_.commutator Sg).map eS.toMonoidHom = alternatingGroup (Fin 8) := by
    rw [_root_.commutator_def, Subgroup.map_commutator]
    simp only [Subgroup.map_top_of_surjective eS.toMonoidHom eS.surjective]
    rw [← _root_.commutator_def]
    exact alternatingGroup.commutator_perm_eq (by simp)
  exact hmap

private noncomputable def wt_commutatorEquivAlt (h : SwapShape t Sg V) :
    (⁅Sg, Sg⁆ : Subgroup X) ≃* alternatingGroup (Fin 8) := by
  let eS : Sg ≃* Equiv.Perm (Fin 8) := Classical.choice h.iso_sg
  have hmap : (_root_.commutator Sg).map eS.toMonoidHom = alternatingGroup (Fin 8) := by
    rw [_root_.commutator_def, Subgroup.map_commutator]
    simp only [Subgroup.map_top_of_surjective eS.toMonoidHom eS.surjective]
    rw [← _root_.commutator_def]
    exact alternatingGroup.commutator_perm_eq (by simp)
  exact ((Subgroup.equivMapOfInjective (_root_.commutator Sg) Sg.subtype
        Sg.subtype_injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator Sg))).symm.trans
    ((Subgroup.equivMapOfInjective (_root_.commutator Sg) eS.toMonoidHom
        eS.injective).trans
      (MulEquiv.subgroupCongr hmap))

private theorem wt_abar_exists_noncomm (h : SwapShape t Sg V) :
    ∃ a b : ↥(⁅Sg, Sg⁆ : Subgroup X), a * b ≠ b * a := by
  classical
  let e := wt_commutatorEquivAlt h
  let σ : Equiv.Perm (Fin 8) := Equiv.swap 0 1 * Equiv.swap 1 2
  let τ : Equiv.Perm (Fin 8) := Equiv.swap 0 1 * Equiv.swap 1 3
  have hσ : σ ∈ alternatingGroup (Fin 8) :=
    Equiv.Perm.mul_mem_alternatingGroup_of_isSwap
      ⟨0, 1, by decide, rfl⟩ ⟨1, 2, by decide, rfl⟩
  have hτ : τ ∈ alternatingGroup (Fin 8) :=
    Equiv.Perm.mul_mem_alternatingGroup_of_isSwap
      ⟨0, 1, by decide, rfl⟩ ⟨1, 3, by decide, rfl⟩
  have hne : σ * τ ≠ τ * σ := by decide
  refine ⟨e.symm ⟨σ, hσ⟩, e.symm ⟨τ, hτ⟩, fun hab => hne ?_⟩
  have h2 : (⟨σ, hσ⟩ : alternatingGroup (Fin 8)) * ⟨τ, hτ⟩ =
      ⟨τ, hτ⟩ * ⟨σ, hσ⟩ := by
    have := congrArg e hab
    simpa using this
  simpa using congrArg Subtype.val h2

theorem sq_eq_one (h : SwapShape t Sg V) : t ^ 2 = 1 := by
  rw [← h.order_eq]
  exact pow_orderOf_eq_one t

theorem mem_v (h : SwapShape t Sg V) : t ∈ V := by
  classical
  obtain ⟨v, hv, s, hs, hvs⟩ := wt_exists_mul_of_mem_centralizer h
    (c := t) (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  let eS : Sg ≃* Equiv.Perm (Fin 8) := Classical.choice h.iso_sg
  have hs_eq : s = v⁻¹ * t := by rw [hvs]; group
  have hs_comm : ∀ a ∈ Sg, s * a = a * s := by
    intro a ha
    have hva : Commute v a := h.mul_comm_of_mem_v_of_mem_sg hv ha
    have hta : t * a = a * t :=
      (Subgroup.mem_centralizer_iff.mp (h.sg_le_centralizer ha)) t (by simp)
    calc s * a = (v⁻¹ * t) * a := by rw [hs_eq]
      _ = v⁻¹ * (t * a) := by group
      _ = v⁻¹ * (a * t) := by rw [hta]
      _ = (v⁻¹ * a) * t := by group
      _ = (a * v⁻¹) * t := by rw [hva.inv_left]
      _ = a * (v⁻¹ * t) := by group
      _ = a * s := by rw [hs_eq]
  have h1 : eS ⟨s, hs⟩ = 1 := by
    refine CFSG.GH74.GLS.IVK.GHInv.eq_one_of_commute_alternating (α := Fin 8) ?_ ?_
    · rw [Nat.card_fin]; norm_num
    · intro g hg
      rw [← wt_commutator_map_eq h] at hg
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hg
      have hcomm : (⟨s, hs⟩ : Sg) * a = a * ⟨s, hs⟩ :=
        Subtype.ext (hs_comm a.1 a.2)
      calc eS ⟨s, hs⟩ * eS a = eS ((⟨s, hs⟩ : Sg) * a) := (map_mul eS _ _).symm
        _ = eS (a * ⟨s, hs⟩) := by rw [hcomm]
        _ = eS a * eS ⟨s, hs⟩ := map_mul eS _ _
  have hsinj : s = 1 := by
    have hsub : (⟨s, hs⟩ : Sg) = 1 := eS.injective (by
      show eS ⟨s, hs⟩ = eS 1
      rw [h1, map_one])
    simpa using congrArg Subtype.val hsub
  rw [hvs, hsinj, mul_one]
  exact hv

theorem nonempty_equiv_abar (h : SwapShape t Sg V) :
    Nonempty (↥(⁅Sg, Sg⁆ : Subgroup X) ≃* alternatingGroup (Fin 8)) :=
  ⟨wt_commutatorEquivAlt h⟩

theorem isQuasisimple_abar (h : SwapShape t Sg V) :
    CFSG.IsQuasisimple ↥(⁅Sg, Sg⁆ : Subgroup X) := by
  haveI : IsSimpleGroup (⁅Sg, Sg⁆ : Subgroup X) := h.isSimpleGroup_commutator_sg
  exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (wt_abar_exists_noncomm h)).1

theorem center_abar_eq_bot (h : SwapShape t Sg V) :
    center ↥(⁅Sg, Sg⁆ : Subgroup X) = ⊥ := by
  haveI : IsSimpleGroup (⁅Sg, Sg⁆ : Subgroup X) := h.isSimpleGroup_commutator_sg
  exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (wt_abar_exists_noncomm h)).2

theorem commutator_centralizer_eq (h : SwapShape t Sg V) :
    ⁅centralizer ({t} : Set X), centralizer ({t} : Set X)⁆ = ⁅Sg, Sg⁆ := by
  exact le_antisymm h.commutator_centralizer_le
    (Subgroup.commutator_mono h.sg_le_centralizer h.sg_le_centralizer)

theorem normal_abar_subgroupOf_centralizer (h : SwapShape t Sg V) :
    ((⁅Sg, Sg⁆ : Subgroup X).subgroupOf (centralizer ({t} : Set X))).Normal := by
  refine (Subgroup.normal_subgroupOf_iff h.commutator_sg_le_centralizer).mpr ?_
  intro a c ha hc
  have h6 := h.commutator_centralizer_eq
  have haC : a ∈ centralizer ({t} : Set X) := h.commutator_sg_le_centralizer ha
  have haCC : a ∈ ⁅centralizer ({t} : Set X), centralizer ({t} : Set X)⁆ := by
    rw [h6]; exact ha
  rw [← h6]
  rw [show c * a * c⁻¹ = ⁅c, a⁆ * a by rw [commutatorElement_def]; group]
  exact Subgroup.mul_mem _ (Subgroup.commutator_mem_commutator hc haC) haCC

theorem isComponent_abar_subgroupOf_centralizer (h : SwapShape t Sg V) :
    CFSG.IsComponent ((⁅Sg, Sg⁆ : Subgroup X).subgroupOf (centralizer ({t} : Set X))) := by
  refine ⟨?_, ?_⟩
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe h.commutator_sg_le_centralizer).symm
      h.isQuasisimple_abar
  · exact h.normal_abar_subgroupOf_centralizer.isSubnormal

theorem centralizer_abar_inf_sg (h : SwapShape t Sg V) :
    centralizer ((⁅Sg, Sg⁆ : Subgroup X) : Set X) ⊓ Sg = ⊥ := by
  classical
  apply le_antisymm _ bot_le
  intro x hx
  rw [Subgroup.mem_bot]
  let eS : Sg ≃* Equiv.Perm (Fin 8) := Classical.choice h.iso_sg
  have h1 : eS ⟨x, hx.2⟩ = 1 := by
    refine CFSG.GH74.GLS.IVK.GHInv.eq_one_of_commute_alternating (α := Fin 8) ?_ ?_
    · rw [Nat.card_fin]; norm_num
    · intro g hg
      rw [← wt_commutator_map_eq h] at hg
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hg
      have ha' : a.1 ∈ (⁅Sg, Sg⁆ : Subgroup X) := by
        rw [← Subgroup.map_subtype_commutator Sg]
        exact Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
      have hxa : a.1 * x = x * a.1 := (Subgroup.mem_centralizer_iff.mp hx.1) a.1 ha'
      have hcomm : (⟨x, hx.2⟩ : Sg) * a = a * ⟨x, hx.2⟩ := Subtype.ext hxa.symm
      calc eS ⟨x, hx.2⟩ * eS a = eS ((⟨x, hx.2⟩ : Sg) * a) := (map_mul eS _ _).symm
        _ = eS (a * ⟨x, hx.2⟩) := by rw [hcomm]
        _ = eS a * eS ⟨x, hx.2⟩ := map_mul eS _ _
  have hsub : (⟨x, hx.2⟩ : Sg) = 1 := eS.injective (by
    show eS ⟨x, hx.2⟩ = eS 1
    rw [h1, map_one])
  exact Subtype.ext_iff.mp hsub

theorem centralizer_abar_inf_centralizer (h : SwapShape t Sg V) :
    centralizer ((⁅Sg, Sg⁆ : Subgroup X) : Set X) ⊓ centralizer ({t} : Set X) = V := by
  have hV_le : V ≤ centralizer ((⁅Sg, Sg⁆ : Subgroup X) : Set X) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (h.mul_comm_of_mem_v_of_mem_sg hv (Subgroup.commutator_le_self Sg ha)).symm
  apply le_antisymm
  · intro x hx
    obtain ⟨v, hv, s, hs, hvs⟩ := wt_exists_mul_of_mem_centralizer h (c := x) hx.2
    have hs_eq : s = v⁻¹ * x := by rw [hvs]; group
    have hs_cent : s ∈ centralizer ((⁅Sg, Sg⁆ : Subgroup X) : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have hxa : a * x = x * a := (Subgroup.mem_centralizer_iff.mp hx.1) a ha
      have hva : Commute a v :=
        (h.mul_comm_of_mem_v_of_mem_sg hv (Subgroup.commutator_le_self Sg ha)).symm
      have hva' : a * v⁻¹ = v⁻¹ * a := hva.inv_right
      calc a * s = a * (v⁻¹ * x) := by rw [hs_eq]
        _ = (a * v⁻¹) * x := by group
        _ = (v⁻¹ * a) * x := by rw [hva']
        _ = v⁻¹ * (a * x) := by group
        _ = v⁻¹ * (x * a) := by rw [hxa]
        _ = (v⁻¹ * x) * a := by group
        _ = s * a := by rw [hs_eq]
    have hs_bot : s ∈ (⊥ : Subgroup X) := by
      rw [← h.centralizer_abar_inf_sg]
      exact ⟨hs_cent, hs⟩
    rw [Subgroup.mem_bot] at hs_bot
    rw [hvs, hs_bot, mul_one]
    exact hv
  · exact le_inf hV_le h.v_le_centralizer

theorem exists_mem_sg_not_mem_abar (h : SwapShape t Sg V) :
    ∃ σ ∈ Sg, σ ∉ (⁅Sg, Sg⁆ : Subgroup X) := by
  classical
  let eS : Sg ≃* Equiv.Perm (Fin 8) := Classical.choice h.iso_sg
  let σg : Sg := eS.symm (Equiv.swap (0 : Fin 8) 1)
  refine ⟨σg.1, σg.2, fun hσA => ?_⟩
  have hσc : σg ∈ _root_.commutator Sg := by
    obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.mp
      (show σg.1 ∈ (_root_.commutator Sg).map Sg.subtype from by
        rw [Subgroup.map_subtype_commutator]
        exact hσA)
    have hEq : a = σg := Subtype.ext hae
    rwa [hEq] at ha
  have hmem : eS σg ∈ alternatingGroup (Fin 8) := by
    rw [← wt_commutator_map_eq h]
    exact Subgroup.mem_map.mpr ⟨σg, hσc, rfl⟩
  have hswap : eS σg = Equiv.swap (0 : Fin 8) 1 := by
    simp [σg]
  rw [hswap] at hmem
  have hsign : Equiv.Perm.sign (Equiv.swap (0 : Fin 8) 1) = -1 :=
    Equiv.Perm.sign_swap (by decide)
  rw [Equiv.Perm.mem_alternatingGroup, hsign] at hmem
  exact absurd hmem (by decide)

end SwapShape

end CFSG.OddStandard.AltStdSec.SwapPartner
