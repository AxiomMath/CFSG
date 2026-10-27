module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NTw
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7RWe

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t g : G} {P U S F M : Subgroup G}

theorem y7n_fuFacts (h : NtTwo t g P U S F M) : FUFacts g U := by
  have hFleS : F ≤ S := by
    rw [← h.sg.cent_eq]
    exact inf_le_left
  let e : ↥U ≃* ↥S :=
    h.wr.centEquiv.trans
      (MulEquiv.subgroupCongr (show P ⊓ centralizer ({t} : Set G) = S from h.cent))
  have he_apply : ∀ x : ↥U, ((e x : ↥S) : G) = (x : G) * (t * (x : G) * t⁻¹) := fun _ => rfl
  have hconj_inner : ∀ u : G, t * (g * u * g⁻¹) * t⁻¹ = g * (t * u * t⁻¹) * g⁻¹ := by
    intro u
    have hgt : g⁻¹ * t⁻¹ = t⁻¹ * g⁻¹ := by
      have := congrArg Inv.inv h.tg
      simpa [mul_inv_rev] using this
    calc t * (g * u * g⁻¹) * t⁻¹
        = (t * g) * u * (g⁻¹ * t⁻¹) := by group
      _ = (g * t) * u * (t⁻¹ * g⁻¹) := by rw [h.tg, hgt]
      _ = g * (t * u * t⁻¹) * g⁻¹ := by group
  have hequiv : ∀ u : ↥U, ((e ⟨g * (u : G) * g⁻¹, h.gU (u : G) u.2⟩ : ↥S) : G) =
      g * ((e u : ↥S) : G) * g⁻¹ := by
    intro u
    have hL : ((e ⟨g * (u : G) * g⁻¹, h.gU (u : G) u.2⟩ : ↥S) : G) =
        (g * (u : G) * g⁻¹) * (t * (g * (u : G) * g⁻¹) * t⁻¹) := he_apply _
    have hR : ((e u : ↥S) : G) = (u : G) * (t * (u : G) * t⁻¹) := he_apply u
    rw [hL, hR, hconj_inner (u : G)]
    group
  have hkey : ∀ u : ↥U, (u : G) ∈ centEl U g ↔ ((e u : ↥S) : G) ∈ F := by
    intro u
    constructor
    · intro hu
      have hgu : (u : G) * g = g * (u : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp hu.2
      have hconj : g * (u : G) * g⁻¹ = (u : G) := by rw [← hgu]; group
      have heq : e ⟨g * (u : G) * g⁻¹, h.gU (u : G) u.2⟩ = e u := by
        apply Subtype.ext
        rw [hequiv u, he_apply u]
        rw [show g * ((u : G) * (t * (u : G) * t⁻¹)) * g⁻¹ =
              (g * (u : G) * g⁻¹) * (g * (t * (u : G) * t⁻¹) * g⁻¹) by group,
            hconj, ← hconj_inner (u : G), hconj]
      have hcomm : g * ((e u : ↥S) : G) * g⁻¹ = ((e u : ↥S) : G) := by
        have hh := congrArg (fun z : ↥S => (z : G)) heq
        rwa [hequiv u] at hh
      have hmem : ((e u : ↥S) : G) ∈ centEl S g := by
        refine ⟨(e u).2, ?_⟩
        have h2 : (g * ((e u : ↥S) : G) * g⁻¹) * g = ((e u : ↥S) : G) * g :=
          congrArg (fun z => z * g) hcomm
        have h2' : g * ((e u : ↥S) : G) = ((e u : ↥S) : G) * g := by
          rwa [show (g * ((e u : ↥S) : G) * g⁻¹) * g = g * ((e u : ↥S) : G) by group] at h2
        exact Subgroup.mem_centralizer_singleton_iff.mpr h2'.symm
      rw [h.sg.cent_eq] at hmem
      exact hmem
    · intro hu
      have hmemC : ((e u : ↥S) : G) ∈ centEl S g := by
        rw [h.sg.cent_eq]
        exact hu
      have hcomm : ((e u : ↥S) : G) * g = g * ((e u : ↥S) : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp hmemC.2
      have hconjE : g * ((e u : ↥S) : G) * g⁻¹ = ((e u : ↥S) : G) := by
        rw [← hcomm]; group
      have heq : e ⟨g * (u : G) * g⁻¹, h.gU (u : G) u.2⟩ = e u := by
        apply Subtype.ext
        rw [hequiv u, hconjE]
      have hux : g * (u : G) * g⁻¹ = (u : G) :=
        congrArg (fun z : ↥U => (z : G)) (e.injective heq)
      refine ⟨u.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have h2 : (g * (u : G) * g⁻¹) * g = (u : G) * g := congrArg (fun z => z * g) hux
      have h2' : g * (u : G) = (u : G) * g := by
        rwa [show (g * (u : G) * g⁻¹) * g = g * (u : G) by group] at h2
      exact h2'.symm
  let FU' : Subgroup ↥U := (F.subgroupOf S).comap e.toMonoidHom
  have hFU'eq : FU' = (F.subgroupOf S).map e.symm.toMonoidHom :=
    Subgroup.comap_equiv_eq_map_symm' e (F.subgroupOf S)
  have hFU'elem : IsElemAbelian 2 FU' := by
    rw [hFU'eq]
    exact (h.sg.F_elem.subgroupOf S).map e.symm.toMonoidHom
  have hFU'card : Nat.card FU' = 8 := by
    rw [hFU'eq, Subgroup.card_map_of_injective e.symm.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFleS).toEquiv, h.sg.F_card]
  have hmap : FU'.map U.subtype = centEl U g := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact (hkey u).mpr (Subgroup.mem_subgroupOf.mp (Subgroup.mem_comap.mp hu))
    · intro hx
      refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
      exact Subgroup.mem_comap.mpr (Subgroup.mem_subgroupOf.mpr ((hkey ⟨x, hx.1⟩).mp hx))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← hmap]
    exact hFU'elem.map U.subtype
  · rw [← hmap, Subgroup.card_map_of_injective (Subgroup.subtype_injective U)]
    exact hFU'card
  ·
    intro u hu hinv
    have hg2 : g * g = 1 := by simpa [pow_two] using h.sg.g_sq
    have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_left hg2
    have h3 : ((e ⟨(u : G)⁻¹, U.inv_mem hu⟩ : ↥S) : G) = ((e ⟨u, hu⟩ : ↥S) : G)⁻¹ := by
      rw [show (⟨(u : G)⁻¹, U.inv_mem hu⟩ : ↥U) = (⟨u, hu⟩ : ↥U)⁻¹ from rfl, map_inv]
      exact map_inv (Subgroup.subtype S) (e ⟨u, hu⟩)
    have hgy' : g * ((e ⟨u, hu⟩ : ↥S) : G) * g⁻¹ = ((e ⟨u, hu⟩ : ↥S) : G)⁻¹ := by
      have h1 : (⟨g * (u : G) * g⁻¹, h.gU (u : G) hu⟩ : ↥U) = ⟨(u : G)⁻¹, U.inv_mem hu⟩ :=
        Subtype.ext hinv
      rw [← hequiv ⟨u, hu⟩, h1, h3]
    have hgy : g * ((e ⟨u, hu⟩ : ↥S) : G) * g = ((e ⟨u, hu⟩ : ↥S) : G)⁻¹ := by
      simpa [hginv] using hgy'
    have hy2 : (((e ⟨u, hu⟩ : ↥S) : G) * g) ^ 2 = 1 := by
      rw [pow_two]
      calc ((e ⟨u, hu⟩ : ↥S) : G) * g * (((e ⟨u, hu⟩ : ↥S) : G) * g)
          = ((e ⟨u, hu⟩ : ↥S) : G) * (g * ((e ⟨u, hu⟩ : ↥S) : G) * g) := by group
        _ = ((e ⟨u, hu⟩ : ↥S) : G) * ((e ⟨u, hu⟩ : ↥S) : G)⁻¹ := by rw [hgy]
        _ = 1 := mul_inv_cancel _
    have hmem : ((e ⟨u, hu⟩ : ↥S) : G) ∈ centEl S g := h.sg.invol _ (e ⟨u, hu⟩).2 hy2
    rw [h.sg.cent_eq] at hmem
    exact (hkey ⟨u, hu⟩).mpr hmem
  ·
    intro w hw
    have hFw : ((e ⟨w, hw.1⟩ : ↥S) : G) ∈ F := (hkey ⟨w, hw.1⟩).mp hw
    obtain ⟨s, hs, hsg⟩ := h.more.cls ((e ⟨w, hw.1⟩ : ↥S) : G) hFw
    let u : ↥U := e.symm ⟨s, hs⟩
    have hue : ((e u : ↥S) : G) = s := by
      change ((e (e.symm ⟨s, hs⟩) : ↥S) : G) = s
      rw [e.apply_symm_apply]
    have hA : (u : G) * (g * (u : G) * g⁻¹)⁻¹ ∈ U :=
      U.mul_mem u.2 (U.inv_mem (h.gU (u : G) u.2))
    have hsu : ((e u : ↥S) : G) * g * ((e u : ↥S) : G)⁻¹ = ((e ⟨w, hw.1⟩ : ↥S) : G) * g := by
      rw [hue]
      exact hsg
    let x2 : ↥U := ⟨(g * (u : G) * g⁻¹)⁻¹, U.inv_mem (h.gU (u : G) u.2)⟩
    let x3 : ↥U := ⟨g * (u : G) * g⁻¹, h.gU (u : G) u.2⟩
    have hx32 : x2 = x3⁻¹ := rfl
    have hAu : (⟨(u : G) * (g * (u : G) * g⁻¹)⁻¹, hA⟩ : ↥U) = u * x2 := Subtype.ext rfl
    have heq : e (⟨(u : G) * (g * (u : G) * g⁻¹)⁻¹, hA⟩ : ↥U) = e ⟨w, hw.1⟩ := by
      apply Subtype.ext
      rw [hAu, map_mul, hx32, map_inv]
      change ((e u : ↥S) : G) * (((e x3 : ↥S) : G))⁻¹ = ((e ⟨w, hw.1⟩ : ↥S) : G)
      rw [show ((e x3 : ↥S) : G) = g * ((e u : ↥S) : G) * g⁻¹ from hequiv u]
      calc ((e u : ↥S) : G) * (g * ((e u : ↥S) : G) * g⁻¹)⁻¹
          = ((e u : ↥S) : G) * g * ((e u : ↥S) : G)⁻¹ * g⁻¹ := by group
        _ = (((e u : ↥S) : G) * g * ((e u : ↥S) : G)⁻¹) * g⁻¹ := by group
        _ = (((e ⟨w, hw.1⟩ : ↥S) : G) * g) * g⁻¹ := by rw [hsu]
        _ = ((e ⟨w, hw.1⟩ : ↥S) : G) := by group
    have hAu' : (u : G) * (g * (u : G) * g⁻¹)⁻¹ = w :=
      congrArg (fun z : ↥U => (z : G)) (e.injective heq)
    exact ⟨(u : G), u.2, by rw [← hAu']; group⟩
  ·
    intro u hu w hw
    have hwU : w ∈ U := hw.1
    have hFw : ((e ⟨w, hwU⟩ : ↥S) : G) ∈ F := (hkey ⟨w, hwU⟩).mp hw
    have hmemU : u * w * u⁻¹ ∈ U := U.mul_mem (U.mul_mem hu hwU) (U.inv_mem hu)
    have heq : ((e ⟨u * w * u⁻¹, hmemU⟩ : ↥S) : G) =
        ((e ⟨u, hu⟩ : ↥S) : G) * ((e ⟨w, hwU⟩ : ↥S) : G) * ((e ⟨u, hu⟩ : ↥S) : G)⁻¹ := by
      have h1 : (⟨u * w * u⁻¹, hmemU⟩ : ↥U) = ⟨u, hu⟩ * ⟨w, hwU⟩ * (⟨u, hu⟩)⁻¹ :=
        Subtype.ext rfl
      rw [h1, map_mul, map_mul, map_inv]
      rfl
    have hFmem : ((e ⟨u * w * u⁻¹, hmemU⟩ : ↥S) : G) ∈ F := by
      rw [heq]
      exact h.more.normF ((e ⟨u, hu⟩ : ↥S) : G) (e ⟨u, hu⟩).2 ((e ⟨w, hwU⟩ : ↥S) : G) hFw
    exact (hkey ⟨u * w * u⁻¹, hmemU⟩).mpr hFmem

end CFSG.OddStandard.HigherRank.YamadaG23
