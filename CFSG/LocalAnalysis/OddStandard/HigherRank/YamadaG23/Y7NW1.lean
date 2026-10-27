module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NSg
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7RWe

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {t g : G} {P U S F : Subgroup G}

theorem y7n_FU (h : Wr7 t P U) (hS : centEl P t = S) (hF : SgFacts S F g) (htg : t * g = g * t)
    (hgU : ∀ u ∈ U, g * u * g⁻¹ ∈ U) :
    ∃ FU : Subgroup G, FU ≤ U ∧ IsElemAbelian 2 FU ∧ Nat.card FU = 8 ∧
      (∀ w ∈ FU, g * w * g⁻¹ = w) ∧ ∀ u ∈ U, g * u * g⁻¹ = u⁻¹ → u ∈ FU := by
  have hFleS : F ≤ S := by
    rw [← hF.cent_eq]
    exact inf_le_left
  let e : ↥U ≃* ↥S :=
    h.centEquiv.trans (MulEquiv.subgroupCongr (show P ⊓ centralizer ({t} : Set G) = S from hS))
  have he_apply : ∀ x : ↥U, (e x : G) = (x : G) * (t * (x : G) * t⁻¹) := by
    intro x
    rfl
  have hconj_inner : ∀ u : G,
      t * (g * u * g⁻¹) * t⁻¹ = g * (t * u * t⁻¹) * g⁻¹ := by
    intro u
    have hgt : g⁻¹ * t⁻¹ = t⁻¹ * g⁻¹ := by
      have := congrArg Inv.inv htg
      simpa [mul_inv_rev] using this
    calc t * (g * u * g⁻¹) * t⁻¹
        = (t * g) * u * (g⁻¹ * t⁻¹) := by group
      _ = (g * t) * u * (t⁻¹ * g⁻¹) := by rw [htg, hgt]
      _ = g * (t * u * t⁻¹) * g⁻¹ := by group
  let FU' : Subgroup ↥U := (F.subgroupOf S).comap e.toMonoidHom
  have hFU'eq : FU' = (F.subgroupOf S).map e.symm.toMonoidHom :=
    Subgroup.comap_equiv_eq_map_symm' e (F.subgroupOf S)
  have hFU'elem : IsElemAbelian 2 FU' := by
    rw [hFU'eq]
    exact (hF.F_elem.subgroupOf S).map e.symm.toMonoidHom
  have hFU'card : Nat.card FU' = 8 := by
    rw [hFU'eq, Subgroup.card_map_of_injective e.symm.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFleS).toEquiv, hF.F_card]
  refine ⟨FU'.map U.subtype, Subgroup.map_subtype_le FU', hFU'elem.map U.subtype, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective U), hFU'card]
  ·
    intro w hw
    rw [Subgroup.mem_map] at hw
    obtain ⟨u, hu, rfl⟩ := hw
    have huF : (e u : G) ∈ F := Subgroup.mem_comap.mp hu
    have hcomm : g * (e u : G) * g⁻¹ = (e u : G) := by
      have hmem : (e u : G) ∈ centEl S g := by
        rw [hF.cent_eq]
        exact huF
      have hc := Subgroup.mem_centralizer_singleton_iff.mp hmem.2
      calc g * (e u : G) * g⁻¹ = (e u : G) * g * g⁻¹ := by rw [hc]
        _ = (e u : G) := by group
    have hequiv : (e ⟨g * (u : G) * g⁻¹, hgU (u : G) u.2⟩ : G) =
        g * (e u : G) * g⁻¹ := by
      have hL : (e ⟨g * (u : G) * g⁻¹, hgU (u : G) u.2⟩ : G) =
          (g * (u : G) * g⁻¹) * (t * (g * (u : G) * g⁻¹) * t⁻¹) := he_apply _
      have hR : (e u : G) = (u : G) * (t * (u : G) * t⁻¹) := he_apply u
      rw [hL, hR, hconj_inner (u : G)]
      group
    have heq : e ⟨g * (u : G) * g⁻¹, hgU (u : G) u.2⟩ = e u := by
      apply Subtype.ext
      rw [hequiv, hcomm]
    exact congrArg (fun x : ↥U => (x : G)) (e.injective heq)
  ·
    intro u hu hinv
    rw [Subgroup.mem_map]
    refine ⟨⟨u, hu⟩, ?_, rfl⟩
    refine Subgroup.mem_comap.mpr ?_
    have hg2 : g * g = 1 := by simpa [pow_two] using hF.g_sq
    have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_left hg2
    have h3 : (e ⟨u⁻¹, U.inv_mem hu⟩ : G) = (e ⟨u, hu⟩ : G)⁻¹ := by
      rw [show (⟨u⁻¹, U.inv_mem hu⟩ : ↥U) = (⟨u, hu⟩ : ↥U)⁻¹ from rfl, map_inv]
      exact map_inv (Subgroup.subtype S) (e ⟨u, hu⟩)
    have hequiv : (e ⟨g * u * g⁻¹, hgU u hu⟩ : G) = g * (e ⟨u, hu⟩ : G) * g⁻¹ := by
      have hL : (e ⟨g * u * g⁻¹, hgU u hu⟩ : G) =
          (g * u * g⁻¹) * (t * (g * u * g⁻¹) * t⁻¹) := he_apply _
      have hR : (e ⟨u, hu⟩ : G) = u * (t * u * t⁻¹) := he_apply ⟨u, hu⟩
      rw [hL, hR, hconj_inner u]
      group
    have hgy : g * (e ⟨u, hu⟩ : G) * g = (e ⟨u, hu⟩ : G)⁻¹ := by
      have h2 : (⟨g * u * g⁻¹, hgU u hu⟩ : ↥U) = ⟨u⁻¹, U.inv_mem hu⟩ := Subtype.ext hinv
      have hgy' : g * (e ⟨u, hu⟩ : G) * g⁻¹ = (e ⟨u, hu⟩ : G)⁻¹ := by
        rw [← hequiv, h2, h3]
      simpa [hginv] using hgy'
    have hy2 : ((e ⟨u, hu⟩ : G) * g) ^ 2 = 1 := by
      rw [pow_two]
      calc (e ⟨u, hu⟩ : G) * g * ((e ⟨u, hu⟩ : G) * g)
          = (e ⟨u, hu⟩ : G) * (g * (e ⟨u, hu⟩ : G) * g) := by group
        _ = (e ⟨u, hu⟩ : G) * (e ⟨u, hu⟩ : G)⁻¹ := by rw [hgy]
        _ = 1 := mul_inv_cancel _
    have hmem : (e ⟨u, hu⟩ : G) ∈ centEl S g := hF.invol _ (e ⟨u, hu⟩ : ↥S).2 hy2
    rw [hF.cent_eq] at hmem
    exact hmem

end CFSG.OddStandard.HigherRank.YamadaG23
