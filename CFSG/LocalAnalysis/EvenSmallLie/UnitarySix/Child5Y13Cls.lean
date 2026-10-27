module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.Child5Defs
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.Child5Y13Basic
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParN1

public section

namespace CFSG.EvenSmallLie.UnitarySix.Child5

open Subgroup Matrix YamadaPar YamadaD

theorem eq_of_add_eq_zero_two {u v : Fin 8 → ZMod 2} (huv : u + v = 0) : u = v := by
  funext i
  have h1 := congrFun huv i
  simp only [Pi.add_apply, Pi.zero_apply] at h1
  generalize u i = a at h1 ⊢
  generalize v i = b at h1 ⊢
  revert a b
  decide

variable {G : Type} [Group G] {d : YamadaD.Data G}

theorem K₁_le_normalizer_A₁ (h : Hyp d) : d.K₁ ≤ normalizer (d.A₁ : Set G) :=
  fun _ hk => h.CHz_le (mem_inf.mpr ⟨h.K₁_cent_z hk, h.L_le_H (h.K₁_le_L hk)⟩)

theorem card_quot_AV [Finite G] (h : Hyp d) (hV : ∀ v ∈ d.V₁, v * v = 1)
    [(d.V₁.subgroupOf d.AV).Normal] :
    Nat.card (d.AV ⧸ d.V₁.subgroupOf d.AV) = 2 ^ 8 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (d.V₁.subgroupOf d.AV)
  rw [YamadaPar.card_subgroupOf_of_le le_sup_right, h.card_V₁, h.card_AV hV] at h1
  omega

variable {θ : d.K₁ ≃* SU42b} {ιG : (Fin 8 → ZMod 2) → G}

theorem ι_mem_AV (hc : Y13Coords d θ ιG) (u : Fin 8 → ZMod 2) : ιG u ∈ d.AV :=
  mem_sup_left (hc.ι_mem u)

variable [Finite G]

section Cls

variable [(d.V₁.subgroupOf d.AV).Normal]

theorem cls_ι_add (h : Hyp d) (hc : Y13Coords d θ ιG) (u v : Fin 8 → ZMod 2) :
    d.cls (ιG (u + v)) = d.cls (ιG u) * d.cls (ιG v) := by
  rw [← Hyp.cls_mul (ι_mem_AV hc u) (ι_mem_AV hc v), eq_comm, Hyp.cls_eq_iff
    (mul_mem (ι_mem_AV hc u) (ι_mem_AV hc v)) (ι_mem_AV hc (u + v))]
  exact zpowers_z_le_V₁ h (hc.ι_add u v)

theorem cls_ι_sq (h : Hyp d) (hC : HypC d) (hc : Y13Coords d θ ιG) (u : Fin 8 → ZMod 2) :
    d.cls (ιG u) * d.cls (ιG u) = 1 := by
  rw [← Hyp.cls_mul (ι_mem_AV hc u) (ι_mem_AV hc u),
    Hyp.cls_eq_one_iff (mul_mem (ι_mem_AV hc u) (ι_mem_AV hc u))]
  exact zpowers_z_le_V₁ h (hC.A₁_sq _ (hc.ι_mem u))

theorem cls_ι_inj (h : Hyp d) (hC : HypC d) (hc : Y13Coords d θ ιG) {u v : Fin 8 → ZMod 2}
    (huv : d.cls (ιG u) = d.cls (ιG v)) : u = v := by
  have h1 : d.cls (ιG (u + v)) = 1 := by
    rw [cls_ι_add h hc, ← huv, cls_ι_sq h hC hc]
  rw [Hyp.cls_eq_one_iff (ι_mem_AV hc _)] at h1
  exact eq_of_add_eq_zero_two (hc.ι_inj _ (mem_zpowers_of_mem_A₁ h (hc.ι_mem _) h1))

theorem cls_ι_surj (h : Hyp d) (hC : HypC d) (hV : ∀ v ∈ d.V₁, v * v = 1)
    (hc : Y13Coords d θ ιG) (a : G) : ∃ u, d.cls (ιG u) = d.cls a := by
  have hinj : Function.Injective (fun u : Fin 8 → ZMod 2 => d.cls (ιG u)) :=
    fun u v huv => cls_ι_inj h hC hc huv
  have hbij := hinj.bijective_of_nat_card_le (by
    rw [card_quot_AV h hV]
    simp)
  obtain ⟨u, hu⟩ := hbij.2 (d.cls a)
  exact ⟨u, hu⟩

theorem cls_conj_ι (h : Hyp d) (hc : Y13Coords d θ ιG) (k : d.K₁) (u : Fin 8 → ZMod 2) :
    d.cls ((k : G) * ιG u * (k : G)⁻¹) =
      d.cls (ιG (((θ k : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ u)) := by
  have hk := (mem_normalizer_iff.mp (K₁_le_normalizer_A₁ h k.2) (ιG u)).mp (hc.ι_mem u)
  rw [Hyp.cls_eq_iff (mem_sup_left hk) (ι_mem_AV hc _)]
  exact zpowers_z_le_V₁ h (hc.K₁_ι k u)

theorem eq_one_of_cent (h : Hyp d) (hC : HypC d) (hc : Y13Coords d θ ιG) (k : d.K₁)
    (hk : ∀ a ∈ d.A₁, ((k : G) * a * (k : G)⁻¹)⁻¹ * a ∈ d.V₁) : k = 1 := by
  have hfix : ∀ u, (((θ k : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ u) = u := by
    intro u
    apply cls_ι_inj h hC hc
    rw [← cls_conj_ι h hc k u]
    have hku := (mem_normalizer_iff.mp (K₁_le_normalizer_A₁ h k.2) (ιG u)).mp (hc.ι_mem u)
    rw [Hyp.cls_eq_iff (mem_sup_left hku) (ι_mem_AV hc u)]
    exact hk _ (hc.ι_mem u)
  have hM : ((θ k : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) = 1 := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro u
    rw [Matrix.toLin'_apply, hfix u, Matrix.toLin'_one, LinearMap.id_apply]
  have hθ : θ k = 1 := Subtype.ext (Units.ext hM)
  exact (MulEquiv.map_eq_one_iff θ).mp hθ

theorem exists_fix_of_cent (h : Hyp d) (hC : HypC d) (hV : ∀ v ∈ d.V₁, v * v = 1)
    (hc : Y13Coords d θ ιG) {a : G} (ha : a ∈ d.AV)
    (hcent : ∀ m < 4, d.cls (((θ.symm (eSU m) : d.K₁) : G) * a *
      ((θ.symm (eSU m) : d.K₁) : G)⁻¹) = d.cls a) :
    ∃ u, (∀ m < 4, toMat 8 8 (eBits m) *ᵥ u = u) ∧ d.cls (ιG u) = d.cls a := by
  obtain ⟨u, hu⟩ := cls_ι_surj h hC hV hc a
  refine ⟨u, fun m hm => ?_, hu⟩
  have hX : ((θ.symm (eSU m) : d.K₁) : G) ∈ d.XV := h.K₁_le_XV (θ.symm (eSU m)).2
  have h1 := cls_conj_ι h hc (θ.symm (eSU m)) u
  rw [MulEquiv.apply_symm_apply, coe_eSU m hm] at h1
  apply cls_ι_inj h hC hc
  rw [← h1, h.cls_conj_congr hX (ι_mem_AV hc u) ha hu, hcent m hm, hu]

end Cls

end CFSG.EvenSmallLie.UnitarySix.Child5
