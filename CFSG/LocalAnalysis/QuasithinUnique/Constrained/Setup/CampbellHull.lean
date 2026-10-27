module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion

public section

namespace CFSG.QuasithinUnique.Setup.Campbell

open Subgroup CFSG CFSG.Quasithin CFSG.Quasithin.BlueprintB2
open scoped LinearAlgebra.Projectivization

section Hull

variable {G : Type*} [Group G]

theorem aimg_trans {S₀ : Subgroup G} (β γ : S₀ ≃* S₀) (Y : Subgroup G) :
    aimg S₀ (β.trans γ) Y = aimg S₀ γ (aimg S₀ β Y) := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := mem_aimg.mp hx
    exact mem_aimg.mpr ⟨β y, mem_aimg.mpr ⟨y, hy, rfl⟩, rfl⟩
  · intro hx
    obtain ⟨z, hz, rfl⟩ := mem_aimg.mp hx
    obtain ⟨y, hy, hyz⟩ := mem_aimg.mp hz
    have : β y = z := Subtype.ext hyz
    exact mem_aimg.mpr ⟨y, hy, by simp [this]⟩

theorem aimg_refl_of_le {S₀ Y : Subgroup G} (hY : Y ≤ S₀) :
    aimg S₀ (MulEquiv.refl S₀) Y = Y := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := mem_aimg.mp hx
    exact hy
  · intro hx
    exact mem_aimg.mpr ⟨⟨x, hY hx⟩, hx, rfl⟩

theorem aimg_iSup {S₀ : Subgroup G} (α : S₀ ≃* S₀) {ι : Sort*} (Y : ι → Subgroup G)
    (hY : ∀ i, Y i ≤ S₀) : aimg S₀ α (⨆ i, Y i) = ⨆ i, aimg S₀ α (Y i) := by
  have hmap : ∀ i, ((Y i).subgroupOf S₀).map S₀.subtype = Y i := fun i =>
    Subgroup.map_subgroupOf_eq_of_le (hY i)
  have h1 : (⨆ i, Y i) = (⨆ i, (Y i).subgroupOf S₀).map S₀.subtype := by
    rw [Subgroup.map_iSup]
    exact iSup_congr fun i => (hmap i).symm
  rw [h1, aimg_map_subtype, Subgroup.map_iSup, Subgroup.map_iSup]
  refine iSup_congr fun i => ?_
  conv_rhs => rw [← hmap i]
  rw [aimg_map_subtype]

theorem isElemAbelian_iSup_of_commute {ι : Sort*} (Y : ι → Subgroup G)
    (hel : ∀ i, CFSG.Open.IsElemAbelian 2 (Y i))
    (hc : ∀ i j, ∀ x ∈ Y i, ∀ y ∈ Y j, x * y = y * x) :
    CFSG.Open.IsElemAbelian 2 (⨆ i, Y i : Subgroup G) := by
  have hK : ∀ x ∈ (⨆ i, Y i : Subgroup G), ∀ y ∈ (⨆ i, Y i : Subgroup G), x * y = y * x := by
    have h1 : ∀ i, (⨆ j, Y j : Subgroup G) ≤ Subgroup.centralizer ((Y i : Subgroup G) : Set G) :=
      fun i => iSup_le fun j y hy => Subgroup.mem_centralizer_iff.mpr fun x hx => hc i j x hx y hy
    have h2 : (⨆ j, Y j : Subgroup G) ≤ Subgroup.centralizer ((⨆ j, Y j : Subgroup G) : Set G) :=
      iSup_le fun i => Subgroup.le_centralizer_iff.mp (h1 i)
    intro x hx y hy
    exact (Subgroup.mem_centralizer_iff.mp (h2 hy) x hx)
  refine isElemAbelian_iff.mpr ⟨hK, fun x hx => ?_⟩
  have key : x ∈ (⨆ i, Y i : Subgroup G) ∧ x ^ 2 = 1 := by
    refine Subgroup.iSup_induction Y (C := fun x => x ∈ (⨆ i, Y i : Subgroup G) ∧ x ^ 2 = 1) hx
      (fun i x hx => ⟨Subgroup.mem_iSup_of_mem i hx, (isElemAbelian_iff.mp (hel i)).2 x hx⟩)
      ⟨one_mem _, one_pow 2⟩ ?_
    rintro a b ⟨ha, ha2⟩ ⟨hb, hb2⟩
    refine ⟨mul_mem ha hb, ?_⟩
    rw [(show Commute a b from hK a ha b hb).mul_pow, ha2, hb2, one_mul]
  exact key.2

@[expose] def Cstar (S : Sylow 2 G) : Subgroup G :=
  ⨆ β : (S : Subgroup G) ≃* (S : Subgroup G), aimg (S : Subgroup G) β (Fcore G)

section Out

variable {k : Type*} [Field k] {S : Sylow 2 G}
  {ρ : G →* Matrix.SpecialLinearGroup (Fin 2) k} {ψ : Ecore G →* Multiplicative (Fin 2 → k)}

theorem IsNatBase.sylow_eq_sup_of_map_eq [Finite G] [Finite k] (h : IsNatBase S ρ (Ecore G) ψ)
    {Y : Subgroup G} (hY : Y ≤ (S : Subgroup G)) (hmap : Y.map ρ = (S : Subgroup G).map ρ) :
    (S : Subgroup G) = Y ⊔ CFSG.pCore 2 G := by
  apply le_antisymm
  · intro s hs
    have : ρ s ∈ Y.map ρ := by rw [hmap]; exact ⟨s, hs, rfl⟩
    obtain ⟨a, ha, hρa⟩ := this
    have hsa : s * a⁻¹ ∈ CFSG.pCore 2 G := by
      have hx : s * a⁻¹ ∈ (S : Subgroup G) ⊓ ρ.ker :=
        Subgroup.mem_inf.mpr ⟨(S : Subgroup G).mul_mem hs ((S : Subgroup G).inv_mem (hY ha)),
          by simp [hρa]⟩
      rwa [h.sylow_inf_ker] at hx
    have : s = (s * a⁻¹) * a := by group
    rw [this]
    exact mul_mem (Subgroup.mem_sup_right hsa) (Subgroup.mem_sup_left ha)
  · exact sup_le hY (core_le_sylow S)

namespace IsSeed

variable [Finite G] [Finite k] (h : IsSeed S ρ (Ecore G) ψ)
include h

theorem outside_translate (α : (S : Subgroup G) ≃* (S : Subgroup G))
    (hα : ¬ aimg (S : Subgroup G) α (Vmod G) ≤ CFSG.pCore 2 G) :
    aimg (S : Subgroup G) α (Vmod G) ⊓ CFSG.pCore 2 G = aimg (S : Subgroup G) α (Zfix S) ∧
      (S : Subgroup G) = CFSG.pCore 2 G ⊔ aimg (S : Subgroup G) α (Vmod G) := by
  classical
  have hCSV := h.sylow_inf_centralizer_Vmod
  have hex : ∃ v ∈ Vmod G, ∃ w ∈ aimg (S : Subgroup G) α (Vmod G), v * w ≠ w * v := by
    by_contra hall
    push Not at hall
    apply hα
    intro w hw
    rw [← hCSV]
    exact ⟨aimg_le hw, Subgroup.mem_centralizer_iff.mpr fun v hv => hall v hv w hw⟩
  obtain ⟨v, hv, w, hw, hne⟩ := hex
  have hvS : v ∈ (S : Subgroup G) := Vmod_le_sylow hv
  have hCvZ : ∀ w₂ ∈ aimg (S : Subgroup G) α (Vmod G), v * w₂ = w₂ * v →
      w₂ ∈ aimg (S : Subgroup G) α (Zfix S) := by
    intro w₂ hw₂ hc
    obtain ⟨y, hy, rfl⟩ := mem_aimg.mp hw₂
    have hs'Q : ((α.symm ⟨v, hvS⟩ : (S : Subgroup G)) : G) ∉ CFSG.pCore 2 G := by
      intro hQ
      apply hne
      obtain ⟨y₀, hy₀, rfl⟩ := mem_aimg.mp hw
      have h1 : (α.symm ⟨v, hvS⟩ : (S : Subgroup G)) * y₀ = y₀ * (α.symm ⟨v, hvS⟩ : (S : Subgroup G)) :=
        Subtype.ext (Ecore_commute_core hQ (Vmod_le_Ecore hy₀))
      have h2 : α (α.symm ⟨v, hvS⟩) * α y₀ = α y₀ * α (α.symm ⟨v, hvS⟩) := by
        rw [← map_mul, ← map_mul, h1]
      rw [α.apply_symm_apply] at h2
      exact congrArg Subtype.val h2
    have hcomm : (α.symm ⟨v, hvS⟩ : (S : Subgroup G)) * y = y * (α.symm ⟨v, hvS⟩ : (S : Subgroup G)) := by
      apply α.injective
      rw [map_mul, map_mul, α.apply_symm_apply]
      exact Subtype.ext hc
    exact mem_aimg_of_mem (h.sylow_not_core_comm_Vmod (α.symm ⟨v, hvS⟩).2 hs'Q hy
      (congrArg Subtype.val hcomm))
  have hA : aimg (S : Subgroup G) α (Vmod G) ⊓ CFSG.pCore 2 G =
      aimg (S : Subgroup G) α (Zfix S) := by
    apply le_antisymm
    · rintro x ⟨hxV, hxQ⟩
      exact hCvZ x hxV (Ecore_commute_core hxQ (Vmod_le_Ecore hv)).symm
    · intro z hz
      refine ⟨aimg_mono (inf_le_left : Zfix S ≤ Vmod G) hz, ?_⟩
      have : z ∈ (S : Subgroup G) ⊓ Subgroup.centralizer (Vmod G : Set G) :=
        ⟨aimg_le hz, Subgroup.mem_centralizer_iff.mpr fun v hv =>
          aimg_Zfix_central α (Vmod_le_sylow hv) hz⟩
      rwa [hCSV] at this
  refine ⟨hA, ?_⟩
  obtain ⟨ℓ, hℓ⟩ := h.exists_rootGrp_eq
  have hYS : aimg (S : Subgroup G) α (Vmod G) ≤ (S : Subgroup G) := aimg_le
  have hker : aimg (S : Subgroup G) α (Vmod G) ⊓ ρ.ker = aimg (S : Subgroup G) α (Zfix S) := by
    rw [← hA]
    apply le_antisymm
    · rintro y ⟨hyY, hyk⟩
      exact ⟨hyY, by rw [← h.sylow_inf_ker]; exact ⟨hYS hyY, hyk⟩⟩
    · rintro y ⟨hyY, hyQ⟩
      exact ⟨hyY, h.core_le hyQ⟩
  have hcardY : Nat.card (aimg (S : Subgroup G) α (Vmod G)) = Nat.card k * Nat.card (Zfix S) := by
    rw [card_aimg Vmod_le_sylow, h.card_k_mul_card_Zfix]
  have hc := card_eq_card_map_mul_card_inf_ker ρ (aimg (S : Subgroup G) α (Vmod G))
  rw [hker, card_aimg Zfix_le_sylow] at hc
  have hpos : 0 < Nat.card (Zfix S) := Nat.card_pos
  have hmapcard : Nat.card ((aimg (S : Subgroup G) α (Vmod G)).map ρ) = Nat.card k :=
    Nat.eq_of_mul_eq_mul_right hpos (by rw [← hc, hcardY])
  have hle : (aimg (S : Subgroup G) α (Vmod G)).map ρ ≤ (S : Subgroup G).map ρ :=
    Subgroup.map_mono hYS
  have hmap : (aimg (S : Subgroup G) α (Vmod G)).map ρ = (S : Subgroup G).map ρ := by
    rw [hℓ] at hle ⊢
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_rootGrp, hmapcard])
  rw [sup_comm]
  exact h.sylow_eq_sup_of_map_eq hYS hmap

theorem Vmod_ne_bot : Vmod G ≠ ⊥ := by
  intro hbot
  obtain ⟨v, hv, hψ⟩ := h.ψ_Vmod_surj (Multiplicative.ofAdd (Pi.single (0 : Fin 2) (1 : k)))
  rw [hbot, Subgroup.mem_bot] at hv
  have hv1 : v = 1 := Subtype.ext hv
  rw [hv1, map_one] at hψ
  have h1 := congrFun (congrArg Multiplicative.toAdd hψ) 0
  simp at h1

theorem hull_of_contained (hV : ∀ β : (S : Subgroup G) ≃* (S : Subgroup G),
    aimg (S : Subgroup G) β (Vmod G) ≤ CFSG.pCore 2 G) :
    (∀ β : (S : Subgroup G) ≃* (S : Subgroup G),
      aimg (S : Subgroup G) β (Fcore G) ≤ CFSG.pCore 2 G) ∧
    CFSG.Open.IsElemAbelian 2 (Cstar S) ∧ Cstar S ≤ CFSG.pCore 2 G ∧
    (∀ γ : (S : Subgroup G) ≃* (S : Subgroup G), aimg (S : Subgroup G) γ (Cstar S) = Cstar S) ∧
    Cstar S ≠ ⊥ := by
  have hFQ : ∀ β : (S : Subgroup G) ≃* (S : Subgroup G),
      aimg (S : Subgroup G) β (Fcore G) ≤ CFSG.pCore 2 G :=
    fun β => h.aimg_Fcore_le_core β (hV β)
  have hcomm : ∀ γ δ : (S : Subgroup G) ≃* (S : Subgroup G),
      ∀ x ∈ aimg (S : Subgroup G) γ (Fcore G), ∀ y ∈ aimg (S : Subgroup G) δ (Fcore G),
        x * y = y * x := by
    intro γ δ x hx y hy
    obtain ⟨f₁, hf₁, rfl⟩ := mem_aimg.mp hx
    obtain ⟨f₂, hf₂, rfl⟩ := mem_aimg.mp hy
    have hmem : ((γ.symm (δ f₂) : (S : Subgroup G)) : G) ∈
        aimg (S : Subgroup G) (δ.trans γ.symm) (Fcore G) :=
      mem_aimg_of_mem (α := δ.trans γ.symm) hf₂
    have hJ := h.aimg_Fcore_le_thompsonJ_core (δ.trans γ.symm) (hV _) hmem
    have hcomm' : (f₁ : G) * ((γ.symm (δ f₂) : (S : Subgroup G)) : G) =
        ((γ.symm (δ f₂) : (S : Subgroup G)) : G) * f₁ :=
      (Fcore_commute_thompsonJ_core hf₁ hJ).symm
    have h1 : f₁ * γ.symm (δ f₂) = γ.symm (δ f₂) * f₁ := Subtype.ext hcomm'
    have h2 := congrArg γ h1
    rw [map_mul, map_mul, γ.apply_symm_apply] at h2
    exact congrArg Subtype.val h2
  have hel : CFSG.Open.IsElemAbelian 2 (Cstar S) :=
    isElemAbelian_iSup_of_commute _ (fun β => isElemAbelian_aimg β isElemAbelian_Fcore) hcomm
  have hCS : Cstar S ≤ (S : Subgroup G) := iSup_le fun β => aimg_le
  have key : ∀ γ : (S : Subgroup G) ≃* (S : Subgroup G),
      aimg (S : Subgroup G) γ (Cstar S) ≤ Cstar S := by
    intro γ
    unfold Cstar
    rw [aimg_iSup γ _ (fun β => aimg_le)]
    refine iSup_le fun β => ?_
    rw [← aimg_trans]
    exact le_iSup (fun β : (S : Subgroup G) ≃* (S : Subgroup G) =>
      aimg (S : Subgroup G) β (Fcore G)) (β.trans γ)
  refine ⟨hFQ, hel, iSup_le hFQ, fun γ => ?_, ?_⟩
  · apply le_antisymm (key γ)
    have h1 := aimg_mono (S := (S : Subgroup G)) (α := γ) (key γ.symm)
    rwa [aimg_aimg_symm hCS] at h1
  · intro hbot
    have hFle : Fcore G ≤ Cstar S := by
      have := le_iSup (fun β : (S : Subgroup G) ≃* (S : Subgroup G) =>
        aimg (S : Subgroup G) β (Fcore G)) (MulEquiv.refl _)
      rwa [aimg_refl_of_le Fcore_le_sylow] at this
    have hV0 : Vmod G ≤ ⊥ := by
      rw [← hbot]; exact (Vmod_le_Ecore.trans h.Ecore_le_Fcore).trans hFle
    exact h.Vmod_ne_bot (le_bot_iff.mp hV0)

theorem outside_core_translate_and_characteristic_hull :
    (∀ α : (S : Subgroup G) ≃* (S : Subgroup G),
      ¬ aimg (S : Subgroup G) α (Vmod G) ≤ CFSG.pCore 2 G →
        aimg (S : Subgroup G) α (Vmod G) ⊓ CFSG.pCore 2 G = aimg (S : Subgroup G) α (Zfix S) ∧
          (S : Subgroup G) = CFSG.pCore 2 G ⊔ aimg (S : Subgroup G) α (Vmod G)) ∧
    ((∀ β : (S : Subgroup G) ≃* (S : Subgroup G),
        aimg (S : Subgroup G) β (Vmod G) ≤ CFSG.pCore 2 G) →
      (∀ β : (S : Subgroup G) ≃* (S : Subgroup G),
        aimg (S : Subgroup G) β (Fcore G) ≤ CFSG.pCore 2 G) ∧
      CFSG.Open.IsElemAbelian 2 (Cstar S) ∧ Cstar S ≤ CFSG.pCore 2 G ∧
      (∀ γ : (S : Subgroup G) ≃* (S : Subgroup G), aimg (S : Subgroup G) γ (Cstar S) = Cstar S) ∧
      Cstar S ≠ ⊥) :=
  ⟨fun α hα => h.outside_translate α hα, fun hV => h.hull_of_contained hV⟩

end IsSeed

end Out

end Hull

end CFSG.QuasithinUnique.Setup.Campbell
