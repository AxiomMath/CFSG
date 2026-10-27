module

public import CFSG.LargeExtraspecial.S111SJSet
public import CFSG.LargeExtraspecial.S111SJBenE

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup CFSG.Open CFSG.LargeExtraspecial.S4 CFSG.ComponentClassification

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem map_conj_Lbar_subgroupOf (h : S.M) :
    ((S.Lbar g).subgroupOf S.Mbar).map
        (MulAut.conj (⟨S.ρ h, ⟨h, rfl⟩⟩ : S.Mbar)).toMonoidHom =
      (S.Lbar ((h : G) * g)).subgroupOf S.Mbar := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [mem_subgroupOf, S4.Lbar_mul S h g]
    exact ⟨z, mem_subgroupOf.mp hz, rfl⟩
  · intro hy
    rw [mem_subgroupOf, S4.Lbar_mul S h g] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    exact ⟨⟨z, S.Lbar_le_Mbar g hz⟩, mem_subgroupOf.mpr hz, Subtype.ext hzy⟩

theorem exists_rho_eq (x : S.Mbar) : ∃ h : S.M, (⟨S.ρ h, ⟨h, rfl⟩⟩ : S.Mbar) = x := by
  obtain ⟨h, hh⟩ := x.2
  exact ⟨h, Subtype.ext hh⟩

theorem weakly_subgroupOf (hy : Hyp S g) (x : S.Mbar)
    (hle : ((S.Lbar g).subgroupOf S.Mbar).map (MulAut.conj x).toMonoidHom ≤
      normalizer (((S.Lbar g).subgroupOf S.Mbar : Subgroup S.Mbar) : Set S.Mbar)) :
    ((S.Lbar g).subgroupOf S.Mbar).map (MulAut.conj x).toMonoidHom =
      (S.Lbar g).subgroupOf S.Mbar := by
  obtain ⟨h, rfl⟩ := exists_rho_eq x
  rw [map_conj_Lbar_subgroupOf] at hle ⊢
  have hle' : S.Lbar ((h : G) * g) ≤ normalizer (S.Lbar g : Set S.O) := by
    intro y hy'
    have hyM : y ∈ S.Mbar := S.Lbar_le_Mbar _ hy'
    have hyn := hle (mem_subgroupOf.mpr hy' : (⟨y, hyM⟩ : S.Mbar) ∈ _)
    rw [mem_normalizer_iff] at hyn ⊢
    intro z
    by_cases hz : z ∈ S.Mbar
    · have := hyn ⟨z, hz⟩
      simpa [mem_subgroupOf] using this
    · constructor
      · intro hzL
        exact absurd (S.Lbar_le_Mbar g hzL) hz
      · intro hzL
        exfalso
        apply hz
        have h1 := S.Lbar_le_Mbar g hzL
        have h2 : z = y⁻¹ * (y * z * y⁻¹) * y := by group
        rw [h2]
        exact S.Mbar.mul_mem (S.Mbar.mul_mem (S.Mbar.inv_mem hyM) h1) hyM
  rw [hy.cons.weaklyClosed h h.2 hle']

theorem not_TI_subgroupOf (hT : ∃ t ∈ S.Lbar g, t ≠ 1 ∧ Rbar S g t ≠ S.Lbar g) :
    ∃ t ∈ (S.Lbar g).subgroupOf S.Mbar, t ≠ 1 ∧ ∃ x : S.Mbar,
      t ∈ ((S.Lbar g).subgroupOf S.Mbar).map (MulAut.conj x).toMonoidHom ∧
      ((S.Lbar g).subgroupOf S.Mbar).map (MulAut.conj x).toMonoidHom ≠
        (S.Lbar g).subgroupOf S.Mbar := by
  obtain ⟨t, ht, ht1, hR⟩ := hT
  obtain ⟨X, ⟨h, rfl, htX⟩, hne⟩ : ∃ X ∈ Dset S g t, X ≠ S.Lbar g := by
    by_contra hno
    push Not at hno
    apply hR
    refine le_antisymm (sSup_le fun X hX => (hno X hX).le) (le_sSup ⟨1, ?_, ht⟩)
    simp
  refine ⟨⟨t, S.Lbar_le_Mbar g ht⟩, mem_subgroupOf.mpr ht, fun h1 => ht1 (congrArg Subtype.val h1),
    ⟨S.ρ h, ⟨h, rfl⟩⟩, ?_, ?_⟩
  · rw [map_conj_Lbar_subgroupOf]
    exact mem_subgroupOf.mpr htX
  · rw [map_conj_Lbar_subgroupOf]
    intro heq
    apply hne
    have h1 := subgroupOf_inj.mp heq
    rwa [inf_eq_left.mpr (S.Lbar_le_Mbar _), inf_eq_left.mpr (S.Lbar_le_Mbar g)] at h1

theorem layerCfg_of' (hy : Hyp S g) (hirr : ¬ S.IsReducible) (h4 : 4 ≤ S.width)
    (hT : ∃ t ∈ S.Lbar g, t ≠ 1 ∧ Rbar S g t ≠ S.Lbar g)
    (h55 : Nat.card (timmesfeldOddCore S.Mbar) ∣ 3 ∧
      CFSG.Open.IsQuasisimple (timmesfeldLayer S.Mbar) ∧
      timmesfeldFStar S.Mbar = timmesfeldOddCore S.Mbar ⊔ timmesfeldLayer S.Mbar)
    (hfaith : ∀ {x : S.Mbar}, (x : S.O) ∈ S.Lbar g →
      (∀ e ∈ timmesfeldLayer S.Mbar, e * x = x * e) → x = 1) :
    LayerCfg (timmesfeldLayer S.Mbar) (timmesfeldOddCore S.Mbar) ((S.Lbar g).subgroupOf S.Mbar)
      S.width (S.O.subtype.comp S.Mbar.subtype) (S.cl (g * S.z * g⁻¹)) := by
  have haQ := hy.hyp4.conj_mem
  have hF : ((timmesfeldOddCore S.Mbar ⊔ timmesfeldLayer S.Mbar : Subgroup S.Mbar) : Set S.Mbar) =
      (GeneralizedFitting.subgroup S.Mbar : Set S.Mbar) := by
    rw [← h55.2.2]
    rfl
  have hfix : ∀ v : S.Qt, (∀ x ∈ S.Lbar g, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) ↔
      v ∈ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
    intro v
    rw [← hy.hyp4.fixSub_eq, mem_fixSub]
  refine
    { quasi := h55.2.1
      card_O := h55.1
      fstar_inv := fun v hv2 hv => eq_one_of_mem_centralizer_fstar hv2 (by rwa [hF] at hv)
      fstar_cent := ?_
      L_sq := fun x hx => Subtype.ext (S4.mul_self_of_mem_Lbar S haQ (mem_subgroupOf.mp hx))
      L_comm := fun x hx y hy' => Subtype.ext (S4.Lbar_comm S haQ (mem_subgroupOf.mp hx)
        (mem_subgroupOf.mp hy'))
      L_faith := fun x hx hxE => hfaith (mem_subgroupOf.mp hx) hxE
      four_le := h4
      card_L := by
        rw [Nat.card_congr (subgroupOfEquivOfLe (S.Lbar_le_Mbar g)).toEquiv, hy.cons.card_Lbar]
      weakly := weakly_subgroupOf hy
      not_TI := not_TI_subgroupOf hT
      rho_inj := S.O.subtype_injective.comp S.Mbar.subtype_injective
      finrank_eq := S.finrank_Qt_eq_two_mul_width
      irr := ?_
      a_ne := cl_conj_z_ne_zero S haQ hy.hyp4.conj_ne
      a_fix := fun x hx => (hfix _).mpr (Submodule.mem_span_singleton_self _) x
        (mem_subgroupOf.mp hx)
      fix_eq := ?_ }
  · intro x hx
    have h1 : x ∈ (GeneralizedFitting.subgroup S.Mbar : Set S.Mbar) :=
      GeneralizedFitting.centralizer_le S.Mbar (by rwa [← hF])
    rw [← hF] at h1
    exact h1
  · intro W hW
    by_contra hne
    push Not at hne
    exact hirr ⟨W, hne.1, hne.2, fun m v hv => hW ⟨S.ρ m, ⟨m, rfl⟩⟩ v hv⟩
  · intro v hv
    have h1 := (hfix v).mp fun x hx => hv ⟨x, S.Lbar_le_Mbar g hx⟩ (mem_subgroupOf.mpr hx)
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp h1
    rcases CFSG.RankThree.Literature.FSmith.zmod2_cases r with rfl | rfl
    · left
      exact zero_smul _ _
    · right
      exact one_smul _ _

theorem layerCfg_of (hy : Hyp S g) (hirr : ¬ S.IsReducible) (h6 : 6 ≤ S.width)
    (hT : ∃ t ∈ S.Lbar g, t ≠ 1 ∧ Rbar S g t ≠ S.Lbar g)
    (h55 : Nat.card (timmesfeldOddCore S.Mbar) ∣ 3 ∧
      CFSG.Open.IsQuasisimple (timmesfeldLayer S.Mbar) ∧
      timmesfeldFStar S.Mbar = timmesfeldOddCore S.Mbar ⊔ timmesfeldLayer S.Mbar) :
    LayerCfg (timmesfeldLayer S.Mbar) (timmesfeldOddCore S.Mbar) ((S.Lbar g).subgroupOf S.Mbar)
      S.width (S.O.subtype.comp S.Mbar.subtype) (S.cl (g * S.z * g⁻¹)) :=
  layerCfg_of' hy hirr (by omega) hT h55
    (fun hx hxE => eq_one_of_mem_Lbar_of_commute hy hirr h6 h55 hx hxE)

theorem shultF6ResidualE_of :
    ShultF6ResidualE := by
  intro G _ _ _ S g hy hirr h6 hT P t ht ht1 htP htc hab hWP hcl hGo h55 hni hmove
  have := S5.timmesfeldOddCore_normal S.Mbar
  have htK : t ∈ normalClosure (wcl t : Set S.Mbar) :=
    subset_normalClosure (self_mem_wcl t)
  have hEK := le_of_not_commute h55.2.1 htK hmove
  obtain ⟨-, -, hG⟩ := hGo
  have hGT := goldschmidtSimpleType_of_le h55.2.1 hEK hG
  exact (layerCfg_of hy hirr h6 hT h55).false_of_goldschmidtSimpleType h6 hGT

end CFSG.LargeExtraspecial.S11
