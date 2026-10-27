module

public import CFSG.GH74.GLS.IVK.Lifted32.HypBar
public import CFSG.GH74.GLS.IVK.Statements.Sec32
public import CFSG.GH74.GLS.IVK.Lifted.FStarC

public section

namespace CFSG.GH74.GLS.IVK.Lifted32

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5
  CFSG.GH74.GLS.Stage1.Thm4 CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank
open CFSG.GH74.GLS.Stage2.Local (Cen toBar barOf)
open CFSG.GH74.GLS.Stage1.Thm2.Recip (II4_44)
open scoped commutatorElement

namespace Hyp

section Setting

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G}

theorem centralizer_bar_le (hII : II4_4_4_center) (hC : Cfg5 G z S K₁ K₂) :
    centralizer ((barOf z K₁ ⊔ barOf z K₂ : Subgroup (CentralizerBar z)) : Set (CentralizerBar z)) ≤
      zpowers (zBar z) := by
  intro h hh
  obtain ⟨c, rfl⟩ := toBar_surjective (z := z) h
  have hKC : K₁ ⊔ K₂ ≤ Cz z := sup_le (K_le_Cz hC (Or.inl rfl)) (K_le_Cz hC (Or.inr rfl))
  have hcomm : ∀ k ∈ K₁ ⊔ K₂, ⁅k, (c : G)⁆ ∈ Oz z := by
    intro k hk
    have hkb : toBar z ⟨k, hKC hk⟩ ∈ barOf z K₁ ⊔ barOf z K₂ := by
      rw [← barOf_sup (K_le_Cz hC (Or.inl rfl)) (K_le_Cz hC (Or.inr rfl))]
      exact toBar_mem_barOf hk
    have h1 := Subgroup.mem_centralizer_iff.1 hh _ hkb
    have h2 : toBar z ⁅(⟨k, hKC hk⟩ : ↥(Cz z)), (c : ↥(Cz z))⁆ = 1 := by
      rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, h1]
      group
    have := (toBar_eq_one_iff).1 h2
    simpa [commutatorElement_def] using this
  have hmem := (IVK.Lifted.fStar_C_of_II4 hII) G z S K₁ K₂ hC.std hC.hQ (c : G) c.2 hcomm
  let M : Subgroup G := ((zpowers (zBar z)).comap (toBar z)).map (Cz z).subtype
  have hz : zpowers z ≤ M := by
    rw [Subgroup.zpowers_le]
    exact ⟨zElt z, Subgroup.mem_zpowers _, rfl⟩
  have hO : Oz z ≤ M := by
    intro o ho
    have hoC : o ∈ Cz z := TwoThin.pPrimeCoreOf_le (Cz z) ho
    refine ⟨⟨o, hoC⟩, ?_, rfl⟩
    show toBar z ⟨o, hoC⟩ ∈ zpowers (zBar z)
    rw [(toBar_eq_one_iff (c := ⟨o, hoC⟩)).2 ho]
    exact one_mem _
  obtain ⟨c', hc', hcc'⟩ := sup_le hz hO hmem
  have : c' = c := Subtype.ext hcc'
  rw [← this]
  exact hc'

theorem layer_le (hII : II4_4_4_center) (hC : Cfg5 G z S K₁ K₂) :
    layer (CentralizerBar z) ≤ barOf z K₁ ⊔ barOf z K₂ := by
  refine sSup_le fun L hL => ?_
  have h1 := CFSG.LocalCores.distinct_components_commute hL (isComponent_bar' hC (Or.inl rfl))
  have h2 := CFSG.LocalCores.distinct_components_commute hL (isComponent_bar' hC (Or.inr rfl))
  rcases h1 with h1 | h1
  · rw [h1]; exact le_sup_left
  rcases h2 with h2 | h2
  · rw [h2]; exact le_sup_right
  exfalso
  have hLc : L ≤ centralizer ((barOf z K₁ ⊔ barOf z K₂ : Subgroup (CentralizerBar z)) :
      Set (CentralizerBar z)) := by
    rw [Subgroup.le_centralizer_iff]
    refine sup_le ?_ ?_
    · rw [Subgroup.le_centralizer_iff]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h1
    · rw [Subgroup.le_centralizer_iff]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h2
  have hLz : L ≤ zpowers (zBar z) := hLc.trans (centralizer_bar_le hII hC)
  have : Group.IsSolvable ↥(zpowers (zBar z)) := inferInstance
  have hs : Group.IsSolvable ↥L := Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hLz)
  have : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial hL.1
  have : Group.IsPerfect ↥L := hL.1.1
  exact Group.IsPerfect.not_isSolvable ↥L hs

theorem bar_sup_le_layer (hC : Cfg5 G z S K₁ K₂) :
    barOf z K₁ ⊔ barOf z K₂ ≤ layer (CentralizerBar z) :=
  sup_le (le_sSup (isComponent_bar' hC (Or.inl rfl))) (le_sSup (isComponent_bar' hC (Or.inr rfl)))

theorem fstar_eq (hII : II4_4_4_center) (hC : Cfg5 G z S K₁ K₂) :
    generalizedFitting (CentralizerBar z) = barOf z K₁ ⊔ barOf z K₂ := by
  have hzK : zBar z ∈ barOf z K₁ ⊔ barOf z K₂ :=
    Subgroup.mem_sup_left (zBar_mem_barOf (z_mem_comp hII hC (Or.inl rfl)))
  have hF : fittingSubgroup (CentralizerBar z) ≤ barOf z K₁ ⊔ barOf z K₂ := by
    have hcomm := CFSG.LocalCores.fitting_layer_commute (G := CentralizerBar z)
    have h1 : fittingSubgroup (CentralizerBar z) ≤
        centralizer ((layer (CentralizerBar z) : Subgroup (CentralizerBar z)) : Set (CentralizerBar z)) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
    have h2 := h1.trans (Subgroup.centralizer_le (G := CentralizerBar z) (bar_sup_le_layer hC))
    exact (h2.trans (centralizer_bar_le hII hC)).trans ((Subgroup.zpowers_le).2 hzK)
  exact le_antisymm (sup_le hF (layer_le hII hC)) ((bar_sup_le_layer hC).trans le_sup_right)

theorem isDoubleCoverOfAlt_of_equiv {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q') {n : ℕ}
    (h : IsDoubleCoverOfAlt Q n) : IsDoubleCoverOfAlt Q' n := by
  obtain ⟨hq, hc, ⟨i⟩⟩ := h
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq, ?_, ?_⟩
  · rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact hc
  · have hc' : (center Q).map (e : Q →* Q') = center Q' := Subgroup.map_center_eq e
    let e' : Q ⧸ center Q ≃* Q' ⧸ center Q' := QuotientGroup.congr _ _ e hc'
    exact ⟨e'.symm.trans i⟩

theorem type_bar (h44 : II4_44) (hC : Cfg5 G z S K₁ K₂) {K : Subgroup G} (hK : K = K₁ ∨ K = K₂) :
    HasSL2Model ↥(barOf z K) (fun q => Odd q ∧ 5 ≤ q) ∨ IsDoubleCoverOfAlt ↥(barOf z K) 7 := by
  have hKmem : K ∈ ({K₁, K₂} : Set (Subgroup G)) := by rcases hK with rfl | rfl <;> simp
  have hOK := IVK.Lifted.std4_hatOK h44 hC.std hKmem
  have Φ := L97.hatBar (rigid_of_comp hC hK)
  rcases hOK.sl2.1 with ⟨F, hF, hFin, hP, ⟨e⟩⟩ | h7
  · exact Or.inl ⟨F, hF, hFin, hP, ⟨Φ.symm.trans e⟩⟩
  · exact Or.inr (isDoubleCoverOfAlt_of_equiv Φ h7)

theorem card_center_bar (h44 : II4_44) (hC : Cfg5 G z S K₁ K₂) {K : Subgroup G}
    (hK : K = K₁ ∨ K = K₂) : Nat.card ↥(center ↥(barOf z K)) = 2 := by
  have hKmem : K ∈ ({K₁, K₂} : Set (Subgroup G)) := by rcases hK with rfl | rfl <;> simp
  have hOK := IVK.Lifted.std4_hatOK h44 hC.std hKmem
  have h2 := hOK.sl2.2
  have := Nat.card_congr (Subgroup.centerCongr (L97.hatBar (rigid_of_comp hC hK))).toEquiv
  rw [h2] at this
  exact this.symm

theorem center_bar_eq (hII : II4_4_4_center) (h44 : II4_44) (hC : Cfg5 G z S K₁ K₂) :
    (Subgroup.center ↥(barOf z K₁ ⊔ barOf z K₂)).map (barOf z K₁ ⊔ barOf z K₂).subtype =
      zpowers (zBar z) := by
  have hcomm : ∀ a ∈ barOf z K₁, ∀ b ∈ barOf z K₂, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.1 (bar_comm hC ha) b hb).symm
  have hzK₁ : zBar z ∈ barOf z K₁ := zBar_mem_barOf (z_mem_comp hII hC (Or.inl rfl))
  have hzK₂ : zBar z ∈ barOf z K₂ := zBar_mem_barOf (z_mem_comp hII hC (Or.inr rfl))
  have hord := orderOf_zBar hC.std.orderOf_z
  have hcen : ∀ K : Subgroup G, (K = K₁ ∨ K = K₂) → zBar z ∈ barOf z K → ∀ a ∈ barOf z K,
      (∀ u ∈ barOf z K, a * u = u * a) → a ∈ zpowers (zBar z) := by
    intro K hK hz a ha hac
    let z' : ↥(barOf z K) := ⟨zBar z, hz⟩
    have hz'c : z' ∈ center ↥(barOf z K) :=
      Subgroup.mem_center_iff.2 (fun u => Subtype.ext (zBar_comm (u : CentralizerBar z)).symm)
    have hcardz : Nat.card ↥(zpowers z') = 2 := by
      rw [Nat.card_zpowers, ← Subgroup.orderOf_coe z']
      exact hord
    have hle : zpowers z' ≤ center ↥(barOf z K) := (Subgroup.zpowers_le).2 hz'c
    have heq : zpowers z' = center ↥(barOf z K) :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [card_center_bar h44 hC hK, hcardz])
    have hac' : (⟨a, ha⟩ : ↥(barOf z K)) ∈ center ↥(barOf z K) :=
      Subgroup.mem_center_iff.2 (fun u => Subtype.ext (hac u u.2).symm)
    rw [← heq] at hac'
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hac'
    have := congrArg Subtype.val hk
    exact ⟨k, by simpa [z'] using this⟩
  apply le_antisymm
  · rintro _ ⟨⟨x, hx⟩, hxc, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := M.mem_sup_of_commute hcomm hx
    have hxc' : ∀ y ∈ barOf z K₁ ⊔ barOf z K₂, y * (a * b) = (a * b) * y := fun y hy =>
      congrArg Subtype.val (Subgroup.mem_center_iff.1 hxc ⟨y, hy⟩)
    have ha' : ∀ u ∈ barOf z K₁, a * u = u * a := by
      intro u hu
      have h1 := hxc' u (Subgroup.mem_sup_left hu)
      have h2 : b * u = u * b := (hcomm u hu b hb).symm
      have : u * a * b = a * u * b := by
        calc u * a * b = u * (a * b) := by group
          _ = (a * b) * u := h1
          _ = a * (b * u) := by group
          _ = a * (u * b) := by rw [h2]
          _ = a * u * b := by group
      exact (mul_right_cancel this).symm
    have hb' : ∀ u ∈ barOf z K₂, b * u = u * b := by
      intro u hu
      have h1 := hxc' u (Subgroup.mem_sup_right hu)
      have h2 : a * u = u * a := hcomm a ha u hu
      have : a * (u * b) = a * (b * u) := by
        calc a * (u * b) = (a * u) * b := by group
          _ = (u * a) * b := by rw [h2]
          _ = u * (a * b) := by group
          _ = (a * b) * u := h1
          _ = a * (b * u) := by group
      exact (mul_left_cancel this).symm
    exact (zpowers (zBar z)).mul_mem (hcen _ (Or.inl rfl) hzK₁ a ha ha')
      (hcen _ (Or.inr rfl) hzK₂ b hb hb')
  · rw [Subgroup.zpowers_le]
    refine ⟨⟨zBar z, Subgroup.mem_sup_left hzK₁⟩, Subgroup.mem_center_iff.2 ?_, rfl⟩
    intro g
    exact Subtype.ext (zBar_comm (g : CentralizerBar z)).symm

end Setting

end Hyp

section Deliverables

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G} {a x : G}

open Hyp

theorem setting_of_cfg5 (hII : II4_4_4_center) (h44 : II4_44) (hC : Cfg5 G z S K₁ K₂) :
    IVK.Prod3.Setting (CentralizerBar z) (barOf z K₁) (barOf z K₂) (zBar z) where
  fstar := fstar_eq hII hC
  comm := fun _ ha b hb => (Subgroup.mem_centralizer_iff.1 (bar_comm hC ha) b hb).symm
  type₁ := type_bar h44 hC (Or.inl rfl)
  type₂ := type_bar h44 hC (Or.inr rfl)
  z_ord := orderOf_zBar hC.std.orderOf_z
  zK := center_bar_eq hII h44 hC

theorem elt5_mem_Cen (_hII : II4_4_4_center) (hC : Cfg5 G z S K₁ K₂) (h : Elt5 G z S K₁ K₂ a) :
    a ∈ Cen z :=
  hC.std.sylow.le h.mem

end Deliverables

end CFSG.GH74.GLS.IVK.Lifted32
