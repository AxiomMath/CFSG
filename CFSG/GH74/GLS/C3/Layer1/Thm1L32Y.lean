module

public import CFSG.GH74.GLS.C3.Layer1.Thm1L32Stable
public import CFSG.GH74.GLS.C3.Layer1.Thm1L32Diag

public section

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.E2 CFSG.GH74.GLS.EvenSelP
  CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.GLS.C3.Layer1.PumpCalc
  CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS.C3.Layer1.Thm1P31c
  CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Proofs2

namespace CFSG.GH74.GLS.C3.Layer1.Thm1L32

section YLevel

variable {G : Type} [Group G] [Finite G] {x f : G}

theorem center_eq_bot_of_hasL2Model_eq {X : Type} [Group X] {r : ℕ} (hr : Odd r)
    (h : HasL2Model X (fun q => q = r)) : center X = ⊥ := by
  have hL2 : HasL2Model X Odd := by
    obtain ⟨p, f', hp, hf, hq, hl⟩ := h
    exact ⟨p, f', hp, hf, hq ▸ hr, hl⟩
  exact Stage1.Thm6.Glue.center_eq_bot_of_isL2Model
    (Stage1.Thm6.Glue.isL2Model_of_hasL2Model (Bk.B810.hasL2Model_gt_three' hL2))

theorem ylevel (T : StableTables) (hF : E2ComponentFacts) (hC2 : C2Facts) (hG : C3Hyp G)
    (hLoc2 : LocL2) (hLocA7 : LocA7) {K Λ : Subgroup G} (E : YEnv G x f Λ)
    (hlay : pLayerOf 2 (K ⊓ centralizer ({f} : Set G)) = Λ) {r : ℕ} (hrodd : Odd r)
    (hr : HasL2Model (kBar Λ) (fun q => q = r))
    (hM12 : ∀ L : Subgroup (barQ ↥(centralizer ({f} : Set G))), ∀ S : Stable32 E L,
      S.sigma ≠ 1 → Shape2M12 ↥L → False) :
    IsPCompIn 2 (centralizer ({f} : Set G)) (pumpUp 2 K f) ∧
      (∀ c ∈ centralizer ({f} : Set G), ∀ j ∈ pumpUp 2 K f, c * j * c⁻¹ ∈ pumpUp 2 K f) ∧
      (HasL2Model (kBar (pumpUp 2 K f)) (fun q => q = r) ∨
        HasL2Model (kBar (pumpUp 2 K f)) (fun q => q = r ^ 2) ∨
        (r = 5 ∧ Nonempty (kBar (pumpUp 2 K f) ≃* alternatingGroup (Fin 7)))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxY := E.hxY
  obtain ⟨hΛE, hJsub, L, hL, hcases, hLJ, hLsJ, hK'⟩ :=
    TwoThin.pumpupY_structure E.hsO E.hΛC E.hΛ2
  rcases hcases with ⟨hst, hΛL⟩ | ⟨hne, hAB, hΛΔ⟩
  swap
  · exact (diag_false' hF hC2 hG E.hx2 E.hf2 E.hxf E.hΛ E.hΛU hL hne hAB hΛΔ).elim
  let S : Stable32 E L := ⟨hL, hst, hΛL⟩
  have hshape : (HasL2Model ↥L (fun q => q = r) ∨ HasL2Model ↥L (fun q => q = r ^ 2) ∨
      (r = 5 ∧ Nonempty (↥L ≃* alternatingGroup (Fin 7)))) := by
    rcases S.classify T hF hG hLoc2 hLocA7 hrodd hr with ⟨-, h⟩ | ⟨hσ, h | h | h2M⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact (hM12 L S hσ h2M).elim
  have hcen : center ↥L = ⊥ := by
    rcases hshape with h | h | ⟨-, ⟨e7⟩⟩
    · exact center_eq_bot_of_hasL2Model_eq hrodd h
    · exact center_eq_bot_of_hasL2Model_eq (hrodd.pow) h
    · exact Stage1.Thm6.Glue.center_eq_bot_of_isA7Model ⟨e7⟩
  obtain ⟨L', hL'c, hbar⟩ := exists_lift_component hL
  have hq : CFSG.IsQuasisimple (kBar L') := isQuasisimple_hat hL'c
  obtain ⟨e⟩ := kBar_equiv_bar hL'c
  let e' : kBar L' ≃* ↥L := e.trans (MulEquiv.subgroupCongr hbar)
  have hcenL' : Subgroup.center (kBar L') = ⊥ := by
    have h1 : (Subgroup.center (kBar L')).map e'.toMonoidHom = Subgroup.center ↥L :=
      Subgroup.map_center_eq e'
    rw [hcen] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e'.injective).1 h1
  have hnormL' : ∀ a ∈ centralizer ({f} : Set G), a ∈ normalizer (L' : Set G) := fun a ha =>
    PumpGen.mem_normalizer_of_centerless hG.pRank_eq_four ⟨E.hf2, hL'c⟩ hq hcenL' ha
  have hL'Y : L' ≤ centralizer ({f} : Set G) := hL'c.1
  have hΛL' : Λ ≤ L' := by
    have hnorm : (L'.subgroupOf (centralizer ({f} : Set G))).Normal := ⟨fun n hn g => by
      have hn' : (n : G) ∈ L' := hn
      exact Subgroup.mem_subgroupOf.2
        ((Subgroup.mem_normalizer_iff.1 (hnormL' (g : G) g.2) _).1 hn')⟩
    have hperfY : ⁅Λ.subgroupOf (centralizer ({f} : Set G)), Λ.subgroupOf (centralizer ({f} : Set G))⁆ =
        Λ.subgroupOf (centralizer ({f} : Set G)) := commutator_self_of_isTwoComponent E.hΛC E.hΛ2
    have hperf : Group.IsPerfect ↥(Λ.subgroupOf (centralizer ({f} : Set G))) :=
      Subgroup.isPerfect_iff.mpr hperfY
    have hsolv : Group.IsSolvable ↥(barMk ↥(centralizer ({f} : Set G))).ker :=
      CFSG.FeitThompson.isSolvable_of_odd_natCard _ odd_card_ker_barMk
    have himg : (Λ.subgroupOf (centralizer ({f} : Set G))).map (barMk ↥(centralizer ({f} : Set G))) ≤
        (L'.subgroupOf (centralizer ({f} : Set G))).map (barMk ↥(centralizer ({f} : Set G))) := by
      have h1 : (L'.subgroupOf (centralizer ({f} : Set G))).map (barMk ↥(centralizer ({f} : Set G))) = L := hbar
      rw [h1]
      exact hΛL
    have hle := SolvableKernelContainment.perfect_containment (barMk ↥(centralizer ({f} : Set G)))
      (Λ.subgroupOf (centralizer ({f} : Set G))) (L'.subgroupOf (centralizer ({f} : Set G))) himg
    intro a ha
    exact Subgroup.mem_subgroupOf.1 (hle (Subgroup.mem_subgroupOf.2 ha : (⟨a, E.hΛY ha⟩ : ↥(centralizer ({f} : Set G))) ∈ _))
  have hJ : pumpUp 2 K f = L' := by
    apply le_antisymm
    · refine iSup₂_le fun g hg => ?_
      rw [hlay]
      rintro _ ⟨a, ha, rfl⟩
      have hgY : g ∈ centralizer ({f} : Set G) := pLayerOf_le 2 _ hg
      exact (Subgroup.mem_normalizer_iff.1 (hnormL' g hgY) a).1 (hΛL' ha)
    · rw [pumpUp_eq_map_pumpupY, hlay]
      intro a ha
      have hL'2 : TwoComponents.IsTwoComponent (L'.subgroupOf (centralizer ({f} : Set G))) :=
        (isPCompIn_two_iff.1 hL'c).2
      have hmap : (L'.subgroupOf (centralizer ({f} : Set G))).map (barMk ↥(centralizer ({f} : Set G))) = L := hbar
      have hle := (hK' _ hL'2).2 (Or.inl hmap)
      exact ⟨⟨a, hL'Y ha⟩, hle (Subgroup.mem_subgroupOf.2 ha), rfl⟩
  rw [hJ]
  refine ⟨hL'c, fun c hc j hj => (Subgroup.mem_normalizer_iff.1 (hnormL' c hc) j).1 hj, ?_⟩
  rcases hshape with ⟨p, f', hp, hf, hq', hlie⟩ | ⟨p, f', hp, hf, hq', hlie⟩ | ⟨hr5, ⟨e7⟩⟩
  · exact Or.inl ⟨p, f', hp, hf, hq', lieModel_of_mulEquiv e'.symm hlie⟩
  · exact Or.inr (Or.inl ⟨p, f', hp, hf, hq', lieModel_of_mulEquiv e'.symm hlie⟩)
  · exact Or.inr (Or.inr ⟨hr5, ⟨e'.trans e7⟩⟩)

end YLevel

end CFSG.GH74.GLS.C3.Layer1.Thm1L32
