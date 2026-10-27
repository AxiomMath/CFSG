module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsGF2
import CFSG.GroupTheory.ConjTransport
import CFSG.GroupTheory.SylowIntersectionControl.GomiGstar

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin (ffJ fixV)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719 (Pset PstarSet O2Trivial)
open scoped commutatorElement

section Module

variable {W : Type} [CommGroup W] {Y A : Subgroup (MulAut W)} {y : MulAut W}

private theorem map_conj_eq_self_of_mem {H : Subgroup (MulAut W)} {g : MulAut W} (hg : g ∈ H) :
    H.map (MulAut.conj g).toMonoidHom = H :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hg)

theorem le_of_mem_gomiNSet {N : Subgroup (MulAut W)} (hN : N ∈ gomiNSet Y) : N ≤ Y := by
  obtain ⟨B, hB, rfl⟩ := hN
  have hBY : B ≤ Y := hB.1.1.1
  refine iSup₂_le fun g hg => ?_
  calc B.map (MulAut.conj g).toMonoidHom ≤ Y.map (MulAut.conj g).toMonoidHom :=
        Subgroup.map_mono hBY
    _ = Y := map_conj_eq_self_of_mem (gomiGstar0_le Y hg)

theorem map_conj_mem_gomiNSet {N : Subgroup (MulAut W)} (hN : N ∈ gomiNSet Y) (hy : y ∈ Y) :
    N.map (MulAut.conj y).toMonoidHom ∈ gomiNSet Y := by
  obtain ⟨B, hB, rfl⟩ := hN
  refine ⟨B.map (MulAut.conj y).toMonoidHom, map_conj_mem_gomiPstar0Set hB hy, ?_⟩
  have hYN : Y ≤ Subgroup.normalizer (gomiGstar0 Y : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (gomiGstar0_le Y)).mp
      (gomiGstar0_subgroupOf_normal Y)
  have hconj : ∀ g ∈ gomiGstar0 Y, y * g * y⁻¹ ∈ gomiGstar0 Y := fun g hg =>
    (Subgroup.mem_normalizer_iff.mp (hYN hy) g).mp hg
  have hconj' : ∀ g ∈ gomiGstar0 Y, y⁻¹ * g * y ∈ gomiGstar0 Y := fun g hg =>
    (Subgroup.mem_normalizer_iff.mp (hYN (Y.inv_mem hy)) g).mp hg
  rw [gomiOrbitSpan, gomiOrbitSpan, Subgroup.map_iSup]
  simp only [Subgroup.map_iSup]
  refine le_antisymm (iSup₂_le fun g hg => ?_) (iSup₂_le fun g hg => ?_)
  · refine le_iSup₂_of_le (y * g * y⁻¹) (hconj g hg) ?_
    rw [map_conj_map_conj y g B, map_conj_map_conj (y * g * y⁻¹) y B]
    rw [show y * g * y⁻¹ * y = y * g by group]
  · refine le_iSup₂_of_le (y⁻¹ * g * y) (hconj' g hg) ?_
    rw [map_conj_map_conj g y B, map_conj_map_conj y (y⁻¹ * g * y) B]
    rw [show y * (y⁻¹ * g * y) = g * y by group]

theorem exists_mem_pstarSet_le [Finite W] (hA : A ∈ Pset Y) : ∃ B ∈ PstarSet Y, B ≤ A := by
  set T : Set ℕ := {n | ∃ C : Subgroup (MulAut W), C ∈ Pset Y ∧ C ≤ A ∧
    Nat.card C * Nat.card (fixV C) = Nat.card A * Nat.card (fixV A) ∧ Nat.card C = n}
  have hT : T.Nonempty := ⟨Nat.card A, A, hA, le_rfl, rfl, rfl⟩
  obtain ⟨B, hBP, hBA, hBcard, hBm⟩ := Nat.sInf_mem hT
  refine ⟨B, ⟨hBP, fun C hCP hCB hCeq => ?_⟩, hBA⟩
  have hCT : Nat.card C ∈ T := ⟨C, hCP, hCB.trans hBA, hCeq.symm.trans hBcard, rfl⟩
  exact Subgroup.eq_of_le_of_card_ge hCB (hBm ▸ Nat.sInf_le hCT)

theorem mem_pset_iff_of_le {S : Subgroup (MulAut W)} (hSY : S ≤ Y) :
    A ∈ Pset S ↔ A ∈ Pset Y ∧ A ≤ S := by
  constructor
  · rintro ⟨hAS, hne, hea, hineq⟩
    exact ⟨⟨hAS.trans hSY, hne, hea, hineq⟩, hAS⟩
  · rintro ⟨⟨hAY, hne, hea, hineq⟩, hAS⟩
    exact ⟨hAS, hne, hea, hineq⟩

theorem mem_pstarSet_iff_of_le {S : Subgroup (MulAut W)} (hSY : S ≤ Y) :
    A ∈ PstarSet S ↔ A ∈ PstarSet Y ∧ A ≤ S := by
  constructor
  · rintro ⟨hAP, hAmin⟩
    have hA' := (mem_pset_iff_of_le (A := A) hSY).mp hAP
    refine ⟨⟨hA'.1, fun B hBP hBA hcard => ?_⟩, hA'.2⟩
    exact hAmin B ((mem_pset_iff_of_le (A := B) hSY).mpr ⟨hBP, hBA.trans hA'.2⟩) hBA hcard
  · rintro ⟨⟨hAP, hAmin⟩, hAS⟩
    refine ⟨(mem_pset_iff_of_le (A := A) hSY).mpr ⟨hAP, hAS⟩, fun B hBP hBA hcard => ?_⟩
    exact hAmin B ((mem_pset_iff_of_le (A := B) hSY).mp hBP).1 hBA hcard

theorem sSup_pstarSet_le_ffJ (Y : Subgroup (MulAut W)) : sSup (PstarSet Y) ≤ ffJ Y := by
  refine sSup_le fun B hB => ?_
  exact le_iSup₂_of_le B hB.1 le_rfl

theorem gomiGstar1_le_sSup_pstarSet (Y : Subgroup (MulAut W)) :
    gomiGstar1 Y ≤ sSup (PstarSet Y) := by
  refine sSup_le fun B hB => ?_
  exact le_sSup hB.1

end Module

section Conjugates

variable {Γ : Type*} [Group Γ] {K K' L S X Y : Subgroup Γ}

theorem le_normalizer_iSup_map_conj (Y L : Subgroup Γ) :
    Y ≤ Subgroup.normalizer
      ((⨆ y ∈ Y, L.map (MulAut.conj y).toMonoidHom : Subgroup Γ) : Set Γ) := by
  intro z hz
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
  refine le_antisymm ?_ ?_
  · rw [Subgroup.map_le_iff_le_comap]
    refine iSup_le fun y => iSup_le fun hy => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    change (L.map (MulAut.conj y).toMonoidHom).map (MulAut.conj z).toMonoidHom ≤ _
    rw [map_conj_map_conj z y L]
    exact le_iSup₂_of_le (z * y) (Y.mul_mem hz hy) le_rfl
  · refine iSup_le fun y => iSup_le fun hy => ?_
    calc L.map (MulAut.conj y).toMonoidHom
        = (L.map (MulAut.conj (z⁻¹ * y)).toMonoidHom).map
            (MulAut.conj z).toMonoidHom := by
          rw [map_conj_map_conj z (z⁻¹ * y) L]
          rw [show z * (z⁻¹ * y) = y by group]
      _ ≤ (⨆ y ∈ Y, L.map (MulAut.conj y).toMonoidHom).map
            (MulAut.conj z).toMonoidHom :=
          Subgroup.map_mono (le_iSup₂_of_le (z⁻¹ * y) (Y.mul_mem (Y.inv_mem hz) hy) le_rfl)

theorem iSup_map_conj_le_normalizer
    (hcomm : ∀ y ∈ Y, L.map (MulAut.conj y).toMonoidHom ≠ L →
      ∀ a ∈ L, ∀ b ∈ L.map (MulAut.conj y).toMonoidHom, a * b = b * a) :
    (⨆ y ∈ Y, L.map (MulAut.conj y).toMonoidHom) ≤ Subgroup.normalizer (L : Set Γ) := by
  refine iSup_le fun y => iSup_le fun hy => ?_
  by_cases h : L.map (MulAut.conj y).toMonoidHom = L
  · rw [h]
    exact Subgroup.le_normalizer
  · rw [Subgroup.le_normalizer_iff]
    intro b hb a ha
    rw [show b * a = a * b from (hcomm y hy h a ha b hb).symm, mul_assoc, mul_inv_cancel,
      mul_one]
    exact ha

private theorem mem_sup_of_le_normalizer {A B : Subgroup Γ}
    (h : A ≤ Subgroup.normalizer (B : Set Γ)) {x : Γ} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right A B h
  have hx' : x ∈ (↑(A ⊔ B) : Set Γ) := hx
  rw [hset] at hx'
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hx'
  exact ⟨a, ha, b, hb, rfl⟩

theorem exists_mem_map_conj_eq (hSY : S ≤ Y)
    (hN : (⨆ y ∈ Y, L.map (MulAut.conj y).toMonoidHom) ≤ Subgroup.normalizer (L : Set Γ))
    (hsup : (⨆ y ∈ Y, L.map (MulAut.conj y).toMonoidHom) ⊔ S = Y) {y : Γ} (hy : y ∈ Y) :
    ∃ s ∈ S, L.map (MulAut.conj y).toMonoidHom = L.map (MulAut.conj s).toMonoidHom := by
  have hSN : S ≤ Subgroup.normalizer
      ((⨆ y ∈ Y, L.map (MulAut.conj y).toMonoidHom : Subgroup Γ) : Set Γ) :=
    hSY.trans (le_normalizer_iSup_map_conj Y L)
  obtain ⟨s, hs, n, hn, rfl⟩ := mem_sup_of_le_normalizer hSN (by rw [sup_comm, hsup]; exact hy)
  refine ⟨s, hs, ?_⟩
  have hnL : L.map (MulAut.conj n).toMonoidHom = L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hN hn)
  rw [← map_conj_map_conj s n L, hnL]

private theorem subgroupOfEquiv_map {H K : Subgroup Γ} (hHK : H ≤ K) (B : Subgroup Γ) :
    (B.subgroupOf H).map (Subgroup.subgroupOfEquivOfLe hHK).symm.toMonoidHom =
      (B.subgroupOf K).subgroupOf (H.subgroupOf K) := by
  ext x
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact hb
  · intro hx
    exact ⟨Subgroup.subgroupOfEquivOfLe hHK x, hx,
      (Subgroup.subgroupOfEquivOfLe hHK).symm_apply_apply x⟩

theorem isComponent_subgroupOf_of_normal (hKX : K ≤ X) (hXY : X ≤ Y)
    (hX : (X.subgroupOf Y).Normal) (hK : CFSG.IsComponent (K.subgroupOf X)) :
    CFSG.IsComponent (K.subgroupOf Y) := by
  have hqK : CFSG.IsQuasisimple ↥K :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKX) hK.1
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe (hKX.trans hXY)).symm hqK, ?_⟩
  have hK'' : ((K.subgroupOf Y).subgroupOf (X.subgroupOf Y)).IsSubnormal := by
    have hmap : ((K.subgroupOf X).map
        (Subgroup.subgroupOfEquivOfLe hXY).symm.toMonoidHom).IsSubnormal :=
      hK.2.map (f := (Subgroup.subgroupOfEquivOfLe hXY).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hXY).symm.surjective
    rwa [subgroupOfEquiv_map hXY K] at hmap
  exact Subgroup.IsSubnormal.trans (fun x hx => hKX hx) hK'' hX.isSubnormal

private theorem subgroupOf_map_normalizerMonoidHom {g : Γ}
    (hg : g ∈ Subgroup.normalizer (X : Set Γ)) (hKX : K ≤ X) :
    (K.subgroupOf X).map (X.normalizerMonoidHom ⟨g, hg⟩).toMonoidHom =
      (K.map (MulAut.conj g).toMonoidHom).subgroupOf X := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    show ↑((X.normalizerMonoidHom ⟨g, hg⟩) y) ∈ K.map (MulAut.conj g).toMonoidHom
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    exact Subgroup.mem_map_of_mem _ hy
  · intro hx
    obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.mp hx
    refine ⟨⟨k, hKX hk⟩, hk, ?_⟩
    apply Subtype.ext
    simp only [MulEquiv.coe_toMonoidHom]
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    simpa only [Subgroup.coe_mk, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply] using hkx

theorem isComponent_map_conj_subgroupOf {g : Γ} (hg : g ∈ Subgroup.normalizer (X : Set Γ))
    (hKX : K ≤ X) (hK : CFSG.IsComponent (K.subgroupOf X)) :
    CFSG.IsComponent ((K.map (MulAut.conj g).toMonoidHom).subgroupOf X) := by
  have hφ : CFSG.IsComponent ((K.subgroupOf X).map
      (X.normalizerMonoidHom ⟨g, hg⟩).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (X.normalizerMonoidHom ⟨g, hg⟩) hK
  rwa [subgroupOf_map_normalizerMonoidHom hg hKX] at hφ

theorem commute_of_isComponent_subgroupOf [Finite Γ] (hKX : K ≤ X) (hK'X : K' ≤ X)
    (hK : CFSG.IsComponent (K.subgroupOf X)) (hK' : CFSG.IsComponent (K'.subgroupOf X))
    (hne : K ≠ K') : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a := by
  rcases CFSG.LocalCores.distinct_components_commute hK hK' with h | h
  · exfalso
    apply hne
    have h' : K ⊓ X = K' ⊓ X := Subgroup.subgroupOf_inj.mp h
    rwa [inf_of_le_left hKX, inf_of_le_left hK'X] at h'
  · intro a ha b hb
    have hc : ⁅(⟨a, hKX ha⟩ : ↥X), (⟨b, hK'X hb⟩ : ↥X)⁆ ∈
        ⁅K.subgroupOf X, K'.subgroupOf X⁆ := Subgroup.commutator_mem_commutator ha hb
    rw [h, Subgroup.mem_bot] at hc
    exact congrArg Subtype.val (commutatorElement_eq_one_iff_mul_comm.mp hc)

end Conjugates

end CFSG.GroupTheory
