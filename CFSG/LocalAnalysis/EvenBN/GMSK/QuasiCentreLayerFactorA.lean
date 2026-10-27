module

public import CFSG.LocalAnalysis.SteinbergBVSp6NonnormalLayer
public import CFSG.LocalAnalysis.EvenBN.GMSK.QuasiCentreProduct

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

open Subgroup CFSG.Blueprint

theorem qcExistsMulOfMemSup {G : Type*} [Group G] {A B : Subgroup G}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let P : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', mul_mem ha ha', b * b', mul_mem hb hb', ?_⟩
        rw [mul_assoc, ← mul_assoc b, ← hAB a' ha' b hb]
        group
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by rw [mul_one]⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, inv_mem ha, b⁻¹, inv_mem hb, ?_⟩
        rw [mul_inv_rev, ← hAB a⁻¹ (inv_mem ha) b⁻¹ (inv_mem hb)] }
  have hle : A ⊔ B ≤ P := sup_le (fun a ha => ⟨a, ha, 1, one_mem _, by rw [mul_one]⟩)
    (fun b hb => ⟨1, one_mem _, b, hb, by rw [one_mul]⟩)
  exact hle hx

theorem quasi_layer_le_pair {H : Type} [Group H] [Finite H]
    (hF : CFSG.fittingSubgroup H = ⊥) {J : Subgroup H} (hJq : CFSG.Open.IsQuasisimple ↥J)
    {a : H} (ha : orderOf a = 2) (haJ : a ∈ centralizer (J : Set H))
    (hJn : (J.subgroupOf (centralizer ({a} : Set H))).Normal) (hJE : J ≤ CFSG.layer H) :
    ∃ K : Subgroup H, CFSG.IsComponent K ∧ J ≤ K ⊔ K.map (MulAut.conj a).toMonoidHom := by
  classical
  have hZE := CFSG.LocalAnalysis.SteinbergBV.OneOrTwoLayer.center_layer_eq_bot hF
  have hJq' : CFSG.IsQuasisimple ↥J :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1 hJq
  have hJa : J ≤ centralizer ({a} : Set H) := fun j hj =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 haJ j hj)
  have ha2 : a * a = 1 := by
    have h := pow_orderOf_eq_one a
    rw [ha, pow_two] at h
    exact h
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  haveI : (CFSG.layer H).Characteristic := CFSG.LocalCores.layer_characteristic
  obtain ⟨K, hK, hJK⟩ : ∃ K : Subgroup H, CFSG.IsComponent K ∧ ¬ J ≤ centralizer (K : Set H) := by
    by_contra hcon
    push_neg at hcon
    haveI : Nontrivial J := CFSG.LocalCores.isQuasisimple_nontrivial hJq'
    obtain ⟨j, hj⟩ := exists_ne (1 : J)
    apply hj
    have hlay : CFSG.layer H ≤ centralizer (J : Set H) := by
      rw [CFSG.layer.eq_sSup]
      exact sSup_le fun L hL => le_centralizer_iff.1 (hcon L hL)
    have hJlay : J ≤ centralizer (CFSG.layer H : Set H) := le_centralizer_iff.2 hlay
    have hmem : (j : H) ∈ (center (CFSG.layer H)).map (CFSG.layer H).subtype :=
      (CFSG.LocalCores.mem_map_center_iff (CFSG.layer H)).2 ⟨hJE j.2, hJlay j.2⟩
    rw [hZE, mem_bot] at hmem
    exact Subtype.ext hmem
  set φ : H →* H := (MulAut.conj a).toMonoidHom
  have hφapp : ∀ x : H, φ x = a * x * a⁻¹ := fun x => rfl
  have hφφ : ∀ x : H, φ (φ x) = x := by
    intro x
    rw [hφapp, hφapp, hainv]
    calc a * (a * x * a) * a = (a * a) * x * (a * a) := by group
      _ = x := by rw [ha2]; group
  have hK₁c : CFSG.IsComponent (K.map φ) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj a) hK
  have hK₁φ : (K.map φ).map φ = K := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      rw [hφφ z]
      exact hz
    · intro hx
      exact ⟨φ x, ⟨x, hx, rfl⟩, hφφ x⟩
  set W : Subgroup H := K ⊔ K.map φ with hW
  set Y : Subgroup H := centralizer (W : Set H) ⊓ CFSG.layer H
  have hcomp : ∀ L : Subgroup H, CFSG.IsComponent L →
      L ≤ W ∨ L ≤ centralizer (W : Set H) := by
    intro L hL
    rcases CFSG.LocalCores.distinct_components_commute hL hK with hLK | hLK
    · exact Or.inl (by rw [hLK]; exact le_sup_left)
    · rcases CFSG.LocalCores.distinct_components_commute hL hK₁c with hLK₁ | hLK₁
      · exact Or.inl (by rw [hLK₁]; exact le_sup_right)
      · right
        exact le_centralizer_iff.1 (sup_le
          (le_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 hLK))
          (le_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 hLK₁)))
  have hWY : ∀ w ∈ W, ∀ y ∈ Y, w * y = y * w := fun w hw y hy =>
    mem_centralizer_iff.1 hy.1 w hw
  have hdisj : W ⊓ Y = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxW, hxC, hxE⟩ := hx
    have hxcent : CFSG.layer H ≤ centralizer ({x} : Set H) := by
      rw [CFSG.layer.eq_sSup]
      refine sSup_le fun L hL l hl => ?_
      rw [mem_centralizer_singleton_iff]
      rcases hcomp L hL with hLW | hLC
      · exact mem_centralizer_iff.1 hxC l (hLW hl)
      · exact (mem_centralizer_iff.1 (hLC hl) x hxW).symm
    have hmem : x ∈ (center (CFSG.layer H)).map (CFSG.layer H).subtype :=
      (CFSG.LocalCores.mem_map_center_iff (CFSG.layer H)).2 ⟨hxE, mem_centralizer_iff.2 fun l hl =>
        mem_centralizer_singleton_iff.1 (hxcent hl)⟩
    rw [hZE] at hmem
    exact hmem
  have hWφ : W.map φ ≤ W := by
    rw [hW, Subgroup.map_sup, hK₁φ]
    exact sup_le le_sup_right le_sup_left
  have haW : ∀ w ∈ W, a * w * a⁻¹ ∈ W := fun w hw => hWφ ⟨w, hw, rfl⟩
  have haY : ∀ y ∈ Y, a * y * a⁻¹ ∈ Y := by
    intro y hy
    have hyC : a * y * a⁻¹ ∈ centralizer (W : Set H) := by
      rw [mem_centralizer_iff]
      intro w hw
      have hw' : a⁻¹ * w * a ∈ W := by
        have := haW w hw
        rwa [hainv] at this ⊢
      have hc := mem_centralizer_iff.1 hy.1 _ hw'
      calc w * (a * y * a⁻¹) = a * ((a⁻¹ * w * a) * y) * a⁻¹ := by group
        _ = a * (y * (a⁻¹ * w * a)) * a⁻¹ := by rw [hc]
        _ = (a * y * a⁻¹) * w := by group
    exact ⟨hyC, (inferInstance : (CFSG.layer H).Normal).conj_mem y hy.2 a⟩
  have hlayWY : CFSG.layer H ≤ W ⊔ Y := by
    rw [CFSG.layer.eq_sSup]
    refine sSup_le fun L hL => ?_
    rcases hcomp L hL with hLW | hLC
    · exact hLW.trans le_sup_left
    · exact le_sup_of_le_right (le_inf hLC (CFSG.LocalCores.component_le_layer hL))
  have hJWY : ∀ j ∈ J, ∃ w ∈ W, ∃ y ∈ Y, j = w * y := fun j hj =>
    qcExistsMulOfMemSup hWY (hlayWY (hJE hj))
  have hJn' : ∀ c ∈ centralizer ({a} : Set H), ∀ j ∈ J, c * j * c⁻¹ ∈ J := by
    intro c hc j hj
    have := hJn.conj_mem ⟨j, hJa hj⟩ (mem_subgroupOf.mpr hj) ⟨c, hc⟩
    exact mem_subgroupOf.mp this
  have hJW : ¬ J ≤ centralizer (W : Set H) := fun h =>
    hJK (h.trans (centralizer_le (SetLike.coe_subset_coe.2 le_sup_left)))
  exact ⟨K, hK, quasisimple_le_of_product hWY hdisj haW haY hJq' hJa hJWY hJn' hJW⟩

end CFSG.LocalAnalysis.EvenBN.GMSK
