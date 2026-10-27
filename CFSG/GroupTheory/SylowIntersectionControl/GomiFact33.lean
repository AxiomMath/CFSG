module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsGF2
import CFSG.GroupTheory.SylowIntersectionControl.GomiFact33Fitting
import CFSG.GroupTheory.SylowIntersectionControl.GomiFact33Transvection
import CFSG.GroupTheory.SylowIntersectionControl.GomiFact33Offender
import CFSG.GroupTheory.SylowIntersectionControl.GomiGstar

public section

namespace CFSG.GroupTheory

open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719 (O2Trivial)

variable {W : Type} [CommGroup W]

private theorem gomiGstar1_map_conj {Y : Subgroup (MulAut W)} {g : MulAut W} (hg : g ∈ Y) :
    (gomiGstar1 Y).map (MulAut.conj g).toMonoidHom = gomiGstar1 Y :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (gomiGstar1_le Y)).mp
      (gomiGstar1_subgroupOf_normal Y) hg)

private theorem conj_mem_map_subtype_of_characteristic {G : Type*} [Group G] {H : Subgroup G}
    {g : G} (hg : H.map (MulAut.conj g).toMonoidHom = H) (K : Subgroup H) [K.Characteristic]
    {x : G} (hx : x ∈ K.map H.subtype) : g * x * g⁻¹ ∈ K.map H.subtype := by
  obtain ⟨k, hk, rfl⟩ := hx
  let φ : H ≃* H :=
    (MulEquiv.subgroupMap (MulAut.conj g) H).trans (MulEquiv.subgroupCongr hg)
  have hk' : φ k ∈ K := by
    rw [← (inferInstance : K.Characteristic).fixed φ] at hk
    exact hk
  exact ⟨φ k, hk', rfl⟩

private theorem conj_mem_pPrimeCore_gomiGstar1 {Y : Subgroup (MulAut W)} {g x : MulAut W}
    (hg : g ∈ Y) (hx : x ∈ (CFSG.pPrimeCore 2 ↥(gomiGstar1 Y)).map (gomiGstar1 Y).subtype) :
    g * x * g⁻¹ ∈ (CFSG.pPrimeCore 2 ↥(gomiGstar1 Y)).map (gomiGstar1 Y).subtype :=
  conj_mem_map_subtype_of_characteristic (gomiGstar1_map_conj hg) _ hx

private theorem le_centralizer_pPrimeCore [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y A : Subgroup (MulAut W)} (hA : A ∈ gomiPstar1Set Y) :
    A ≤ Subgroup.centralizer
      ((CFSG.pPrimeCore 2 ↥(gomiGstar1 Y)).map (gomiGstar1 Y).subtype : Set (MulAut W)) := by
  set R := (CFSG.pPrimeCore 2 ↥(gomiGstar1 Y)).map (gomiGstar1 Y).subtype with hRdef
  have : Finite (MulAut W) := MulEquiv.finite_left
  have hR : Odd (Nat.card R) := by
    rw [hRdef, Subgroup.card_map_of_injective (gomiGstar1 Y).subtype_injective,
      ← Nat.coprime_two_left]
    exact CFSG.pPrimeCore_coprime_card (p := 2)
  have hRY : R ≤ Y := (Subgroup.map_subtype_le _).trans (gomiGstar1_le Y)
  have hRn : (R.subgroupOf Y).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact conj_mem_pPrimeCore_gomiGstar1 g.2 hn⟩
  have hAY : A ≤ Y := hA.1.1.1
  have hAR : A ≤ Subgroup.normalizer (R : Set (MulAut W)) := fun a ha =>
    Subgroup.mem_normalizer_iff.2 fun h => ⟨fun hh => conj_mem_pPrimeCore_gomiGstar1 (hAY ha) hh,
      fun hh => by
        have := conj_mem_pPrimeCore_gomiGstar1 (Y.inv_mem (hAY ha)) hh
        simpa only [mul_assoc, inv_inv, inv_mul_cancel, mul_one, inv_mul_cancel_left] using this⟩
  by_contra hnc
  obtain ⟨a, u, rfl, ha⟩ := exists_isTransv_of_mem_pstarSet hW hA.1 hR hAR hnc
  have haY : a ∈ Y := hAY (Subgroup.mem_zpowers a)
  have hna : a ∉ Subgroup.centralizer (R : Set (MulAut W)) := fun h =>
    hnc ((Subgroup.zpowers_le).2 h)
  have hO := mem_inSubgroup_pPrimePCore_of_isTransv hW ha haY hRY hRn hR hna
  exact hA.2 ⟨hA.1, (Subgroup.zpowers_le).2 hO⟩

private theorem pPrimeCore_le_center [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    (Y : Subgroup (MulAut W)) :
    CFSG.pPrimeCore 2 ↥(gomiGstar1 Y) ≤ Subgroup.center ↥(gomiGstar1 Y) := by
  intro k hk
  rw [Subgroup.mem_center_iff]
  intro z
  have hz : (z : MulAut W) ∈ Subgroup.centralizer
      ((CFSG.pPrimeCore 2 ↥(gomiGstar1 Y)).map (gomiGstar1 Y).subtype : Set (MulAut W)) :=
    sSup_le (fun _ hA => le_centralizer_pPrimeCore hW hA) z.2
  exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hz _ ⟨k, hk, rfl⟩).symm

private theorem pCore_eq_bot_of_o2Trivial {H : Subgroup (MulAut W)} (hO2 : O2Trivial H) :
    CFSG.pCore 2 ↥H = ⊥ := by
  have h := hO2 ((CFSG.pCore 2 ↥H).map H.subtype) (Subgroup.map_subtype_le _)
    (by
      rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
      infer_instance)
    (CFSG.pCore_isPGroup.map H.subtype)
  exact (Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective).1 h

private theorem even_card_gomiGstar1 [Finite W] {Y : Subgroup (MulAut W)}
    (hne : (gomiPstar1Set Y).Nonempty) : Even (Nat.card ↥(gomiGstar1 Y)) := by
  have : Finite (MulAut W) := MulEquiv.finite_left
  obtain ⟨A, hA⟩ := hne
  obtain ⟨⟨a, haA⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hA.1.1.2.1
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hoa : orderOf a = 2 := orderOf_eq_prime (hA.1.1.2.2.1.2 a haA) ha1'
  have haH : a ∈ gomiGstar1 Y := le_sSup hA haA
  rw [even_iff_two_dvd, ← hoa, ← Subgroup.orderOf_mk a haH]
  exact orderOf_dvd_natCard _

theorem gomiFact33_holds : GomiFact33 := by
  intro W _ _ hW Y hne hO2
  have : Finite (MulAut W) := MulEquiv.finite_left
  exact layer_ne_bot_and_of_pPrimeCore_le_center (pCore_eq_bot_of_o2Trivial hO2)
    (pPrimeCore_le_center hW Y) (even_card_gomiGstar1 hne)

end CFSG.GroupTheory
