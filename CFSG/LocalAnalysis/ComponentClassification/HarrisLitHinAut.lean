module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinBasic
public import CFSG.LocalAnalysis.ComponentInitial.SolvableCoreComponents

public section

namespace CFSG.ComponentClassification.HarrisLit.Hin

open CFSG Subgroup

variable {Y : Type} [Group Y]

theorem conj_apply_eq (τ : MulAut Y) (y : Y) :
    MulAut.conj (τ y) = τ * MulAut.conj y * τ⁻¹ := by
  ext x
  simp [MulAut.conj_apply, MulAut.mul_apply]

theorem conj_injective_of_center (hZ : center Y = ⊥) :
    Function.Injective (MulAut.conj : Y →* MulAut Y) := by
  intro a b hab
  have hc : a⁻¹ * b ∈ center Y := by
    rw [mem_center_iff]
    intro g
    have h1 := congrArg (fun φ : MulAut Y => φ g) hab
    simp only [MulAut.conj_apply] at h1
    calc g * (a⁻¹ * b) = a⁻¹ * (a * g * a⁻¹) * b := by group
      _ = a⁻¹ * (b * g * b⁻¹) * b := by rw [h1]
      _ = a⁻¹ * b * g := by group
  rw [hZ, mem_bot, inv_mul_eq_one] at hc
  exact hc

theorem conj_mem_centralizer_iff (hZ : center Y = ⊥) (τ : MulAut Y) (y : Y) :
    MulAut.conj y ∈ centralizer ({τ} : Set (MulAut Y)) ↔ y ∈ fixedPoints τ := by
  rw [mem_centralizer_singleton_iff, mem_fixedPoints]
  constructor
  · intro h
    have h1 : MulAut.conj (τ y) = MulAut.conj y := by
      rw [conj_apply_eq, ← h, mul_inv_cancel_right]
    exact conj_injective_of_center hZ h1
  · intro h
    have h1 := conj_apply_eq τ y
    rw [h] at h1
    calc MulAut.conj y * τ = (τ * MulAut.conj y * τ⁻¹) * τ := by rw [← h1]
      _ = τ * MulAut.conj y := by group

theorem conj_mem_layerIn [Finite Y] {C : Subgroup Y} {c l : Y} (hc : c ∈ C)
    (hl : l ∈ GSThmB.layerIn C) : c * l * c⁻¹ ∈ GSThmB.layerIn C := by
  obtain ⟨l₀, hl₀, rfl⟩ := Subgroup.mem_map.mp hl
  have := (pLayer_two_normal C).conj_mem l₀ hl₀ ⟨c, hc⟩
  exact ⟨_, this, rfl⟩

theorem isComponentOf_map_conj_layer [Finite Y] (hZ : center Y = ⊥) {τ : MulAut Y} {p m : ℕ}
    (hL : Blueprint.LieModel ↥(GSThmB.layerIn (fixedPoints τ)) .PSL 2 p m) :
    Assembly.IsComponentOf ((GSThmB.layerIn (fixedPoints τ)).map (MulAut.conj : Y →* MulAut Y))
      (centralizer ({τ} : Set (MulAut Y))) := by
  set C := fixedPoints τ
  set L := GSThmB.layerIn C
  set L' := L.map (MulAut.conj : Y →* MulAut Y)
  set W := (MulAut.conj : Y →* MulAut Y).range
  set CA := centralizer ({τ} : Set (MulAut Y))
  have hLC : L ≤ C := map_subtype_le _
  have hL'CA : L' ≤ CA := by
    rintro _ ⟨l, hl, rfl⟩
    exact (conj_mem_centralizer_iff hZ τ l).mpr (hLC hl)
  have hL'W : L' ≤ W := map_le_range _ _
  have hn1 : (L'.subgroupOf (W ⊓ CA)).Normal := by
    rw [normal_subgroupOf_iff (le_inf hL'W hL'CA)]
    rintro _ k ⟨l, hl, rfl⟩ ⟨⟨y, rfl⟩, hy⟩
    have hyC : y ∈ C := (conj_mem_centralizer_iff hZ τ y).mp hy
    refine ⟨y * l * y⁻¹, conj_mem_layerIn hyC hl, ?_⟩
    rw [map_mul, map_mul, map_inv]
  have hn2 : ((W ⊓ CA).subgroupOf CA).Normal := by
    rw [normal_subgroupOf_iff inf_le_right]
    rintro h k ⟨hW, hCA⟩ hk
    exact ⟨(OuterAutomorphisms.inner_normal Y).conj_mem h hW k,
      CA.mul_mem (CA.mul_mem hk hCA) (CA.inv_mem hk)⟩
  have hsn : Assembly.IsSubnormal L' CA :=
    .step (le_inf hL'W hL'CA) hn1 (.step inf_le_right hn2 (.refl CA))
  have hs := isSimpleGroup_pLayer hL
  let eL' : ↥L ≃* ↥L' := L.equivMapOfInjective _ (conj_injective_of_center hZ)
  let e : ↥(pLayer ↥C 2) ≃* ↥L' := (layerInEquiv C).symm.trans eL'
  have hq : IsQuasisimple ↥L' :=
    LocalCores.isQuasisimple_of_mulEquiv e
      (LocalCores.isQuasisimple_of_isSimpleGroup (nonabelian_pLayer hL)).1
  exact ⟨hL'CA, hsn, (AssemblyBPredicates.isQuasisimple_iff_native _).mpr hq⟩

theorem isPComponent_map_conj_layer [Finite Y] (hZ : center Y = ⊥) {τ : MulAut Y} {p m : ℕ}
    (hp2 : p ≠ 2) (hL : Blueprint.LieModel ↥(GSThmB.layerIn (fixedPoints τ)) .PSL 2 p m) :
    IsPComponent 2 (((GSThmB.layerIn (fixedPoints τ)).map (MulAut.conj : Y →* MulAut Y)).subgroupOf
      (centralizer ({τ} : Set (MulAut Y)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut Y) :=
    Finite.of_injective (fun σ : MulAut Y => (σ : Y → Y)) fun a b h => MulEquiv.ext (congrFun h)
  set L' := (GSThmB.layerIn (fixedPoints τ)).map (MulAut.conj : Y →* MulAut Y)
  set CA := centralizer ({τ} : Set (MulAut Y))
  have hcomp := isComponentOf_map_conj_layer hZ hL
  have hK := (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf
    hcomp.1).mp hcomp
  refine LocalAnalysis.ComponentInitial.isPComponent_of_isComponent_of_not_le 2 hK fun hle => ?_
  have hcard : Nat.card ↥(L'.subgroupOf CA) = Nat.card ↥(GSThmB.layerIn (fixedPoints τ)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hcomp.1).toEquiv]
    exact (Nat.card_congr ((GSThmB.layerIn (fixedPoints τ)).equivMapOfInjective _
      (conj_injective_of_center hZ)).toEquiv).symm
  have h2 : 2 ∣ Nat.card ↥(L'.subgroupOf CA) := by
    rw [hcard]
    exact even_iff_two_dvd.mp (even_card_of_lieModel_psl2 hp2 hL)
  have hdvd : Nat.card ↥(L'.subgroupOf CA) ∣ Nat.card ↥(pPrimeCore 2 ↥CA) :=
    Subgroup.card_dvd_of_le hle
  exact Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl (h2.trans hdvd)
    (pPrimeCore_coprime_card (p := 2) (G := ↥CA))

end CFSG.ComponentClassification.HarrisLit.Hin
