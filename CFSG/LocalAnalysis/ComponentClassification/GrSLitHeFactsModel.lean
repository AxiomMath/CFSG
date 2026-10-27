module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeLayerModel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixTwoBCent
public import CFSG.LocalAnalysis.ComponentInitial.PerfectFixedCentralQuotient
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeTransport

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier
  CFSG.ComponentClassification.UnbalancedGS

@[expose] noncomputable def heK0 : Subgroup (Equiv.Perm (Fin 8330)) :=
  gsFixedLayer heP (heGenPerm 0)

@[expose] noncomputable def heZ0 : Subgroup (Equiv.Perm (Fin 8330)) :=
  (center ↥heK0).map heK0.subtype

@[expose] def HeldTwoBTwelveModel : Prop :=
  ∃ x ∈ centralizerIn heP heT1P, x ^ 12 = 1 ∧
    ∃ w₁ ∈ centralizerIn heP heT1P, ∃ w₂ ∈ centralizerIn heP heT1P,
      w₁ ∈ conjClass heP (heGenPerm 0) ∧ w₂ ∈ conjClass heP (heGenPerm 0) ∧
      (∀ N : Subgroup (Equiv.Perm (Fin 8330)), N ≤ centralizerIn heP heT1P →
        (N.subgroupOf (centralizerIn heP heT1P)).Normal → (x ^ 4 ∈ N ∨ x ^ 3 ∈ N) →
        w₁ ∈ N ∧ w₂ ∈ N) ∧
      heT1P ∉ centralizer (gsFixedLayer heP w₁ : Set (Equiv.Perm (Fin 8330))) ∧
      heT1P ∉ centralizer (gsFixedLayer heP w₂ : Set (Equiv.Perm (Fin 8330))) ∧
      gsFixedLayer heP w₁ ⊔ gsFixedLayer heP w₂ = heP

@[expose] def HeldTwoAFourModel : Prop :=
  ∃ y₁ ∈ heK0, ∃ y₂ ∈ heK0, y₁ * y₁ = 1 ∧ y₂ * y₂ = 1 ∧ y₁ ≠ 1 ∧ y₂ ≠ 1 ∧ y₁ ≠ y₂ ∧
    y₁ * y₂ = y₂ * y₁

@[expose] def HeldTwoAPairModel : Prop :=
  ∃ w ∈ heK0, w ∈ conjClass heP (heGenPerm 0) ∧ w ∉ heZ0 ∧ heGenPerm 0 * w ∉ heZ0

@[expose] def HeldTwoAGenerationModel : Prop :=
  ∀ w ∈ heK0, w ∈ conjClass heP (heGenPerm 0) → w ∉ heZ0 → heGenPerm 0 * w ∉ heZ0 →
    heK0 ⊔ gsFixedLayer heP w = heP

namespace HeFM

variable {X : Type} [Group X] [Finite X] {L : Subgroup X}

omit [Finite X] in
theorem mem_center_trS_iff {X' : Type} [Group X'] {L' : Subgroup X'} (φ : ↥L ≃* ↥L')
    {A : Subgroup X} (hA : A ≤ L) (x : ↥L) :
    (φ x : X') ∈ (center ↥(HeT.trS φ A)).map (HeT.trS φ A).subtype ↔
      (x : X) ∈ (center ↥A).map A.subtype := by
  rw [LocalAnalysis.ComponentInitial.mem_map_center_iff,
    LocalAnalysis.ComponentInitial.mem_map_center_iff]
  constructor
  · rintro ⟨hx, hc⟩
    refine ⟨HeT.mem_of_mem_trS φ hx, fun e he => ?_⟩
    have h1 := hc _ (HeT.mem_trS_of_mem φ (x := ⟨e, hA he⟩) he)
    have h2 : φ ⟨e, hA he⟩ * φ x = φ x * φ ⟨e, hA he⟩ := Subtype.ext h1
    rw [← map_mul, ← map_mul] at h2
    exact congrArg Subtype.val (φ.injective h2)
  · rintro ⟨hx, hc⟩
    refine ⟨HeT.mem_trS_of_mem φ hx, fun e he => ?_⟩
    obtain ⟨y, hy, rfl⟩ := (HeT.mem_trS φ).mp he
    have h1 : y * x = x * y := Subtype.ext (hc _ hy)
    rw [← coe_mul, ← coe_mul, ← map_mul, ← map_mul, h1]

@[expose] noncomputable def conjP (c : ↥heP) : ↥heP ≃* ↥heP := MulAut.conj c

theorem orderOf_of_mem_conjClass
    {p : Equiv.Perm (Fin 8330)}
    (hp : p ∈ conjClass heP (heGenPerm 0)) : orderOf p = 2 := by
  obtain ⟨c, -, rfl⟩ := hp
  rw [orderOf_conj_eq, orderOf_heA0]


@[expose] noncomputable def toP (e : ↥L ≃* Blueprint.NativeSporadic.He) : ↥L ≃* ↥heP :=
  e.trans heEquivP


theorem exists_equiv_t0 (e : ↥L ≃* Blueprint.NativeSporadic.He) {u : X} (hu : HeldTwoA L u) :
    ∃ φ : ↥L ≃* ↥heP, (φ ⟨u, hu.1⟩ : Equiv.Perm (Fin 8330)) = heGenPerm 0 := by
  have hu' : HeldTwoA heP (toP e ⟨u, hu.1⟩ : Equiv.Perm (Fin 8330)) :=
    (HeT.heldTwoA_iff (toP e) hu.1).mpr hu
  obtain ⟨c, hc, hcu⟩ := (HeLay.heldTwoA_heP_iff (toP e _).2 hu'.2.1).mp hu'
  refine ⟨(toP e).trans (conjP ⟨c, hc⟩⁻¹), ?_⟩
  change (⟨c, hc⟩⁻¹ * toP e ⟨u, hu.1⟩ * (⟨c, hc⟩⁻¹)⁻¹ : ↥heP).1 = heGenPerm 0
  simp only [coe_mul, coe_inv, inv_inv, hcu]
  group

theorem exists_equiv_t1 (e : ↥L ≃* Blueprint.NativeSporadic.He) {v : X} (hvL : v ∈ L)
    (hv : orderOf v = 2) (hv0 : gsFixedLayer L v = ⊥) :
    ∃ φ : ↥L ≃* ↥heP, (φ ⟨v, hvL⟩ : Equiv.Perm (Fin 8330)) = heT1P := by
  have hord : orderOf (toP e ⟨v, hvL⟩ : Equiv.Perm (Fin 8330)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hv]
  have hnot : ¬ HeldTwoA heP (toP e ⟨v, hvL⟩ : Equiv.Perm (Fin 8330)) := fun h =>
    ((HeT.heldTwoA_iff (toP e) hvL).mp h).2.2 hv0
  rcases involution_conj_cases (toP e ⟨v, hvL⟩).2 hord with h | ⟨c, hc, hcv⟩
  · exact (hnot ((HeLay.heldTwoA_heP_iff (toP e _).2 hord).mpr h)).elim
  · refine ⟨(toP e).trans (conjP ⟨c, hc⟩⁻¹), ?_⟩
    change (⟨c, hc⟩⁻¹ * toP e ⟨v, hvL⟩ * (⟨c, hc⟩⁻¹)⁻¹ : ↥heP).1 = heT1P
    simp only [coe_mul, coe_inv, inv_inv, hcv]
    group

end HeFM

open HeFM


theorem heldTwoAClassFact : HeldTwoAClassFact := by
  intro X _ _ L ⟨e⟩ u w hu hw
  have hu' := (HeT.heldTwoA_iff (toP e) hu.1).mpr hu
  have hw' := (HeT.heldTwoA_iff (toP e) hw.1).mpr hw
  obtain ⟨c, hc, hcu⟩ := (HeLay.heldTwoA_heP_iff (toP e _).2 hu'.2.1).mp hu'
  obtain ⟨d, hd, hdw⟩ := (HeLay.heldTwoA_heP_iff (toP e _).2 hw'.2.1).mp hw'
  set g : ↥heP := ⟨d * c⁻¹, mul_mem hd (inv_mem hc)⟩ with hg
  refine ⟨((toP e).symm g : X), ((toP e).symm g).2, ?_⟩
  have h1 : toP e ⟨w, hw.1⟩ = g * toP e ⟨u, hu.1⟩ * g⁻¹ := by
    apply Subtype.ext
    simp only [coe_mul, coe_inv, hg, hdw, hcu]
    group
  have h2 : (⟨w, hw.1⟩ : ↥L) = (toP e).symm g * ⟨u, hu.1⟩ * ((toP e).symm g)⁻¹ := by
    apply (toP e).injective
    rw [h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  exact congrArg Subtype.val h2

theorem heldTwoALayerFact : HeldTwoALayerFact := by
  intro X _ _ L ⟨e⟩ u hu
  obtain ⟨φ, hφ⟩ := exists_equiv_t0 e hu
  have hK := HeT.trS_gsFixedLayer φ hu.1
  rw [hφ] at hK
  obtain ⟨-, hp, ht⟩ := HeLay.gsFixedLayer_t0
  let ι : ↥(gsFixedLayer L u) ≃* ↥(gsFixedLayer heP (heGenPerm 0)) :=
    (HeT.trEquiv φ ((gsFixedLayer_le_inf L u).trans inf_le_left)).trans
      (MulEquiv.subgroupCongr hK)
  refine ⟨?_, LieType.CurtisTits.lieModel_of_mulEquiv (Sol78.centerQuotCongr ι).symm ht⟩
  have : Group.IsPerfect ↥(gsFixedLayer heP (heGenPerm 0)) := isPerfect_iff.mpr hp
  exact isPerfect_iff.mp (Group.IsPerfect.ofSurjective (f := ι.symm.toMonoidHom)
    ι.symm.surjective)

theorem heldTwoBCentralizerFact_of_model
    (hM : HeldTwoBTwelveModel) : HeldTwoBCentralizerFact := by
  intro X _ _ L ⟨e⟩ v hvL hv hv0
  obtain ⟨φ, hφ⟩ := exists_equiv_t1 e hvL hv hv0
  have hC0 := HeT.trS_inf_centralizer φ hvL
  rw [hφ] at hC0
  have hC : HeT.trS φ (L ⊓ centralizer ({v} : Set X)) = centralizerIn heP heT1P := hC0
  let χ : ↥(L ⊓ centralizer ({v} : Set X)) ≃* ↥(centralizerIn heP heT1P) :=
    (HeT.trEquiv φ inf_le_left).trans (MulEquiv.subgroupCongr hC)
  obtain ⟨hperf, -⟩ := heldTwoBCentralizerStructure
  obtain ⟨x₀, hx₀C, hx₀12, w₁, hw₁C, w₂, hw₂C, hw₁c, hw₂c, hN, hv₁, hv₂, hgen⟩ := hM
  have hpre : ∀ p ∈ centralizerIn heP heT1P, ∃ y : ↥L,
      (y : X) ∈ L ⊓ centralizer ({v} : Set X) ∧ (φ y : Equiv.Perm (Fin 8330)) = p := by
    intro p hp
    rw [← hC] at hp
    exact (HeT.mem_trS φ).mp hp
  obtain ⟨y, hyH, hyφ⟩ := hpre x₀ hx₀C
  obtain ⟨z₁, hz₁H, hz₁φ⟩ := hpre w₁ hw₁C
  obtain ⟨z₂, hz₂H, hz₂φ⟩ := hpre w₂ hw₂C
  have hpowφ : ∀ n : ℕ, (φ (y ^ n) : Equiv.Perm (Fin 8330)) = x₀ ^ n := by
    intro n
    rw [map_pow, coe_pow, hyφ]
  have hA : ∀ (z : ↥L) (w : Equiv.Perm (Fin 8330)), (φ z : Equiv.Perm (Fin 8330)) = w →
      w ∈ conjClass heP (heGenPerm 0) → HeldTwoA L z := by
    intro z w hzw hwc
    refine (HeT.heldTwoA_iff φ z.2).mp ?_
    rw [hzw] at ⊢
    exact (HeLay.heldTwoA_heP_iff (hzw ▸ (φ z).2) (orderOf_of_mem_conjClass hwc)).mpr hwc
  have hK : ∀ (z : ↥L) (w : Equiv.Perm (Fin 8330)), (φ z : Equiv.Perm (Fin 8330)) = w →
      heT1P ∉ centralizer (gsFixedLayer heP w : Set (Equiv.Perm (Fin 8330))) →
      v ∉ centralizer (gsFixedLayer L z : Set X) := by
    intro z w hzw hw hvc
    apply hw
    have hKz := HeT.trS_gsFixedLayer φ z.2
    rw [show (⟨(z : X), z.2⟩ : ↥L) = z from rfl, hzw] at hKz
    rw [← hKz, mem_centralizer_iff]
    intro a ha
    obtain ⟨b, hb, rfl⟩ := (HeT.mem_trS φ).mp ha
    have h1 : b * ⟨v, hvL⟩ = ⟨v, hvL⟩ * b := Subtype.ext (mem_centralizer_iff.mp hvc _ hb)
    rw [← hφ, ← coe_mul, ← coe_mul, ← map_mul, ← map_mul, h1]
  refine ⟨?_, (y : X), hyH, ?_, (z₁ : X), hz₁H, (z₂ : X), hz₂H, hA z₁ w₁ hz₁φ hw₁c,
    hA z₂ w₂ hz₂φ hw₂c, ?_, hK z₁ w₁ hz₁φ hv₁, hK z₂ w₂ hz₂φ hv₂, ?_⟩
  · have : Group.IsPerfect ↥(centralizerIn heP heT1P) := isPerfect_iff.mpr hperf
    exact isPerfect_iff.mp (Group.IsPerfect.ofSurjective (f := χ.symm.toMonoidHom)
      χ.symm.surjective)
  · have h1 : φ (y ^ 12) = 1 := Subtype.ext (by rw [hpowφ, hx₀12, coe_one])
    rw [MulEquiv.map_eq_one_iff] at h1
    rw [← coe_pow, h1, coe_one]
  · intro N hNle hNn hyN
    have hN'le : HeT.trS φ N ≤ centralizerIn heP heT1P := by
      rw [← hC]
      exact HeT.trS_mono φ hNle
    have hN'n : ((HeT.trS φ N).subgroupOf (centralizerIn heP heT1P)).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [mem_subgroupOf] at hn ⊢
      obtain ⟨x, hx, hxe⟩ := (HeT.mem_trS φ).mp hn
      have hg : (g : Equiv.Perm (Fin 8330)) ∈ HeT.trS φ (L ⊓ centralizer ({v} : Set X)) := by
        rw [hC]; exact g.2
      obtain ⟨z, hz, hze⟩ := (HeT.mem_trS φ).mp hg
      have h1 := hNn.conj_mem ⟨x, hNle hx⟩ (mem_subgroupOf.mpr hx) ⟨z, hz⟩
      rw [mem_subgroupOf] at h1
      have h2 := HeT.mem_trS_of_mem φ (x := z * x * z⁻¹) h1
      rw [map_mul, map_mul, map_inv] at h2
      simp only [coe_mul, coe_inv] at h2 ⊢
      rwa [hxe, hze] at h2
    have hmem : ∀ n : ℕ, (y : X) ^ n ∈ N → x₀ ^ n ∈ HeT.trS φ N := by
      intro n hn
      rw [← hpowφ n]
      exact HeT.mem_trS_of_mem φ (x := y ^ n) (by rw [coe_pow]; exact hn)
    obtain ⟨h1, h2⟩ := hN _ hN'le hN'n (hyN.imp (hmem 4) (hmem 3))
    exact ⟨HeT.mem_of_mem_trS φ (hz₁φ ▸ h1), HeT.mem_of_mem_trS φ (hz₂φ ▸ h2)⟩
  · have hKle : ∀ z : ↥L, gsFixedLayer L z ≤ L := fun z =>
      (gsFixedLayer_le_inf L z).trans inf_le_left
    apply HeT.trS_injective φ (sup_le (hKle z₁) (hKle z₂)) le_rfl
    rw [HeT.trS_sup φ (hKle z₁) (hKle z₂), HeT.trS_gsFixedLayer φ z₁.2,
      HeT.trS_gsFixedLayer φ z₂.2, HeT.trS_self]
    rw [show (⟨(z₁ : X), z₁.2⟩ : ↥L) = z₁ from rfl, show (⟨(z₂ : X), z₂.2⟩ : ↥L) = z₂ from rfl,
      hz₁φ, hz₂φ]
    exact hgen

theorem heldTwoAFourFact_of_model (hM : HeldTwoAFourModel) : HeldTwoAFourFact := by
  intro X _ _ L ⟨e⟩ u hu
  obtain ⟨φ, hφ⟩ := exists_equiv_t0 e hu
  have hK : HeT.trS φ (gsFixedLayer L u) = heK0 := by
    rw [HeT.trS_gsFixedLayer φ hu.1, hφ]
    rfl
  obtain ⟨y₁, hy₁, y₂, hy₂, h1, h2, h3, h4, h5, h6⟩ := hM
  rw [← hK] at hy₁ hy₂
  obtain ⟨a, ha, rfl⟩ := (HeT.mem_trS φ).mp hy₁
  obtain ⟨b, hb, rfl⟩ := (HeT.mem_trS φ).mp hy₂
  have hsq : ∀ c : ↥L, (φ c : Equiv.Perm (Fin 8330)) * φ c = 1 → (c : X) * c = 1 := by
    intro c hc
    have h : φ (c * c) = 1 := Subtype.ext (by rw [map_mul, coe_mul, coe_one]; exact hc)
    rw [MulEquiv.map_eq_one_iff] at h
    rw [← coe_mul, h, coe_one]
  have hne1 : ∀ c : ↥L, (φ c : Equiv.Perm (Fin 8330)) ≠ 1 → (c : X) ≠ 1 := by
    intro c hc h
    apply hc
    rw [show c = 1 from Subtype.ext h, map_one, coe_one]
  refine ⟨a, ha, b, hb, hsq a h1, hsq b h2, hne1 a h3, hne1 b h4, fun h => h5 ?_, ?_⟩
  · rw [show a = b from Subtype.ext h]
  · have h : φ (a * b) = φ (b * a) := Subtype.ext (by rw [map_mul, map_mul, coe_mul, coe_mul, h6])
    rw [← coe_mul, ← coe_mul, φ.injective h]

theorem heldTwoAPairFact_of_model (hM : HeldTwoAPairModel) : HeldTwoAPairFact := by
  intro X _ _ L ⟨e⟩ u hu
  obtain ⟨φ, hφ⟩ := exists_equiv_t0 e hu
  have hKle : gsFixedLayer L u ≤ L := (gsFixedLayer_le_inf L u).trans inf_le_left
  have hK : HeT.trS φ (gsFixedLayer L u) = heK0 := by
    rw [HeT.trS_gsFixedLayer φ hu.1, hφ]
    rfl
  obtain ⟨w₀, hw₀K, hw₀c, hw₀Z, hw₀uZ⟩ := hM
  rw [← hK] at hw₀K
  obtain ⟨x, hxK, hxe⟩ := (HeT.mem_trS φ).mp hw₀K
  have hZ : ∀ y : ↥L, (φ y : Equiv.Perm (Fin 8330)) ∈ heZ0 ↔
      (y : X) ∈ (center ↥(gsFixedLayer L u)).map (gsFixedLayer L u).subtype := by
    intro y
    rw [← mem_center_trS_iff φ hKle y, hK]
    rfl
  refine ⟨x, hxK, ?_, fun h => hw₀Z (hxe ▸ (hZ x).mpr h), fun h => hw₀uZ ?_⟩
  · apply (HeT.heldTwoA_iff φ x.2).mp
    rw [hxe]
    exact (HeLay.heldTwoA_heP_iff (heP.mem_carrier.mpr (by
      obtain ⟨c, hc, rfl⟩ := hw₀c
      exact mul_mem (mul_mem hc (heGenPerm_mem (by norm_num))) (inv_mem hc)))
      (orderOf_of_mem_conjClass hw₀c)).mpr hw₀c
  · have h1 := (hZ (⟨u, hu.1⟩ * x)).mpr h
    rwa [map_mul, coe_mul, hφ, hxe] at h1

theorem heldTwoAGenerationFact_of_model (hM : HeldTwoAGenerationModel) :
    HeldTwoAGenerationFact := by
  intro X _ _ L ⟨e⟩ u w hu hw hwK hwZ huwZ
  obtain ⟨φ, hφ⟩ := exists_equiv_t0 e hu
  have hKle : gsFixedLayer L u ≤ L := (gsFixedLayer_le_inf L u).trans inf_le_left
  have hKwle : gsFixedLayer L w ≤ L := (gsFixedLayer_le_inf L w).trans inf_le_left
  have hK : HeT.trS φ (gsFixedLayer L u) = heK0 := by
    rw [HeT.trS_gsFixedLayer φ hu.1, hφ]
    rfl
  have hZ : ∀ y : ↥L, (φ y : Equiv.Perm (Fin 8330)) ∈ heZ0 ↔
      (y : X) ∈ (center ↥(gsFixedLayer L u)).map (gsFixedLayer L u).subtype := by
    intro y
    rw [← mem_center_trS_iff φ hKle y, hK]
    rfl
  have hw₀K : (φ ⟨w, hw.1⟩ : Equiv.Perm (Fin 8330)) ∈ heK0 := by
    rw [← hK]
    exact HeT.mem_trS_of_mem φ hwK
  have hw₀A := (HeT.heldTwoA_iff φ hw.1).mpr hw
  have hw₀c := (HeLay.heldTwoA_heP_iff (φ _).2 hw₀A.2.1).mp hw₀A
  have hw₀Z : (φ ⟨w, hw.1⟩ : Equiv.Perm (Fin 8330)) ∉ heZ0 := fun h => hwZ ((hZ _).mp h)
  have hw₀uZ : heGenPerm 0 * (φ ⟨w, hw.1⟩ : Equiv.Perm (Fin 8330)) ∉ heZ0 := by
    intro h
    apply huwZ
    have h1 : (φ (⟨u, hu.1⟩ * ⟨w, hw.1⟩) : Equiv.Perm (Fin 8330)) ∈ heZ0 := by
      rw [map_mul, coe_mul, hφ]
      exact h
    exact (hZ _).mp h1
  have hgen := hM _ hw₀K hw₀c hw₀Z hw₀uZ
  apply HeT.trS_injective φ (sup_le hKle hKwle) le_rfl
  rw [HeT.trS_sup φ hKle hKwle, hK, HeT.trS_gsFixedLayer φ hw.1, HeT.trS_self]
  exact hgen

end CFSG.ComponentClassification.GrSLit
