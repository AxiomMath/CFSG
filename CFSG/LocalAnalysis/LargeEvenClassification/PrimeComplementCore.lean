module

public import CFSG.LocalAnalysis.LargeEvenClassification.SubgroupTransport

public section

open CFSG.Open

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse targetUniverse

theorem prime_complement_sup {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    {prime : ℕ} (hprime : prime.Prime) (Normal Other : Subgroup Ambient)
    (hnormal : Normal.Normal) (hfirst : ¬prime ∣ Nat.card Normal)
    (hother : ¬prime ∣ Nat.card Other) :
    ¬prime ∣ Nat.card (Normal ⊔ Other : Subgroup Ambient) := by
  let : Normal.Normal := hnormal
  have hquotient : ¬prime ∣ Nat.card (Other ⧸ Normal.subgroupOf Other) :=
    fun hdivides => hother (hdivides.trans (Subgroup.card_quotient_dvd_card _))
  have hquotientSup : ¬prime ∣ Nat.card
      ((Other ⊔ Normal : Subgroup Ambient) ⧸ Normal.subgroupOf (Other ⊔ Normal)) := by
    rw [← Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalQuotient
      Other Normal).toEquiv]
    exact hquotient
  have hnormalCard : Nat.card (Normal.subgroupOf (Other ⊔ Normal)) = Nat.card Normal :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [sup_comm, Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Normal.subgroupOf (Other ⊔ Normal)), hnormalCard]
  exact hprime.not_dvd_mul hquotientSup hfirst

@[expose] noncomputable def primeComplementCore (prime : ℕ) (Ambient : Type groupUniverse)
    [Group Ambient] : Subgroup Ambient :=
  ⨆ Normal : Subgroup Ambient, ⨆ (_ : Normal.Normal),
    ⨆ (_ : ¬prime ∣ Nat.card Normal), Normal

theorem normal_prime_complement_le_core {Ambient : Type groupUniverse} [Group Ambient]
    {prime : ℕ} (Normal : Subgroup Ambient) (hnormal : Normal.Normal)
    (hcomplement : ¬prime ∣ Nat.card Normal) : Normal ≤ primeComplementCore prime Ambient :=
  le_iSup_of_le Normal (le_iSup_of_le hnormal (le_iSup_of_le hcomplement le_rfl))

theorem primeComplementCore_eq_maximal (Ambient : Type groupUniverse) [Group Ambient]
    [Finite Ambient] {prime : ℕ} (hprime : prime.Prime) :
    ∃ Core : Subgroup Ambient,
      Core.Normal ∧ ¬prime ∣ Nat.card Core ∧ primeComplementCore prime Ambient = Core := by
  have hbot : (⊥ : Subgroup Ambient).Normal ∧ ¬prime ∣ Nat.card (⊥ : Subgroup Ambient) :=
    ⟨inferInstance, by simpa using hprime.not_dvd_one⟩
  obtain ⟨Core, _, hmaximal⟩ := Finite.exists_le_maximal
    (p := fun Normal : Subgroup Ambient => Normal.Normal ∧ ¬prime ∣ Nat.card Normal) hbot
  obtain ⟨hnormal, hcomplement⟩ := hmaximal.prop
  refine ⟨Core, hnormal, hcomplement, le_antisymm ?_ ?_⟩
  · apply iSup_le
    intro Normal
    apply iSup_le
    intro hsubgroupNormal
    apply iSup_le
    intro hsubgroupComplement
    let : Core.Normal := hnormal
    let : Normal.Normal := hsubgroupNormal
    have hsup : (Core ⊔ Normal).Normal ∧ ¬prime ∣ Nat.card (Core ⊔ Normal : Subgroup Ambient) :=
      ⟨inferInstance, prime_complement_sup hprime Core Normal hnormal
        hcomplement hsubgroupComplement⟩
    exact le_sup_right.trans (hmaximal.2 hsup le_sup_left)
  · exact normal_prime_complement_le_core Core hnormal hcomplement

theorem primeComplementCore_normal (Ambient : Type groupUniverse) [Group Ambient]
    [Finite Ambient] {prime : ℕ} (hprime : prime.Prime) :
    (primeComplementCore prime Ambient).Normal := by
  obtain ⟨Core, hnormal, _, hcore⟩ := primeComplementCore_eq_maximal Ambient hprime
  exact hcore ▸ hnormal

theorem primeComplementCore_order (Ambient : Type groupUniverse) [Group Ambient]
    [Finite Ambient] {prime : ℕ} (hprime : prime.Prime) :
    ¬prime ∣ Nat.card (primeComplementCore prime Ambient) := by
  obtain ⟨Core, _, hcomplement, hcore⟩ := primeComplementCore_eq_maximal Ambient hprime
  exact hcore ▸ hcomplement

theorem primeComplementCore_map_le {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {Target : Type targetUniverse} [Group Target] [Finite Target]
    {prime : ℕ} (hprime : prime.Prime) (coordinates : Ambient ≃* Target) :
    (primeComplementCore prime Ambient).map coordinates.toMonoidHom ≤
      primeComplementCore prime Target := by
  apply normal_prime_complement_le_core
  · exact (primeComplementCore_normal Ambient hprime).map coordinates.toMonoidHom
      coordinates.surjective
  · rw [← Nat.card_congr (Subgroup.equivMapOfInjective (primeComplementCore prime Ambient)
      coordinates.toMonoidHom coordinates.injective).toEquiv]
    exact primeComplementCore_order Ambient hprime

theorem primeComplementCore_map_mulEquiv {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {Target : Type targetUniverse} [Group Target] [Finite Target]
    {prime : ℕ} (hprime : prime.Prime) (coordinates : Ambient ≃* Target) :
    (primeComplementCore prime Ambient).map coordinates.toMonoidHom =
      primeComplementCore prime Target := by
  apply le_antisymm (primeComplementCore_map_le hprime coordinates)
  have hinverse := Subgroup.map_mono (f := coordinates.toMonoidHom)
    (primeComplementCore_map_le hprime coordinates.symm)
  rw [subgroup_map_forward_inverse_mulEquiv coordinates] at hinverse
  exact hinverse

theorem primeComplementCore_characteristic (Ambient : Type groupUniverse) [Group Ambient]
    [Finite Ambient] {prime : ℕ} (hprime : prime.Prime) :
    (primeComplementCore prime Ambient).Characteristic :=
  Subgroup.characteristic_iff_map_eq.mpr (primeComplementCore_map_mulEquiv hprime)

@[expose] noncomputable def primeComplementCoreOf {Ambient : Type groupUniverse} [Group Ambient]
    (prime : ℕ) (Local : Subgroup Ambient) : Subgroup Ambient :=
  (primeComplementCore prime Local).map Local.subtype

theorem primeComplementCoreOf_le {Ambient : Type groupUniverse} [Group Ambient]
    (prime : ℕ) (Local : Subgroup Ambient) : primeComplementCoreOf prime Local ≤ Local := by
  intro element helement
  obtain ⟨source, _, rfl⟩ := helement
  exact source.property

theorem primeComplementCoreOf_order {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {prime : ℕ} (hprime : prime.Prime) (Local : Subgroup Ambient) :
    ¬prime ∣ Nat.card (primeComplementCoreOf prime Local) := by
  unfold primeComplementCoreOf
  rw [← Nat.card_congr (Subgroup.equivMapOfInjective (primeComplementCore prime Local)
    Local.subtype Local.subtype_injective).toEquiv]
  exact primeComplementCore_order Local hprime

theorem primeComplementCoreOf_map_mulEquiv {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {Target : Type targetUniverse} [Group Target] [Finite Target]
    {prime : ℕ} (hprime : prime.Prime) (coordinates : Ambient ≃* Target)
    (Local : Subgroup Ambient) :
    (primeComplementCoreOf prime Local).map coordinates.toMonoidHom =
      primeComplementCoreOf prime (Local.map coordinates.toMonoidHom) := by
  let localCoordinates := Subgroup.equivMapOfInjective Local coordinates.toMonoidHom
    coordinates.injective
  have hcomposition : (Local.map coordinates.toMonoidHom).subtype.comp
      localCoordinates.toMonoidHom = coordinates.toMonoidHom.comp Local.subtype := by
    ext element
    rfl
  unfold primeComplementCoreOf
  rw [← primeComplementCore_map_mulEquiv hprime localCoordinates,
    Subgroup.map_map, Subgroup.map_map, hcomposition]

theorem centralizer_set_map_mulEquiv {Ambient : Type groupUniverse} [Group Ambient]
    {Target : Type targetUniverse} [Group Target] (coordinates : Ambient ≃* Target)
    (elements : Set Ambient) :
    (Subgroup.centralizer elements).map coordinates.toMonoidHom =
      Subgroup.centralizer (coordinates '' elements) := by
  apply le_antisymm (Subgroup.map_centralizer_le_centralizer_image elements coordinates.toMonoidHom)
  have hinverse := Subgroup.map_mono (f := coordinates.toMonoidHom)
    (Subgroup.map_centralizer_le_centralizer_image (coordinates '' elements)
      coordinates.symm.toMonoidHom)
  have himage : coordinates.symm '' (coordinates '' elements) = elements := by
    ext element
    simp
  simpa only [subgroup_map_forward_inverse_mulEquiv, MulEquiv.coe_toMonoidHom,
    himage] using hinverse

end CFSG.LargeEvenClassification.Helpers
