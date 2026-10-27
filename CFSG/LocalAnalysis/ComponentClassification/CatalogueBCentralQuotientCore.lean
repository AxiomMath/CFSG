module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBCentralQuotientDerived
public import CFSG.LocalAnalysis.ComponentClassification.LBalancePrimeCore

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBCentralQuotient

theorem primeCore_map_le {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y]
    (p : ℕ) [Fact p.Prime] (f : X →* Y) (hsurjective : Function.Surjective f) :
    (pPrimeCore p X).map f ≤ pPrimeCore p Y := by
  apply le_sSup
  exact ⟨Subgroup.Normal.map inferInstance f hsurjective,
    (pPrimeCore_coprime_card (p := p) (G := X)).of_dvd_right
      ((pPrimeCore p X).card_map_dvd f)⟩

theorem corePreimage_pSubgroup_central {X Y : Type*} [Group X] [Finite X]
    [Group Y] [Finite Y] (p : ℕ) [Fact p.Prime] (f : X →* Y)
    (hcentral : f.ker ≤ Subgroup.center X)
    (P : Subgroup ((pPrimeCore p Y).comap f)) (hP : IsPGroup p P) :
    P ≤ Subgroup.center ((pPrimeCore p Y).comap f) := by
  let r := preimageRestriction f (pPrimeCore p Y)
  have hbot : P.map r = ⊥ := by
    apply Subgroup.card_eq_one.mp
    rcases (hP.map r).card_eq_or_dvd with hone | hdivides
    · exact hone
    · exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mp
        (pPrimeCore_coprime_card (p := p) (G := Y))
        (hdivides.trans (Subgroup.card_subgroup_dvd_card _))).elim
  exact (Subgroup.map_eq_bot_iff _).mp hbot |>.trans
    (preimageRestriction_kernel_central f hcentral (pPrimeCore p Y))

theorem primeCore_map {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y]
    (p : ℕ) [Fact p.Prime] (f : X →* Y) (hsurjective : Function.Surjective f)
    (hcentral : f.ker ≤ Subgroup.center X) :
    (pPrimeCore p X).map f = pPrimeCore p Y := by
  apply le_antisymm (primeCore_map_le p f hsurjective)
  let V := (pPrimeCore p Y).comap f
  let : V.Normal := Subgroup.Normal.comap inferInstance f
  let r := preimageRestriction f (pPrimeCore p Y)
  let P : Sylow p V := Classical.choice Sylow.nonempty
  have hPcentral : (P : Subgroup V) ≤ Subgroup.center V :=
    corePreimage_pSubgroup_central p f hcentral P P.isPGroup'
  have hnormalizer : Subgroup.normalizer (P : Set V) ≤ Subgroup.centralizer (P : Set V) := by
    intro x _
    apply Subgroup.mem_centralizer_iff.mpr
    intro z hz
    exact ((Subgroup.mem_center_iff.mp (hPcentral hz)) x).symm
  let t := MonoidHom.transferSylow P hnormalizer
  have hcoprime : Nat.Coprime p (Nat.card t.ker) :=
    (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
      (MonoidHom.not_dvd_card_ker_transferSylow P hnormalizer)
  have hTcore : t.ker ≤ pPrimeCore p V := le_sSup ⟨inferInstance, hcoprime⟩
  have hTambient : t.ker.map V.subtype ≤ pPrimeCore p X := by
    have h := Subgroup.map_mono (f := V.subtype) hTcore
    rw [← LBalance.primeCore_eq_map, LBalance.primeCore_normal_intersection] at h
    exact h.trans inf_le_right
  have hPker : (P : Subgroup V) ≤ r.ker := by
    apply (Subgroup.map_eq_bot_iff _).mp
    apply Subgroup.card_eq_one.mp
    rcases (P.isPGroup'.map r).card_eq_or_dvd with hone | hdivides
    · exact hone
    · exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mp
        (pPrimeCore_coprime_card (p := p) (G := Y))
        (hdivides.trans (Subgroup.card_subgroup_dvd_card _))).elim
  have hsup : t.ker ⊔ (P : Subgroup V) = ⊤ :=
    (MonoidHom.ker_transferSylow_isComplement' P hnormalizer).sup_eq_top
  intro y hy
  obtain ⟨x, hxy⟩ := preimageRestriction_surjective f hsurjective (pPrimeCore p Y) ⟨y, hy⟩
  have hx : x ∈ t.ker ⊔ (P : Subgroup V) := by
    rw [hsup]
    exact Subgroup.mem_top x
  obtain ⟨u, hu, z, hz, hproduct⟩ := Subgroup.mem_sup_of_normal_left.mp hx
  have hrz : r z = 1 := MonoidHom.mem_ker.mp (hPker hz)
  have hru : r u = ⟨y, hy⟩ := by
    rw [← hxy, ← hproduct, map_mul, hrz, mul_one]
  exact ⟨u.val, hTambient (Subgroup.mem_map_of_mem V.subtype hu),
    congrArg Subtype.val hru⟩

@[expose] def coreQuotientMap {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y]
    (p : ℕ) [Fact p.Prime] (f : X →* Y) (hsurjective : Function.Surjective f) :
    (X ⧸ pPrimeCore p X) →* (Y ⧸ pPrimeCore p Y) :=
  QuotientGroup.map _ _ f (Subgroup.map_le_iff_le_comap.mp (primeCore_map_le p f hsurjective))

theorem coreQuotientMap_mk {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y]
    (p : ℕ) [Fact p.Prime] (f : X →* Y) (hsurjective : Function.Surjective f) (x : X) :
    coreQuotientMap p f hsurjective ((QuotientGroup.mk' (pPrimeCore p X)) x) =
      (QuotientGroup.mk' (pPrimeCore p Y)) (f x) :=
  QuotientGroup.map_mk _ _ f _ x

theorem coreQuotientMap_surjective {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y]
    (p : ℕ) [Fact p.Prime] (f : X →* Y) (hsurjective : Function.Surjective f) :
    Function.Surjective (coreQuotientMap p f hsurjective) := by
  intro y
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore p Y) y
  obtain ⟨x, rfl⟩ := hsurjective z
  exact ⟨(QuotientGroup.mk' (pPrimeCore p X)) x, coreQuotientMap_mk p f hsurjective x⟩

theorem coreQuotientMap_kernel_central {X Y : Type*} [Group X] [Finite X]
    [Group Y] [Finite Y] (p : ℕ) [Fact p.Prime] (f : X →* Y)
    (hsurjective : Function.Surjective f) (hcentral : f.ker ≤ Subgroup.center X) :
    (coreQuotientMap p f hsurjective).ker ≤ Subgroup.center (X ⧸ pPrimeCore p X) := by
  intro x hx
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore p X) x
  have hzero := MonoidHom.mem_ker.mp hx
  rw [coreQuotientMap_mk] at hzero
  have hcore : f z ∈ pPrimeCore p Y := (QuotientGroup.eq_one_iff _).mp hzero
  rw [← primeCore_map p f hsurjective hcentral] at hcore
  obtain ⟨u, hu, hfu⟩ := Subgroup.mem_map.mp hcore
  have hker : z * u⁻¹ ∈ f.ker := by
    apply MonoidHom.mem_ker.mpr
    rw [map_mul, map_inv, hfu, mul_inv_cancel]
  let q := QuotientGroup.mk' (pPrimeCore p X)
  have hqu : q u = 1 := (QuotientGroup.eq_one_iff _).mpr hu
  have hrepresentative : q z = q (z * u⁻¹) := by
    rw [map_mul, map_inv, hqu, inv_one, mul_one]
  change q z ∈ Subgroup.center (X ⧸ pPrimeCore p X)
  rw [hrepresentative]
  apply Subgroup.mem_center_iff.mpr
  intro y
  obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore p X) y
  simpa only [map_mul] using congrArg q ((Subgroup.mem_center_iff.mp (hcentral hker)) v)

theorem coreQuotientMap_map_image {X Y : Type*} [Group X] [Finite X]
    [Group Y] [Finite Y] (p : ℕ) [Fact p.Prime] (f : X →* Y)
    (hsurjective : Function.Surjective f) (L : Subgroup X) :
    (L.map (QuotientGroup.mk' (pPrimeCore p X))).map (coreQuotientMap p f hsurjective) =
      (L.map f).map (QuotientGroup.mk' (pPrimeCore p Y)) := by
  rw [Subgroup.map_map, Subgroup.map_map]
  apply congrArg (Subgroup.map · L)
  exact MonoidHom.ext (coreQuotientMap_mk p f hsurjective)

end CFSG.ComponentClassification.CatalogueBCentralQuotient
