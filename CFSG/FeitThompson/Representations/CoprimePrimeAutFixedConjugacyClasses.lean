module

public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.Group
public import CFSG.FeitThompson.Foundations.PGroupFixedPointCongruence

open MulAction Pointwise

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {K : Type*} [Group K] {b : MulAut K} {q : ℕ}

def autFixedSubgroup (b : MulAut K) : Subgroup K := (b : K →* K).eqLocus (.id K)

@[simp]
theorem mem_autFixedSubgroup {x : K} : x ∈ autFixedSubgroup b ↔ b x = x := Iff.rfl

theorem autFixedSubgroup_eq_eqLocus (b : MulAut K) :
    autFixedSubgroup b = (b : K →* K).eqLocus (.id K) := (rfl)

theorem coe_autFixedSubgroup (b : MulAut K) :
    (autFixedSubgroup b : Set K) = {x : K | b x = x} := (rfl)

theorem autFixedSubgroup_eq_fixedPoints_zpowers (b : MulAut K) :
    autFixedSubgroup b = FixedPoints.subgroup (Subgroup.zpowers b) K := by
  ext x
  rw [mem_autFixedSubgroup, FixedPoints.mem_subgroup]
  refine ⟨fun hx g => ?_, fun h => h ⟨b, Subgroup.mem_zpowers b⟩⟩
  exact (Subgroup.zpowers_le (g := b) (H := stabilizer (MulAut K) x)).mpr hx g.2

theorem carrier_mk_eq_setOf_conj (x : K) :
    (ConjClasses.mk x).carrier = {y : K | ∃ t : K, t⁻¹ * x * t = y} := by
  ext y
  simp only [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff,
    Set.mem_ofPred_eq]
  exact ⟨fun ⟨c, hc⟩ => ⟨c, by rw [← hc]; group⟩, fun ⟨t, ht⟩ => ⟨t, by rw [← ht]; group⟩⟩

theorem conjClasses_map_mk {L : Type*} [Group L] (f : K →* L) (x : K) :
    ConjClasses.map f (ConjClasses.mk x) = ConjClasses.mk (f x) := (rfl)

theorem conjClasses_carrier_injective : Function.Injective (ConjClasses.carrier (α := K)) := by
  intro D E h
  obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective D
  exact ConjClasses.mem_carrier_iff_mk_eq.mp (h ▸ ConjClasses.mem_carrier_mk)

theorem isConj_mulEquiv_iff (f : K ≃* K) {x y : K} : IsConj (f x) (f y) ↔ IsConj x y :=
  ⟨fun h => by simpa using MonoidHom.map_isConj (f.symm : K →* K) h,
    MonoidHom.map_isConj (f : K →* K)⟩

theorem carrier_map_mulEquiv (f : K ≃* K) (D : ConjClasses K) :
    (ConjClasses.map (f : K →* K) D).carrier = f • D.carrier := by
  obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective D
  ext z
  rw [conjClasses_map_mk, Set.mem_smul_set_iff_inv_smul_mem]
  simp only [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]
  exact ⟨fun h => by simpa using (isConj_mulEquiv_iff f.symm).mpr h,
    fun h => by simpa using (isConj_mulEquiv_iff f).mpr h⟩

theorem natCard_carrier_dvd_natCard (D : ConjClasses K) : Nat.card D.carrier ∣ Nat.card K := by
  obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective D
  rw [← ConjAct.orbit_eq_carrier_conjClasses]
  exact (natCard_orbit_dvd_natCard x).trans
    (dvd_of_eq (Nat.card_congr ConjAct.ofConjAct.toEquiv))

def bStableConjClasses (b : MulAut K) : Set (ConjClasses K) := {D | b • D.carrier = D.carrier}

theorem mem_bStableConjClasses {D : ConjClasses K} :
    D ∈ bStableConjClasses b ↔ b • D.carrier = D.carrier := Iff.rfl

theorem mem_bStableConjClasses_iff_map_eq {D : ConjClasses K} :
    D ∈ bStableConjClasses b ↔ ConjClasses.map (b : K →* K) D = D := by
  rw [mem_bStableConjClasses, ← carrier_map_mulEquiv]
  exact ⟨fun h => conjClasses_carrier_injective h, fun h => by rw [h]⟩

theorem mapsTo_carrier_of_mem_bStableConjClasses {D : ConjClasses K}
    (hD : D ∈ bStableConjClasses b) {x : K} (hx : x ∈ D.carrier) : b x ∈ D.carrier :=
  (mem_bStableConjClasses.mp hD) ▸ Set.smul_mem_smul_set hx

private def stableSubMulAction (S : Set K) (hS : b • S = S) :
    SubMulAction (Subgroup.zpowers b) K where
  carrier := S
  smul_mem' := by
    intro g x hx
    have hg : (g : MulAut K) • S = S :=
      (Subgroup.zpowers_le (g := b) (H := stabilizer (MulAut K) S)).mpr hS g.2
    exact hg ▸ Set.smul_mem_smul_set hx

theorem smul_set_eq_self_of_mapsTo [Finite K] {S : Set K} (hS : ∀ x ∈ S, b x ∈ S) : b • S = S :=
  Set.eq_of_subset_of_ncard_le (by rintro _ ⟨t, ht, rfl⟩; simpa using hS t ht)
    (le_of_eq (Set.ncard_smul_set b S).symm) (Set.toFinite S)

theorem exists_fixed_mem_of_not_dvd_natCard [Finite K] (hq : q.Prime) (hbq : b ^ q = 1)
    {S : Set K} (hS : ∀ x ∈ S, b x ∈ S) (hcard : ¬ q ∣ Nat.card S) : ∃ x ∈ S, b x = x := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨a, ha⟩ : ∃ a, orderOf b = q ^ a := by
    rcases (Nat.dvd_prime hq).mp (orderOf_dvd_of_pow_eq_one hbq) with h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩
  have hP : Nat.card (Subgroup.zpowers b) = q ^ a := by rw [Nat.card_zpowers, ha]
  obtain ⟨x, hx⟩ := nonempty_fixedPoints_of_not_dvd_natCard (P := Subgroup.zpowers b)
    (X := ↥(stableSubMulAction S (smul_set_eq_self_of_mapsTo hS))) hP hcard
  refine ⟨(x : K), x.2, ?_⟩
  simpa [SubMulAction.val_smul] using congrArg Subtype.val (hx ⟨b, Subgroup.mem_zpowers b⟩)

theorem setOf_conj_eq_smul_centralizer {x y t₀ : K} (ht₀ : t₀ * x * t₀⁻¹ = y) :
    {t : K | t * x * t⁻¹ = y} = t₀ • (Subgroup.centralizer ({x} : Set K) : Set K) := by
  subst ht₀
  ext t
  simp only [Set.mem_ofPred_eq, Set.mem_smul_set_iff_inv_smul_mem, SetLike.mem_coe,
    Subgroup.mem_centralizer_singleton_iff, smul_eq_mul]
  constructor
  · intro h
    have := congrArg (fun z => t₀⁻¹ * z * t) h
    simp only [mul_assoc] at this ⊢
    simpa [mul_assoc] using this
  · intro h
    have := congrArg (fun z => t₀ * z * t⁻¹) h
    simp only [mul_assoc] at this ⊢
    simpa [mul_assoc] using this

theorem isConj_of_isConj_coe [Finite K] (hq : q.Prime) (hqK : ¬ q ∣ Nat.card K) (hbq : b ^ q = 1)
    {x y : autFixedSubgroup b} (h : IsConj (x : K) (y : K)) : IsConj x y := by
  obtain ⟨t₀, ht₀⟩ := isConj_iff.mp h
  have hcard : Nat.card {t : K | t * (x : K) * t⁻¹ = (y : K)} ∣ Nat.card K := by
    rw [setOf_conj_eq_smul_centralizer ht₀, Nat.card_coe_set_eq, Set.ncard_smul_set,
      ← Nat.card_coe_set_eq]
    exact Subgroup.card_subgroup_dvd_card _
  have hstab : ∀ t ∈ {t : K | t * (x : K) * t⁻¹ = (y : K)},
      b t ∈ {t : K | t * (x : K) * t⁻¹ = (y : K)} := by
    intro t ht
    have hbx : b (t * (x : K) * t⁻¹) = b t * (x : K) * (b t)⁻¹ := by
      simp [mem_autFixedSubgroup.mp x.2]
    simp only [Set.mem_ofPred_eq] at ht ⊢
    rw [← hbx, ht, mem_autFixedSubgroup.mp y.2]
  obtain ⟨t, htT, htb⟩ := exists_fixed_mem_of_not_dvd_natCard hq hbq hstab
    (fun hd => hqK (hd.trans hcard))
  exact isConj_iff.mpr ⟨⟨t, htb⟩, Subtype.ext (by simpa using htT)⟩

theorem map_subtype_mem_bStableConjClasses (E : ConjClasses (autFixedSubgroup b)) :
    ConjClasses.map (autFixedSubgroup b).subtype E ∈ bStableConjClasses b := by
  obtain ⟨c, rfl⟩ := ConjClasses.mk_surjective E
  rw [mem_bStableConjClasses_iff_map_eq, conjClasses_map_mk, conjClasses_map_mk]
  exact congrArg ConjClasses.mk (mem_autFixedSubgroup.mp c.2)

theorem exists_map_subtype_eq [Finite K] (hq : q.Prime) (hqK : ¬ q ∣ Nat.card K)
    (hbq : b ^ q = 1) {D : ConjClasses K} (hD : D ∈ bStableConjClasses b) :
    ∃ E : ConjClasses (autFixedSubgroup b),
      ConjClasses.map (autFixedSubgroup b).subtype E = D := by
  obtain ⟨x, hxD, hxb⟩ := exists_fixed_mem_of_not_dvd_natCard hq hbq
    (fun _ hx => mapsTo_carrier_of_mem_bStableConjClasses hD hx)
    (fun hd => hqK (hd.trans (natCard_carrier_dvd_natCard D)))
  refine ⟨ConjClasses.mk ⟨x, hxb⟩, ?_⟩
  rw [conjClasses_map_mk]
  exact ConjClasses.mem_carrier_iff_mk_eq.mp hxD

theorem map_subtype_injective [Finite K] (hq : q.Prime) (hqK : ¬ q ∣ Nat.card K)
    (hbq : b ^ q = 1) :
    Function.Injective (ConjClasses.map (autFixedSubgroup b).subtype) := by
  intro E F h
  obtain ⟨c, rfl⟩ := ConjClasses.mk_surjective E
  obtain ⟨d, rfl⟩ := ConjClasses.mk_surjective F
  rw [conjClasses_map_mk, conjClasses_map_mk, ConjClasses.mk_eq_mk_iff_isConj] at h
  exact ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_of_isConj_coe hq hqK hbq h)

theorem preimage_val_carrier_map_subtype [Finite K] (hq : q.Prime) (hqK : ¬ q ∣ Nat.card K)
    (hbq : b ^ q = 1) (E : ConjClasses (autFixedSubgroup b)) :
    Subtype.val ⁻¹' (ConjClasses.map (autFixedSubgroup b).subtype E).carrier = E.carrier := by
  obtain ⟨c, rfl⟩ := ConjClasses.mk_surjective E
  ext z
  simp only [Set.mem_preimage, conjClasses_map_mk, ConjClasses.mem_carrier_iff_mk_eq,
    ConjClasses.mk_eq_mk_iff_isConj]
  exact ⟨fun h => isConj_of_isConj_coe hq hqK hbq h,
    fun h => MonoidHom.map_isConj (autFixedSubgroup b).subtype h⟩

theorem val_image_carrier_map_subtype [Finite K] (hq : q.Prime) (hqK : ¬ q ∣ Nat.card K)
    (hbq : b ^ q = 1) (E : ConjClasses (autFixedSubgroup b)) :
    Subtype.val '' E.carrier =
      (ConjClasses.map (autFixedSubgroup b).subtype E).carrier ∩
        (autFixedSubgroup b : Set K) := by
  rw [← preimage_val_carrier_map_subtype hq hqK hbq E, Set.image_preimage_eq_inter_range,
    Subtype.range_coe]

noncomputable def conjClassesAutFixedEquivBStable [Finite K] (hq : q.Prime)
    (hqK : ¬ q ∣ Nat.card K) (hbq : b ^ q = 1) :
    ConjClasses (autFixedSubgroup b) ≃ bStableConjClasses b :=
  Equiv.ofBijective (fun E => ⟨ConjClasses.map (autFixedSubgroup b).subtype E,
      map_subtype_mem_bStableConjClasses E⟩)
    ⟨fun _ _ h => map_subtype_injective hq hqK hbq (congrArg Subtype.val h), fun D => by
      obtain ⟨E, hE⟩ := exists_map_subtype_eq hq hqK hbq D.2
      exact ⟨E, Subtype.ext hE⟩⟩

@[simp]
theorem coe_conjClassesAutFixedEquivBStable [Finite K] (hq : q.Prime) (hqK : ¬ q ∣ Nat.card K)
    (hbq : b ^ q = 1) (E : ConjClasses (autFixedSubgroup b)) :
    (conjClassesAutFixedEquivBStable hq hqK hbq E : ConjClasses K) =
      ConjClasses.map (autFixedSubgroup b).subtype E := (rfl)

noncomputable def bStableConjClassesEquivConjClassesAutFixed [Finite K] (hq : q.Prime)
    (hqK : ¬ q ∣ Nat.card K) (hbq : b ^ q = 1) :
    bStableConjClasses b ≃ ConjClasses (autFixedSubgroup b) :=
  (conjClassesAutFixedEquivBStable hq hqK hbq).symm

theorem carrier_bStableConjClassesEquivConjClassesAutFixed [Finite K] (hq : q.Prime)
    (hqK : ¬ q ∣ Nat.card K) (hbq : b ^ q = 1) (D : bStableConjClasses b) :
    Subtype.val '' (bStableConjClassesEquivConjClassesAutFixed hq hqK hbq D).carrier =
      (D : ConjClasses K).carrier ∩ (autFixedSubgroup b : Set K) := by
  rw [val_image_carrier_map_subtype hq hqK hbq]
  congr 2
  exact congrArg Subtype.val
    ((conjClassesAutFixedEquivBStable hq hqK hbq).apply_symm_apply D)

theorem existsUnique_conjClasses_val_image_carrier_eq [Finite K] (hq : q.Prime)
    (hqK : ¬ q ∣ Nat.card K) (hbq : b ^ q = 1) {D : ConjClasses K}
    (hD : D ∈ bStableConjClasses b) :
    ∃! E : ConjClasses (autFixedSubgroup b),
      Subtype.val '' E.carrier = D.carrier ∩ (autFixedSubgroup b : Set K) := by
  refine ⟨bStableConjClassesEquivConjClassesAutFixed hq hqK hbq ⟨D, hD⟩,
    carrier_bStableConjClassesEquivConjClassesAutFixed hq hqK hbq ⟨D, hD⟩, fun E hE => ?_⟩
  refine conjClasses_carrier_injective (Set.image_injective.mpr Subtype.val_injective ?_)
  rw [hE, carrier_bStableConjClassesEquivConjClassesAutFixed hq hqK hbq ⟨D, hD⟩]

end

end CFSG.FeitThompson
