module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveLocal

public section

namespace CFSG.ComponentClassification.RankTwoAltFive

open Subgroup Equiv CFSG.Open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b

variable {G : Type} [Group G]

theorem conjPerm5_bijective : Function.Bijective (CFSG.Quasithin.SteinbergCB.conjPerm 5) :=
  ⟨CFSG.Quasithin.SteinbergCB.conjPerm_injective (by norm_num),
    CFSG.Quasithin.SteinbergCB.conjPerm_surjective (Or.inl rfl)⟩

noncomputable def autA5Equiv : MulAut A5 ≃* Perm (Fin 5) :=
  (MulEquiv.ofBijective (CFSG.Quasithin.SteinbergCB.conjPerm 5) conjPerm5_bijective).symm

noncomputable def autPerm {A : Subgroup G} (e : ↥A ≃* A5) :
    ↥(normalizer (A : Set G)) →* Perm (Fin 5) :=
  have : (A.subgroupOf (normalizer (A : Set G))).Normal := Subgroup.normal_in_normalizer
  (autA5Equiv.toMonoidHom.comp
    (MulAut.congr ((subgroupOfEquivOfLe le_normalizer).trans e)).toMonoidHom).comp
    (MulAut.conjNormal (H := A.subgroupOf (normalizer (A : Set G))))

theorem conjPerm_autPerm {A : Subgroup G} (e : ↥A ≃* A5) (x : ↥(normalizer (A : Set G))) :
    have : (A.subgroupOf (normalizer (A : Set G))).Normal := Subgroup.normal_in_normalizer
    CFSG.Quasithin.SteinbergCB.conjPerm 5 (autPerm e x) =
      MulAut.congr ((subgroupOfEquivOfLe le_normalizer).trans e)
        (MulAut.conjNormal (H := A.subgroupOf (normalizer (A : Set G))) x) := by
  intro _
  exact (MulEquiv.ofBijective _ conjPerm5_bijective).apply_symm_apply _

theorem autPerm_spec {A : Subgroup G} (e : ↥A ≃* A5) (x : ↥(normalizer (A : Set G))) (a : G)
    (ha : a ∈ A) :
    ((e ⟨x * a * (x : G)⁻¹, (mem_normalizer_iff.mp x.2 a).mp ha⟩ : A5) : Perm (Fin 5)) =
      autPerm e x * (e ⟨a, ha⟩ : Perm (Fin 5)) * (autPerm e x)⁻¹ := by
  have : (A.subgroupOf (normalizer (A : Set G))).Normal := Subgroup.normal_in_normalizer
  set e' : ↥(A.subgroupOf (normalizer (A : Set G))) ≃* A5 :=
    (subgroupOfEquivOfLe le_normalizer).trans e with he'
  have hσ := conjPerm_autPerm e x
  have h := CFSG.Quasithin.SteinbergCB.conjPerm_apply 5 (autPerm e x) (e ⟨a, ha⟩)
  rw [hσ] at h
  rw [← h]
  apply congrArg Subtype.val
  have h1 : e'.symm (e ⟨a, ha⟩) = ⟨⟨a, le_normalizer ha⟩, mem_subgroupOf.mpr ha⟩ := by
    apply e'.injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, h1]
  rfl

theorem autPerm_eq_one_iff {A : Subgroup G} (e : ↥A ≃* A5) (x : ↥(normalizer (A : Set G))) :
    autPerm e x = 1 ↔ (x : G) ∈ centralizer (A : Set G) := by
  constructor
  · intro h
    rw [mem_centralizer_iff]
    intro a ha
    have h1 := autPerm_spec e x a ha
    rw [h, one_mul, inv_one, mul_one] at h1
    have h2 : (x : G) * a * (x : G)⁻¹ = a := by
      have := e.injective (Subtype.ext h1)
      exact congrArg Subtype.val this
    calc a * (x : G) = (x : G) * a * (x : G)⁻¹ * (x : G) := by rw [h2]
      _ = (x : G) * a := by group
  · intro h
    apply conjPerm5_bijective.1
    rw [map_one, conjPerm_autPerm]
    refine MulEquiv.ext fun g => ?_
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulAut.one_apply]
    apply ((subgroupOfEquivOfLe le_normalizer).trans e).symm.injective
    rw [MulEquiv.symm_apply_apply]
    apply Subtype.ext
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    simp only [coe_mul, InvMemClass.coe_inv]
    have hg := mem_centralizer_iff.mp h _
      (mem_subgroupOf.mp (((subgroupOfEquivOfLe le_normalizer).trans e).symm g).2)
    calc (x : G) * _ * (x : G)⁻¹ = _ * (x : G) * (x : G)⁻¹ := by rw [hg]
      _ = _ := by group

theorem autPerm_of_mem {A : Subgroup G} (e : ↥A ≃* A5) {a : G} (ha : a ∈ A) :
    autPerm e ⟨a, le_normalizer ha⟩ = ((e ⟨a, ha⟩ : A5) : Perm (Fin 5)) := by
  apply conjPerm5_bijective.1
  refine MulEquiv.ext fun g => Subtype.ext ?_
  rw [CFSG.Quasithin.SteinbergCB.conjPerm_apply, CFSG.Quasithin.SteinbergCB.conjPerm_apply]
  obtain ⟨b, rfl⟩ := e.surjective g
  have h1 := autPerm_spec e ⟨a, le_normalizer ha⟩ b b.2
  rw [← h1]
  have h2 : e ⟨a * b * a⁻¹, (mem_normalizer_iff.mp (le_normalizer ha) b).mp b.2⟩ =
      e ⟨a, ha⟩ * e b * (e ⟨a, ha⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [h2]
  rfl

theorem perm5_eq_one_of_commute : ∀ σ τ : Perm (Fin 5), τ * τ = 1 → τ ≠ 1 →
    Perm.sign τ = 1 → σ * τ = τ * σ → σ ^ 15 = 1 → σ = 1 := by
  decide +kernel

theorem mem_centralizer_of_odd_of_commute {A : Subgroup G} (e : ↥A ≃* A5) {x z : G}
    (hxN : x ∈ normalizer (A : Set G)) (hx : Odd (orderOf x)) (hzA : z ∈ A) (hz2 : z * z = 1)
    (hz1 : z ≠ 1) (hxz : x * z = z * x) : x ∈ centralizer (A : Set G) := by
  set σ := autPerm e ⟨x, hxN⟩ with hσ
  set τ := autPerm e ⟨z, le_normalizer hzA⟩ with hτ
  have hτ2 : τ * τ = 1 := by
    rw [hτ, ← map_mul, ← map_one (autPerm e)]
    exact congrArg _ (Subtype.ext hz2)
  have hτ1 : τ ≠ 1 := fun h => hz1 (by
    have h1 := (autPerm_eq_one_iff e _).mp h
    have h2 : z ∈ A ⊓ centralizer (A : Set G) := mem_inf.mpr ⟨hzA, h1⟩
    rw [inf_centralizer_eq_bot e] at h2
    exact h2)
  have hτs : Perm.sign τ = 1 := by
    rw [hτ, autPerm_of_mem e hzA]
    exact Equiv.Perm.mem_alternatingGroup.mp (e ⟨z, hzA⟩).2
  have hστ : σ * τ = τ * σ := by
    rw [hσ, hτ, ← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext hxz)
  have hσ15 : σ ^ 15 = 1 := by
    have h1 : σ ^ orderOf x = 1 := by
      rw [hσ, ← map_pow, ← map_one (autPerm e)]
      exact congrArg _ (Subtype.ext (pow_orderOf_eq_one x))
    have h2 : orderOf σ ∣ orderOf x := orderOf_dvd_of_pow_eq_one h1
    have h3 : orderOf σ ∣ 8 * 15 := by
      have := orderOf_dvd_natCard σ
      rwa [card_perm5] at this
    have h4 : Nat.Coprime (orderOf σ) 8 := by
      have h5 : Odd (orderOf σ) := hx.of_dvd_nat h2
      exact Nat.Coprime.pow_right 3 (Nat.coprime_two_right.mpr h5)
    exact orderOf_dvd_iff_pow_eq_one.mp (h4.dvd_of_dvd_mul_left h3)
  exact (autPerm_eq_one_iff e ⟨x, hxN⟩).mp (perm5_eq_one_of_commute σ τ hτ2 hτ1 hτs hστ hσ15)

theorem oddCoreIn_centralizer_le_centralizer [Finite G] {A' R' : Subgroup G} (e : ↥A' ≃* A5)
    {z : G} (hzA : z ∈ A') (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hRC : R' ≤ centralizer (A' : Set G)) (hRe : IsElemAbelian 2 R') (hR4 : Nat.card R' = 4)
    (hRN : ∀ r ∈ R', r ≠ 1 → centralizer ({r} : Set G) ≤ normalizer (A' : Set G)) :
    oddCoreIn (centralizer ({z} : Set G)) ≤ centralizer (A' : Set G) := by
  set X := oddCoreIn (centralizer ({z} : Set G)) with hXdef
  have hXz : X ≤ centralizer ({z} : Set G) := oddCoreIn_le _
  have hRz : R' ≤ centralizer ({z} : Set G) := fun r hr =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hRC hr) z hzA).symm
  have hRX : R' ≤ normalizer (X : Set G) := hRz.trans (le_normalizer_oddCoreIn _)
  have hXodd : Odd (Nat.card X) := odd_card_oddCoreIn _
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane 2
    Nat.prime_two R' X (fun r => Subtype.ext (by simpa using hRe.2 r r.2)) (by rw [hR4]; rfl)
    (fun h => (Nat.not_even_iff_odd.mpr hXodd) (even_iff_two_dvd.mpr h)) hRX
  have hXN : X ≤ normalizer (A' : Set G) := by
    rw [hgen]
    refine iSup₂_le fun r hr => ?_
    exact inf_le_right.trans (hRN r r.2 fun h => hr (Subtype.ext h))
  intro x hx
  have hxo : Odd (orderOf x) := by
    have h1 : orderOf x ∣ Nat.card X := by
      rw [← Subgroup.orderOf_mk x hx]
      exact orderOf_dvd_natCard _
    exact hXodd.of_dvd_nat h1
  exact mem_centralizer_of_odd_of_commute e (hXN hx) hxo hzA hz2 hz1
    (mem_centralizer_singleton_iff.mp (hXz hx))

theorem centralizer_le_normalizer_conj [Finite G] {A : Subgroup G}
    (hA : standardComponentIsStandard A) (x : G) {r : G}
    (hrK : r ∈ centralizer (rightConjugate A x : Set G)) (hr1 : r ≠ 1) (hr2 : r * r = 1) :
    centralizer ({r} : Set G) ≤ normalizer (rightConjugate A x : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [centralizer_rightConjugate] at hrK
  have hord : orderOf r = 2 := orderOf_eq_prime (by rw [sq]; exact hr2) hr1
  have hP : IsPGroup 2 (zpowers r) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; rfl)
  have hle : zpowers r ≤ rightConjugate (centralizer (A : Set G)) x := zpowers_le.mpr hrK
  have hne : zpowers r ≠ ⊥ := fun h => hr1 (by
    have h1 := mem_zpowers r
    rw [h] at h1
    exact h1)
  intro c hc
  have hcN : c ∈ normalizer (zpowers r : Set G) := by
    refine centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun h hh => ?_)
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hh
    exact ((Commute.zpow_left (mem_centralizer_singleton_iff.mp hc).symm k)).eq
  have h1 := normalizer_two_subgroup_le _ _
    (tightlyEmbedded_rightConjugate (tightlyEmbedded_centralizer hA) x) hP hle hne hcN
  rw [mem_normalizer_rightConjugate_iff] at h1 ⊢
  rwa [← normalizer_centralizer_eq hA]

theorem oddCoreIn_centralizer_le_centralizer_conj [Finite G] {A R : Subgroup G}
    (hA : standardComponentIsStandard A) (e : ↥A ≃* A5) (hRC : R ≤ centralizer (A : Set G))
    (hRe : IsElemAbelian 2 R) (hR4 : Nat.card R = 4) (x : G) {z : G}
    (hzA : z ∈ rightConjugate A x) (hz2 : z * z = 1) (hz1 : z ≠ 1) :
    oddCoreIn (centralizer ({z} : Set G)) ≤ centralizer (rightConjugate A x : Set G) := by
  refine oddCoreIn_centralizer_le_centralizer ((conjEquiv A x).trans e) hzA hz2 hz1
    (R' := rightConjugate R x) ?_ (isElemAbelian_rightConjugate hRe x)
    (by rw [rightConjugate_card, hR4]) fun r hr hr1 => ?_
  · rw [centralizer_rightConjugate]
    exact map_mono hRC
  · refine centralizer_le_normalizer_conj hA x ?_ hr1 ?_
    · rw [centralizer_rightConjugate]
      exact (map_mono hRC) hr
    · rw [← sq]
      exact (isElemAbelian_rightConjugate hRe x).2 r hr

@[expose] def conjSupThrough (A : Subgroup G) (z : G) : Subgroup G :=
  ⨆ (x : G) (_ : z ∈ rightConjugate A x), rightConjugate A x

theorem oddCoreIn_centralizer_le_centralizer_conjSupThrough [Finite G] {A R : Subgroup G}
    (hA : standardComponentIsStandard A) (e : ↥A ≃* A5) (hRC : R ≤ centralizer (A : Set G))
    (hRe : IsElemAbelian 2 R) (hR4 : Nat.card R = 4) {z : G} (hz2 : z * z = 1) (hz1 : z ≠ 1) :
    oddCoreIn (centralizer ({z} : Set G)) ≤ centralizer (conjSupThrough A z : Set G) := by
  rw [le_centralizer_iff]
  refine iSup₂_le fun x hx => ?_
  rw [← le_centralizer_iff]
  exact oddCoreIn_centralizer_le_centralizer_conj hA e hRC hRe hR4 x hx hz2 hz1

end CFSG.ComponentClassification.RankTwoAltFive
