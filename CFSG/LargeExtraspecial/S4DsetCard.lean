module

public import CFSG.LargeExtraspecial.S4FiveMain
public import CFSG.LargeExtraspecial.S12DWCount

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module QuadraticMap

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

theorem exists_classes_of_mem_orbit (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O} (ht : t ∈ S.Lbar g)
    {v : S.Qt} (hv : v ∈ orbit S g t) :
    ∃ h : S.M, t ∈ S.Lbar ((h : G) * g) ∧
      v = S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) := by
  obtain ⟨x, hx, rfl⟩ := hv
  obtain ⟨h, rfl⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar hx)
  refine ⟨h, ?_, ρ_cl_conj_z S h haQ⟩
  have e : (S.ρ h)⁻¹ * t * S.ρ h = t := by
    rw [mul_assoc, ← commute_of_mem_Rbar haQ hx, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [mem_Lbar_mul_iff, e]
  exact ht

theorem ncard_Dset_eq_ncard_orbit (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (hB : ∀ h : S.M, t ∈ S.Lbar ((h : G) * g) →
      S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) ∈ orbit S g t) :
    (Dset S g t).ncard = (orbit S g t).ncard := by
  have haQ := H.conj_mem
  have hex : ∀ v ∈ orbit S g t, ∃ h : S.M, t ∈ S.Lbar ((h : G) * g) ∧
      v = S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) :=
    fun v hv => exists_classes_of_mem_orbit haQ ht hv
  symm
  refine Set.ncard_congr (fun v hv => S.Lbar ((Classical.choose (hex v hv) : S.M) * g))
    ?_ ?_ ?_
  · intro v hv
    exact ⟨Classical.choose (hex v hv), rfl, (Classical.choose_spec (hex v hv)).1⟩
  · intro v w hv hw hvw
    have e := cl_eq_of_Lbar_eq H hvw
    exact ((Classical.choose_spec (hex v hv)).2).trans
      (e.trans (Classical.choose_spec (hex w hw)).2.symm)
  · intro X hX
    obtain ⟨k, rfl, hk⟩ := hX
    have hvk := hB k hk
    refine ⟨S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹), hvk, ?_⟩
    obtain ⟨-, hv⟩ := Classical.choose_spec (hex _ hvk)
    exact Lbar_eq_of_cl_eq S (conj_mem_QG' S k.2 haQ) (conj_ne_z' S k.2 H.conj_ne)
      (conj_mem_QG' S (Classical.choose (hex _ hvk)).2 haQ) hv.symm

theorem Lbar_mul_eq_of_Rbar_eq {t : S.O} (hR : Rbar S g t = S.Lbar g) {k : S.M}
    (hk : t ∈ S.Lbar ((k : G) * g)) : S.Lbar ((k : G) * g) = S.Lbar g := by
  have hle : S.Lbar ((k : G) * g) ≤ S.Lbar g := (Lbar_mul_le_Rbar hk).trans hR.le
  have hcard : Nat.card (S.Lbar ((k : G) * g)) = Nat.card (S.Lbar g) := by
    rw [Lbar_mul S k g]
    exact Subgroup.card_map_of_injective (f := MulEquiv.toMonoidHom (MulAut.conj (S.ρ k)))
      (MulAut.conj (S.ρ k)).injective
  exact Subgroup.eq_of_le_of_card_ge hle hcard.ge

theorem orbit_eq_singleton (H : Hyp4 S g) {t : S.O} (hR : Rbar S g t = S.Lbar g) :
    orbit S g t = {S.cl (g * S.z * g⁻¹)} := by
  ext v
  refine ⟨?_, ?_⟩
  · rintro ⟨x, hx, rfl⟩
    rw [Set.mem_singleton_iff]
    have hx' : x ∈ S.Lbar g := hR ▸ hx
    have hfix : S.cl (g * S.z * g⁻¹) ∈ fixSub S (S.Lbar g) := by
      rw [H.fixSub_eq]
      exact Submodule.mem_span_singleton_self _
    exact (mem_fixSub S).mp hfix x hx'
  · rintro rfl
    exact cl_a_mem_orbit

theorem orbit_eq_diff (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (htr : ∀ v : Vt S g t, v ≠ 0 → (v : S.Qt) ∈ orbit S g t) :
    orbit S g t = (Vt S g t : Set S.Qt) \ {0} := by
  ext v
  refine ⟨fun hv => ⟨orbit_subset_Vt ht H.conj_mem hv, ?_⟩, fun hv => ?_⟩
  · rintro h0
    obtain ⟨x, hx, rfl⟩ := hv
    rw [Set.mem_singleton_iff] at h0
    exact cl_conj_z_ne_zero S H.conj_mem H.conj_ne ((LinearEquiv.map_eq_zero_iff _).mp h0)
  · obtain ⟨hvV, hv0⟩ := hv
    refine htr ⟨v, hvV⟩ fun h0 => hv0 ?_
    rw [Set.mem_singleton_iff]
    exact congrArg Subtype.val h0

theorem ncard_Vt_diff_zero {t : S.O} :
    ((Vt S g t : Set S.Qt) \ {0}).ncard + 1 = 2 ^ finrank (ZMod 2) (Vt S g t) := by
  have hcard : Nat.card (Vt S g t) = 2 ^ finrank (ZMod 2) (Vt S g t) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hmem : (0 : S.Qt) ∈ (Vt S g t : Set S.Qt) := (Vt S g t).zero_mem
  rw [Set.ncard_diff_singleton_add_one hmem, ← hcard]
  exact (Nat.card_coe_set_eq _).symm

theorem card_Dset_add_one_of_transitive (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (hR : Rbar S g t ≠ S.Lbar g)
    (htr : ∀ v : Vt S g t, v ≠ 0 → (v : S.Qt) ∈ orbit S g t) :
    ∃ m, 2 ≤ m ∧ (Dset S g t).ncard + 1 = 2 ^ m := by
  have hB : ∀ h : S.M, t ∈ S.Lbar ((h : G) * g) →
      S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) ∈ orbit S g t := by
    intro h hth
    rw [← coe_bV hth]
    exact htr _ (bV_ne_zero H hth)
  refine ⟨finrank (ZMod 2) (Vt S g t), two_le_finrank_Vt H ht hR, ?_⟩
  rw [ncard_Dset_eq_ncard_orbit H ht hB, orbit_eq_diff H ht htr]
  exact ncard_Vt_diff_zero

theorem ncard_zero_quadratic_eq {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (Q : QuadraticForm (ZMod 2) V)
    (hQ : (polarBilin Q).Nondegenerate) {k : ℕ} (hk : finrank (ZMod 2) V = 2 * k)
    (hk1 : 1 ≤ k) :
    {x | Q x = 0}.ncard = 2 ^ (k - 1) * (2 ^ k + 1) ∨
      {x | Q x = 0}.ncard = 2 ^ (k - 1) * (2 ^ k - 1) := by
  have hc : Nat.card V = 4 ^ k := S12DW.natCard_eq_four_pow hk
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have h2 := CFSG.Fischer.Classification.LocalSymp.two_mul_ncard_quadratic Q
    (S12DW.polar_eq_zero_imp hQ) hc
  have h3 := S12DW.ncard_eq_zero_eq Q
  rw [hc] at h3
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have e1 : (2 : ℕ) ^ (j + 1) = 2 * 2 ^ j := by ring
  have e4 : (4 : ℕ) ^ j = 2 ^ j * 2 ^ j := by rw [← mul_pow]; norm_num
  have e2 : (4 : ℕ) ^ (j + 1) = 4 * (2 ^ j * 2 ^ j) := by rw [pow_succ, e4]; ring
  have hx : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  rw [e1, e2] at h2
  rw [e2] at h3
  simp only [Nat.add_sub_cancel]
  rw [e1]
  obtain ⟨x, hxdef⟩ : ∃ x, x = 2 ^ j := ⟨_, rfl⟩
  rw [← hxdef] at h2 h3 hx ⊢
  obtain ⟨s, hs⟩ : ∃ s, s = x * x := ⟨_, rfl⟩
  rw [← hs] at h2 h3
  rcases h2 with h | h
  · left
    rw [show x * (2 * x + 1) = 2 * s + x by rw [hs]; ring]
    omega
  · right
    rw [Nat.mul_sub_one, show x * (2 * x) = 2 * s by rw [hs]; ring]
    omega

theorem card_Dset_add_one_of_omega (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) :
    ∃ k, 2 ≤ k ∧ ((Dset S g t).ncard + 1 = 2 ^ (k - 1) * (2 ^ k + 1) ∨
      (Dset S g t).ncard + 1 = 2 ^ (k - 1) * (2 ^ k - 1)) := by
  obtain ⟨k, hk⟩ := even_finrank_Vt H C ht ht1 hVQ
  have h4 := four_le_finrank_Vt H C ht ht1 hVQ hNo
  haveI : Module.Finite (ZMod 2) (Vt S g t) := Module.Finite.of_finite
  obtain ⟨Q, hQ, -, -, -, hQiff⟩ := hΩ.exists_form
  have hk2 : 2 ≤ k := by omega
  have hB : ∀ h : S.M, t ∈ S.Lbar ((h : G) * g) →
      S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) ∈ orbit S g t := by
    intro h hth
    have hmem := bV_mem_orbitOf H C ht ht1 hVQ hNo hΩ.not_transitive hth
    have := (mem_orbitOf_RmodN_iff H.conj_mem ht).mp hmem
    rwa [coe_bV] at this
  have hne : ∀ w ∈ orbitOf (RmodN S g t) (aV ht), w ≠ 0 := by
    rintro w ⟨x, -, rfl⟩ h0
    exact aV_ne_zero H ht ((LinearEquiv.map_eq_zero_iff x).mp h0)
  have hO : orbit S g t = Subtype.val '' ({x | Q x = 0} \ {0}) := by
    ext v
    constructor
    · intro hv
      have hvV := orbit_subset_Vt ht H.conj_mem hv
      have hwO : (⟨v, hvV⟩ : ↥(Vt S g t)) ∈ orbitOf (RmodN S g t) (aV ht) :=
        (mem_orbitOf_RmodN_iff H.conj_mem ht).mpr hv
      have hw0 := hne _ hwO
      exact ⟨⟨v, hvV⟩, ⟨(hQiff _ hw0).mpr hwO, hw0⟩, rfl⟩
    · rintro ⟨w, ⟨hQw, hw0'⟩, rfl⟩
      have hw0 : w ≠ 0 := fun h => hw0' (Set.mem_singleton_iff.mpr h)
      exact (mem_orbitOf_RmodN_iff H.conj_mem ht).mp ((hQiff w hw0).mp hQw)
  have hD : (Dset S g t).ncard + 1 = {x : ↥(Vt S g t) | Q x = 0}.ncard := by
    rw [ncard_Dset_eq_ncard_orbit H ht hB, hO, Set.ncard_image_of_injective _ Subtype.val_injective,
      Set.ncard_diff_singleton_add_one (show (0 : ↥(Vt S g t)) ∈ {x | Q x = 0} from map_zero Q)]
  refine ⟨k, hk2, ?_⟩
  rw [hD]
  exact ncard_zero_quadratic_eq Q hQ (by omega) (by omega)

theorem Dset_card_cases (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) :
    (Dset S g t).ncard + 1 = 2 ∨ (∃ m, 2 ≤ m ∧ (Dset S g t).ncard + 1 = 2 ^ m) ∨
      ∃ k, 2 ≤ k ∧ ((Dset S g t).ncard + 1 = 2 ^ (k - 1) * (2 ^ k + 1) ∨
        (Dset S g t).ncard + 1 = 2 ^ (k - 1) * (2 ^ k - 1)) := by
  by_cases hR : Rbar S g t = S.Lbar g
  · left
    have hB : ∀ h : S.M, t ∈ S.Lbar ((h : G) * g) →
        S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) ∈ orbit S g t := by
      intro h hth
      have e : S.Lbar ((h : G) * g) = S.Lbar (((1 : S.M) : G) * g) := by
        rw [Lbar_mul_eq_of_Rbar_eq hR hth, Subgroup.coe_one, one_mul]
      have hc := cl_eq_of_Lbar_eq H e
      simp only [Subgroup.coe_one, one_mul] at hc
      rw [hc]
      exact cl_a_mem_orbit
    rw [ncard_Dset_eq_ncard_orbit H ht hB, orbit_eq_singleton H hR, Set.ncard_singleton]
  · right
    rcases timmesfeld_4_5 H hNo C ht ht1 with hR' | hL | ⟨hVQ, hSp | hA6 | hΩ | hP⟩
    · exact absurd hR' hR
    · left
      exact card_Dset_add_one_of_transitive H ht hR (fun v hv => hL.mem_orbit v hv)
    · left
      exact card_Dset_add_one_of_transitive H ht hR fun v hv => by
        obtain ⟨x, hx, hxv⟩ := hSp.transitive v hv
        exact (mem_orbitOf_RmodN_iff H.conj_mem ht).mp ⟨x, hx, hxv⟩
    · left
      exact card_Dset_add_one_of_transitive H ht hR fun v hv => by
        obtain ⟨x, hx, hxv⟩ := hA6.transitive v hv
        exact (mem_orbitOf_RmodN_iff H.conj_mem ht).mp ⟨x, hx, hxv⟩
    · right
      exact card_Dset_add_one_of_omega H C ht ht1 hVQ hNo hΩ
    · left
      exact card_Dset_add_one_of_transitive H ht hR fun v hv => by
        obtain ⟨x, hx, hxv⟩ := hP.transitive v hv
        exact (mem_orbitOf_RmodN_iff H.conj_mem ht).mp ⟨x, hx, hxv⟩

theorem Dset_ncard_ne_2025 (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) : (Dset S g t).ncard ≠ 2025 := by
  intro h
  rcases Dset_card_cases H hNo C ht ht1 with h1 | ⟨m, hm, h1⟩ | ⟨k, hk, h1 | h1⟩ <;> rw [h] at h1
  · omega
  · have hm : m < 12 := by
      by_contra hc
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (not_lt.mp hc)
      omega
    interval_cases m <;> omega
  · have hk' : k < 7 := by
      by_contra hc
      have h3 := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (not_lt.mp hc)
      have h4 : 2 ^ (k - 1) ≥ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have : 2 ^ (k - 1) * (2 ^ k + 1) ≥ 2 ^ 6 * (2 ^ 7 + 1) := Nat.mul_le_mul h4 (by omega)
      omega
    interval_cases k <;> omega
  · have hk' : k < 7 := by
      by_contra hc
      have h3 := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (not_lt.mp hc)
      have h4 : 2 ^ (k - 1) ≥ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h5 : 2 ^ k - 1 ≥ 2 ^ 7 - 1 := by omega
      have : 2 ^ (k - 1) * (2 ^ k - 1) ≥ 2 ^ 6 * (2 ^ 7 - 1) := Nat.mul_le_mul h4 h5
      omega
    interval_cases k <;> omega

end CFSG.LargeExtraspecial.S4
