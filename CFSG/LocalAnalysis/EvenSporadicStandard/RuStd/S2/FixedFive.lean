module

public import Mathlib.GroupTheory.Sylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.CloseGroup

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2

open Subgroup

variable {G : Type*} [Group G]

private theorem exists_invariant_sylow_five [Finite G] {O V : Subgroup G} (hV : IsPGroup 2 V)
    (hVO : V ≤ normalizer (O : Set G)) (hO : Odd (Nat.card O)) :
    ∃ S : Subgroup G, S ≤ O ∧ IsPGroup 5 S ∧ Nat.card S = 5 ^ (Nat.card O).factorization 5 ∧
      V ≤ normalizer (S : Set G) := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : ↥V →* MulAut ↥O := O.normalizerMonoidHom.comp (Subgroup.inclusion hVO)
  let _ : MulDistribMulAction ↥V ↥O := MulDistribMulAction.compHom ↥O φ
  let _ : MulAction ↥V (Sylow 5 ↥O) := Sylow.pointwiseMulAction
  have hcard : ¬ 2 ∣ Nat.card (Sylow 5 ↥O) := by
    obtain ⟨P⟩ : Nonempty (Sylow 5 ↥O) := inferInstance
    intro h
    have h1 := (Sylow.card_dvd_index P).trans (Subgroup.index_dvd_card (P : Subgroup O))
    exact (Nat.not_even_iff_odd.2 hO) (even_iff_two_dvd.2 (h.trans h1))
  obtain ⟨Q₀, hQ₀⟩ := hV.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 5 ↥O) hcard
  refine ⟨(Q₀ : Subgroup O).map O.subtype, Subgroup.map_subtype_le _, Q₀.isPGroup'.map _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective O.subtype_injective, Sylow.card_eq_multiplicity]
  · rw [Subgroup.le_normalizer_iff]
    rintro v hv _ ⟨y, hy, rfl⟩
    have hfix : (⟨v, hv⟩ : ↥V) • Q₀ = Q₀ := (MulAction.mem_fixedPoints.mp hQ₀) ⟨v, hv⟩
    have hmem : (⟨v, hv⟩ : ↥V) • y ∈ (Q₀ : Subgroup O) := by
      have h := Subgroup.smul_mem_pointwise_smul y (⟨v, hv⟩ : ↥V) (Q₀ : Subgroup O) hy
      rwa [← Sylow.pointwise_smul_def, hfix] at h
    refine ⟨_, hmem, ?_⟩
    change ((O.normalizerMonoidHom (Subgroup.inclusion hVO ⟨v, hv⟩)) y : G) = _
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    rfl

private theorem exists_order_five [Finite G] {C : Subgroup G} (hC : IsPGroup 5 C) (hne : C ≠ ⊥) :
    ∃ h ∈ C, orderOf h = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rcases hC.card_eq_or_dvd with h1 | h5
  · exact absurd (Subgroup.card_eq_one.mp h1) hne
  · obtain ⟨⟨h, hh⟩, ho⟩ := exists_prime_orderOf_dvd_card' (G := C) 5 h5
    exact ⟨h, hh, by rw [← ho, Subgroup.orderOf_mk]⟩

theorem exists_fixed_five [Finite G] (O V : Subgroup G) (z d : G) (hV : IsPGroup 2 V)
    (hVO : V ≤ normalizer (O : Set G)) (hO : Odd (Nat.card O)) (hzV : z ∈ V) (hdV : d ∈ V)
    (hz2 : z * z = 1) (hd2 : d * d = 1) (hC : ∀ x ∈ O, z * x = x * z → x ^ 3 = 1)
    (h5 : 5 ∣ Nat.card O) :
    ∃ e, (e = d ∨ e = z * d) ∧ ∃ h ∈ O, orderOf h = 5 ∧ e * h = h * e := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨S, hSO, hSp, hScard, hVS⟩ := exists_invariant_sylow_five hV hVO hO
  have hSne : S ≠ ⊥ := by
    intro hS
    have hk : 0 < (Nat.card O).factorization 5 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_five Nat.card_pos.ne' h5
    have h1 : Nat.card S = 1 := by rw [hS]; exact Subgroup.card_bot
    rw [hScard] at h1
    exact absurd (Nat.pow_eq_one.mp h1) (by simp [hk.ne'])
  by_cases hd : S ⊓ centralizer ({d} : Set G) = ⊥
  ·
    have hfix5 : ∀ x ∈ S, orderOf x ∣ 3 → x = 1 := by
      intro x hx h3
      obtain ⟨k, hk⟩ := hSp ⟨x, hx⟩
      have h5k : orderOf x ∣ 5 ^ k := by
        rw [← Subgroup.orderOf_mk x hx]; exact orderOf_dvd_of_pow_eq_one hk
      have : orderOf x ∣ Nat.gcd 3 (5 ^ k) := Nat.dvd_gcd h3 h5k
      rw [Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 5)] at this
      exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp this)
    have hzS : ∀ a ∈ S, z * a * z⁻¹ ∈ S := fun a ha => (mem_normalizer_iff.1 (hVS hzV) a).1 ha
    have hdS : ∀ a ∈ S, d * a * d⁻¹ ∈ S := fun a ha => (mem_normalizer_iff.1 (hVS hdV) a).1 ha
    have hzinv := Close.inv_of_fpf hz2 hzS fun x hx hfx => by
      apply hfix5 x hx
      apply orderOf_dvd_of_pow_eq_one
      apply hC x (hSO hx)
      calc z * x = z * x * z⁻¹ * z := by group
        _ = x * z := by rw [hfx]
    have hdinv := Close.inv_of_fpf hd2 hdS fun x hx hfx => by
      have : x ∈ S ⊓ centralizer ({d} : Set G) := Subgroup.mem_inf.mpr ⟨hx, by
        rw [mem_centralizer_singleton_iff]
        calc x * d = d * x * d⁻¹ * d := by rw [hfx]
          _ = d * x := by group⟩
      rw [hd, mem_bot] at this; exact this
    obtain ⟨h, hh, ho⟩ := exists_order_five hSp hSne
    refine ⟨z * d, Or.inr rfl, h, hSO hh, ho, ?_⟩
    have h1 : (z * d) * h * (z * d)⁻¹ = h := by
      calc (z * d) * h * (z * d)⁻¹ = z * (d * h * d⁻¹) * z⁻¹ := by group
        _ = z * h⁻¹ * z⁻¹ := by rw [hdinv h hh]
        _ = (z * h * z⁻¹)⁻¹ := by group
        _ = h := by rw [hzinv h hh, inv_inv]
    calc (z * d) * h = (z * d) * h * (z * d)⁻¹ * (z * d) := by group
      _ = h * (z * d) := by rw [h1]
  · obtain ⟨h, hhSd, ho⟩ := exists_order_five (hSp.to_le inf_le_left) hd
    obtain ⟨hhS, hhd⟩ := Subgroup.mem_inf.mp hhSd
    refine ⟨d, Or.inl rfl, h, hSO hhS, ho, ?_⟩
    rw [mem_centralizer_singleton_iff] at hhd
    exact hhd.symm

end CFSG.EvenSporadicStandard.RuStd.S2
