module

public import CFSG.LargeExtraspecial.GLRElimMain
public import CFSG.LargeExtraspecial.S3Eight

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLW4

open Subgroup Module CFSG.GroupTheory.GLnTwoSplitting CFSG.LargeExtraspecial.GLR
open scoped IsMulCommutative

variable {G : Type*} [Group G] [Finite G] {S : Setting G} (C : Config S)

theorem card_M_eq : Nat.card S.M = Nat.card S.Q * Nat.card S.Mbar := by
  rw [card_eq_card_quotient_mul_card_subgroup S.ρ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange S.ρ).toEquiv, S.ker_ρ, mul_comm]
  rfl

include C in
theorem factorization_card_M (h4 : S.width = 4) : (Nat.card S.M).factorization 2 = 16 := by
  have hM := card_M_eq (S := S)
  have hMbar : Nat.card S.Mbar = 2 * Nat.card C.Xbar := by
    have := relIndex_mul_card C.Xbar S.Mbar
    rw [C.relIndex_Xbar, inf_eq_left.mpr C.Xbar_le] at this
    exact this.symm
  rw [hM, hMbar, C.card_Xbar, S.card_Q_eq, h4]
  have hGL := factorization_card_GL_zmod_two 4
  have h0 : Nat.card (GL (Fin 4) (ZMod 2)) ≠ 0 := Nat.card_pos.ne'
  rw [Nat.factorization_mul (by positivity) (by positivity), Nat.factorization_mul (by norm_num) h0,
    Finsupp.add_apply, Finsupp.add_apply, hGL, Nat.Prime.factorization_pow Nat.prime_two,
    Finsupp.single_eq_same, Nat.Prime.factorization_self Nat.prime_two]
  norm_num

include C in
theorem factorization_card_centralizer_of_mem_A (h4 : S.width = 4) {y : G} (hyA : y ∈ C.A) :
    16 ≤ (Nat.card (centralizer {y})).factorization 2 := by
  have hM := factorization_card_M C h4
  have hle : ∀ H : Subgroup G, S.M ≤ H → 16 ≤ (Nat.card H).factorization 2 := fun H hH => by
    rw [← hM]
    exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
      (card_dvd_of_le hH) 2
  have hyQ : y ∈ S.QG := C.A_le_QG hyA
  by_cases h01 : y = 1 ∨ y = S.z
  · rcases h01 with rfl | rfl
    · exact hle _ fun g _ => mem_centralizer_singleton_iff.mpr (by rw [mul_one, one_mul])
    · exact le_of_eq hM.symm
  push Not at h01
  have hcl : S.cl y ≠ 0 := fun h => by
    rcases (S.cl_eq_zero_iff hyQ).mp h with h | h
    exacts [h01.1 h, h01.2 h]
  obtain ⟨k, hkQ, hk⟩ := C.conj_At (S.cl y) hyA.2 hcl
  obtain ⟨w, hw⟩ : ∃ w : G, w * S.z * w⁻¹ = y := by
    rcases (S.cl_eq_cl_iff hkQ hyQ).mp hk with h | h
    · exact ⟨k, h.symm⟩
    · have ht1 : k * S.z * k⁻¹ ≠ 1 := fun h' => by
        apply hcl; rw [← hk, h', S.cl_one]
      have htz : k * S.z * k⁻¹ ≠ S.z := fun h' => by
        apply hcl; rw [← hk, h', S.cl_z]
      obtain ⟨u, -, hu⟩ := S.exists_conj_eq_mul_z hkQ ht1 htz
      refine ⟨u * k, ?_⟩
      rw [show u * k * S.z * (u * k)⁻¹ = u * (k * S.z * k⁻¹) * u⁻¹ by group, hu, h]
  have hc := card_centralizer_conj w⁻¹ S.z
  rw [inv_inv, hw] at hc
  rw [hc]
  exact le_of_eq hM.symm

theorem lt_factorization_card_centralizer_four (h4 : S.width = 4) {y : G} (hyN : y ∈ C.N)
    (hy : y * y = 1) : 10 < (Nat.card (centralizer {y})).factorization 2 := by
  classical
  by_cases hyA : y ∈ C.A
  · exact lt_of_lt_of_le (by norm_num) (factorization_card_centralizer_of_mem_A C h4 hyA)
  · have hπ : Function.Surjective (conjLinear C.AN) := C.natExt.surjective
    have : Finite (Additive C.AN ≃ₗ[ZMod 2] Additive C.AN) :=
      Finite.of_injective (fun e : Additive C.AN ≃ₗ[ZMod 2] Additive C.AN =>
        (e : Additive C.AN → Additive C.AN)) fun _ _ h => LinearEquiv.ext (congrFun h)
    set yN : C.N := ⟨y, hyN⟩ with hyNdef
    set g := conjLinear C.AN yN with hgdef
    have hg : g * g = 1 := by
      rw [hgdef, ← map_mul, show yN * yN = 1 from Subtype.ext hy, map_one]
    set r := finrank (ZMod 2)
      (LinearMap.range ((g : Additive C.AN →ₗ[ZMod 2] Additive C.AN) - LinearMap.id)) with hr
    have hv := factorization_card_centralizer_involution_add hg C.finrank_AN hr.symm
    have hr2 := two_mul_rank_le_of_involution hg C.finrank_AN hr.symm
    set P : Subgroup C.N := (centralizer {g}).comap (conjLinear C.AN) with hP
    have hker : (conjLinear C.AN).ker = C.AN := by
      ext x
      rw [MonoidHom.mem_ker, C.conjLinear_eq_one_iff_mem]
      rfl
    have hcardP : Nat.card P = 2 ^ (S.width + 1) * Nat.card (centralizer {g}) := by
      rw [hP, card_comap_of_surjective hπ, hker, C.card_AN]
    let ι : Additive C.AN → G := fun e => (((Additive.toMul e : C.AN) : C.N) : G)
    let K := LinearMap.ker ((g : Additive C.AN →ₗ[ZMod 2] Additive C.AN) - LinearMap.id)
    let Ω : Set G := (fun e : K => y * ι e) '' Set.univ
    have hΩ : ∀ k ∈ P.map C.N.subtype, k * y * k⁻¹ ∈ Ω := by
      rintro _ ⟨p, hp, rfl⟩
      have hpc : conjLinear C.AN p * g = g * conjLinear C.AN p :=
        mem_centralizer_singleton_iff.mp hp
      have ha' : (p : G) * y * (p : G)⁻¹ * y⁻¹ ∈ C.A := by
        have h1 : conjLinear C.AN (p * yN * p⁻¹ * yN⁻¹) = 1 := by
          rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hgdef, hpc, mul_inv_cancel_right,
            mul_inv_cancel]
        exact (C.conjLinear_eq_one_iff_mem).mp h1
      set a := y⁻¹ * ((p : G) * y * (p : G)⁻¹ * y⁻¹) * y with ha
      have haA : a ∈ C.A := by
        have := (mem_normalizer_iff.mp (C.N.inv_mem hyN) _).mp ha'
        rwa [inv_inv] at this
      have hkya : (p : G) * y * (p : G)⁻¹ = y * a := by rw [ha]; group
      have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
      have hya : y * a * y⁻¹ = a := by
        have h1 : (y * a) * (y * a) = 1 := by
          rw [← hkya]
          calc (p : G) * y * (p : G)⁻¹ * ((p : G) * y * (p : G)⁻¹)
              = (p : G) * (y * y) * (p : G)⁻¹ := by group
            _ = 1 := by rw [hy, mul_one, mul_inv_cancel]
        have h2 : y * a * y = a⁻¹ := by
          rw [← mul_assoc] at h1
          exact eq_inv_of_mul_eq_one_left h1
        rw [hyinv, h2]
        exact inv_eq_of_mul_eq_one_right (C.A_mul_self haA)
      let e : Additive C.AN := Additive.ofMul ⟨⟨a, C.A_le_N haA⟩, haA⟩
      have he : e ∈ K := by
        rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
        refine Additive.toMul.injective (Subtype.ext (Subtype.ext ?_))
        change (((Additive.toMul (conjLinear C.AN yN e) : C.AN) : C.N) : G) = a
        rw [coe_conjLinear_apply]
        exact hya
      exact ⟨⟨e, he⟩, Set.mem_univ _, hkya.symm⟩
    have hfinK : finrank (ZMod 2) K = S.width + 1 - r := by
      have h1 := LinearMap.finrank_range_add_finrank_ker
        ((g : Additive C.AN →ₗ[ZMod 2] Additive C.AN) - LinearMap.id)
      rw [C.finrank_AN, ← hr] at h1
      change r + finrank (ZMod 2) K = S.width + 1 at h1
      omega
    have hΩcard : Ω.ncard ≤ 2 ^ (S.width + 1 - r) := by
      calc Ω.ncard ≤ (Set.univ : Set K).ncard := Set.ncard_image_le
        _ = Nat.card K := Set.ncard_univ K
        _ = 2 ^ (S.width + 1 - r) := by
          rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hfinK]
    have key := factorization_card_le_add_centralizer Nat.prime_two (K := P.map C.N.subtype)
      (Set.toFinite Ω) hΩ hΩcard
    rw [card_map_of_injective C.N.subtype_injective, hcardP,
      Nat.factorization_mul (pow_ne_zero _ two_ne_zero) Nat.card_pos.ne', Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same] at key
    have hle : (Nat.card ↥(P.map C.N.subtype ⊓ centralizer {y})).factorization 2 ≤
        (Nat.card (centralizer {y})).factorization 2 :=
      (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
        (card_dvd_of_le inf_le_right) 2
    rcases Nat.eq_zero_or_pos r with hr0 | hr1
    · exfalso
      apply hyA
      have hg1 : g = 1 := by
        have hr0' : LinearMap.range
            ((g : Additive C.AN →ₗ[ZMod 2] Additive C.AN) - LinearMap.id) = ⊥ :=
          Submodule.finrank_eq_zero.mp (hr.symm.trans hr0)
        refine LinearEquiv.ext fun v => ?_
        have hv0 := LinearMap.range_eq_bot.mp hr0'
        have := LinearMap.congr_fun hv0 v
        rw [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.zero_apply, sub_eq_zero] at this
        exact this
      exact (C.conjLinear_eq_one_iff_mem).mp (hgdef ▸ hg1)
    · have := centExp_lt_of_add_eq (N := S.width + 1) (by omega) hr1 hr2 hv
      simp only [Nat.add_sub_cancel] at this
      rw [h4] at this
      omega

end CFSG.LargeExtraspecial.GLW4
