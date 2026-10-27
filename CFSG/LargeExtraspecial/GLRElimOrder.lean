module

public import CFSG.LargeExtraspecial.GLRSplitDemp
public import CFSG.LargeExtraspecial.GLRCent

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLR

open Subgroup Module CFSG.GroupTheory.GLnTwoSplitting
open scoped IsMulCommutative

theorem card_comap_of_surjective {H K : Type*} [Group H] [Group K] [Finite H] {f : H →* K}
    (hf : Function.Surjective f) (L : Subgroup K) :
    Nat.card (L.comap f) = Nat.card f.ker * Nat.card L := by
  have : Finite K := Finite.of_surjective f hf
  have h1 := card_mul_index (L.comap f)
  rw [index_comap_of_surjective L hf] at h1
  have h2 := card_mul_index L
  have h3 : Nat.card H = Nat.card f.ker * Nat.card K := by
    rw [card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv, mul_comm]
  have hidx : L.index ≠ 0 := index_ne_zero_of_finite
  rw [h3, ← h2] at h1
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hidx) (by rw [h1]; ring)

theorem centExp_lt_choose {N : ℕ} (hN : 6 ≤ N) :
    2 + 2 * ((N - 1) / 2) + ((N - 1) / 2) ^ 2 < N * (N - 1) / 2 := by
  have hs := mul_pred_div_two_mul_two N
  set s := N * (N - 1) / 2
  obtain ⟨M, hM | hM⟩ : ∃ M, N = 2 * M + 1 ∨ N = 2 * M + 2 := ⟨(N - 1) / 2, by omega⟩
  · have hM' : (N - 1) / 2 = M := by omega
    rw [hM']
    subst hM
    have e1 : 2 * M + 1 - 1 = 2 * M := by omega
    rw [e1] at hs
    have hM3 : 3 ≤ M := by omega
    nlinarith
  · have hM' : (N - 1) / 2 = M := by omega
    rw [hM']
    subst hM
    have e1 : 2 * M + 2 - 1 = 2 * M + 1 := by omega
    rw [e1] at hs
    have hM2 : 2 ≤ M := by omega
    nlinarith

namespace Config

variable {G : Type*} [Group G] [Finite G] {S : Setting G} (C : Config S)

theorem conjLinear_eq_one_iff_mem {x : C.N} : conjLinear C.AN x = 1 ↔ (x : G) ∈ C.A := by
  rw [conjLinear_eq_one_iff C.AN C.centralizer_AN_le x]
  constructor
  · rintro ⟨e, rfl⟩
    exact (Additive.toMul e).2
  · intro hx
    exact ⟨Additive.ofMul ⟨x, hx⟩, rfl⟩

theorem lt_factorization_card_centralizer (h5 : 5 ≤ S.width) {y : G} (hyN : y ∈ C.N)
    (hy : y * y = 1) :
    2 + 2 * (S.width / 2) + (S.width / 2) ^ 2 < (Nat.card (centralizer {y})).factorization 2 := by
  classical
  have hπ : Function.Surjective (conjLinear C.AN) := C.natExt.surjective
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
  · rw [hr0] at hv
    have := centExp_lt_choose (N := S.width + 1) (by omega)
    simp only [Nat.add_sub_cancel, Nat.zero_mul, Nat.zero_div, add_zero] at this hv
    omega
  · have := centExp_lt_of_add_eq (N := S.width + 1) (by omega) hr1 hr2 hv
    simp only [Nat.add_sub_cancel] at this
    omega

end Config

end CFSG.LargeExtraspecial.GLR
