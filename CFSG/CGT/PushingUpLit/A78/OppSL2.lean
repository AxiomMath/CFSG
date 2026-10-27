module

public import CFSG.Timmesfeld.ARS.BasicRankOne
public import CFSG.Timmesfeld.ARS.NaturalModule

public section

namespace CFSG.CGT.PushingUpLit.A78

open CFSG.Timmesfeld CFSG.Timmesfeld.ARS CFSG.Timmesfeld.RankOne
  CFSG.Timmesfeld.ARS.NaturalModule
open scoped MatrixGroups

section Model

variable (K : Type*) [Field K] [CharP K 2]

theorem lowerElt_inv_eq {s : K} (hs : s ≠ 0) :
    lowerElt K s⁻¹ = upperElt K s * diagElt (Units.mk0 s hs) * weylElt K * upperElt K s := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_upperElt, coe_diagElt, coe_weylElt, coe_lowerElt, Matrix.mul_apply,
      Fin.sum_univ_two] <;>
    first
      | exact (mul_inv_cancel₀ hs).symm
      | exact (inv_mul_cancel₀ hs).symm
      | exact (CharTwo.add_self_eq_zero s).symm

theorem map_conj_weylElt_upper :
    (upperUnipotent K).map (MulAut.conj (weylElt K)).toMonoidHom = lowerUnipotent K := by
  ext g
  rw [RankOne.mem_map_conj, (inv_eq_of_mul_eq_one_right (weylElt_mul_self (K := K))),
    RankOne.mem_upperUnipotent_iff, RankOne.mem_lowerUnipotent_iff]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [← weylElt_mul_upperElt_mul_weylElt, ← ht]
    calc g = weylElt K * weylElt K * g * (weylElt K * weylElt K) := by
          rw [weylElt_mul_self, one_mul, mul_one]
      _ = weylElt K * (weylElt K * g * weylElt K) * weylElt K := by group
  · rintro ⟨t, rfl⟩
    refine ⟨t, ?_⟩
    rw [← weylElt_mul_upperElt_mul_weylElt]
    simp only [← mul_assoc, weylElt_mul_self, one_mul]
    rw [mul_assoc, weylElt_mul_self, mul_one]

theorem map_conj_upper_lowerElt_inv {s : K} (hs : s ≠ 0) :
    (upperUnipotent K).map (MulAut.conj (lowerElt K s⁻¹)).toMonoidHom =
      (lowerUnipotent K).map (MulAut.conj (upperElt K s)).toMonoidHom := by
  have hU : (upperUnipotent K).map (MulAut.conj (upperElt K s)).toMonoidHom = upperUnipotent K :=
    RankOne.map_conj_of_mem ((RankOne.mem_upperUnipotent_iff K).2 ⟨s, rfl⟩)
  have hD : (lowerUnipotent K).map (MulAut.conj (diagElt (Units.mk0 s hs))).toMonoidHom =
      lowerUnipotent K :=
    RankOne.map_conj_eq_self_iff.2 (diagElt_mem_normalizer_lowerUnipotent _)
  rw [lowerElt_inv_eq K hs, RankOne.map_conj_mul, hU, RankOne.map_conj_mul,
    map_conj_weylElt_upper, RankOne.map_conj_mul, hD]

theorem isElemAbRankOne_upper_lower :
    IsElemAbRankOne (upperUnipotent K) (lowerUnipotent K) := by
  refine ⟨upperUnipotent_sup_lowerUnipotent, RankOne.upperUnipotent_ne_lowerUnipotent K,
    fun x hx y hy => ?_, fun x hx => ?_, fun x hx hx1 => ?_, fun y hy hy1 => ?_⟩
  · obtain ⟨s, rfl⟩ := (RankOne.mem_upperUnipotent_iff K).1 hx
    obtain ⟨t, rfl⟩ := (RankOne.mem_upperUnipotent_iff K).1 hy
    rw [Commute, SemiconjBy, RankOne.upperElt_mul, RankOne.upperElt_mul, add_comm]
  · obtain ⟨s, rfl⟩ := (RankOne.mem_upperUnipotent_iff K).1 hx
    exact upperElt_mul_self s
  · obtain ⟨s, rfl⟩ := (RankOne.mem_upperUnipotent_iff K).1 hx
    have hs : s ≠ 0 := fun h0 => hx1 (by rw [h0, RankOne.upperElt_zero])
    refine ⟨RankOne.lowerElt K s⁻¹, (RankOne.mem_lowerUnipotent_iff K).2 ⟨s⁻¹, rfl⟩,
      fun h' => ?_, map_conj_upper_lowerElt_inv K hs⟩
    rw [← RankOne.lowerElt_zero] at h'
    exact inv_ne_zero hs (RankOne.lowerElt_injective K h')
  · obtain ⟨t, rfl⟩ := (RankOne.mem_lowerUnipotent_iff K).1 hy
    have ht : t ≠ 0 := fun h0 => hy1 (by rw [h0, RankOne.lowerElt_zero])
    refine ⟨RankOne.upperElt K t⁻¹, (RankOne.mem_upperUnipotent_iff K).2 ⟨t⁻¹, rfl⟩,
      fun h' => ?_, ?_⟩
    · rw [← RankOne.upperElt_zero] at h'
      exact inv_ne_zero ht (RankOne.upperElt_injective K h')
    · have := map_conj_upper_lowerElt_inv K (inv_ne_zero ht)
      rw [inv_inv] at this
      exact this.symm

end Model

section Transport

variable {Y G : Type*} [Group Y] [Group G]

theorem opposite_map_of_injective (ψ : Y →* G) (hψ : Function.Injective ψ) {A B : Subgroup Y}
    (h : Opposite A B) : Opposite (A.map ψ) (B.map ψ) := by
  have key : ∀ (H : Subgroup Y) (g : Y), conjSub (H.map ψ) (ψ g) = (conjSub H g).map ψ :=
    fun H g => (RankOne.map_map_conj ψ H g).symm
  refine ⟨fun hAB => h.1 (Subgroup.map_injective hψ hAB), ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ ha1
    obtain ⟨b, hb, hb1, hab⟩ := h.2.1 a ha (fun h1 => ha1 (by rw [h1, map_one]))
    refine ⟨ψ b, ⟨b, hb, rfl⟩, fun h1 => hb1 (hψ (by rw [h1, map_one])), ?_⟩
    rw [key, key, hab]
  · rintro _ ⟨b, hb, rfl⟩ hb1
    obtain ⟨a, ha, ha1, hab⟩ := h.2.2 b hb (fun h1 => hb1 (by rw [h1, map_one]))
    refine ⟨ψ a, ⟨a, ha, rfl⟩, fun h1 => ha1 (hψ (by rw [h1, map_one])), ?_⟩
    rw [key, key, hab]

theorem opposite_conjSub' {A B : Subgroup Y} (h : Opposite A B) (g : Y) :
    Opposite (conjSub A g) (conjSub B g) :=
  opposite_map_of_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective h

end Transport

section SL2

variable {e : ℕ}

theorem card_upperUnipotent_gf (he : e ≠ 0) :
    Nat.card (upperUnipotent (GaloisField 2 e)) = 2 ^ e := by
  rw [RankOne.card_upperUnipotent, GaloisField.card 2 e he]

theorem opposite_of_card_eq_SL2 (he : e ≠ 0) {A B : Subgroup SL(2, GaloisField 2 e)}
    (hA : Nat.card A = 2 ^ e) (hB : Nat.card B = 2 ^ e) (hAB : A ≠ B) : Opposite A B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := isElemAbRankOne_upper_lower (GaloisField 2 e)
  have hU := card_upperUnipotent_gf he
  obtain ⟨x, hx⟩ := ElemAbRankOne.exists_eq_map_conj h (IsPGroup.of_card hA) (hA.trans hU.symm)
  obtain ⟨y, hy⟩ := ElemAbRankOne.exists_eq_map_conj h (IsPGroup.of_card hB) (hB.trans hU.symm)
  have hopp : Opposite (upperUnipotent (GaloisField 2 e)) (lowerUnipotent (GaloisField 2 e)) :=
    ⟨h.ne, h.moufang, h.moufang'⟩
  have hne : conjSub (upperUnipotent (GaloisField 2 e)) (x⁻¹ * y) ≠
      upperUnipotent (GaloisField 2 e) := by
    intro heq
    apply hAB
    have h1 := conjSub_mul (upperUnipotent (GaloisField 2 e)) x (x⁻¹ * y)
    rw [mul_inv_cancel_left, heq] at h1
    rw [hx, hy]
    exact h1.symm
  obtain ⟨a, ha, hUa⟩ := h.exists_eq_of_map_conj_ne hne
  have hz : Opposite (upperUnipotent (GaloisField 2 e))
      (conjSub (upperUnipotent (GaloisField 2 e)) (x⁻¹ * y)) := by
    have := opposite_conjSub' hopp a
    rw [conjSub_of_mem ha] at this
    change Opposite _ (Subgroup.map (MulAut.conj (x⁻¹ * y)).toMonoidHom _)
    rw [hUa]
    exact this
  have := opposite_conjSub' hz x
  rw [← conjSub_mul, mul_inv_cancel_left] at this
  rw [hx, hy]
  exact this

end SL2

section Sylow

variable {G : Type*} [Group G] {K : Subgroup G} {e : ℕ}

theorem opposite_of_sylow_sl2 {A B : Subgroup G} (he : 2 ≤ e)
    (φ : ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e)) (hA : A ≤ K) (hB : B ≤ K)
    (hAc : Nat.card A = 2 ^ e) (hBc : Nat.card B = 2 ^ e) (hAB : A ≠ B) : Opposite A B := by
  let ψ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e) →* G :=
    K.subtype.comp φ.symm.toMonoidHom
  have hψ : Function.Injective ψ := K.subtype_injective.comp φ.symm.injective
  have hψφ : ψ.comp φ.toMonoidHom = K.subtype := by
    ext x
    simp [ψ]
  have hmap : ∀ {C : Subgroup G}, C ≤ K → ((C.subgroupOf K).map φ.toMonoidHom).map ψ = C := by
    intro C hC
    rw [Subgroup.map_map, hψφ, Subgroup.subgroupOf_map_subtype, inf_of_le_left hC]
  have hcard : ∀ {C : Subgroup G}, C ≤ K → Nat.card ((C.subgroupOf K).map φ.toMonoidHom) =
      Nat.card C := fun {C} hC => by
    rw [Subgroup.card_map_of_injective φ.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hC).toEquiv
  have hne : (A.subgroupOf K).map φ.toMonoidHom ≠ (B.subgroupOf K).map φ.toMonoidHom := by
    intro h
    apply hAB
    rw [← hmap hA, ← hmap hB, h]
  have h := opposite_of_card_eq_SL2 (by omega) ((hcard hA).trans hAc) ((hcard hB).trans hBc) hne
  have := opposite_map_of_injective ψ hψ h
  rwa [hmap hA, hmap hB] at this

theorem ncard_sylow_sl2 (he : 2 ≤ e)
    (φ : ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e)) :
    {P : Subgroup G | P ≤ K ∧ Nat.card P = 2 ^ e}.ncard = 2 ^ e + 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := isElemAbRankOne_upper_lower (GaloisField 2 e)
  have hU := card_upperUnipotent_gf (e := e) (by omega)
  let ψ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e) →* G :=
    K.subtype.comp φ.symm.toMonoidHom
  have hψ : Function.Injective ψ := K.subtype_injective.comp φ.symm.injective
  have hψφ : ψ.comp φ.toMonoidHom = K.subtype := by
    ext x
    simp [ψ]
  have hrange : ψ.range = K := by
    rw [MonoidHom.range_eq_map]
    ext g
    constructor
    · rintro ⟨x, -, rfl⟩
      exact (φ.symm x).2
    · intro hg
      exact ⟨φ ⟨g, hg⟩, Subgroup.mem_top _, by simp [ψ]⟩
  have hS : {P : Subgroup G | P ≤ K ∧ Nat.card P = 2 ^ e} =
      Subgroup.map ψ '' {Q : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e)) |
        Nat.card Q = 2 ^ e} := by
    ext P
    constructor
    · rintro ⟨hPK, hPc⟩
      refine ⟨(P.subgroupOf K).map φ.toMonoidHom, ?_, ?_⟩
      · show Nat.card ((P.subgroupOf K).map φ.toMonoidHom) = 2 ^ e
        rw [Subgroup.card_map_of_injective φ.injective, ← hPc]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPK).toEquiv
      · rw [Subgroup.map_map, hψφ, Subgroup.subgroupOf_map_subtype, inf_of_le_left hPK]
    · rintro ⟨Q, hQ, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [← hrange]
        exact (Subgroup.map_le_range ψ Q)
      · rw [Subgroup.card_map_of_injective hψ]
        exact hQ
  have hQ : {Q : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e)) |
      Nat.card Q = 2 ^ e} = Set.range (RankOne.Point.val : RankOne.Point
        (upperUnipotent (GaloisField 2 e)) → _) := by
    ext Q
    constructor
    · intro hQ
      obtain ⟨x, hx⟩ := ElemAbRankOne.exists_eq_map_conj h (IsPGroup.of_card hQ)
        (hQ.trans hU.symm)
      exact ⟨⟨Q, x, hx⟩, rfl⟩
    · rintro ⟨C, rfl⟩
      obtain ⟨g, hg⟩ := C.exists_eq
      show Nat.card C.val = 2 ^ e
      rw [hg, Subgroup.card_map_of_injective (MulAut.conj g).injective, hU]
  rw [hS, Set.ncard_image_of_injective _ (Subgroup.map_injective hψ), hQ,
    ← Nat.card_coe_set_eq, Nat.card_range_of_injective (fun C D hCD => RankOne.Point.ext hCD),
    h.card_point, hU]

end Sylow

end CFSG.CGT.PushingUpLit.A78
