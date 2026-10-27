module

public import CFSG.ClassicalGroups.PCoreSection
public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.Permutable
public import CFSG.Walter.W67.Section6.Util

public section

namespace CFSG.GroupTheory

open Subgroup
open scoped Pointwise commutatorElement

variable {H : Type}

private theorem eq_one_or_self_of_mem_zpowers_of_mul_self_eq_one [Group H] {s : H}
    (hs2 : s * s = 1) {y : H} (hy : y ∈ Subgroup.zpowers s) : y = 1 ∨ y = s := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have h2 : s ^ (2 : ℤ) = 1 := by
    rw [zpow_ofNat, pow_two]
    exact hs2
  rcases Int.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
  · left
    rw [hm, show m + m = 2 * m by ring, zpow_mul, h2, one_zpow]
  · right
    rw [hm, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem inv_of_mem_commutator_zpowers_of_sq_centralizes [Group H] {A : Subgroup H}
    [IsMulCommutative ↥A] {s : H} (hsN : s ∈ Subgroup.normalizer (A : Set H))
    (hsα : ∀ a ∈ A, s * (s * a * s⁻¹) * s⁻¹ = a) :
    ∀ x ∈ ⁅A, Subgroup.zpowers s⁆, s * x * s⁻¹ = x⁻¹ := by
  classical
  let α : MulAut ↥A := Subgroup.normalizerMonoidHom A ⟨s, hsN⟩
  have hαcoe : ∀ a : ↥A, ((α a : ↥A) : H) = s * (a : H) * s⁻¹ := fun a =>
    Subgroup.normalizerMonoidHom_apply_apply_coe A ⟨s, hsN⟩ a
  have hα2 : α * α = 1 := by
    ext a
    rw [MulAut.mul_apply, hαcoe, hαcoe, hsα a a.2]
    rfl
  let φ : ↥(Subgroup.zpowers s) →* MulAut ↥A :=
    (Subgroup.normalizerMonoidHom A).comp (Subgroup.inclusion (Subgroup.zpowers_le.mpr hsN))
  have hφs : φ ⟨s, Subgroup.mem_zpowers s⟩ = α := rfl
  have hφcoe : ∀ (y : ↥(Subgroup.zpowers s)) (a : ↥A),
      (((φ y) a : ↥A) : H) = (y : H) * (a : H) * (y : H)⁻¹ := by
    intro y a
    have hy' : ((y : H) ∈ Subgroup.normalizer (A : Set H)) :=
      Subgroup.zpowers_le.mpr hsN y.2
    have hcoe := Subgroup.normalizerMonoidHom_apply_apply_coe A ⟨(y : H), hy'⟩ a
    simpa [φ] using hcoe
  let D : Subgroup H :=
    { carrier := {x | x ∈ A ∧ s * x * s⁻¹ = x⁻¹}
      one_mem' := by simp
      mul_mem' := by
        rintro x y ⟨hxA, hx⟩ ⟨hyA, hy⟩
        refine ⟨A.mul_mem hxA hyA, ?_⟩
        have hcomm : x * y = y * x := congrArg Subtype.val
          ((IsMulCommutative.is_comm (M := ↥A)).comm ⟨x, hxA⟩ ⟨y, hyA⟩)
        calc s * (x * y) * s⁻¹ = (s * x * s⁻¹) * (s * y * s⁻¹) := by group
          _ = x⁻¹ * y⁻¹ := by rw [hx, hy]
          _ = (x * y)⁻¹ := by
            rw [mul_inv_rev]
            simpa [mul_inv_rev] using (congrArg Inv.inv hcomm).symm
      inv_mem' := by
        rintro x ⟨hxA, hx⟩
        refine ⟨A.inv_mem hxA, ?_⟩
        calc s * x⁻¹ * s⁻¹ = (s * x * s⁻¹)⁻¹ := by group
          _ = (x⁻¹)⁻¹ := by rw [hx] }
  have hBleD : ⁅A, Subgroup.zpowers s⁆ ≤ D := by
    rw [Subgroup.commutator_le]
    intro a ha y hy
    let ys : ↥(Subgroup.zpowers s) := ⟨y, hy⟩
    have hφmem : φ ys ∈ Subgroup.zpowers α := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hys : ys = (⟨s, Subgroup.mem_zpowers s⟩ : ↥(Subgroup.zpowers s)) ^ k := by
        apply Subtype.ext
        simpa using hk.symm
      rw [hys, map_zpow, hφs]
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩
    rcases eq_one_or_self_of_mem_zpowers_of_mul_self_eq_one hα2 hφmem with h1 | h2
    · have hyfix : y * a * y⁻¹ = a := by
        have h := hφcoe ys ⟨a, ha⟩
        rw [h1] at h
        simpa using h.symm
      have hcomm1 : ⁅a, y⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_commute]
        show a * y = y * a
        calc a * y = (y * a * y⁻¹) * y := by rw [hyfix]
          _ = y * a := by group
      rw [hcomm1]
      exact D.one_mem
    · have hya : y * a * y⁻¹ = s * a * s⁻¹ := by
        have h := hφcoe ys ⟨a, ha⟩
        rw [h2] at h
        simpa [hαcoe] using h.symm
      have heq : ⁅a, y⁆ = a * (s * a * s⁻¹)⁻¹ := by
        rw [show ⁅a, y⁆ = a * (y * a * y⁻¹)⁻¹ from by
          rw [commutatorElement_def, mul_inv_rev, mul_inv_rev, inv_inv]
          group]
        rw [hya]
      have hmemA : a * (s * a * s⁻¹)⁻¹ ∈ A :=
        A.mul_mem ha (A.inv_mem ((Subgroup.mem_normalizer_iff.mp hsN a).mp ha))
      refine ⟨?_, ?_⟩
      · rwa [heq]
      · rw [heq]
        have hback : s * (s * a * s⁻¹) * s⁻¹ = a := hsα a ha
        have hinvu : s * (s * a * s⁻¹)⁻¹ * s⁻¹ = a⁻¹ := by
          calc
            s * (s * a * s⁻¹)⁻¹ * s⁻¹ = (s * (s * a * s⁻¹) * s⁻¹)⁻¹ := by
              group
              rw [zpow_two]
            _ = a⁻¹ := by rw [hback]
        calc s * (a * (s * a * s⁻¹)⁻¹) * s⁻¹
            = (s * a * s⁻¹) * (s * (s * a * s⁻¹)⁻¹ * s⁻¹) := by group
          _ = (s * a * s⁻¹) * a⁻¹ := by rw [hinvu]
          _ = (a * (s * a * s⁻¹)⁻¹)⁻¹ := by
            rw [mul_inv_rev, mul_inv_rev, inv_inv]
            group
  intro x hx
  exact (hBleD hx).2

private theorem setup_pCoreOf_relIndex_two [Group H] [Finite H] {A S : Subgroup H}
    (hAodd : Odd (Nat.card A)) (hS2 : IsPGroup 2 S)
    (hAS : (A : Set H) * S = S * A)
    (hQrel : (CFSG.Open.pCoreOf 2 (A ⊔ S)).relIndex S = 2) :
    (A ⊔ S ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (A ⊔ S) : Set H)) ∧
      (A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (A ⊔ S) : Set H)) ∧
      A ⊓ CFSG.Open.pCoreOf 2 (A ⊔ S) = ⊥ ∧
      A ⊓ S = ⊥ ∧
      Nat.card ↥(A ⊔ S) = Nat.card A * Nat.card S ∧
      S.relIndex (A ⊔ S) = Nat.card A ∧
      CFSG.Open.pCoreOf 2 (A ⊔ S) ≤ S := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let X : Subgroup H := A ⊔ S
  let Q : Subgroup H := CFSG.Open.pCoreOf 2 X
  have hAX : A ≤ X := le_sup_left
  have hSX : S ≤ X := le_sup_right
  have hQX : Q ≤ X := CFSG.ClassicalGroups.PCoreSection.pCoreOf_le 2 X
  have hQ2 : IsPGroup 2 Q := CFSG.ClassicalGroups.PCoreSection.isPGroup_pCoreOf 2 X
  have hQnX : X ≤ Subgroup.normalizer (Q : Set H) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact CFSG.ClassicalGroups.PCoreSection.conj_mem_pCoreOf hx hy
    · intro hy
      have h1 := CFSG.ClassicalGroups.PCoreSection.conj_mem_pCoreOf (X.inv_mem hx) hy
      have h1' : x⁻¹ * (x * y * x⁻¹) * (x⁻¹)⁻¹ ∈ Q := by
        simpa [MulAut.conj_apply] using h1
      have h2 : x⁻¹ * (x * y * x⁻¹) * (x⁻¹)⁻¹ = y := by group
      rwa [h2] at h1'
  have hAnormQ : A ≤ Subgroup.normalizer (Q : Set H) := fun a ha => hQnX (hAX ha)
  have hAinfQ : A ⊓ Q = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime ?_
    obtain ⟨k, hk⟩ := hQ2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hAodd)
  have hAinfS : A ⊓ S = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime ?_
    obtain ⟨k, hk⟩ := hS2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hAodd)
  have hcardX : Nat.card X = Nat.card A * Nat.card S := by
    rw [show X = A ⊔ S from rfl]
    exact CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.card_sup_of_permutable hAS hAinfS
  have hSrel : S.relIndex X = Nat.card A := by
    have h := Subgroup.relIndex_mul_card (H := S) (K := X)
    rw [inf_eq_left.mpr hSX, hcardX] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have hSnotdvd : ¬ 2 ∣ (S.subgroupOf X).index := by
    rw [show (S.subgroupOf X).index = S.relIndex X from rfl, hSrel]
    exact hAodd.not_two_dvd_nat
  have hSsub2 : IsPGroup 2 (S.subgroupOf X) := hS2.comap_subtype
  let PS : Sylow 2 X := hSsub2.toSylow hSnotdvd
  have hPScoe : (PS : Subgroup X) = S.subgroupOf X :=
    IsPGroup.toSylow_coe hSsub2 hSnotdvd
  have hQleS : Q ≤ S := by
    have hQsubn : (Q.subgroupOf X).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hQX).mpr hQnX
    haveI : (Q.subgroupOf X).Normal := hQsubn
    have hQsub2 : IsPGroup 2 (Q.subgroupOf X) := hQ2.comap_subtype
    have hle : Q.subgroupOf X ≤ (PS : Subgroup X) :=
      IsPGroup.le_sylow_of_normal hQsub2 PS
    intro q hq
    have hmem : (⟨q, hQX hq⟩ : X) ∈ (PS : Subgroup X) := hle hq
    rw [hPScoe, Subgroup.mem_subgroupOf] at hmem
    exact hmem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [X, Q] using hQnX
  · simpa [X, Q] using hAnormQ
  · simpa [X, Q] using hAinfQ
  · exact hAinfS
  · simpa [X] using hcardX
  · simpa [X] using hSrel
  · simpa [X, Q] using hQleS

theorem exists_mem_normalizer_not_mem_of_relIndex_two [Group H] [Finite H]
    {A S : Subgroup H} (hAodd : Odd (Nat.card A)) (hS2 : IsPGroup 2 S)
    (hAS : (A : Set H) * S = S * A)
    (hQrel : (CFSG.Open.pCoreOf 2 (A ⊔ S)).relIndex S = 2) :
    ∃ s : H, s ∈ S ∧ s ∉ CFSG.Open.pCoreOf 2 (A ⊔ S) ∧
      s ∈ Subgroup.normalizer (A : Set H) ∧
        s * s ∈ CFSG.Open.pCoreOf 2 (A ⊔ S) ∧
          ∀ a ∈ A, s * (s * a * s⁻¹) * s⁻¹ = a := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let X : Subgroup H := A ⊔ S
  let Q : Subgroup H := CFSG.Open.pCoreOf 2 X
  let E : Subgroup H := A ⊔ Q
  have hAX : A ≤ X := le_sup_left
  have hSX : S ≤ X := le_sup_right
  have hQX : Q ≤ X := CFSG.ClassicalGroups.PCoreSection.pCoreOf_le 2 X
  have hQ2 : IsPGroup 2 Q := CFSG.ClassicalGroups.PCoreSection.isPGroup_pCoreOf 2 X
  obtain ⟨hQnX0, hAnormQ0, hAinfQ0, _, hcardX0, _, hQleS0⟩ :=
    setup_pCoreOf_relIndex_two hAodd hS2 hAS hQrel
  have hQnX : X ≤ Subgroup.normalizer (Q : Set H) := by simpa [X, Q] using hQnX0
  have hAnormQ : A ≤ Subgroup.normalizer (Q : Set H) := by simpa [X, Q] using hAnormQ0
  have hAinfQ : A ⊓ Q = ⊥ := by simpa [X, Q] using hAinfQ0
  have hcardX : Nat.card X = Nat.card A * Nat.card S := by simpa [X] using hcardX0
  have hQleS : Q ≤ S := by simpa [X, Q] using hQleS0
  obtain ⟨t, htS, htQ, -⟩ :=
    (Subgroup.relIndex_eq_two_iff_exists_notMem_and (H := Q) (K := S)).mp hQrel
  have hcardS : Nat.card S = 2 * Nat.card Q := by
    have h := Subgroup.relIndex_mul_card (H := Q) (K := S)
    rw [inf_eq_left.mpr hQleS, hQrel] at h
    exact h.symm
  have hcardE : Nat.card E = Nat.card A * Nat.card Q := by
    have hperm : (A : Set H) * (Q : Set H) = (Q : Set H) * (A : Set H) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right A Q hAnormQ,
        ← Subgroup.coe_mul_of_right_le_normalizer_left Q A hAnormQ, sup_comm]
    rw [show E = A ⊔ Q from rfl]
    exact CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.card_sup_of_permutable hperm hAinfQ
  have hEX : E ≤ X := sup_le hAX hQX
  have hErel : E.relIndex X = 2 := by
    have h := Subgroup.relIndex_mul_card (H := E) (K := X)
    rw [inf_eq_left.mpr hEX, hcardX, hcardE, hcardS] at h
    have hposA : 0 < Nat.card A := Nat.card_pos
    have hposQ : 0 < Nat.card Q := Nat.card_pos
    have h1 : E.relIndex X * Nat.card A = 2 * Nat.card A := by
      apply Nat.eq_of_mul_eq_mul_right hposQ
      calc (E.relIndex X * Nat.card A) * Nat.card Q
          = E.relIndex X * (Nat.card A * Nat.card Q) := by ring
        _ = Nat.card A * (2 * Nat.card Q) := h
        _ = (2 * Nat.card A) * Nat.card Q := by ring
    exact Nat.eq_of_mul_eq_mul_right hposA h1
  have hEsubn : (E.subgroupOf X).Normal := by
    apply Subgroup.normal_of_index_eq_two
    rw [show (E.subgroupOf X).index = E.relIndex X from rfl]
    exact hErel
  have hEXnorm : X ≤ Subgroup.normalizer (E : Set H) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hEX).mp hEsubn
  have hQrelE : Q.relIndex E = Nat.card A := by
    have h := (relIndex_sup_eq_relIndex_inf_of_le_normalizer (H := A) (K := Q) hAnormQ).2
    rw [hAinfQ, Subgroup.relIndex_bot_left] at h
    simpa [E] using h
  have hcop : Nat.Coprime (Nat.card Q) (Q.relIndex E) := by
    rw [hQrelE]
    obtain ⟨k, hk⟩ := hQ2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hAodd)
  let W₂ : Subgroup H := A.map (MulAut.conj t).toMonoidHom
  have htN : t ∈ Subgroup.normalizer (E : Set H) := hEXnorm (hSX htS)
  have hW₂E : W₂ ≤ E := by
    rintro x ⟨a, ha, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp htN a).1 (Subgroup.mem_sup_left ha)
  have hW₂inf : Q ⊓ W₂ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxQ, hxW⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hxW
    have haQ : a ∈ Q := by
      have h1 := CFSG.ClassicalGroups.PCoreSection.conj_mem_pCoreOf
        (X.inv_mem (hSX htS)) hxQ
      have h1' : t⁻¹ * (t * a * t⁻¹) * (t⁻¹)⁻¹ ∈ Q := by
        simpa [MulAut.conj_apply] using h1
      have h2 : t⁻¹ * (t * a * t⁻¹) * (t⁻¹)⁻¹ = a := by group
      rwa [h2] at h1'
    have habot : a ∈ (⊥ : Subgroup H) := by
      rw [← hAinfQ]
      exact ⟨ha, haQ⟩
    have ha1 : a = 1 := Subgroup.mem_bot.mp habot
    simp [ha1]
  have hW₂sup : Q ⊔ W₂ = E := by
    have hmapQ : Q.map (MulAut.conj t).toMonoidHom = Q :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hQnX (hSX htS))
    have hmapE : E.map (MulAut.conj t).toMonoidHom = E :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp htN
    calc Q ⊔ W₂ = Q.map (MulAut.conj t).toMonoidHom ⊔
          A.map (MulAut.conj t).toMonoidHom := by rw [hmapQ]
      _ = (Q ⊔ A).map (MulAut.conj t).toMonoidHom := (Subgroup.map_sup Q A _).symm
      _ = (A ⊔ Q).map (MulAut.conj t).toMonoidHom := by rw [sup_comm]
      _ = E := hmapE
  obtain ⟨q, hqQ, hAq⟩ :=
    CFSG.Walter.W67.Sec6.exists_conj_complement_in (C := Q) (N := E)
      (W₁ := A) (W₂ := W₂) le_sup_right (hEX.trans hQnX) hcop le_sup_left hW₂E
      (by rw [inf_comm]; exact hAinfQ) (by rw [sup_comm]) hW₂inf hW₂sup
  have hAq' : A.map (MulAut.conj t).toMonoidHom =
      A.map (MulAut.conj q).toMonoidHom := hAq
  let s : H := q⁻¹ * t
  have hsS : s ∈ S := S.mul_mem (S.inv_mem (hQleS hqQ)) htS
  have hsQ : s ∉ Q := by
    intro hs
    apply htQ
    have hqs : q * s ∈ Q := Q.mul_mem hqQ hs
    simpa [s] using hqs
  have hsN : s ∈ Subgroup.normalizer (A : Set H) := by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    have hmaple : A.map (MulAut.conj s).toMonoidHom ≤ A := by
      rintro x ⟨a, ha, rfl⟩
      have hta : t * a * t⁻¹ ∈ A.map (MulAut.conj q).toMonoidHom := by
        rw [← hAq']
        exact Subgroup.mem_map_of_mem _ ha
      obtain ⟨b, hbA, hb⟩ := Subgroup.mem_map.mp hta
      have hb' : q * b * q⁻¹ = t * a * t⁻¹ := by
        simpa [MulAut.conj_apply] using hb
      have hsa : s * a * s⁻¹ = b := by
        dsimp [s]
        calc (q⁻¹ * t) * a * (q⁻¹ * t)⁻¹ = q⁻¹ * (t * a * t⁻¹) * q := by group
          _ = q⁻¹ * (q * b * q⁻¹) * q := by rw [← hb']
          _ = b := by group
      change s * a * s⁻¹ ∈ A
      rw [hsa]
      exact hbA
    refine Subgroup.eq_of_le_of_card_ge hmaple ?_
    exact le_of_eq (Subgroup.card_map_of_injective (f := (MulAut.conj s).toMonoidHom)
      (MulAut.conj s).injective).symm
  have hs2Q : s * s ∈ Q := by
    have hidx : (Q.subgroupOf S).index = 2 := by
      rw [show (Q.subgroupOf S).index = Q.relIndex S from rfl, hQrel]
    have h := Subgroup.mul_self_mem_of_index_two hidx (⟨s, hsS⟩ : S)
    exact Subgroup.mem_subgroupOf.mp h
  have hs2N : s * s ∈ Subgroup.normalizer (A : Set H) :=
    Subgroup.mul_mem (Subgroup.normalizer (A : Set H)) hsN hsN
  have hcentral : Q ⊓ Subgroup.normalizer (A : Set H) ≤
      Subgroup.centralizer (A : Set H) := by
    intro x hx
    obtain ⟨hxQ, hxN⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hxa : x * a * x⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hxN a).1 ha
    have hmemQ : x * a * x⁻¹ * a⁻¹ ∈ Q := by
      have h1 := CFSG.ClassicalGroups.PCoreSection.conj_mem_pCoreOf
        (hAX ha) (Q.inv_mem hxQ)
      have heq : x * a * x⁻¹ * a⁻¹ = x * (a * x⁻¹ * a⁻¹) := by group
      rw [heq]
      exact Q.mul_mem hxQ h1
    have hmemA : x * a * x⁻¹ * a⁻¹ ∈ A := A.mul_mem hxa (A.inv_mem ha)
    have hbot : x * a * x⁻¹ * a⁻¹ ∈ (⊥ : Subgroup H) := by
      rw [← hAinfQ]
      exact ⟨hmemA, hmemQ⟩
    have hone : x * a * x⁻¹ * a⁻¹ = 1 := Subgroup.mem_bot.mp hbot
    have hxa' : x * a * x⁻¹ = a := by
      have h := congrArg (fun y : H => y * a) hone
      simpa [mul_assoc] using h
    have hcomm : x * a = a * x := by
      have h := congrArg (fun y : H => y * x) hxa'
      simpa [mul_assoc] using h
    exact hcomm.symm
  have hs2cent : s * s ∈ Subgroup.centralizer (A : Set H) :=
    hcentral (Subgroup.mem_inf.mpr ⟨hs2Q, hs2N⟩)
  refine ⟨s, hsS, hsQ, hsN, hs2Q, ?_⟩
  intro a ha
  have hcomm : (s * s) * a = a * (s * s) :=
    (Subgroup.mem_centralizer_iff.mp hs2cent a ha).symm
  calc s * (s * a * s⁻¹) * s⁻¹ = (s * s) * a * (s * s)⁻¹ := by group
    _ = a := by rw [hcomm]; group

theorem false_of_commutator_zpowers_eq_bot [Group H] [Finite H]
    {A S : Subgroup H} (hAodd : Odd (Nat.card A)) (hS2 : IsPGroup 2 S)
    (hAS : (A : Set H) * S = S * A)
    (hQrel : (CFSG.Open.pCoreOf 2 (A ⊔ S)).relIndex S = 2) {s : H}
    (hsS : s ∈ S) (hsQ : s ∉ CFSG.Open.pCoreOf 2 (A ⊔ S))
    (hB : ⁅A, Subgroup.zpowers s⁆ = ⊥) : False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let X : Subgroup H := A ⊔ S
  let Q : Subgroup H := CFSG.Open.pCoreOf 2 X
  have hQrelQ : Q.relIndex S = 2 := hQrel
  have hAX : A ≤ X := le_sup_left
  have hSX : S ≤ X := le_sup_right
  obtain ⟨hQnX0, -, -, -, -, -, hQleS0⟩ :=
    setup_pCoreOf_relIndex_two hAodd hS2 hAS hQrel
  have hQnX : X ≤ Subgroup.normalizer (Q : Set H) := by simpa [X, Q] using hQnX0
  have hQleS : Q ≤ S := by simpa [X, Q] using hQleS0
  let L : Subgroup H := Q ⊔ Subgroup.zpowers s
  have hQleL : Q ≤ L := le_sup_left
  have hLleS : L ≤ S := sup_le hQleS (Subgroup.zpowers_le.mpr hsS)
  have hQLne : Q.relIndex L ≠ 1 := by
    intro h1
    exact hsQ (Subgroup.relIndex_eq_one.mp h1
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers s)))
  have hmul := Subgroup.relIndex_mul_relIndex (H := Q) (K := L) (L := S) hQleL hLleS
  have hQrelL : Q.relIndex L = 2 := by
    have hdvd : Q.relIndex L ∣ 2 := ⟨L.relIndex S, by rw [hmul, hQrelQ]⟩
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h1
    · exact absurd h1 hQLne
    · exact h1
  have hLrelS : L.relIndex S = 1 := by
    have h := hmul
    rw [hQrelL, hQrelQ] at h
    omega
  have hSleL : S ≤ L := Subgroup.relIndex_eq_one.mp hLrelS
  have hS_eq : S = L := le_antisymm hSleL hLleS
  have hAcent : A ≤ Subgroup.centralizer (Subgroup.zpowers s : Set H) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hB
  let B : Subgroup H := A ⊔ Subgroup.zpowers s
  have hAnormS : A ≤ Subgroup.normalizer (S : Set H) := by
    intro a ha
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    have hmapQ : Q.map (MulAut.conj a).toMonoidHom = Q :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hQnX (hAX ha))
    have hcomm : Commute a s :=
      (Subgroup.mem_centralizer_iff.mp (hAcent ha) s (Subgroup.mem_zpowers s)).symm
    have hfixs : a * s * a⁻¹ = s := by
      rw [hcomm.eq]
      group
    have hmapZ : (Subgroup.zpowers s).map (MulAut.conj a).toMonoidHom =
        Subgroup.zpowers s := by
      rw [MonoidHom.map_zpowers]
      change Subgroup.zpowers (MulAut.conj a s) = Subgroup.zpowers s
      rw [show MulAut.conj a s = s by simpa [MulAut.conj_apply] using hfixs]
    calc S.map (MulAut.conj a).toMonoidHom
        = (Q ⊔ Subgroup.zpowers s).map (MulAut.conj a).toMonoidHom := by rw [hS_eq]
      _ = Q.map (MulAut.conj a).toMonoidHom ⊔
            (Subgroup.zpowers s).map (MulAut.conj a).toMonoidHom := Subgroup.map_sup Q _ _
      _ = Q ⊔ Subgroup.zpowers s := by rw [hmapQ, hmapZ]
      _ = S := hS_eq.symm
  have hBnormS : B ≤ Subgroup.normalizer (S : Set H) :=
    sup_le hAnormS (Subgroup.zpowers_le.mpr (Subgroup.le_normalizer hsS))
  have hQnormS : Q ≤ Subgroup.normalizer (S : Set H) :=
    hQleS.trans (Subgroup.le_normalizer)
  have hXeq : X = B ⊔ Q := by
    dsimp [X, B]
    rw [hS_eq]
    ac_rfl
  have hXnormS : X ≤ Subgroup.normalizer (S : Set H) := by
    rw [hXeq]
    exact sup_le hBnormS hQnormS
  have hSleQ : S ≤ Q := by
    refine CFSG.ClassicalGroups.PCoreSection.le_pCoreOf hSX ?_ hS2
    intro x hx y hy
    exact (Subgroup.mem_normalizer_iff.mp (hXnormS hx) y).1 hy
  have heq : Q = S := le_antisymm hQleS hSleQ
  rw [heq, Subgroup.relIndex_self] at hQrelQ
  omega

end CFSG.GroupTheory
