module

public import CFSG.GH74.GLS.C3.Layer2.LocalBasic
public import CFSG.GH74.GLS.C3.Layer2.AltFacts

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.C3.Layer2

section Omega

variable {G : Type} [Group G]

@[expose] def omegaZ (T : Subgroup G) : Subgroup G where
  carrier := {z | z ∈ T ∧ (∀ t ∈ T, z * t = t * z) ∧ z ^ 2 = 1}
  one_mem' := ⟨one_mem T, fun t _ => by simp, one_pow 2⟩
  mul_mem' := by
    rintro y z ⟨hyT, hyc, hy2⟩ ⟨hzT, hzc, hz2⟩
    refine ⟨mul_mem hyT hzT, fun t ht => ?_, ?_⟩
    · calc y * z * t = y * (z * t) := mul_assoc _ _ _
        _ = y * (t * z) := by rw [hzc t ht]
        _ = (y * t) * z := (mul_assoc _ _ _).symm
        _ = (t * y) * z := by rw [hyc t ht]
        _ = t * (y * z) := mul_assoc _ _ _
    · have hc : Commute y z := (hzc y hyT).symm
      rw [hc.mul_pow, hy2, hz2, one_mul]
  inv_mem' := by
    rintro y ⟨hyT, hyc, hy2⟩
    refine ⟨inv_mem hyT, fun t ht => ?_, ?_⟩
    · have hc : Commute y t := hyc t ht
      exact (hc.inv_left).eq
    · rw [inv_pow, hy2, inv_one]

theorem omegaZ_comm (T : Subgroup G) {y z : G} (hy : y ∈ omegaZ T) (hz : z ∈ omegaZ T) :
    y * z = z * y := hy.2.1 z hz.1

theorem omegaZ_isElementaryAbelian (T : Subgroup G) : IsElementaryAbelian 2 ↥(omegaZ T) := by
  refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩, exponent_dvd_p := ?_ }
  · exact Subtype.ext (omegaZ_comm T a.2 b.2)
  · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
    intro z
    exact Subtype.ext z.2.2.2

theorem conj_mem_omegaZ (T : Subgroup G) {a : G} (ha : a ∈ normalizer (T : Set G)) {v : G}
    (hv : v ∈ omegaZ T) : a * v * a⁻¹ ∈ omegaZ T := by
  obtain ⟨hvT, hvc, hv2⟩ := hv
  refine ⟨(mem_normalizer_iff.1 ha v).1 hvT, fun t ht => ?_, ?_⟩
  · have ht' : a⁻¹ * t * a ∈ T := by
      have := (mem_normalizer_iff.1 (inv_mem ha) t).1 ht
      simpa using this
    have h1 := hvc _ ht'
    calc a * v * a⁻¹ * t = a * (v * (a⁻¹ * t * a)) * a⁻¹ := by group
      _ = a * ((a⁻¹ * t * a) * v) * a⁻¹ := by rw [h1]
      _ = t * (a * v * a⁻¹) := by group
  · calc (a * v * a⁻¹) ^ 2 = a * (v * v) * a⁻¹ := by rw [sq]; group
      _ = a * v ^ 2 * a⁻¹ := by rw [sq]
      _ = 1 := by rw [hv2]; group

end Omega

variable {G : Type} [Group G] [Finite G] {n : ℕ} {x : G} {K T Q S : Subgroup G} {a : G}

namespace IsAConfig

theorem exists_noncomm (h : IsAConfig n x K T Q S a) (hn : n = 6 ∨ n = 7)
    (hG4 : pRank 2 G ≤ 4) : ∃ t ∈ T, ∃ q ∈ Q, t * q ≠ q * t := by
  by_contra hcon
  push Not at hcon
  have h6 := h.cond6 (fun q hq t ht => (hcon t ht q hq).symm)
  have haS : a ∈ S := h.a_mem.1
  have haN : a ∈ normalizer (T : Set G) := h.a_mem.2.1
  have haT : a ∉ T := h.a_mem.2.2.1
  have ha2T : a ^ 2 ∈ T := h.a_mem.2.2.2
  have hTS : T ≤ S := h.T_lt_S.le
  set V := omegaZ T with hV
  have hVel : IsElementaryAbelian 2 ↥V := omegaZ_isElementaryAbelian T
  have hQV : Q ≤ V := fun q hq => ⟨h.Q_le_T hq, fun t ht => (hcon t ht q hq).symm, h.Q_sq hq⟩
  have haV : ∀ v ∈ V, a * v * a⁻¹ ∈ V := fun v hv => conj_mem_omegaZ T haN hv
  have ha2 : ∀ v ∈ V, a ^ 2 * v = v * a ^ 2 := fun v hv => (hv.2.1 _ ha2T).symm
  have h1 := card_le_sq_card_fixed V haV ha2
  have hinf : (V ⊓ centralizer ({a} : Set G)) ⊓ Q = ⊥ := by
    rw [eq_bot_iff]
    rintro u ⟨⟨huV, hua⟩, huQ⟩
    by_contra hu1
    have hu1' : u ≠ 1 := fun h' => hu1 (by rw [h']; exact one_mem _)
    have hTu := h6 u huQ hu1'
    have hTle : T ≤ centralizer ({u} : Set G) := fun t ht =>
      mem_centralizer_singleton_iff.2 (huV.2.1 t ht).symm
    have hale : a ∈ centralizer ({u} : Set G) :=
      mem_centralizer_singleton_iff.2 (mem_centralizer_singleton_iff.1 hua).symm
    have hsup : T ⊔ zpowers a ≤ centralizer ({u} : Set G) :=
      sup_le hTle (zpowers_le.2 hale)
    have hSle : T ⊔ zpowers a ≤ S := sup_le hTS (zpowers_le.2 haS)
    have hp : IsPGroup 2 ↥(T ⊔ zpowers a) := IsPGroup.to_le h.sylowS.isPGroup hSle
    have heq := hTu.eq_of_le le_sup_left hsup hp
    have hmem : a ∈ T ⊔ zpowers a := (le_sup_right : zpowers a ≤ T ⊔ zpowers a) (mem_zpowers a)
    rw [heq] at hmem
    exact haT hmem
  have hVcomm : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v := fun v hv w hw => omegaZ_comm T hv hw
  have h2 := card_mul_card_le_inf_mul_of_comm (V ⊓ centralizer ({a} : Set G)) Q V inf_le_left hQV
    hVcomm
  rw [hinf, Subgroup.card_bot, one_mul, h.card_Q] at h2
  have hc0 : 0 < Nat.card ↥(V ⊓ centralizer ({a} : Set G)) := Nat.card_pos
  have hc4 : 4 ≤ Nat.card ↥(V ⊓ centralizer ({a} : Set G)) := by nlinarith
  have hV16 : 16 ≤ Nat.card ↥V := by omega
  obtain ⟨e⟩ := h.K_equiv_alt
  have hP : IsSylowOf 2 (T ⊓ K) K :=
    h.sylowT.inf_of_le_normalizer h.K_le_C h.C_le_normalizer_K
  obtain ⟨-, ⟨z, hzP, hz1, hzc, hzu⟩, -, D, hDP, hD4, hDel⟩ := sylow_alt_facts n hn e hP
  have hDT : D ≤ T := hDP.trans inf_le_left
  have hVD : D ≤ centralizer (V : Set G) := fun d hd =>
    mem_centralizer_iff.2 fun v hv => (hv.2.1 d (hDT hd))
  have hW := IsElementaryAbelian.sup_of_le_centralizer (E := V) (C := D) (p := 2) hVD
  have hWcard := card_mul_card_le_inf_mul_of_comm V D (V ⊔ D) le_sup_left le_sup_right
    (fun v hv w hw => setLike_mul_comm hv hw)
  have hVD2 : Nat.card ↥(V ⊓ D) ≤ 2 := by
    have hmem : ∀ w ∈ V ⊓ D, w = 1 ∨ w = z := by
      rintro w ⟨hwV, hwD⟩
      exact hzu w (hDP hwD) (fun p hp => hwV.2.1 p hp.1)
    classical
    have : Nat.card ↥(V ⊓ D) ≤ Nat.card (Fin 2) := by
      refine Nat.card_le_card_of_injective
        (fun w : ↥(V ⊓ D) => if (w : G) = 1 then (0 : Fin 2) else 1) ?_
      intro w w' hww
      by_cases hw : (w : G) = 1 <;> by_cases hw' : (w' : G) = 1
      · exact Subtype.ext (hw.trans hw'.symm)
      · simp [hw, hw'] at hww
      · simp [hw, hw'] at hww
      · have h1 := (hmem w w.2).resolve_left hw
        have h2 := (hmem w' w'.2).resolve_left hw'
        exact Subtype.ext (h1.trans h2.symm)
    simpa using this
  have hWle := card_elemAb_le_pow_pRank (V ⊔ D)
  have hpow : 2 ^ pRank 2 G ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hG4
  rw [hD4] at hWcard
  have hW16 : Nat.card ↥(V ⊔ D) ≤ 16 := hWle.trans (by simpa using hpow)
  have hmul := Nat.mul_le_mul hVD2 hW16
  omega

end IsAConfig

end CFSG.GH74.GLS
