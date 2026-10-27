module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SNSyl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SNFr
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SNTT
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8SSup
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t t₀ z g : G} {L S B : Subgroup G}

private theorem sec9n_priv_B_le_A : B ≤ Asub9 t t₀ B := by
  rw [Asub9]
  exact le_sup_right

private theorem sec9n_priv_A8_le_A : (zpowers t ⊔ B : Subgroup G) ≤ Asub9 t t₀ B := by
  rw [Asub9]
  exact sup_le (le_sup_left.trans le_sup_left) le_sup_right

private theorem sec9n_priv_t_mem_A : t ∈ Asub9 t t₀ B :=
  sec9n_priv_A8_le_A (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))

private theorem sec9n_priv_t0_mem_A : t₀ ∈ Asub9 t t₀ B := by
  rw [Asub9]
  exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers t₀))

private theorem sec9n_priv_centMod_conj_mem_sup (hctx : Sec9Ctx G t L S z g B t₀) {x : G}
    (hx : x ∈ centMod (Asub9 t t₀ B) B) {y : G} (hy : y ∈ zpowers t ⊔ B) :
    x * y * x⁻¹ ∈ zpowers t ⊔ B := by
  obtain ⟨-, hx'⟩ := hx
  have hyA : y ∈ Asub9 t t₀ B := sec9n_priv_A8_le_A hy
  have hcomm : x * y * x⁻¹ * y⁻¹ ∈ B := hx' y hyA
  rw [show x * y * x⁻¹ = (x * y * x⁻¹ * y⁻¹) * y by group]
  exact (zpowers t ⊔ B).mul_mem (Subgroup.mem_sup_right hcomm) hy

private theorem sec9n_priv_conj_t0_contra (hT : Asc82Tab9M) (hctx : Sec9Ctx G t L S z g B t₀)
    {p : G} (hpM : p ∈ normalizer ((zpowers t ⊔ B : Subgroup G) : Set G))
    (hmem : p * t₀ * p⁻¹ ∈ zpowers t ⊔ B) : False := by
  have hpinv : p⁻¹ ∈ normalizer ((zpowers t ⊔ B : Subgroup G) : Set G) :=
    (normalizer _).inv_mem hpM
  have ht0 : t₀ ∈ zpowers t ⊔ B := by
    have h := (Subgroup.mem_normalizer_iff.mp hpinv (p * t₀ * p⁻¹)).mp hmem
    rwa [show p⁻¹ * (p * t₀ * p⁻¹) * (p⁻¹)⁻¹ = t₀ by group] at h
  exact sec9n_t0_not_mem_A8 hT hctx ht0

private theorem sec9n_priv_comm_mul_mem (hctx : Sec9Ctx G t L S z g B t₀) {p a a' : G}
    (ha : a ∈ Asub9 t t₀ B) (hpa : p * a * p⁻¹ * a⁻¹ ∈ B)
    (hpa' : p * a' * p⁻¹ * a'⁻¹ ∈ B) :
    p * (a * a') * p⁻¹ * (a * a')⁻¹ ∈ B := by
  have hw : a * (p * a' * p⁻¹ * a'⁻¹) * a⁻¹ = p * a' * p⁻¹ * a'⁻¹ := by
    have hwA : p * a' * p⁻¹ * a'⁻¹ ∈ Asub9 t t₀ B := sec9n_priv_B_le_A hpa'
    rw [CFSG.Open.IsElemAbelian.comm (sec9n_A_elem hctx) ha hwA]
    group
  rw [show p * (a * a') * p⁻¹ * (a * a')⁻¹ =
      (p * a * p⁻¹ * a⁻¹) * (a * (p * a' * p⁻¹ * a'⁻¹) * a⁻¹) by group, hw]
  exact B.mul_mem hpa hpa'

private theorem sec9n_priv_coset_mul_inv_mem (hctx : Sec9Ctx G t L S z g B t₀) {e e' : G}
    (he : e ∈ B) (he' : e' ∈ B) : (t * e) * (t * e')⁻¹ ∈ B := by
  have h1 : t * e = e * t := sec9n_t_B hctx e he
  have h2 : t * e' = e' * t := sec9n_t_B hctx e' he'
  have h2' : t * e'⁻¹ = e'⁻¹ * t := sec9n_t_B hctx e'⁻¹ (B.inv_mem he')
  have ht2 : t * t = 1 := sec9n_t_sq hctx
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have heq : (t * e) * (t * e')⁻¹ = e * e'⁻¹ := by
    rw [h1, mul_inv_rev, htinv, ← h2']
    calc (e * t) * (t * e'⁻¹) = e * (t * t) * e'⁻¹ := by group
      _ = e * e'⁻¹ := by rw [ht2, mul_one]
  rw [heq]
  exact B.mul_mem he (B.inv_mem he')

private theorem sec9n_priv_conj_mul (p q u : G) :
    (p⁻¹ * q) * u * (p⁻¹ * q)⁻¹ * u⁻¹ =
      p⁻¹ * ((q * u * q⁻¹ * u⁻¹) * (p * u * p⁻¹ * u⁻¹)⁻¹) * p := by
  group

theorem sec9n_centMod_le_P (hctx : Sec9Ctx G t L S z g B t₀) :
    centMod (Asub9 t t₀ B) B ≤
      normalizer ((zpowers t ⊔ B : Subgroup G) : Set G) ⊓ normalizer (Asub9 t t₀ B : Set G) := by
  intro x hx
  refine ⟨?_, ?_⟩
  · change x ∈ normalizer ((zpowers t ⊔ B : Subgroup G) : Set G)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact sec9n_priv_centMod_conj_mem_sup hctx hx
    · intro hy
      have hxinv : x⁻¹ ∈ centMod (Asub9 t t₀ B) B := (centMod (Asub9 t t₀ B) B).inv_mem hx
      have h := sec9n_priv_centMod_conj_mem_sup hctx hxinv hy
      rwa [show x⁻¹ * (x * y * x⁻¹) * (x⁻¹)⁻¹ = y by group] at h
  · exact sec9n_centMod_le_normalizer (A := Asub9 t t₀ B) (B := B) sec9n_priv_B_le_A hx

theorem sec9n_commutator_mem (hT : Asc82Tab9M) (hctx : Sec9Ctx G t L S z g B t₀) {p : G}
    (hpM : p ∈ normalizer ((zpowers t ⊔ B : Subgroup G) : Set G))
    (hpA : p ∈ normalizer (Asub9 t t₀ B : Set G)) :
    p * t₀ * p⁻¹ * t₀⁻¹ ∈ zpowers t ⊔ B := by
  have hmemA : p * t₀ * p⁻¹ ∈ Asub9 t t₀ B :=
    (Subgroup.mem_normalizer_iff.mp hpA t₀).mp sec9n_priv_t0_mem_A
  obtain ⟨b, hb, h | h | h | h⟩ := sec9n_mem_A hctx hmemA
  · exact absurd (show p * t₀ * p⁻¹ ∈ zpowers t ⊔ B by
        rw [h]
        exact Subgroup.mem_sup_right hb)
      (sec9n_priv_conj_t0_contra hT hctx hpM)
  · exact absurd (show p * t₀ * p⁻¹ ∈ zpowers t ⊔ B by
        rw [h]
        exact (zpowers t ⊔ B).mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
          (Subgroup.mem_sup_right hb))
      (sec9n_priv_conj_t0_contra hT hctx hpM)
  · rw [h, hctx.t0_B b hb]
    rw [show b * t₀ * t₀⁻¹ = b by group]
    exact Subgroup.mem_sup_right hb
  · rw [h]
    have heq : t * (t₀ * b) * t₀⁻¹ = t * b := by
      rw [hctx.t0_B b hb]
      group
    rw [heq]
    exact (zpowers t ⊔ B).mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
      (Subgroup.mem_sup_right hb)

theorem sec9n_mem_centMod_iff (hctx : Sec9Ctx G t L S z g B t₀)
    (hM : ConjTwoTransOn (normalizer ((zpowers t ⊔ B : Subgroup G) : Set G)) (cosetSet t B))
    {p : G} (hpM : p ∈ normalizer ((zpowers t ⊔ B : Subgroup G) : Set G))
    (hpA : p ∈ normalizer (Asub9 t t₀ B : Set G)) :
    p ∈ centMod (Asub9 t t₀ B) B ↔ p * t₀ * p⁻¹ * t₀⁻¹ ∈ B := by
  constructor
  · intro hp
    exact hp.2 t₀ sec9n_priv_t0_mem_A
  · intro hp0
    have hpB : p ∈ normalizer (B : Set G) :=
      sec9n_M_le_normalizer_B (sec9n_t_sq hctx) (sec9n_t_B hctx) hM hpM
    have hpt : p * t * p⁻¹ * t⁻¹ ∈ B := by
      obtain ⟨b, hb, hptb⟩ := hM.1 p hpM t ⟨1, B.one_mem, (mul_one t).symm⟩
      rw [hptb, sec9n_t_B hctx b hb]
      rw [show b * t * t⁻¹ = b by group]
      exact hb
    have hpb : ∀ b ∈ B, p * b * p⁻¹ * b⁻¹ ∈ B := fun b hb =>
      B.mul_mem ((Subgroup.mem_normalizer_iff.mp hpB b).mp hb) (B.inv_mem hb)
    refine ⟨hpB, fun a ha => ?_⟩
    obtain ⟨b, hb, h | h | h | h⟩ := sec9n_mem_A hctx ha
    · rw [h]; exact hpb b hb
    · rw [h]
      exact sec9n_priv_comm_mul_mem hctx sec9n_priv_t_mem_A hpt (hpb b hb)
    · rw [h]
      exact sec9n_priv_comm_mul_mem hctx sec9n_priv_t0_mem_A hp0 (hpb b hb)
    · rw [h]
      exact sec9n_priv_comm_mul_mem hctx sec9n_priv_t_mem_A hpt
        (sec9n_priv_comm_mul_mem hctx sec9n_priv_t0_mem_A hp0 (hpb b hb))

theorem sec9n_index_two (hT : Asc82Tab9M) (hctx : Sec9Ctx G t L S z g B t₀)
    (hM : ConjTwoTransOn (normalizer ((zpowers t ⊔ B : Subgroup G) : Set G)) (cosetSet t B)) :
    ∀ p ∈ normalizer ((zpowers t ⊔ B : Subgroup G) : Set G) ⊓ normalizer (Asub9 t t₀ B : Set G),
      ∀ q ∈ normalizer ((zpowers t ⊔ B : Subgroup G) : Set G) ⊓
          normalizer (Asub9 t t₀ B : Set G),
        p ∈ centMod (Asub9 t t₀ B) B ∨ q ∈ centMod (Asub9 t t₀ B) B ∨
          p⁻¹ * q ∈ centMod (Asub9 t t₀ B) B := by
  intro p hp q hq
  obtain ⟨hpM, hpA⟩ := hp
  obtain ⟨hqM, hqA⟩ := hq
  by_cases hpN : p ∈ centMod (Asub9 t t₀ B) B
  · exact Or.inl hpN
  by_cases hqN : q ∈ centMod (Asub9 t t₀ B) B
  · exact Or.inr (Or.inl hqN)
  refine Or.inr (Or.inr ?_)
  have hpwB : p * t₀ * p⁻¹ * t₀⁻¹ ∉ B :=
    fun h => hpN ((sec9n_mem_centMod_iff hctx hM hpM hpA).mpr h)
  have hqwB : q * t₀ * q⁻¹ * t₀⁻¹ ∉ B :=
    fun h => hqN ((sec9n_mem_centMod_iff hctx hM hqM hqA).mpr h)
  have htn : ∀ e ∈ B, t * e * t⁻¹ ∈ B := by
    intro e he
    rw [sec9n_t_B hctx e he]
    rwa [show e * t * t⁻¹ = e by group]
  have hwp : ∃ e ∈ B, p * t₀ * p⁻¹ * t₀⁻¹ = t * e := by
    rcases sec8s_mem_sup_zpowers (sec9n_t_sq hctx) htn
        (sec9n_commutator_mem hT hctx hpM hpA) with h | h
    · exact absurd h hpwB
    · exact h
  have hwq : ∃ e ∈ B, q * t₀ * q⁻¹ * t₀⁻¹ = t * e := by
    rcases sec8s_mem_sup_zpowers (sec9n_t_sq hctx) htn
        (sec9n_commutator_mem hT hctx hqM hqA) with h | h
    · exact absurd h hqwB
    · exact h
  obtain ⟨ep, hep, hwp'⟩ := hwp
  obtain ⟨eq, heq, hwq'⟩ := hwq
  have hmemB : (q * t₀ * q⁻¹ * t₀⁻¹) * (p * t₀ * p⁻¹ * t₀⁻¹)⁻¹ ∈ B := by
    rw [hwq', hwp']
    exact sec9n_priv_coset_mul_inv_mem hctx heq hep
  have hpB : p ∈ normalizer (B : Set G) :=
    sec9n_M_le_normalizer_B (sec9n_t_sq hctx) (sec9n_t_B hctx) hM hpM
  have hconjB : p⁻¹ * ((q * t₀ * q⁻¹ * t₀⁻¹) * (p * t₀ * p⁻¹ * t₀⁻¹)⁻¹) * p ∈ B := by
    have hpBinv : p⁻¹ ∈ normalizer (B : Set G) := (normalizer (B : Set G)).inv_mem hpB
    have h := (Subgroup.mem_normalizer_iff.mp hpBinv
      ((q * t₀ * q⁻¹ * t₀⁻¹) * (p * t₀ * p⁻¹ * t₀⁻¹)⁻¹)).mp hmemB
    simpa only [inv_inv] using h
  have hcomm : (p⁻¹ * q) * t₀ * (p⁻¹ * q)⁻¹ * t₀⁻¹ ∈ B := by
    rw [sec9n_priv_conj_mul p q t₀]
    exact hconjB
  have hpM' : p⁻¹ * q ∈ normalizer ((zpowers t ⊔ B : Subgroup G) : Set G) :=
    (normalizer _).mul_mem ((normalizer _).inv_mem hpM) hqM
  have hpA' : p⁻¹ * q ∈ normalizer (Asub9 t t₀ B : Set G) :=
    (normalizer _).mul_mem ((normalizer _).inv_mem hpA) hqA
  exact (sec9n_mem_centMod_iff hctx hM hpM' hpA').mpr hcomm

theorem sec9n_twoTrans (h36 : Asc82Lemma36) (h68 : Asc82Lemma68) (hB : Asc82Sec8B)
    (hT : Asc82Tab9M) (hctx : Sec9Choice G t L S z g B t₀) :
    ConjTwoTransOn (centMod (Asub9 t t₀ B) B) (cosetSet t B) := by
  have hM := (sec9n_h68 h68 hB hctx).2
  have hsyl := sec9n_sylow_cent8 h36 h68 hB hT hctx
  have hTA8 : cosetSet t B ⊆ (zpowers t ⊔ B : Subgroup G) := by
    rintro x ⟨b, hb, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
      (Subgroup.mem_sup_right hb)
  have hP := sec9n_P_twoTrans hTA8 hsyl hM
  have hcard : (cosetSet t B).ncard = 16 :=
    sec9n_ncard_coset (by rw [hctx.B_e16.2]; norm_num)
  exact sec9n_conjTwoTransOn_of_index_two (sec9n_centMod_le_P hctx.toSec9Ctx)
    (sec9n_index_two hT hctx.toSec9Ctx hM) hcard hP

end CFSG.OddStandard.SmallF3.Omega
