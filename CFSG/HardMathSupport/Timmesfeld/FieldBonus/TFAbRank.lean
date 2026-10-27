module

public import CFSG.HardMathSupport.Timmesfeld.FieldBonus.SU3Core
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Tools

public section

namespace CFSG.HardMathSupport.Timmesfeld.FieldBonus

open Matrix CFSG.Open CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance
open CFSG.SectionRank.ClassicalEven (torusDiag torusDiag_mem_SL torusDiag_mem_SU coe_torusDiag
  torusDiag_injective)

section Transfer

variable {G : Type*} [Group G] [Finite G]

theorem le_glaTwoLocalRank_subgroup {p : ℕ} (hp : 1 < p) (H : Subgroup G) {T E : Subgroup G}
    (hTH : T ≤ H) (hEH : E ≤ H) (hT : T ≠ ⊥) (h2 : IsPGroup 2 T) (hE : IsElemAbelian p E)
    (hEN : E ≤ Subgroup.normalizer (T : Set G)) {k : ℕ} (hk : Nat.card E = p ^ k) :
    k ≤ GLATwoLocalRank p ↥H := by
  refine le_glaTwoLocalRank_of_le_normalizer hp (T := T.subgroupOf H) (E := E.subgroupOf H)
    ?_ ?_ ?_ ?_ ?_
  · intro h
    apply hT
    rw [← Subgroup.map_subgroupOf_eq_of_le hTH, h, Subgroup.map_bot]
  · exact h2.comap_subtype
  · refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
    · have := hE.1.is_comm.comm ⟨((a : H) : G), Subgroup.mem_subgroupOf.1 a.2⟩
        ⟨((b : H) : G), Subgroup.mem_subgroupOf.1 b.2⟩
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : E => (x : G)) this
    · apply Subtype.ext
      exact hE.2 _ (Subgroup.mem_subgroupOf.1 hy)
  · intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have := Subgroup.mem_normalizer_iff.1 (hEN (Subgroup.mem_subgroupOf.1 hg)) (h : G)
    simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] using this
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEH).toEquiv]
    exact hk

end Transfer

section Torus

variable {K : Type} [Field K] {ω : Kˣ}

theorem torusA_pow_three (hω : ω ^ 3 = 1) :
    torusDiag (K := K) ![ω, ω⁻¹, 1] ^ 3 = 1 := by
  rw [← map_pow, ← map_one (torusDiag (ι := Fin 3) (K := K))]
  congr 1
  funext i
  fin_cases i <;> simp [hω, inv_pow]

theorem torusB_pow_three (hω : ω ^ 3 = 1) :
    torusDiag (K := K) ![1, ω, ω⁻¹] ^ 3 = 1 := by
  rw [← map_pow, ← map_one (torusDiag (ι := Fin 3) (K := K))]
  congr 1
  funext i
  fin_cases i <;> simp [hω, inv_pow]

theorem torusA_comm_torusB :
    torusDiag (K := K) ![ω, ω⁻¹, 1] * torusDiag (K := K) ![1, ω, ω⁻¹] =
      torusDiag (K := K) ![1, ω, ω⁻¹] * torusDiag (K := K) ![ω, ω⁻¹, 1] :=
  ((Commute.all _ _).map torusDiag).eq

theorem torusPair_indep (hω : orderOf ω = 3) (i j : ℕ) (hi : i < 3) (hj : j < 3)
    (h : torusDiag (K := K) ![ω, ω⁻¹, 1] ^ i * torusDiag (K := K) ![1, ω, ω⁻¹] ^ j = 1) :
    i = 0 ∧ j = 0 := by
  rw [← map_pow, ← map_pow, ← map_mul,
    ← map_one (torusDiag (ι := Fin 3) (K := K))] at h
  have h' := torusDiag_injective h
  have e0 := congrFun h' 0
  have e2 := congrFun h' 2
  simp only [Pi.mul_apply, Pi.pow_apply, Matrix.cons_val_zero, Matrix.cons_val, one_pow,
    mul_one, one_mul, Pi.one_apply] at e0 e2
  have hi0 : ω ^ i = 1 := e0
  have hj0 : ω ^ j = 1 := by
    have : (ω⁻¹) ^ j = 1 := e2
    rwa [inv_pow, inv_eq_one] at this
  refine ⟨Nat.eq_zero_of_dvd_of_lt ?_ hi, Nat.eq_zero_of_dvd_of_lt ?_ hj⟩
  · rw [← hω]; exact orderOf_dvd_of_pow_eq_one hi0
  · rw [← hω]; exact orderOf_dvd_of_pow_eq_one hj0

theorem two_le_glaTwoLocalRank_of_torus [Finite K] (hω : orderOf ω = 3)
    {H : Subgroup (GL (Fin 3) K)} (ha : torusDiag ![ω, ω⁻¹, 1] ∈ H)
    (hb : torusDiag ![1, ω, ω⁻¹] ∈ H) {T : Subgroup (GL (Fin 3) K)} (hTH : T ≤ H) (hT : T ≠ ⊥)
    (h2 : IsPGroup 2 T) (haN : torusDiag ![ω, ω⁻¹, 1] ∈ Subgroup.normalizer (T : Set _))
    (hbN : torusDiag ![1, ω, ω⁻¹] ∈ Subgroup.normalizer (T : Set _)) :
    2 ≤ GLATwoLocalRank 3 ↥H := by
  have hω3 : ω ^ 3 = 1 := hω ▸ pow_orderOf_eq_one ω
  refine le_glaTwoLocalRank_subgroup (by norm_num) H hTH (E :=
    (pairHom _ _ (torusA_pow_three hω3) (torusB_pow_three hω3) torusA_comm_torusB).range)
    ?_ hT h2 (isElemAbelian_range_of_comm_pow (p := 3) (A := Multiplicative (ZMod 3 × ZMod 3))
      (fun a b => mul_comm a b) zmod3_pow_three _) ?_ (k := 2)
    (by rw [card_range_pairHom _ _ (torusA_pow_three hω3) (torusB_pow_three hω3)
      torusA_comm_torusB (torusPair_indep hω)]; norm_num)
  · rintro _ ⟨x, rfl⟩
    induction x using Multiplicative.rec with
    | ofAdd x =>
      obtain ⟨i, j⟩ := x
      exact mul_mem (pow_mem ha _) (pow_mem hb _)
  · rintro _ ⟨x, rfl⟩
    induction x using Multiplicative.rec with
    | ofAdd x =>
      obtain ⟨i, j⟩ := x
      exact mul_mem (pow_mem haN _) (pow_mem hbN _)

theorem two_le_glaTwoLocalRank_of_involution [Finite K] (hω : orderOf ω = 3)
    {H : Subgroup (GL (Fin 3) K)} (ha : torusDiag ![ω, ω⁻¹, 1] ∈ H)
    (hb : torusDiag ![1, ω, ω⁻¹] ∈ H) {d : Fin 3 → Kˣ} (hd : torusDiag d ∈ H)
    (hd1 : torusDiag (K := K) d ≠ 1) (hd2 : torusDiag (K := K) d ^ 2 = 1) :
    2 ≤ GLATwoLocalRank 3 ↥H := by
  have hcen : ∀ d' : Fin 3 → Kˣ,
      torusDiag (K := K) d' ∈ Subgroup.normalizer ((Subgroup.zpowers (torusDiag (K := K) d) :
        Subgroup (GL (Fin 3) K)) : Set _) := by
    intro d'
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨n, rfl⟩
    exact (Commute.zpow_left ((Commute.all d d').map torusDiag) n).eq
  refine two_le_glaTwoLocalRank_of_torus hω ha hb (T := Subgroup.zpowers (torusDiag d)) ?_ ?_ ?_
    (hcen _) (hcen _)
  · rw [Subgroup.zpowers_le]; exact hd
  · intro h
    exact hd1 (Subgroup.zpowers_eq_bot.1 h)
  · refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime hd2 hd1, pow_one]

end Torus

end CFSG.HardMathSupport.Timmesfeld.FieldBonus
