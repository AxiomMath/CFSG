module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CBCent
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B5c
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CBBase
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CBImg

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7c_isE_img (s : Setting3 G L) {H : Subgroup G} (hX : H ≤ y7cX s) (hM : M3 s ≤ H)
    (hc : ∀ m ∈ H, ∀ n ∈ H, ⁅m, n⁆ ∈ M3 s) (hsq : ∀ m ∈ H, m ^ 2 ∈ M3 s) {k : ℕ}
    (hH : Nat.card H = 2 ^ (6 + k)) (h3 : Nat.card (M3 s) = 2 ^ 6) :
    IsE k ↥(y7cImg s H) := by
  have hcard : Nat.card ↥(y7cImg s H) = 2 ^ k := by
    have h := y7c_card_img s hX hM
    rw [h3, hH, pow_add, mul_comm (2 ^ 6) (2 ^ k)] at h
    exact Nat.mul_right_cancel (by positivity : 0 < 2 ^ 6) h
  have hcommA : ∀ a b : ↥(y7cImg s H), a * b = b * a := by
    intro a b
    apply Subtype.ext
    change (a : y7cGam s) * (b : y7cGam s) = (b : y7cGam s) * (a : y7cGam s)
    obtain ⟨y, hyH, hyx⟩ := (mem_y7cImg s).mp a.2
    obtain ⟨w, hwH, hwz⟩ := (mem_y7cImg s).mp b.2
    rw [← hyx, ← hwz]
    have hker : (((y * w)⁻¹ * (w * y) : ↥(y7cX s)) : G) ∈ M3 s := by
      have hc' : ⁅(y : G)⁻¹, (w : G)⁆ ∈ M3 s := hc _ (H.inv_mem hyH) _ hwH
      have hconj : (w : G)⁻¹ * ⁅(y : G)⁻¹, (w : G)⁆ * (w : G) ∈ M3 s :=
        (Subgroup.mem_normalizer_iff''.mp (hX hwH) ⁅(y : G)⁻¹, (w : G)⁆).mp hc'
      rw [show (((y * w)⁻¹ * (w * y) : ↥(y7cX s)) : G) =
          (w : G)⁻¹ * ⁅(y : G)⁻¹, (w : G)⁆ * (w : G) by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
        group]
      exact hconj
    have heq : y7cPi s (y * w) = y7cPi s (w * y) :=
      (y7cPi_eq_iff s (y * w) (w * y)).mpr (by simpa using hker)
    calc y7cPi s y * y7cPi s w = y7cPi s (y * w) := (map_mul _ _ _).symm
      _ = y7cPi s (w * y) := heq
      _ = y7cPi s w * y7cPi s y := map_mul _ _ _
  have hsqA : ∀ a : ↥(y7cImg s H), a ^ 2 = 1 := by
    intro a
    apply Subtype.ext
    change (a : y7cGam s) ^ 2 = 1
    obtain ⟨y, hyH, hyx⟩ := (mem_y7cImg s).mp a.2
    rw [← hyx]
    have h2 : (y : G) ^ 2 ∈ M3 s := hsq (y : G) hyH
    have hsq' : y7cPi s (y ^ 2) = 1 :=
      (y7cPi_eq_one_iff s (y ^ 2)).mpr (by simpa using h2)
    calc (y7cPi s y) ^ 2 = y7cPi s (y ^ 2) := (map_pow _ _ _).symm
      _ = 1 := hsq'
  refine ⟨⟨?_, ?_⟩, hcard⟩
  · exact IsMulCommutative.of_comm fun x z => Subtype.ext (hcommA x.1 z.1)
  · intro x _
    exact hsqA x

theorem y7c_M3_le_M6 (c : Ctx7 G L) (hb : B7Std c) : M3 c.s ≤ M6 c.e :=
  hb.h71.2.2.2.1

theorem y7c_M3_le_P7 (c : Ctx7 G L) (hb : B7Std c) : M3 c.s ≤ P7 c.e :=
  (y7c_M3_le_M6 c hb).trans le_sup_left

theorem y7c_M6_le_X (c : Ctx7 G L) (hb : B7Std c) : M6 c.e ≤ y7cX c.s := by
  intro m hm
  exact Subgroup.mem_normalizer_fintype fun n hn =>
    y7b_M6_norm_M3 c hb.toB5Std m hm n hn

theorem y7c_M7_le_X (c : Ctx7 G L) (hb : B7Std c) : M7 c.s ≤ y7cX c.s := by
  intro m hm
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  have hc' : ⁅m, x⁆ ∈ M3 c.s :=
    (y7b_M7_comm_sq c hb.toB6Std).1 m hm x (y7b_M3_le_M7 c hx)
  have he : m * x * m⁻¹ = ⁅m, x⁆ * x := by rw [commutatorElement_def]; group
  rw [he]
  exact (M3 c.s).mul_mem hc' hx

theorem y7c_P7_le_X (c : Ctx7 G L) (hb : B7Std c) : P7 c.e ≤ y7cX c.s :=
  sup_le (y7c_M6_le_X c hb) (y7c_M7_le_X c hb)

theorem y7c_t_norm_P7 (c : Ctx7 G L) (hb : B7Std c) :
    ∀ x ∈ P7 c.e, c.s.t * x * c.s.t⁻¹ ∈ P7 c.e := by
  have htR : c.s.t ∈ c.s.R := s3_t_mem_R c.s
  have htN6 : c.s.t ∈ normalizer (M6 c.e : Set G) := y7b_R_le_NM6 c hb.toB5Std htR
  have htN7 : c.s.t ∈ normalizer (M7 c.s : Set G) := y7b_R_le_NM7 hb.hH htR
  have htP : c.s.t ∈ normalizer (P7 c.e : Set G) := by
    rw [P7]
    exact mem_normalizer_sup htN6 htN7
  intro x hx
  exact (Subgroup.mem_normalizer_iff.mp htP x).mp hx

theorem y7c_B_P_card (c : Ctx7 G L) (hb : B7Std c) : Nat.card ↥(y7cPC c) = 2 ^ 6 := by
  have h := y7c_card_img c.s (y7c_P7_le_X c hb) (y7c_M3_le_P7 c hb)
  rw [y7b_card_P7 c hb.toB6Std, y7c_card_M3 c.toCtx5 hb.hH] at h
  show Nat.card ↥(y7cImg c.s (P7 c.e)) = 2 ^ 6
  norm_num at h ⊢
  omega

theorem y7c_B_P_two (c : Ctx7 G L) (hb : B7Std c) : IsPGroup 2 ↥(y7cPC c) :=
  IsPGroup.of_card (by rw [y7c_B_P_card c hb])

theorem y7c_B_P_sup (c : Ctx7 G L) (hb : B7Std c) : y7cPC c = y7cM6C c ⊔ y7cM7C c := by
  change y7cImg c.s (M6 c.e ⊔ M7 c.s) = y7cImg c.s (M6 c.e) ⊔ y7cImg c.s (M7 c.s)
  rw [y7cImg_sup c.s (y7c_M6_le_X c hb) (y7c_M7_le_X c hb)]

theorem y7c_B_M6_E (c : Ctx7 G L) (hb : B7Std c) : IsE 4 ↥(y7cM6C c) := by
  have hcs := y7b_M6_comm_sq c hb.toB5Std
  have hV1M3 : V1 c.e ≤ M3 c.s := inf_le_right
  refine y7c_isE_img (s := c.s) (H := M6 c.e) (k := 4)
    (y7c_M6_le_X c hb) (y7c_M3_le_M6 c hb)
    (fun m hm n hn => hV1M3 (hcs.1 m hm n hn))
    (fun m hm => hV1M3 (hcs.2 m hm)) ?_ (y7c_card_M3 c.toCtx5 hb.hH)
  norm_num [y7b_card_M6 c hb.toB5Std]

theorem y7c_B_M7_E (c : Ctx7 G L) (hb : B7Std c) : IsE 4 ↥(y7cM7C c) := by
  have hcs := y7b_M7_comm_sq c hb.toB6Std
  refine y7c_isE_img (s := c.s) (H := M7 c.s) (k := 4)
    (y7c_M7_le_X c hb) (y7b_M3_le_M7 c) hcs.1 hcs.2 ?_
    (y7c_card_M3 c.toCtx5 hb.hH)
  norm_num [y7b_card_M7 c hb.toB6Std]

theorem y7c_B_M67 (c : Ctx7 G L) (hb : B7Std c) : y7cM6C c ≠ y7cM7C c := by
  intro h
  have h6 : y7cPre c.s (y7cM6C c) = M6 c.e :=
    y7cPre_img c.s (y7c_M6_le_X c hb) (y7c_M3_le_M6 c hb)
  have h7 : y7cPre c.s (y7cM7C c) = M7 c.s :=
    y7cPre_img c.s (y7c_M7_le_X c hb) (y7b_M3_le_M7 c)
  have hM : M6 c.e = M7 c.s := by rw [← h6, h, h7]
  have hcard : Nat.card ↥(M6 c.e) = Nat.card ↥(M5 c.e) := by
    rw [← y7b_M6_inf_M7 c hb.toB6Std, ← hM, inf_idem]
  rw [y7b_card_M6 c hb.toB5Std, y7b_card_M5 c hb.toB5Std] at hcard
  norm_num at hcard

theorem y7c_B_P_norm_t (c : Ctx7 G L) (hb : B7Std c) :
    ∀ x ∈ y7cPC c, y7cTC c hb * x * (y7cTC c hb)⁻¹ ∈ y7cPC c := by
  intro x hx
  obtain ⟨y, hyP, hyx⟩ := (mem_y7cImg c.s).mp hx
  have hPi : y7cPi c.s (⟨c.s.t, y7c_t_mem_X c hb⟩ * y * ⟨c.s.t, y7c_t_mem_X c hb⟩⁻¹)
      = y7cTC c hb * y7cPi c.s y * (y7cTC c hb)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
  rw [← hyx, ← hPi]
  refine (mem_y7cImg c.s).mpr
    ⟨⟨c.s.t, y7c_t_mem_X c hb⟩ * y * ⟨c.s.t, y7c_t_mem_X c hb⟩⁻¹, ?_, rfl⟩
  simpa using y7c_t_norm_P7 c hb (y : G) hyP

theorem y7c_B_P_cent_t (c : Ctx7 G L) (hb : B7Std c) :
    ∀ x ∈ y7cPC c, x * y7cTC c hb = y7cTC c hb * x → x ∈ y7cJC c := by
  intro x hx hcomm
  obtain ⟨p, hpP, hpEq⟩ := (mem_y7cImg c.s).mp hx
  have hcomm' : y7cPi c.s p * y7cTC c hb = y7cTC c hb * y7cPi c.s p := by
    rw [hpEq]
    exact hcomm
  have hmm : (p : G) * c.s.t * (p : G)⁻¹ * c.s.t⁻¹ ∈ M3 c.s :=
    y7c_comm_mem_M3 c hb (y := (p : G)) p.2 hcomm'
  obtain ⟨w, hwM3, hwH⟩ := y7c_coset_cent c hb hmm
  have hwX : w ∈ y7cX c.s := y7c_M3_le_X c.s hwM3
  have hMem : w⁻¹ * (p : G) ∈ centEl (P7 c.e) c.s.t := by
    rw [centEl, Subgroup.mem_inf]
    exact ⟨(P7 c.e).mul_mem ((P7 c.e).inv_mem (y7c_M3_le_P7 c hb hwM3)) hpP, hwH⟩
  have hS : w⁻¹ * (p : G) ∈ c.s.fr.S := by
    rw [← y7b_P7_cent_t c hb.toB6Std]
    exact hMem
  have hJ : w⁻¹ * (p : G) ∈ JF c.s := y7c_S_le_JF hb.hH hS
  refine (mem_y7cImg c.s).mpr
    ⟨(⟨w, hwX⟩ : ↥(y7cX c.s))⁻¹ * p, ?_, ?_⟩
  · show w⁻¹ * (p : G) ∈ JF c.s
    exact hJ
  · rw [map_mul, map_inv, (y7cPi_eq_one_iff c.s ⟨w, hwX⟩).mpr hwM3, inv_one, one_mul]
    exact hpEq

end CFSG.OddStandard.HigherRank.YamadaG23
