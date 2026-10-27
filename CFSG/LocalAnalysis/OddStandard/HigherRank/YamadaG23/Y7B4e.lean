module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B3f
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B4c
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B4d

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7b_exists_R5_mul (c : Ctx7 G L) (hb : B6Std c) {x : G} (hx : x ∈ X76 c.e)
    (hxt : ⁅x, c.s.t⁆ ∈ M5 c.e) : ∃ r ∈ R5 c.e, ∃ n ∈ c.s.T ⊓ X76 c.e, x = r * n := by
  obtain ⟨m, hm, hmy⟩ := y7b_exists_adjust c hb.toB5Std hxt
  have hm6 : m ∈ M6 c.e := y7b_M5_le_M6 c hb.toB5Std hm
  have hmX : m ∈ X76 c.e := y7b_M6_le_X76 c hb hm6
  have hyX : m * x ∈ X76 c.e := (X76 c.e).mul_mem hmX hx
  have ht2 : c.s.t * c.s.t = 1 := by
    have h := pow_orderOf_eq_one c.s.t
    rwa [c.s.t_order, pow_two] at h
  have htV : ∀ v ∈ V2 c.e, c.s.t * v * c.s.t⁻¹ ∈ V2 c.e := by
    intro v hv
    exact (Subgroup.mem_normalizer_iff.mp (y7b_R_le_NV2 c hb.toB5Std (s3_t_mem_R c.s)) v).1 hv
  have hxV : ∀ v ∈ V2 c.e, (m * x) * v * (m * x)⁻¹ ∈ V2 c.e := by
    intro v hv
    exact (Subgroup.mem_normalizer_iff.mp hyX.2 v).1 hv
  have hcent : centEl (V2 c.e) c.s.t = cen c.s.fr.B := by
    rw [centEl, inf_comm]
    exact y7b_H_inf_V2 c hb.toB5Std
  have hnorm := mem_normalizer_cent_sup_zpowers (V := V2 c.e) (t := c.s.t) (x := m * x)
    (y7b_V2_elem c hb.toB5Std) ht2 htV hxV hmy
  rw [hcent] at hnorm
  have hySX : m * x ∈ c.s.X := by
    rwa [(B5Std.fact33 hb.toB5Std).1.1]
  obtain ⟨c', hc', n, hn, hy_eq⟩ := f3_X_eq_C₂N hb.hH (m * x) hySX
  have hc'R5 : c' ∈ R5 c.e := y7b_C2_le_R5 c hb.toB5Std hc'
  have hc'X : c' ∈ X76 c.e := y7b_R5_le_X76 c hb hc'R5
  have hnX : n ∈ X76 c.e := by
    have hne : n = c'⁻¹ * (m * x) := by rw [hy_eq]; group
    rw [hne]
    exact (X76 c.e).mul_mem ((X76 c.e).inv_mem hc'X) hyX
  have hnT : n ∈ c.s.T := y7b_X76_inf_H_le_T c hb ⟨hnX, hn.1⟩
  have hxr : x = (m⁻¹ * c') * n := by
    calc x = m⁻¹ * (m * x) := by group
      _ = m⁻¹ * (c' * n) := by rw [hy_eq]
      _ = (m⁻¹ * c') * n := by group
  exact ⟨m⁻¹ * c', (R5 c.e).mul_mem ((R5 c.e).inv_mem (Subgroup.mem_sup_right hm)) hc'R5,
    n, ⟨hnT, hnX⟩, hxr⟩

theorem y7b_X76_isPGroup (c : Ctx7 G L) (hb : B6Std c) : IsPGroup 2 ↥(X76 c.e) := by
  refine isPGroup_of_prime_order_mem (p := 2) (K := ⊥) IsPGroup.of_bot bot_le ?_
  intro x hx q hq hq2 hxq
  have hqodd : Odd q := hq.eq_two_or_odd'.resolve_left hq2
  have hSM5norm := y7b_SM5_le_NM5 c hb.toB5Std
  have hSM5 := y7b_SM5_comm_sq c hb
  have hxtM5 : ⁅x, c.s.t⁆ ∈ M5 c.e :=
    comm_mem_of_odd_pow_eq_one (X := X76 c.e) (W := SM5 c.e) (M := M5 c.e) (t := c.s.t)
      le_sup_right
      (fun w hw m hm => (Subgroup.mem_normalizer_iff.mp (hSM5norm hw) m).1 hm)
      hSM5.1 hSM5.2 (y7b_X76_comm_SM5 c hb) (y7b_X76_comm_t c hb) hx hqodd hxq
  obtain ⟨r, hr, n, hn, hxrn⟩ := y7b_exists_R5_mul c hb hx hxtM5
  have hT2 : IsPGroup 2 ↥(c.s.T ⊓ X76 c.e) := c.s.sylow_T.2.1.to_le inf_le_left
  have hR52 : IsPGroup 2 ↥(R5 c.e) := y7b_R5_isPGroup c hb
  have hnorm : c.s.T ⊓ X76 c.e ≤ normalizer (R5 c.e : Set G) := fun z hz => hz.2.1.1.1
  have hK2 : IsPGroup 2 ↥((c.s.T ⊓ X76 c.e) ⊔ R5 c.e) :=
    isPGroup_sup_of_le_normalizer hT2 hR52 hnorm
  have hxK : x ∈ (c.s.T ⊓ X76 c.e) ⊔ R5 c.e := by
    rw [hxrn]
    exact (sup_comm (R5 c.e) (c.s.T ⊓ X76 c.e)) ▸ Subgroup.mul_mem_sup hr hn
  haveI : Fact q.Prime := ⟨hq⟩
  have hx1 : x = 1 := eq_one_of_isPGroup_of_pow_prime (p := 2) (q := q) hq2 hK2 hxK hxq
  rw [hx1]
  exact Subgroup.mem_bot.mpr rfl

end CFSG.OddStandard.HigherRank.YamadaG23
