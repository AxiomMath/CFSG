module

public import CFSG.GH74.GLS.C3.Layer1.BkS4Core
public import CFSG.GH74.GLS.C3.Layer1.BackAuxSA
public import CFSG.GH74.GLS.Bg.Rank
public import CFSG.GH74.GLS.C3.Layer1.BackAction
public import CFSG.GH74.GLS.C3.Layer1.BackStmt

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1.Back

theorem sec4Core_gen {G : Type} [Group G] [Finite G] (hG : C3Hyp G) {x : G}
    {K M T Q : Subgroup G} (hh : Hyp9 x K K M T Q) (p91 : Prop91Concl K M T Q)
    (hs : IsSimpleGroup (kBar K)) (hn : ∃ a b : kBar K, a * b ≠ b * a)
    (hTS : ¬ IsSylowOf 2 T ⊤) (hPD8 : IsD8 (T ⊓ K)) :
    ∃ (a : G) (S : Subgroup G), Sec4Core a (T ⊓ K) Q T S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA := hh.a
  have hLn : ∀ m ∈ M, ∀ l ∈ K, m * l * m⁻¹ ∈ K := hA.L_normal.2
  have hTM : T ≤ M := hA.sylowTM.le
  have hT2 : IsPGroup 2 ↥T := hA.sylowT.isPGroup
  obtain ⟨-, hPQcomm, hPQ⟩ := hA.R_eq hs hn
  obtain ⟨S, hS, hTlt, a, haS, haN, haT, ha2⟩ := exists_sylow_gt_and_a hT2 hTS
  have hQT : Q ≤ T := Setup91.Q_le_T hA
  have hQeq : T ⊓ CMK M K = Q :=
    hA.sylowQ.eq_of_le (le_inf hQT hA.sylowQ.le) inf_le_right hT2.to_inf_left
  have hPT : T ⊓ K ≤ T := inf_le_left
  have hPn : ∀ t ∈ T, ∀ p ∈ T ⊓ K, t * p * t⁻¹ ∈ T ⊓ K := fun t ht p hp =>
    ⟨T.mul_mem (T.mul_mem ht hp.1) (T.inv_mem ht), hLn t (hTM ht) p hp.2⟩
  set ψ : ↥M →* MulAut (kBar K) := Back.actHom hLn with hψ
  have hψker : ∀ m : ↥M, ψ m = 1 ↔ (m : G) ∈ CMK M K := by
    intro m
    have h := Subgroup.ext_iff.1 (Back.actHom_ker hLn) m
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf] at h
    exact h
  have hQn : ∀ t ∈ T, ∀ q ∈ Q, t * q * t⁻¹ ∈ Q := by
    intro t ht q hq
    rw [← hQeq]
    refine ⟨T.mul_mem (T.mul_mem ht (hQT hq)) (T.inv_mem ht), ?_⟩
    have hqM : q ∈ M := hTM (hQT hq)
    have hψq : ψ ⟨q, hqM⟩ = 1 := (hψker _).2 (hA.sylowQ.le hq)
    have htqM : t * q * t⁻¹ ∈ M := M.mul_mem (M.mul_mem (hTM ht) hqM) (M.inv_mem (hTM ht))
    have : ψ ⟨t * q * t⁻¹, htqM⟩ = 1 := by
      have e : (⟨t * q * t⁻¹, htqM⟩ : ↥M) = ⟨t, hTM ht⟩ * ⟨q, hqM⟩ * ⟨t, hTM ht⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, hψq, mul_one, map_inv, mul_inv_cancel]
    exact (hψker _).1 this
  refine ⟨a, S, ?_⟩
  exact
    { T_pgroup := hT2
      S_pgroup := hS.isPGroup
      T_le_S := hTlt.le
      a_mem := haS
      a_mem_norm := haN
      a_not_mem := haT
      a_sq_mem := by rw [← sq]; exact ha2
      P_le := hPT
      Q_le := hQT
      P_norm := hPn
      Q_norm := hQn
      P_d8 := hPD8
      Q_shape := Or.inl p91.1.1
      Q_card := p91.1.2
      PQ_comm := hPQcomm
      PQ_disj := hPQ
      cent6 := by
        intro u hu hu1 huT s hsS hsu
        have hu2 : orderOf u = 2 := by
          have := (forall_of_isElementaryAbelian p91.1.1).2 u hu
          exact orderOf_eq_prime (by rwa [sq]) hu1
        have hsyl : IsSylowOf 2 T (centralizer ({u} : Set G)) := hA.cent5 u hu huT hu2
        have hsC : s ∈ centralizer ({u} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 hsu
        have hle : T ⊔ zpowers s ≤ centralizer ({u} : Set G) :=
          sup_le hsyl.le (zpowers_le.2 hsC)
        have hleS : T ⊔ zpowers s ≤ S := sup_le hTlt.le (zpowers_le.2 hsS)
        have heq : T ⊔ zpowers s = T :=
          hsyl.eq_of_le le_sup_left hle (hS.isPGroup.to_le hleS)
        exact heq ▸ Subgroup.mem_sup_right (mem_zpowers s)
      rank4 := by
        intro E hE
        have h1 := card_eq_two_pow_pRank hE
        have h2 : pRank 2 ↥E ≤ pRank 2 G := Bg.pRank_subgroup_le one_lt_two E
        have h3 := hG.pRank_eq_four
        rw [h1]
        calc 2 ^ pRank 2 ↥E ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = 16 := by norm_num }

end CFSG.GH74.GLS.C3.Layer1.Bk
