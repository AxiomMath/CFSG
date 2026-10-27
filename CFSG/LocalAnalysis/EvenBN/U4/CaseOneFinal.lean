module

public import CFSG.LocalAnalysis.EvenBN.U4.CaseOneOuter
public import CFSG.LocalAnalysis.EvenBN.U4.CaseOneOuterSwap
public import CFSG.LocalAnalysis.EvenBN.U4.CaseOneEndgame
public import CFSG.LocalAnalysis.EvenBN.Common.SL2TorusNine

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.EvenBN.Common (prodFactorOne prodFactorTwo mem_normalizer_inf
  mem_normalizer_sup)
open scoped MatrixGroups

theorem miyamotoBarEquiv_ne_one {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) :
    miyamotoBarEquiv h ≠ 1 := by
  intro e
  obtain ⟨ω, hω⟩ := h.exists_bar_ne
  exact hω ((miyamotoBarEquiv_apply h ω).symm.trans (DFunLike.congr_fun e ω))

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

theorem not_mem_L_of_act_eq_bar (_hS : Setting h L η t Q T) {u : G}
    (hu : u ∈ normalizer (L : Set G))
    (hact : miyamotoAct h L η ⟨u, hu⟩ = miyamotoFieldAut h (miyamotoBarEquiv h)) : u ∉ L := by
  intro huL
  have e : miyamotoAct h L η ⟨u, hu⟩ = MulAut.conj (η ⟨u, huL⟩) :=
    miyamotoAct_mem h L η ⟨u, huL⟩
  rw [hact] at e
  have := congrArg (miyamotoFieldFactor h) e
  rw [miyamotoFieldFactor_fieldAut, miyamotoFieldFactor_conj] at this
  exact miyamotoBarEquiv_ne_one h this

theorem not_mem_F1_of_act_eq_bar (hS : Setting h L η t Q T) {u : G}
    (hu : u ∈ centralizer ({t} : Set G))
    (hact : miyamotoAct h L η ⟨u, hS.centralizer_le_normalizer hu⟩ =
      miyamotoFieldAut h (miyamotoBarEquiv h)) : u ∉ miyamotoF1G h L η t := by
  intro huF
  have huP : u ∈ miyamotoPG h L η := by
    rw [← hS.RG_inf_C]
    exact mem_inf.2 ⟨le_sup_left.trans hS.P1_le_miyamotoRG huF, hu⟩
  exact hS.not_mem_L_of_act_eq_bar _ hact (miyamotoPull_le h L η _ huP)


theorem conj_t_ne_mul_of_act_eq_bar (hS : Setting h L η t Q T) {k₂ : Type} [Field k₂]
    [Fintype k₂] (hk₂ : Fintype.card k₂ = (2 ^ f) ^ 2) (ψ₂ : miyamotoM2G h L η t Q ≃* SL(2, k₂))
    (u : G) (hu : u ∈ centralizer ({t} : Set G)) (huu : u * u = 1)
    (hact : miyamotoAct h L η ⟨u, hS.centralizer_le_normalizer hu⟩ =
      miyamotoFieldAut h (miyamotoBarEquiv h))
    (r : G) (hr : r ∈ miyamotoRG h L η t Q) (g : G) : g⁻¹ * t * g ≠ u * r := by
  obtain ⟨k, _, _, hk, ψ, α, hψα, hψt⟩ := hS.sec3_15_iso
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP k 2 := charP_of_card_eq_prime_pow (f := 2 * f) (by rw [hk, ← pow_mul, mul_comm])
  have hZF := hS.centerIn_U_le_F_of_case_one hk₂ ψ₂ hk ψ
  have hZ := (hS.F1_eq_centerIn_U_sup_r1 hk hψt hZF).1
  have huN := hS.centralizer_le_normalizer hu
  have hut : u * t = t * u := mem_centralizer_singleton_iff.1 hu
  have huW := hS.mem_normalizer_W_of_act_eq_bar huN hact hut
  have huF1 := mem_normalizer_F1G_of_act_eq_bar huN hact hut
  have hu1 := hS.not_mem_F1_of_act_eq_bar hu hact
  have hroot := card_rootA_inf_centralizer_of_act_eq_bar huN hact
  have h4 : 4 ≤ Nat.card k := by
    rw [Nat.card_eq_fintype_card, hk]
    exact hS.four_le.trans (Nat.le_self_pow two_ne_zero _)
  rcases Common.conj_prodFactor_eq_or_swap h4 ψ (mem_normalizer_M1G_of_act_eq_bar huN hact hut)
    with ⟨h1, h2⟩ | ⟨h1, h2⟩
  ·
    have hX1 : ∀ x ∈ prodFactorOne ψ, u * x * u⁻¹ ∈ prodFactorOne ψ := fun x hx => by
      rw [← h1]
      exact ⟨x, hx, rfl⟩
    have hX2 : ∀ x ∈ prodFactorTwo ψ, u * x * u⁻¹ ∈ prodFactorTwo ψ := fun x hx => by
      rw [← h2]
      exact ⟨x, hx, rfl⟩
    exact hS.conj_t_ne_mul_of_outer hψα huu hut huW huF1 hu1 hroot
      (Or.inr ⟨hX1, hX2, exists_mem_N1G_orderOf_of_act_eq_bar huN hact⟩) hr g
  ·
    have hup := hS.t_mul_mem_normalizer huN
    have hactp := hS.act_t_mul_of_act_eq_bar huN hact
    have hutp : t * u * t = t * (t * u) := t_mul_mul_t_of_commute hut
    have huup : t * u * (t * u) = 1 := (hS.t_mul_mul_self hut).trans huu
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right hS.t_mul_t
    have hconj : ∀ x : G, t * u * x * (t * u)⁻¹ = t⁻¹ * (u * x * u⁻¹) * t := fun x => by
      calc t * u * x * (t * u)⁻¹ = t * (u * x * u⁻¹) * t⁻¹ := by group
        _ = t⁻¹ * (u * x * u⁻¹) * t := by rw [hti]
    have hX1 : ∀ x ∈ prodFactorOne ψ, t * u * x * (t * u)⁻¹ ∈ prodFactorOne ψ := fun x hx => by
      rw [hconj]
      exact hS.t_conj_mem_X1 hψt (by rw [← h1]; exact ⟨x, hx, rfl⟩)
    have hX2 : ∀ x ∈ prodFactorTwo ψ, t * u * x * (t * u)⁻¹ ∈ prodFactorTwo ψ := fun x hx => by
      rw [hconj]
      exact hS.t_conj_mem_X2 hψt (by rw [← h2]; exact ⟨x, hx, rfl⟩)
    have hD : ∀ d ∈ miyamotoDG h L η, t * u * d * (t * u)⁻¹ = d ^ (2 ^ f) := by
      intro d hd
      rw [← range_miyamotoDHom h L η] at hd
      obtain ⟨a, rfl⟩ := MonoidHom.mem_range.1 hd
      exact conj_miyamotoDHom_of_act_eq_bar hup hactp a
    have hE := hS.mul_mem_centralizer_E hk hψt hψα hZ huup hutp
      (hS.mem_normalizer_EG_of_act_eq_bar hup hactp hutp) hX1 hX2 hD
    rw [← mul_assoc, hS.t_mul_t, one_mul] at hE
    have hUp : t * u ∈ normalizer ((miyamotoF1G h L η t ⊔
        ((miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G)) ⊓ prodFactorOne ψ) :
          Subgroup G) : Set G) :=
      mem_normalizer_sup (mem_normalizer_F1G_of_act_eq_bar hup hactp hutp)
        (mem_normalizer_inf (hS.mem_normalizer_W_of_act_eq_bar hup hactp hutp)
          (mem_normalizer_fintype fun x hx => hX1 x hx))
    have hZp := normalizer_le_normalizer_centerIn _ hUp
    have hvZ : ∀ z ∈ CFSG.centerIn (miyamotoF1G h L η t ⊔
        ((miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G)) ⊓ prodFactorOne ψ)),
        u * z * u⁻¹ ∈ (CFSG.centerIn (miyamotoF1G h L η t ⊔
          ((miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G)) ⊓
            prodFactorOne ψ))).map (MulAut.conj t).toMonoidHom := by
      intro z hz
      refine ⟨t * u * z * (t * u)⁻¹, (mem_normalizer_iff.1 hZp z).1 hz, ?_⟩
      show t * (t * u * z * (t * u)⁻¹) * t⁻¹ = u * z * u⁻¹
      calc t * (t * u * z * (t * u)⁻¹) * t⁻¹ = t * t * u * z * u⁻¹ * (t * t)⁻¹ := by group
        _ = u * z * u⁻¹ := by rw [hS.t_mul_t, one_mul, inv_one, mul_one]
    exact hS.conj_t_ne_mul_of_outer hψα huu hut huW huF1 hu1 hroot
      (Or.inl (hS.card_lt_card_F1_inf_centralizer hk hψt hZF huu hE
        (mul_miyamotoR1G_of_act_eq_bar huN hact) hvZ)) hr g

theorem false_of_case_one (hS : Setting h L η t Q T) {k₂ : Type} [Field k₂] [Fintype k₂]
    (hk₂ : Fintype.card k₂ = (2 ^ f) ^ 2) (ψ₂ : miyamotoM2G h L η t Q ≃* SL(2, k₂)) : False :=
  hS.false_of_case_one_of_outer hk₂ ψ₂ fun u hu huu hact r hr g =>
    hS.conj_t_ne_mul_of_act_eq_bar hk₂ ψ₂ u hu huu hact r hr g

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
