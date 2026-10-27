module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoFinalAType
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoFinalACent

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Subgroup

variable {G : Type} [Group G] {z : G}

structure JankoFinalW (fr : JankoFrame G z) (m : G) (W : Subgroup G) (s : G) : Prop where
  choiceM : JankoChoiceM fr m
  comm_mem_S : ∀ x ∈ fr.I, ∀ u ∈ fr.U, u * x * u⁻¹ * x⁻¹ ∈ fr.S
  I_eq : fr.I = fr.E ⊔ fr.S
  E_inf_S : fr.E ⊓ fr.S = ⊥
  I_inf_centralizer_U : fr.I ⊓ centralizer (fr.U : Set G) = fr.S
  card_U_inf_centralizer : ∀ e ∈ fr.E, e ≠ 1 →
    Nat.card (fr.U ⊓ centralizer ({e} : Set G) : Subgroup G) = 3 ^ 7
  exists_conj_mul : ∀ e ∈ fr.E, e ≠ 1 → ∀ y ∈ fr.S, ∃ u ∈ fr.U, u * e * u⁻¹ = e * y
  exists_conj_mem_E : ∀ x ∈ fr.I, x ∉ fr.S →
    ∃ e ∈ fr.E, e ≠ 1 ∧ e⁻¹ * x ∈ fr.S ∧ ∃ u ∈ fr.U, u * x * u⁻¹ = e
  card_type_s₃ : Nat.card {x : G // x ∈ fr.I ∧ x ∉ fr.S ∧ IsConj x fr.s₃} = 72
  centralizer_UK_le : ∀ e ∈ fr.E, (fr.U ⊔ fr.K) ⊓ centralizer ({e} : Set G) ≤
    fr.K ⊓ centralizer ({e} : Set G) ⊔ fr.U ⊓ centralizer ({e} : Set G)
  isConj_of_le_UK : ∀ e ∈ fr.E, e ≠ 1 → ∀ B : Subgroup G,
    B ≤ (fr.U ⊔ fr.K) ⊓ centralizer ({e} : Set G) → Nat.card B = 3 ^ 8 → IsConj e fr.s₃
  s_mem_E : s ∈ fr.E
  orderOf_s : orderOf s = 3
  zpowers_s : zpowers s = fr.E ⊓ centralizer ({m} : Set G)
  card_centralizer_s :
    Nat.card (centralizer ({s} : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G) = 162
  isConj_s : IsConj s fr.s₃
  s_not_mem_P₁ : s ∉ fr.P₁
  t_mul_s : fr.t * s * fr.t⁻¹ = s⁻¹
  W_eq : W = fr.U ⊓ centralizer ({s} : Set G) ⊔ zpowers m
  card_W : Nat.card W = 3 ^ 8
  W_inf_U : W ⊓ fr.U = fr.U ⊓ centralizer ({s} : Set G)
  W_inf_N : W ⊓ fr.N = fr.I
  W_sup_U : W ⊔ fr.U = fr.R m
  R_inf_centralizer : fr.R m ⊓ centralizer ({s} : Set G) = W
  centralizer_UK : (fr.U ⊔ fr.K) ⊓ centralizer ({s} : Set G) = W ⊔ zpowers z
  card_centralizer_UK :
    Nat.card ((fr.U ⊔ fr.K) ⊓ centralizer ({s} : Set G) : Subgroup G) = 2 * 3 ^ 8
  le_W_of_odd : ∀ B : Subgroup G, Odd (Nat.card B) →
    B ≤ (fr.U ⊔ fr.K) ⊓ centralizer ({s} : Set G) → B ≤ W
  z_mem_normalizer_W : z ∈ normalizer (W : Set G)
  t_mem_normalizer_W : fr.t ∈ normalizer (W : Set G)
  S_inf_centralizer_W : fr.S ⊓ centralizer (W : Set G) = fr.P3bar
  card_W_inf_z : Nat.card (W ⊓ centralizer ({z} : Set G) : Subgroup G) = 3 ^ 4
  card_W_inf_t : Nat.card (W ⊓ centralizer ({fr.t} : Set G) : Subgroup G) = 3 ^ 3
  card_W_inf_tz : Nat.card (W ⊓ centralizer ({fr.t * z} : Set G) : Subgroup G) = 3 ^ 3

open JankoTwelve JankoFinal in
theorem exists_jankoFinalW [Finite G] (fr : JankoFrame G z) (hset : JankoSetting G z)
    (hfrs : JankoFrames G) (p7 : JankoProp7 fr)
    (p9 : ¬ centralizer (fr.P₁ : Set G) ≤ centralizer ({z} : Set G)) (p10 : JankoProp10 fr)
    (p11 : JankoProp11 fr) (p12 : JankoProp12 fr) {m : G} (hm : JankoChoiceM fr m) :
    ∃ (W : Subgroup G) (s : G), JankoFinalW fr m W s := by
  have h : Hyp fr := ⟨hset, hfrs, p7, p9, p10, p11⟩
  obtain ⟨s, hs, hs3⟩ := exists_zpowers_eq h hm
  exact ⟨Wof fr m s, s,
    { choiceM := hm
      comm_mem_S := fun x hx u hu => comm_mem_S h p12 hx hu
      I_eq := h.I_eq_E_sup_S
      E_inf_S := E_inf_S h
      I_inf_centralizer_U := by rw [p12.centralizer_U, inf_eq_right.mpr (S_le_I h)]
      card_U_inf_centralizer := fun e he he1 => card_U_inf_centralizer_E h p12 he he1
      exists_conj_mul := fun e he he1 y hy => exists_conj_eq_mul h p12 he he1 hy
      exists_conj_mem_E := fun x hx hxS => exists_conj_mem_E h p12 hx hxS
      card_type_s₃ := card_type_s₃_I h p12
      centralizer_UK_le := fun e he => UK_inf_le_of_mem h p12 he
      isConj_of_le_UK := fun e he he1 B hB hcard => isConj_of_le_UK h p12 he he1 hB hcard
      s_mem_E := s_mem_E hs
      orderOf_s := hs3
      zpowers_s := hs.symm
      card_centralizer_s := card_centralizer_s h hm hs hs3
      isConj_s := isConj_s h hm hs hs3
      s_not_mem_P₁ := s_not_mem_P₁ h hm hs hs3
      t_mul_s := t_mul_s h hm hs hs3
      W_eq := rfl
      card_W := card_W h p12 hm hs hs3
      W_inf_U := W_inf_U h p12 hm hs
      W_inf_N := W_inf_N h p12 hm hs hs3
      W_sup_U := W_sup_U
      R_inf_centralizer := R_inf_centralizer h p12 hm hs hs3
      centralizer_UK := UK_inf_centralizer_eq h p12 hm hs hs3
      card_centralizer_UK := by
        rw [UK_inf_centralizer_eq h p12 hm hs hs3, card_W_sup_z h p12 hm hs hs3]
      le_W_of_odd := fun B hB hBle => le_W_of_odd h p12 hm hs hs3 hB hBle
      z_mem_normalizer_W := z_mem_normalizer_W h hm hs
      t_mem_normalizer_W := t_mem_normalizer_W h hm hs hs3
      S_inf_centralizer_W := S_inf_centralizer_W h hm
      card_W_inf_z := card_W_inf_z h p12 hm hs hs3
      card_W_inf_t := card_W_inf_t h p12 hm hs hs3
      card_W_inf_tz := card_W_inf_tz h p12 hm hs hs3 }⟩

theorem exists_jankoFinalW' [Finite G] (fr : JankoFrame G z) (hset : JankoSetting G z)
    (hfrs : JankoFrames G) (p7 : JankoProp7 fr)
    (p9 : ¬ centralizer (fr.P₁ : Set G) ≤ centralizer ({z} : Set G)) (p10 : JankoProp10 fr)
    (p11 : JankoProp11 fr) (p12 : JankoProp12 fr) :
    ∃ (m : G) (W : Subgroup G) (s : G), JankoFinalW fr m W s := by
  obtain ⟨m, hm⟩ := p12.exists_choiceM
  exact ⟨m, exists_jankoFinalW fr hset hfrs p7 p9 p10 p11 p12 hm⟩

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
