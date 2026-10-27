module

public import CFSG.GH74.GLS.C3.Layer1.Th2T1Rel
public import CFSG.GH74.GLS.C3.Layer1.Thm1P31

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.C3.Layer1
open CFSG.Open (ordA)

section Shapes

theorem card_eq_ordA_of_hasL2Model {J : Type} [Group J] {m : ℕ}
    (h : HasL2Model J (fun q => q = m)) : Nat.card J = ordA 1 m := by
  obtain ⟨p, f, -, -, hq, hL⟩ := h
  have := CFSG.GH74.card_of_lieModel_PSL (n := 2) (by norm_num) hL
  rw [hq] at this
  exact this

theorem not_hasL2Model_five_of_sq {J : Type} [Group J] {r : ℕ} (hr : Odd r) (hr5 : 5 ≤ r)
    (h : HasL2Model J (fun q => q = r ^ 2)) : ¬ HasL2Model J (fun q => q = 5) := fun h5 => by
  have h1 := card_eq_ordA_of_hasL2Model h
  have h60 := Th2.L625.card_of_l2_five h5
  have hge : 7 ≤ r ^ 2 := by nlinarith
  have := Th2.L625.le_ordA_of_odd_of_seven_le hr.pow hge
  omega

theorem not_hasL2Model_five_of_alt7 {J : Type} [Group J]
    (h : Nonempty (J ≃* alternatingGroup (Fin 7))) : ¬ HasL2Model J (fun q => q = 5) := fun h5 => by
  obtain ⟨e⟩ := h
  have h60 := Th2.L625.card_of_l2_five h5
  have h7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  rw [Nat.card_congr e.toEquiv, h7] at h60
  omega

theorem not_hasL2Model_five_of_pumpShape {J : Type} [Group J] {r : ℕ} (hr : Odd r) (hr5 : 5 ≤ r)
    (h : HasL2Model J (fun q => q = r ^ 2) ∨ Nonempty (J ≃* alternatingGroup (Fin 7))) :
    ¬ HasL2Model J (fun q => q = 5) :=
  h.elim (not_hasL2Model_five_of_sq hr hr5) not_hasL2Model_five_of_alt7

theorem not_hasL2Model_five_of_not_inC2
    {J : Type} [Group J] (hU : InU2 J) (hN : ¬ InC2 J) :
    ¬ HasL2Model J (fun q => q = 5) := by
  rintro ⟨p, f, hp, hf, h5, hL⟩
  exact hN (Th2.L625.inC2_of_l2_fm9 hU ⟨p, f, hp, hf, h5 ▸ Th2Tstar.isFM9_five, hL⟩)

theorem sixty_lt_card_of_shape_of_not_five {J : Type} [Group J]
    (hshape : HasL2Model J Odd ∨ Nonempty (J ≃* alternatingGroup (Fin 7)))
    (h5 : ¬ HasL2Model J (fun q => q = 5)) : 60 < Nat.card J := by
  rcases hshape with ⟨p, f, hp, hf, hodd, hL⟩ | ⟨⟨e⟩⟩
  · obtain ⟨F, _, _, _, hF, hFq⟩ := Th2.Bal.exists_l2Field_of_lieModel hodd hL
    have h3 : 3 < p ^ f := hFq ▸ hF.2
    have h5' : p ^ f ≠ 5 := fun h => h5 ⟨p, f, hp, hf, h, hL⟩
    have h7 : 7 ≤ p ^ f := by
      obtain ⟨k, hk⟩ := hodd
      omega
    have hc := CFSG.GH74.card_of_lieModel_PSL (n := 2) (by norm_num) hL
    have := Th2.L625.le_ordA_of_odd_of_seven_le hodd h7
    have hc' : Nat.card J = ordA 1 (p ^ f) := hc
    omega
  · have h7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
      decide
    rw [Nat.card_congr e.toEquiv, h7]
    norm_num

end Shapes

theorem fmax1_not_five (h102 : B_ivk_10_2) (hL34 : B_gen4_noL34_elem)
    {G : Type} [Group G] [Finite G] (hG : C3Hyp G) {x y : G} {K : Subgroup G} {f : G}
    (hmax : FMax1 x y K f) {x₀ y₀ : G} {K₀ : Subgroup G} {f₀ : G} (h₀ : IsFU2 x₀ y₀ K₀ f₀)
    (h5₀ : ¬ HasL2Model (kBar K₀) (fun q => q = 5)) :
    ¬ HasL2Model (kBar K) (fun q => q = 5) := fun h5 => by
  have hshape := C3.Layer1.Thm1.kBar_model_of_U2 hG h102 hL34 h₀.1
  have h60 := sixty_lt_card_of_shape_of_not_five hshape h5₀
  have hle := hmax.2 x₀ y₀ K₀ f₀ h₀
  have h60' := Th2.L625.card_of_l2_five h5
  omega

end CFSG.GH74.GLS

namespace CFSG.GH74.GLS.C3.Layer1.Thm1

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1

theorem card_le_two_of_noV2Fine {G : Type} [Group G] [Finite G] (hV : NoV2Fine G) {x y : G}
    {K : Subgroup G} (h𝒰 : Is2TerminalU2Triple x y K)
    (h5 : ¬ HasL2Model (kBar K) (fun q => q = 5)) :
    ∀ A : Subgroup G, A ≤ CMK (centralizer ({x} : Set G)) K → IsElementaryAbelian 2 ↥A →
      Nat.card ↥A ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro A hAC hA
  by_contra hlt
  push Not at hlt
  have hAC' : A ≤ CxK x K := hAC
  obtain ⟨r, hr⟩ := (IsPGroup.iff_card).1 (IsElementaryAbelian.isPGroup 2 ↥A)
  have hr2 : 2 ≤ r := by
    by_contra hr2
    push Not at hr2
    have h2r : 2 ^ r ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hA' : IsElementaryAbelian 2 ↥(A.subgroupOf (CxK x K)) := by
    have := hA
    exact IsElementaryAbelian.subgroupOf hAC'
  have hcard : Nat.card ↥(A.subgroupOf (CxK x K)) = 2 ^ r := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC').toEquiv]
    exact hr
  have h2 : 2 ≤ pRank 2 ↥(CxK x K) :=
    hr2.trans (LieType.SteinbergBR.le_pRank_of_card one_lt_two _ hA' hcard)
  exact h5 (hV x y K ⟨h𝒰.1, h𝒰.2.1, Or.inl h2, fun _ => h𝒰⟩)

theorem not_hasL2Model_nine_of_noV2Fine {G : Type} [Group G] (hV : NoV2Fine G) {x y : G}
    {K : Subgroup G} (h𝒰 : Is2TerminalU2Triple x y K)
    (h5 : ¬ HasL2Model (kBar K) (fun q => q = 5)) :
    ¬ HasL2Model (kBar K) (fun q => q = 9) := fun h =>
  h5 (hV x y K ⟨h𝒰.1, h𝒰.2.1, Or.inl (h𝒰.2.2.2.2 h).1, fun _ => h𝒰⟩)

theorem kBar_autData_rel
    {G : Type} [Group G] [Finite G] (h2hb : IVK.IVK_1_2h_b) (hV : NoV2Fine G)
    {x y : G} {K : Subgroup G} (h𝒰 : Is2TerminalU2Triple x y K)
    (hshape : HasL2Model (kBar K) Odd ∨ Nonempty (kBar K ≃* alternatingGroup (Fin 7)))
    (h5 : ¬ HasL2Model (kBar K) (fun q => q = 5)) :
    Function.Injective (MulAut.conj : kBar K →* MulAut (kBar K)) ∧ AutLevelF (kBar K) := by
  rcases hshape with h | ⟨⟨e7⟩⟩
  · obtain ⟨F, _, _, _, ⟨e⟩⟩ := exists_l2_model_of_hasL2Model h
    exact ⟨IVK.conj_injective_of_L2 e,
      autLevelF_of_L2 h2hb (not_hasL2Model_nine_of_noV2Fine hV h𝒰 h5) h⟩
  · exact ⟨conj_injective_of_A7 e7, autLevelF_of_A7 e7⟩

end CFSG.GH74.GLS.C3.Layer1.Thm1
