module

public import CFSG.Quasithin.H13.L32NLem14413j
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14413b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14413h

public section

namespace CFSG.Quasithin.H13.L14413

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13.A6
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace XCtx_F4
open CFSG.Quasithin.H13.L14413.XCtx_F4

variable {T L V V₂ X : Subgroup G} {g : G}

section Basic

variable (C : XCtx_F4 G T L V V₂ X g)
include C

theorem not_L2_le_T_F4 : ¬ lOne L V₂ ≤ T := by
  intro hle
  obtain ⟨z, hz, hz1, -⟩ := C.exists_z_F4
  obtain ⟨b, hbV₂, hbV₁⟩ := C.abs.exists_mem_not_mem
  obtain ⟨k, hk, hkz, -, -⟩ := L128P.exists_rotation_mem_F4 C.h1222 C.s1282.hyp C.s1282.v1
    C.plane.1 C.plane.2 hz hz1 hbV₂ hbV₁
  have hkT : k ∈ T := hle (C.oTwoUpper_p128_le_F4 hk)
  have := (Subgroup.mem_normalizer_iff.mp (C.s1282.v1.2.2 hkT) z).mp hz
  rw [hkz] at this
  exact hbV₁ this

theorem T_le_normalizer_L1_F4 : T ≤ Subgroup.normalizer (lOne L (fsuV1 T V) : Set G) := by
  intro t ht
  have htN : t ∈ Subgroup.normalizer
      ((L ⊓ Subgroup.normalizer (fsuV1 T V : Set G) : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨C.s1282.hyp.hyp.normalizes ht,
      Subgroup.le_normalizer (C.s1282.v1.2.2 ht)⟩
  exact Subgroup.mem_normalizer_fintype fun y hy => conj_mem_oTwoUpper htN hy

theorem pCore_H3_le_T_F4 :
    CFSG.Open.pCore 2 ↥(lOne L V₂ ⊔ X ⊔ T) ≤ T.subgroupOf (lOne L V₂ ⊔ X ⊔ T) := by
  have : (CFSG.Open.pCore 2 ↥(lOne L V₂ ⊔ X ⊔ T)).Normal :=
    CFSG.LieType.BorelTits.pCore_normal (G := ↥(lOne L V₂ ⊔ X ⊔ T)) (r := 2)
  exact IsPGroup.le_sylow_of_normal
    (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥(lOne L V₂ ⊔ X ⊔ T)) (r := 2))
    (A4.toSylow C.sylow_H3_F4)

end Basic

structure Orders_F4 (C : XCtx_F4 G T L V V₂ X g) : Prop where

  hD1 : quasithinO2QuotientIso (L ⊔ T) SL3.S

  hD2a : quasithinO2QuotientIso (lOne L (fsuV1 T V) ⊔ X ⊔ T)
    (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) × Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))

  hD2b : quasithinO2QuotientIso (lOne L V₂ ⊔ X ⊔ T) SL3.S

  L1_3 : (pCoreOf 2 (lOne L (fsuV1 T V))).relIndex (lOne L (fsuV1 T V)) = 3

  cardL : Nat.card L = 168 * Nat.card (pCoreOf 2 L)

theorem Orders_F4.mk'_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (h37 : A37ForSQTK)
    (h39 : A39ForSQTK) (h1434 : Lemma1434One_F4) (C : XCtx_F4 G T L V V₂ X g)
    (hiso : Nonempty (OTwoQuot (lOne L (fsuV1 T V) ⊔ X ⊔ T) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))) : C.Orders_F4 := by
  obtain ⟨_, S'⟩ := L14332.exists_setting_F4 h1332 h1334 C.h1222 C.hyp C.plane
  obtain ⟨e⟩ := hiso
  exact ⟨quasithinO2QuotientIso_LT_F4 h1332 h1334 C.h1222 C.hyp C.plane,
    quasithinO2QuotientIso_of_perm3 e, C.quasithinO2QuotientIso_H3_F4 h37 h39 h1434,
    by rw [lOne_eq_L₁Of]; exact S'.Lp3_F4, S'.card_L_F4⟩

variable {C : XCtx_F4 G T L V V₂ X g} (O : C.Orders_F4)
include O

theorem Orders_F4.card_H2_F4 : ∃ b : ℕ, Nat.card ↥(lOne L (fsuV1 T V) ⊔ X ⊔ T) = 36 * 2 ^ b := by
  obtain ⟨b, hb⟩ := exists_card_eq_of_iso O.hD2a
  exact ⟨b, by rw [hb, card_SL22]⟩

theorem Orders_F4.card_H3_F4 : ∃ c : ℕ, Nat.card ↥(lOne L V₂ ⊔ X ⊔ T) = 168 * 2 ^ c := by
  obtain ⟨c, hc⟩ := exists_card_eq_of_iso O.hD2b
  exact ⟨c, by rw [hc, SL3.card_S]⟩

theorem Orders_F4.not_L1_le_H3_F4 : ¬ lOne L (fsuV1 T V) ≤ lOne L V₂ ⊔ X ⊔ T := by
  intro hle
  have h23 : lOne L (fsuV1 T V) ⊔ X ⊔ T ≤ lOne L V₂ ⊔ X ⊔ T :=
    sup_le (sup_le hle CFSG.Quasithin.H13.L14413.XCtx.X_le_H3) CFSG.Quasithin.H13.L14413.XCtx.T_le_H3
  obtain ⟨b, hb⟩ := O.card_H2_F4
  obtain ⟨c, hc⟩ := O.card_H3_F4
  have hdvd := Subgroup.card_dvd_of_le h23
  rw [hb, hc] at hdvd
  exact not_nine_dvd c ((Dvd.dvd.mul_right (by norm_num : (9 : ℕ) ∣ 36) _).trans hdvd)

theorem Orders_F4.not_L2_le_H2_F4 : ¬ lOne L V₂ ≤ lOne L (fsuV1 T V) ⊔ X ⊔ T := by
  intro hle
  have h32 : lOne L V₂ ⊔ X ⊔ T ≤ lOne L (fsuV1 T V) ⊔ X ⊔ T :=
    sup_le (sup_le hle (le_sup_right.trans le_sup_left)) le_sup_right
  obtain ⟨b, hb⟩ := O.card_H2_F4
  obtain ⟨c, hc⟩ := O.card_H3_F4
  have hdvd := Subgroup.card_dvd_of_le h32
  rw [hb, hc] at hdvd
  exact not_seven_dvd b ((Dvd.dvd.mul_right (by norm_num : (7 : ℕ) ∣ 168) _).trans hdvd)

theorem Orders_F4.not_L_le_H2_F4 : ¬ L ≤ lOne L (fsuV1 T V) ⊔ X ⊔ T := by
  intro hle
  obtain ⟨b, hb⟩ := O.card_H2_F4
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [hb, O.cardL] at hdvd
  exact not_seven_dvd b ((Dvd.dvd.mul_right (by norm_num : (7 : ℕ) ∣ 168) _).trans hdvd)

theorem Orders_F4.not_X_le_LT_F4 : ¬ X ≤ L ⊔ T := by
  intro hXLT
  have hXL1 : X ≤ lOne L (fsuV1 T V) := by
    rw [← C.Y.2.2.1]
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨hxX, hodd⟩
    obtain ⟨k, hk⟩ := L128P.exists_two_pow_mem_of_le_sup C.hyp.fsu.sylow.1
      C.s1282.hyp.hyp.normalizes hXLT hxX
    exact Subgroup.subset_closure ⟨⟨L128P.mem_of_odd_of_two_pow_mem hodd hk, C.Y.1 hxX⟩, hodd⟩
  have heq : lOne L (fsuV1 T V) ⊔ X ⊔ T = T ⊔ lOne L (fsuV1 T V) := by
    rw [sup_comm T]
    exact le_antisymm (sup_le (sup_le le_sup_left (hXL1.trans le_sup_left)) le_sup_right)
      (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
  obtain ⟨b, hb⟩ := O.card_H2_F4
  obtain ⟨m, hm⟩ := card_of_relIndex_three O.L1_3
  obtain ⟨t, ht⟩ := C.hyp.fsu.sylow.1.exists_card_eq
  have hsup := L32NSet14.card_sup_mul_card_inf C.T_le_normalizer_L1_F4
  rw [ht, hm, ← heq, hb] at hsup
  have h9 : 9 ∣ 3 * 2 ^ (t + m) := by
    refine (Dvd.dvd.mul_right (by norm_num : (9 : ℕ) ∣ 36) (2 ^ b)).trans ⟨Nat.card
      ↥(T ⊓ lOne L (fsuV1 T V)), ?_⟩
    rw [hsup, pow_add]
    ring
  exact not_nine_dvd' _ h9

theorem Orders_F4.inf_eq_T_F4 :
    (L ⊔ T) ⊓ (lOne L (fsuV1 T V) ⊔ X ⊔ T) ⊓ (lOne L V₂ ⊔ X ⊔ T) = T := by
  obtain ⟨P₀, X₁, X₂, hP, hP', hcls, h₁, h₂, h₁₂, h₂₁⟩ := modelData_SL3.exists_data
  obtain ⟨A₁, A₂, -, -, -, -, hA₁₂, hA₂₁, hA₁, hA₂, hclsX⟩ :=
    overgroups_transport O.hD2b C.sylow_H3_F4 hP hP' hcls h₁ h₂ h₁₂ h₂₁
  have hL2 : lOne L V₂ ≤ lOne L V₂ ⊔ X ⊔ T := le_sup_left.trans le_sup_left
  have hY₁ : (L ⊔ T) ⊓ (lOne L V₂ ⊔ X ⊔ T) = A₁ ∨ (L ⊔ T) ⊓ (lOne L V₂ ⊔ X ⊔ T) = A₂ := by
    rcases hclsX ((L ⊔ T) ⊓ (lOne L V₂ ⊔ X ⊔ T)) (le_inf le_sup_right CFSG.Quasithin.H13.L14413.XCtx.T_le_H3) inf_le_right
      with h | h | h | h
    · exact absurd ((le_inf (CFSG.Quasithin.H13.L14413.XCtx.L2_le_L.trans le_sup_left) hL2).trans h.le) C.not_L2_le_T_F4
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd ((CFSG.Quasithin.H13.L14413.XCtx.X_le_H3.trans h.ge).trans inf_le_left) O.not_X_le_LT_F4
  have hY₂ : (lOne L (fsuV1 T V) ⊔ X ⊔ T) ⊓ (lOne L V₂ ⊔ X ⊔ T) = A₁ ∨
      (lOne L (fsuV1 T V) ⊔ X ⊔ T) ⊓ (lOne L V₂ ⊔ X ⊔ T) = A₂ := by
    rcases hclsX ((lOne L (fsuV1 T V) ⊔ X ⊔ T) ⊓ (lOne L V₂ ⊔ X ⊔ T))
      (le_inf le_sup_right CFSG.Quasithin.H13.L14413.XCtx.T_le_H3) inf_le_right with h | h | h | h
    · exact absurd ((le_inf (le_sup_right.trans le_sup_left) CFSG.Quasithin.H13.L14413.XCtx.X_le_H3).trans h.le)
        (not_le_of_relIndex_three C.Y.2.2.2.1 C.hyp.fsu.sylow.1)
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd ((hL2.trans h.ge).trans inf_le_left) O.not_L2_le_H2_F4
  have hne : (L ⊔ T) ⊓ (lOne L V₂ ⊔ X ⊔ T) ≠ (lOne L (fsuV1 T V) ⊔ X ⊔ T) ⊓
      (lOne L V₂ ⊔ X ⊔ T) := fun h =>
    O.not_X_le_LT_F4 ((le_inf (le_sup_right.trans le_sup_left) CFSG.Quasithin.H13.L14413.XCtx.X_le_H3 |>.trans h.ge).trans
      inf_le_left)
  rw [inf_inf_distrib_right]
  exact inf_eq_of_cls hclsX hA₁₂ hA₂₁ hA₁ hA₂ hY₁ hY₂ hne (le_inf le_sup_right CFSG.Quasithin.H13.L14413.XCtx.T_le_H3)
    (le_inf le_sup_right CFSG.Quasithin.H13.L14413.XCtx.T_le_H3) inf_le_right

omit O in

theorem Orders_F4.d4_F4 (h1332 : Stmt13_3_2_F4) (O : C.Orders_F4) (N : Subgroup G)
    (hN : N ≤ (L ⊔ T) ⊓ (lOne L (fsuV1 T V) ⊔ X ⊔ T) ⊓ (lOne L V₂ ⊔ X ⊔ T))
    (hG₀ : L ⊔ T ⊔ (lOne L (fsuV1 T V) ⊔ X ⊔ T) ⊔ (lOne L V₂ ⊔ X ⊔ T) ≤
      Subgroup.normalizer (N : Set G)) : N = ⊥ := by
  by_contra hne
  rw [O.inf_eq_T_F4] at hN
  obtain ⟨M, hM, hle⟩ := exists_maxTwoLocal_ge
    (⟨N, hne, C.hyp.fsu.sylow.1.to_le hN, rfl⟩ : IsTwoLocal (Subgroup.normalizer (N : Set G)))
  have hL13 := h1332 G T L C.hyp.hyp.h13 L C.hyp.hyp.h13.faithful
  have hMeq := hL13.2.1.2.2.2 M hM ((le_sup_left.trans le_sup_left).trans (hG₀.trans hle))
  have hH3L : lOne L V₂ ⊔ X ⊔ T ≤ Subgroup.normalizer (L : Set G) :=
    (le_sup_right.trans hG₀).trans (hle.trans hMeq.le)
  obtain ⟨ψ, hψs, hψk⟩ := O.hD2b
  have hS : IsSimpleGroup SL3.S := Vol2Native.A312L.Seven.slThree_isSimple
  have hn : (L.subgroupOf (lOne L V₂ ⊔ X ⊔ T)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hH3L
  have : ((L.subgroupOf (lOne L V₂ ⊔ X ⊔ T)).map ψ).Normal := hn.map ψ hψs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((L.subgroupOf (lOne L V₂ ⊔ X ⊔ T)).map ψ)
    with h | h
  · apply C.not_L2_le_T_F4
    intro y hy
    have hyH : y ∈ lOne L V₂ ⊔ X ⊔ T :=
      (le_sup_left.trans le_sup_left : lOne L V₂ ≤ lOne L V₂ ⊔ X ⊔ T) hy
    have hyL : y ∈ L := CFSG.Quasithin.H13.L14413.XCtx.L2_le_L hy
    have h1 : ψ ⟨y, hyH⟩ = 1 := by
      have : ψ ⟨y, hyH⟩ ∈ (L.subgroupOf (lOne L V₂ ⊔ X ⊔ T)).map ψ :=
        ⟨⟨y, hyH⟩, hyL, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact this
    have hker : (⟨y, hyH⟩ : ↥(lOne L V₂ ⊔ X ⊔ T)) ∈ CFSG.Open.pCore 2 ↥(lOne L V₂ ⊔ X ⊔ T) := by
      rw [← hψk]; exact h1
    exact C.pCore_H3_le_T_F4 hker
  · apply O.not_X_le_LT_F4
    intro x hx
    have hxH : x ∈ lOne L V₂ ⊔ X ⊔ T := CFSG.Quasithin.H13.L14413.XCtx.X_le_H3 hx
    have hx' : ψ ⟨x, hxH⟩ ∈ (L.subgroupOf (lOne L V₂ ⊔ X ⊔ T)).map ψ := h ▸ Subgroup.mem_top _
    obtain ⟨⟨l, hlH⟩, hlL, hlx⟩ := hx'
    have hker : (⟨l, hlH⟩ : ↥(lOne L V₂ ⊔ X ⊔ T))⁻¹ * ⟨x, hxH⟩ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hlx, inv_mul_cancel]
    rw [hψk] at hker
    have htT : l⁻¹ * x ∈ T := C.pCore_H3_le_T_F4 hker
    rw [show x = l * (l⁻¹ * x) by group]
    exact mul_mem (Subgroup.mem_sup_left hlL) (Subgroup.mem_sup_right htT)

omit O in

theorem Orders_F4.isDSystemIn_F4 (h1332 : Stmt13_3_2_F4) (O : C.Orders_F4) :
    IsDSystemIn .A3 ![L ⊔ T, lOne L (fsuV1 T V) ⊔ X ⊔ T, lOne L V₂ ⊔ X ⊔ T] := by
  have hT' : (L ⊔ T) ⊓ (lOne L (fsuV1 T V) ⊔ X ⊔ T) ⊓ (lOne L V₂ ⊔ X ⊔ T) = T := O.inf_eq_T_F4
  have hL1 : lOne L (fsuV1 T V) ≤ lOne L (fsuV1 T V) ⊔ X ⊔ T := le_sup_left.trans le_sup_left
  have hL2 : lOne L V₂ ≤ lOne L V₂ ⊔ X ⊔ T := le_sup_left.trans le_sup_left
  have hX2 : X ≤ lOne L (fsuV1 T V) ⊔ X ⊔ T := le_sup_right.trans le_sup_left
  have hL1T : ¬ lOne L (fsuV1 T V) ≤ T := not_le_of_relIndex_three O.L1_3 C.hyp.fsu.sylow.1
  have hXT : ¬ X ≤ T := not_le_of_relIndex_three C.Y.2.2.2.1 C.hyp.fsu.sylow.1
  have hne : ∀ {A Y : Subgroup G}, Y ≤ A → ¬ Y ≤ T → A ≠ T := fun hYA hYT hA =>
    hYT (hYA.trans hA.le)
  refine isDSystemIn_A3_of _ O.hD1 O.hD2a O.hD2b ?_ ?_ ?_ ?_ (O.d4_F4 h1332)
  · intro i
    change IsSylowTwoOf ((L ⊔ T) ⊓ (lOne L (fsuV1 T V) ⊔ X ⊔ T) ⊓ (lOne L V₂ ⊔ X ⊔ T)) _
    rw [hT']
    fin_cases i
    · exact isSylowTwoOf_of_quasithinIsSylowTwo C.hyp.fsu.sylow le_sup_right
    · exact isSylowTwoOf_of_quasithinIsSylowTwo C.hyp.fsu.sylow le_sup_right
    · exact isSylowTwoOf_of_quasithinIsSylowTwo C.hyp.fsu.sylow le_sup_right
  · intro i j hij
    change _ ≠ (L ⊔ T) ⊓ (lOne L (fsuV1 T V) ⊔ X ⊔ T) ⊓ (lOne L V₂ ⊔ X ⊔ T)
    rw [hT']
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hne (le_inf (CFSG.Quasithin.H13.L14413.XCtx.L1_le_L.trans le_sup_left) hL1) hL1T
    · exact hne (le_inf (CFSG.Quasithin.H13.L14413.XCtx.L2_le_L.trans le_sup_left) hL2) C.not_L2_le_T_F4
    · exact hne (le_inf hL1 (CFSG.Quasithin.H13.L14413.XCtx.L1_le_L.trans le_sup_left)) hL1T
    · exact absurd rfl hij
    · exact hne (le_inf hX2 CFSG.Quasithin.H13.L14413.XCtx.X_le_H3) hXT
    · exact hne (le_inf hL2 (CFSG.Quasithin.H13.L14413.XCtx.L2_le_L.trans le_sup_left)) C.not_L2_le_T_F4
    · exact hne (le_inf CFSG.Quasithin.H13.L14413.XCtx.X_le_H3 hX2) hXT
    · exact absurd rfl hij
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact fun h => O.not_L_le_H2_F4 (le_sup_left.trans (inf_eq_left.mp h))
    · exact fun h => O.not_L1_le_H3_F4 ((CFSG.Quasithin.H13.L14413.XCtx.L1_le_L.trans le_sup_left).trans (inf_eq_left.mp h))
    · exact fun h => O.not_X_le_LT_F4 (hX2.trans (inf_eq_left.mp h))
    · exact absurd rfl hij
    · exact fun h => O.not_L1_le_H3_F4 (hL1.trans (inf_eq_left.mp h))
    · exact fun h => O.not_X_le_LT_F4 (CFSG.Quasithin.H13.L14413.XCtx.X_le_H3.trans (inf_eq_left.mp h))
    · exact fun h => O.not_L2_le_H2_F4 (hL2.trans (inf_eq_left.mp h))
    · exact absurd rfl hij
  · intro i j k hij hik hjk
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      first
      | exact absurd rfl hij
      | exact absurd rfl hik
      | exact absurd rfl hjk
      | skip
    · exact fun h => O.not_L1_le_H3_F4 ((le_inf (CFSG.Quasithin.H13.L14413.XCtx.L1_le_L.trans le_sup_left) hL1 |>.trans
        h.le).trans inf_le_right)
    · exact fun h => O.not_L1_le_H3_F4 ((le_inf (CFSG.Quasithin.H13.L14413.XCtx.L1_le_L.trans le_sup_left) hL1 |>.trans
        h.ge).trans inf_le_right)
    · exact fun h => O.not_L1_le_H3_F4 ((le_inf hL1 (CFSG.Quasithin.H13.L14413.XCtx.L1_le_L.trans le_sup_left) |>.trans
        h.le).trans inf_le_right)
    · exact fun h => O.not_L1_le_H3_F4 ((le_inf hL1 (CFSG.Quasithin.H13.L14413.XCtx.L1_le_L.trans le_sup_left) |>.trans
        h.ge).trans inf_le_right)
    · exact fun h => O.not_X_le_LT_F4 ((le_inf CFSG.Quasithin.H13.L14413.XCtx.X_le_H3 hX2 |>.trans h.ge).trans inf_le_right)
    · exact fun h => O.not_X_le_LT_F4 ((le_inf CFSG.Quasithin.H13.L14413.XCtx.X_le_H3 hX2 |>.trans h.le).trans inf_le_right)

end XCtx_F4

theorem lemma14413Big_of_Y_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (h1222 : Stmt12_2_2_F4)
    (h12213 : Stmt12_2_13_F4) (h12811 : Lemma12_8_11_F4) (h37 : A37ForSQTK) (h39 : A39ForSQTK)
    (h1434 : Lemma1434One_F4) {T L V : Subgroup G} (h : Hyp14310One G T L V)
    (hext : CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V)) {V₂ : Subgroup G} {g : G}
    (hV₂ : IsL32NPlane T V V₂) (hgP : g ∈ p128 T L V) (hgH : g ∉ l32nH T V) {X : Subgroup G}
    (hX : IsY1442 T V V₂ g X)
    (hiso : Nonempty (OTwoQuot (lOne L (fsuV1 T V) ⊔ X ⊔ T) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))) :
    Nonempty (↥(L ⊔ T ⊔ (lOne L (fsuV1 T V) ⊔ X ⊔ T) ⊔ (lOne L V₂ ⊔ X ⊔ T)) ≃*
      Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) := by
  have C := XCtx_F4.mk'_F4 h1332 h1334 h1222 h12213 h12811 h hext hV₂ hgP hgH hX
  have O := XCtx_F4.Orders_F4.mk'_F4 h1332 h1334 h37 h39 h1434 C hiso
  have h3 := nonempty_mulEquiv_SL_of_isDSystemIn (O.isDSystemIn_F4 h1332)
  have hEq : (![L ⊔ T, lOne L (fsuV1 T V) ⊔ X ⊔ T, lOne L V₂ ⊔ X ⊔ T] : Fin 3 → Subgroup G) 0 ⊔
      (![L ⊔ T, lOne L (fsuV1 T V) ⊔ X ⊔ T, lOne L V₂ ⊔ X ⊔ T] : Fin 3 → Subgroup G) 1 ⊔
      (![L ⊔ T, lOne L (fsuV1 T V) ⊔ X ⊔ T, lOne L V₂ ⊔ X ⊔ T] : Fin 3 → Subgroup G) 2 =
      L ⊔ T ⊔ (lOne L (fsuV1 T V) ⊔ X ⊔ T) ⊔ (lOne L V₂ ⊔ X ⊔ T) := rfl
  rwa [hEq] at h3

theorem lemma14413Big_of_claim_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4) (h12811 : Lemma12_8_11_F4) (h37 : A37ForSQTK)
    (h39 : A39ForSQTK) (h1434 : Lemma1434One_F4)
    (hY : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp14310One G T L V →
      CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V) → Nat.card ↥(fsuU T V) ≠ 2 ^ 5 →
      ∀ (V₂ : Subgroup G) (g : G), IsL32NPlane T V V₂ → g ∈ p128 T L V → g ∉ l32nH T V →
        Y1444Claim T L V V₂ g) : Lemma14413Big_F4 := by
  intro G _ _ T L V h hext hne V₂ g hV₂ hgP hgH
  obtain ⟨X, hX, hXL, hiso⟩ := hY G T L V h hext hne V₂ g hV₂ hgP hgH
  exact ⟨X, hXL, hX.1, hX.2.1, hX.2.2.1, hX.2.2.2.1, hX.2.2.2.2.1, hX.2.2.2.2.2,
    lemma14413Big_of_Y_F4 h1332 h1334 h1222 h12213 h12811 h37 h39 h1434 h hext hV₂ hgP hgH hX
      hiso⟩

end CFSG.Quasithin.H13.L14413
