module

public import CFSG.GH74.GLS.C3.Layer1.Th2P61A7
public import CFSG.GH74.GLS.C3.Layer1.Th2P61L2
public import CFSG.GH74.GLS.C3.Layer1.Th2ConnRows
public import CFSG.GH74.GLS.C3.Layer1.St1PumpCalc

public section

namespace CFSG.GH74.GLS.Th2.Obs

open Equiv Equiv.Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK
  CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.Bal CFSG.ClassicalInvolution.Balance
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure Obstr52Two (B : Subgroup G) (b : G) (J D : Subgroup G) : Prop where
  D_le : D ≤ B
  D_el : CFSG.IsElementaryAbelian 2 ↥D
  D_rank : 2 ≤ pRank 2 ↥D
  D_norm : ∀ d ∈ D, d ∈ normalizer (J : Set G)
  D_faith : ∀ d ∈ D, d ≠ 1 → d ∉ centralizerSection J (pPrimeCoreOf 2 J)
  D_inndiag : ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ e : kBar J ≃* L2 F, ∀ (d : G)
    (hd : d ∈ D), barAct J ⟨d, D_norm d hd⟩ ∈ innDiagSub e
  D_root : ∀ e : kBar J ≃* alternatingGroup (Fin 7),
    IsRootFour ((D.subgroupOf (normalizer (J : Set G))).map (a7Act J e))
  X_norm : ∀ x ∈ ⁅AG D ⊓ centralizer ({b} : Set G), B⁆, x ∈ normalizer (J : Set G)
  X_move : ∃ x ∈ ⁅AG D ⊓ centralizer ({b} : Set G), B⁆, x ∉ centralizerSection J (pPrimeCoreOf 2 J)
  B_inv : (∀ g ∈ B, g ∈ normalizer (J : Set G)) →
    Nonempty (kBar J ≃* alternatingGroup (Fin 7)) ∧
      ∀ e : kBar J ≃* alternatingGroup (Fin 7), ∃ t : Perm (Fin 7), t.IsSwap ∧
        (∀ i, (∃ f ∈ (D.subgroupOf (normalizer (J : Set G))).map (a7Act J e), f i ≠ i) → t i = i) ∧
        (B.subgroupOf (normalizer (J : Set G))).map (a7Act J e) =
          (D.subgroupOf (normalizer (J : Set G))).map (a7Act J e) ⊔ Subgroup.zpowers t

structure Obstr52 (B : Subgroup G) (b : G) (J : Subgroup G) : Prop where
  mem : b ∈ B
  ne_one : b ≠ 1
  comp : IsPCompIn 2 (centralizer ({b} : Set G)) J
  u20 : Nonempty (kBar J ≃* alternatingGroup (Fin 7)) ∨
    HasL2Model (kBar J) (fun q => Odd q ∧ ¬ IsFM9 q)
  exists_D : ∃ D : Subgroup G, Obstr52Two B b J D

theorem exists_obstr52_at_of_comp_selected
    {B : Subgroup G} (hB : CFSG.IsElementaryAbelian 2 ↥B) {a : G}
    (haB : a ∈ B) (ha1 : a ≠ 1)
    (hcomp_a : ∀ L : Subgroup (CentralizerBar a), IsComponent L →
      ¬ IsLocallyKBalanced 2 (↥L ⧸ Subgroup.center ↥L) →
        Nonempty (↥L ≃* alternatingGroup (Fin 7)) ∨ HasL2Model ↥L (fun q => Odd q ∧ ¬ IsFM9 q))
    (hnot : ¬ WeakBalAt B a) : ∃ J : Subgroup G, Obstr52 B a J := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hBc, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hB
  obtain ⟨J, D, h, L, hL, hLJ, hnb⟩ := exists_obsData_at hB haB ha1 hnot
  have hu : Nonempty (kBar J ≃* alternatingGroup (Fin 7)) ∨
      HasL2Model (kBar J) (fun q => Odd q ∧ ¬ IsFM9 q) := by
    obtain ⟨e0⟩ := C3.Layer1.PumpCalc.kBar_equiv_bar h.comp
    have e : kBar J ≃* ↥L := e0.trans (MulEquiv.subgroupCongr hLJ.symm)
    rcases hcomp_a L hL hnb with ⟨⟨e'⟩⟩ | hL2
    · exact Or.inl ⟨e.trans e'⟩
    · exact Or.inr (TwoThin.hasL2Model_of_mulEquiv e.symm hL2)
  have hDel : CFSG.IsElementaryAbelian 2 ↥D :=
    isElementaryAbelian_two_of_sq D (fun d hd => hBsq d (h.D_le hd))
  refine ⟨J, ⟨h.a_mem, h.a_ne, h.comp, hu, D, ?_⟩⟩
  exact
    { D_le := h.D_le
      D_el := hDel
      D_rank := by
        have h1 := C3.Layer1.Back.card_eq_two_pow_pRank hDel
        have h4 : 2 ^ 2 ≤ 2 ^ pRank 2 ↥D := by rw [← h1]; simpa using h.D_card
        exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h4
      D_norm := h.D_norm
      D_faith := h.D_faith
      D_inndiag := fun F _ _ hF e d hd => obs_innDiag h hB hF e hd
      D_root := fun e => obs_root h hB e
      X_norm := h.X_norm
      X_move := h.X_move
      B_inv := fun hBN => by
        rcases hu with hA | hL2
        · exact ⟨hA, fun e => obs_A7_B h hB hBN e⟩
        · exfalso
          obtain ⟨F, _, _, hF, ⟨e⟩⟩ := C3.Layer1.Thm1.exists_l2_model_of_hasL2Model
            (C3.Layer1.Back.hasL2Model_mono (fun q hq => hq.1) hL2)
          exact obs_L2_not_B h hB hBN hF e }

theorem exists_obstr52_at_of_comp
    {B : Subgroup G} (hB : CFSG.IsElementaryAbelian 2 ↥B) {a : G}
    (haB : a ∈ B) (ha1 : a ≠ 1)
    (hcomp : ∀ a : G, orderOf a = 2 → ∀ L : Subgroup (CentralizerBar a), IsComponent L →
      ¬ IsLocallyKBalanced 2 (↥L ⧸ Subgroup.center ↥L) →
        Nonempty (↥L ≃* alternatingGroup (Fin 7)) ∨ HasL2Model ↥L (fun q => Odd q ∧ ¬ IsFM9 q))
    (hnot : ¬ WeakBalAt B a) : ∃ J : Subgroup G, Obstr52 B a J := by
  have hBsq := (C3.Layer1.Back.forall_of_isElementaryAbelian hB).2
  have ha2 : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact hBsq a haB) ha1
  exact exists_obstr52_at_of_comp_selected hB haB ha1
    (fun L hL hnb => hcomp a ha2 L hL hnb) hnot

theorem exists_obstr52_of_comp
    {B : Subgroup G} (hB : CFSG.IsElementaryAbelian 2 ↥B)
    (hcomp : ∀ a : G, orderOf a = 2 → ∀ L : Subgroup (CentralizerBar a), IsComponent L →
      ¬ IsLocallyKBalanced 2 (↥L ⧸ Subgroup.center ↥L) →
        Nonempty (↥L ≃* alternatingGroup (Fin 7)) ∨ HasL2Model ↥L (fun q => Odd q ∧ ¬ IsFM9 q))
    (hnot : ¬ IsWeakKBal 2 B) : ∃ (b : G) (J : Subgroup G), Obstr52 B b J := by
  rw [isWeakKBal_two_iff] at hnot
  push Not at hnot
  obtain ⟨a, haB, ha1, hna⟩ := hnot
  obtain ⟨J, h⟩ := exists_obstr52_at_of_comp hB haB ha1 hcomp hna
  exact ⟨a, J, h⟩

omit [Finite G] in
theorem Obstr52.centerlessBar {B : Subgroup G} {b : G} {J : Subgroup G} (h : Obstr52 B b J) :
    CenterlessBar J := by
  rcases h.u20 with hA | hL
  · exact centerlessBar_of_A7 hA
  · exact centerlessBar_of_hasL2Model (fun q hq => hq.1) hL

theorem Obstr52.two_le_pRank {B : Subgroup G} {b : G} {J : Subgroup G} (h : Obstr52 B b J) :
    2 ≤ pRank 2 ↥J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_isSylowOf 2 J
  have hshape : RankTwoShape P := by
    rcases h.u20 with hA | hL
    · exact rankTwoShape_sylow_A7 hP hA
    · exact rankTwoShape_sylow_L2 hP (TwoThin.isQuasisimple_hat h.comp) (fun q hq => hq.1) hL
  obtain ⟨U, hU⟩ := exists_isFourSub_of_rankTwoShape hshape
  have hPJ : P ≤ J := by
    rcases hP with ⟨Q, hQ⟩
    rw [← hQ]
    exact Subgroup.map_subtype_le _
  have hUJ : U ≤ J := hU.1.trans hPJ
  have h1 := C3.Layer1.Back.card_eq_two_pow_pRank hU.2.1
  have h2 : 2 ^ 2 ≤ 2 ^ pRank 2 ↥U := by rw [← h1, hU.2.2]; norm_num
  have h3 : 2 ≤ pRank 2 ↥U := (Nat.pow_le_pow_iff_right (by norm_num)).1 h2
  exact h3.trans (C3.Layer1.Back.pRank_mono' hUJ)

theorem Obstr52.normalizes {B : Subgroup G} {b : G} {J : Subgroup G} (h : Obstr52 B b J)
    (hG4 : pRank 2 G ≤ 4) (hB : CFSG.IsElementaryAbelian 2 ↥B) :
    ∀ g ∈ B, g ∈ normalizer (J : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hB
  have hb2 : orderOf b = 2 := orderOf_eq_prime (by rw [sq]; exact hBsq b h.mem) h.ne_one
  intro g hg
  exact mem_normalizer_of_pRank_le_four hG4 hb2 hB h.mem h.comp h.centerlessBar h.two_le_pRank hg

theorem Obstr52.nonempty_A7_of_rank_four {B : Subgroup G} {b : G} {J : Subgroup G}
    (h : Obstr52 B b J) (hG4 : pRank 2 G ≤ 4) (hB : CFSG.IsElementaryAbelian 2 ↥B) :
    Nonempty (kBar J ≃* alternatingGroup (Fin 7)) := by
  obtain ⟨D, hD⟩ := h.exists_D
  exact (hD.B_inv (h.normalizes hG4 hB)).1

end CFSG.GH74.GLS.Th2.Obs
