module

public import CFSG.Quasithin.H13.A6S1372L76B
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1354
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372SixteenTilde

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative commutatorElement

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem pRank_three_centralizer_V2_F4 (h13314 : Stmt13_3_14_F4) (h13315 : Stmt13_3_15_F4) :
    CFSG.Open.pRank 3 (Subgroup.centralizer (S.V2 : Set G)) ≤ 1 := by
  have h : CFSG.pRank 3 ↥(Subgroup.centralizer (S.V2 : Set G)) ≤ 1 := by
    by_cases hhat : IsHatA6 L
    · exact (S.lemma13_5_4_F4 h13314 h13315 (oTwoRes ⁅L₁Of L S.V2, T ⊓ L⁆) (fun _ => rfl)
        (fun h => absurd hhat h)).2.2.2.2.2.1
    · exact (S.lemma13_5_4_F4 h13314 h13315 (L₁Of L S.V2) (fun h => absurd h hhat)
        (fun _ => rfl)).2.2.2.2.2.1
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
  exact h

variable {S}

section Tilde

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
  {H : Subgroup G} (hH : H ∈ S.Hz) [IsMulCommutative ↥(conjClosure S.V3 H)]
include hNS h13315 h1356two hH

theorem not_e9_tilde_fix_V2_F4 (h13314 : Stmt13_3_14_F4)
    {K : Subgroup G} (hKH : K ≤ H) {v₂ : G} (hv₂ : v₂ ∈ S.V2) (hv₂1 : v₂ ∉ fsuV1 T V)
    {α β' : MulAut (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))}
    (hα : α ∈ autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
    (hβ : β' ∈ autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
    (hE : A6L76B.E9Pair α β')
    (hαv : α (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))
        ⟨v₂, le_conjClosure _ _ (S.V2_le_V3 hv₂)⟩) =
      InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))
        ⟨v₂, le_conjClosure _ _ (S.V2_le_V3 hv₂)⟩)
    (hβv : β' (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))
        ⟨v₂, le_conjClosure _ _ (S.V2_le_V3 hv₂)⟩) =
      InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))
        ⟨v₂, le_conjClosure _ _ (S.V2_le_V3 hv₂)⟩) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hHU := le_normalizer_conjClosure S.V3 H
  have hHV := S.le_normalizer_UV1 hH
  set x₂ := InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))
    ⟨v₂, le_conjClosure _ _ (S.V2_le_V3 hv₂)⟩ with hx₂
  set φ := A6Mod.secAct hHU hHV with hφ

  have hker : ¬ 3 ∣ Nat.card φ.ker := by
    rw [hφ, ker_secAct_tilde_F4 hNS h13315 h1356two hH]
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := ↥H)).exists_card_eq
    rw [hk]
    intro h
    have := (Nat.prime_three.dvd_of_dvd_pow h)
    omega

  set X : Subgroup ↥H := K.subgroupOf H ⊓
    (MulAction.stabilizer (MulAut (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) x₂).comap φ with hX
  have hmem : ∀ ψ ∈ autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)), ψ x₂ = x₂ → ψ ∈ X.map φ := by
    intro ψ hψ hψx
    obtain ⟨f, hfK, rfl⟩ := (A6Mod.mem_autSec_iff hHU hHV hKH).1 hψ
    exact ⟨f, ⟨hfK, hψx⟩, rfl⟩
  have h2 : 2 ≤ CFSG.Open.pRank 3 (X.map φ) :=
    A6L76B.two_le_pRank_of_e9 (hmem α hα hαv) (hmem β' hβ hβv) hE
  have h3 := A6L76B.pRank_map_le φ hker X
  have h4 := CFSG.SectionRank.pRank_le_map (p := 3) (by norm_num) H.subtype H.subtype_injective X

  have h5 : CFSG.Open.pRank 3 (X.map H.subtype) ≤ 1 := by
    refine CFSG.SectionRank.pRank_le (by norm_num) fun E hEX hE => ?_
    have hEC : E ≤ Subgroup.centralizer (S.V2 : Set G) := by
      intro e he
      obtain ⟨h, ⟨hhK, hhx⟩, rfl⟩ := hEX he
      have he3 : (h : G) ^ 3 = 1 := hE.2 _ he
      have hc : (h : G) * v₂ * (h : G)⁻¹ * v₂⁻¹ ∈ fsuV1 T V := by
        have h1 : φ h x₂ = x₂ := hhx
        rw [hφ, hx₂, A6Mod.secAct_secMk, ← mul_inv_eq_one, ← map_inv, ← map_mul,
          A6Mod.secMk_eq_one_iff] at h1
        simpa [Setup.rho_apply_coe] using h1
      have hv := S.conj_eq_of_cube hH h.2 he3 hc
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rcases S.mem_V1_or_of_mem_V2 hv₂ hv₂1 hw with hw1 | hw1
      · have := S.conj_V1_of_mem hH h.2 hw1
        calc w * (h : G) = (h : G) * w * (h : G)⁻¹ * h := by rw [this]
          _ = h * w := by group
      · have h6 := S.conj_V1_of_mem hH h.2 hw1
        have e : (h : G) * w * (h : G)⁻¹ =
            ((h : G) * (w * v₂⁻¹) * (h : G)⁻¹) * ((h : G) * v₂ * (h : G)⁻¹) := by group
        have h7 : (h : G) * w * (h : G)⁻¹ = w := by
          rw [e, h6, hv]
          group
        calc w * (h : G) = (h : G) * w * (h : G)⁻¹ * h := by rw [h7]
          _ = h * w := by group
    have hEp : IsPGroup 3 ↥E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 _ g.2)⟩
    obtain ⟨k, hk⟩ := hEp.exists_card_eq
    have hk1 : k ≤ 1 :=
      (CFSG.SectionRank.le_pRank (by norm_num) hEC hE hk).trans
        (S.pRank_three_centralizer_V2_F4 h13314 h13315)
    rw [hk]
    exact Nat.pow_le_pow_right (by norm_num) hk1
  omega

theorem not_e9_model_fix_V2_F4 (h13314 : Stmt13_3_14_F4)
    (hab : IsElemAbelian 2 (conjClosure S.V3 H)) {K : Subgroup G} (hKH : K ≤ H) {D : FFModel}
    {π : D.Gam →* ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))}
    {β : ↥(commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) →* ↥D.sec ⧸ D.ker.subgroupOf D.sec}
    (hR : CFSG.Quasithin.H.Mathieu.RealizesBy D
      (autSec (autOn K (conjClosure S.V3 H)) ⊤ ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
      (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
      (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
        commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) π β)
    (hπ : Function.Injective π) {v₂ : G} (hv₂ : v₂ ∈ S.V2) (hv₂1 : v₂ ∉ fsuV1 T V)
    (hx : InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))
        ⟨v₂, le_conjClosure _ _ (S.V2_le_V3 hv₂)⟩ ∈
      commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
    {m : D.Amb} (hm : m ∈ D.sec) (hxm : β ⟨_, hx⟩ = QuotientGroup.mk ⟨m, hm⟩) {a b : D.Gam}
    (hE : A6L76B.E9Pair a b) (ha : D.act a m * m⁻¹ ∈ D.ker) (hb : D.act b m * m⁻¹ ∈ D.ker) :
    False := by
  have hV := sec_mul_self (S := S) (H := H) hab
  have hfa := A6L76B.fix_of_realizesBy hV hR inf_le_left hE.2.1 hm hxm ha
  have hfb := A6L76B.fix_of_realizesBy hV hR inf_le_left hE.2.2.1 hm hxm hb
  have hE' := hE.map ((autSec (autOn K (conjClosure S.V3 H)) ⊤
    ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))).subtype.comp π)
    (Subtype.val_injective.comp hπ)
  exact not_e9_tilde_fix_V2_F4 hNS h13315 h1356two hH h13314 hKH hv₂ hv₂1 (π a).2 (π b).2 hE'
    hfa hfb

end Tilde

end Setting4

end CFSG.Quasithin.H13.A6
