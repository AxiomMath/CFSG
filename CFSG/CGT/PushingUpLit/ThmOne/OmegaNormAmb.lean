module

public import CFSG.CGT.PushingUpLit.ThmOne.OmegaNormModel
public import CFSG.CGT.PushingUpLit.ThmOne.AmbKSharp
public import CFSG.CGT.PushingUpLit.ThmOne.Basic
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.CGT.PushingUpLit.ThmOne

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit CFSG.Quasithin
open CFSG.Quasithin.XMod CFSG.CGT.PushingUpLit.CGT6 CFSG.CGT.PushingUpLit.BHS6
open CFSG.Open (IsElemAbelian)
open scoped commutatorElement

namespace OmegaNorm

variable {G : Type} [Group G]

theorem isElemAbelian_of_le_omega {V W : Subgroup G} (hV : IsElemAbelian 2 V) (hWV : W ≤ V) :
    IsElemAbelian 2 W := CFSG.Open.IsElemAbelian.mono hV hWV

theorem mem_normalizer_commutator_omega [Finite G] {H K : Subgroup G} {g : G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  have h1 : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨c, hc, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hH c).mp hc
  have h2 : K.map (MulAut.conj g).toMonoidHom ≤ K := by
    rintro _ ⟨c, hc, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hK c).mp hc
  have := Subgroup.commutator_mono h1 h2
  rw [← Subgroup.map_commutator] at this
  exact this ⟨x, hx, rfl⟩

theorem exists_mulEquiv_isModelAct {D W : Subgroup G} (hDW : D ≤ Subgroup.normalizer (W : Set G))
    {Sg M : Type} [Group Sg] [CommGroup M] {act : Sg → M → M} (hnat : IsNatBy act D W)
    (hWC : W ⊓ Subgroup.centralizer (D : Set G) = ⊥) :
    ∃ ψ : ↥W ≃* M, IsModelAct (autOn D W) ψ act := by
  obtain ⟨φ, ψ, hφs, -, hψs, hψk, hψe⟩ := hnat
  have hψi : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, hψk, hWC, Subgroup.bot_subgroupOf]
  have hact : ∀ (d : ↥D) (w : ↥W), ψ (actOn W D hDW d w) = act (φ d) (ψ w) := by
    intro d w
    have hw : (d : G) * w * (d : G)⁻¹ ∈ W := by
      rw [← actOn_apply_coe hDW d w]
      exact (actOn W D hDW d w).2
    rw [← hψe d w hw]
    exact congrArg ψ (Subtype.ext (actOn_apply_coe hDW d w))
  refine ⟨MulEquiv.ofBijective ψ ⟨hψi, hψs⟩, fun g => ?_, fun s hs => ?_⟩
  · obtain ⟨d, rfl⟩ := hφs g
    exact ⟨actOn W D hDW d, by rw [← range_actOn W D hDW]; exact ⟨d, rfl⟩, fun w => hact d w⟩
  · rw [← range_actOn W D hDW] at hs
    obtain ⟨d, rfl⟩ := hs
    exact ⟨φ d, fun w => hact d w⟩

theorem commutator_commutator_eq_blockU [Finite G] {V Y D : Subgroup G} (hYD : Y ≤ D)
    (hDV : D ≤ Subgroup.normalizer (V : Set G)) (hY : oResidualTwo ↥Y = ⊤)
    (hU : ⁅V, Y⁆ = blockU Y) : ⁅Y, ⁅D, V⁆⁆ = blockU Y := by
  apply le_antisymm
  · rw [← hU, Subgroup.commutator_comm V Y]
    exact Subgroup.commutator_mono le_rfl (commutator_le_of_le_normalizer hDV)
  · have hUW : blockU Y ≤ ⁅D, V⁆ := by
      rw [← hU, Subgroup.commutator_comm V Y]
      exact Subgroup.commutator_mono hYD le_rfl
    calc blockU Y = ⁅blockU Y, Y⁆ := (blockU_commutator_eq_self hY).symm
      _ ≤ ⁅⁅D, V⁆, Y⁆ := Subgroup.commutator_mono hUW le_rfl
      _ = ⁅Y, ⁅D, V⁆⁆ := Subgroup.commutator_comm _ _

theorem blockU_le_of_omega {V Y D : Subgroup G} (hYD : Y ≤ D)
    (hDV : D ≤ Subgroup.normalizer (V : Set G)) (hU : ⁅V, Y⁆ = blockU Y) : blockU Y ≤ V := by
  rw [← hU, Subgroup.commutator_comm]
  exact commutator_le_of_le_normalizer (hYD.trans hDV)

theorem map_commOn_eq_blockU {W Y : Subgroup G} (hW : IsElemAbelian 2 W)
    (hYW : Y ≤ Subgroup.normalizer (W : Set G)) (hWY : ⁅Y, W⁆ = blockU Y) :
    (commOn hW Y).map W.subtype = blockU Y ∧
      (commOn hW Y ⊓ fixOn hW Y).map W.subtype = blockZ Y := by
  have hU : (commOn hW Y).map W.subtype = blockU Y := (map_commOn hW hYW).trans hWY
  refine ⟨hU, ?_⟩
  have hUW : blockU Y ≤ W := by
    rw [← hU]
    exact Subgroup.map_subtype_le _
  rw [Subgroup.map_inf _ _ _ W.subtype_injective, hU, fixOn_eq hW hYW,
    Subgroup.subgroupOf_map_subtype, blockZ]
  ext x
  simp only [Subgroup.mem_inf]
  exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hUW h.1⟩⟩

theorem commOn_irreducible_of_isShortGroup [Finite G] {W Y : Subgroup G} (hW : IsElemAbelian 2 W)
    (hYW : Y ≤ Subgroup.normalizer (W : Set G)) (hY : IsShortGroup ↥Y) (hWY : ⁅Y, W⁆ = blockU Y)
    (J : Subgroup ↥W) (hJ : ∀ y ∈ autOn Y W, ∀ j ∈ J, y j ∈ J)
    (hCJ : commOn hW Y ⊓ fixOn hW Y ≤ J) (hJU : J ≤ commOn hW Y) :
    J = commOn hW Y ⊓ fixOn hW Y ∨ J = commOn hW Y := by
  obtain ⟨hU, hC⟩ := map_commOn_eq_blockU hW hYW hWY
  have hZN : blockZ Y ≤ J.map W.subtype := hC ▸ Subgroup.map_mono hCJ
  have hNU : J.map W.subtype ≤ blockU Y := hU ▸ Subgroup.map_mono hJU
  have hNn : ∀ g ∈ Y, ∀ x ∈ J.map W.subtype, g * x * g⁻¹ ∈ J.map W.subtype := by
    rintro g hg _ ⟨j, hj, rfl⟩
    have hmem : conjAct W ⟨g, hYW hg⟩ ∈ autOn Y W := ⟨⟨g, hYW hg⟩, hg, rfl⟩
    exact ⟨_, hJ _ hmem j hj, BHS.conjAct_apply' W ⟨g, hYW hg⟩ j⟩
  rcases blockU_irred_of_short hY _ hZN hNU hNn with h | h
  · left
    exact Subgroup.map_injective W.subtype_injective (h.trans hC.symm)
  · right
    exact Subgroup.map_injective W.subtype_injective (h.trans hU.symm)

theorem commOn_inf_fixOn_lt_of_isShortGroup [Finite G] {W Y : Subgroup G}
    (hW : IsElemAbelian 2 W) (hYW : Y ≤ Subgroup.normalizer (W : Set G)) (hY : IsShortGroup ↥Y)
    (hWY : ⁅Y, W⁆ = blockU Y) : commOn hW Y ⊓ fixOn hW Y < commOn hW Y := by
  obtain ⟨hU, hC⟩ := map_commOn_eq_blockU hW hYW hWY
  rw [← Subgroup.map_lt_map_iff_of_injective W.subtype_injective, hU, hC]
  exact blockZ_lt_of_short hY

theorem conjAct_normalizes_autOn {D W : Subgroup G} {r : G}
    (hrW : r ∈ Subgroup.normalizer (W : Set G)) (hrD : r ∈ Subgroup.normalizer (D : Set G)) :
    conjAct W ⟨r, hrW⟩ ∈ Subgroup.normalizer (autOn D W : Set (MulAut ↥W)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro s
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨r, hrW⟩ * x * ⟨r, hrW⟩⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    exact (Subgroup.mem_normalizer_iff.mp hrD x).mp hx
  · rintro ⟨x, hx, hxs⟩
    refine ⟨⟨r, hrW⟩⁻¹ * x * ⟨r, hrW⟩, ?_, ?_⟩
    · have h1 := (Subgroup.mem_normalizer_iff.mp (inv_mem hrD) x).mp hx
      rw [inv_inv] at h1
      exact h1
    · rw [map_mul, map_mul, map_inv, hxs]
      group

theorem conjAct_commute_of_commutator_mem {V W Y : Subgroup G} (hV : IsElemAbelian 2 V)
    (hWV : W ≤ V) {r : G} (hrW : r ∈ Subgroup.normalizer (W : Set G))
    (hrc : ∀ y ∈ Y, ⁅r, y⁆ ∈ V) :
    ∀ y ∈ autOn Y W, conjAct W ⟨r, hrW⟩ * y = y * conjAct W ⟨r, hrW⟩ := by
  rintro _ ⟨y, hy, rfl⟩
  refine MulEquiv.ext fun w => Subtype.ext ?_
  simp only [MulAut.mul_apply, BHS.conjAct_apply']
  have hc : ⁅r, (y : G)⁆ ∈ V := hrc y hy
  have hyw : (y : G) * w * (y : G)⁻¹ ∈ W := by
    rw [← BHS.conjAct_apply' W y w]
    exact (conjAct W y w).2
  have hrw : (y : G) * (r * w * r⁻¹) * (y : G)⁻¹ ∈ W := by
    have h1 : r * w * r⁻¹ ∈ W := by
      rw [← BHS.conjAct_apply' W ⟨r, hrW⟩ w]
      exact (conjAct W ⟨r, hrW⟩ w).2
    rw [← BHS.conjAct_apply' W y ⟨_, h1⟩]
    exact (conjAct W y ⟨_, h1⟩).2
  have := hV.1
  have hcomm : ⁅r, (y : G)⁆ * ((y : G) * (r * w * r⁻¹) * (y : G)⁻¹) =
      ((y : G) * (r * w * r⁻¹) * (y : G)⁻¹) * ⁅r, (y : G)⁆ :=
    setLike_mul_comm hc (hWV hrw)
  calc r * ((y : G) * w * (y : G)⁻¹) * r⁻¹ =
      ⁅r, (y : G)⁆ * ((y : G) * (r * w * r⁻¹) * (y : G)⁻¹) * ⁅r, (y : G)⁆⁻¹ := by
        simp only [commutatorElement_def]
        group
    _ = (y : G) * (r * w * r⁻¹) * (y : G)⁻¹ := by rw [hcomm, mul_inv_cancel_right]

theorem omega_setup [Finite G] {V Y D : Subgroup G} (hV : IsElemAbelian 2 V)
    (hDV : D ≤ Subgroup.normalizer (V : Set G)) (hO : OmegaFourOutcomeSharp V Y D) (hYD : Y ≤ D)
    (hY : IsShortGroup ↥Y) (hU : ⁅V, Y⁆ = blockU Y) :
    ∃ (n : ℕ) (hW : IsElemAbelian 2 ⁅D, V⁆), 2 ≤ n ∧ ⁅D, V⁆ ≤ V ∧
      D ≤ Subgroup.normalizer ((⁅D, V⁆ : Subgroup G) : Set G) ∧
      (commOn hW Y).map ⁅D, V⁆.subtype = blockU Y ∧
      @IsIrrSec ↥(autOn D ⁅D, V⁆) _ ↥⁅D, V⁆ (commGroupOfElemAbelian hW) _ ⊥ ⊤ ∧
      autOn Y ⁅D, V⁆ ≤ autOn D ⁅D, V⁆ ∧
      (∀ J : Subgroup ↥⁅D, V⁆, (∀ y ∈ autOn Y ⁅D, V⁆, ∀ j ∈ J, y j ∈ J) →
        commOn hW Y ⊓ fixOn hW Y ≤ J → J ≤ commOn hW Y →
          J = commOn hW Y ⊓ fixOn hW Y ∨ J = commOn hW Y) ∧
      commOn hW Y ⊓ fixOn hW Y < commOn hW Y ∧
      Nat.card ↥⁅D, V⁆ ≤
        Nat.card ↥(@eqvEnd ↥(autOn D ⁅D, V⁆) _ ↥⁅D, V⁆ (commGroupOfElemAbelian hW) _) *
          Nat.card ↥(commOn hW Y) ∧
      Nat.card ↥⁅D, V⁆ = 2 ^ (4 * n) ∧ Nat.card ↥(commOn hW Y) = 2 ^ (3 * n) := by
  obtain ⟨-, -, -, -, n, hn, hnat, hWC, -, -, -, -, -, -, hcardU⟩ := hO
  have hWV : ⁅D, V⁆ ≤ V := commutator_le_of_le_normalizer hDV
  have hW : IsElemAbelian 2 ⁅D, V⁆ := isElemAbelian_of_le_omega hV hWV
  have hDW : D ≤ Subgroup.normalizer ((⁅D, V⁆ : Subgroup G) : Set G) := fun d hd =>
    mem_normalizer_commutator_omega (Subgroup.le_normalizer hd) (hDV hd)
  have hYW := hYD.trans hDW
  have hWY : ⁅Y, ⁅D, V⁆⁆ = blockU Y := commutator_commutator_eq_blockU hYD hDV hY.residual_eq hU
  obtain ⟨hUmap, -⟩ := map_commOn_eq_blockU hW hYW hWY
  have hmod : (∃ ψ : ↥⁅D, V⁆ ≃* Multiplicative (Matrix (Fin 2) (Fin 2) (Fq n)),
        IsModelAct (autOn D ⁅D, V⁆) ψ (omegaPlusAct n)) ∨
      ∃ ψ : ↥⁅D, V⁆ ≃* Multiplicative (hermSub n),
        IsModelAct (autOn D ⁅D, V⁆) ψ (omegaMinusAct n) :=
    hnat.imp (fun h => exists_mulEquiv_isModelAct hDW h hWC)
      (fun h => exists_mulEquiv_isModelAct hDW h hWC)
  obtain ⟨hS, hF, hWc⟩ := @omega_isIrrSec_card ↥⁅D, V⁆ (commGroupOfElemAbelian hW) _
    (autOn D ⁅D, V⁆) n (by omega) hmod
  have h1 : Nat.card ↥(commOn hW Y) = 2 ^ (3 * n) := by
    rw [← Subgroup.card_map_of_injective ⁅D, V⁆.subtype_injective, hUmap, ← hU,
      Subgroup.commutator_comm, hcardU]
  refine ⟨n, hW, hn, hWV, hDW, hUmap, hS, ?_, commOn_irreducible_of_isShortGroup hW hYW hY hWY,
    commOn_inf_fixOn_lt_of_isShortGroup hW hYW hY hWY, ?_, hWc, h1⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hYD hx, rfl⟩
  · rw [hWc, h1, show 4 * n = n + 3 * n by ring, pow_add]
    exact Nat.mul_le_mul_right _ hF

end OmegaNorm

end CFSG.CGT.PushingUpLit.ThmOne
