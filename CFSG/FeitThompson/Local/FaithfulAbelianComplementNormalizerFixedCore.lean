module

public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Local.SmallRankLineInMaximalPlane
public import CFSG.FeitThompson.Definitions.TISubsetWithItsExactNormalizer
import CFSG.FeitThompson.Representations.TISetDadeData
import CFSG.FeitThompson.Local.InvariantCyclicComplementPrimeLine
import CFSG.FeitThompson.Local.ComplementFixedFreeSpecialization
import CFSG.FeitThompson.Local.CoprimeSolvableCommutatorDecomposition
import CFSG.FeitThompson.OddOrder.SemidirectReassociation
import CFSG.FeitThompson.Local.ControlledNormalElementaryPlane

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup Pointwise

variable {G : Type*} [Group G]

structure IsFixedCoreConfig (p : ℕ) (S P U B : Subgroup G) : Prop where
  prime_p : p.Prime
  isElementaryAbelian_P : IsElementaryAbelian p P
  P_ne_bot : P ≠ ⊥
  U_ne_bot : U ≠ ⊥
  isMulCommutative_U : IsMulCommutative ↥U
  B_ne_bot : B ≠ ⊥
  isCyclic_B : IsCyclic ↥B
  coprime_P : (Nat.card P).Coprime (Nat.card U * Nat.card B)
  coprime_U_B : (Nat.card U).Coprime (Nat.card B)
  S_le_normalizer_P : S ≤ Subgroup.normalizer (P : Set G)
  sup_eq_S : P ⊔ (U ⊔ B) = S
  inf_eq_bot : P ⊓ (U ⊔ B) = ⊥
  B_le_normalizer_U : B ≤ Subgroup.normalizer (U : Set G)
  U_inf_B_eq_bot : U ⊓ B = ⊥
  inf_centralizer_singleton_eq_bot : ∀ b ∈ B, b ≠ 1 → U ⊓ Subgroup.centralizer {b} = ⊥
  inf_centralizer_P_eq_bot : U ⊓ Subgroup.centralizer (P : Set G) = ⊥
  inf_centralizer_B_ne_bot : P ⊓ Subgroup.centralizer (B : Set G) ≠ ⊥
  isTIWithNormalizer_P : IsTIWithNormalizer ((P : Set G) \ {1}) S

namespace IsFixedCoreConfig

variable {p : ℕ} {S P U B : Subgroup G} (h : IsFixedCoreConfig p S P U B)

include h

theorem P_le_S : P ≤ S := h.sup_eq_S ▸ le_sup_left

theorem U_le_S : U ≤ S := h.sup_eq_S ▸ (le_sup_left.trans le_sup_right)

theorem B_le_S : B ≤ S := h.sup_eq_S ▸ (le_sup_right.trans le_sup_right)

theorem B_le_normalizer_P : B ≤ Subgroup.normalizer (P : Set G) :=
  h.B_le_S.trans h.S_le_normalizer_P

theorem U_le_normalizer_P : U ≤ Subgroup.normalizer (P : Set G) :=
  h.U_le_S.trans h.S_le_normalizer_P

theorem disjoint_P_B : Disjoint P B :=
  disjoint_iff.2 (le_bot_iff.1 (h.inf_eq_bot ▸ inf_le_inf_left P le_sup_right))

theorem disjoint_U_B : Disjoint U B := disjoint_iff.2 h.U_inf_B_eq_bot

theorem core_le_P : P ⊓ Subgroup.centralizer (B : Set G) ≤ P := inf_le_left

theorem P_le_centralizer_core :
    P ≤ Subgroup.centralizer ((P ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) : Set G) := by
  intro x hx
  refine Subgroup.mem_centralizer_iff.2 fun z hz => ?_
  exact h.isElementaryAbelian_P.mul_comm (Subgroup.mem_inf.1 hz).1 hx

theorem B_le_centralizer_core :
    B ≤ Subgroup.centralizer ((P ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) : Set G) := by
  intro b hb
  refine Subgroup.mem_centralizer_iff.2 fun z hz => ?_
  exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hz).2 b hb).symm

theorem sup_P_B_le_centralizer_core :
    P ⊔ B ≤ Subgroup.centralizer ((P ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) : Set G) :=
  sup_le h.P_le_centralizer_core h.B_le_centralizer_core

theorem normalizer_core_le_S :
    Subgroup.normalizer ((P ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) : Set G) ≤ S := by
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h.inf_centralizer_B_ne_bot
  have hzZ : (z : G) ∈ P ⊓ Subgroup.centralizer (B : Set G) := z.2
  have hz1' : (z : G) ≠ 1 := fun hc => hz1 (Subtype.ext hc)
  intro g hg
  have hconj : g * (z : G) * g⁻¹ ∈ P ⊓ Subgroup.centralizer (B : Set G) :=
    (Subgroup.mem_normalizer_iff.1 hg (z : G)).1 hzZ
  refine h.isTIWithNormalizer_P.mem_of_conj_mem (a := (z : G))
    ⟨(Subgroup.mem_inf.1 hzZ).1, ?_⟩ ⟨(Subgroup.mem_inf.1 hconj).1, ?_⟩
  · simpa using hz1'
  · simp only [Set.mem_singleton_iff]
    intro hc
    exact hz1' (by simpa using hc)

theorem exists_mul_mul_of_mem_S {s : G} (hs : s ∈ S) :
    ∃ x ∈ P, ∃ u ∈ U, ∃ b ∈ B, s = x * u * b := by
  have hUB : (U ⊔ B : Subgroup G) ≤ Subgroup.normalizer (P : Set G) :=
    sup_le h.U_le_normalizer_P h.B_le_normalizer_P
  have hcoeS : ((S : Subgroup G) : Set G) = (P : Set G) * ((U ⊔ B : Subgroup G) : Set G) := by
    rw [← h.sup_eq_S]
    exact Subgroup.coe_mul_of_right_le_normalizer_left P (U ⊔ B) hUB
  have hcoeUB : ((U ⊔ B : Subgroup G) : Set G) = (U : Set G) * (B : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left U B h.B_le_normalizer_U
  obtain ⟨x, hx, y, hy, rfl⟩ := (hcoeS ▸ hs : s ∈ (P : Set G) * ((U ⊔ B : Subgroup G) : Set G))
  obtain ⟨u, hu, b, hb, rfl⟩ := (hcoeUB ▸ hy : y ∈ (U : Set G) * (B : Set G))
  exact ⟨x, hx, u, hu, b, hb, (mul_assoc x u b).symm⟩

theorem normal_subgroupOf_sup_P_B : (P.subgroupOf (P ⊔ B)).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer (sup_le Subgroup.le_normalizer h.B_le_normalizer_P)

theorem coe_sup_P_B : ((P ⊔ B : Subgroup G) : Set G) = (P : Set G) * (B : Set G) :=
  Subgroup.coe_mul_of_right_le_normalizer_left P B h.B_le_normalizer_P

theorem isComplement'_subgroupOf_sup_P_B :
    (P.subgroupOf (P ⊔ B)).IsComplement' (B.subgroupOf (P ⊔ B)) :=
  isComplement'_subgroupOf_sup h.B_le_normalizer_P h.disjoint_P_B

end IsFixedCoreConfig

section Main

variable [Finite G] {p : ℕ} {S P U B : Subgroup G}

namespace IsFixedCoreConfig

variable (h : IsFixedCoreConfig p S P U B)

include h

theorem prime_dvd_natCard_P : p ∣ Nat.card P := by
  have : Fact p.Prime := ⟨h.prime_p⟩
  obtain ⟨n, hn⟩ := h.isElementaryAbelian_P.isPGroup.exists_card_eq
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · exact absurd (Subgroup.card_eq_one.1 (by rw [hn, hn0, pow_zero])) h.P_ne_bot
  · exact hn ▸ dvd_pow_self p hn0.ne'

theorem natCard_sup_U_B : Nat.card ((U ⊔ B : Subgroup G)) = Nat.card U * Nat.card B := by
  have hcompl := isComplement'_subgroupOf_sup h.B_le_normalizer_U h.disjoint_U_B
  have h1 : Nat.card ↥(U.subgroupOf (U ⊔ B)) = Nat.card U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : U ≤ U ⊔ B)).toEquiv
  have h2 : Nat.card ↥(B.subgroupOf (U ⊔ B)) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : B ≤ U ⊔ B)).toEquiv
  rw [← h1, ← h2]
  exact hcompl.card_mul_card.symm

theorem not_dvd_natCard_of_le_sup_U_B {A : Subgroup G} (hA : A ≤ U ⊔ B) : ¬ p ∣ Nat.card A := by
  intro hpA
  have hdvd : p ∣ Nat.card U * Nat.card B :=
    hpA.trans (h.natCard_sup_U_B ▸ Subgroup.card_dvd_of_le hA)
  have hg : p ∣ Nat.gcd (Nat.card P) (Nat.card U * Nat.card B) :=
    Nat.dvd_gcd h.prime_dvd_natCard_P hdvd
  rw [Nat.Coprime.gcd_eq_one h.coprime_P] at hg
  exact h.prime_p.one_lt.ne' (Nat.dvd_one.1 hg)

section Key

variable {D A : Subgroup G}

private theorem exists_invariant_compl (hANP : A ≤ Subgroup.normalizer (P : Set G))
    (hANZ : A ≤ Subgroup.normalizer
      ((P ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) : Set G))
    (hpA : ¬ p ∣ Nat.card A) :
    ∃ Y : Subgroup G, Y ≤ P ∧ A ≤ Subgroup.normalizer (Y : Set G) ∧
      (P ⊓ Subgroup.centralizer (B : Set G)) ⊓ Y = ⊥ ∧
      (P ⊓ Subgroup.centralizer (B : Set G)) ⊔ Y = P := by
  set Z : Subgroup G := P ⊓ Subgroup.centralizer (B : Set G) with hZ
  have hZP : Z ≤ P := inf_le_left
  have hPcomm : IsMulCommutative ↥P := (isElementaryAbelian_iff.1 h.isElementaryAbelian_P).1
  let instC : CommGroup ↥P := IsMulCommutative.instCommGroup
  let β : ↥A →* MulAut ↥P := P.normalizerMonoidHom.comp (Subgroup.inclusion hANP)
  have hβ : ∀ (a : ↥A) (x : ↥P), ((β a x : ↥P) : G) = (a : G) * (x : G) * (a : G)⁻¹ := by
    intro a x; simp [β, Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hexp : ∀ x : ↥P, x ^ p = 1 := fun x =>
    Subtype.ext (by push_cast; exact h.isElementaryAbelian_P.pow_eq_one x.2)
  have hZinv : ∀ b : ↥A, ∀ x ∈ Z.subgroupOf P, β b x ∈ Z.subgroupOf P := by
    intro b x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    rw [hβ]
    exact (Subgroup.mem_normalizer_iff.1 (hANZ b.2) (x : G)).1 hx
  obtain ⟨T, hTinv, hcompl⟩ :=
    exists_invariant_isCompl_of_pow_eq_one h.prime_p hexp β hpA hZinv
  refine ⟨T.map P.subtype, ?_, ?_, ?_, ?_⟩
  · rintro x ⟨t, -, rfl⟩
    exact t.2
  · rw [Subgroup.le_normalizer_iff]
    rintro a ha y ⟨t, ht, rfl⟩
    exact ⟨β ⟨a, ha⟩ t, hTinv ⟨a, ha⟩ t ht, by simpa using hβ ⟨a, ha⟩ t⟩
  · have hmap := congrArg (Subgroup.map P.subtype) hcompl.inf_eq_bot
    rwa [Subgroup.map_inf _ _ _ P.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hZP,
      Subgroup.map_bot] at hmap
  · have hmap := congrArg (Subgroup.map P.subtype) hcompl.sup_eq_top
    rwa [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hZP, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at hmap

private theorem le_centralizer_of_invariant {Y : Subgroup G} (hDU : D ≤ U)
    (hBND : B ≤ Subgroup.normalizer (D : Set G)) (hYP : Y ≤ P)
    (hANY : D ⊔ B ≤ Subgroup.normalizer (Y : Set G))
    (hZY : (P ⊓ Subgroup.centralizer (B : Set G)) ⊓ Y = ⊥) :
    D ≤ Subgroup.centralizer (Y : Set G) := by
  have hUcomm : IsMulCommutative ↥U := h.isMulCommutative_U
  have hPcomm : IsMulCommutative ↥P := (isElementaryAbelian_iff.1 h.isElementaryAbelian_P).1
  set A : Subgroup G := D ⊔ B with hA
  have hDA : D ≤ A := le_sup_left
  have hBA : B ≤ A := le_sup_right
  have hDB : Disjoint D B := h.disjoint_U_B.mono_left hDU
  have hDcomm : IsMulCommutative ↥D := isMulCommutative_of_le (A := U) hDU
  have hYcomm : IsMulCommutative ↥Y := isMulCommutative_of_le (A := P) hYP
  have hYsol : Group.IsSolvable ↥Y := Group.isSolvable_of_comm (isMulCommutative_iff.1 hYcomm)
  have hDsol : Group.IsSolvable ↥D := Group.isSolvable_of_comm (isMulCommutative_iff.1 hDcomm)
  have hBsol : Group.IsSolvable ↥B :=
    Group.isSolvable_of_comm fun a b => h.isCyclic_B.commGroup.mul_comm a b
  have hcompl : (D.subgroupOf A).IsComplement' (B.subgroupOf A) :=
    isComplement'_subgroupOf_sup hBND hDB
  have hNorm : (D.subgroupOf A).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (sup_le Subgroup.le_normalizer hBND)
  have hAsol : Group.IsSolvable ↥A := by
    have h1 : Group.IsSolvable ↥(D.subgroupOf A) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe hDA).toMonoidHom) (MulEquiv.injective _)
    have h2 : Group.IsSolvable ↥(B.subgroupOf A) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe hBA).toMonoidHom) (MulEquiv.injective _)
    have hq : Group.IsSolvable (↥A ⧸ D.subgroupOf A) :=
      Group.isSolvable_of_surjective
        (f := (Subgroup.isComplement'_comm.1 hcompl).QuotientMulEquiv.symm.toMonoidHom)
        (MulEquiv.surjective _)
    exact (Group.isSolvable_iff_subgroup_quotient (D.subgroupOf A)).2 ⟨h1, hq⟩
  have hAUB : A ≤ U ⊔ B := sup_le (hDU.trans le_sup_left) le_sup_right
  have hcardA : Nat.card A ∣ Nat.card U * Nat.card B :=
    h.natCard_sup_U_B ▸ Subgroup.card_dvd_of_le hAUB
  have hcop : (Nat.card A).Coprime (Nat.card Y) :=
    ((h.coprime_P.coprime_dvd_right hcardA).symm).coprime_dvd_right
      (Subgroup.card_dvd_of_le hYP)
  let ρ : ↥A →* MulAut ↥Y := Y.normalizerMonoidHom.comp (Subgroup.inclusion hANY)
  have hρ : ∀ (a : ↥A) (y : ↥Y), ((ρ a y : ↥Y) : G) = (a : G) * (y : G) * (a : G)⁻¹ := by
    intro a y; simp [ρ, Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hC : ∀ w ∈ B.subgroupOf A, w ≠ 1 → D.subgroupOf A ⊓ Subgroup.centralizer {w} = ⊥ := by
    intro w hw hw1
    rw [eq_bot_iff]
    intro x hx
    have hxD : (x : G) ∈ D := Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 hx).1
    have hxc : (w : G) * (x : G) = (x : G) * (w : G) :=
      congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hx).2 w rfl)
    have hmem : (x : G) ∈ U ⊓ Subgroup.centralizer {(w : G)} :=
      Subgroup.mem_inf.2 ⟨hDU hxD, Subgroup.mem_centralizer_iff.2 (by
        intro g hg; rw [Set.mem_singleton_iff] at hg; subst hg; exact hxc)⟩
    rw [h.inf_centralizer_singleton_eq_bot (w : G) (Subgroup.mem_subgroupOf.1 hw)
      (fun hc => hw1 (Subtype.ext hc))] at hmem
    exact Subgroup.mem_bot.2 (Subtype.ext (Subgroup.mem_bot.1 hmem))
  have hCK : ∀ v : ↥Y, (∀ w ∈ B.subgroupOf A, ρ w v = v) → v = 1 := by
    intro v hv
    have hvZ : (v : G) ∈ (P ⊓ Subgroup.centralizer (B : Set G)) := by
      refine Subgroup.mem_inf.2 ⟨hYP v.2, Subgroup.mem_centralizer_iff.2 fun b hb => ?_⟩
      have hfix := hv ⟨b, hBA hb⟩ (Subgroup.mem_subgroupOf.2 hb)
      exact mul_inv_eq_iff_eq_mul.1 (by rw [← hρ ⟨b, hBA hb⟩ v, hfix])
    have hmem : (v : G) ∈ (P ⊓ Subgroup.centralizer (B : Set G)) ⊓ Y :=
      Subgroup.mem_inf.2 ⟨hvZ, v.2⟩
    rw [hZY] at hmem
    exact Subtype.ext (Subgroup.mem_bot.1 hmem)
  have hker := le_ker_of_forall_fixedPoints_eq_one ρ hcop hNorm hcompl hC hCK
  intro x hx
  refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
  have hx1 : ρ ⟨x, hDA hx⟩ = 1 := MonoidHom.mem_ker.1 (hker (Subgroup.mem_subgroupOf.2 hx))
  have hcc := hρ ⟨x, hDA hx⟩ ⟨y, hy⟩
  rw [hx1] at hcc
  simp only [MulAut.one_apply] at hcc
  exact (mul_inv_eq_iff_eq_mul.1 hcc.symm).symm

private theorem inf_normalizer_core_le_centralizer_core :
    U ⊓ Subgroup.normalizer ((P ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) : Set G)
      ≤ Subgroup.centralizer ((P ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) : Set G) := by
  have hUcomm : IsMulCommutative ↥U := h.isMulCommutative_U
  set Z : Subgroup G := P ⊓ Subgroup.centralizer (B : Set G) with hZ
  set D : Subgroup G := U ⊓ Subgroup.normalizer (Z : Set G) with hDdef
  have hBZ : B ≤ Subgroup.centralizer (Z : Set G) := h.B_le_centralizer_core
  have hDU : D ≤ U := inf_le_left
  have hDNZ : D ≤ Subgroup.normalizer (Z : Set G) := inf_le_right
  have hBNZ : B ≤ Subgroup.normalizer (Z : Set G) :=
    hBZ.trans (Subgroup.centralizer_le_normalizer _)
  have hBND : B ≤ Subgroup.normalizer (D : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro b hb d hd
    exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 (h.B_le_normalizer_U hb) d).1
      (hDU hd), mul_mem (mul_mem (hBNZ hb) (hDNZ hd)) (inv_mem (hBNZ hb))⟩
  let ρ : ↥B →* MulAut ↥D := D.normalizerMonoidHom.comp (Subgroup.inclusion hBND)
  let act : MulDistribMulAction ↥B ↥D := MulDistribMulAction.compHom _ ρ
  have hsmul : ∀ (b : ↥B) (d : ↥D), ((b • d : ↥D) : G) = (b : G) * (d : G) * (b : G)⁻¹ := by
    intro b d
    change ((ρ b d : ↥D) : G) = _
    simp [ρ, Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hDcomm : IsMulCommutative ↥D := isMulCommutative_of_le (A := U) hDU
  have hDsol : Group.IsSolvable ↥D := Group.isSolvable_of_comm (isMulCommutative_iff.1 hDcomm)
  have hBsol : Group.IsSolvable ↥B :=
    Group.isSolvable_of_comm fun a b => h.isCyclic_B.commGroup.mul_comm a b
  have hcop : (Nat.card ↥B).Coprime (Nat.card ↥D) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hDU) h.coprime_U_B.symm
  have hfix : FixedPoints.subgroup ↥B ↥D = ⊥ := by
    obtain ⟨b0, hb0⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h.B_ne_bot
    have hb0' : (b0 : G) ≠ 1 := fun hc => hb0 (Subtype.ext hc)
    rw [eq_bot_iff]
    intro x hx
    rw [FixedPoints.mem_subgroup] at hx
    have hmem : (x : G) ∈ U ⊓ Subgroup.centralizer {(b0 : G)} := by
      refine Subgroup.mem_inf.2 ⟨hDU x.2, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
      rw [Set.mem_singleton_iff] at hg
      subst hg
      exact mul_inv_eq_iff_eq_mul.1 (by rw [← hsmul b0 x, hx b0])
    rw [h.inf_centralizer_singleton_eq_bot (b0 : G) b0.2 hb0'] at hmem
    exact Subgroup.mem_bot.2 (Subtype.ext (Subgroup.mem_bot.1 hmem))
  have hdisp : smulDisplacementSubgroup ↥B ↥D = ⊤ := by
    have hs := smulDisplacementSubgroup_sup_fixedPoints_subgroup ↥B ↥D hcop
    rwa [hfix, sup_bot_eq] at hs
  let φ : ↥D →* MulAut ↥Z := Z.normalizerMonoidHom.comp (Subgroup.inclusion hDNZ)
  have hφ : ∀ (d : ↥D) (z : ↥Z), ((φ d z : ↥Z) : G) = (d : G) * (z : G) * (d : G)⁻¹ := by
    intro d z; simp [φ, Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hkey : smulDisplacementSubgroup ↥B ↥D ≤ φ.ker := by
    refine smulDisplacementSubgroup_le fun b d => ?_
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    have hcomm : φ (b • d) = φ d := by
      ext z
      have hbz : (b : G)⁻¹ * (z : G) * (b : G) = (z : G) := by
        have hz2 := Subgroup.mem_centralizer_iff.1 (hBZ b.2) (z : G) z.2
        rw [mul_assoc, hz2]; group
      have hz3 := Subgroup.mem_centralizer_iff.1 (hBZ b.2) _ (φ d z).2
      rw [hφ] at hz3
      have hbdz : (b : G) * ((d : G) * (z : G) * (d : G)⁻¹) * (b : G)⁻¹
          = (d : G) * (z : G) * (d : G)⁻¹ := by rw [← hz3]; group
      rw [hφ, hsmul, hφ]
      calc ((b : G) * (d : G) * (b : G)⁻¹) * (z : G) * ((b : G) * (d : G) * (b : G)⁻¹)⁻¹
          = (b : G) * ((d : G) * ((b : G)⁻¹ * (z : G) * (b : G)) * (d : G)⁻¹) * (b : G)⁻¹ := by
            group
        _ = (b : G) * ((d : G) * (z : G) * (d : G)⁻¹) * (b : G)⁻¹ := by rw [hbz]
        _ = (d : G) * (z : G) * (d : G)⁻¹ := hbdz
    rw [hcomm, inv_mul_cancel]
  have hker : φ.ker = ⊤ := top_le_iff.1 (hdisp ▸ hkey)
  intro x hx
  refine Subgroup.mem_centralizer_iff.2 fun z hz => ?_
  have hx1 : φ ⟨x, hx⟩ = 1 := by rw [← MonoidHom.mem_ker, hker]; trivial
  have hcc := hφ ⟨x, hx⟩ ⟨z, hz⟩
  rw [hx1] at hcc
  simp only [MulAut.one_apply] at hcc
  exact (mul_inv_eq_iff_eq_mul.1 hcc.symm).symm

theorem inf_normalizer_core_eq_bot :
    U ⊓ Subgroup.normalizer ((P ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) : Set G) = ⊥ := by
  set Z : Subgroup G := P ⊓ Subgroup.centralizer (B : Set G) with hZ
  set D : Subgroup G := U ⊓ Subgroup.normalizer (Z : Set G) with hDdef
  have hDU : D ≤ U := inf_le_left
  have hDNZ : D ≤ Subgroup.normalizer (Z : Set G) := inf_le_right
  have hBZ : B ≤ Subgroup.centralizer (Z : Set G) := h.B_le_centralizer_core
  have hBNZ : B ≤ Subgroup.normalizer (Z : Set G) :=
    hBZ.trans (Subgroup.centralizer_le_normalizer _)
  have hBND : B ≤ Subgroup.normalizer (D : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro b hb d hd
    exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 (h.B_le_normalizer_U hb) d).1
      (hDU hd), mul_mem (mul_mem (hBNZ hb) (hDNZ hd)) (inv_mem (hBNZ hb))⟩
  set A : Subgroup G := D ⊔ B with hA
  have hANP : A ≤ Subgroup.normalizer (P : Set G) :=
    sup_le (hDU.trans h.U_le_normalizer_P) h.B_le_normalizer_P
  have hANZ : A ≤ Subgroup.normalizer (Z : Set G) := sup_le hDNZ hBNZ
  have hpA : ¬ p ∣ Nat.card A :=
    h.not_dvd_natCard_of_le_sup_U_B (sup_le (hDU.trans le_sup_left) le_sup_right)
  obtain ⟨Y, hYP, hANY, hZY, hZYP⟩ := h.exists_invariant_compl hANP hANZ hpA
  have hDY : D ≤ Subgroup.centralizer (Y : Set G) :=
    h.le_centralizer_of_invariant hDU hBND hYP hANY hZY
  have hDZ : D ≤ Subgroup.centralizer (Z : Set G) := h.inf_normalizer_core_le_centralizer_core
  have hDP : D ≤ Subgroup.centralizer (P : Set G) := by
    intro d hd
    refine Subgroup.mem_centralizer_iff.2 fun g hg => ?_
    have hle : Z ⊔ Y ≤ Subgroup.centralizer {d} := by
      refine sup_le (fun z hz => ?_) (fun y hy => ?_)
      · refine Subgroup.mem_centralizer_iff.2 fun w hw => ?_
        rw [Set.mem_singleton_iff] at hw
        subst hw
        exact (Subgroup.mem_centralizer_iff.1 (hDZ hd) z hz).symm
      · refine Subgroup.mem_centralizer_iff.2 fun w hw => ?_
        rw [Set.mem_singleton_iff] at hw
        subst hw
        exact (Subgroup.mem_centralizer_iff.1 (hDY hd) y hy).symm
    exact (Subgroup.mem_centralizer_iff.1 (hle (hZYP ▸ hg)) d rfl).symm
  rw [eq_bot_iff]
  intro x hx
  have : x ∈ U ⊓ Subgroup.centralizer (P : Set G) := Subgroup.mem_inf.2 ⟨hDU hx, hDP hx⟩
  rwa [h.inf_centralizer_P_eq_bot] at this

theorem normalizer_core_eq_sup :
    Subgroup.normalizer ((P ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) : Set G) = P ⊔ B := by
  set Z : Subgroup G := P ⊓ Subgroup.centralizer (B : Set G) with hZ
  refine le_antisymm (fun s hs => ?_) ?_
  · obtain ⟨x, hx, u, hu, b, hb, rfl⟩ := h.exists_mul_mul_of_mem_S (h.normalizer_core_le_S hs)
    have hxNZ : x ∈ Subgroup.normalizer (Z : Set G) :=
      Subgroup.centralizer_le_normalizer _ (h.P_le_centralizer_core hx)
    have hbNZ : b ∈ Subgroup.normalizer (Z : Set G) :=
      Subgroup.centralizer_le_normalizer _ (h.B_le_centralizer_core hb)
    have huNZ : u ∈ Subgroup.normalizer (Z : Set G) := by
      have hxu : x * u ∈ Subgroup.normalizer (Z : Set G) := by
        have : (x * u * b) * b⁻¹ ∈ Subgroup.normalizer (Z : Set G) :=
          mul_mem hs (inv_mem hbNZ)
        simpa using this
      have : x⁻¹ * (x * u) ∈ Subgroup.normalizer (Z : Set G) := mul_mem (inv_mem hxNZ) hxu
      simpa using this
    have hu1 : u = 1 := by
      have hmem : u ∈ U ⊓ Subgroup.normalizer (Z : Set G) := Subgroup.mem_inf.2 ⟨hu, huNZ⟩
      rw [h.inf_normalizer_core_eq_bot] at hmem
      exact Subgroup.mem_bot.1 hmem
    rw [hu1, mul_one]
    exact mul_mem (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hb)
  · exact h.sup_P_B_le_centralizer_core.trans (Subgroup.centralizer_le_normalizer _)

theorem centralizer_core_eq_sup :
    Subgroup.centralizer ((P ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) : Set G)
      = P ⊔ B :=
  le_antisymm ((Subgroup.centralizer_le_normalizer _).trans h.normalizer_core_eq_sup.le)
    h.sup_P_B_le_centralizer_core

theorem normalizer_core_eq_centralizer_core :
    Subgroup.normalizer ((P ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) : Set G)
      = Subgroup.centralizer ((P ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) : Set G) := by
  rw [h.normalizer_core_eq_sup, h.centralizer_core_eq_sup]

end Key

end IsFixedCoreConfig

end Main

end CFSG.FeitThompson
