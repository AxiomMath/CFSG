module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.Open.LocalVocabulary
import CFSG.GF2Type.CenterFour.SymplecticIsotropic
import CFSG.GF2Type.CenterFour.SymplecticPairwise

public section

namespace CFSG.GF2Type.CenterFour

open Subgroup
open scoped IsMulCommutative commutatorElement

theorem zmod2_eq_one_of_val (t : ZMod 2) (h : t.val = 1) : t = 1 := by
  revert t h
  decide

section Image

variable {P : Type*} [Group P] [Finite P] [Fact (Nat.Prime 2)]
  [CFSG.IsElementaryAbelian 2 (P ⧸ center P)]

def imageSub (U : Subgroup P) : Submodule (ZMod 2) (Additive (P ⧸ center P)) :=
  (AddSubgroup.toZModSubmodule (n := 2))
    (Subgroup.toAddSubgroup (U.map (QuotientGroup.mk' (center P))))

theorem mem_imageSub (U : Subgroup P) (x : Additive (P ⧸ center P)) :
    x ∈ imageSub U ↔ Additive.toMul x ∈ U.map (QuotientGroup.mk' (center P)) := by
  simp [imageSub]

theorem natCard_map_eq_natCard_imageSub (U : Subgroup P) :
    Nat.card (U.map (QuotientGroup.mk' (center P))) = Nat.card (imageSub U) :=
  Nat.card_congr (Equiv.subtypeEquiv Additive.ofMul fun a =>
    (mem_imageSub U (Additive.ofMul a)).symm)

end Image

section

variable {P : Type*} [Group P] [Finite P] [Fact (Nat.Prime 2)]
  [CFSG.IsElementaryAbelian 2 (P ⧸ center P)] {c : P}
  (b : LinearMap.BilinForm (ZMod 2) (Additive (P ⧸ center P)))
  (hrule : ∀ x y : P, ⁅x, y⁆ =
    c ^ (b (Additive.ofMul (x : P ⧸ center P)) (Additive.ofMul (y : P ⧸ center P))).val)
  {v : ℕ} (hdim : Module.finrank (ZMod 2) (Additive (P ⧸ center P)) = 2 * v)

include hrule in
theorem imageSub_isotropic (hc : c ≠ 1) {U : Subgroup P} (hU : CFSG.Open.IsElemAbelian 2 U) :
    ∀ x ∈ imageSub U, ∀ y ∈ imageSub U, b x y = 0 := by
  intro x hx y hy
  rw [mem_imageSub] at hx hy
  obtain ⟨u, hu, hux⟩ := Subgroup.mem_map.mp hx
  obtain ⟨u', hu', huy⟩ := Subgroup.mem_map.mp hy
  rw [QuotientGroup.mk'_apply] at hux huy
  have hx' : x = Additive.ofMul ((u : P) : P ⧸ center P) := by
    simp [hux]
  have hy' : y = Additive.ofMul ((u' : P) : P ⧸ center P) := by
    simp [huy]
  haveI : IsMulCommutative U := hU.1
  have hcomm : u * u' = u' * u := by
    have h := (IsMulCommutative.is_comm (M := U)).comm ⟨u, hu⟩ ⟨u', hu'⟩
    exact congrArg Subtype.val h
  have hone : ⁅u, u'⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hcomm
  have hpow := hrule u u'
  rw [hone] at hpow
  have hv : (b (Additive.ofMul ((u : P) : P ⧸ center P))
      (Additive.ofMul ((u' : P) : P ⧸ center P))).val = 0 := by
    have hlt := ZMod.val_lt (b (Additive.ofMul ((u : P) : P ⧸ center P))
      (Additive.ofMul ((u' : P) : P ⧸ center P)))
    rcases Nat.lt_or_ge (b (Additive.ofMul ((u : P) : P ⧸ center P))
      (Additive.ofMul ((u' : P) : P ⧸ center P))).val 1 with h0 | h1
    · omega
    · have h1' : (b (Additive.ofMul ((u : P) : P ⧸ center P))
          (Additive.ofMul ((u' : P) : P ⧸ center P))).val = 1 := by omega
      rw [h1', pow_one] at hpow
      exact absurd hpow.symm hc
  rw [hx', hy']
  exact (ZMod.val_eq_zero _).mp hv

include hrule hdim in
theorem natCard_map_le_pow (hnd : b.Nondegenerate) (hc : c ≠ 1)
    {U : Subgroup P} (hU : CFSG.Open.IsElemAbelian 2 U) :
    Nat.card (U.map (QuotientGroup.mk' (center P))) ≤ 2 ^ v := by
  have h2 := two_mul_finrank_le_of_isOrtho b hnd (imageSub U) (imageSub_isotropic b hrule hc hU)
  rw [hdim] at h2
  have hv : Module.finrank (ZMod 2) (imageSub U) ≤ v := by omega
  have hcard2 : Nat.card (ZMod 2) = 2 := by
    rw [Nat.card_eq_fintype_card, ZMod.card]
  rw [natCard_map_eq_natCard_imageSub, Module.natCard_eq_pow_finrank (K := ZMod 2), hcard2]
  exact Nat.pow_le_pow_right (by norm_num) hv

theorem natCard_eq_natCard_inf_mul (U : Subgroup P) :
    Nat.card U = Nat.card (U ⊓ center P : Subgroup P) *
      Nat.card (U.map (QuotientGroup.mk' (center P))) := by
  have hker : ((QuotientGroup.mk' (center P)).comp U.subtype).ker
      = (U ⊓ center P).subgroupOf U := by
    ext x
    simp [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, QuotientGroup.eq_one_iff, Subgroup.mem_inf]
  have hrange : ((QuotientGroup.mk' (center P)).comp U.subtype).range
      = U.map (QuotientGroup.mk' (center P)) := by
    ext y
    simp [MonoidHom.mem_range, Subgroup.mem_map]
  have hK : Nat.card ((U ⊓ center P).subgroupOf U) = Nat.card (U ⊓ center P : Subgroup P) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have h1 := ((QuotientGroup.mk' (center P)).comp U.subtype).ker.card_mul_index
  have h2 := Subgroup.index_ker ((QuotientGroup.mk' (center P)).comp U.subtype)
  rw [h2] at h1
  rw [hker, hK, hrange] at h1
  exact h1.symm

theorem natCard_inf_center_le_two (hZ : IsCyclic (center P)) {U : Subgroup P}
    (hU : CFSG.Open.IsElemAbelian 2 U) :
    Nat.card (U ⊓ center P : Subgroup P) ≤ 2 := by
  haveI := hZ
  have hK : Nat.card (U ⊓ center P : Subgroup P) =
      Nat.card ((U ⊓ center P).subgroupOf (center P)) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).symm
  rw [hK]
  have hexp : Monoid.exponent ((U ⊓ center P).subgroupOf (center P)) ∣ 2 := by
    refine Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_
    intro x
    apply Subtype.ext
    apply Subtype.ext
    have hx : ((x : center P) : P) ∈ U :=
      (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp x.2)).1
    have hx2 := hU.2 _ hx
    simpa using hx2
  rw [IsCyclic.exponent_eq_card] at hexp
  exact Nat.le_of_dvd (by norm_num) hexp

include hrule hdim in
theorem card_le_of_disjoint (hnd : b.Nondegenerate) (hc : c ≠ 1) {U : Subgroup P}
    (hU : CFSG.Open.IsElemAbelian 2 U) (hUZ : U ⊓ center P = ⊥) : Nat.card U ≤ 2 ^ v := by
  have hsplit := natCard_eq_natCard_inf_mul U
  rw [hUZ, Subgroup.card_bot, one_mul] at hsplit
  rw [hsplit]
  exact natCard_map_le_pow b hrule hdim hnd hc hU

include hrule hdim in
theorem card_le_of_elemAbelian (hnd : b.Nondegenerate) (hc : c ≠ 1) (hZ : IsCyclic (center P))
    {U : Subgroup P} (hU : CFSG.Open.IsElemAbelian 2 U) : Nat.card U ≤ 2 ^ (v + 1) := by
  have hsplit := natCard_eq_natCard_inf_mul U
  have h2 := natCard_inf_center_le_two hZ hU
  have h3 := natCard_map_le_pow b hrule hdim hnd hc hU
  rw [hsplit]
  calc Nat.card (U ⊓ center P : Subgroup P) * Nat.card (U.map (QuotientGroup.mk' (center P)))
      ≤ 2 * 2 ^ v := Nat.mul_le_mul h2 h3
    _ = 2 ^ (v + 1) := by ring

include hrule hdim in
theorem card_le_of_pairwise (halt : b.IsAlt) (hc : c ≠ 1) {s : ℕ} (f : Fin s → P)
    (hf : ∀ i j, i ≠ j → ⁅f i, f j⁆ = c) : s ≤ 2 * v + 1 := by
  have hpair : ∀ i j, i ≠ j →
      b (Additive.ofMul ((f i : P) : P ⧸ center P))
        (Additive.ofMul ((f j : P) : P ⧸ center P)) = 1 := by
    intro i j hij
    have h := hrule (f i) (f j)
    rw [hf i j hij] at h
    have ht : (b (Additive.ofMul ((f i : P) : P ⧸ center P))
        (Additive.ofMul ((f j : P) : P ⧸ center P))).val ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at h
      exact hc h
    have ht1 : (b (Additive.ofMul ((f i : P) : P ⧸ center P))
        (Additive.ofMul ((f j : P) : P ⧸ center P))).val = 1 := by
      have hlt := ZMod.val_lt (b (Additive.ofMul ((f i : P) : P ⧸ center P))
        (Additive.ofMul ((f j : P) : P ⧸ center P)))
      have hne : (b (Additive.ofMul ((f i : P) : P ⧸ center P))
          (Additive.ofMul ((f j : P) : P ⧸ center P))).val < 2 := by
        simpa using hlt
      omega
    exact zmod2_eq_one_of_val _ ht1
  have hle :=
    card_le_finrank_add_one b halt (fun i => Additive.ofMul ((f i : P) : P ⧸ center P)) hpair
  rw [hdim] at hle
  exact hle

end

end CFSG.GF2Type.CenterFour
