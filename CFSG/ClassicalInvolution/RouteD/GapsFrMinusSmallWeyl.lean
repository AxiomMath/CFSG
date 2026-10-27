module

public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusLeaf
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted CFSG.Timmesfeld

section Weyl

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {n : ℕ}

private theorem longWeylBool_not {i j : Fin n} (s t : Bool) (m : Fin n) (r : Bool) :
    longWeylBool i j s t m (!r) = !(longWeylBool i j s t m r) := by
  unfold longWeylBool
  split_ifs <;> cases r <;> cases s <;> cases t <;> simp

theorem map_conj_longWeyl_rootSL2 (F₀ : HypFrame Q n) {i j : Fin n} (hij : i ≠ j) (s t : Bool)
    {a b : ℕ} (ha : a < n) (hb : b < n) (hab : a ≠ b) (u v : Bool) :
    (rootSL2 F₀ a b ha hb hab u v).map (MulAut.conj (F₀.longWeyl hij s t)).toMonoidHom =
      rootSL2 F₀ (Equiv.swap i j ⟨a, ha⟩).val (Equiv.swap i j ⟨b, hb⟩).val
        (Equiv.swap i j ⟨a, ha⟩).isLt (Equiv.swap i j ⟨b, hb⟩).isLt
        (fun h => hab (by
          have h' : Equiv.swap i j ⟨a, ha⟩ = Equiv.swap i j ⟨b, hb⟩ := Fin.ext h
          exact congrArg Fin.val ((Equiv.swap i j).injective h')))
        (longWeylBool i j s t ⟨a, ha⟩ u) (longWeylBool i j s t ⟨b, hb⟩ v) := by
  have key : ∀ {k l : Fin n} (hkl : k ≠ l) (u v : Bool),
      (F₀.longRoot hkl u v).range.map (MulAut.conj (F₀.longWeyl hij s t)).toMonoidHom =
        (F₀.longRoot ((Equiv.swap i j).injective.ne hkl) (longWeylBool i j s t k u)
          (longWeylBool i j s t l v)).range := by
    intro k l hkl u v
    have hε : (longWeylSign i k : K) * longWeylSign i l ≠ 0 := by
      unfold longWeylSign
      split_ifs <;> simp
    ext y
    constructor
    · rintro ⟨_, ⟨c', rfl⟩, rfl⟩
      refine ⟨Multiplicative.ofAdd ((longWeylSign i k : K) * longWeylSign i l *
        Multiplicative.toAdd c'), ?_⟩
      exact (F₀.longWeyl_conj_longRoot hij s t hkl u v (Multiplicative.toAdd c')).symm
    · rintro ⟨c', rfl⟩
      refine ⟨_, ⟨Multiplicative.ofAdd (((longWeylSign i k : K) * longWeylSign i l)⁻¹ *
        Multiplicative.toAdd c'), rfl⟩, ?_⟩
      have h := F₀.longWeyl_conj_longRoot hij s t hkl u v
        (((longWeylSign i k : K) * longWeylSign i l)⁻¹ * Multiplicative.toAdd c')
      rw [← mul_assoc, mul_inv_cancel₀ hε, one_mul] at h
      exact h
  have hij' : (⟨a, ha⟩ : Fin n) ≠ ⟨b, hb⟩ := fun h => hab (congrArg Fin.val h)
  unfold rootSL2
  rw [longSL2_range_eq_sup, longSL2_range_eq_sup, Subgroup.map_sup, key hij' u v,
    key hij'.symm (!v) (!u), longWeylBool_not, longWeylBool_not]

end Weyl

section Bridge

variable {p f : ℕ} [Fact p.Prime]

theorem stdPair_nodeM_minus {s : ℕ} (hs : 1 ≤ s) (hp2 : p ≠ 2)
    (x : spinGroup (quadMinus (s + 5) (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2)) (tM : Bool) :
    ∃ W, LinearBlockStandardPair (GaloisField p f) W
      ((rootSL2 (minusHyp (s + 5) (minusCoeffs p f).1 (minusCoeffs p f).2) (s + 1) (s + 2)
        (by omega) (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom)
      ((rootSL2 (minusHyp (s + 5) (minusCoeffs p f).1 (minusCoeffs p f).2) (s + 2) (s + 3)
        (by omega) (by omega) (by omega) true tM).map (MulAut.conj x).toMonoidHom) := by
  have hm3 : 3 ≤ s + 5 - 1 := by omega
  set Fr := minusHyp (s + 5) (minusCoeffs p f).1 (minusCoeffs p f).2 with hFr
  have hA : dNode hm3 Fr x ⟨s + 1, by omega⟩ = (rootSL2 Fr (s + 1) (s + 2) (by omega) (by omega)
      (by omega) true false).map (MulAut.conj x).toMonoidHom := by
    rw [dNode_lt hm3 Fr x ⟨s + 1, by omega⟩ (by show s + 1 + 1 < s + 5 - 1; omega)]
  cases tM with
  | false =>
    obtain ⟨W, hW⟩ := stdPair_dNode_minus (p := p) (f := f) (m := s + 5) (by omega) hp2 x
      (a := ⟨s + 1, by omega⟩) (b := ⟨s + 2, by omega⟩)
      (Or.inl ⟨rfl, by show s + 2 + 1 < s + 5 - 1; omega⟩)
    have hB : dNode hm3 Fr x ⟨s + 2, by omega⟩ = (rootSL2 Fr (s + 2) (s + 3) (by omega)
        (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom := by
      rw [dNode_lt hm3 Fr x ⟨s + 2, by omega⟩ (by show s + 2 + 1 < s + 5 - 1; omega)]
    rw [hA, hB] at hW
    exact ⟨W, hW⟩
  | true =>
    obtain ⟨W, hW⟩ := stdPair_dNode_minus (p := p) (f := f) (m := s + 5) (by omega) hp2 x
      (a := ⟨s + 1, by omega⟩) (b := ⟨s + 3, by omega⟩)
      (Or.inr ⟨by show s + 1 + 3 = s + 5 - 1; omega, by show s + 3 + 1 = s + 5 - 1; omega⟩)
    have hB : dNode hm3 Fr x ⟨s + 3, by omega⟩ = (rootSL2 Fr (s + 2) (s + 3) (by omega)
        (by omega) (by omega) true true).map (MulAut.conj x).toMonoidHom := by
      rw [dNode_last hm3 Fr x ⟨s + 3, by omega⟩ (by show ¬ s + 3 + 1 < s + 5 - 1; omega)]
      congr 1
    rw [hA, hB] at hW
    exact ⟨W, hW⟩

private theorem map_conj_conj_conj {G : Type} [Group G] (x w : G) (A : Subgroup G) :
    (A.map (MulAut.conj x).toMonoidHom).map (MulAut.conj (x * w * x⁻¹)).toMonoidHom =
      (A.map (MulAut.conj w).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext y
  show x * w * x⁻¹ * (x * y * x⁻¹) * (x * w * x⁻¹)⁻¹ = x * (w * y * w⁻¹) * x⁻¹
  group

theorem stdPair_bridge_minus {s : ℕ} (hs : 3 ≤ s) (hp2 : p ≠ 2)
    (x : spinGroup (quadMinus (s + 5) (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2)) (tM : Bool) :
    ∃ W, LinearBlockStandardPair (GaloisField p f) W
      ((rootSL2 (minusHyp (s + 5) (minusCoeffs p f).1 (minusCoeffs p f).2) 2 (s + 2)
        (by omega) (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom)
      ((rootSL2 (minusHyp (s + 5) (minusCoeffs p f).1 (minusCoeffs p f).2) (s + 2) (s + 3)
        (by omega) (by omega) (by omega) true tM).map (MulAut.conj x).toMonoidHom) := by
  obtain ⟨W, hW⟩ := stdPair_nodeM_minus (p := p) (f := f) (by omega) hp2 x tM
  set Fr := minusHyp (s + 5) (minusCoeffs p f).1 (minusCoeffs p f).2 with hFr
  have hij : (⟨2, by omega⟩ : Fin (s + 5 - 1)) ≠ ⟨s + 1, by omega⟩ := by
    simp [Fin.ext_iff]
    try omega
  set w := Fr.longWeyl hij false true with hw
  have hW2 := CFSG.ClassicalInvolution.ModelFacts.linearBlockStandardPair_map_conj hW
    (x * w * x⁻¹)
  rw [map_conj_conj_conj, map_conj_conj_conj] at hW2
  have h1 : (rootSL2 Fr (s + 1) (s + 2) (by omega) (by omega) (by omega) true false).map
      (MulAut.conj w).toMonoidHom = rootSL2 Fr 2 (s + 2) (by omega) (by omega) (by omega) true
        false := by
    rw [hw, map_conj_longWeyl_rootSL2 Fr hij false true]
    have e1 : (Equiv.swap (⟨2, by omega⟩ : Fin (s + 5 - 1)) ⟨s + 1, by omega⟩
        ⟨s + 1, by omega⟩).val = 2 := by
      rw [Equiv.swap_apply_right]
    have e2 : (Equiv.swap (⟨2, by omega⟩ : Fin (s + 5 - 1)) ⟨s + 1, by omega⟩
        ⟨s + 2, by omega⟩).val = s + 2 := by
      rw [Equiv.swap_apply_of_ne_of_ne (by simp [Fin.ext_iff]; try omega)
        (by simp [Fin.ext_iff]; try omega)]
    rw [rootSL2_congr Fr _ _ _ (by omega) (by omega) (by omega) e1 e2]
    have e3 : longWeylBool (⟨2, by omega⟩ : Fin (s + 5 - 1)) ⟨s + 1, by omega⟩ false true
        ⟨s + 1, by omega⟩ true = true := by
      rw [longWeylBool_right false true]
      rfl
    have e4 : longWeylBool (⟨2, by omega⟩ : Fin (s + 5 - 1)) ⟨s + 1, by omega⟩ false true
        ⟨s + 2, by omega⟩ false = false := by
      rw [longWeylBool_of_ne false true (by simp [Fin.ext_iff]; try omega)
        (by simp [Fin.ext_iff]; try omega)]
    rw [e3, e4]
  have h2 : (rootSL2 Fr (s + 2) (s + 3) (by omega) (by omega) (by omega) true tM).map
      (MulAut.conj w).toMonoidHom = rootSL2 Fr (s + 2) (s + 3) (by omega) (by omega) (by omega)
        true tM := by
    rw [hw, map_conj_longWeyl_rootSL2 Fr hij false true]
    have e1 : (Equiv.swap (⟨2, by omega⟩ : Fin (s + 5 - 1)) ⟨s + 1, by omega⟩
        ⟨s + 2, by omega⟩).val = s + 2 := by
      rw [Equiv.swap_apply_of_ne_of_ne (by simp [Fin.ext_iff]; try omega)
        (by simp [Fin.ext_iff]; try omega)]
    have e2 : (Equiv.swap (⟨2, by omega⟩ : Fin (s + 5 - 1)) ⟨s + 1, by omega⟩
        ⟨s + 3, by omega⟩).val = s + 3 := by
      rw [Equiv.swap_apply_of_ne_of_ne (by simp [Fin.ext_iff]; try omega)
        (by simp [Fin.ext_iff]; try omega)]
    rw [rootSL2_congr Fr _ _ _ (by omega) (by omega) (by omega) e1 e2]
    rw [longWeylBool_of_ne false true (by simp [Fin.ext_iff]; try omega)
        (by simp [Fin.ext_iff]; try omega),
      longWeylBool_of_ne false true (by simp [Fin.ext_iff]; try omega)
        (by simp [Fin.ext_iff]; try omega)]
  rw [h1, h2] at hW2
  exact ⟨_, hW2⟩

end Bridge

end CFSG.ClassicalInvolution.RouteD.Gaps
