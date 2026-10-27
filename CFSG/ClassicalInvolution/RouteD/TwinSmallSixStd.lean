module

public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusNodes
public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusSmallWeyl
public import CFSG.ClassicalInvolution.RouteD.TwinSmallTwin
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

namespace CFSG.ClassicalInvolution.RouteD.TwinSmall

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalGroups.Orthogonal CFSG.Timmesfeld QuadraticMap

section Swap

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {n : ℕ}

theorem map_conj_swapWeyl_rootSL2 (F₀ : HypFrame Q n) {i j : Fin n} (hij : i ≠ j) {a b : ℕ}
    (ha : a < n) (hb : b < n) (hab : a ≠ b) (u v : Bool) {a' b' : ℕ} (ha' : a' < n)
    (hb' : b' < n) (hab' : a' ≠ b') (e : (Equiv.swap i j ⟨a, ha⟩).val = a')
    (e' : (Equiv.swap i j ⟨b, hb⟩).val = b') :
    (rootSL2 F₀ a b ha hb hab u v).map (MulAut.conj (F₀.longWeyl hij false true)).toMonoidHom =
      rootSL2 F₀ a' b' ha' hb' hab' u v := by
  have hlw : ∀ (m : Fin n) (r : Bool), longWeylBool i j false true m r = r := by
    intro m r
    simp [longWeylBool]
  rw [map_conj_longWeyl_rootSL2 F₀ hij false true ha hb hab u v, hlw, hlw]
  exact rootSL2_congr F₀ _ _ _ ha' hb' hab' e e' u v

end Swap

section Std

variable {p f : ℕ} [Fact p.Prime]

theorem stdPair_zero_three (hp2 : p ≠ 2) (x : SpinM p f 6) (tM : Bool) :
    ∃ W, LinearBlockStandardPair (GaloisField p f) W
      ((rootSL2 (minusHyp 6 (minusCoeffs p f).1 (minusCoeffs p f).2) 0 3 (by omega) (by omega)
        (by omega) true false).map (MulAut.conj x).toMonoidHom)
      ((rootSL2 (minusHyp 6 (minusCoeffs p f).1 (minusCoeffs p f).2) 3 4 (by omega) (by omega)
        (by omega) true tM).map (MulAut.conj x).toMonoidHom) := by
  set Fr := (minusFrame 6 (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame with hFr
  have hij : (⟨0, by omega⟩ : Fin (6 - 1)) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  set w := Fr.longWeyl hij false true with hw
  have e0 : (Equiv.swap (⟨0, by omega⟩ : Fin (6 - 1)) ⟨2, by omega⟩ ⟨2, by omega⟩).val = 0 := by
    rw [Equiv.swap_apply_right]
  have e3 : (Equiv.swap (⟨0, by omega⟩ : Fin (6 - 1)) ⟨2, by omega⟩ ⟨3, by omega⟩).val = 3 := by
    rw [Equiv.swap_apply_of_ne_of_ne (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])]
  have e4 : (Equiv.swap (⟨0, by omega⟩ : Fin (6 - 1)) ⟨2, by omega⟩ ⟨4, by omega⟩).val = 4 := by
    rw [Equiv.swap_apply_of_ne_of_ne (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])]
  have hA : (rootSL2 Fr 2 3 (by omega) (by omega) (by omega) true false).map
      (MulAut.conj w).toMonoidHom = rootSL2 Fr 0 3 (by omega) (by omega) (by omega) true false :=
    map_conj_swapWeyl_rootSL2 Fr hij _ _ _ true false _ _ _ e0 e3
  have hB : (rootSL2 Fr 3 4 (by omega) (by omega) (by omega) true false).map
      (MulAut.conj w).toMonoidHom = rootSL2 Fr 3 4 (by omega) (by omega) (by omega) true false :=
    map_conj_swapWeyl_rootSL2 Fr hij _ _ _ true false _ _ _ e3 e4
  have hC : (rootSL2 Fr 3 4 (by omega) (by omega) (by omega) true true).map
      (MulAut.conj w).toMonoidHom = rootSL2 Fr 3 4 (by omega) (by omega) (by omega) true true :=
    map_conj_swapWeyl_rootSL2 Fr hij _ _ _ true true _ _ _ e3 e4
  have edge23 : edgeD (6 - 1) (⟨2, by omega⟩ : Fin (6 - 1)) ⟨3, by omega⟩ :=
    Or.inl ⟨rfl, by decide⟩
  have edge24 : edgeD (6 - 1) (⟨2, by omega⟩ : Fin (6 - 1)) ⟨4, by omega⟩ :=
    Or.inr ⟨by decide, by decide⟩
  cases tM
  · obtain ⟨W₁, hW₁⟩ := stdPair_dNode_minus (m := 6) (f := f) (by norm_num) hp2 w
      (a := ⟨2, by omega⟩) (b := ⟨3, by omega⟩) edge23
    rw [dNode_lt (by omega) _ w _ (by show 2 + 1 < 6 - 1; omega),
      dNode_lt (by omega) _ w _ (by show 3 + 1 < 6 - 1; omega)] at hW₁
    have hW₂ : LinearBlockStandardPair (GaloisField p f) W₁
        ((rootSL2 Fr 2 3 (by omega) (by omega) (by omega) true false).map
          (MulAut.conj w).toMonoidHom)
        ((rootSL2 Fr 3 4 (by omega) (by omega) (by omega) true false).map
          (MulAut.conj w).toMonoidHom) := hW₁
    rw [hA, hB] at hW₂
    exact ⟨_, CFSG.ClassicalInvolution.ModelFacts.linearBlockStandardPair_map_conj hW₂ x⟩
  · obtain ⟨W₁, hW₁⟩ := stdPair_dNode_minus (m := 6) (f := f) (by norm_num) hp2 w
      (a := ⟨2, by omega⟩) (b := ⟨4, by omega⟩) edge24
    rw [dNode_lt (by omega) _ w _ (by show 2 + 1 < 6 - 1; omega),
      dNode_last (by omega) _ w _ (by show ¬ 4 + 1 < 6 - 1; omega)] at hW₁
    have hW₂ : LinearBlockStandardPair (GaloisField p f) W₁
        ((rootSL2 Fr 2 3 (by omega) (by omega) (by omega) true false).map
          (MulAut.conj w).toMonoidHom)
        ((rootSL2 Fr 3 4 (by omega) (by omega) (by omega) true true).map
          (MulAut.conj w).toMonoidHom) := hW₁
    rw [hA, hC] at hW₂
    exact ⟨_, CFSG.ClassicalInvolution.ModelFacts.linearBlockStandardPair_map_conj hW₂ x⟩

end Std

end CFSG.ClassicalInvolution.RouteD.TwinSmall
