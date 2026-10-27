module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.RankThree.PartTwo.Sec4.RonanK429RowTools
import CFSG.RankThree.PartTwo.Sec4.Item413AutGen
import CFSG.RankThree.PartOne.K133.KillL2
import CFSG.HardMathSupport.Solomon.Coordinator.I11_2FullTypes
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CDefs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenDefs
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KbarListThree

open CFSG.Open Subgroup CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.RankThreeUC.AGL81C (IsSLType)

theorem center_eq_bot_of_quasisimple {K S : Type} [Group K] [Group S] (hq : CFSG.IsQuasisimple K)
    (e : K ⧸ center K ≃* S) : center S = ⊥ := by
  obtain ⟨-, hs, a, b, hab⟩ := hq
  have h : center (K ⧸ center K) = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal _).resolve_right fun ht =>
      hab (mem_center_iff.mp (ht ▸ mem_top b) a)
  rw [← Subgroup.map_center_eq e, h, Subgroup.map_bot]

theorem false_of_pRank_mulAut_le_two {S : Type} [Group S] [Finite S]
    (h : CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut S)) ≤ 2) {V : Subgroup (MulAut S)}
    (hV : IsElemAbelian 3 V) (hc : Nat.card V = 27) : False := by
  have : Finite (MulAut S) := MulEquiv.finite_left
  have h3 := CFSG.SectionRank.le_pRank (by norm_num) (le_top : V ≤ ⊤) hV
    (show Nat.card V = 3 ^ 3 by rw [hc]; norm_num)
  omega

theorem false_of_le_inner {S : Type} [Group S] [Finite S] (hZ : center S = ⊥)
    (hr : CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ 2) {V : Subgroup (MulAut S)}
    (hV : IsElemAbelian 3 V) (hc : Nat.card V = 27)
    (hVI : V ≤ (MulAut.conj : S →* MulAut S).range) : False := by
  have hinj := CFSG.RankThree.PartTwo.Sec4.RonanK429.conj_injective_of_center_eq_bot hZ
  have hmap : (V.comap (MulAut.conj : S →* MulAut S)).map MulAut.conj = V :=
    map_comap_eq_self hVI
  have hP : IsElemAbelian 3 (V.comap (MulAut.conj : S →* MulAut S)) := hV.comap hinj
  have hPc : Nat.card (V.comap (MulAut.conj : S →* MulAut S)) = 3 ^ 3 := by
    rw [← card_map_of_injective hinj, hmap, hc]
    norm_num
  have h3 := CFSG.SectionRank.le_pRank (by norm_num) le_top hP hPc
  omega

theorem le_inner_of_not_three_dvd {S : Type} [Group S] (hout : ¬ 3 ∣ Nat.card (Outer S))
    {V : Subgroup (MulAut S)} (hV : IsElemAbelian 3 V) :
    V ≤ (MulAut.conj : S →* MulAut S).range := fun a ha =>
  CFSG.RankThree.PartTwo.Sec4.RonanK429.mem_inner_of_pow_three hout (hV.2 a ha)

theorem not_three_dvd_card_outer_of_isPGroup_two {S : Type} [Group S] [Finite S]
    (h : IsPGroup 2 (Outer S)) : ¬ 3 ∣ Nat.card (Outer S) := by
  have : Finite (MulAut S) := MulEquiv.finite_left
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := h.exists_card_eq
  rw [hn]
  intro h3
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
    (Nat.prime_three.dvd_of_dvd_pow h3)
  omega

theorem not_three_dvd_card_outer_of_le_two {S : Type} [Group S] [Finite S]
    (h : Nat.card (Outer S) ≤ 2) : ¬ 3 ∣ Nat.card (Outer S) := by
  have : Finite (MulAut S) := MulEquiv.finite_left
  intro h3
  have := Nat.le_of_dvd Nat.card_pos h3
  omega

theorem false_of_alt_six {S : Type} [Group S] [Finite S] (hZ : center S = ⊥)
    (e : S ≃* alternatingGroup (Fin 6)) {V : Subgroup (MulAut S)} (hV : IsElemAbelian 3 V)
    (hc : Nat.card V = 27) : False :=
  false_of_pRank_mulAut_le_two
    (CFSG.HardMathSupport.Solomon.Coordinator.i112f_pRank_mulAut_alt (Or.inl rfl) hZ e) hV hc

theorem false_of_psl_two_eight {S : Type} [Group S] [Finite S]
    (hS : StatedClassicalModel S .PSL 2 2 3) {V : Subgroup (MulAut S)} (hV : IsElemAbelian 3 V)
    (hc : Nat.card V = 27) : False := by
  obtain ⟨-, F, instF, instFin, hF, ⟨a⟩⟩ := hS
  let ψ : S ≃* CFSG.GorensteinWalter.PSL2 F :=
    a.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
  have : NeZero (3 : F) :=
    ⟨CFSG.RankThree.PartTwo.Sec4.three_ne_zero_of_card Nat.prime_two (by norm_num) hF⟩
  have hno := CFSG.RankThree.PartOne.K133.NoRankThree.of_mulEquiv Nat.prime_three ψ
    (CFSG.RankThree.PartOne.K133.noRankThree_psl2 Nat.prime_three (by norm_num))
  exact hno ⟨V, (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 V).2 hV,
    by simpa using hc⟩

theorem false_of_psl_three_four {S : Type} [Group S] [Finite S]
    (hS : StatedClassicalModel S .PSL 3 2 2) {V : Subgroup (MulAut S)} (hV : IsElemAbelian 3 V)
    (hc : Nat.card V = 27) : False := by
  obtain ⟨-, F, instF, instFin, hF, ⟨a⟩⟩ := hS
  exact false_of_pRank_mulAut_le_two
    (CFSG.LocalAnalysis.GLTheoremB.pRank_mulAut_le_two_of_isLThreeFour
      ⟨F, instF, instFin, by rw [hF]; norm_num, ⟨a⟩⟩) hV hc

theorem false_of_sl_three_four {K S : Type} [Group K] [Group S] [Finite S]
    (e : K ⧸ center K ≃* S) {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4)
    (hK : IsSLType 3 F K) {V : Subgroup (MulAut S)} (hV : IsElemAbelian 3 V)
    (hc : Nat.card V = 27) : False := by
  obtain ⟨e₁⟩ := hK
  exact false_of_pRank_mulAut_le_two
    (CFSG.LocalAnalysis.GLTheoremB.pRank_mulAut_le_two_of_isLThreeFour
      ⟨F, inferInstance, inferInstance, hF,
        ⟨e.symm.trans ((QuotientGroup.congr _ _ e₁ (Subgroup.map_center_eq e₁)).trans
          (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F))⟩⟩) hV hc

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KbarListThree

end
