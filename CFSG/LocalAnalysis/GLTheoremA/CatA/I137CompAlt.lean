module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I137CompList
public import CFSG.HardMathSupport.Dickson.I271.Support.OuterTransport
public import CFSG.LocalAnalysis.GLTheoremA.PartI.RankTwoDownAux
public import CFSG.LocalAnalysis.GLTheoremA.S6.AltSetup

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (LieOrderBridge)

private theorem alternatingGroup_fin_nine_nonabelian :
    ∃ a b : alternatingGroup (Fin 9), a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have hc : IsMulCommutative (alternatingGroup (Fin 9)) := ⟨⟨fun a b => hcon a b⟩⟩
  have h3 := alternatingGroup.isMulCommutative_iff_card_le_three.1 hc
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h3
  omega

section Certificates


theorem isChevSimple_two_of_alt_comp (hb : LieOrderBridge) {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hn : 5 ≤ n) (hk : (p = 3 ∧ (n = 5 ∨ n = 9)) ∨ (p = 7 ∧ n = 7)) {S : Type} [Group S]
    [Finite S] (e : S ≃* alternatingGroup (Fin n)) (α : MulAut S) (hα : α ^ p = 1)
    (I : Subgroup S)
    (hI : GLAPComponent p (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α) I)
    (hcat : catalogIs (PSimple p I) (S9.isList93 p)) : IsChevSimple 2 S := by
  rcases hk with ⟨hp3, hn5 | hn9⟩ | ⟨hp7, hn7⟩
  ·
    subst hp3
    subst hn5
    refine Or.inr ⟨TauCeti.CFSGIndex.alternating 5 (by norm_num), ?_, ?_⟩
    · simp [ambiguousChev]
    · exact ⟨e⟩
  ·
    subst hp3
    subst hn9
    exfalso
    by_cases hα1 : α = 1
    ·
      subst hα1
      have hfix : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (1 : MulAut S) = ⊤ := by
        ext x
        simp [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup]
      have hItop : GLAPComponent 3 (⊤ : Subgroup S) I := by
        rwa [hfix] at hI
      haveI : IsSimpleGroup (alternatingGroup (Fin 9)) :=
        alternatingGroup.isSimpleGroup (by simp)
      haveI : IsSimpleGroup S := MulEquiv.isSimpleGroup e
      have hnc : ∃ a b : S, a * b ≠ b * a := by
        obtain ⟨a, b, hab⟩ := alternatingGroup_fin_nine_nonabelian
        exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
      obtain ⟨g⟩ := rtd_nonempty_pSimple_equiv_top Nat.prime_three hnc hItop
      have hcatS : catalogIs S (S9.isList93 3) := (catalogIs_congr g).mp hcat
      exact (not_isList93_of_alt hb (n := 9) (by norm_num) (by norm_num) e) hcatS
    ·
      have hα' : (MulAut.congr e α) ^ 3 = 1 := by
        rw [← map_pow (MulAut.congr e) α 3, hα, map_one]
      have hα'1 : MulAut.congr e α ≠ 1 := fun h =>
        hα1 ((MulAut.congr e).injective (by rw [h, map_one]))
      have hI' : GLAPComponent 3
          (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.congr e α))
          (I.map e.toMonoidHom) := by
        have h := glaPComponent_map_mulEquiv Nat.prime_three e hI
        rwa [← CFSG.HardMathSupport.Dickson.I271.fixSubgroup_congr e α] at h
      obtain ⟨m, hmax, hsum, ⟨f⟩⟩ := kdAltDown_holds 9 3 (by norm_num) Nat.prime_three
        (by norm_num) (MulAut.congr e α) hα' hα'1 (I.map e.toMonoidHom) hI'
      have hm5 : 5 ≤ m := le_trans (le_max_left 5 3) hmax
      have hm8 : m ≠ 8 := by omega
      have ee : PSimple 3 I ≃* alternatingGroup (Fin m) :=
        (CFSG.HardMathSupport.Dickson.I271.pSimpleEquiv 3 (e.subgroupMap I)).trans f
      exact (not_isList93_of_alt hb (n := m) hm5 hm8 ee) hcat
  ·
    subst hp7
    subst hn7
    exfalso
    rcases hcat with ⟨i, hi, -⟩
    simp [S9.isList93] at hi


end Certificates

end CFSG.LocalAnalysis.GLTheoremA
