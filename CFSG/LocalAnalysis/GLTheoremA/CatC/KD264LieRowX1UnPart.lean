module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1UnStruct
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1UnGood
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1Parts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowX1Un

open CFSG.ComponentClassification.Burgoyne.U
open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowXUn
open CFSG.Yardstones.Md0ec50421ce4

theorem kd264X1Concl_twistedA (n : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA n q).Valid) (hq : q.card = 2) (hN7 : 7 ≤ n + 1)
    (h3 : ¬ 3 ∣ n + 1) [Finite (TauCeti.CFSGIndex.lie ⟨.twistedA n q, hv⟩).Group] :
    KD264X1Concl ⟨.twistedA n q, hv⟩ := by
  unfold KD264X1Concl
  intro A hA hrk
  obtain ⟨e0⟩ := nonempty_mulEquiv_xunM n q hv hq
  have hSrank : CFSG.Open.pRank 3
      (⊤ : Subgroup (TauCeti.CFSGIndex.lie ⟨.twistedA n q, hv⟩).Group) =
      CFSG.Open.pRank 3 (⊤ : Subgroup (xunM (n + 1))) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e0
  have hNr : n + 1 - 1 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (xunM (n + 1))) :=
    pRank_xunM_ge (by omega) h3
  set A' : Subgroup (MulAut (xunM (n + 1))) := A.map (MulAut.congr e0).toMonoidHom with hA'def
  have hA'el : IsElemAbelian 3 A' :=
    isElemAbelian_map_of_injective (MulAut.congr e0).injective hA
  have hrank' : CFSG.Open.pRank 3 A' = CFSG.Open.pRank 3 A :=
    pRank_map_of_injective Nat.prime_three (MulAut.congr e0).injective hA
  have hrankA' : n + 1 - 1 ≤ CFSG.Open.pRank 3 A' := by
    rw [hrank']
    exact le_trans hNr ((le_of_eq hSrank.symm).trans hrk)
  obtain ⟨c, hc⟩ := kd264X1UnTorusStruct7 hN7 A' hA'el hrankA'
  set γ : MulAut (xunM (n + 1)) := xunConj (n + 1) (by omega) c with hγ
  set A'' : Subgroup (MulAut (xunM (n + 1))) := A'.map (MulAut.congr γ).toMonoidHom with hA''def
  have hA''el : IsElemAbelian 3 A'' :=
    isElemAbelian_map_of_injective (MulAut.congr γ).injective hA'el
  have hrank'' : CFSG.Open.pRank 3 A'' = CFSG.Open.pRank 3 A' :=
    pRank_map_of_injective Nat.prime_three (MulAut.congr γ).injective hA'el
  have hdiag : ∀ g : uU xunH (n + 1), xunConj (n + 1) (by omega) g ∈ A'' →
      IsDiagU (n + 1) (g : GL (Fin (n + 1)) xunK) := by
    intro g hg
    rw [hA''def, mem_map_mulAut_congr] at hg
    have hg' : xunConj (n + 1) (by omega) (c⁻¹ * g * c) ∈ A' := by
      have heq : xunConj (n + 1) (by omega) (c⁻¹ * g * c) =
          MulAut.congr γ.symm (xunConj (n + 1) (by omega) g) := by
        rw [mulAut_congr_eq_conj, map_mul, map_mul, map_inv, hγ]
        rfl
      rw [heq]
      exact hg
    have := hc (c⁻¹ * g * c) hg'
    have hcg : c * (c⁻¹ * g * c) * c⁻¹ = g := by group
    rw [hcg] at this
    exact this
  obtain ⟨F'', hF''A'', hF''el, hF''rank, hF''good⟩ :=
    kd264X1UnTorusGood7 hN7 A'' hA''el (by rw [hrank'']; exact hrankA') hdiag
  have hF'A' : F''.map (MulAut.congr γ.symm).toMonoidHom ≤ A' := by
    intro x hx
    rw [mem_map_mulAut_congr] at hx
    have hx' := hF''A'' hx
    rw [hA''def, mem_map_mulAut_congr, mulAut_congr_congr_symm] at hx'
    exact hx'
  have hF'el : IsElemAbelian 3 (F''.map (MulAut.congr γ.symm).toMonoidHom) :=
    isElemAbelian_map_of_injective (MulAut.congr γ.symm).injective hF''el
  have hF'rank : CFSG.Open.pRank 3 (F''.map (MulAut.congr γ.symm).toMonoidHom) =
      CFSG.Open.pRank 3 F'' :=
    pRank_map_of_injective Nat.prime_three (MulAut.congr γ.symm).injective hF''el
  have hF'good : IsGood 3 (F''.map (MulAut.congr γ.symm).toMonoidHom) :=
    (isGood_iff_map_mulEquiv γ.symm F'').1 hF''good
  have hFA : (F''.map (MulAut.congr γ.symm).toMonoidHom).map
      (MulAut.congr e0.symm).toMonoidHom ≤ A := by
    intro x hx
    rw [mem_map_mulAut_congr] at hx
    have hx' := hF'A' hx
    rw [hA'def, mem_map_mulAut_congr, mulAut_congr_congr_symm] at hx'
    exact hx'
  have hFel : IsElemAbelian 3 ((F''.map (MulAut.congr γ.symm).toMonoidHom).map
      (MulAut.congr e0.symm).toMonoidHom) :=
    isElemAbelian_map_of_injective (MulAut.congr e0.symm).injective hF'el
  have hFrank : CFSG.Open.pRank 3 ((F''.map (MulAut.congr γ.symm).toMonoidHom).map
      (MulAut.congr e0.symm).toMonoidHom) = CFSG.Open.pRank 3 F'' := by
    rw [pRank_map_of_injective Nat.prime_three (MulAut.congr e0.symm).injective hF'el, hF'rank]
  refine ⟨(F''.map (MulAut.congr γ.symm).toMonoidHom).map (MulAut.congr e0.symm).toMonoidHom,
    hFA, hFel, ?_, ?_⟩
  · refine (min_le_left _ _).trans ?_
    rw [hFrank]
    exact hF''rank
  · exact (isGood_iff_map_mulEquiv e0.symm _).1 hF'good

theorem kd264X1UnPart_holds : KD264X1UnPart := by
  unfold KD264X1UnPart
  intro d n q hd inst
  obtain ⟨idx, hv⟩ := d
  have hd' : idx = .twistedA n q := hd
  subst hd'
  unfold KD264X1At
  intro hChev hk2 _ hov hnot3 _
  have hq : q.card = 2 := by simpa [ov2Idx, fieldSize] using hov
  have hq' : q.p ^ q.exponent = 2 := by
    rw [← TauCeti.PrimePower.card_def]
    exact hq
  have h3 : ¬ 3 ∣ n + 1 := fun h => hnot3 ⟨n, q, rfl, h⟩
  have hn2 : 2 ≤ n :=
    TauCeti.LieTypeIndex.two_le_of_twistedA_inStandardRange
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hn3 : n ≠ 3 := by
    rintro rfl
    apply hChev
    unfold IsChevSimple catalogIs
    refine Or.inr ⟨TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩, ?_, ⟨MulEquiv.refl _⟩⟩
    simp [ambiguousChev, hq']
  have hn4 : n ≠ 4 := by
    rintro rfl
    exact hk2 (by simp [k2Lie, hq'])
  have hN7 : 7 ≤ n + 1 := by omega
  exact kd264X1Concl_twistedA n q hv hq hN7 h3

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowX1Un

end
