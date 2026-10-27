module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I91T5

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace I91T

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.StandardType CFSG.Assembly TauCeti
open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.CatB
open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA.MI
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped commutatorElement


@[expose] def TD4NotL3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsTD4 3 L → ¬ catalogIs (PSimple 3 L) S9.isL3char2

theorem l3_of_td4 (hTD4 : TD4NotL3) (G : Type) [Group G] [Finite G] : ∀ (X L : Subgroup G) (b : G),
    GLAPComponent 3 X L → b ^ 3 = 1 → R2Prop 3 b L →
    GLAPComponent 3 (L ⊓ cx b) (Ipart 3 L b) → Ipart 3 L b ≠ ⊥ →
    catalogIs (PSimple 3 L) S9.isL3char2 → catalogIs (PSimple 3 (Ipart 3 L b)) S9.isL3char2 := by
  intro X L b hL hbp hR hI _ hc
  have hp3 : (3 : ℕ).Prime := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  rcases hR with hF | ⟨-, hTD, -⟩
  ·
    have hb : b ∈ Subgroup.normalizer (L : Set G) := hF.1
    have hap : IsPGroup 3 (Subgroup.zpowers b) := isPGroup_zpowers_of_pow_eq_one hbp
    have hcompT := glaPComponent_chevTransfer hp3 hb hap hI
    have hTC : chevTransfer 3 L (Ipart 3 L b) ≤ FP.fixSub (indAut 3 L b hb) := by
      rw [FR.fixSub_indAut hb]; exact hcompT.1
    have hTperf : ⁅chevTransfer 3 L (Ipart 3 L b), chevTransfer 3 L (Ipart 3 L b)⁆ =
        chevTransfer 3 L (Ipart 3 L b) := glaPComponent_perfect hcompT
    have hTne : chevTransfer 3 L (Ipart 3 L b) ≠ ⊥ := glaPComponent_ne_bot' hcompT
    obtain ⟨lab, hlab, h3, hM, hpn, D, hD, hdat⟩ := FR.fieldOn_subfield hp3 hp2 hF
    obtain ⟨k, hk2, hkE, hX⟩ := lieModel_of_catalogIs_isL3char2 hc
    obtain ⟨ht, hr, hn⟩ := label_of_markedModel_L3 hk2 hM hX
    have h3k : 3 ∣ k := by rw [← hn]; exact hpn
    have hTD : chevTransfer 3 L (Ipart 3 L b) ≤ D :=
      hTperf ▸ (Subgroup.commutator_mono hTC hTC).trans hD.2.1
    have hna : ∃ x y : ↥D, x * y ≠ y * x := FR.exists_noncomm_of_perfect hTD hTperf hTne
    have hperfD : ∀ T : Subgroup (PSimple 3 L), T ≤ FP.fixSub (indAut 3 L b hb) → ⁅T, T⁆ = T → T ≤ D :=
      fun T hTC' hTp => hTp ▸ (Subgroup.commutator_mono hTC' hTC').trans hD.2.1
    have hdat' : CFSG.Assembly.LargeEvenRawDatum ⟨.A, 2, k / 3⟩ (fun R' _ _ _ => Nonempty (↥D ≃* R')) := by
      rcases hdat with h | h
      · have hl : (⟨lab.tag, lab.rank, lab.n / 3⟩ : LargeEvenLabel) = ⟨.A, 2, k / 3⟩ := by
          rw [ht, hr, hn]
        rw [← hl]
        exact h
      · exfalso
        rcases h with ⟨h1, -, -⟩ | ⟨h1, -⟩ <;> rw [ht] at h1 <;> cases h1
    have hΛ : LargeEvenInLambda2 (⟨.A, 2, k / 3⟩ : LargeEvenLabel) := by
      have hk3 : 1 ≤ k / 3 := by omega
      unfold LargeEvenInLambda2
      exact ⟨hk3, by norm_num, fun h => by norm_num at h⟩
    obtain ⟨hDs, hMD⟩ := simple_of_datum hΛ (by intro h; cases h) hna hdat'
    have hMD' : CFSG.Blueprint.LieModel D .PSL 3 2 (k / 3) := hMD
    have hEvj : Even (k / 3) := by
      have hk2' : k % 2 = 0 := Nat.even_iff.1 hkE
      exact Nat.even_iff.2 (by omega)
    have hk3 : 2 ≤ k / 3 := by
      have := Nat.even_iff.1 hEvj
      omega
    have hcD : catalogIs D S9.isL3char2 := catalogIs_isL3char2_of_lieModel hk3 hEvj hMD'
    obtain ⟨e⟩ := pSimple_component_equiv hp3 hb hbp hDs hD.1 hna hperfD hI
    exact (catalogIs_congr e.symm).mp hcD
  · exact (hTD4 G L hTD hc).elim

end I91T

end CFSG.LocalAnalysis.GLTheoremA
