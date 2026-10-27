module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167CCover
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167CLinNum
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167CLinData
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167CLinBlock
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167CLinS
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167CLinR1M
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167CLinMisc
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167CLinJ
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167FieldDict

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Open.StatedAPI CFSG.Assembly CFSG.Yardstones.Md0ec50421ce4 Matrix

private theorem i167CLin_pkill {G : Type} [Group G] {p : ℕ} {J : Subgroup G} {b e : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2)
    (hjr : (p = 3 ∧ e = 1 ∧ ∃ n : ℕ, Odd n ∧ 5 ≤ n ∧ b = n ∧ catalogIs (PSimple 3 J) (isLnA n 2)) ∨
      (∃ k : ℕ, 2 ≤ k ∧ p ∣ 2 ^ k + 1 ∧ e = k ∧ b = 4 ∧ catalogIs (PSimple p J) (isOmPA 3 (2 ^ k))))
    (hP : p ∣ 2 ^ e - 1) : False := by
  rcases hjr with ⟨-, rfl, -⟩ | ⟨k, -, hk, rfl, -, -⟩
  · norm_num at hP
    exact hp.ne_one hP
  · exact (i167CLin_num_pdvd hp hp2 hP dvd_rfl).2 hk

private theorem i167CLin_catalog_A {S : Type} [Group S] (hS : IsSimpleGroup S) {K : Type} [Field K] [Finite K]
    {d a : ℕ} (hd : 5 ≤ d) (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ a) (e : S ≃* LargeEvenProj (StatedSL d K)) :
    catalogIs S (isLnA d (2 ^ a)) := by
  have hSC : StatedClassicalModel S .PSL d 2 a :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.statedClassicalModel_psl_of_isSimpleGroup (by omega) hK e
  exact fld_catalogIs_isLnA_of_lieModel ⟨ha, Or.inl ⟨rfl, Or.inl hd⟩⟩
    (Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], hSC⟩)

private theorem i167CLin_T3 {p a : ℕ} {labK : GLALabel} (hp : p.Prime) (hp2 : p ≠ 2) (hFam : Y10GField.FamLin labK)
    (hHS : HalfSplitLab p labK) (ha : (canonLabel labK).n = a) (h2a : 2 ≤ a) (hpa : p ∣ 2 ^ a + 1)
    (hlt : 4 < (canonLabel labK).rank + 1) : (canonLabel labK).rank = 5 ∧ a = 2 ∧ p = 5 := by
  rcases i167CLin_halfSplit_cases hFam hHS with h | ⟨h1, -⟩ | ⟨h5, h2, h3⟩ | ⟨-, h1, -⟩ | ⟨h3, -⟩
  · rw [ha] at h
    exact absurd hpa (i167CLin_num_pdvd hp hp2 h dvd_rfl).2
  · omega
  · exact ⟨h5, ha ▸ h2, h3⟩
  · omega
  · omega

private theorem i167CLin_T1 {S : Type} [Group S] {Bb : Subgroup (MulAut S)} {α : MulAut S} {J : Subgroup S}
    (hcen : Subgroup.center S = ⊥) (hSs : IsSimpleGroup S) (hBb : IsElemAbelian 3 Bb) (hαB : α ∈ Bb)
    (hSc : PFreeCover 3 S → ScpS 3 S Bb) (hCJ : CentJ Bb α J) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {d : ℕ} (e : S ≃* LargeEvenProj (StatedSL d K)) (g : GL (Fin d) K) (hg3 : g ^ 3 = 1)
    (hg1 : g ≠ 1)
    (hgr : ∀ h h' : ↥(StatedSL d K), (h' : GL (Fin d) K) = g * (h : GL (Fin d) K) * g⁻¹ →
      MulAut.congr e α (LargeEvenProjMk (StatedSL d K) h) = LargeEvenProjMk (StatedSL d K) h')
    (M : Subgroup (GL (Fin d) K))
    (hM : CFSG.Open.IsComponentOf M (Subgroup.centralizer ({g} : Set (GL (Fin d) K)) ⊓ StatedSL d K))
    (hMtriv : ∀ m ∈ M, ∀ v ∈ LinearMap.range (Matrix.toLin' ((g : Matrix (Fin d) (Fin d) K) - 1)),
      (m : Matrix (Fin d) (Fin d) K) *ᵥ v = v)
    (hJM : ∀ x ∈ J, ∃ m ∈ M, ∃ hm : m ∈ StatedSL d K, e x = LargeEvenProjMk (StatedSL d K) ⟨m, hm⟩)
    {n : ℕ} (hn5 : 5 ≤ n)
    (hb : n = Module.finrank K (LinearMap.ker (Matrix.toLin' ((g : Matrix (Fin d) (Fin d) K) - 1)))) :
    catalogIs S (isLnA (n + 2) 2) := by
  have hlt := i167CLin_fixed_lt hg1
  have hd5 : 5 ≤ d := by omega
  have hcat : catalogIs S (isLnA d 2) := by
    simpa using i167CLin_catalog_A hSs hd5 (a := 1) le_rfl (by simpa using hK) e
  obtain ⟨Ã, hÃ, hgÃ, hmax, hCA⟩ := i167CLin_scp_matrix hcen hBb hαB
    (hSc (pFreeCover_of_isLnA_two Nat.prime_three (by norm_num) hd5 hcat)) hCJ hK (by omega) e g hg3 hgr M
    (fun m hm => (hM.1 hm).1) hMtriv hJM
  have hdn := i167CLin_r_one hK Ã hÃ hmax hgÃ hg3 hg1 hCA
  have hd : d = n + 2 := by omega
  rw [← hd]
  exact hcat

set_option linter.unusedSectionVars false


theorem i167CLin_holds : I167CLin := by
  intro S _ _ p Bb α J labK hp hp2 hFam hcen hBb hαB hαord hin hSc hCJ hHS hJc hJt
  have hα1 : α ≠ 1 := fun h => by
    rw [h, orderOf_one] at hαord
    exact hp.one_lt.ne hαord
  have hαpow : α ^ p = 1 := by rw [← hαord]; exact pow_orderOf_eq_one α
  obtain ⟨d, K, _, _, A, e, hd, hd2, h2, hKa, hgrA, hAns, hSs⟩ := i167CLin_data hcen hFam hα1 hin
  by_cases hpK : p ∣ Nat.card K - 1
  · have hpK' : p ∣ 2 ^ (canonLabel labK).n - 1 := by rwa [hKa] at hpK
    obtain ⟨M, hM, hord, hPS, -⟩ := i167CLin_lift h2 (by omega) A e hp hp2 hgrA hαpow hJc
    obtain ⟨b, f, hmod, haf⟩ := i167CLin_split_model hKa h2 A hord M hM
    exact (i167CLin_pkill hp hp2 (i167CLin_jrigid hJt hM.2.2 hPS hmod)
      (i167CLin_num_pdvd hp hp2 hpK' haf).1).elim
  obtain ⟨g, hgp, hgr, hgns⟩ := i167CLin_normalize h2 (by omega) hp hp2 hpK A (MulAut.congr e α) hgrA
    (by rw [← map_pow, hαpow, map_one]) hAns
  obtain ⟨M, hM, -, hPS, hJM⟩ := i167CLin_lift h2 (by omega) g e hp hp2 hgr hαpow hJc
  obtain ⟨b, f, hmod, hdi⟩ := i167CLin_block_dichotomy hKa h2 hp hp2 g hgp M hM
  have hjr := i167CLin_jrigid hJt hM.2.2 hPS hmod
  rcases hdi with hP | ⟨hfa, hb, hMtriv⟩
  · exact (i167CLin_pkill hp hp2 hjr hP).elim
  have hg1 : g ≠ 1 := fun h => hgns 1 (by simp [h])
  have hlt := i167CLin_fixed_lt hg1
  rcases hjr with ⟨hp3, hf1, n, hodd, hn5, hbn, hcat⟩ | ⟨k, hk2, hpk, hfk, hb4, hcat⟩
  · subst hp3
    have hK2 : Nat.card K = 2 := by rw [hKa, ← hfa, hf1]; norm_num
    exact Or.inl ⟨rfl, n, hodd, hcat, Or.inl (i167CLin_T1 hcen hSs hBb hαB hSc hCJ hK2 e g hgp hg1 hgr M hM
      hMtriv hJM hn5 (hbn ▸ hb))⟩
  · have hka : (canonLabel labK).n = k := hfa.symm.trans hfk
    obtain ⟨hr5, hk2', hp5⟩ := i167CLin_T3 hp hp2 hFam hHS hka hk2 hpk (by omega)
    subst hp5 hk2'
    have hd6 : d = 6 := by omega
    have hS6 : catalogIs S (isLnA 6 (2 ^ 2)) := by
      have := i167CLin_catalog_A hSs (by omega : 5 ≤ d) (a := 2) (by norm_num) (by rw [hKa, hka]) e
      rwa [hd6] at this
    exact Or.inr (Or.inr ⟨3, 2, by decide, by norm_num, hpk, hcat, Or.inr (Or.inr ⟨rfl, rfl, rfl, hS6⟩)⟩)

end CFSG.LocalAnalysis.GLTheoremA.I167

end
