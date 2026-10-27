module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SKSympMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SDOrthModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Symp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.SK

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.T263 CFSG.LocalAnalysis.GLTheoremA.T263.SD
  CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

theorem sympRecipe_of_tag {lab : LargeEvenLabel} (h : lab.tag = .B ∨ lab.tag = .C) (Q : LargeEvenRawCont) :
    LargeEvenRawDatum lab Q ↔ LargeEvenRecipeSymplectic lab.rank (2 ^ lab.n) false Q := by
  obtain ⟨tag, rank, n⟩ := lab
  rcases h with h | h <;> (dsimp only at h; subst h; exact Iff.rfl)

theorem sk_catalogIs_l154Symp {T : Type} [Group T] (h : catalogIs T t263GSymp) : catalogIs T K155X.l154Symp :=
  h

theorem sk_inner_of_mem_matConjImage {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {φ : MulAut (StatedProj (StatedSp m K))}
    (hφ : φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m)) :
    ∃ s : StatedSp m K, φ = MulAut.conj (SymplecticFlag.proj m K s) := by
  obtain ⟨A, hA⟩ := Y10GFldSympMark.exists_conjAut_eq_of_mem_matConjImage hφ
  obtain ⟨s, hs⟩ := UnitaryHigher.exists_conjAut_eq_statedSp A
  exact ⟨s, by rw [← hA, hs, SymplecticHigher.conjAut_statedSp]⟩

section Certs


theorem sdFamModel_symp : SDFamModel t263GSymp := by
  intro p hp hp2 Ω _ _ S B B₀ hSn hSq hSp hSc hQ hF2 hBel hB₀B hInn
  obtain ⟨lab, hΛ, hraw⟩ := sd_marking_on_S hSp hInn
  have hlab : Y10F.HasLabel ↥S (fun l : GLALabel => l = lab) :=
    ⟨hSq.1, lab, hΛ, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
      (fun R _ I F ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩
  obtain ⟨r, m, E, instE, instEfin, hr, hE, hne, ⟨e⟩⟩ :=
    K155XSp.l154s_exists_psp (T := ↥S ⧸ Subgroup.center ↥S) (sk_catalogIs_l154Symp hQ)
  have hcanon := Y10GSympLabel.canonLabel_eq_of_quot_statedSp CFSG.StandardType.ggLabelRigidInput_holds hr hE
    hne hlab e
  have hne' : ¬ (r = 2 ∧ m = 1) := fun h => hne ⟨h.1, by rw [hE, h.2, pow_one]⟩
  obtain ⟨htag, hrank, -⟩ := K155XSp.l154s_tag_of_canonLabel hcanon hne'
  obtain ⟨K, instF, instFin, hK, hs, hna, θm, hindb⟩ := (sympRecipe_of_tag htag _).1 hraw
  haveI : CharP K 2 := Y10GField.charP_two_of_card_pow hK
  have hr1 : 1 ≤ lab.rank := by omega
  haveI : NeZero lab.rank := ⟨by omega⟩
  let θm' : ↥S ⧸ Subgroup.center ↥S ≃* StatedProj (StatedSp lab.rank K) := θm
  have hindb' : ∀ b ∈ B₀, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K lab.rank))
      (LargeEvenGSpSet K lab.rank), LargeEvenInduces θm' (fun s s' : ↥S => (s' : Ω) = b * s * b⁻¹) φ := hindb
  have hK3 : p = 3 → 4 ≤ Nat.card K := by
    intro h3
    by_contra hlt
    push Not at hlt
    rw [hK] at hlt
    have hn1 : lab.n = 1 := by
      have h1 : 1 ≤ lab.n := hΛ.1
      by_contra hne1
      have h4 : 2 ^ 2 ≤ 2 ^ lab.n := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact hF2 h3 ⟨hSq.1, lab, hΛ, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
      (fun R _ I F ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, hn1⟩) hraw⟩
  let pe : ↥(StatedSp lab.rank K) ≃* StatedProj (StatedSp lab.rank K) :=
    MulEquiv.ofBijective (SymplecticFlag.proj lab.rank K) UnitaryHigher.proj_bijective_of_charTwo
  let θ : ↥S ⧸ Subgroup.center ↥S ≃* ↥(StatedSp lab.rank K) := θm'.trans pe.symm
  refine ⟨↥(StatedSp lab.rank K), inferInstance, inferInstance, θ,
    fun φ => φ ∈ Set.range (MulAut.conj : ↥(StatedSp lab.rank K) →* MulAut ↥(StatedSp lab.rank K)), ?_,
    famSel_symplectic hr1 hp hp2 hK3⟩
  intro b hb
  obtain ⟨φ, hφI, hφ⟩ := hindb' (b : Ω) hb
  obtain ⟨s, rfl⟩ := sk_inner_of_mem_matConjImage hφI
  rw [Orth.sdo_kd264Rho_congr (sd_hBN hSn B) θ b, Orth.sdo_rho_inner (sd_hBN hSn B) θm' b _ hφ,
    Orth.sdo_congr_conj]
  exact ⟨_, rfl⟩

end Certs

end CFSG.LocalAnalysis.GLTheoremA.T263.SK

end
