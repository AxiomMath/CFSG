module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointExoticSigBase
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4TI
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.OutTrivial
public import CFSG.Sporadic.Bridge.J4Surj
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointExoticDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
  CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient CFSG.ComponentClassification.OuterAutomorphisms

theorem signalizerAutAt_jFour
    {p : ℕ} (hp : p = 11) : SignalizerAutAt p (.sporadic .J4) := by
  subst hp
  intro K _ _ hK B Y hB hBc hY hBY _
  obtain ⟨e⟩ := hK
  have eKJ : K ≃* J :=
    e.trans ((CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv.some).symm.trans
      (seedEquiv j4Facts.mat))
  have hfinJ : Finite J := Finite.of_equiv K eKJ.toEquiv
  have hout1 : Nat.card (Outer K) = 1 := by
    have h := @card_outer_congr K J _ (Subgroup.toGroup J) eKJ
    rw [h]
    exact card_outer_J_eq_one
  have hinner : inner K = ⊤ := by
    have h1 : (inner K).index = 1 := hout1
    exact Subgroup.index_eq_one.1 h1
  have hsurj : Function.Surjective (MulAut.conj : K →* MulAut K) := by
    intro φ
    have hφ : φ ∈ inner K := by rw [hinner]; exact Subgroup.mem_top _
    exact hφ
  have hinj : Function.Injective (MulAut.conj : K →* MulAut K) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hz : eKJ a ∈ Subgroup.center J := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨g, rfl⟩ := eKJ.surjective y
      have hag : a * g * a⁻¹ = g := by
        simpa using congrArg (fun φ : MulAut K => φ g) ha
      rw [← map_mul, ← map_mul]
      congr 1
      calc g * a = (a * g * a⁻¹) * a := by rw [hag]
        _ = a * g := by group
    rw [center_J] at hz
    exact eKJ.injective (by simpa using Subgroup.mem_bot.1 hz)
  let ι : J ≃* MulAut K :=
    eKJ.symm.trans (MulEquiv.ofBijective (MulAut.conj : K →* MulAut K) ⟨hinj, hsurj⟩)
  have hY' : ¬ 11 ∣ Nat.card Y := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).1 hY
  have hR : Nat.card (Q11 : Subgroup J) = 11 ^ (Nat.card J).factorization 11 := card_Q11_sylow
  have hTI : WeakTI (Q11 : Subgroup J) := weakTI_of_inf_eq_bot fun g hg => TI_Q11 g hg
  have hp11 : Nat.Prime 11 := by norm_num
  exact @centralizes_of_equiv_weakTI (MulAut K) J _ (Subgroup.toGroup J) hfinJ 11 hp11 ι _ hR hTI
    B Y hB hBc hY' hBY

end CFSG.LocalAnalysis.RankFourTheoremC
