module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxDefs
import CFSG.GH74.Bender
import CFSG.GH74.Uniqueness.Bender.Lemma32
import CFSG.GH74.Uniqueness.Bender.OddCentralizer

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open Subgroup CFSG.GH74.Uniqueness

theorem kFact2715_holds : KFact2715 := by
  intro A _ _ K T z r hK hT hzK hzT hzr hr hr2 J hJz hJT
  obtain ⟨n, i, e, hBT⟩ := Bender.isBenderGroup_iff_exists_benderType.mp
    (CFSG.GH74.isBenderGroup_of_fusionIsBenderGroup hK)
  obtain ⟨Q, hQ⟩ := hT.exists_sylow_eq_subgroupOf
  obtain ⟨t, hcore⟩ := hBT.exists_benderCore Q
  have hzK' : zpowers z ≤ K := Subgroup.zpowers_le.mpr hzK
  let A' : Subgroup ↥K := (zpowers z).subgroupOf K
  have hA'card : Nat.card A' = r := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzK').toEquiv, Nat.card_zpowers, hzr]
  have hodd : Odd (Nat.card A') := by
    rw [hA'card]
    exact hr.odd_of_ne_two hr2
  have hNQ : Bender.borel (Q : Subgroup ↥K) = (normalizer (T : Set A)).subgroupOf K := by
    unfold Bender.borel
    rw [hQ]
    exact (Subgroup.subgroupOf_normalizer_eq hT.le).symm
  have hA'M : A' ≤ Bender.borel (Q : Subgroup ↥K) := by
    intro a ha
    rw [hNQ]
    exact (Subgroup.zpowers_le.mpr hzT) ha
  obtain ⟨q', hq'Q, hq'⟩ := hcore.exists_conj_cartan_of_odd Q.isPGroup' hA'M hodd
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right hcore.sq_eq_one
  let B1 : Subgroup ↥K := A'.map (MulAut.conj q').toMonoidHom
  let B2 : Subgroup ↥K := B1.map (MulAut.conj t).toMonoidHom
  have hB1D : B1 ≤ Bender.cartan (Q : Subgroup ↥K) t := by
    rintro _ ⟨a, ha, rfl⟩
    simpa [MulAut.conj_apply] using hq' a ha
  have hB2D : B2 ≤ Bender.cartan (Q : Subgroup ↥K) t := by
    rintro _ ⟨b, hb, rfl⟩
    have hb' := hB1D hb
    have := hcore.cartan_mul_mul hb'
    simpa [MulAut.conj_apply, hti] using this
  have hB12 : Nat.card B2 = Nat.card B1 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj t).injective]
  have hB21 : B2 = B1 := Bender.eq_of_card_eq_of_cyclic hcore.isCyclic hB2D hB1D hB12
  let g : ↥K := q'⁻¹ * t * q'
  have hgg : g * g = 1 := by
    have := hcore.sq_eq_one
    calc g * g = q'⁻¹ * (t * t) * q' := by simp only [g]; group
      _ = 1 := by rw [this]; group
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hgg
  have hgA : ∀ a ∈ A', g * a * g⁻¹ ∈ A' := by
    intro a ha
    have h1 : t * (q' * a * q'⁻¹) * t⁻¹ ∈ B2 := ⟨_, ⟨a, ha, rfl⟩, by simp [MulAut.conj_apply]⟩
    rw [hB21] at h1
    obtain ⟨a', ha', hae⟩ := h1
    have h2 : g * a * g⁻¹ = a' := by
      have : (MulAut.conj q') a' = t * (q' * a * q'⁻¹) * t⁻¹ := hae
      simp only [MulAut.conj_apply] at this
      calc g * a * g⁻¹ = q'⁻¹ * (t * (q' * a * q'⁻¹) * t⁻¹) * q' := by simp only [g]; group
        _ = q'⁻¹ * (q' * a' * q'⁻¹) * q' := by rw [this]
        _ = a' := by group
    rw [h2]
    exact ha'
  have hgN : g ∈ normalizer (A' : Set ↥K) := by
    refine Subgroup.mem_normalizer_iff.mpr fun h => ⟨fun hh => hgA h hh, fun hh => ?_⟩
    have := hgA _ hh
    have h3 : g * (g * h * g⁻¹) * g⁻¹ = h := by
      rw [hginv]
      calc g * (g * h * g) * g = (g * g) * h * (g * g) := by group
        _ = h := by rw [hgg]; group
    rwa [h3] at this
  have hgNA : (g : A) ∈ normalizer ((zpowers z : Subgroup A) : Set A) := by
    have h4 : g ∈ (normalizer ((zpowers z : Subgroup A) : Set A)).subgroupOf K := by
      rw [Subgroup.subgroupOf_normalizer_eq hzK']
      exact hgN
    exact h4
  have hgJ : (g : A) ∈ J := hJz ⟨hgNA, g.2⟩
  by_contra hKJ
  have hQJ : (Q : Subgroup ↥K) ≤ J.subgroupOf K := by
    rw [hQ]
    intro x hx
    exact hJT hx
  have hJne : J.subgroupOf K ≠ ⊤ := fun h => hKJ (Subgroup.subgroupOf_eq_top.mp h)
  have hle := hBT.le_borel_of_sylow_le Q hQJ hJne
  have hgM : g ∈ Bender.borel (Q : Subgroup ↥K) := hle hgJ
  have hqM : q' ∈ Bender.borel (Q : Subgroup ↥K) := Bender.le_borel _ hq'Q
  have htM : t ∈ Bender.borel (Q : Subgroup ↥K) := by
    have h5 : t = q' * g * q'⁻¹ := by simp only [g]; group
    rw [h5]
    exact (Bender.borel _).mul_mem ((Bender.borel _).mul_mem hqM hgM)
      ((Bender.borel _).inv_mem hqM)
  exact hcore.not_mem htM

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
