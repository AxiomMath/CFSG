module

public import CFSG.LocalAnalysis.EvenBN.U5.LinModelDefs
public import CFSG.LocalAnalysis.EvenBN.LinearThree.ModelAut
public import CFSG.LocalAnalysis.EvenBN.U5.ModelThreeTwo
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag

namespace LinCase

theorem l3fix_congr_conj {X P : Type} [Group X] [Group P] (e : X ≃* P) (x : X) :
    MulAut.congr e (MulAut.conj x) = MulAut.conj (e x) := by
  ext y
  simp [MulAut.conj_apply]

theorem l3fix_congr_apply {X P : Type} [Group X] [Group P] (e : X ≃* P) (σ : MulAut X)
    (x : X) : (MulAut.congr e σ) (e x) = e (σ x) := by
  simp [MulAut.congr_apply]

theorem l3fix_range_map {X P : Type} [Group X] [Group P] (e : X ≃* P) :
    (MulAut.conj : X →* MulAut X).range.map (MulAut.congr e).toMonoidHom =
      (MulAut.conj : P →* MulAut P).range := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨e x, (l3fix_congr_conj e x).symm⟩
  · rintro ⟨p, rfl⟩
    refine ⟨MulAut.conj (e.symm p), ⟨e.symm p, rfl⟩, ?_⟩
    show MulAut.congr e (MulAut.conj (e.symm p)) = MulAut.conj p
    rw [l3fix_congr_conj, e.apply_symm_apply]

theorem l3fix_inf_card {X P : Type} [Group X] [Group P] (e : X ≃* P)
    (𝒜 : Subgroup (MulAut X)) :
    Nat.card ↥(𝒜.map (MulAut.congr e).toMonoidHom ⊓ (MulAut.conj : P →* MulAut P).range :
      Subgroup (MulAut P)) =
    Nat.card ↥(𝒜 ⊓ (MulAut.conj : X →* MulAut X).range : Subgroup (MulAut X)) := by
  have hinj : Function.Injective (MulAut.congr e).toMonoidHom := (MulAut.congr e).injective
  rw [← l3fix_range_map e, ← Subgroup.map_inf_eq _ _ _ hinj, Subgroup.card_map_of_injective hinj]

theorem l3Fixed : L3FixedStatement := by
  intro f hf X _ hX
  obtain ⟨K', _, _, _, hK', ⟨e⟩⟩ := exists_mulEquiv_projectiveSL_three_sq hf hX
  have hK2 : Nat.card K' = 2 ^ (2 * f) := by rw [hK', ← pow_mul, mul_comm]
  have hf2 : 1 ≤ 2 * f := by omega
  have hinj : Function.Injective (MulAut.congr e).toMonoidHom := (MulAut.congr e).injective
  refine ⟨fun 𝒜 h𝒜 => ?_, fun σ hσ Z hZ hfix => ?_⟩
  ·
    have hE : CFSG.IsElementaryAbelian 2 (𝒜.map (MulAut.congr e).toMonoidHom) :=
      h𝒜.subgroup_map _
    have h1 := CFSG.LocalAnalysis.EvenBN.LinearThree.card_le_four_mul_card_inf_range hf2 hK2
      (CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr hE)
    rwa [Subgroup.card_map_of_injective hinj, l3fix_inf_card e 𝒜] at h1
  ·
    have hσ' : (MulAut.congr e σ) ∉
        (MulAut.conj : projectiveSL 3 K' →* MulAut (projectiveSL 3 K')).range := by
      rw [← l3fix_range_map e]
      intro h
      obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.1 h
      have haσ : a = σ := hinj hae
      subst haσ
      exact hσ ha
    have hZ' : CFSG.IsElementaryAbelian 2 (Z.map e.toMonoidHom) := hZ.subgroup_map _
    have hfix' : ∀ z ∈ Z.map e.toMonoidHom, (MulAut.congr e σ) z = z := by
      rintro _ ⟨x, hx, rfl⟩
      show (MulAut.congr e σ) (e x) = e x
      rw [l3fix_congr_apply, hfix x hx]
    have h1 := CFSG.LocalAnalysis.EvenBN.LinearThree.card_le_of_forall_fix hf2 hK2
      (CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr hZ') hfix' hσ'
    rw [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective] at h1
    rwa [hK'] at h1

end LinCase

end CFSG.LocalAnalysis.EvenBN.U5
