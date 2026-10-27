module

public import CFSG.Quasithin.Background.A1bBasic

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin Subgroup

theorem exists_injective_map_eq_of_isSylowIn {Q Y : Type} [Group Q] [Finite Q] [Group Y] [Finite Y]
    {p : ℕ} [Fact p.Prime] {G T₀ : Subgroup Y} (hT₀ : IsSylowIn p T₀ G)
    (f : Q →* Y) (hf : Function.Injective f) (hran : f.range = G) {T : Subgroup Q}
    (hT : IsSylowIn p T ⊤) :
    ∃ f' : Q →* Y, Function.Injective f' ∧ f'.range = G ∧ T.map f' = T₀ := by
  have hpre : IsSylowIn p (T₀.comap f) ⊤ := by
    refine isSylowIn_of_card_eq le_top ?_
    have h1 : Nat.card (T₀.comap f) = Nat.card T₀ := by
      rw [← Subgroup.card_map_of_injective hf, Subgroup.map_comap_eq_self (hran ▸ hT₀.le)]
    have h2 : Nat.card (⊤ : Subgroup Q) = Nat.card G := by
      rw [Subgroup.card_top]
      calc Nat.card Q = Nat.card ↥f.range := Nat.card_congr (MonoidHom.ofInjective hf).toEquiv
        _ = Nat.card G := by rw [hran]
    rw [h1, h2]
    exact hT₀.card_eq
  have hT' : ¬ p ∣ T.index := by
    rw [← relIndex_top_right]
    exact hT.not_dvd_relIndex
  have hpre' : ¬ p ∣ (T₀.comap f).index := by
    rw [← relIndex_top_right]
    exact hpre.not_dvd_relIndex
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Q (hpre.isPGroup.toSylow hpre')
    (hT.isPGroup.toSylow hT')
  have hconj : T = (T₀.comap f).map (MulAut.conj g).toMonoidHom := by
    have h1 : ((g • hpre.isPGroup.toSylow hpre' : Sylow p Q) : Subgroup Q) = T := by
      rw [hg, IsPGroup.toSylow_coe]
    rw [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at h1
    ext x
    rw [← h1, mem_smul_pointwise_iff_exists, mem_map]
    simp [MulAut.smul_def]
  set f' : Q →* Y := f.comp (MulAut.conj g⁻¹).toMonoidHom with hf'def
  have hf' : Function.Injective f' := hf.comp (MulAut.conj g⁻¹).injective
  have hran' : f'.range = G := by
    rw [← hran]
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨x, rfl⟩
      refine ⟨g * x * g⁻¹, ?_⟩
      simp only [hf'def, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      congr 1
      group
  have hmap : T.map f' = T₀ := by
    rw [hf'def, hconj, Subgroup.map_map]
    have hcomp : (f.comp (MulAut.conj g⁻¹).toMonoidHom).comp
        (MulAut.conj g).toMonoidHom = f := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      congr 1
      group
    rw [hcomp]
    exact Subgroup.map_comap_eq_self (hran ▸ hT₀.le)
  exact ⟨f', hf', hran', hmap⟩

end CFSG.GroupTheory
