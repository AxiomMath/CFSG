module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClBar
public import CFSG.LieType.CurtisTits.Conclusion

public section

namespace CFSG.ComponentClassification.GSThmB.QPUCl

open CFSG Subgroup

variable {P P' : Type} [Group P] [Group P']

theorem isPComponent_map_subgroupOf (φ : P ≃* P') {H L : Subgroup P} (hLH : L ≤ H)
    (hL : IsPComponent 2 (L.subgroupOf H)) :
    IsPComponent 2 ((L.map φ.toMonoidHom).subgroupOf (H.map φ.toMonoidHom)) := by
  have h := LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 (φ.subgroupMap H) hL
  have hmap : (L.subgroupOf H).map (φ.subgroupMap H).toMonoidHom =
      (L.map φ.toMonoidHom).subgroupOf (H.map φ.toMonoidHom) := by
    ext ⟨y, hy⟩
    simp only [mem_subgroupOf, mem_map]
    constructor
    · rintro ⟨⟨x, hxH⟩, hx, hxy⟩
      exact ⟨x, hx, congrArg Subtype.val hxy⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hLH hx⟩, hx, rfl⟩
  rw [hmap] at h
  exact h

theorem fixedBy_map_congr (φ : P ≃* P') (E : Subgroup (MulAut P)) :
    fixedBy (E.map (MulAut.congr φ).toMonoidHom) = (fixedBy E).map φ.toMonoidHom := by
  ext y
  rw [mem_fixedBy, mem_map]
  constructor
  · intro h
    refine ⟨φ.symm y, fun ε hε => ?_, φ.apply_symm_apply y⟩
    have := h _ ⟨ε, hε, rfl⟩
    change φ (ε (φ.symm y)) = y at this
    apply φ.injective
    rw [this, φ.apply_symm_apply]
  · rintro ⟨x, hx, rfl⟩ _ ⟨ε, hε, rfl⟩
    change φ (ε (φ.symm (φ x))) = φ x
    rw [φ.symm_apply_apply, hx ε hε]

theorem centralizer_map_equiv (φ : P ≃* P') (t : P) :
    centralizer {φ t} = (centralizer {t}).map φ.toMonoidHom := by
  ext y
  rw [mem_centralizer_singleton_iff, mem_map]
  constructor
  · intro h
    refine ⟨φ.symm y, ?_, φ.apply_symm_apply y⟩
    rw [mem_centralizer_singleton_iff]
    apply φ.injective
    rw [map_mul, map_mul, φ.apply_symm_apply, h]
  · rintro ⟨x, hx, rfl⟩
    rw [mem_centralizer_singleton_iff] at hx
    change φ x * φ t = φ t * φ x
    rw [← map_mul, ← map_mul, hx]

theorem lieModel_map_equiv (φ : P ≃* P') {L : Subgroup P} {τ : Assembly.LowTwoRank.StatedLieTag}
    {n p f : ℕ} (h : Blueprint.LieModel (↥L ⧸ pPrimeCore 2 ↥L) τ n p f) :
    Blueprint.LieModel (↥(L.map φ.toMonoidHom) ⧸ pPrimeCore 2 ↥(L.map φ.toMonoidHom)) τ n p f :=
  LieType.CurtisTits.lieModel_of_mulEquiv
    (QuotientGroup.congr _ _ (L.equivMapOfInjective φ.toMonoidHom φ.injective)
      (pPrimeCore_map_iso 2 _)) h

theorem BarConfig.of_mulEquiv (φ : P ≃* P') {p' f' p f : ℕ} (h : BarConfig P p' f' p f) :
    BarConfig P' p' f' p f := by
  obtain ⟨E, L, t, J, J₀, hE, hLE, hLc, hLtop, hLm, htL, ht2, ht1, hJt, hJc, hJm, hJ₀L, hJ₀J,
    hJ₀⟩ := h
  have hfix := fixedBy_map_congr φ E
  have hcent := centralizer_map_equiv φ t
  refine ⟨E.map (MulAut.congr φ).toMonoidHom, L.map φ.toMonoidHom, φ t, J.map φ.toMonoidHom,
    J₀.map φ.toMonoidHom, hE.map _, ?_, ?_, ?_, lieModel_map_equiv φ hLm, ⟨t, htL, rfl⟩,
    by rw [← map_mul, ht2, map_one], fun h1 => ht1 (φ.injective (by rw [h1, map_one])), ?_, ?_,
    lieModel_map_equiv φ hJm, map_mono hJ₀L, map_mono hJ₀J, ?_⟩
  · rw [hfix]
    exact map_mono hLE
  · rw [hfix]
    exact isPComponent_map_subgroupOf φ hLE hLc
  · intro htop
    apply hLtop
    have := congrArg (Subgroup.map φ.symm.toMonoidHom) htop
    rwa [Subgroup.map_map, show φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id P from by
      ext; simp, Subgroup.map_id, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.2 φ.symm.surjective] at this
  · rw [hcent]
    exact map_mono hJt
  · rw [hcent]
    exact isPComponent_map_subgroupOf φ hJt hJc
  · have hO : ((pPrimeCore 2 ↥J).map J.subtype).map φ.toMonoidHom =
        (pPrimeCore 2 ↥(J.map φ.toMonoidHom)).map (J.map φ.toMonoidHom).subtype := by
      rw [← pPrimeCore_map_iso 2 (J.equivMapOfInjective φ.toMonoidHom φ.injective),
        Subgroup.map_map, Subgroup.map_map]
      rfl
    rw [← hO, ← Subgroup.map_sup, hJ₀]

end CFSG.ComponentClassification.GSThmB.QPUCl
