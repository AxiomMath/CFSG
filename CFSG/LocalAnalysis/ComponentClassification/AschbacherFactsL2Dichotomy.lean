module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Outer

public section

namespace CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2

open CFSG.Open CFSG.GorensteinWalter

theorem hasDihedralSylowTwo_of_mulEquiv {X Y : Type*} [Group X] [Group Y] [Finite X]
    (e : X ≃* Y) (h : HasDihedralSylowTwo X) : HasDihedralSylowTwo Y := by
  obtain ⟨S, n, hn, ⟨eS⟩⟩ := h
  refine ⟨S.mapSurjective (f := e.toMonoidHom) e.surjective, n, hn, ⟨?_⟩⟩
  exact ((S : Subgroup X).equivMapOfInjective e.toMonoidHom e.injective).symm.trans eS

theorem involution_dichotomy {R : Type} [Group R] [Finite R] (N : Subgroup R) [N.Normal]
    [IsSimpleGroup N] (hN : HasDihedralSylowTwo N) (r : R) (hr : r ^ 2 = 1) :
    (∃ u w : N, u ^ 2 = 1 ∧ w ^ 2 = 1 ∧ u ≠ 1 ∧ w ≠ 1 ∧ u ≠ w ∧ u * w = w * u ∧
      r * u = u * r ∧ r * w = w * r) ∨
      ∀ y : N, orderOf y = 4 → r * y ≠ y * r := by
  by_cases hI : ∃ u w : N, u ^ 2 = 1 ∧ w ^ 2 = 1 ∧ u ≠ 1 ∧ w ≠ 1 ∧ u ≠ w ∧ u * w = w * u ∧
      r * u = u * r ∧ r * w = w * r
  · exact Or.inl hI
  right
  have hno : ∀ u w : N, u ^ 2 = 1 → w ^ 2 = 1 → u ≠ 1 → w ≠ 1 → u ≠ w → u * w = w * u →
      r * u = u * r → r * w = w * r → False :=
    fun u w h1 h2 h3 h4 h5 h6 h7 h8 => hI ⟨u, w, h1, h2, h3, h4, h5, h6, h7, h8⟩
  rcases simple_dihedral_cases (exists_ne_comm_of_simple_dihedral hN) hN with
    hA7 | ⟨K, _, _, p, f, hp, hKcard, hK, hcard, ⟨eL⟩⟩
  · obtain ⟨eA⟩ := hA7
    exact absurd (a7_involution_commuting_pair N eA r hr) hI
  have : Fact p.Prime := ⟨hp⟩
  have hsurj := pGammaL2ToMulAutPSL2_surjective K hKcard hK hcard
  obtain ⟨g, hg⟩ := psl2Action_involution_linear N hK hcard eL hsurj r hr hno
  have hgJ : g ∉ pslRange K := by
    intro hgJ
    have hmem : normalPSL2ToPGammaL2 N K hK hcard eL hsurj r ∈ pGammaL2PSLRange K := by
      obtain ⟨y, hy⟩ := hgJ
      rw [hg, ← hy]
      exact ⟨y, rfl⟩
    obtain ⟨m, hm⟩ := psl2Action_mem_pslRange N hK hcard eL hsurj r hmem
    have hc : r * (m : R)⁻¹ ∈ Subgroup.centralizer (N : Set R) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (hm ⟨y, hy⟩).symm
    have hin : r ∈ N ⊔ Subgroup.centralizer (N : Set R) := by
      have : r = r * (m : R)⁻¹ * m := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hc) (Subgroup.mem_sup_left m.2)
    obtain ⟨u, w, hu, hw, hu2, hw2, hu1, hw1, huw, hc'⟩ := inner_commuting_pair hN hr hin
    apply hno ⟨u, (Subgroup.mem_inf.mp hu).1⟩ ⟨w, (Subgroup.mem_inf.mp hw).1⟩
      (Subtype.ext hu2) (Subtype.ext hw2) (fun h => hu1 (congrArg Subtype.val h))
      (fun h => hw1 (congrArg Subtype.val h)) (fun h => huw (congrArg Subtype.val h))
      (Subtype.ext hc')
    · exact (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hu).2).symm
    · exact (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hw).2).symm
  have hg2 : g ^ 2 = 1 := by
    have h1 : (SemidirectProduct.inl (g ^ 2) : PGammaL2 K) = SemidirectProduct.inl 1 := by
      rw [map_pow, ← hg, ← map_pow, hr, map_one, map_one]
    exact SemidirectProduct.inl_injective h1
  intro y hy hry
  set c := Matrix.ProjectiveSpecialLinearGroup.toPGL (eL y) with hcdef
  have hc4 : orderOf c = 4 := by
    rw [hcdef, orderOf_injective _ Matrix.ProjectiveSpecialLinearGroup.toPGL_injective,
      MulEquiv.orderOf_eq, hy]
  have hcomm := (psl2Action_commute_iff N hK hcard eL hsurj r y).mp hry
  rw [hg, psl2Action_apply, ← map_mul, ← map_mul] at hcomm
  have hgc : c * g = g * c := (SemidirectProduct.inl_injective hcomm).symm
  rcases pgl2_eq_of_commute_orderOf_four hK hc4 hg2 hgc with h | h
  · exact hgJ (h ▸ (pslRange K).one_mem)
  · exact hgJ (h ▸ (pslRange K).pow_mem ⟨eL y, rfl⟩ 2)

theorem mulAut_involution_dichotomy {Q : Type} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hQ : HasDihedralSylowTwo Q) (α : MulAut Q) (hα : ∀ x, α (α x) = x) :
    (∃ u w : Q, u ^ 2 = 1 ∧ w ^ 2 = 1 ∧ u ≠ 1 ∧ w ≠ 1 ∧ u ≠ w ∧ u * w = w * u ∧
      α u = u ∧ α w = w) ∨
      ∀ y : Q, orderOf y = 4 → α y ≠ y := by
  have hQ' : HasDihedralSylowTwo (⊤ : Subgroup Q) :=
    hasDihedralSylowTwo_of_mulEquiv Subgroup.topEquiv.symm hQ
  have : IsSimpleGroup (⊤ : Subgroup Q) := Subgroup.topEquiv.isSimpleGroup
  have hcen : ∀ x : Q, (∀ y : Q, x * y = y * x) → x = 1 := by
    intro x hx
    have := eq_one_of_mem_center_of_simple_dihedral (L := ⊤) hQ' (x := x) trivial
      (fun y _ => hx y)
    exact this
  let c : Q →* MulAut Q := MulAut.conj
  have hcinj : Function.Injective c := by
    rw [injective_iff_map_eq_one]
    intro x hx
    apply hcen x
    intro y
    have := DFunLike.congr_fun hx y
    simp only [c, MulAut.conj_apply, MulAut.one_apply] at this
    calc x * y = x * y * x⁻¹ * x := by group
      _ = y * x := by rw [this]
  let N : Subgroup (MulAut Q) := c.range
  have hconj : ∀ (φ : MulAut Q) (x : Q), φ * c x * φ⁻¹ = c (φ x) := by
    intro φ x
    ext y
    simp [c, MulAut.conj_apply, MulAut.mul_apply]
  have hNn : N.Normal := by
    constructor
    rintro _ ⟨x, rfl⟩ φ
    exact ⟨φ x, (hconj φ x).symm⟩
  let e : Q ≃* N := MonoidHom.ofInjective hcinj
  have he : ∀ x, (e x : MulAut Q) = c x := fun x => MonoidHom.ofInjective_apply hcinj
  have : IsSimpleGroup N := e.symm.isSimpleGroup
  have hNd : HasDihedralSylowTwo N := hasDihedralSylowTwo_of_mulEquiv e hQ
  have hα2 : α ^ 2 = 1 := by
    ext x
    simp [pow_two, MulAut.mul_apply, hα]
  have hfix : ∀ x : Q, α * c x = c x * α ↔ α x = x := by
    intro x
    constructor
    · intro h
      apply hcinj
      rw [← hconj, h]
      group
    · intro h
      have := hconj α x
      rw [h] at this
      calc α * c x = α * c x * α⁻¹ * α := by group
        _ = c x * α := by rw [this]
  rcases involution_dichotomy N hNd α hα2 with
    ⟨u, w, hu, hw, hu1, hw1, huw, hc, hαu, hαw⟩ | hII
  · left
    refine ⟨e.symm u, e.symm w, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← map_pow, hu, map_one]
    · rw [← map_pow, hw, map_one]
    · simpa using hu1
    · simpa using hw1
    · simpa using huw
    · rw [← map_mul, ← map_mul, hc]
    · rw [← hfix, ← he, MulEquiv.apply_symm_apply]
      exact hαu
    · rw [← hfix, ← he, MulEquiv.apply_symm_apply]
      exact hαw
  · right
    intro y hy hαy
    apply hII (e y) (by rw [MulEquiv.orderOf_eq, hy])
    rw [he]
    exact (hfix y).mpr hαy

end CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2
