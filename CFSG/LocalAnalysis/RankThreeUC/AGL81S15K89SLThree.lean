module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.FamilyL3
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Oracles
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K89SProof

open CFSG.AGLEmbeddingD2.McLaughlin CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem exists_Y_of_sub {X : Type} [Group X] [Finite X] (L : Subgroup X)
    (T : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) (hT : IsLThreeTwo ↥T) :
    ∃ Y : Subgroup X, Y ≤ L ∧ IsLThreeTwo (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
  classical
  let φ : ↥L →* (↥L ⧸ CFSG.pCore 2 ↥L) := QuotientGroup.mk' _
  let Y₀ : Subgroup ↥L := T.comap φ
  let Y : Subgroup X := Y₀.map L.subtype
  refine ⟨Y, Subgroup.map_subtype_le _, ?_⟩
  let e : ↥Y₀ ≃* ↥Y := Y₀.equivMapOfInjective L.subtype L.subtype_injective
  let ψ₀ : ↥Y₀ →* ↥T := (φ.comp Y₀.subtype).codRestrict T (fun x => x.2)
  let ψ : ↥Y →* ↥T := ψ₀.comp e.symm.toMonoidHom
  have hψs : Function.Surjective ψ := by
    intro t
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (t : ↥L ⧸ CFSG.pCore 2 ↥L)
    have hxY : x ∈ Y₀ := by
      show φ x ∈ T
      have : φ x = (t : ↥L ⧸ CFSG.pCore 2 ↥L) := hx
      rw [this]
      exact t.2
    refine ⟨e ⟨x, hxY⟩, ?_⟩
    show ψ₀ (e.symm (e ⟨x, hxY⟩)) = t
    rw [MulEquiv.symm_apply_apply]
    exact Subtype.ext hx
  have hk : ∀ y ∈ ψ.ker, ∃ k : ℕ, y ^ 2 ^ k = 1 := by
    intro y hy
    have hz : ψ₀ (e.symm y) = 1 := hy
    have hz' : φ ((e.symm y : ↥Y₀) : ↥L) = 1 := congrArg Subtype.val hz
    have hmem : ((e.symm y : ↥Y₀) : ↥L) ∈ CFSG.pCore 2 ↥L := (QuotientGroup.eq_one_iff _).mp hz'
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨_, hmem⟩
    refine ⟨k, ?_⟩
    have h1 : (e.symm y) ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    have h2 : y ^ 2 ^ k = e ((e.symm y) ^ 2 ^ k) := by
      rw [map_pow, MulEquiv.apply_symm_apply]
    rw [h2, h1, map_one]
  exact isLThreeTwo_quot_pCore_of_surj hT ψ hψs hk

open Matrix MatrixGroups

theorem exists_psl_embedding (K : Type) [Field K] [CharP K 2] :
    ∃ φ : SpecialLinearGroup (Fin 3) (ZMod 2) →* PSL(3, K), Function.Injective φ := by
  classical
  let f : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K
  have hf : Function.Injective f := f.injective
  refine ⟨(QuotientGroup.mk' _).comp (SpecialLinearGroup.map f), ?_⟩
  rw [injective_iff_map_eq_one]
  intro g hg
  have hc : SpecialLinearGroup.map f g ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K) :=
    (QuotientGroup.eq_one_iff _).mp hg
  obtain ⟨r, hr3, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  have hent : ∀ i j : Fin 3, f ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j) =
      (Matrix.scalar (Fin 3) r : Matrix (Fin 3) (Fin 3) K) i j := by
    intro i j
    have := congr_fun (congr_fun hr i) j
    rw [SpecialLinearGroup.map_apply_coe] at this
    simpa using this.symm
  have hoff : ∀ i j : Fin 3, i ≠ j → (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j = 0 := by
    intro i j hij
    apply hf
    rw [hent i j]
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, hij]
  have hdiag : ∀ i : Fin 3, f ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) i i) = r := by
    intro i
    rw [hent i i]
    simp [Matrix.scalar_apply, Matrix.diagonal_apply]
  have hd0 : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 0 = 1 := by
    have h3 : f (((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 0) ^ 3) = 1 := by
      rw [map_pow, hdiag 0]
      simpa using hr3
    have h3' : ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 0) ^ 3 = 1 := by
      apply hf
      rw [h3, map_one]
    generalize (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 0 = c at h3'
    revert c
    decide
  have hdi : ∀ i : Fin 3, (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) i i = 1 := by
    intro i
    apply hf
    rw [hdiag i, ← hdiag 0, hd0, map_one]
  apply Subtype.ext
  ext i j
  by_cases hij : i = j
  · subst hij
    simpa using hdi i
  · simpa [Matrix.one_apply, hij] using hoff i j hij

theorem exists_isLThreeTwo_sub (S : Type) [Group S] (h : IsLThreeTwoPow S) :
    ∃ T : Subgroup S, IsLThreeTwo ↥T := by
  classical
  rcases h with ⟨d, ⟨Q, hQ, hd⟩, ⟨e⟩⟩ | h7
  · obtain ⟨d1, hv⟩ := d
    have hd' : d1 = TauCeti.LieTypeIndex.A 2 Q := hd
    subst hd'
    haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
    haveI : CharP (GaloisField Q.p Q.exponent) 2 := by
      rw [← hQ]
      infer_instance
    let eP : S ≃* PSL(3, GaloisField Q.p Q.exponent) :=
      e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 Q hv)
    obtain ⟨φ, hφ⟩ := exists_psl_embedding (GaloisField Q.p Q.exponent)
    let T : Subgroup S := φ.range.map eP.symm.toMonoidHom
    refine ⟨T, ?_⟩
    have hSL : IsLThreeTwo (SpecialLinearGroup (Fin 3) (ZMod 2)) :=
      isLThreeTwo_of_mulEquiv
        (MulEquiv.ofBijective _ CFSG.LocalAnalysis.ComponentInitial.bijective_toGL_three_zmod_two)
        CFSG.AGLEmbeddingD2.McLaughlin.Lie.isLThreeTwo_GL_three_two
    let e1 : ↥T ≃* ↥φ.range :=
      (φ.range.equivMapOfInjective eP.symm.toMonoidHom eP.symm.injective).symm
    let e2 : ↥φ.range ≃* SpecialLinearGroup (Fin 3) (ZMod 2) := (MonoidHom.ofInjective hφ).symm
    exact isLThreeTwo_of_mulEquiv (e1.trans e2) hSL
  · exact ⟨⊤, isLThreeTwo_of_mulEquiv Subgroup.topEquiv h7⟩

theorem exists_Y {X : Type} [Group X] [Finite X] (L : Subgroup X)
    (h : IsLThreeTwoPow (↥L ⧸ CFSG.pCore 2 ↥L)) :
    ∃ Y : Subgroup X, Y ≤ L ∧ IsLThreeTwo (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
  obtain ⟨T, hT⟩ := exists_isLThreeTwo_sub _ h
  exact exists_Y_of_sub L T hT

end CFSG.LocalAnalysis.RankThreeUC.S15.K89SProof
