module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLift
public import CFSG.GH74.Generic.BProg.B3.S3Ctx29Defs

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
open scoped MatrixGroups

namespace S3Sec29BDiagAux

theorem involved_qdSL_of_equiv_sl2 {T : Type} [Group T] {F : Type} [Field F] {p : ℕ}
    [Fact p.Prime] [CharP F p] (e : T ≃* SL(2, F)) :
    CFSG.Glauberman.Involved (CFSG.Glauberman.qdSL p) T := by
  let f : ZMod p →+* F := ZMod.castHom (dvd_refl p) F
  have hf : Function.Injective f := f.injective
  let φ : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) F :=
    Matrix.SpecialLinearGroup.map f
  have hφ : Function.Injective φ := fun a b h => by
    apply Subtype.ext
    have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F =>
      (g : Matrix (Fin 2) (Fin 2) F)) h
    exact Matrix.map_injective hf this
  let ψ : CFSG.Glauberman.qdSL p →* T := e.symm.toMonoidHom.comp φ
  have hψ : Function.Injective ψ := e.symm.injective.comp hφ
  exact ⟨ψ.range, ⊥, Subgroup.normal_bot,
    ⟨(QuotientGroup.quotientBot).trans (MonoidHom.ofInjective hψ).symm⟩⟩

theorem involved_of_involved_subgroup' {H G : Type} [Group H] [Group G] {K : Subgroup G}
    (h : CFSG.Glauberman.Involved H ↥K) : CFSG.Glauberman.Involved H G := by
  obtain ⟨A, B, hB, ⟨e⟩⟩ := h
  have : B.Normal := hB
  let A₀ : Subgroup G := A.map K.subtype
  let e₀ : ↥A ≃* ↥A₀ := A.equivMapOfInjective K.subtype K.subtype_injective
  let N₀ : Subgroup ↥A₀ := B.map e₀.toMonoidHom
  have hN₀ : N₀.Normal := Subgroup.Normal.map inferInstance e₀.toMonoidHom e₀.surjective
  refine ⟨A₀, N₀, hN₀, ⟨?_⟩⟩
  have hmap : N₀.map e₀.symm.toMonoidHom = B := by
    rw [Subgroup.map_map]
    have : e₀.symm.toMonoidHom.comp e₀.toMonoidHom = MonoidHom.id _ := by
      ext a; simp
    rw [this, Subgroup.map_id]
  exact (QuotientGroup.congr N₀ B e₀.symm hmap).trans e

theorem false_of_sl2_quotient {H X : Type} [Group H] [Group X]
    (hX : CFSG.GorensteinWalter.HasDihedralSylowTwo X) [Finite X]
    (N : Subgroup H) [N.Normal] {F : Type} [Field F] {p : ℕ}
    [Fact p.Prime] [CharP F p] (hp2 : p ≠ 2) (e : (H ⧸ N) ≃* SL(2, F)) (ρ : H →* X)
    (hρ : ρ.ker ≤ N) : False := by
  classical
  set ρ' : H →* ↥ρ.range := ρ.rangeRestrict with hρ'
  have hρs : Function.Surjective ρ' := ρ.rangeRestrict_surjective
  have hkerρ' : ρ'.ker = ρ.ker := MonoidHom.ker_rangeRestrict ρ
  set N' : Subgroup ↥ρ.range := N.map ρ' with hN'
  have hN'n : N'.Normal := Subgroup.Normal.map inferInstance ρ' hρs
  set φ : H →* ↥ρ.range ⧸ N' := (QuotientGroup.mk' N').comp ρ' with hφ
  have hφs : Function.Surjective φ :=
    (QuotientGroup.mk'_surjective N').comp hρs
  have hφk : φ.ker = N := by
    ext g
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, hN']
    constructor
    · rintro ⟨n, hn, hng⟩
      have h1 : n⁻¹ * g ∈ ρ'.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hng, inv_mul_cancel]
      have h2 : n⁻¹ * g ∈ N := hρ (hkerρ' ▸ h1)
      have : g = n * (n⁻¹ * g) := by group
      rw [this]
      exact N.mul_mem hn h2
    · intro hg
      exact ⟨g, hg, rfl⟩
  have e1 : (↥ρ.range ⧸ N') ≃* (H ⧸ N) :=
    ((QuotientGroup.quotientKerEquivOfSurjective φ hφs).symm).trans
      (QuotientGroup.quotientMulEquivOfEq hφk)
  have h1 : CFSG.Glauberman.Involved (CFSG.Glauberman.qdSL p) (↥ρ.range ⧸ N') :=
    involved_qdSL_of_equiv_sl2 (e1.trans e)
  have h2 : CFSG.Glauberman.Involved (CFSG.Glauberman.qdSL p) ↥ρ.range :=
    CFSG.Glauberman.involved_of_involved_quotient N' h1
  have h3 : CFSG.Glauberman.Involved (CFSG.Glauberman.qdSL p) X :=
    involved_of_involved_subgroup' h2
  exact CFSG.GorensteinWalter.qdSL_not_involved_of_hasDihedralSylowTwo hX hp2 h3

theorem type_data {G : Type} [Group G] [Finite G] {J : Subgroup G}
    (h : IsA7Bar J ∨ IsL2OddNonSquare J) :
    CFSG.GorensteinWalter.HasDihedralSylowTwo (↥J ⧸ pPrimeCore 2 ↥J) ∧
      IsSimpleGroup (↥J ⧸ pPrimeCore 2 ↥J) := by
  rcases h with he | ⟨r, m, hr, hr2, hm, hmod⟩
  · obtain ⟨e⟩ := he
    refine ⟨CFSG.GorensteinWalter.hasDihedralSylowTwo_of_mulEquiv e
      CFSG.GorensteinWalter.hasDihedralSylowTwo_alternatingGroupSeven, ?_⟩
    have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by norm_num)
    exact e.isSimpleGroup
  · exact ⟨CFSG.ComponentClassification.HarrisLit.hasDihedralSylowTwo_of_lieModel_psl2 hr2 hmod,
      CFSG.ComponentClassification.HarrisLit.isSimpleGroup_of_lieModel_psl2 hmod⟩

end S3Sec29BDiagAux

end CFSG.GH74.Generic.BProg.B3
