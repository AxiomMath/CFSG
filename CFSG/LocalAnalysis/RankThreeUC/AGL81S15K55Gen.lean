module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15F1L3Syl
public import CFSG.LargeExtraspecial.S5Syl
public import CFSG.Quasithin.Background.A4V
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.FiveThreeAlt.A6Clause
public import CFSG.LargeExtraspecial.S5Defs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K55Proof

open CFSG CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding
  CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt
  CFSG.LargeExtraspecial.S5 CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542 CFSG.ABGLocalTools

section Gen

variable {X : Type} [Group X] {T : Subgroup X} (hV : IsElemAbelian 2 (gnV T))
  [Module (ZMod 2) (Additive (IntMod (gnV T) hV))]

theorem exists_sylow_generation [Finite X] (hT : IsSylowTwoOf T ⊤)
    {Ls : Subgroup (X ⧸ gnC T)} (hL : IsSubnormal Ls ⊤) :
    ∃ S₀ : Subgroup (X ⧸ gnC T), IsSylowTwoIn S₀ Ls ∧
      ∀ w : Additive (IntMod (gnV T) hV), w ∈ Submodule.span (ZMod 2)
        {v | ∃ l ∈ Ls, ∃ c : Additive (IntMod (gnV T) hV),
          (∀ s ∈ S₀, gnRep hV s c = c) ∧ v = gnRep hV l c} := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT' : IsSylowTwoIn T ⊤ := hT
  set mk := QuotientGroup.mk' (gnC T) with hmk
  have hmksurj : Function.Surjective mk := QuotientGroup.mk'_surjective _
  have hTmap : IsSylowTwoIn (T.map mk) ⊤ := by
    have := hT'.map mk
    rwa [Subgroup.map_top_of_surjective mk hmksurj] at this
  refine ⟨(T.map mk) ⊓ Ls, hTmap.inf_of_isSubnormal hL, fun w => ?_⟩
  set Sp := Submodule.span (ZMod 2)
    {v : Additive (IntMod (gnV T) hV) | ∃ l ∈ Ls, ∃ c : Additive (IntMod (gnV T) hV),
      (∀ s ∈ (T.map mk) ⊓ Ls, gnRep hV s c = c) ∧ v = gnRep hV l c} with hSp
  have hgn : gnV T ≤ subOf hV Sp := by
    unfold gnV Subgroup.normalClosure
    refine (Subgroup.closure_le _).2 ?_
    intro v hv
    have hvg : v ∈ gnV T := Subgroup.subset_closure hv
    obtain ⟨z, hz, hconj⟩ := Group.mem_conjugatesOfSet_iff.1 hv
    obtain ⟨x, hxv⟩ := isConj_iff.1 hconj
    obtain ⟨w₀, hw₀⟩ := exists_elt hV hvg
    refine ⟨w₀, ?_, hw₀⟩
    let f : X →* (X ⧸ gnC T) := mk.comp (MulAut.conj x).toMonoidHom
    have hfsurj : Function.Surjective f := hmksurj.comp (MulAut.conj x).surjective
    have hR : IsSylowTwoIn (T.map f) ⊤ := by
      have := hT'.map f
      rwa [Subgroup.map_top_of_surjective f hfsurj] at this
    have hfix : ∀ r ∈ T.map f, gnRep hV r w₀ = w₀ := by
      rintro _ ⟨t, ht, rfl⟩
      apply elt_injective hV
      have hzc : t * z = z * t :=
        Subgroup.mem_centralizer_iff.1
          (CFSG.Quasithin.A4.centerOf_le_centralizer T
            (CFSG.Quasithin.A4.omegaOneCenterOf_le_centerOf T hz)) t ht
      show elt hV (gnRep hV (QuotientGroup.mk (x * t * x⁻¹)) w₀) = elt hV w₀
      rw [elt_gnRep, hw₀, ← hxv]
      calc x * t * x⁻¹ * (x * z * x⁻¹) * (x * t * x⁻¹)⁻¹ = x * (t * z * t⁻¹) * x⁻¹ := by group
        _ = x * z * x⁻¹ := by rw [hzc]; group
    have hS₀ : IsSylowTwoIn ((T.map mk) ⊓ Ls) Ls := hTmap.inf_of_isSubnormal hL
    have hS' : IsSylowTwoIn ((T.map f) ⊓ Ls) Ls := hR.inf_of_isSubnormal hL
    obtain ⟨l, hlL, hl⟩ := F1Proof.exists_conj_of_isSylowOf_two
      (isSylowOf_iff.2 hS₀) (isSylowOf_iff.2 hS')
    set c : Additive (IntMod (gnV T) hV) := gnRep hV l⁻¹ w₀ with hc
    have hcfix : ∀ s ∈ (T.map mk) ⊓ Ls, gnRep hV s c = c := by
      intro s hs
      have hy : l * s * l⁻¹ ∈ (T.map f) ⊓ Ls := by
        rw [hl]
        have : l⁻¹ * (l * s * l⁻¹) * l = s := by group
        rw [this]
        exact hs
      have h1 := hfix _ hy.1
      calc gnRep hV s c = gnRep hV (l⁻¹ * (l * s * l⁻¹)) w₀ := by
            rw [hc, ← Module.End.mul_apply, ← map_mul]
            congr 2
            group
        _ = gnRep hV l⁻¹ (gnRep hV (l * s * l⁻¹) w₀) := by
            rw [map_mul, Module.End.mul_apply]
        _ = c := by rw [h1]
    refine Submodule.subset_span ⟨l, hlL, c, hcfix, ?_⟩
    rw [hc, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  have hwK : elt hV w ∈ subOf hV Sp := hgn (elt_mem hV w)
  obtain ⟨w', hw', hww'⟩ := hwK
  rwa [← elt_injective hV hww']

end Gen

end CFSG.LocalAnalysis.RankThreeUC.S15.K55Proof
