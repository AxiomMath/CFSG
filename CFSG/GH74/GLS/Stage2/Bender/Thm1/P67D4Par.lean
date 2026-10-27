module

public import CFSG.GH74.GLS.Stage2.OddAut.RPData
public import CFSG.GH74.GLS.Stage2.OddAut.OutCyc
public import CFSG.LieType.Chevalley.ParabolicDiagonalFieldNormalizersFixed

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.BorelTits
  CFSG.GH74.GLS.Stage2.OddAut CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open CFSG.LocalAnalysis.ComponentInitial (ringAut_mul_comm)

theorem par_conj_mem_fixedDiagonalFieldActors (t : TwistTag) (K : Type) [Field K] (σ : K ≃+* K) :
    (MulAut.conj : graphFixedRootGroup t K σ.toRingHom →*
      MulAut (graphFixedRootGroup t K σ.toRingHom)).range ≤ fixedDiagonalFieldActors t K σ :=
  (Chevalley_diagonal_field_actor_data.2 t K σ).2.2

theorem pCharData_fixed (t : TwistTag) (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (hσ : σ ^ t.order = 1) (p : ℕ) [Fact p.Prime] [CharP K p] :
    PCharData (graphFixedRootGroup t K σ.toRingHom) p (fixedDiagonalFieldActors t K σ) := by
  classical
  have : Finite (ModGL t.tag K) := finite_modGL
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element t.tag
  obtain ⟨⟨U, hU⟩, -⟩ := exceptional_fixed_Sylow_opposition t K p σ w₀ hw₀
  have hB := (fixed_Borel_self_normalizers t K σ w₀ hw₀).2.2.2.2.2.2.1
  have hBC : graphFixedRootBorel t K σ.toRingHom ≤ graphFixedRootGroup t K σ.toRingHom := by
    rw [← hB]
    exact inf_le_left
  have hBN : ∀ b ∈ graphFixedRootBorel t K σ.toRingHom,
      b ∈ Subgroup.normalizer (graphFixedPosUnipotent t K σ.toRingHom : Set (ModGL t.tag K)) := by
    intro b hb
    rw [← hB] at hb
    exact hb.2
  refine PCharData.of_standard (par_conj_mem_fixedDiagonalFieldActors t K σ) U ?_
  intro P hNP hPtop
  have hBle : graphFixedRootBorel t K σ.toRingHom ≤
      P.map (graphFixedRootGroup t K σ.toRingHom).subtype := by
    intro b hb
    have hbC : b ∈ graphFixedRootGroup t K σ.toRingHom := hBC hb
    have hbN : (⟨b, hbC⟩ : graphFixedRootGroup t K σ.toRingHom) ∈
        Subgroup.normalizer ((U : Subgroup (graphFixedRootGroup t K σ.toRingHom)) :
          Set (graphFixedRootGroup t K σ.toRingHom)) := by
      rw [hU, Subgroup.mem_normalizer_iff]
      intro u
      have := Subgroup.mem_normalizer_iff.1 (hBN b hb) (u : ModGL t.tag K)
      constructor
      · intro hu
        exact Subgroup.mem_subgroupOf.2 (this.1 (Subgroup.mem_subgroupOf.1 hu))
      · intro hu
        exact Subgroup.mem_subgroupOf.2 (this.2 (Subgroup.mem_subgroupOf.1 hu))
    exact ⟨_, hNP hbN, rfl⟩
  have hP'C : P.map (graphFixedRootGroup t K σ.toRingHom).subtype ≤
      graphFixedRootGroup t K σ.toRingHom := Subgroup.map_subtype_le _
  have hcl := (fixed_Borel_overgroup_classification t K σ _ hBle hP'C).1
  set P' : Subgroup (ModGL t.tag K) := P.map (graphFixedRootGroup t K σ.toRingHom).subtype
    with hP'
  set J : Set (Fin t.foldedTag.rank) :=
    {a | canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∈ P'} with hJdef
  have hJ : J ≠ Set.univ := by
    intro h
    apply hPtop
    have hP'top : P' = graphFixedRootGroup t K σ.toRingHom := by
      rw [hcl, h, (fixed_standard_parabolic_cells t K σ).2.2.2.2.2]
    rw [eq_top_iff]
    intro x _
    have hx : (x : ModGL t.tag K) ∈ P' := by rw [hP'top]; exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  obtain ⟨-, -, -, -, -, -, -, -, hQPJ, hQnJ, -, -, -, -, -, -, hQpJ, -⟩ :=
    diagram_fixed_parabolic_root_radical_Levi_factors t K σ J
  have hPJ : ∀ y : graphFixedRootGroup t K σ.toRingHom, y ∈ P →
      (y : ModGL t.tag K) ∈ graphFixedParabolic t K σ.toRingHom J := by
    intro y hy
    rw [← hcl]
    exact ⟨y, hy, rfl⟩
  have hQC : graphFixedParabolicRadical t K σ.toRingHom J ≤
      graphFixedRootGroup t K σ.toRingHom :=
    graphFixedParabolicRadical_le_graphFixedRootGroup t K σ.toRingHom J
  have hQP : graphFixedParabolicRadicalIn t K σ J ≤ P := by
    intro x hx
    have h1 : (x : ModGL t.tag K) ∈ graphFixedParabolic t K σ.toRingHom J :=
      hQPJ (mem_graphFixedParabolicRadicalIn.1 hx)
    rw [← hcl] at h1
    obtain ⟨y, hy, hyx⟩ := h1
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  have hQn : ((graphFixedParabolicRadicalIn t K σ J).subgroupOf P).Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hxQ : ((x : graphFixedRootGroup t K σ.toRingHom) : ModGL t.tag K) ∈
        graphFixedParabolicRadical t K σ.toRingHom J :=
      mem_graphFixedParabolicRadicalIn.1 (Subgroup.mem_subgroupOf.1 hx)
    have hxP : ((x : graphFixedRootGroup t K σ.toRingHom) : ModGL t.tag K) ∈
        graphFixedParabolic t K σ.toRingHom J := hQPJ hxQ
    have hgP := hPJ (g : graphFixedRootGroup t K σ.toRingHom) g.2
    have key := hQnJ.conj_mem
      (⟨((x : graphFixedRootGroup t K σ.toRingHom) : ModGL t.tag K), hxP⟩ :
        ↥(graphFixedParabolic t K σ.toRingHom J))
      (Subgroup.mem_subgroupOf.2 hxQ)
      ⟨((g : graphFixedRootGroup t K σ.toRingHom) : ModGL t.tag K), hgP⟩
    have key' := Subgroup.mem_subgroupOf.1 key
    refine Subgroup.mem_subgroupOf.2 (mem_graphFixedParabolicRadicalIn.2 ?_)
    exact key'
  have hQp : IsPGroup p (graphFixedParabolicRadicalIn t K σ J) :=
    (hQpJ p).of_equiv (Subgroup.subgroupOfEquivOfLe hQC).symm
  have hrigL :=
    (exact_parabolic_diagonal_field_normalizers_characteristic_p_fixed (p := p) t K σ hσ hJ).2.2.2.1
  refine ⟨graphFixedParabolicRadicalIn t K σ J, hQP, hQn, hQp, fun α hαA hfix => ?_⟩
  obtain ⟨z, ⟨z', hz', hzz⟩, hzα⟩ := (hrigL α).1 ⟨hαA, hfix⟩
  have hzQ : z ∈ graphFixedParabolicRadicalIn t K σ J := by
    rw [← hzz]
    exact z'.2
  exact ⟨z, hzQ, hzα⟩

theorem par_fixedDiagonalFieldActors_D4_eq_top_odd {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) : fixedDiagonalFieldActors TwistTag.D4 K σ = ⊤ := by
  obtain ⟨hfa, hnf, -⟩ := odd_triality_exact_automorphism_normal_form hp hp2 hf K hK σ hσ
  refine eq_top_iff.mpr fun α _ => ?_
  obtain ⟨⟨g, δ⟩, hgδ, -⟩ := hnf α
  refine ((Chevalley_diagonal_field_actor_data.2 TwistTag.D4 K σ).1 α).2
    ⟨g, g.2, 1, fun _ => (map_one _).symm, δ, ringAut_mul_comm K δ σ, fun x => ?_⟩
  rw [hgδ, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, hfa,
    rootDiagUnit_one, Subgroup.coe_inv]
  group

theorem d4_false_of_rp {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] [CharP K p] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f))
    {V Z : Subgroup (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))}
    (h2 : N2Cfg (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) p V Z)
    (h3 : N3Full (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) V Z) : False := by
  classical
  have hpp : p.Prime := Fact.out
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  obtain ⟨-, -, ⟨Θ, -, -, hΘk, -⟩, hcyc, -, -, hcen, ⟨eQ⟩⟩ :=
    odd_triality_exact_automorphism_normal_form hpp hp2 hf K hK σ hσ
  have hAtop := par_fixedDiagonalFieldActors_D4_eq_top_odd hpp hp2 hf K hK σ hσ
  have hσ3 : σ ^ TwistTag.D4.order = 1 := by
    have h3 : TwistTag.D4.order = 3 := rfl
    rw [h3]
    ext c
    simp [pow_succ, ringEquiv_cube_apply_eq hK hσ c]
  obtain ⟨-, -, hVe, hVc, -⟩ := id h2
  have := hVe
  have hVA : V ≤ fixedDiagonalFieldActors TwistTag.D4 K σ := fun v _ => hAtop ▸ Subgroup.mem_top v
  have hZA : Z ≤ fixedDiagonalFieldActors TwistTag.D4 K σ := fun v _ => hAtop ▸ Subgroup.mem_top v
  have hBT : Holds (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) p :=
    holds_of_twistedChevalleyModel (t := TwistTag.D4) hf
      ⟨K, inferInstance, inferInstance, hK, σ.toRingHom, hσ, ⟨eQ.symm⟩⟩
  obtain ⟨v, hvV, hv1, hΘv⟩ := exists_mem_ker_of_isCyclic (r := p) Θ hVc
  have hvinn : v ∈ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range := by
    rw [← hΘk]
    exact hΘv
  exact false_of_rp_data hBT hcen (pCharData_fixed TwistTag.D4 K σ hσ3 p)
    (par_conj_mem_fixedDiagonalFieldActors TwistTag.D4 K σ) hVA hZA h2 h3 ⟨v, hvV, hv1, hvinn⟩

end CFSG.GH74.GLS.Stage2.Bender.Thm1
