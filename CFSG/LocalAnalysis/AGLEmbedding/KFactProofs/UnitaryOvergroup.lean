module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryModel
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryAut
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.AGLEmbedding.UnitaryModel

open CFSG.UnitaryThreeRecognition.Model CFSG.BenderSuzuki.MatrixGroups

theorem le_stabilizer_of_isSimpleGroup {G Ω : Type*} [Group G] [MulAction G Ω] [IsSimpleGroup G]
    {ω : Ω} {U H : Subgroup G} (hU : U ≠ ⊥)
    (hN : MulAction.stabilizer G ω ≤ Subgroup.normalizer (U : Set G))
    (hreg : ∀ β γ : Ω, β ≠ ω → γ ≠ ω → ∃ u ∈ U, u • β = γ) (hUH : U ≤ H) (hH : H ≠ ⊤) :
    H ≤ MulAction.stabilizer G ω := by
  by_contra hle
  obtain ⟨h, hhH, hhω⟩ := Set.not_subset.1 hle
  have hhω' : h • ω ≠ ω := hhω
  have hcos : ∀ g : G, ∃ k ∈ H, k⁻¹ * g ∈ MulAction.stabilizer G ω := by
    intro g
    by_cases hg : g • ω = ω
    · exact ⟨1, H.one_mem, by rwa [inv_one, one_mul, MulAction.mem_stabilizer_iff]⟩
    obtain ⟨u, hu, hug⟩ := hreg (h • ω) (g • ω) hhω' hg
    refine ⟨u * h, H.mul_mem (hUH hu) hhH, ?_⟩
    rw [MulAction.mem_stabilizer_iff, mul_smul, ← hug, ← mul_smul u h, inv_smul_smul]
  have hconj : ∀ g : G, ∀ x ∈ U, g * x * g⁻¹ ∈ H := by
    intro g x hx
    obtain ⟨k, hk, hs⟩ := hcos g
    have hsx : (k⁻¹ * g) * x * (k⁻¹ * g)⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.1 (hN hs) x).1 hx
    have e : g * x * g⁻¹ = k * ((k⁻¹ * g) * x * (k⁻¹ * g)⁻¹) * k⁻¹ := by group
    rw [e]
    exact H.mul_mem (H.mul_mem hk (hUH hsx)) (H.inv_mem hk)
  have hcl : Subgroup.normalClosure (U : Set G) ≤ H := by
    show Subgroup.closure (Group.conjugatesOfSet (U : Set G)) ≤ H
    rw [Subgroup.closure_le]
    intro y hy
    obtain ⟨x, hx, hxy⟩ := Group.mem_conjugatesOfSet_iff.1 hy
    obtain ⟨c, rfl⟩ := isConj_iff.1 hxy
    exact hconj c x hx
  rcases (Subgroup.normalClosure_normal (s := (U : Set G))).eq_bot_or_eq_top with h1 | h1
  · exact hU (eq_bot_iff.2 fun x hx => h1 ▸ Subgroup.subset_normalClosure hx)
  · exact hH (eq_top_iff.2 (h1 ▸ hcl))

section Model

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {q : ℕ}
  (hK : Nat.card K = q ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = q)

include hK hfix

theorem le_stabilizer_pinf_of_rootGroup_le (hq : 2 < q)
    {H : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)} (hRH : rootGroup J hJ ≤ H)
    (hH : H ≠ ⊤) : H ≤ MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (pinf J hJ) := by
  haveI := isSimpleGroup_psu J q hK hfix hq
  refine le_stabilizer_of_isSimpleGroup ?_ (stabilizer_pinf_le_normalizer_rootGroup J hJ q hK hfix)
    (fun β γ hβ hγ => ?_) hRH hH
  · intro h0
    have hc := card_rootGroup J hJ q hK hfix
    rw [h0, Subgroup.card_bot] at hc
    have : 1 < q ^ 3 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  · obtain ⟨⟨r, hr⟩, hrβ, -⟩ := rootGroup_regular J hJ β γ hβ hγ
    exact ⟨r, hr, hrβ⟩

end Model

theorem isSolvable_of_unitary_sylow_le {L : Type} [Group L] [Finite L] {p : ℕ} [Fact p.Prime]
    {d : TauCeti.ValidLieTypeIndex} (hd : IsUnitaryIndex p d) (h : Nonempty (L ≃* CatGroup d))
    (U : Sylow p L) {H : Subgroup L} (hUH : (U : Subgroup L) ≤ H) (hH : H ≠ ⊤) :
    Group.IsSolvable H := by
  obtain ⟨-, hf, hq, K, _, _, J, hJ, hK, hfix, ⟨e⟩⟩ :=
    exists_equiv_psu (statedClassicalModel hd h)
  obtain ⟨S, hS⟩ := exists_sylow_eq_rootGroup J hJ hK hfix hf
  obtain ⟨e', he'⟩ := exists_equiv_map_eq e U S
  have hle : H.map e'.toMonoidHom ≤
      MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (pinf J hJ) := by
    refine le_stabilizer_pinf_of_rootGroup_le J hJ hK hfix hq ?_ ?_
    · rw [← hS, ← he']
      exact Subgroup.map_mono hUH
    · intro htop
      apply hH
      have := congrArg (Subgroup.comap e'.toMonoidHom) htop
      rwa [Subgroup.comap_map_eq_self_of_injective e'.injective, Subgroup.comap_top] at this
  haveI := isSolvable_stabilizer_pinf J hJ hK hfix
  exact Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.inclusion hle).comp
      (Subgroup.equivMapOfInjective H e'.toMonoidHom e'.injective).toMonoidHom)
    ((Subgroup.inclusion_injective hle).comp
      (Subgroup.equivMapOfInjective H e'.toMonoidHom e'.injective).injective)

end CFSG.AGLEmbedding.UnitaryModel
