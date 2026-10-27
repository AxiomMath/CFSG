module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitInputs
public import CFSG.ClassicalInvolution.LBalance.Proof.Tools
public import CFSG.LocalAnalysis.ComponentClassification.SolAltLitStandard
import CFSG.GroupTheory.Fitting.LayerTopBot

public section

namespace CFSG.ComponentClassification.Sol78

open CFSG Subgroup

theorem layer_eq_top_of_mulEquiv {A B : Type*} [Group A] [Group B] (f : A ≃* B)
    (h : layer A = ⊤) : layer B = ⊤ := by
  have hle : (layer A).map f.toMonoidHom ≤ layer B := by
    rw [map_le_iff_le_comap]
    refine sSup_le fun K hK => ?_
    rw [← map_le_iff_le_comap]
    exact le_sSup (LocalCores.isComponent_map_mulEquiv f hK)
  rw [h, map_top_of_surjective _ f.surjective] at hle
  exact top_unique hle

theorem layer_layer_eq_top {Q : Type*} [Group Q] : layer ↥(layer Q) = ⊤ :=
  CFSG.WholeGroup.layer_layer_eq_top

theorem normal_of_isComponent_of_layer_eq_top {Q : Type*} [Group Q] [Finite Q]
    (hQ : layer Q = ⊤) {K : Subgroup Q} (hK : IsComponent K) : K.Normal := by
  rw [← normalizer_eq_top_iff, eq_top_iff, ← hQ]
  refine sSup_le fun K' hK' => ?_
  rcases LocalCores.distinct_components_commute hK hK' with h | h
  · rw [← h]
    exact le_normalizer
  · rw [commutator_comm] at h
    exact (commutator_eq_bot_iff_le_centralizer.mp h).trans (centralizer_le_normalizer _)

theorem layer_eq_top_of_normal_of_perfect {Q : Type*} [Group Q] [Finite Q] (hQ : layer Q = ⊤)
    {N : Subgroup Q} (hN : N.Normal) (hNp : ⁅N, N⁆ = N) : layer ↥N = ⊤ := by
  set S := sSup {K : Subgroup Q | IsComponent K ∧ K ≤ N} with hS
  set T := sSup {K : Subgroup Q | IsComponent K ∧ ¬ K ≤ N} with hT
  have hSN : S ≤ N := sSup_le fun K hK => hK.2
  have hSn : S.Normal := Subgroup.sSup_normal _ fun K hK =>
    normal_of_isComponent_of_layer_eq_top hQ hK.1
  have hTN : T ≤ centralizer (N : Set Q) := sSup_le fun K hK => by
    rcases LocalCores.component_normal_subgroup hK.1 hN with h | h
    · exact absurd h hK.2
    · exact commutator_eq_bot_iff_le_centralizer.mp h
  have hST : S ⊔ T = ⊤ := by
    rw [eq_top_iff, ← hQ]
    refine sSup_le fun K hK => ?_
    by_cases h : K ≤ N
    · exact le_sup_of_le_left (le_sSup ⟨hK, h⟩)
    · exact le_sup_of_le_right (le_sSup ⟨hK, h⟩)
  have hNS : N ≤ S := by
    set π := QuotientGroup.mk' S with hπ
    have hcen : N.map π ≤ center (Q ⧸ S) := by
      rintro _ ⟨x, hx, rfl⟩
      rw [mem_center_iff]
      intro q
      have hq : q ∈ (S ⊔ T).map π := by
        rw [hST, map_top_of_surjective _ (QuotientGroup.mk'_surjective S)]
        exact mem_top q
      rw [Subgroup.map_sup] at hq
      have hle : S.map π ⊔ T.map π ≤ centralizer ({π x} : Set (Q ⧸ S)) := by
        refine sup_le ?_ ?_
        · rintro _ ⟨s, hs, rfl⟩
          rw [mem_centralizer_singleton_iff]
          have h1 : π s = 1 := (QuotientGroup.eq_one_iff s).mpr hs
          rw [h1, one_mul, mul_one]
        · rintro _ ⟨u, hu, rfl⟩
          rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
          congr 1
          exact (mem_centralizer_iff.mp (hTN hu) x hx).symm
      exact mem_centralizer_singleton_iff.mp (hle hq)
    have hab : ⁅N.map π, N.map π⁆ = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr (hcen.trans (center_le_centralizer _))
    rw [← Subgroup.map_commutator, hNp, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hab
    exact hab
  have hle : S ≤ (layer ↥N).map N.subtype := by
    refine sSup_le fun K hK => ?_
    have hc' : K.subgroupOf N ≤ layer ↥N := le_sSup (LocalCores.component_overgroup hK.1 hK.2)
    intro x hx
    exact ⟨⟨x, hK.2 hx⟩, hc' (show (⟨x, hK.2 hx⟩ : N) ∈ K.subgroupOf N from hx), rfl⟩
  refine top_unique fun y _ => ?_
  obtain ⟨z, hz, hzy⟩ := hle (hNS y.2)
  rwa [Subtype.ext hzy] at hz

theorem layer_twoLayerIn_eq_top {X : Type} [Group X] [Finite X] {C : Subgroup X}
    (hO : pPrimeCore 2 ↥C = ⊥) : layer ↥(FooteLit.twoLayerIn C) = ⊤ := by
  have h1 : pLayer ↥C 2 = layer ↥C :=
    ClassicalInvolution.LBalanceProof.pLayer_eq_layer_of_pPrimeCore_eq_bot hO
  have e : ↥(layer ↥C) ≃* ↥(FooteLit.twoLayerIn C) := by
    rw [FooteLit.twoLayerIn, h1]
    exact (layer ↥C).equivMapOfInjective C.subtype C.subtype_injective
  exact layer_eq_top_of_mulEquiv e layer_layer_eq_top

theorem conjClosure_le {X : Type*} [Group X] {J E M : Subgroup X} (hJM : J ≤ M)
    (hEM : E ≤ normalizer (M : Set X)) : FooteLit.conjClosure J E ≤ M := by
  rw [FooteLit.conjClosure, closure_le]
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨e, he, hxe⟩ := hx
  rw [SetLike.mem_coe, SolAltLit.mem_conjugate_iff_conj] at hxe
  have h1 := (mem_normalizer_iff.mp (hEM (inv_mem he)) (e * x * e⁻¹)).mp (hJM hxe)
  have h2 : e⁻¹ * (e * x * e⁻¹) * e⁻¹⁻¹ = x := by group
  rw [h2] at h1
  exact h1

theorem le_normalizer_conjClosure {X : Type*} [Group X] (J E : Subgroup X) :
    E ≤ normalizer (FooteLit.conjClosure J E : Set X) := by
  have key : ∀ g ∈ E, ∀ x ∈ FooteLit.conjClosure J E, g * x * g⁻¹ ∈ FooteLit.conjClosure J E := by
    intro g hg x hx
    have hmap : (FooteLit.conjClosure J E).map (MulAut.conj g).toMonoidHom ≤
        FooteLit.conjClosure J E := by
      rw [FooteLit.conjClosure, MonoidHom.map_closure]
      refine closure_mono ?_
      rintro _ ⟨y, hy, rfl⟩
      simp only [Set.mem_iUnion] at hy ⊢
      obtain ⟨e, he, hye⟩ := hy
      refine ⟨e * g⁻¹, mul_mem he (inv_mem hg), ?_⟩
      rw [SetLike.mem_coe, SolAltLit.mem_conjugate_iff_conj] at hye ⊢
      have h1 : e * g⁻¹ * ((MulAut.conj g).toMonoidHom y) * (e * g⁻¹)⁻¹ = e * y * e⁻¹ := by
        simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply]
        group
      rw [h1]
      exact hye
    exact hmap ⟨x, hx, rfl⟩
  intro g hg
  rw [mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have h1 := key g⁻¹ (inv_mem hg) _ hx
  have h2 : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rwa [h2] at h1

theorem conjClosure_perfect {X : Type*} [Group X] {J : Subgroup X} (hJ : ⁅J, J⁆ = J)
    (E : Subgroup X) :
    ⁅FooteLit.conjClosure J E, FooteLit.conjClosure J E⁆ = FooteLit.conjClosure J E := by
  refine le_antisymm (commutator_le.mpr fun x hx y hy => ?_) ?_
  · exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  · rw [FooteLit.conjClosure, closure_le]
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨e, he, hxe⟩ := hx
    have hle : conjugate J e ≤ FooteLit.conjClosure J E := by
      rw [FooteLit.conjClosure]
      intro y hy
      exact subset_closure (Set.mem_iUnion₂.mpr ⟨e, he, hy⟩)
    have hperf : ⁅conjugate J e, conjugate J e⁆ = conjugate J e := by
      rw [conjugate, ← Subgroup.map_commutator, hJ]
    rw [SetLike.mem_coe, ← hperf] at hxe
    exact commutator_mono hle hle hxe

theorem layer_conjClosure_eq_top {X : Type} [Group X] [Finite X] {C J E : Subgroup X}
    (hO : pPrimeCore 2 ↥C = ⊥) (hJ : ⁅J, J⁆ = J) (hJL : J ≤ FooteLit.twoLayerIn C)
    (hLE : FooteLit.twoLayerIn C ≤ E)
    (hEL : E ≤ normalizer (FooteLit.twoLayerIn C : Set X)) :
    layer ↥(FooteLit.conjClosure J E) = ⊤ := by
  set M := FooteLit.twoLayerIn C with hM
  set Y := FooteLit.conjClosure J E with hY
  have hYM : Y ≤ M := conjClosure_le hJL hEL
  have hn : (Y.subgroupOf M).Normal := by
    rw [normal_subgroupOf_iff_le_normalizer hYM]
    exact hLE.trans (le_normalizer_conjClosure J E)
  have hperf : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr (conjClosure_perfect hJ E)
  have hperf' : ⁅Y.subgroupOf M, Y.subgroupOf M⁆ = Y.subgroupOf M := by
    rw [← Subgroup.isPerfect_iff]
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hYM).symm.toMonoidHom)
      (subgroupOfEquivOfLe hYM).symm.surjective
  have h := layer_eq_top_of_normal_of_perfect (layer_twoLayerIn_eq_top hO) hn hperf'
  exact layer_eq_top_of_mulEquiv (subgroupOfEquivOfLe hYM) h

end CFSG.ComponentClassification.Sol78
