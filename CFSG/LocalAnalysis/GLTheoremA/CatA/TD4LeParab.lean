module

public import CFSG.LieType.BorelTits.AllModels
public import CFSG.RankThree.PartOne.S11c.Sec66D4Tri
public import CFSG.LieType.Chevalley.GraphFixedSylowOpposition
public import CFSG.LieType.Chevalley.GraphFixedBorelOvergroups
public import CFSG.LieType.Chevalley.GraphFixedBorelSelfNormalizer
public import CFSG.LieType.Chevalley.GraphFixedRootBruhat
public import CFSG.LieType.Chevalley.SylowOpposition
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Triality
public import CFSG.LocalAnalysis.GLTheoremA.CatA.TD4LeGrp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.TD4LeField
public import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.TD4Le

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open

theorem eq_empty_or_singleton_of_ne_univ {J : Set (Fin TwistTag.D4.foldedTag.rank)}
    (hJ : J ≠ Set.univ) : J = ∅ ∨ ∃ a, J = {a} := by
  by_cases hne : J.Nonempty
  · obtain ⟨a, ha⟩ := hne
    obtain ⟨b, hb⟩ : ∃ b, b ∉ J := by
      by_contra hcon
      push Not at hcon
      exact hJ (Set.eq_univ_of_forall hcon)
    have hab : ∀ a b x : Fin TwistTag.D4.foldedTag.rank, a ≠ b → x = a ∨ x = b := by decide
    refine Or.inr ⟨a, Set.eq_singleton_iff_unique_mem.2 ⟨ha, fun x hx => ?_⟩⟩
    have hba : a ≠ b := fun hh => hb (hh ▸ ha)
    rcases hab a b x hba with rfl | rfl
    · rfl
    · exact absurd hx hb
  · exact Or.inl (Set.not_nonempty_iff_eq_empty.1 hne)


theorem graphFixedParabolic_univ {t : TwistTag} {K : Type} [Field K] {σ : K →+* K}
    (hσ : Function.Surjective σ) :
    graphFixedParabolic t K σ Set.univ = graphFixedRootGroup t K σ := by
  refine le_antisymm (graphFixedParabolic_le t K σ _) ?_
  rw [graphFixedRootGroup_eq_sup_closure hσ]
  refine sup_le (graphFixedRootBorel_le_graphFixedParabolic t K σ _) ?_
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨a, rfl⟩
  exact le_sup_right (a := graphFixedRootBorel t K σ)
    (Subgroup.subset_closure ⟨a, Set.mem_univ a, rfl⟩)

variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {e : ℕ}

local notation "𝐂" => graphFixedRootGroup TwistTag.D4 K σ.toRingHom
local notation "𝐏(" J ")" =>
  Subgroup.subgroupOf (graphFixedParabolic TwistTag.D4 K σ.toRingHom J) 𝐂

theorem borelTits_normalized (h : Std e K σ) (T : Subgroup ↥𝐂) (hT : T ≠ ⊥)
    (hT2 : IsPGroup 2 T) :
    ∃ (g : ↥𝐂) (J : Set (Fin TwistTag.D4.foldedTag.rank)), J ≠ Set.univ ∧ ∃ R : Subgroup ↥𝐂,
      R ≤ 𝐏(J) ∧ IsPGroup 2 R ∧ (∀ x ∈ 𝐏(J), ∀ y ∈ R, x * y * x⁻¹ ∈ R) ∧
      T.map (MulAut.conj g).toMonoidHom ≤ R ∧
      (Subgroup.normalizer (T : Set ↥𝐂)).map (MulAut.conj g).toMonoidHom ≤ 𝐏(J) := by
  classical
  haveI : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  haveI : Finite ↥𝐂 := inferInstance
  haveI := h.charP_two
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmodel := CFSG.RankThree.PartOne.Sec66T.lieModel_graphFixedRootGroup_trialityD4 h.he h.hK σ
    h.hσ
  obtain ⟨S, P, hPtop, hNP, -, hTP, hSP, -⟩ :=
    CFSG.LieType.BorelTits.lieModel_conclusion _ _ 0 2 e hmodel T hT hT2
  have hNS := hSP (by decide)
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  obtain ⟨PU, hPU⟩ := (exceptional_fixed_Sylow_opposition TwistTag.D4 K 2 σ w₀ hw₀).1
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥𝐂 PU S
  set Ux : Subgroup ↥𝐂 :=
    (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf 𝐂 with hUx
  set Bx : Subgroup ↥𝐂 :=
    (graphFixedRootBorel TwistTag.D4 K σ.toRingHom).subgroupOf 𝐂 with hBx
  have hS : (S : Subgroup ↥𝐂) = Ux.map (MulAut.conj g).toMonoidHom := by
    rw [← hg, coe_smul_sylow_eq_map, hPU]
  have hBN : ∀ b ∈ Bx, ∀ u : ↥𝐂, u ∈ Ux ↔ b * u * b⁻¹ ∈ Ux := by
    intro b hb u
    have hbB : (b : ModGL TwistTag.D4.tag K) ∈ graphFixedRootBorel TwistTag.D4 K σ.toRingHom :=
      Subgroup.mem_subgroupOf.1 hb
    have hb' : (b : ModGL TwistTag.D4.tag K) ∈ Subgroup.normalizer
        (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom : Set (ModGL TwistTag.D4.tag K)) := by
      have := graphFixedRootGroup_inf_normalizer_graphFixedPosUnipotent (t := TwistTag.D4)
        (K := K) (σ := σ.toRingHom) σ.surjective
      rw [← this] at hbB
      exact (Subgroup.mem_inf.1 hbB).2
    have := Subgroup.mem_normalizer_iff.1 hb' (u : ModGL TwistTag.D4.tag K)
    rw [hUx, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
    exact this
  have hgB : ∀ b ∈ Bx, g * b * g⁻¹ ∈ P := by
    intro b hb
    refine hNS ?_
    rw [Subgroup.mem_normalizer_iff]
    intro s
    rw [hS, mem_map_conj_iff, mem_map_conj_iff]
    have := hBN b hb (g⁻¹ * s * g)
    have e : g⁻¹ * (g * b * g⁻¹ * s * (g * b * g⁻¹)⁻¹) * g = b * (g⁻¹ * s * g) * b⁻¹ := by group
    rw [e]
    exact this
  set P' : Subgroup ↥𝐂 := P.map (MulAut.conj g⁻¹).toMonoidHom with hP'
  have hmemP' : ∀ y, y ∈ P' ↔ g * y * g⁻¹ ∈ P := fun y => by
    rw [hP', mem_map_conj_iff, inv_inv]
  have hBP' : Bx ≤ P' := fun b hb => (hmemP' b).2 (hgB b hb)
  have hP'top : P' ≠ ⊤ := by
    intro htop
    apply hPtop
    rw [eq_top_iff]
    intro x _
    have := (hmemP' (g⁻¹ * x * g)).1 (htop ▸ Subgroup.mem_top _)
    have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rwa [e] at this
  have hBP'' : graphFixedRootBorel TwistTag.D4 K σ.toRingHom ≤ P'.map 𝐂.subtype := by
    intro b hb
    exact ⟨⟨b, graphFixedRootBorel_le _ _ _ hb⟩, hBP' (Subgroup.mem_subgroupOf.2 hb), rfl⟩
  have hP''C : P'.map 𝐂.subtype ≤ 𝐂 := Subgroup.map_subtype_le _
  obtain ⟨-, J, hJ, -⟩ := fixed_Borel_overgroup_classification TwistTag.D4 K σ _ hBP'' hP''C
  have hP'J : P' = 𝐏(J) := by
    rw [← hJ]
    exact (Subgroup.comap_map_eq_self_of_injective 𝐂.subtype_injective P').symm
  have hJuniv : J ≠ Set.univ := by
    rintro rfl
    apply hP'top
    rw [hP'J, graphFixedParabolic_univ σ.surjective]
    exact Subgroup.subgroupOf_self _
  refine ⟨g⁻¹, J, hJuniv, (pCoreOf 2 P).map (MulAut.conj g⁻¹).toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hP'J]
    exact Subgroup.map_mono (pCoreOf_le_self 2 P)
  · exact (isPGroup_pCoreOf 2 P).map _
  · intro x hx y hy
    rw [← hP'J] at hx
    have hx' := (hmemP' x).1 hx
    have hy' := (mem_map_conj_iff _ _ _).1 hy
    rw [mem_map_conj_iff]
    have := conj_mem_pCoreOf 2 P _ hx' _ hy'
    have e : g⁻¹⁻¹ * (x * y * x⁻¹) * g⁻¹ = g * x * g⁻¹ * (g⁻¹⁻¹ * y * g⁻¹) * (g * x * g⁻¹)⁻¹ := by
      group
    rw [e]
    exact this
  · exact Subgroup.map_mono hTP
  · rw [← hP'J]
    exact Subgroup.map_mono hNP

theorem not_dvd_relIndex_borel (h : Std e K σ) (hQ : 2 ^ e % 3 = 1)
    {J : Set (Fin TwistTag.D4.foldedTag.rank)} (hJ : J ≠ Set.univ) :
    ¬ 3 ∣ (graphFixedRootBorel TwistTag.D4 K σ.toRingHom).relIndex
      (graphFixedParabolic TwistTag.D4 K σ.toRingHom J) := by
  rcases eq_empty_or_singleton_of_ne_univ hJ with rfl | ⟨a, rfl⟩
  · rw [graphFixedParabolic_empty, Subgroup.relIndex_self]
    omega
  · rw [CFSG.QuasithinUnique.Setup.X6.relIndex_graphFixedParabolic_singleton σ a,
      card_orbitField_std h a]
    have hk : (TwistTag.D4.orbit a).card = 1 ∨ (TwistTag.D4.orbit a).card = 3 :=
      TwistTag.D4.card_orbit a
    have : (2 ^ e) ^ (TwistTag.D4.orbit a).card % 3 = 1 := by
      rw [Nat.pow_mod, hQ]
      simp
    omega

theorem relIndex_torus_borel (h : Std e K σ) :
    (graphFixedRootTorus TwistTag.D4 K σ.toRingHom).relIndex
      (graphFixedRootBorel TwistTag.D4 K σ.toRingHom) =
      Nat.card (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) := by
  haveI : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  set U := graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom with hU
  set H := graphFixedRootTorus TwistTag.D4 K σ.toRingHom with hH
  set B := graphFixedRootBorel TwistTag.D4 K σ.toRingHom with hB
  have hHB : H ≤ B := graphFixedRootTorus_le_graphFixedRootBorel
  have hUB : U ≤ B := graphFixedPosUnipotent_le_graphFixedRootBorel
  have hN : H ≤ Subgroup.normalizer (U : Set (ModGL TwistTag.D4.tag K)) :=
    hHB.trans graphFixedRootBorel_le_normalizer_graphFixedPosUnipotent
  have hsup : U ⊔ H = B := by
    refine le_antisymm (sup_le hUB hHB) fun b hb => ?_
    have hb' : b ∈ (B : Set (ModGL TwistTag.D4.tag K)) := hb
    rw [hB, graphFixedRootBorel_eq_mul' σ.surjective] at hb'
    obtain ⟨u, hu, x, hx, rfl⟩ := hb'
    exact mul_mem (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right hx)
  have hinf : U ⊓ H = ⊥ := by
    rw [inf_comm]
    exact graphFixedRootTorus_inf_graphFixedPosUnipotent
  have h1 := card_sup_mul_card_inf_of_le_normalizer hN
  rw [hsup, hinf, Subgroup.card_bot, mul_one] at h1
  have h2 := Subgroup.relIndex_mul_card (H := H) (K := B)
  rw [inf_eq_left.2 hHB] at h2
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h2.trans h1)

theorem isPGroup_two_posUnipotent (h : Std e K σ) :
    IsPGroup 2 ↥(graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) := by
  haveI := h.charP_two
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (isPGroup_graphFixedPosUnipotent_subgroupOf (p := 2) (t := TwistTag.D4)
    (σ := σ.toRingHom)).of_equiv
    (Subgroup.subgroupOfEquivOfLe (graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _))

theorem torus_parabolic_conditions (h : Std e K σ) (hQ : 2 ^ e % 3 = 1)
    {J : Set (Fin TwistTag.D4.foldedTag.rank)} (hJ : J ≠ Set.univ) :
    graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤
        graphFixedParabolic TwistTag.D4 K σ.toRingHom J ∧
      graphFixedRootTorus TwistTag.D4 K σ.toRingHom ≤
        graphFixedParabolic TwistTag.D4 K σ.toRingHom J ∧
      ¬ 3 ∣ (graphFixedRootTorus TwistTag.D4 K σ.toRingHom).relIndex
        (graphFixedParabolic TwistTag.D4 K σ.toRingHom J) := by
  haveI : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hBP := graphFixedRootBorel_le_graphFixedParabolic TwistTag.D4 K σ.toRingHom J
  have hHB : graphFixedRootTorus TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootBorel TwistTag.D4 K σ.toRingHom := graphFixedRootTorus_le_graphFixedRootBorel
  refine ⟨graphFixedPosUnipotent_le_graphFixedRootBorel.trans hBP, hHB.trans hBP, ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex _ _ _ hHB hBP, relIndex_torus_borel σ h]
  intro h3
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3 with h3 | h3
  · obtain ⟨n, hn⟩ := (isPGroup_two_posUnipotent σ h).exists_card_eq
    rw [hn] at h3
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  · exact not_dvd_relIndex_borel σ h hQ hJ h3

end CFSG.LocalAnalysis.GLTheoremA.TD4Le

end
