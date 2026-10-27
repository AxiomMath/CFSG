module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.Cov
public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.RootFacts

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Lang.Triality CFSG.HardMathSupport.Lang.E27Lie
open CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement
open scoped Pointwise

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3


variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 3]
  (hK : Nat.card K = (3 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (3 ^ f))
include hf hK hσ

private theorem pinnedX_mem_posUnipotent_caseB {γ : Fin TwistTag.D4.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.D4.tag γ) (hp : 0 < height γ) (c : K) :
    pinnedX TwistTag.D4.tag K γ c ∈ posUnipotent TwistTag.D4.tag K :=
  pinnedX_mem_rootSpan (S := {α | IsRoot TwistTag.D4.tag α ∧ 0 < height α}) ⟨hγ, hp⟩ c

private theorem posUnipotent_le_borelGroup_caseB :
    posUnipotent TwistTag.D4.tag K ≤ borelGroup TwistTag.D4.tag K :=
  le_sup_right

private theorem exists_long_form_caseB (γ : Fin TwistTag.D4.tag.rank → ℤ)
    (hγ : γ = rootB ∨ γ = rootC ∨ γ = rootD) {c c'' : K} (hc : σ c = c) (hc'' : σ c'' = c'') :
    ∃ s r r' : K, σ s = s ∧ σ r = r ∧ σ r' = r' ∧
      pinnedX TwistTag.D4.tag K rootD (-c) * pinnedX TwistTag.D4.tag K γ c'' =
        pinnedX TwistTag.D4.tag K rootB s * pinnedX TwistTag.D4.tag K rootC r *
          pinnedX TwistTag.D4.tag K rootD r' := by
  rcases hγ with rfl | rfl | rfl
  · refine ⟨c'', 0, -c, hc'', map_zero σ, by rw [map_neg, hc], ?_⟩
    rw [pinnedX_zero, mul_one]
    exact (commute_pinnedX_rootD_of_mem_posUnipotent hf hK σ hσ
      (pinnedX_mem_posUnipotent_caseB hf hK σ hσ isRoot_rootB (by rw [height_rootB]; norm_num) c'')
      (-c)).eq.symm
  · refine ⟨0, c'', -c, map_zero σ, hc'', by rw [map_neg, hc], ?_⟩
    rw [pinnedX_zero, one_mul]
    exact (commute_pinnedX_rootD_of_mem_posUnipotent hf hK σ hσ
      (pinnedX_mem_posUnipotent_caseB hf hK σ hσ isRoot_rootC (by rw [height_rootC]; norm_num) c'')
      (-c)).eq.symm
  · refine ⟨0, 0, c'' - c, map_zero σ, map_zero σ, by rw [map_sub, hc'', hc], ?_⟩
    simp only [pinnedX_zero, one_mul]
    rw [← pinnedX_add]
    congr 1
    ring

theorem bruhat_caseB {c : K} (hc : σ c = c) (hc0 : c ≠ 0)
    (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hg : longElt hf hK σ hσ (Or.inr (Or.inr rfl)) c hc * fieldActor (t := TwistTag.D4) σ σ g *
      (longElt hf hK σ hσ (Or.inr (Or.inr rfl)) c hc)⁻¹ = g)
    {w : WeylGroup TwistTag.D4.tag} (hw : weylTwist TwistTag.D4 w = w) {b u : ModGL TwistTag.D4.tag K}
    (hb : b ∈ graphFixedBorel TwistTag.D4 K σ.toRingHom)
    (hu : u ∈ graphFixedInversionUnipotent TwistTag.D4 K σ.toRingHom w)
    (hgbu : (g : ModGL TwistTag.D4.tag K) =
      b * canonicalRep (coxeterSystem TwistTag.D4.tag) K w * u)
    (hinv : rootD ∉ inversionSet w) : fieldActor (t := TwistTag.D4) σ σ g = g := by
  set N : ModGL TwistTag.D4.tag K := canonicalRep (coxeterSystem TwistTag.D4.tag) K w
  set Z : ModGL TwistTag.D4.tag K := pinnedX TwistTag.D4.tag K rootD c with hZ
  have hZmem : Z ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom :=
    pinnedX_mem_graphFixedPosUnipotent hf hK σ hσ (Or.inr (Or.inr rfl)) hc
  have hZU : Z ∈ posUnipotent TwistTag.D4.tag K := (Subgroup.mem_inf.1 hZmem).1
  have hZΓ : Z ∈ twistedFixedGroup TwistTag.D4 K σ.toRingHom := (Subgroup.mem_inf.1 hZmem).2
  have hgZ : Z * Units.map (entrywiseHom σ.toRingHom) (g : ModGL TwistTag.D4.tag K) * Z⁻¹ =
      (g : ModGL TwistTag.D4.tag K) := by
    have h1 := congrArg Subtype.val hg
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_fieldActor,
      coe_longElt hf hK σ hσ (Or.inr (Or.inr rfl)) c hc] at h1
    exact h1
  have hEg : Units.map (entrywiseHom σ.toRingHom) (g : ModGL TwistTag.D4.tag K) =
      Z⁻¹ * (g : ModGL TwistTag.D4.tag K) * Z := by
    conv_rhs => rw [← hgZ]
    group
  have hEN : Units.map (entrywiseHom σ.toRingHom) N = N :=
    entrywise_canonicalRep (σ := σ) w
  have hEgbu : Units.map (entrywiseHom σ.toRingHom) (g : ModGL TwistTag.D4.tag K) =
      Units.map (entrywiseHom σ.toRingHom) b * N * Units.map (entrywiseHom σ.toRingHom) u := by
    rw [hgbu, map_mul, map_mul, hEN]
  have hu_R : u ∈ rootSpan TwistTag.D4.tag K (inversionSet w) := (Subgroup.mem_inf.1 hu).1
  have hu_pos : u ∈ posUnipotent TwistTag.D4.tag K :=
    rootSpan_le_posUnipotent (S := inversionSet w) (fun _ h => inversionSet_pos h) hu_R
  have hcomm : Commute u Z := commute_pinnedX_rootD_of_mem_posUnipotent hf hK σ hσ hu_pos c
  have hγroot : IsRoot TwistTag.D4.tag (w • rootD) := IsRoot.smul isRoot_rootD w
  have hγpos : 0 < height (w • rootD) := by
    rcases lt_or_gt_of_ne (IsRoot.height_ne_zero hγroot) with hlt | hgt
    · exfalso
      apply hinv
      simp only [inversionSet, Set.mem_setOf_eq]
      exact ⟨isRoot_rootD, by rw [height_rootD]; norm_num, hγroot, hlt⟩
    · exact hgt
  have hγfix : permLattice TwistTag.D4.perm (w • rootD) = w • rootD := by
    have h1 := weylTwist_smul_permLattice TwistTag.D4 w rootD
    have h2 : permLattice TwistTag.D4.perm rootD = rootD := by decide
    rw [hw, h2] at h1
    exact h1.symm
  have hγcase := eq_rootB_or_rootC_or_rootD_of_fixed hf hK σ hσ hγroot hγpos hγfix
  have hNΓ : N ∈ twistedFixedGroup TwistTag.D4 K σ.toRingHom :=
    canonicalRep_mem_twistedFixedGroup TwistTag.D4 K σ.toRingHom hw
  have hNZΓ : N * Z * N⁻¹ ∈ twistedFixedGroup TwistTag.D4 K σ.toRingHom :=
    mul_mem (mul_mem hNΓ hZΓ) (inv_mem hNΓ)
  have hNZ_root : N * Z * N⁻¹ ∈ rootSubgroup TwistTag.D4.tag K (w • rootD) := by
    rw [← (canonical_weyl_root_transport TwistTag.D4.tag K).2.1 w rootD isRoot_rootD]
    exact Subgroup.mem_map_of_mem _ (mem_rootSubgroup.2 ⟨c, rfl⟩)
  obtain ⟨cn, hcn⟩ := mem_rootSubgroup.1 hNZ_root
  have hNZ_pos : N * Z * N⁻¹ ∈ posUnipotent TwistTag.D4.tag K := by
    rw [← hcn]
    exact pinnedX_mem_posUnipotent_caseB hf hK σ hσ hγroot hγpos cn
  have hZB : Z ∈ borelGroup TwistTag.D4.tag K := posUnipotent_le_borelGroup_caseB hf hK σ hσ hZU
  have hZnB : N * Z * N⁻¹ ∈ borelGroup TwistTag.D4.tag K := posUnipotent_le_borelGroup_caseB hf hK σ hσ hNZ_pos
  have hbB : b ∈ borelGroup TwistTag.D4.tag K := (Subgroup.mem_inf.1 hb).1
  have hEb_B : Units.map (entrywiseHom σ.toRingHom) b ∈ borelGroup TwistTag.D4.tag K :=
    entrywise_mem_borelGroup (σ := σ) hbB
  have hEu_R : Units.map (entrywiseHom σ.toRingHom) u ∈
      rootSpan TwistTag.D4.tag K (inversionSet w) :=
    entrywise_mem_rootSpan (σ := σ) hu_R
  have hbZ : Z⁻¹ * b * (N * Z * N⁻¹) ∈ borelGroup TwistTag.D4.tag K :=
    mul_mem (mul_mem (inv_mem hZB) hbB) hZnB
  have heq : Units.map (entrywiseHom σ.toRingHom) b * N * Units.map (entrywiseHom σ.toRingHom) u =
      Z⁻¹ * b * (N * Z * N⁻¹) * N * u := by
    calc Units.map (entrywiseHom σ.toRingHom) b * N * Units.map (entrywiseHom σ.toRingHom) u
        = Units.map (entrywiseHom σ.toRingHom) (g : ModGL TwistTag.D4.tag K) := hEgbu.symm
      _ = Z⁻¹ * (g : ModGL TwistTag.D4.tag K) * Z := hEg
      _ = Z⁻¹ * (b * N * u) * Z := by rw [hgbu]
      _ = Z⁻¹ * b * N * (u * Z) := by group
      _ = Z⁻¹ * b * N * (Z * u) := by rw [hcomm.eq]
      _ = Z⁻¹ * b * (N * Z * N⁻¹) * N * u := by group
  have hpair := (bijOn_bruhatCell (K := K) w).2.1
    (Set.mk_mem_prod hEb_B hEu_R) (Set.mk_mem_prod hbZ hu_R) heq
  have hEb : Units.map (entrywiseHom σ.toRingHom) b = Z⁻¹ * b * (N * Z * N⁻¹) :=
    congrArg Prod.fst hpair
  have hEu : Units.map (entrywiseHom σ.toRingHom) u = u := congrArg Prod.snd hpair
  have hsurj : Function.Surjective σ.toRingHom := σ.surjective
  have hbmul : b ∈ (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom : Set (ModGL TwistTag.D4.tag K)) *
      (graphFixedTorus TwistTag.D4 K σ.toRingHom : Set (ModGL TwistTag.D4.tag K)) := by
    rw [← graphFixedBorel_eq_mul' hsurj]
    exact hb
  obtain ⟨u₁, hu₁, T, hT, hbT⟩ := Set.mem_mul.1 hbmul
  subst hbT
  have hu₁' : u₁ ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom := hu₁
  have hT' : T ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom := hT
  have hu₁U : u₁ ∈ posUnipotent TwistTag.D4.tag K := (Subgroup.mem_inf.1 hu₁').1
  have hu₁Γ : u₁ ∈ twistedFixedGroup TwistTag.D4 K σ.toRingHom := (Subgroup.mem_inf.1 hu₁').2
  have hTtor : T ∈ torusGroup TwistTag.D4.tag K := (Subgroup.mem_inf.1 hT').1
  have hTΓ : T ∈ twistedFixedGroup TwistTag.D4 K σ.toRingHom := (Subgroup.mem_inf.1 hT').2
  have hu₁C : u₁ ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.D4 K σ.toRingHom hu₁'
  obtain ⟨c'', hc''def⟩ : ∃ x : K, x = torusRootChar T (w • rootD) * cn := ⟨_, rfl⟩
  have hY : T * (N * Z * N⁻¹) * T⁻¹ = pinnedX TwistTag.D4.tag K (w • rootD) c'' := by
    rw [← hcn, conj_pinnedX_of_mem_torusGroup hTtor hγroot, hc''def]
  have hYΓ : T * (N * Z * N⁻¹) * T⁻¹ ∈ twistedFixedGroup TwistTag.D4 K σ.toRingHom :=
    mul_mem (mul_mem hTΓ hNZΓ) (inv_mem hTΓ)
  have hc''fix : σ c'' = c'' := by
    have hF := ((mem_twistedFixedGroup_iff_twistHom TwistTag.D4 K σ.toRingHom).1 hYΓ).2
    rw [hY, twistHom_pinnedX_of_fixedRoot hf hK σ hσ hγroot hγfix] at hF
    exact pinnedX_injective TwistTag.D4.tag K (w • rootD) hF
  have hYU : T * (N * Z * N⁻¹) * T⁻¹ ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom := by
    rw [hY]
    exact pinnedX_mem_graphFixedPosUnipotent hf hK σ hσ hγcase hc''fix
  have hETmem : Units.map (entrywiseHom σ.toRingHom) T ∈
      graphFixedTorus TwistTag.D4 K σ.toRingHom :=
    Subgroup.mem_inf.2 ⟨entrywise_mem_torusGroup (σ := σ) hTtor,
      entrywise_mem_twistedFixedGroup (t := TwistTag.D4) (σ := σ) (δ := σ) (fun _ => rfl) hTΓ⟩
  have hEu1Mem : Units.map (entrywiseHom σ.toRingHom) u₁ ∈
      graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom :=
    Subgroup.mem_inf.2 ⟨entrywise_mem_rootSpan (σ := σ) hu₁U,
      entrywise_mem_twistedFixedGroup (t := TwistTag.D4) (σ := σ) (δ := σ) (fun _ => rfl) hu₁Γ⟩
  have hu2Mem : Z⁻¹ * u₁ * (T * (N * Z * N⁻¹) * T⁻¹) ∈
      graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom :=
    mul_mem (mul_mem (inv_mem hZmem) hu₁') hYU
  have hEb' : Units.map (entrywiseHom σ.toRingHom) (u₁ * T) =
      Z⁻¹ * (u₁ * T) * (N * Z * N⁻¹) := hEb
  have heq2 : Units.map (entrywiseHom σ.toRingHom) u₁ * Units.map (entrywiseHom σ.toRingHom) T =
      Z⁻¹ * u₁ * (T * (N * Z * N⁻¹) * T⁻¹) * T := by
    calc Units.map (entrywiseHom σ.toRingHom) u₁ * Units.map (entrywiseHom σ.toRingHom) T
        = Units.map (entrywiseHom σ.toRingHom) (u₁ * T) := (map_mul _ _ _).symm
      _ = Z⁻¹ * (u₁ * T) * (N * Z * N⁻¹) := hEb'
      _ = Z⁻¹ * u₁ * (T * (N * Z * N⁻¹) * T⁻¹) * T := by group
  obtain ⟨hEu1, hET⟩ := graphFixed_mul_unique' hETmem hT' hEu1Mem hu2Mem heq2
  obtain ⟨s, r, r', hs, hr, hr', hX⟩ :=
    exists_long_form_caseB hf hK σ hσ (w • rootD) hγcase hc hc''fix
  have hZinv : Z⁻¹ = pinnedX TwistTag.D4.tag K rootD (-c) := by
    rw [hZ]
    exact pinnedX_neg TwistTag.D4.tag K rootD c
  have hXZ : Z⁻¹ * (T * (N * Z * N⁻¹) * T⁻¹) =
      pinnedX TwistTag.D4.tag K rootB s * pinnedX TwistTag.D4.tag K rootC r *
        pinnedX TwistTag.D4.tag K rootD r' := by
    rw [hY, hZinv, hX]
  have hcomm1 : Commute u₁ Z := commute_pinnedX_rootD_of_mem_posUnipotent hf hK σ hσ hu₁U c
  have hEu1' : Units.map (entrywiseHom σ.toRingHom) u₁ =
      u₁ * (Z⁻¹ * (T * (N * Z * N⁻¹) * T⁻¹)) := by
    rw [hEu1, ← hcomm1.inv_right.eq, mul_assoc]
  have hfa : fieldActor (t := TwistTag.D4) σ σ ⟨u₁, hu₁C⟩ =
      ⟨u₁, hu₁C⟩ * (longElt hf hK σ hσ (Or.inl rfl) s hs *
        longElt hf hK σ hσ (Or.inr (Or.inl rfl)) r hr *
        longElt hf hK σ hσ (Or.inr (Or.inr rfl)) r' hr') := by
    apply Subtype.ext
    rw [coe_fieldActor]
    show Units.map (entrywiseHom σ.toRingHom) u₁ = u₁ * (pinnedX TwistTag.D4.tag K rootB s *
      pinnedX TwistTag.D4.tag K rootC r * pinnedX TwistTag.D4.tag K rootD r')
    rw [hEu1', hXZ]
  obtain ⟨hs0, hr0, hr'0⟩ :=
    fieldActor_eq_mul_long_imp hf hK σ hσ ⟨u₁, hu₁C⟩ hu₁' s r r' hs hr hr' hfa
  have hZY1 : Z⁻¹ * (T * (N * Z * N⁻¹) * T⁻¹) = 1 := by
    rw [hXZ, hs0, hr0, hr'0]
    simp only [pinnedX_zero, mul_one]
  have hEu1'' : Units.map (entrywiseHom σ.toRingHom) u₁ = u₁ := by
    rw [hEu1', hZY1, mul_one]
  have hEb_final : Units.map (entrywiseHom σ.toRingHom) (u₁ * T) = u₁ * T := by
    rw [map_mul, hEu1'', hET]
  apply Subtype.ext
  rw [coe_fieldActor, hEgbu, hEb_final, hEu, hgbu]

end CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3
