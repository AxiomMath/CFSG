module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeCT
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwap
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizeSwap

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.SeitzReduction.UnitaryPilot (modelToG symm_mem_modelToG mem_modelToG)
open scoped MatrixGroups

namespace SiegelSwapParam

section Factors

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] {n : ℕ}
  {e : L ≃* StatedSp n K} {t : G} (S : SiegelSwapParam e t)

@[expose] noncomputable def fstS (B : Subgroup (StatedSp n K)) : Subgroup G :=
  (B.subgroupOf (siegelLevi K n)).map (S.Ψ.comp (MonoidHom.inl _ _))

@[expose] noncomputable def sndS (B : Subgroup (StatedSp n K)) : Subgroup G :=
  (B.subgroupOf (siegelLevi K n)).map (S.Ψ.comp (MonoidHom.inr _ _))

theorem sndS_le_centralizer_fstS (B B' : Subgroup (StatedSp n K)) :
    S.sndS B' ≤ centralizer (S.fstS B : Set G) := by
  rintro _ ⟨y, -, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨x, -, rfl⟩
  simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply]
  rw [← map_mul, ← map_mul]
  congr 1
  ext <;> simp

theorem map_conj_fstS (B : Subgroup (StatedSp n K)) :
    (S.fstS B).map (MulAut.conj t).toMonoidHom = S.sndS B := by
  rw [fstS, sndS, Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact S.swap x 1

theorem map_prod_eq_fstS_sup_sndS (B : Subgroup (StatedSp n K)) :
    ((B.subgroupOf (siegelLevi K n)).prod (B.subgroupOf (siegelLevi K n))).map S.Ψ =
      S.fstS B ⊔ S.sndS B := by
  apply le_antisymm
  · rintro _ ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
    have hxy : ((x, y) : siegelLevi K n × siegelLevi K n) = (x, 1) * (1, y) := by
      ext <;> simp
    rw [hxy, map_mul]
    exact mul_mem (mem_sup_left ⟨x, hx, rfl⟩) (mem_sup_right ⟨y, hy, rfl⟩)
  · refine sup_le ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨(x, 1), ⟨hx, one_mem _⟩, rfl⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact ⟨(1, y), ⟨one_mem _, hy⟩, rfl⟩

theorem mul_conj_mem_modelToG_of_mem_fstS {B : Subgroup (StatedSp n K)} {x : G}
    (hx : x ∈ S.fstS B) : x * (t * x * t⁻¹) ∈ modelToG e B := by
  obtain ⟨a, ha, rfl⟩ := hx
  simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inl_apply]
  rw [S.swap, ← map_mul, show ((a, 1) : siegelLevi K n × siegelLevi K n) * (1, a) = (a, a) by
    ext <;> simp, S.diag]
  exact symm_mem_modelToG e (mem_subgroupOf.1 ha)

theorem exists_mem_fstS_mul_conj_eq {B : Subgroup (StatedSp n K)} (hB : B ≤ siegelLevi K n)
    {y : G} (hy : y ∈ modelToG e B) : ∃ x ∈ S.fstS B, x * (t * x * t⁻¹) = y := by
  obtain ⟨z, hz, rfl⟩ := (mem_modelToG e).1 hy
  set b : siegelLevi K n := ⟨z, hB hz⟩
  refine ⟨S.Ψ (b, 1), ⟨b, mem_subgroupOf.2 hz, rfl⟩, ?_⟩
  rw [S.swap, ← map_mul, show ((b, 1) : siegelLevi K n × siegelLevi K n) * (1, b) = (b, b) by
    ext <;> simp, S.diag]

theorem ker_comp_inl_le_center :
    (S.Ψ.comp (MonoidHom.inl _ _)).ker ≤ center (siegelLevi K n) := by
  intro x hx
  have hz := S.ker_le (show ((x, 1) : siegelLevi K n × siegelLevi K n) ∈ S.Ψ.ker from hx)
  exact mem_center_iff.2 fun g => by
    have := congrArg Prod.fst (mem_center_iff.1 hz (g, 1))
    simpa using this

theorem fstS_props {B : Subgroup (StatedSp n K)}
    (hB : CFSG.Open.IsQuasisimple (B.subgroupOf (siegelLevi K n))) :
    ⁅S.fstS B, S.fstS B⁆ = S.fstS B ∧ S.fstS B ≠ ⊥ ∧
      ∀ M : Subgroup G, M ≤ S.fstS B → S.fstS B ≤ normalizer (M : Set G) →
        M ≤ centralizer (S.fstS B : Set G) ∨ M = S.fstS B :=
  ⟨UnitaryPilot.commutator_map_eq_of_isQuasisimple hB _,
    UnitaryPilot.map_ne_bot_of_isQuasisimple hB _ S.ker_comp_inl_le_center,
    UnitaryPilot.dichotomy_map_of_isQuasisimple hB _⟩

@[expose] noncomputable def flip : SiegelSwapParam e t where
  Ψ := S.Ψ.comp (MulEquiv.prodComm : siegelLevi K n × siegelLevi K n ≃* _).toMonoidHom
  range_eq := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulEquiv.surjective _),
      ← MonoidHom.range_eq_map, S.range_eq]
  ker_le := by
    intro x hx
    have hz := S.ker_le (show ((x.2, x.1) : siegelLevi K n × siegelLevi K n) ∈ S.Ψ.ker from hx)
    refine mem_center_iff.2 fun g => ?_
    have h1 := mem_center_iff.1 hz (g.2, g.1)
    simp only [Prod.mk_mul_mk] at h1
    exact Prod.ext (congrArg Prod.snd h1) (congrArg Prod.fst h1)
  diag x := S.diag x
  N2 s x := S.N2 s (x.2, x.1)
  swap x y := S.swap y x

theorem flip_fstS (B : Subgroup (StatedSp n K)) : S.flip.fstS B = S.sndS B := by
  rw [fstS, sndS]
  rfl

end Factors

end SiegelSwapParam

section Main

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem simpleRootSL2_one_le_spBlock_three :
    simpleRootSL2 K (1 : Fin 3) ≤ spBlock K ({0}ᶜ : Finset (Fin 3)) :=
  simpleRootSL2_le_spBlock_compl' ⟨by decide, fun _ => by decide⟩

omit [Finite K] [CharP K 2] in
theorem simpleRootSL2_two_le_spBlock_three :
    simpleRootSL2 K (2 : Fin 3) ≤ spBlock K ({0}ᶜ : Finset (Fin 3)) :=
  simpleRootSL2_le_spBlock_compl' ⟨by decide, fun h => absurd h (by decide)⟩

omit [CharP K 2] in
theorem SiegelSwapParam.pieceCore_eq_fstS_sup_sndS {e : L ≃* StatedSp 3 K} {t : G}
    (S : SiegelSwapParam e t) (hK : 4 ≤ Nat.card K) {j : Fin 3} (h : j.val + 1 < 3) :
    pieceCore e ({j} : Finset (Fin 3)) = S.fstS (simpleRootSL2 K j) ⊔ S.sndS (simpleRootSL2 K j) := by
  rw [S.pieceCore_singleton_eq_map hK h, siegelBlock_pair_eq_simpleRootSL2' h,
    S.map_prod_eq_fstS_sup_sndS]

omit [CharP K 2] in
theorem SwapNeighbourParam.pieceCore_eq_fstF_sup_sndF_three {e : L ≃* StatedSp 3 K} {t : G}
    (P : SwapNeighbourParam e t 0) (hK : 4 ≤ Nat.card K) {j : Fin 3} (hj : (0 : Fin 3) ≠ j)
    (hj1 : j.val + 1 < 3 → (0 : Fin 3).val ≠ j.val + 1) :
    pieceCore e ({j} : Finset (Fin 3)) = P.fstF (simpleRootSL2 K j) ⊔ P.sndF (simpleRootSL2 K j) := by
  rw [P.pieceCore_singleton_eq_map hK hj hj1, P.map_prod_eq_fstF_sup_sndF]

theorem SiegelSwapParam.fstS_eq_or_eq {e : L ≃* StatedSp 3 K} {t : G} (hK : 4 ≤ Nat.card K)
    (P₀ : SwapNeighbourParam e t 0) (S : SiegelSwapParam e t) :
    S.fstS (simpleRootSL2 K 1) = P₀.fstF (simpleRootSL2 K 1) ∨
      S.fstS (simpleRootSL2 K 1) = P₀.sndF (simpleRootSL2 K 1) := by
  have hqB := isQuasisimple_simpleRootSL2_subgroupOf hK (simpleRootSL2_one_le_spBlock_three (K := K))
  have hqS := isQuasisimple_simpleRootSL2_subgroupOf hK
    (simpleRootSL2_le_siegelLevi (F := K) (j := (1 : Fin 3)) (by decide))
  have hM : P₀.fstF (simpleRootSL2 K 1) ⊔ P₀.sndF (simpleRootSL2 K 1) =
      S.fstS (simpleRootSL2 K 1) ⊔ S.sndS (simpleRootSL2 K 1) := by
    rw [← P₀.pieceCore_eq_fstF_sup_sndF_three hK (by decide) (fun _ => by decide),
      S.pieceCore_eq_fstS_sup_sndS hK (by decide)]
  obtain ⟨-, -, hn₁⟩ := P₀.fstF_props hqB
  obtain ⟨-, -, hn₂⟩ := P₀.sndF_props hqB
  obtain ⟨hperf, hbot, hnN⟩ := S.fstS_props hqS
  refine F4Pilot.eq_or_eq_of_perfect_of_le_sup (P₀.sndF_le_centralizer_fstF _ _) hn₁ hn₂ hperf
    hbot hnN ?_ ?_
  · rw [hM]
    exact le_sup_left
  · rw [hM]
    exact sup_le le_normalizer
      ((S.sndS_le_centralizer_fstS _ _).trans (centralizer_le_normalizer _))

theorem exists_swapFactors_three_of_siegel (hK : 4 ≤ Nat.card K) (e : L ≃* StatedSp 3 K) {t : G}
    (P₀ : SwapNeighbourParam e t 0) (S : SiegelSwapParam e t)
    (hcomm : ∀ a ∈ pieceCore e ({0} : Finset (Fin 3)), ∀ b ∈ pieceCore e ({2} : Finset (Fin 3)),
      Commute a b) :
    ∃ G₁ : Subgroup G, CFSG.Open.IsQuasisimple G₁ ∧
      G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G) ∧
      G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom = spGlobal e ∧
      (∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L) ∧ ∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y := by
  classical
  obtain ⟨S', hS'⟩ : ∃ S' : SiegelSwapParam e t,
      S'.fstS (simpleRootSL2 K 1) = P₀.fstF (simpleRootSL2 K 1) := by
    rcases S.fstS_eq_or_eq hK P₀ with h | h
    · exact ⟨S, h⟩
    · refine ⟨S.flip, ?_⟩
      rw [S.flip_fstS, ← S.map_conj_fstS, h, P₀.map_conj_sndF]
  have hS'snd : S'.sndS (simpleRootSL2 K 1) = P₀.sndF (simpleRootSL2 K 1) := by
    rw [← S'.map_conj_fstS, hS', P₀.map_conj_fstF]
  have hJ0S : simpleRootSL2 K (0 : Fin 3) ≤ siegelLevi K 3 := simpleRootSL2_le_siegelLevi (by decide)
  have hJ1B := simpleRootSL2_one_le_spBlock_three (K := K)
  have hJ2B := simpleRootSL2_two_le_spBlock_three (K := K)
  have hq0 := isQuasisimple_simpleRootSL2_subgroupOf hK hJ0S
  have hq1 := isQuasisimple_simpleRootSL2_subgroupOf hK hJ1B
  have hq2 := isQuasisimple_simpleRootSL2_subgroupOf hK hJ2B
  have hM0 := S'.pieceCore_eq_fstS_sup_sndS hK (j := (0 : Fin 3)) (by decide)
  have hM1 := P₀.pieceCore_eq_fstF_sup_sndF_three hK (j := (1 : Fin 3)) (by decide)
    (fun _ => by decide)
  have hM2 := P₀.pieceCore_eq_fstF_sup_sndF_three hK (j := (2 : Fin 3)) (by decide)
    (fun h => absurd h (by decide))
  set U : Fin 3 → Subgroup G :=
    ![S'.fstS (simpleRootSL2 K 0), P₀.fstF (simpleRootSL2 K 1), P₀.fstF (simpleRootSL2 K 2)]
    with hUdef
  set V : Fin 3 → Subgroup G :=
    ![S'.sndS (simpleRootSL2 K 0), P₀.sndF (simpleRootSL2 K 1), P₀.sndF (simpleRootSL2 K 2)]
    with hVdef
  have hmapU : ∀ j, (U j).map (MulAut.conj t).toMonoidHom = V j := by
    intro j
    fin_cases j
    · exact S'.map_conj_fstS _
    · exact P₀.map_conj_fstF _
    · exact P₀.map_conj_fstF _
  have hUV : ∀ j, U j ⊔ V j = pieceCore e ({j} : Finset (Fin 3)) := by
    intro j
    fin_cases j
    · exact hM0.symm
    · exact hM1.symm
    · exact hM2.symm
  have hpair : ∀ i j, (U j).map (MulAut.conj t).toMonoidHom ≤ centralizer (U i : Set G) := by
    intro i j
    rw [hmapU j]
    fin_cases i <;> fin_cases j
    · exact S'.sndS_le_centralizer_fstS _ _
    · change P₀.sndF (simpleRootSL2 K 1) ≤ centralizer (S'.fstS (simpleRootSL2 K 0) : Set G)
      rw [← hS'snd]
      exact S'.sndS_le_centralizer_fstS _ _
    · change P₀.sndF (simpleRootSL2 K 2) ≤ centralizer (S'.fstS (simpleRootSL2 K 0) : Set G)
      intro b hb
      rw [mem_centralizer_iff]
      intro a ha
      exact (hcomm a (by rw [hM0]; exact mem_sup_left ha) b (by rw [hM2]; exact mem_sup_right hb)).eq
    · change S'.sndS (simpleRootSL2 K 0) ≤ centralizer (P₀.fstF (simpleRootSL2 K 1) : Set G)
      rw [← hS']
      exact S'.sndS_le_centralizer_fstS _ _
    · exact P₀.sndF_le_centralizer_fstF _ _
    · exact P₀.sndF_le_centralizer_fstF _ _
    · change S'.sndS (simpleRootSL2 K 0) ≤ centralizer (P₀.fstF (simpleRootSL2 K 2) : Set G)
      intro b hb
      rw [mem_centralizer_iff]
      intro a ha
      exact (hcomm b (by rw [hM0]; exact mem_sup_right hb) a
        (by rw [hM2]; exact mem_sup_left ha)).eq.symm
    · exact P₀.sndF_le_centralizer_fstF _ _
    · exact P₀.sndF_le_centralizer_fstF _ _
  have h₁₂ := LinearPilot.map_conj_iSup_le_centralizer hpair
  have hperf : ⁅⨆ j, U j, ⨆ j, U j⁆ = ⨆ j, U j :=
    LinearPilot.commutator_iSup_eq_of_forall U fun j => by
      fin_cases j
      · exact (S'.fstS_props hq0).1
      · exact (P₀.fstF_props hq1).1
      · exact (P₀.fstF_props hq2).1
  have hS : IsSimpleGroup L :=
    (e.symm.isSimpleGroup_congr).1 (isSimpleGroup_statedSp_of_four_le hK (by omega))
  have hδ : ∀ x ∈ ⨆ j, U j, x * (t * x * t⁻¹) ∈ L :=
    LinearPilot.mul_conj_mem_of_mem_iSup h₁₂ fun j x hx => by
      fin_cases j
      · exact UnitaryPilot.modelToG_le e _ (S'.mul_conj_mem_modelToG_of_mem_fstS hx)
      · exact UnitaryPilot.modelToG_le e _ (P₀.mul_conj_mem_modelToG_of_mem_fstF hx)
      · exact UnitaryPilot.modelToG_le e _ (P₀.mul_conj_mem_modelToG_of_mem_fstF hx)
  have hsurj : ∀ y ∈ L, ∃ x ∈ ⨆ j, U j, x * (t * x * t⁻¹) = y := by
    intro y hy
    have hy' : y ∈ ⨆ j : Fin 3, modelToG e (simpleRootSL2 K j) := by
      rw [← UnitaryPilot.modelToG_iSup, iSup_simpleRootSL2_eq_top (by omega),
        UnitaryPilot.modelToG_top]
      exact hy
    refine LinearPilot.exists_mul_conj_eq_of_mem_iSup h₁₂ (fun j z hz => ?_) y hy'
    fin_cases j
    · obtain ⟨x, hx, hxz⟩ := S'.exists_mem_fstS_mul_conj_eq hJ0S hz
      exact ⟨x, mem_iSup_of_mem (0 : Fin 3) hx, hxz⟩
    · obtain ⟨x, hx, hxz⟩ := P₀.exists_mem_fstF_mul_conj_eq hJ1B hz
      exact ⟨x, mem_iSup_of_mem (1 : Fin 3) hx, hxz⟩
    · obtain ⟨x, hx, hxz⟩ := P₀.exists_mem_fstF_mul_conj_eq hJ2B hz
      exact ⟨x, mem_iSup_of_mem (2 : Fin 3) hx, hxz⟩
  refine ⟨⨆ j, U j, LinearPilot.isQuasisimple_of_linearSwapDiag h₁₂ hperf hS hδ hsurj, h₁₂, ?_,
    hδ, hsurj⟩
  rw [Subgroup.map_iSup, ← iSup_sup_eq, spGlobal]
  exact iSup_congr fun j => by rw [hmapU j, hUV j]

end Main

end CFSG.SeitzReduction.SymplecticPilot
