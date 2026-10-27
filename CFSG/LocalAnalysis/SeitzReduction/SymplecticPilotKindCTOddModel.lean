module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTOddRigid
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphLinearNeighbour
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelPiece

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open LinearFlag
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeafProof (fixedSubgroupCongrEquiv)
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (statedSpMap statedSpMap_injective)

section Model

variable {m : ℕ} {F : Type} [Field F] [CharP F 2]

theorem ctEmbed_statedSpMap {ε : ℕ} {K : Type} [Field K] [CharP K 2] (σ : K →+* F)
    (y : StatedSp m K) :
    ctEmbed ε (statedSpMap σ m y) = SpecialLinearGroup.map σ (ctEmbed ε y) := by
  apply Subtype.ext
  ext a b
  obtain ⟨w, rfl⟩ := (q2Coord m ε).surjective a
  obtain ⟨w', rfl⟩ := (q2Coord m ε).surjective b
  rw [ctEmbed_apply_q2Coord]
  change _ = σ (((ctEmbed ε y : SpecialLinearGroup (Fin (2 * m + ε)) K) :
    Matrix (Fin (2 * m + ε)) (Fin (2 * m + ε)) K) (q2Coord m ε w) (q2Coord m ε w'))
  rw [ctEmbed_apply_q2Coord]
  rcases w with u | i <;> rcases w' with v | j
  · rw [fromBlocks_apply₁₁, fromBlocks_apply₁₁, mat_apply, mat_apply, F4Pilot.coe_statedSpMap,
      F4Pilot.coe_map_GL]
    rfl
  · simp
  · simp
  · rw [fromBlocks_apply₂₂, fromBlocks_apply₂₂, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

variable (m F) in
@[expose] noncomputable def ctGramGL : GL (Fin (2 * m + 1)) F :=
  SpecialLinearGroup.toGL (ctEmbed 1 (q2SpJ (N := m) (K := F)))

theorem coe_ctGramGL :
    ((ctGramGL m F : GL (Fin (2 * m + 1)) F) : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) F) =
      q2GramMat 1 := by
  change q2EmbedMat 1 (mat m F q2SpJ) = q2GramMat 1
  rw [mat_q2SpJ]
  rfl

theorem coe_ctGramGL_inv :
    (((ctGramGL m F)⁻¹ : GL (Fin (2 * m + 1)) F) : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) F) =
      q2GramMat 1 := by
  rw [ctGramGL, ← map_inv, ctEmbed_q2SpJ_inv]
  exact coe_ctGramGL

variable (m F) in
@[expose] noncomputable def ctGraphPSL : MulAut (projectiveSL (2 * m + 1) F) :=
  conjAut (2 * m + 1) F (ctGramGL m F) * dualAut (2 * m + 1) F

theorem ctGraphPSL_proj (x : SpecialLinearGroup (Fin (2 * m + 1)) F) :
    ctGraphPSL m F (proj (2 * m + 1) F x) = proj (2 * m + 1) F (ctGraph 1 x) := by
  rw [ctGraphPSL, MulAut.mul_apply, dualAut_proj, conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation, coe_ctGraph, coe_ctGramGL, coe_ctGramGL_inv]
  rfl

theorem ctGraphPSL_mul_self : ctGraphPSL m F * ctGraphPSL m F = 1 := by
  ext1 z
  obtain ⟨x, rfl⟩ := proj_surjective (2 * m + 1) F z
  rw [MulAut.mul_apply, ctGraphPSL_proj, ctGraphPSL_proj, ctGraph_ctGraph, MulAut.one_apply]

variable (m F) in
@[expose] noncomputable def ctOddPSL : StatedSp m F →* projectiveSL (2 * m + 1) F :=
  (proj (2 * m + 1) F).comp (ctEmbed 1)

theorem ctOddPSL_apply (y : StatedSp m F) :
    ctOddPSL m F y = proj (2 * m + 1) F (ctEmbed 1 y) := rfl

theorem ctOddPSL_injective : Function.Injective (ctOddPSL m F) := by
  rw [injective_iff_map_eq_one]
  intro y hy
  obtain ⟨c, -, hc⟩ := proj_eq_one_iff.1 hy
  have h1 := congrFun (congrFun hc (ctV m)) (ctV m)
  rw [ctEmbed_apply_q2Coord, fromBlocks_apply₂₂, Matrix.one_apply_eq, scalar_apply,
    diagonal_apply_eq] at h1
  have hc1 : (ctEmbed 1 y : SpecialLinearGroup (Fin (2 * m + 1)) F) = 1 := by
    apply Subtype.ext
    rw [hc, ← h1, map_one]
    rfl
  exact ctEmbed_injective (by rw [hc1, map_one])

theorem ctGraph_of_mem_scalars {N ε : ℕ} {K : Type} [Field K] [CharP K 2]
    {w : SpecialLinearGroup (Fin (2 * N + ε)) K} (hw : w ∈ scalars (2 * N + ε) K) :
    ctGraph ε w = w⁻¹ := by
  obtain ⟨d, -, hd⟩ := inv_mem hw
  apply Subtype.ext
  rw [coe_ctGraph, hd, scalar_apply, diagonal_transpose, ← scalar_apply,
    ← (scalar_commute (d : K) (fun _ => Commute.all _ _) (q2GramMat ε)).eq, Matrix.mul_assoc,
    q2GramMat_mul_self, Matrix.mul_one]

theorem fixedSubgroup_ctGraphPSL : fixedSubgroup (ctGraphPSL m F) = (ctOddPSL m F).range := by
  ext z
  constructor
  · intro hz
    obtain ⟨x, rfl⟩ := proj_surjective (2 * m + 1) F z
    have hz' : proj (2 * m + 1) F (ctGraph 1 x) = proj (2 * m + 1) F x := by
      rw [← ctGraphPSL_proj]
      exact hz
    set s := (ctGraph 1 x)⁻¹ * x with hs
    have hsmem : s ∈ scalars (2 * m + 1) F := proj_eq_proj_iff.1 hz'
    clear_value s
    obtain ⟨c, hcn, hc⟩ := hsmem
    have hμ : (c ^ m) ^ (2 * m + 1) = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hcn, one_pow]
    set w := scalarElement (c ^ m) hμ with hw
    have hwmem : w ∈ scalars (2 * m + 1) F := scalarElement_mem_scalars _ hμ
    clear_value w
    have hsww : s * (w * w) = 1 := by
      have hc3 : c * (c ^ m * c ^ m) = 1 := by
        rw [← pow_add, ← pow_succ', show m + m + 1 = 2 * m + 1 by ring, hcn]
      have hmat : ((s * (w * w) : SpecialLinearGroup (Fin (2 * m + 1)) F) :
          Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) F) =
          ((1 : SpecialLinearGroup (Fin (2 * m + 1)) F) :
            Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) F) := by
        rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hc, hw,
          coe_scalarElement, ← map_mul, ← map_mul, ← Units.val_mul, ← Units.val_mul, hc3,
          Units.val_one, map_one, Matrix.SpecialLinearGroup.coe_one]
      exact Subtype.ext hmat
    have hsinv : s⁻¹ = w * w := inv_eq_of_mul_eq_one_right hsww
    have hfix : ctGraph 1 (x * w) = x * w := by
      rw [map_mul, ctGraph_of_mem_scalars hwmem]
      have hx : ctGraph 1 x = x * s⁻¹ := by
        rw [hs, _root_.mul_inv_rev, inv_inv, mul_inv_cancel_left]
      rw [hx, hsinv, mul_assoc, mul_assoc, mul_inv_cancel, mul_one]
    obtain ⟨y, hy⟩ := exists_eq_ctEmbed_of_ctGraph_eq le_rfl hfix
    refine ⟨y, ?_⟩
    rw [ctOddPSL_apply, hy, map_mul, proj_eq_one_iff.2 hwmem, mul_one]
  · rintro ⟨y, rfl⟩
    change ctGraphPSL m F (proj (2 * m + 1) F (ctEmbed 1 y)) = proj (2 * m + 1) F (ctEmbed 1 y)
    rw [ctGraphPSL_proj, ctGraph_ctEmbed]

end Model

section Normal

variable {m : ℕ} {F : Type} [Field F] [CharP F 2]

theorem exists_conjAut_eq_ctGraphPSL [Finite F] (hm : 1 ≤ m)
    {e : ℕ} (he : 1 ≤ e) (hF : Nat.card F = 2 ^ e) {α : MulAut (projectiveSL (2 * m + 1) F)}
    (hα2 : α ^ 2 = 1) (hαE : α ∉ semilinearAutGroup (2 * m + 1) F) {m' f : ℕ}
    (hfix : LieModel (fixedSubgroup α) .PSp m' 2 f) :
    ∃ H : GL (Fin (2 * m + 1)) F,
      α = conjAut (2 * m + 1) F H * ctGraphPSL m F * (conjAut (2 * m + 1) F H)⁻¹ := by
  obtain ⟨H, C, hC, hαHC⟩ := exists_conjAut_dualAut_normalForm (by omega : 3 ≤ 2 * m + 1) he hF
    hα2 hαE hfix
  have hC1 : C = 1 := by
    rcases hC with h1 | ⟨r', hr', -⟩
    · exact Units.ext h1
    · omega
  rw [hC1, map_one, one_mul] at hαHC
  have hP2 : (conjAut (2 * m + 1) F (ctGramGL m F) * dualAut (2 * m + 1) F) ^ 2 = 1 := by
    rw [sq]
    exact ctGraphPSL_mul_self
  obtain ⟨-, ⟨H', C', -, hconj, hC'⟩, -⟩ :=
    UnitaryHigher.even_linear_pure_graph_involution_normal_forms he hF (by omega : 3 ≤ 2 * m + 1)
      (ctGramGL m F) hP2
  have hC'1 : C' = 1 := by
    rcases hC' with ⟨h1, -⟩ | ⟨r', hr', -, -⟩
    · exact Units.ext h1
    · omega
  rw [hC'1, map_one, one_mul] at hconj
  refine ⟨H * H'⁻¹, ?_⟩
  rw [hαHC, map_mul, map_inv, ctGraphPSL, hconj]
  group

theorem fieldAut_ctOddPSL (ρ : F ≃+* F) (x : StatedSp m F) :
    fieldAut (2 * m + 1) F ρ (ctOddPSL m F x) =
      ctOddPSL m F (statedSpMap (ρ : F →+* F) m x) := by
  rw [ctOddPSL_apply, fieldAut_proj, ctOddPSL_apply, ctEmbed_statedSpMap]
  rfl

theorem exists_mulAut_ctOddPSL {K : Type} [Field K] [Finite K] [CharP K 2] (hm : 3 ≤ m)
    (σ : K ≃+* F) (δ : MulAut (StatedSp m K)) :
    ∃ δ' : MulAut (projectiveSL (2 * m + 1) F),
      ∀ g, δ' (ctOddPSL m F (statedSpMap (σ : K →+* F) m g)) =
        ctOddPSL m F (statedSpMap (σ : K →+* F) m (δ g)) := by
  obtain ⟨s, ρ₀, hδ⟩ := exists_eq_conj_mul_fieldSp hm δ
  set ρ' : F ≃+* F := (σ.symm.trans ρ₀).trans σ with hρ'
  have hρ'σ : (ρ' : F →+* F).comp (σ : K →+* F) = (σ : K →+* F).comp (ρ₀ : K →+* K) := by
    ext c
    simp [hρ']
  refine ⟨MulAut.conj (ctOddPSL m F (statedSpMap (σ : K →+* F) m s)) * fieldAut (2 * m + 1) F ρ',
    fun g => ?_⟩
  rw [MulAut.mul_apply, fieldAut_ctOddPSL, F4Pilot.statedSpMap_comp, hρ'σ,
    ← F4Pilot.statedSpMap_comp, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul,
    ← map_inv, ← map_mul, ← map_mul, hδ, MulAut.mul_apply, MulAut.conj_apply,
    F4Pilot.fieldSp_eq_statedSpMap]

theorem exists_mulEquiv_ctOddPSL_eq [Finite F] {K : Type} [Field K]
    [Finite K] [CharP K 2] {f : ℕ} (hm : 3 ≤ m) (hf : 2 ≤ f) (hF : Nat.card F = 2 ^ f)
    (σ : K ≃+* F) {M : Type} [Group M] (ψ : projectiveSL (2 * m + 1) F ≃* M) {θ : MulAut M}
    (hθ : θ * θ = 1) (hθE : MulAut.congr ψ.symm θ ∉ semilinearAutGroup (2 * m + 1) F)
    (hθfix : LieModel (fixedSubgroup θ) .PSp m 2 f) (ε : StatedSp m K →* M)
    (hε : Function.Injective ε) (hεr : ε.range = perfectCore (fixedSubgroup θ)) :
    ∃ ψ' : projectiveSL (2 * m + 1) F ≃* M,
      ∀ g, ψ' (ctOddPSL m F (statedSpMap (σ : K →+* F) m g)) = ε g := by
  have hF4 : 4 ≤ Nat.card F := (LinearPilot.four_le_card_iff_two_le hF).2 hf
  set θ' := MulAut.congr ψ.symm θ with hθ'
  have hθ'app : ∀ y, θ' y = ψ.symm (θ (ψ y)) := fun _ => rfl
  have hθ'2 : θ' ^ 2 = 1 := by rw [sq, hθ', ← map_mul, hθ, map_one]
  have hθ'fix : LieModel (fixedSubgroup θ') .PSp m 2 f :=
    LieType.CurtisTits.lieModel_of_mulEquiv (fixedSubgroupCongrEquiv ψ.symm θ) hθfix
  obtain ⟨H, hθ'H⟩ := exists_conjAut_eq_ctGraphPSL (by omega) (by omega : 1 ≤ f) hF hθ'2 hθE
    hθ'fix
  set c := conjAut (2 * m + 1) F H with hc
  set ψ₁ : projectiveSL (2 * m + 1) F ≃* M := (c : projectiveSL (2 * m + 1) F ≃* _).trans ψ
    with hψ₁
  have hψ₁app : ∀ x, ψ₁ x = ψ (c x) := fun _ => rfl
  have hθψ₁ : ∀ x, θ (ψ₁ x) = ψ₁ (ctGraphPSL m F x) := by
    intro x
    have h1 : θ' (c x) = c (ctGraphPSL m F x) := by
      rw [hθ'H]
      simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply]
    rw [hθ'app] at h1
    rw [hψ₁app, hψ₁app, ← h1, MulEquiv.apply_symm_apply]
  have hfixθ : fixedSubgroup θ = (ctOddPSL m F).range.map ψ₁.toMonoidHom := by
    rw [← fixedSubgroup_ctGraphPSL]
    ext y
    obtain ⟨x, rfl⟩ := ψ₁.surjective y
    rw [mem_map_equiv, ψ₁.symm_apply_apply]
    change θ (ψ₁ x) = ψ₁ x ↔ ctGraphPSL m F x = x
    rw [hθψ₁]
    exact ψ₁.injective.eq_iff
  have htop : ⁅(⊤ : Subgroup (StatedSp m F)), (⊤ : Subgroup (StatedSp m F))⁆ = ⊤ := by
    have := isPerfect_statedSp_of_four_le hF4 m
    rw [← _root_.commutator_def]
    exact Group.IsPerfect.commutator_eq_top
  have hperf : ⁅(ctOddPSL m F).range.map ψ₁.toMonoidHom,
      (ctOddPSL m F).range.map ψ₁.toMonoidHom⁆ = (ctOddPSL m F).range.map ψ₁.toMonoidHom := by
    rw [← map_commutator, MonoidHom.range_eq_map, ← map_commutator, htop]
  have hrange : ε.range = (ψ₁.toMonoidHom.comp
      ((ctOddPSL m F).comp (statedSpMap (σ : K →+* F) m))).range := by
    rw [hεr, hfixθ, CFSG.Quasithin.perfectCore_eq_self_of_perfect hperf, MonoidHom.range_comp,
      MonoidHom.range_comp, MonoidHom.range_eq_top.2 (statedSpMap_surjective σ),
      ← MonoidHom.range_eq_map]
  have hinj₁ : Function.Injective (ψ₁.toMonoidHom.comp
      ((ctOddPSL m F).comp (statedSpMap (σ : K →+* F) m))) :=
    ψ₁.injective.comp (ctOddPSL_injective.comp (statedSpMap_injective _ m))
  set δ₀ : MulAut (StatedSp m K) := ((MonoidHom.ofInjective hε).trans
    (MulEquiv.subgroupCongr hrange)).trans (MonoidHom.ofInjective hinj₁).symm with hδ₀def
  have hδ₀ : ∀ g, ψ₁ (ctOddPSL m F (statedSpMap (σ : K →+* F) m (δ₀ g))) = ε g := by
    intro g
    have h1 := (MonoidHom.ofInjective hinj₁).apply_symm_apply
      (MulEquiv.subgroupCongr hrange (MonoidHom.ofInjective hε g))
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  obtain ⟨δ', hδ'⟩ := exists_mulAut_ctOddPSL hm σ δ₀
  refine ⟨δ'.trans ψ₁, fun g => ?_⟩
  change ψ₁ (δ' (ctOddPSL m F (statedSpMap (σ : K →+* F) m g))) = ε g
  rw [hδ', hδ₀]

end Normal

end CFSG.SeitzReduction.SymplecticPilot
