module

public import CFSG.ClassicalInvolution.Asc77.SU4Torus
public import CFSG.ClassicalInvolution.SmallCases.EndpointsOrthPatternB

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.LieType.Steinberg
  CFSG.ClassicalInvolution.RouteD.SU4Pattern
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair blockSL diagConj2 pair_normalize
  coe_blockSL_three_zero coe_blockSL_three_one)
open scoped MatrixGroups commutatorElement

section Commute

variable {F : Type} [Field F] {X : Type} [Group X]

theorem comm_eq_smul {θ : SL(3, F) →* X} (hker : θ.ker ≤ Subgroup.center SL(3, F))
    (A T : SL(3, F)) (hc : θ A * θ T = θ T * θ A) :
    ∃ z : F, (A : Matrix (Fin 3) (Fin 3) F) * (T : Matrix (Fin 3) (Fin 3) F) =
      z • ((T : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F)) := by
  have h1 : ⁅A, T⁆ ∈ θ.ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr hc
  obtain ⟨z, -, hz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp (hker h1)
  refine ⟨z, ?_⟩
  have e : A * T = ⁅A, T⁆ * (T * A) := by rw [commutatorElement_def]; group
  have e2 := congrArg (fun B : SL(3, F) => (B : Matrix (Fin 3) (Fin 3) F)) e
  simp only [Matrix.SpecialLinearGroup.coe_mul] at e2
  rw [e2, ← hz]
  ext i j
  simp [Matrix.scalar_apply, Matrix.diagonal_mul]

theorem eq_one_of_commutes_blocks {θ : SL(3, F) →* X}
    (hker : θ.ker ≤ Subgroup.center SL(3, F)) {M : SL(2, F)}
    (hc : ∀ s : SL(2, F), θ (blockSL F 3 2 0 (by omega) M) * θ (blockSL F 3 2 1 (by omega) s) =
      θ (blockSL F 3 2 1 (by omega) s) * θ (blockSL F 3 2 0 (by omega) M)) : M = 1 := by
  obtain ⟨z, hz⟩ := comm_eq_smul hker _ _ (hc (sl2Upper 1))
  obtain ⟨z', hz'⟩ := comm_eq_smul hker _ _ (hc (sl2Lower 1))
  have a22 := congrFun (congrFun hz 2) 2
  have a02 := congrFun (congrFun hz 0) 2
  have a12 := congrFun (congrFun hz 1) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, coe_blockSL_three_zero, coe_blockSL_three_one,
    coe_sl2Upper] at a22 a02 a12
  have b22 := congrFun (congrFun hz' 2) 2
  have b20 := congrFun (congrFun hz' 2) 0
  simp [Matrix.mul_apply, Fin.sum_univ_three, coe_blockSL_three_zero, coe_blockSL_three_one,
    coe_sl2Lower] at b22 b20
  have hz1 : z = 1 := a22.symm
  have hM11 : (M : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by rw [a12, hz1]
  have hz1' : z' = 1 := b22.symm
  have hM10 : (M : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    rcases b20 with h | h
    · rw [hz1'] at h
      exact absurd h one_ne_zero
    · exact h
  have hdet := M.2
  rw [Matrix.det_fin_two, hM11, hM10, a02] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hM11, hM10, a02]
  linear_combination hdet

end Commute

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem eq_one_of_commutes_standardPair {F : Type} [Field F] {K₁ K₂ : Subgroup G}
    (hpair : ∃ W, LinearBlockStandardPair F W K₁ K₂) {k : G} (hk : k ∈ K₁)
    (hc : ∀ b ∈ K₂, k * b = b * k) : k = 1 := by
  obtain ⟨W, hW⟩ := hpair
  obtain ⟨θ₃, -, hker, hU, hV⟩ := pair_normalize hW
  rw [← hU] at hk
  obtain ⟨_, ⟨M, rfl⟩, rfl⟩ := hk
  have hM : M = 1 := eq_one_of_commutes_blocks hker fun s => hc _ (by
    rw [← hV]
    exact ⟨_, ⟨s, rfl⟩, rfl⟩)
  rw [hM, map_one, map_one]

theorem exists_square_root_chart (hp2 : p ≠ 2) {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω)
    {x z₁ : G} {K K₁ K₂ : Subgroup G} (hx : IsClassicalMember p f K x)
    (hz₁ : IsClassicalMember p f K₁ z₁) (hK₂ : K₂ ≤ locLayer Ω x)
    (hK₂x : K₂ ≤ Subgroup.centralizer ({x} : Set G))
    (p01 : ∃ W, LinearBlockStandardPair (GaloisField p f) W K K₁)
    (p12 : ∃ W, LinearBlockStandardPair (GaloisField p f) W K₁ K₂) (u : (GaloisField p f)ˣ)
    (hu : u ^ 2 = -1) :
    ∃ (ρ : G) (hρx : ρ * x * ρ⁻¹ = x) (θ : SL(2, GaloisField p f) →* locQuot Ω x),
      ρ * ρ = z₁ ∧ θ.range = locImg Ω x K₂ ∧
        ∀ s, Gaps.locAut hΩ hρx (θ s) = θ (diagConj2 u⁻¹ 1 s) := by
  have hrc : ringChar (GaloisField p f) = p := ringChar.eq (GaloisField p f) p
  have h2 : (2 : GaloisField p f) ≠ 0 := Ring.two_ne_zero (by rw [hrc]; exact hp2)
  obtain ⟨W₂, hW₂⟩ := p12
  obtain ⟨θ₃, -, hker, hU, hV⟩ := pair_normalize hW₂
  set ρ : G := θ₃ (blockSL (GaloisField p f) 3 2 0 (by omega) (torusW u)) with hρ
  have hρK₁ : ρ ∈ K₁ := by
    rw [← hU]
    exact ⟨_, ⟨torusW u, rfl⟩, rfl⟩
  have hz₁mem : z₁ ∈ (blockSL (GaloisField p f) 3 2 0 (by omega)).range.map θ₃ := by
    have : z₁ ∈ K₁ := hz₁.mem
    rwa [← hU] at this
  have hz₁eq : z₁ = θ₃ (blockSL (GaloisField p f) 3 2 0 (by omega) (-1)) :=
    Gaps.eq_block_neg_one h2 hker (by omega) hz₁mem hz₁.orderOf_eq_two
  have hρρ : ρ * ρ = z₁ := by
    rw [hz₁eq, hρ, ← map_mul, ← map_mul, torusW_mul_self hu]
  set φ₂ : SL(2, GaloisField p f) →* G :=
    θ₃.comp (blockSL (GaloisField p f) 3 2 1 (by omega)) with hφ₂
  have hφ₂range : φ₂.range = K₂ := by
    rw [hφ₂, MonoidHom.range_comp]
    exact hV
  have hmem : ∀ s, φ₂ s ∈ locLayer Ω x := fun s => hK₂ (hφ₂range ▸ ⟨s, rfl⟩)
  have hρconj : ∀ s, ρ * φ₂ s * ρ⁻¹ = φ₂ (diagConj2 u⁻¹ 1 s) := by
    intro s
    simp only [hρ, hφ₂, MonoidHom.comp_apply]
    rw [← map_inv, ← map_mul, ← map_mul, blockSL_torusW_conj]
  have hρconj' : ∀ s, ρ⁻¹ * φ₂ s * ρ = φ₂ (diagConj2 u 1 s) := by
    intro s
    simp only [hρ, hφ₂, MonoidHom.comp_apply]
    rw [← map_inv, ← map_mul, ← map_mul, blockSL_torusW_inv_conj]
  have hxK₁ : ∀ k ∈ K₁, x * k * x⁻¹ ∈ K₁ := by
    obtain ⟨W₁, hW₁⟩ := p01
    obtain ⟨θ₂, -, hker₂, hU₂, hV₂⟩ := pair_normalize hW₁
    have hxmem : x ∈ (blockSL (GaloisField p f) 3 2 0 (by omega)).range.map θ₂ := by
      have : x ∈ K := hx.mem
      rwa [← hU₂] at this
    have hxeq : x = θ₂ (blockSL (GaloisField p f) 3 2 0 (by omega) (-1)) :=
      Gaps.eq_block_neg_one h2 hker₂ (by omega) hxmem hx.orderOf_eq_two
    intro k hk
    rw [← hV₂] at hk
    obtain ⟨_, ⟨s, rfl⟩, rfl⟩ := hk
    rw [hxeq, ← map_inv, ← map_mul, ← map_mul, blockSL_neg_one_conj, ← hV₂]
    exact ⟨_, ⟨_, rfl⟩, rfl⟩
  have hxc : ∀ y ∈ K₂, x * y = y * x := fun y hy =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hK₂x hy)).symm
  have hρx' : x * ρ * x⁻¹ = ρ := by
    have hk : x * ρ * x⁻¹ * ρ⁻¹ = 1 := by
      refine eq_one_of_commutes_standardPair (F := GaloisField p f) ⟨W₂, hW₂⟩
        (Subgroup.mul_mem _ (hxK₁ ρ hρK₁) (Subgroup.inv_mem _ hρK₁)) fun b hb => ?_
      rw [← hφ₂range] at hb
      obtain ⟨s, rfl⟩ := hb
      set b₁ : G := φ₂ (diagConj2 u 1 s) with hb₁
      have hb₁K : b₁ ∈ K₂ := hφ₂range ▸ ⟨_, rfl⟩
      have e1 : ρ * b₁ * ρ⁻¹ = φ₂ s := by
        rw [hb₁, ← hρconj']
        group
      have e2 : x * φ₂ s * x⁻¹ = φ₂ s := by
        rw [hxc _ (hφ₂range ▸ ⟨s, rfl⟩), mul_inv_cancel_right]
      have e3 : x⁻¹ * b₁ * x = b₁ := by
        calc x⁻¹ * b₁ * x = x⁻¹ * (b₁ * x) := by group
          _ = x⁻¹ * (x * b₁) := by rw [hxc _ hb₁K]
          _ = b₁ := by group
      calc x * ρ * x⁻¹ * ρ⁻¹ * φ₂ s
          = x * ρ * (x⁻¹ * (ρ⁻¹ * φ₂ s * ρ) * x) * x⁻¹ * ρ⁻¹ := by group
        _ = x * ρ * (x⁻¹ * b₁ * x) * x⁻¹ * ρ⁻¹ := by rw [hρconj']
        _ = x * (ρ * b₁ * ρ⁻¹) * (ρ * x⁻¹ * ρ⁻¹) := by rw [e3]; group
        _ = φ₂ s * (x * ρ * x⁻¹ * ρ⁻¹) := by
            rw [e1]
            calc x * φ₂ s * (ρ * x⁻¹ * ρ⁻¹) = (x * φ₂ s * x⁻¹) * (x * ρ * x⁻¹ * ρ⁻¹) := by group
              _ = φ₂ s * (x * ρ * x⁻¹ * ρ⁻¹) := by rw [e2]
    have := mul_inv_eq_one.mp hk
    exact this
  have hρx : ρ * x * ρ⁻¹ = x := by
    have : x * ρ = ρ * x := by
      have h := hρx'
      rw [mul_inv_eq_iff_eq_mul] at h
      exact h
    rw [mul_inv_eq_iff_eq_mul]
    exact this.symm
  let θ : SL(2, GaloisField p f) →* locQuot Ω x :=
    (Gaps.locMk Ω x).comp (φ₂.codRestrict (locLayer Ω x) hmem)
  refine ⟨ρ, hρx, θ, hρρ, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨⟨φ₂ s, hmem s⟩, Subgroup.mem_subgroupOf.2 (hφ₂range ▸ ⟨s, rfl⟩), rfl⟩
    · rintro ⟨w, hw, rfl⟩
      have hw' : (w : G) ∈ φ₂.range := by rw [hφ₂range]; exact Subgroup.mem_subgroupOf.1 hw
      obtain ⟨s, hs⟩ := hw'
      exact ⟨s, by
        show Gaps.locMk Ω x ⟨φ₂ s, hmem s⟩ = Gaps.locMk Ω x w
        congr 1
        exact Subtype.ext hs⟩
  · intro s
    show Gaps.locAut hΩ hρx (Gaps.locMk Ω x ⟨φ₂ s, hmem s⟩) =
      Gaps.locMk Ω x ⟨φ₂ (diagConj2 u⁻¹ 1 s), hmem _⟩
    rw [Gaps.locAut_mk]
    congr 1
    apply Subtype.ext
    exact hρconj s

end CFSG.ClassicalInvolution.RouteD
