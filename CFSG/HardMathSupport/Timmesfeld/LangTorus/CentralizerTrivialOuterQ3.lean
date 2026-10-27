module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.AnyKindThreeDefs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialOuter
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialQ3Comp

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Classical CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.RootAut
open scoped MatrixGroups commutatorElement

set_option linter.unusedSectionVars false

section Heis

variable {G : Type*} [Group G] {R : Type*} [CommRing R]

structure OuterHeis (A B C : R → G) (ε : R) : Prop where
  addA : ∀ a a', A (a + a') = A a * A a'
  addB : ∀ b b', B (b + b') = B b * B b'
  addC : ∀ c c', C (c + c') = C c * C c'
  commAC : ∀ a c, Commute (A a) (C c)
  commBC : ∀ b c, Commute (B b) (C c)
  commAB : ∀ a b, ⁅A a, B b⁆ = C (ε * a * b)

namespace OuterHeis

variable {A B C : R → G} {ε : R} (H : OuterHeis A B C ε)
include H

theorem C_zero : C 0 = 1 := by
  have h := H.addC 0 0
  rw [add_zero] at h
  exact (mul_eq_left.1 h.symm)

theorem C_neg (c : R) : C (-c) = (C c)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← H.addC, add_neg_cancel, H.C_zero]

theorem A_zero : A 0 = 1 := by
  have h := H.addA 0 0
  rw [add_zero] at h
  exact (mul_eq_left.1 h.symm)

theorem B_zero : B 0 = 1 := by
  have h := H.addB 0 0
  rw [add_zero] at h
  exact (mul_eq_left.1 h.symm)

theorem AB (a b : R) : A a * B b = C (ε * a * b) * (B b * A a) := by
  have h := H.commAB a b
  rw [commutatorElement_def] at h
  calc A a * B b = A a * B b * (A a)⁻¹ * (B b)⁻¹ * (B b * A a) := by group
    _ = C (ε * a * b) * (B b * A a) := by rw [h]

theorem BA (a b : R) : B b * A a = C (-(ε * a * b)) * (A a * B b) := by
  rw [H.AB a b, H.C_neg, ← mul_assoc, inv_mul_cancel, one_mul]

theorem mul_normal (a₁ b₁ c₁ a₂ b₂ c₂ : R) :
    A a₁ * B b₁ * C c₁ * (A a₂ * B b₂ * C c₂) =
      A (a₁ + a₂) * B (b₁ + b₂) * C (c₁ + c₂ - ε * a₂ * b₁) := by
  have hc₁ : Commute (C c₁) (A a₂ * B b₂) :=
    ((H.commAC a₂ c₁).symm.mul_right (H.commBC b₂ c₁).symm)
  have hx : Commute (C (-(ε * a₂ * b₁))) (A a₁) := (H.commAC a₁ _).symm
  have e1 : A a₁ * B b₁ * C c₁ * (A a₂ * B b₂ * C c₂) =
      A a₁ * (B b₁ * A a₂) * B b₂ * (C c₁ * C c₂) := by
    calc A a₁ * B b₁ * C c₁ * (A a₂ * B b₂ * C c₂) =
          A a₁ * B b₁ * (C c₁ * (A a₂ * B b₂)) * C c₂ := by simp only [mul_assoc]
      _ = A a₁ * B b₁ * (A a₂ * B b₂ * C c₁) * C c₂ := by rw [hc₁.eq]
      _ = A a₁ * (B b₁ * A a₂) * B b₂ * (C c₁ * C c₂) := by simp only [mul_assoc]
  rw [e1, H.BA, ← H.addC]
  calc A a₁ * (C (-(ε * a₂ * b₁)) * (A a₂ * B b₁)) * B b₂ * C (c₁ + c₂) =
        (A a₁ * C (-(ε * a₂ * b₁))) * (A a₂ * (B b₁ * B b₂)) * C (c₁ + c₂) := by
        simp only [mul_assoc]
    _ = (C (-(ε * a₂ * b₁)) * A a₁) * (A a₂ * (B b₁ * B b₂)) * C (c₁ + c₂) := by
        rw [hx.eq]
    _ = C (-(ε * a₂ * b₁)) * ((A a₁ * A a₂) * (B b₁ * B b₂)) * C (c₁ + c₂) := by
        simp only [mul_assoc]
    _ = ((A a₁ * A a₂) * (B b₁ * B b₂)) * C (-(ε * a₂ * b₁)) * C (c₁ + c₂) := by
        rw [(((H.commAC _ _).mul_left (H.commAC _ _)).mul_left
          ((H.commBC _ _).mul_left (H.commBC _ _))).symm.eq]
    _ = A (a₁ + a₂) * B (b₁ + b₂) * C (c₁ + c₂ - ε * a₂ * b₁) := by
        rw [H.addA, H.addB, mul_assoc _ (C _), ← H.addC]
        congr 2
        ring

theorem inv_normal (a b c : R) :
    (A a * B b * C c)⁻¹ = A (-a) * B (-b) * C (-c - ε * a * b) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [H.mul_normal, add_neg_cancel, add_neg_cancel, H.A_zero, H.B_zero, one_mul, one_mul]
  convert H.C_zero using 2
  ring

theorem commutator_normal (a₁ b₁ c₁ a₂ b₂ c₂ : R) :
    ⁅A a₁ * B b₁ * C c₁, A a₂ * B b₂ * C c₂⁆ = C (ε * (a₁ * b₂ - a₂ * b₁)) := by
  rw [commutatorElement_def, H.inv_normal, H.inv_normal, H.mul_normal, H.mul_normal,
    H.mul_normal]
  have e1 : a₁ + a₂ + -a₁ + -a₂ = 0 := by ring
  have e2 : b₁ + b₂ + -b₁ + -b₂ = 0 := by ring
  rw [e1, e2, H.A_zero, H.B_zero, one_mul, one_mul]
  congr 1
  ring

theorem commutator_inv_conj (h3 : (3 : R) = 0) {h : G} (hA : ∀ a, h * A a * h⁻¹ = A (-a))
    (hB : ∀ b, h * B b * h⁻¹ = B (-b)) (hC : ∀ c, h * C c * h⁻¹ = C c) (a b : R) :
    ⁅h, A a * B b * C (ε * a * b)⁆ = A a * B b * C (ε * a * b) := by
  have hconj : h * (A a * B b * C (ε * a * b)) * h⁻¹ = A (-a) * B (-b) * C (ε * a * b) := by
    calc h * (A a * B b * C (ε * a * b)) * h⁻¹ =
          (h * A a * h⁻¹) * (h * B b * h⁻¹) * (h * C (ε * a * b) * h⁻¹) := by group
      _ = A (-a) * B (-b) * C (ε * a * b) := by rw [hA, hB, hC]
  rw [commutatorElement_def, hconj, H.inv_normal, H.mul_normal]
  have e1 : -a + -a = a := by linear_combination (-a) * h3
  have e2 : -b + -b = b := by linear_combination (-b) * h3
  rw [e1, e2]
  congr 2
  linear_combination (-(ε * a * b)) * h3

theorem mul_AB (a₁ b₁ a₂ b₂ : R) :
    A a₁ * B b₁ * (A a₂ * B b₂) = A (a₁ + a₂) * B (b₁ + b₂) * C (-(ε * a₂ * b₁)) := by
  have h := H.mul_normal a₁ b₁ 0 a₂ b₂ 0
  rw [H.C_zero, mul_one, mul_one] at h
  rw [h]
  congr 2
  ring

end OuterHeis

end Heis

section Block

variable {τ : Tag} {L : Type} [Field L]

theorem outer_iform_self_of_simplyLaced (hsl : SimplyLacedTag τ) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) : iform γ γ = 2 := by
  obtain ⟨j, hj⟩ := iform_self_of_isRoot hγ
  rcases hsl with rfl | rfl | rfl | rfl <;> simpa [Tag.symmetrizer] using hj

theorem outer_rootSpan_le_adjoint (Ψ : Set (Fin τ.rank → ℤ)) :
    rootSpan τ L Ψ ≤ adjointGroup τ L :=
  iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α

theorem outer_block_heis (hsl : SimplyLacedTag τ) {γ γ' : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hγ' : IsRoot τ γ') (h1 : iform γ γ' = -1) :
    IsRoot τ (γ + γ') ∧ ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      OuterHeis (pinnedX τ L γ) (pinnedX τ L γ') (pinnedX τ L (γ + γ')) (ε : L) := by
  have hn : iform γ γ = 2 := outer_iform_self_of_simplyLaced hsl hγ
  have hn' : iform γ' γ' = 2 := outer_iform_self_of_simplyLaced hsl hγ'
  have hne : γ ≠ γ' := fun h => by rw [← h] at h1; omega
  have hne' : γ ≠ -γ' := fun h => by rw [h, outer_iform_neg_left] at h1; omega
  have hω : IsRoot τ (γ + γ') := isRoot_add_of_iform_neg hγ hγ' hne' (by omega)
  have hsl' : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := hsl
  obtain ⟨h₁, -⟩ := simply_laced_root_commutator_unit.{0} τ hsl' hγ hγ' hne hne'
  obtain ⟨hε, hF⟩ := h₁ hω
  have hωn : iform (γ + γ') (γ + γ') = 2 := outer_iform_self_of_simplyLaced hsl hω
  have hcomm : ∀ β, IsRoot τ β → iform β (γ + γ') = 1 → ∀ a c : L,
      Commute (pinnedX τ L β a) (pinnedX τ L (γ + γ') c) := by
    intro β hβ h a c
    have hβn := outer_iform_self_of_simplyLaced hsl hβ
    have hne1 : β ≠ γ + γ' := fun e => by rw [e, hωn] at h; omega
    have hne2 : β ≠ -(γ + γ') := fun e => by rw [e, outer_iform_neg_left, hωn] at h; omega
    have hnr : ¬ IsRoot τ (β + (γ + γ')) := fun hr => by
      have := outer_iform_self_of_simplyLaced hsl hr
      rw [iform_add_left, iform_add_right β β (γ + γ'), iform_add_right (γ + γ') β (γ + γ'),
        hβn, h, iform_comm (γ + γ') β, h, hωn] at this
      omega
    obtain ⟨-, h₂⟩ := simply_laced_root_commutator_unit.{0} τ hsl' hβ hω hne1 hne2
    exact h₂ hnr L _ (Subgroup.subset_closure ⟨a, rfl⟩) _ (Subgroup.subset_closure ⟨c, rfl⟩)
  have hγω : iform γ (γ + γ') = 1 := by rw [iform_add_right, hn, h1]; norm_num
  have hγ'ω : iform γ' (γ + γ') = 1 := by rw [iform_add_right, iform_comm, h1, hn']; norm_num
  refine ⟨hω, commConst τ γ γ' (1, 1), hε, ⟨fun a a' => pinnedX_add τ L γ a a',
    fun b b' => pinnedX_add τ L γ' b b', fun c c' => pinnedX_add τ L (γ + γ') c c',
    fun a c => hcomm γ hγ hγω a c, fun b c => hcomm γ' hγ' hγ'ω b c, fun a b => ?_⟩⟩
  rw [hF L a b]

end Block

section BlockData

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)

theorem outer_exists_commutator_neg_one {K : Type*} [Field K] (h3 : (3 : K) = 0) :
    ∃ I J : SL(2, K), I * J * I⁻¹ * J⁻¹ = -1 := by
  have hdetI : (!![(0 : K), 1; -1, 0]).det = 1 := by rw [Matrix.det_fin_two_of]; ring
  have hdetJ : (!![(1 : K), 1; 1, -1]).det = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination (-1 : K) * h3
  set I : SL(2, K) := ⟨!![0, 1; -1, 0], hdetI⟩ with hIdef
  set J : SL(2, K) := ⟨!![1, 1; 1, -1], hdetJ⟩ with hJdef
  have hIc : (I : Matrix (Fin 2) (Fin 2) K) = !![0, 1; -1, 0] := rfl
  have hJc : (J : Matrix (Fin 2) (Fin 2) K) = !![1, 1; 1, -1] := rfl
  have hIJ : I * J = -(J * I) := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, hIc, hJc]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨I, J, ?_⟩
  calc I * J * I⁻¹ * J⁻¹ = I * J * (J * I)⁻¹ := by rw [mul_inv_rev, mul_assoc]
    _ = -1 := by rw [hIJ, neg_mul, mul_inv_cancel]

theorem outer_conj_mem_model {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a))
    (hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1)
    {z₀ : ModGL τ L}
    (hz₀ : ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      z₀ * g * z₀⁻¹ ∈ rootSpan τ L (componentRoots (rootCharHom a) i))
    {φ₁ : ModGL τ L →* ModGL τ L}
    (hφ₁ : ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      iterHom S.D.step (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
        (z₀ * g * z₀⁻¹) = z₀ * φ₁ g * z₀⁻¹)
    {g : ModGL τ L} (hg : g ∈ rootSpan τ L (componentRoots (rootCharHom a) i))
    (hfix : φ₁ g = g) : z₀ * g * z₀⁻¹ ∈ S.D.model := by
  refine ⟨outer_rootSpan_le_adjoint _ (hz₀ g hg), ?_⟩
  have h := hφ₁ g hg
  rw [hs1, hfix] at h
  exact h

theorem outer_commutator_mem_Γ {x y : ModGL τ L} (hx : x ∈ S.D.model) (hy : y ∈ S.D.model) :
    ⁅x, y⁆ ∈ S.Γ :=
  Subgroup.commutator_mem_commutator hx hy

theorem outer_mem_rationalSpan {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a))
    {x : ModGL τ L} (hx : x ∈ rootSpan τ L (componentRoots (rootCharHom a) i)) (hΓ : x ∈ S.Γ) :
    x ∈ rationalSpan S.ρ S.Γ (rootCharHom a) i :=
  ⟨rootSpan_mono (fun γ hγ => (⟨0, γ, hγ, rfl⟩ : γ ∈ rationalRoots S.ρ (rootCharHom a) i)) hx,
    hΓ⟩

theorem outer_rootTorusSL2_conj_pinnedX {β α : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (hα : IsRoot τ α) (c : Lˣ) (z : L) :
    rootTorusSL2 τ L β c * pinnedX τ L α z * (rootTorusSL2 τ L β c)⁻¹ =
      pinnedX τ L α (((c ^ (2 * iform β α / iform β β) : Lˣ) : L) * z) := by
  obtain ⟨-, hdH, -, -, hv, hH, -, -⟩ := exceptional_Lang_root_rank_one_torus_transport τ L hβ
  obtain ⟨a, ha, -⟩ := hH _ (hdH c)
  have h1 := (hv c).2 α hα
  rw [ha] at h1
  change rootDiag a (rootVec τ L α) = _ at h1
  rw [rootDiag_rootVec a hα] at h1
  have hne : rootVec τ L α ≠ 0 := by
    rw [rootVec_eq_single_of_isRoot hα]
    exact Finsupp.single_ne_zero.2 one_ne_zero
  have h2 := smul_left_injective L hne h1
  rw [ha, rootDiagUnit_conj_pinnedX a hα]
  congr 2

theorem outer_HSL_neg_one : (HSL (-1 : Lˣ) : SL2 L) = -1 := by
  apply Subtype.ext
  rw [coe_HSL, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem outer_conjSL_neg_one (P : GL (Fin 2) L) : conjSL P (-1 : SL2 L) = -1 := by
  apply Subtype.ext
  rw [coe_conjSL, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
    Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_one, ← Units.val_mul, mul_inv_cancel,
    Units.val_one]

theorem outer_map_neg_one {K : Type*} [Field K] (ι : K →+* L) :
    Matrix.SpecialLinearGroup.map ι (-1 : SL(2, K)) = -1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one, map_neg, map_one]

theorem outer_three_block_data (hsl : SimplyLacedTag τ) (hq : S.D.q = 3) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1)
    {z₀ : ModGL τ L}
    (hz₀ : ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      z₀ * g * z₀⁻¹ ∈ rootSpan τ L (componentRoots (rootCharHom a) i))
    {φ₁ : ModGL τ L →* ModGL τ L}
    (hφ₁ : ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      iterHom S.D.step (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
        (z₀ * g * z₀⁻¹) = z₀ * φ₁ g * z₀⁻¹)
    {f : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ}
    (hf : IsIsometry (componentRoots (rootCharHom a) i) f)
    (hpos : ∀ γ ∈ posRoots (componentRoots (rootCharHom a) i),
      f γ ∈ posRoots (componentRoots (rootCharHom a) i))
    (hpin : OuterPinned φ₁ f
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)))
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ componentRoots (rootCharHom a) i) (hγ2 : f (f γ) = γ)
    (hγ1 : iform γ (f γ) = -1) :
    ∃ (ε : ℤ) (μ₁ t₁ ζ : L), (ε = 1 ∨ ε = -1) ∧ μ₁ ≠ 0 ∧ t₁ ≠ 0 ∧ ζ * ζ = -1 ∧
      OuterHeis (pinnedX τ L γ) (pinnedX τ L (f γ)) (pinnedX τ L (γ + f γ)) (ε : L) ∧
      ∀ t, (t = t₁ ∨ t = ζ * t₁) →
        z₀ * (pinnedX τ L γ t * pinnedX τ L (f γ) (μ₁ * t ^ 3) *
          pinnedX τ L (γ + f γ) ((ε : L) * t * (μ₁ * t ^ 3))) * z₀⁻¹ ∈
          rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  classical
  have hΨ := isRootComponent_componentRoots (χ := rootCharHom a) i
  have h3 : (3 : L) = 0 := by
    have h := S.hqpow.2
    rw [hq] at h
    exact_mod_cast h
  have hγr : IsRoot τ γ := hΨ.isRoot γ hγ
  have hfγ : f γ ∈ componentRoots (rootCharHom a) i := hf.bijOn.mapsTo hγ
  have hfγr : IsRoot τ (f γ) := hΨ.isRoot _ hfγ
  obtain ⟨hωr, ε, hε, H⟩ := outer_block_heis (L := L) hsl hγr hfγr hγ1
  have hωΨ : γ + f γ ∈ componentRoots (rootCharHom a) i := hΨ.add_mem γ hγ (f γ) hfγ hωr
  have hfω : f (γ + f γ) = γ + f γ := by
    have h := outerRoots_iterate_add hf 1 hγ hfγ hωΨ
    simp only [Function.iterate_one] at h
    rw [h, hγ2, add_comm]
  have hQ : S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 3 := by
    rw [hs1, hq, pow_one]
  obtain ⟨-, μ₁, hμ₁, h₁⟩ := hpin γ hγr
  obtain ⟨-, μ₂, hμ₂, h₂⟩ := hpin (f γ) hfγr
  obtain ⟨-, μ₃, -, h₃⟩ := hpin (γ + f γ) hωr
  rw [hQ] at h₁ h₂ h₃
  rw [hγ2] at h₂
  rw [hfω] at h₃
  have hεL : ((ε : ℤ) : L) * (ε : L) = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  have hε0 : ((ε : ℤ) : L) ≠ 0 := fun h => by rw [h, zero_mul] at hεL; exact zero_ne_one hεL
  have hε3 : ((ε : ℤ) : L) ^ 3 = (ε : L) := by rw [pow_succ, sq, hεL, one_mul]
  have hμ : μ₃ = -(μ₁ * μ₂) := by
    have e := congrArg φ₁ (H.commAB 1 1)
    rw [map_commutatorElement, h₁, h₂, h₃, ← commutatorElement_inv, H.commAB, pinnedX_neg] at e
    have e' := pinnedX_injective τ L _ e
    simp only [one_pow, mul_one] at e'
    have e2 : (ε : L) * (μ₃ + μ₁ * μ₂) = 0 := by
      linear_combination (-1 : L) * e' + (-μ₃) * hε3
    have := (mul_eq_zero.1 e2).resolve_left hε0
    linear_combination this
  set κ : L := μ₂ * μ₁ ^ 3 with hκ
  have hκ0 : κ ≠ 0 := mul_ne_zero hμ₂ (pow_ne_zero 3 hμ₁)
  obtain ⟨t₁, ht₁⟩ := IsAlgClosed.exists_pow_nat_eq κ⁻¹ (by norm_num : 0 < 8)
  have ht₁0 : t₁ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at ht₁
    exact inv_ne_zero hκ0 ht₁.symm
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : L) (by norm_num : 0 < 2)
  have hζζ : ζ * ζ = -1 := by rw [← sq]; exact hζ
  have hW : ∀ t, (t = t₁ ∨ t = ζ * t₁) → μ₂ * (μ₁ * t ^ 3) ^ 3 = t := by
    rintro t (rfl | rfl)
    · calc μ₂ * (μ₁ * t ^ 3) ^ 3 = κ * t ^ 8 * t := by rw [hκ]; ring
        _ = t := by rw [ht₁, mul_inv_cancel₀ hκ0, one_mul]
    · have e : μ₂ * (μ₁ * (ζ * t₁) ^ 3) ^ 3 = (ζ * ζ) ^ 4 * ζ * (κ * t₁ ^ 8 * t₁) := by
        rw [hκ]; ring
      rw [e, hζζ, ht₁, mul_inv_cancel₀ hκ0]
      ring
  have hufix : ∀ t, (t = t₁ ∨ t = ζ * t₁) →
      φ₁ (pinnedX τ L γ t * pinnedX τ L (f γ) (μ₁ * t ^ 3) *
        pinnedX τ L (γ + f γ) ((ε : L) * t * (μ₁ * t ^ 3))) =
      pinnedX τ L γ t * pinnedX τ L (f γ) (μ₁ * t ^ 3) *
        pinnedX τ L (γ + f γ) ((ε : L) * t * (μ₁ * t ^ 3)) := by
    intro t ht
    rw [map_mul, map_mul, h₁, h₂, h₃, hW t ht, H.BA]
    have hc : Commute (pinnedX τ L (γ + f γ) (-((ε : L) * t * (μ₁ * t ^ 3))))
        (pinnedX τ L γ t * pinnedX τ L (f γ) (μ₁ * t ^ 3)) :=
      ((H.commAC _ _).mul_left (H.commBC _ _)).symm
    rw [hc.eq, mul_assoc, ← H.addC]
    congr 2
    linear_combination ((ε : L) * t * (μ₁ * t ^ 3)) ^ 3 * hμ -
      μ₁ * (ε : L) ^ 3 * t ^ 3 * hW t ht - μ₁ * t ^ 4 * hε3 - (ε : L) * μ₁ * t ^ 4 * h3
  obtain ⟨hβ, hcomm₁, σm, X, P, -, hret, hP⟩ :=
    outer_exists_first_data S hT i hf hpos hpin hωΨ one_pos (by simpa using hfω)
      (fun n hn hn1 => absurd hn1 (by omega))
  obtain ⟨θ, hθ, hθfix, hθS⟩ := outer_exists_theta i one_pos (fun j => f^[j] (γ + f γ))
    (fun j => outerRoots_iterate_mem hf j hωΨ) hβ hcomm₁ σm X hret P hP
  have h3K : (3 : fixSubfield σm) = 0 := by
    apply (algebraMap (fixSubfield σm) L).injective
    rw [map_ofNat, map_zero, h3]
  obtain ⟨I, J, hIJ⟩ := outer_exists_commutator_neg_one h3K
  have hθneg : θ (I * J * I⁻¹ * J⁻¹) = rootTorusSL2 τ L (γ + f γ) (-1) := by
    rw [hIJ, hθ]
    simp only [List.range_one, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, Function.iterate_zero, id_eq]
    rw [outer_map_neg_one, outer_conjSL_neg_one]
    show rootSL2 τ L (γ + f γ) (-1) = rootSL2 τ L (γ + f γ) (HSL (-1))
    rw [outer_HSL_neg_one]
  set h₀ := rootTorusSL2 τ L (γ + f γ) (-1) with hh₀
  have hnγ : iform γ γ = 2 := outer_iform_self_of_simplyLaced hsl hγr
  have hnfγ : iform (f γ) (f γ) = 2 := outer_iform_self_of_simplyLaced hsl hfγr
  have hnω : iform (γ + f γ) (γ + f γ) = 2 := outer_iform_self_of_simplyLaced hsl hωr
  have hωγ : iform (γ + f γ) γ = 1 := by rw [iform_add_left, hnγ, iform_comm, hγ1]; norm_num
  have hωfγ : iform (γ + f γ) (f γ) = 1 := by rw [iform_add_left, hγ1, hnfγ]; norm_num
  have hA : ∀ x, h₀ * pinnedX τ L γ x * h₀⁻¹ = pinnedX τ L γ (-x) := by
    intro x
    rw [hh₀, outer_rootTorusSL2_conj_pinnedX hωr hγr, hωγ, hnω]
    norm_num
  have hB : ∀ x, h₀ * pinnedX τ L (f γ) x * h₀⁻¹ = pinnedX τ L (f γ) (-x) := by
    intro x
    rw [hh₀, outer_rootTorusSL2_conj_pinnedX hωr hfγr, hωfγ, hnω]
    norm_num
  have hC : ∀ x, h₀ * pinnedX τ L (γ + f γ) x * h₀⁻¹ = pinnedX τ L (γ + f γ) x := by
    intro x
    rw [hh₀, outer_rootTorusSL2_conj_pinnedX hωr hωr, hnω]
    norm_num
  have hM : ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i), φ₁ g = g →
      z₀ * g * z₀⁻¹ ∈ S.D.model := fun g hg hfix => outer_conj_mem_model S i hs1 hz₀ hφ₁ hg hfix
  have hconj : ∀ x y : ModGL τ L, z₀ * ⁅x, y⁆ * z₀⁻¹ = ⁅z₀ * x * z₀⁻¹, z₀ * y * z₀⁻¹⁆ := by
    intro x y
    simp only [commutatorElement_def]
    group
  have hh₀S : h₀ ∈ rootSpan τ L (componentRoots (rootCharHom a) i) := by
    rw [← hθneg]
    exact hθS _
  have hh₀fix : φ₁ h₀ = h₀ := by
    rw [← hθneg]
    exact hθfix _
  have hh₀Γ : z₀ * h₀ * z₀⁻¹ ∈ S.Γ := by
    have e : h₀ = ⁅θ I, θ J⁆ := by
      rw [← hθneg]
      exact map_commutatorElement θ I J
    rw [e, hconj]
    exact outer_commutator_mem_Γ S (hM _ (hθS I) (hθfix I)) (hM _ (hθS J) (hθfix J))
  refine ⟨ε, μ₁, t₁, ζ, hε, hμ₁, ht₁0, hζζ, H, fun t ht => ?_⟩
  set u := pinnedX τ L γ t * pinnedX τ L (f γ) (μ₁ * t ^ 3) *
    pinnedX τ L (γ + f γ) ((ε : L) * t * (μ₁ * t ^ 3)) with hu
  have huS : u ∈ rootSpan τ L (componentRoots (rootCharHom a) i) :=
    mul_mem (mul_mem (pinnedX_mem_rootSpan hγ _) (pinnedX_mem_rootSpan hfγ _))
      (pinnedX_mem_rootSpan hωΨ _)
  have huM := hM u huS (hufix t ht)
  have hh₀M := hM h₀ hh₀S hh₀fix
  have hcu : ⁅h₀, u⁆ = u := H.commutator_inv_conj h3 hA hB hC t (μ₁ * t ^ 3)
  have huΓ : z₀ * u * z₀⁻¹ ∈ S.Γ := by
    rw [← hcu, hconj]
    exact outer_commutator_mem_Γ S hh₀M huM
  have hh₀R := outer_mem_rationalSpan S i (hz₀ _ hh₀S) hh₀Γ
  have huR := outer_mem_rationalSpan S i (hz₀ _ huS) huΓ
  rw [← hcu, hconj]
  exact Subgroup.commutator_mem_commutator hh₀R huR

theorem outer_conj_commutator (z₀ x y : ModGL τ L) :
    z₀ * ⁅x, y⁆ * z₀⁻¹ = ⁅z₀ * x * z₀⁻¹, z₀ * y * z₀⁻¹⁆ := by
  simp only [commutatorElement_def]
  group

theorem outer_three_block_omega (hsl : SimplyLacedTag τ) (hq : S.D.q = 3)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a))
    (hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1)
    {z₀ : ModGL τ L}
    (hz₀ : ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      z₀ * g * z₀⁻¹ ∈ rootSpan τ L (componentRoots (rootCharHom a) i))
    {φ₁ : ModGL τ L →* ModGL τ L}
    (hφ₁ : ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      iterHom S.D.step (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
        (z₀ * g * z₀⁻¹) = z₀ * φ₁ g * z₀⁻¹)
    {f : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ}
    (hf : IsIsometry (componentRoots (rootCharHom a) i) f)
    (hpos : ∀ γ ∈ posRoots (componentRoots (rootCharHom a) i),
      f γ ∈ posRoots (componentRoots (rootCharHom a) i))
    (hpin : OuterPinned φ₁ f
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)))
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ componentRoots (rootCharHom a) i) (hγ2 : f (f γ) = γ)
    (hγ1 : iform γ (f γ) = -1) (z : ModGL τ L)
    (hcomm : ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i, Commute z x) :
    ∀ c : L, Commute z (z₀ * pinnedX τ L (γ + f γ) c * z₀⁻¹) := by
  classical
  have hτ : τ ≠ .G2 := by rcases hsl with h | h | h | h <;> rw [h] <;> decide
  have hΨ := isRootComponent_componentRoots (χ := rootCharHom a) i
  have h3 : (3 : L) = 0 := by
    have h := S.hqpow.2
    rw [hq] at h
    exact_mod_cast h
  have h2 : (2 : L) ≠ 0 := fun h => by
    have : (1 : L) = 0 := by linear_combination h3 - h
    exact one_ne_zero this
  have hγr : IsRoot τ γ := hΨ.isRoot γ hγ
  have hfγr : IsRoot τ (f γ) := hΨ.isRoot _ (hf.bijOn.mapsTo hγ)
  have hωr := (outer_block_heis (L := L) hsl hγr hfγr hγ1).1
  obtain ⟨ε, μ₁, t₁, ζ, hε, hμ₁, ht₁0, hζζ, H, hmem⟩ :=
    outer_three_block_data S hsl hq hT i hs1 hz₀ hφ₁ hf hpos hpin hγ hγ2 hγ1
  have hε0 : ((ε : ℤ) : L) ≠ 0 := by rcases hε with h | h <;> rw [h] <;> norm_num
  have hζ0 : ζ ≠ 0 := fun h => by
    rw [h, zero_mul] at hζζ
    exact one_ne_zero (neg_eq_zero.1 hζζ.symm)
  set c₀ : L := (ε : L) * (t₁ * (μ₁ * (ζ * t₁) ^ 3) - ζ * t₁ * (μ₁ * t₁ ^ 3)) with hc₀
  have hX : z₀ * pinnedX τ L (γ + f γ) c₀ * z₀⁻¹ ∈
      rationalComponent S.ρ S.Γ (rootCharHom a) i := by
    have h1 := hmem t₁ (Or.inl rfl)
    have h2 := hmem (ζ * t₁) (Or.inr rfl)
    have e := H.commutator_normal t₁ (μ₁ * t₁ ^ 3) ((ε : L) * t₁ * (μ₁ * t₁ ^ 3)) (ζ * t₁)
      (μ₁ * (ζ * t₁) ^ 3) ((ε : L) * (ζ * t₁) * (μ₁ * (ζ * t₁) ^ 3))
    rw [← hc₀] at e
    rw [← e, outer_conj_commutator]
    exact mul_mem (mul_mem (mul_mem h1 h2) (inv_mem h1)) (inv_mem h2)
  have hX' : z₀ * pinnedX τ L (γ + f γ) (-c₀) * z₀⁻¹ ∈
      rationalComponent S.ρ S.Γ (rootCharHom a) i := by
    have e : z₀ * pinnedX τ L (γ + f γ) (-c₀) * z₀⁻¹ =
        (z₀ * pinnedX τ L (γ + f γ) c₀ * z₀⁻¹)⁻¹ := by
      rw [← pinnedX_neg]
      group
    rw [e]
    exact inv_mem hX
  have hc₀0 : c₀ ≠ 0 := by
    have e : c₀ = (ε : L) * μ₁ * ζ * t₁ ^ 4 * (ζ * ζ - 1) := by rw [hc₀]; ring
    have e2 : (-1 - 1 : L) = 1 := by linear_combination (-1 : L) * h3
    rw [e, hζζ, e2, mul_one]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hε0 hμ₁) hζ0) (pow_ne_zero 4 ht₁0)
  obtain ⟨aZ, bZ, -, -, -, -, -, hE1, -⟩ := exists_factor_data S hτ (RingHom.id L) z₀ hωr 0
  have hform : ∀ t : L, ((z₀ * pinnedX τ L (γ + f γ) t * z₀⁻¹ : ModGL τ L) :
      Module.End L (RootModule τ L)) = 1 + t • aZ + t ^ 2 • bZ := by
    intro t
    have := hE1 t
    rw [iterHom_zero, pow_zero, pow_one] at this
    exact this
  have hp := congrArg (fun m : ModGL τ L => (m : Module.End L (RootModule τ L)))
    (hcomm _ hX).eq
  have hm := congrArg (fun m : ModGL τ L => (m : Module.End L (RootModule τ L)))
    (hcomm _ hX').eq
  simp only [Units.val_mul, hform] at hp hm
  obtain ⟨hza, hzb⟩ := commute_of_pm_points h2 hc₀0 hp hm
  intro c
  have hfc := hform c
  generalize z₀ * pinnedX τ L (γ + f γ) c * z₀⁻¹ = W at hfc ⊢
  show z * W = W * z
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, hfc]
  simp only [mul_add, add_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc, hza, hzb]

theorem outer_three_block_root (hsl : SimplyLacedTag τ) (hq : S.D.q = 3)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a))
    (hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1)
    {z₀ : ModGL τ L}
    (hz₀ : ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      z₀ * g * z₀⁻¹ ∈ rootSpan τ L (componentRoots (rootCharHom a) i))
    {φ₁ : ModGL τ L →* ModGL τ L}
    (hφ₁ : ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      iterHom S.D.step (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
        (z₀ * g * z₀⁻¹) = z₀ * φ₁ g * z₀⁻¹)
    {f : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ}
    (hf : IsIsometry (componentRoots (rootCharHom a) i) f)
    (hpos : ∀ γ ∈ posRoots (componentRoots (rootCharHom a) i),
      f γ ∈ posRoots (componentRoots (rootCharHom a) i))
    (hpin : OuterPinned φ₁ f
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)))
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ componentRoots (rootCharHom a) i) (hγ2 : f (f γ) = γ)
    (hγ1 : iform γ (f γ) = -1) (z : ModGL τ L)
    (hcomm : ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i, Commute z x)
    (hQω : ∀ x ∈ rootRankOneGroup τ L (γ + f γ), Commute z (z₀ * x * z₀⁻¹)) :
    (∀ c : L, Commute z (z₀ * pinnedX τ L γ c * z₀⁻¹)) ∧
      ∀ c : L, Commute z (z₀ * pinnedX τ L (f γ) c * z₀⁻¹) := by
  classical
  have hΨ := isRootComponent_componentRoots (χ := rootCharHom a) i
  have h3 : (3 : L) = 0 := by
    have h := S.hqpow.2
    rw [hq] at h
    exact_mod_cast h
  have hγr : IsRoot τ γ := hΨ.isRoot γ hγ
  have hfγr : IsRoot τ (f γ) := hΨ.isRoot _ (hf.bijOn.mapsTo hγ)
  have hωr := (outer_block_heis (L := L) hsl hγr hfγr hγ1).1
  obtain ⟨ε, μ₁, t₁, ζ, -, hμ₁, ht₁0, hζζ, H, hmem⟩ :=
    outer_three_block_data S hsl hq hT i hs1 hz₀ hφ₁ hf hpos hpin hγ hγ2 hγ1
  have hζ0 : ζ ≠ 0 := fun h => by
    rw [h, zero_mul] at hζζ
    exact one_ne_zero (neg_eq_zero.1 hζζ.symm)
  have hnγ : iform γ γ = 2 := outer_iform_self_of_simplyLaced hsl hγr
  have hnfγ : iform (f γ) (f γ) = 2 := outer_iform_self_of_simplyLaced hsl hfγr
  have hnω : iform (γ + f γ) (γ + f γ) = 2 := outer_iform_self_of_simplyLaced hsl hωr
  have hωγ : iform (γ + f γ) γ = 1 := by rw [iform_add_left, hnγ, iform_comm, hγ1]; norm_num
  have hωfγ : iform (γ + f γ) (f γ) = 1 := by rw [iform_add_left, hγ1, hnfγ]; norm_num
  have hCω : ∀ c, Commute z (z₀ * pinnedX τ L (γ + f γ) c * z₀⁻¹) := fun c => hQω _ (by
    rw [rootRankOneGroup, range_rootSL2_of_isRoot hωr]
    exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨c, rfl⟩))
  have hd : ∀ l : Lˣ, Commute z (z₀ * rootTorusSL2 τ L (γ + f γ) l * z₀⁻¹) := fun l =>
    hQω _ ⟨HSL l, rfl⟩
  have hdA : ∀ (l : Lˣ) x, rootTorusSL2 τ L (γ + f γ) l * pinnedX τ L γ x *
      (rootTorusSL2 τ L (γ + f γ) l)⁻¹ = pinnedX τ L γ ((l : L) * x) := by
    intro l x
    rw [outer_rootTorusSL2_conj_pinnedX hωr hγr, hωγ, hnω]
    norm_num
  have hdB : ∀ (l : Lˣ) x, rootTorusSL2 τ L (γ + f γ) l * pinnedX τ L (f γ) x *
      (rootTorusSL2 τ L (γ + f γ) l)⁻¹ = pinnedX τ L (f γ) ((l : L) * x) := by
    intro l x
    rw [outer_rootTorusSL2_conj_pinnedX hωr hfγr, hωfγ, hnω]
    norm_num
  have hdC : ∀ (l : Lˣ) x, rootTorusSL2 τ L (γ + f γ) l * pinnedX τ L (γ + f γ) x *
      (rootTorusSL2 τ L (γ + f γ) l)⁻¹ = pinnedX τ L (γ + f γ) ((l : L) ^ 2 * x) := by
    intro l x
    rw [outer_rootTorusSL2_conj_pinnedX hωr hωr, hnω]
    norm_num
  have hpair : ∀ t, (t = t₁ ∨ t = ζ * t₁) → ∀ l : Lˣ,
      Commute z (z₀ * (pinnedX τ L γ ((l : L) * t) *
        pinnedX τ L (f γ) ((l : L) * (μ₁ * t ^ 3))) * z₀⁻¹) := by
    intro t ht l
    have h1 := hcomm _ (hmem t ht)
    set d := rootTorusSL2 τ L (γ + f γ) l with hddef
    have h2 : Commute z (z₀ * (d * (pinnedX τ L γ t * pinnedX τ L (f γ) (μ₁ * t ^ 3) *
        pinnedX τ L (γ + f γ) ((ε : L) * t * (μ₁ * t ^ 3))) * d⁻¹) * z₀⁻¹) := by
      have e : ∀ u : ModGL τ L, z₀ * (d * u * d⁻¹) * z₀⁻¹ =
          (z₀ * d * z₀⁻¹) * (z₀ * u * z₀⁻¹) * (z₀ * d * z₀⁻¹)⁻¹ := fun u => by group
      rw [e]
      exact ((hd l).mul_right h1).mul_right (hd l).inv_right
    have e2 : d * (pinnedX τ L γ t * pinnedX τ L (f γ) (μ₁ * t ^ 3) *
        pinnedX τ L (γ + f γ) ((ε : L) * t * (μ₁ * t ^ 3))) * d⁻¹ =
        pinnedX τ L γ ((l : L) * t) * pinnedX τ L (f γ) ((l : L) * (μ₁ * t ^ 3)) *
          pinnedX τ L (γ + f γ) ((l : L) ^ 2 * ((ε : L) * t * (μ₁ * t ^ 3))) := by
      have e : ∀ x y w : ModGL τ L, d * (x * y * w) * d⁻¹ =
          (d * x * d⁻¹) * (d * y * d⁻¹) * (d * w * d⁻¹) := fun x y w => by group
      rw [e, hdA, hdB, hdC]
    rw [e2] at h2
    have e3 : ∀ x y w : ModGL τ L, z₀ * (x * y) * z₀⁻¹ =
        z₀ * (x * y * w) * z₀⁻¹ * (z₀ * w * z₀⁻¹)⁻¹ := fun x y w => by group
    rw [e3 _ _ (pinnedX τ L (γ + f γ) ((l : L) ^ 2 * ((ε : L) * t * (μ₁ * t ^ 3))))]
    exact h2.mul_right (hCω _).inv_right
  have hA : ∀ s : L, Commute z (z₀ * pinnedX τ L γ s * z₀⁻¹) := by
    intro s
    by_cases hs : s = 0
    · rw [hs, pinnedX_zero, mul_one, mul_inv_cancel]
      exact Commute.one_right z
    have hζt₁ : ζ * t₁ ≠ 0 := mul_ne_zero hζ0 ht₁0
    set l₁ : Lˣ := Units.mk0 (-s / t₁) (div_ne_zero (neg_ne_zero.2 hs) ht₁0) with hl₁
    set l₂ : Lˣ := Units.mk0 (-s / (ζ * t₁)) (div_ne_zero (neg_ne_zero.2 hs) hζt₁) with hl₂
    have ha : (l₁ : L) * t₁ + (l₂ : L) * (ζ * t₁) = s := by
      rw [hl₁, hl₂, Units.val_mk0, Units.val_mk0, div_mul_cancel₀ _ ht₁0,
        div_mul_cancel₀ _ hζt₁]
      linear_combination (-s) * h3
    have hb : (l₁ : L) * (μ₁ * t₁ ^ 3) + (l₂ : L) * (μ₁ * (ζ * t₁) ^ 3) = 0 := by
      rw [hl₁, hl₂, Units.val_mk0, Units.val_mk0]
      have e : -s / t₁ * (μ₁ * t₁ ^ 3) + -s / (ζ * t₁) * (μ₁ * (ζ * t₁) ^ 3) =
          -s * μ₁ * t₁ ^ 2 * (1 + ζ * ζ) := by
        field_simp
        ring
      rw [e, hζζ]
      ring
    have e := H.mul_AB ((l₁ : L) * t₁) ((l₁ : L) * (μ₁ * t₁ ^ 3)) ((l₂ : L) * (ζ * t₁))
      ((l₂ : L) * (μ₁ * (ζ * t₁) ^ 3))
    rw [ha, hb, pinnedX_zero, mul_one] at e
    have e' : pinnedX τ L γ s = pinnedX τ L γ ((l₁ : L) * t₁) *
        pinnedX τ L (f γ) ((l₁ : L) * (μ₁ * t₁ ^ 3)) *
        (pinnedX τ L γ ((l₂ : L) * (ζ * t₁)) *
          pinnedX τ L (f γ) ((l₂ : L) * (μ₁ * (ζ * t₁) ^ 3))) *
        pinnedX τ L (γ + f γ) ((ε : L) * ((l₂ : L) * (ζ * t₁)) * ((l₁ : L) * (μ₁ * t₁ ^ 3))) := by
      rw [e, mul_assoc, ← H.addC, neg_add_cancel, H.C_zero, mul_one]
    rw [e']
    have e2 : ∀ x y w : ModGL τ L, z₀ * (x * y * w) * z₀⁻¹ =
        (z₀ * x * z₀⁻¹) * (z₀ * y * z₀⁻¹) * (z₀ * w * z₀⁻¹) := fun x y w => by group
    rw [e2]
    exact ((hpair t₁ (Or.inl rfl) l₁).mul_right (hpair (ζ * t₁) (Or.inr rfl) l₂)).mul_right
      (hCω _)
  refine ⟨hA, fun s => ?_⟩
  by_cases hs : s = 0
  · rw [hs, pinnedX_zero, mul_one, mul_inv_cancel]
    exact Commute.one_right z
  have hb0 : μ₁ * t₁ ^ 3 ≠ 0 := mul_ne_zero hμ₁ (pow_ne_zero 3 ht₁0)
  set l : Lˣ := Units.mk0 (s / (μ₁ * t₁ ^ 3)) (div_ne_zero hs hb0) with hl
  have hls : (l : L) * (μ₁ * t₁ ^ 3) = s := by
    rw [hl, Units.val_mk0, div_mul_cancel₀ _ hb0]
  have h1 := hpair t₁ (Or.inl rfl) l
  rw [hls] at h1
  have e : z₀ * pinnedX τ L (f γ) s * z₀⁻¹ =
      (z₀ * pinnedX τ L γ ((l : L) * t₁) * z₀⁻¹)⁻¹ *
        (z₀ * (pinnedX τ L γ ((l : L) * t₁) * pinnedX τ L (f γ) s) * z₀⁻¹) := by group
  rw [e]
  exact (hA _).inv_right.mul_right h1

end BlockData

section Fixed

variable {τ : Tag}

theorem outer_exists_nonfixed_sub {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    {f : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ} (hf : IsIsometry Ψ f) {δ : Fin τ.rank → ℤ}
    (hδ : δ ∈ Ψ) (hδf : f δ = δ) (hne : ∃ γ ∈ Ψ, f γ ≠ γ) :
    ∃ β ∈ Ψ, f β ≠ β ∧ δ - β ∈ Ψ ∧ f (δ - β) ≠ δ - β := by
  classical
  have hδr := hΨ.isRoot δ hδ
  have hfneg : ∀ β ∈ Ψ, f β ≠ β → f (-β) ≠ -β := fun β hβ hβf h => by
    rw [hf.neg β hβ] at h
    exact hβf (neg_inj.1 h)
  have hex : ∃ β ∈ Ψ, f β ≠ β ∧ iform δ β ≠ 0 := by
    by_contra hcon
    push Not at hcon
    set T : Set (Fin τ.rank → ℤ) := {γ | γ ∈ Ψ ∧ ∀ β ∈ Ψ, f β ≠ β → iform γ β = 0} with hTdef
    have hirr : ∀ α ∈ T, ∀ β ∈ Ψ, β ∉ T → iform α β = 0 := by
      intro α hα β hβ hβT
      by_contra hαβ
      have hβf : f β = β := by
        by_contra h
        exact hαβ (hα.2 β hβ h)
      have hβ' : ∃ β₀ ∈ Ψ, f β₀ ≠ β₀ ∧ iform β β₀ ≠ 0 := by
        by_contra h
        push Not at h
        exact hβT ⟨hβ, h⟩
      obtain ⟨β₀, hβ₀, hβ₀f, hββ₀⟩ := hβ'
      obtain ⟨β₁, hβ₁, hβ₁f, hββ₁⟩ : ∃ β₁ ∈ Ψ, f β₁ ≠ β₁ ∧ iform β β₁ < 0 := by
        rcases lt_or_gt_of_ne hββ₀ with h | h
        · exact ⟨β₀, hβ₀, hβ₀f, h⟩
        · exact ⟨-β₀, hΨ.neg_mem _ hβ₀, hfneg β₀ hβ₀ hβ₀f, by rw [outer_iform_neg_right]; omega⟩
      have hne' : β ≠ -β₁ := fun h => by
        apply hβ₁f
        have e : β₁ = -β := by rw [h, neg_neg]
        rw [e, hf.neg β hβ, hβf]
      have hsum := isRoot_add_of_iform_neg (hΨ.isRoot β hβ) (hΨ.isRoot β₁ hβ₁) hne' hββ₁
      have hsumΨ := hΨ.add_mem β hβ β₁ hβ₁ hsum
      have hsumf : f (β + β₁) ≠ β + β₁ := by
        have e := outerRoots_iterate_add hf 1 hβ hβ₁ hsumΨ
        simp only [Function.iterate_one] at e
        rw [e, hβf]
        intro h
        exact hβ₁f (add_left_cancel h)
      have h1 := hα.2 _ hsumΨ hsumf
      have h2 := hα.2 β₁ hβ₁ hβ₁f
      rw [iform_add_right, h2, add_zero] at h1
      exact hαβ h1
    rcases hΨ.irreducible T (fun γ h => h.1) hirr with h | h
    · have hδT : δ ∈ T := ⟨hδ, hcon⟩
      rw [h] at hδT
      exact hδT
    · obtain ⟨γ₀, hγ₀, hγ₀f⟩ := hne
      have hγ₀T : γ₀ ∈ T := by rw [h]; exact hγ₀
      have h0 := hγ₀T.2 γ₀ hγ₀ hγ₀f
      have := iform_self_pos_of_isRoot (hΨ.isRoot γ₀ hγ₀)
      omega
  obtain ⟨β, hβ, hβf, hδβ⟩ := hex
  obtain ⟨β', hβ', hβ'f, hδβ'⟩ : ∃ β' ∈ Ψ, f β' ≠ β' ∧ 0 < iform δ β' := by
    rcases lt_or_gt_of_ne hδβ with h | h
    · exact ⟨-β, hΨ.neg_mem _ hβ, hfneg β hβ hβf, by rw [outer_iform_neg_right]; omega⟩
    · exact ⟨β, hβ, hβf, h⟩
  have hne'' : δ ≠ β' := fun h => hβ'f (h ▸ hδf)
  have hsub := isRoot_sub_of_iform_pos hδr (hΨ.isRoot β' hβ') hne'' hδβ'
  have hsubΨ : δ - β' ∈ Ψ := by
    have := hΨ.add_mem δ hδ (-β') (hΨ.neg_mem _ hβ') (by rwa [← sub_eq_add_neg])
    rwa [← sub_eq_add_neg] at this
  refine ⟨β', hβ', hβ'f, hsubΨ, fun h => hβ'f ?_⟩
  have e := outerRoots_iterate_sub hf 1 hδ hβ' hsubΨ
  simp only [Function.iterate_one] at e
  rw [e, hδf] at h
  exact sub_right_injective h

variable {L : Type} [Field L] [IsAlgClosed L]

theorem outer_commute_pinnedX_of_sum (hsl : SimplyLacedTag τ) {β β' : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) (hβ' : IsRoot τ β') (hsum : IsRoot τ (β + β')) (hne : β ≠ β')
    (hne' : β ≠ -β') {z z₀ : ModGL τ L}
    (h1 : ∀ c, Commute z (z₀ * pinnedX τ L β c * z₀⁻¹))
    (h2 : ∀ c, Commute z (z₀ * pinnedX τ L β' c * z₀⁻¹)) :
    ∀ c, Commute z (z₀ * pinnedX τ L (β + β') c * z₀⁻¹) := by
  have hsl' : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := hsl
  obtain ⟨h₁, -⟩ := simply_laced_root_commutator_unit.{0} τ hsl' hβ hβ' hne hne'
  obtain ⟨hε, hF⟩ := h₁ hsum
  intro c
  have e : pinnedX τ L (β + β') c =
      ⁅pinnedX τ L β ((commConst τ β β' (1, 1) : L) * c), pinnedX τ L β' 1⁆ := by
    rw [hF L]
    congr 1
    rcases hε with h | h <;> rw [h] <;> norm_num
  rw [e, outer_conj_commutator]
  simp only [commutatorElement_def]
  exact (((h1 _).mul_right (h2 _)).mul_right (h1 _).inv_right).mul_right (h2 _).inv_right

theorem outer_commute_rankOne_of_pm {ω : Fin τ.rank → ℤ} (hω : IsRoot τ ω)
    {z z₀ : ModGL τ L} (h1 : ∀ c, Commute z (z₀ * pinnedX τ L ω c * z₀⁻¹))
    (h2 : ∀ c, Commute z (z₀ * pinnedX τ L (-ω) c * z₀⁻¹)) :
    ∀ x ∈ rootRankOneGroup τ L ω, Commute z (z₀ * x * z₀⁻¹) := by
  have hle : rootRankOneGroup τ L ω ≤
      (Subgroup.centralizer {z}).comap (MulAut.conj z₀).toMonoidHom := by
    rw [rootRankOneGroup, range_rootSL2_of_isRoot hω]
    refine sup_le ?_ ?_
    · rw [rootSubgroup, Subgroup.closure_le]
      rintro _ ⟨c, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.2 (h1 c).symm.eq
    · rw [rootSubgroup, Subgroup.closure_le]
      rintro _ ⟨c, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.2 (h2 c).symm.eq
  intro x hx
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hx)).symm

end Fixed

section Assembly

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)

theorem commute_rootSpan_of_commute_component_outer_three (hsl : SimplyLacedTag τ)
    (hq : S.D.q = 3) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a))
    (hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1)
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (z : ModGL τ L)
    (hcomm : ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i, Commute z x) :
    ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i), Commute z g := by
  classical
  have hτ : τ ≠ .G2 := by rcases hsl with h | h | h | h <;> rw [h] <;> decide
  have hq3 : 3 ≤ S.D.q := by omega
  have hΨ := isRootComponent_componentRoots (χ := rootCharHom a) i
  obtain ⟨f, z₀, φ₁, hf, hpos, hpin, hz₀n, hφ₁, hφ₁S, hne⟩ := outer_exists_lang_data S hT i
  have hnf := hne hout
  have hz₀' : ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      z₀ * g * z₀⁻¹ ∈ rootSpan τ L (componentRoots (rootCharHom a) i) := fun g hg =>
    (hz₀n g).1 hg
  have hQ4m : ∀ m, 2 ≤ m →
      4 ≤ S.D.q ^ (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) * m) := by
    intro m hm
    rw [hs1, hq, one_mul]
    calc 4 ≤ 3 ^ 2 := by norm_num
      _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hfromQ : ∀ δ, IsRoot τ δ → (∀ B, Commute z (z₀ * rootSL2 τ L δ B * z₀⁻¹)) →
      (∀ t, Commute z (z₀ * pinnedX τ L δ t * z₀⁻¹)) ∧
        ∀ t, Commute z (z₀ * pinnedX τ L (-δ) t * z₀⁻¹) := by
    intro δ hδ hB
    refine ⟨fun t => ?_, fun t => ?_⟩
    · obtain ⟨B, hB'⟩ : pinnedX τ L δ t ∈ (rootSL2 τ L δ).range := by
        rw [range_rootSL2_of_isRoot hδ]
        exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨t, rfl⟩)
      rw [← hB']
      exact hB B
    · obtain ⟨B, hB'⟩ : pinnedX τ L (-δ) t ∈ (rootSL2 τ L δ).range := by
        rw [range_rootSL2_of_isRoot hδ]
        exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨t, rfl⟩)
      rw [← hB']
      exact hB B
  have hfirst : ∀ δ ∈ componentRoots (rootCharHom a) i, ∀ m, 2 ≤ m → f^[m] δ = δ →
      (∀ n, 0 < n → n < m → iform δ (f^[n] δ) = 0) →
      ∀ B : SL2 L, Commute z (z₀ * rootSL2 τ L δ B * z₀⁻¹) :=
    fun δ hδ m hm hper horth => outer_commute_first S hτ hT i hq3 hz₀' hφ₁ hφ₁S hf hpos hpin
      hδ (by omega) (hQ4m m hm) hper horth z hcomm
  have hstage1 : ∀ δ ∈ posRoots (componentRoots (rootCharHom a) i), f δ ≠ δ →
      (∀ t, Commute z (z₀ * pinnedX τ L δ t * z₀⁻¹)) ∧
        ∀ t, Commute z (z₀ * pinnedX τ L (-δ) t * z₀⁻¹) := by
    intro δ hδ hδf
    have hδr : IsRoot τ δ := hΨ.isRoot δ hδ.1
    rcases outerRoots_dichotomy hΨ hf hpos hδ with horth | ⟨k, hk, hper, hpair, horth⟩
    · have hm0 := outerRoots_minimalPeriod_pos hΨ hf hδ.1
      have hm2 : 2 ≤ Function.minimalPeriod f δ := by
        by_contra h
        have h1 : Function.minimalPeriod f δ = 1 := by omega
        apply hδf
        have := Function.iterate_minimalPeriod (f := f) (x := δ)
        rw [h1] at this
        simpa using this
      exact hfromQ δ hδr (hfirst δ hδ.1 _ hm2 Function.iterate_minimalPeriod horth)
    · have hb : OuterBlock f δ k :=
        ⟨hk, hper, hpair, fun n hn hn2 hnk => horth n hn (by rw [hper]; exact hn2) hnk⟩
      have hω := outerRoots_block_mem hΨ hpos hδ hb
      by_cases hk1 : k = 1
      · subst hk1
        have hfδ : f δ ∈ componentRoots (rootCharHom a) i := hf.bijOn.mapsTo hδ.1
        have hδ2 : f (f δ) = δ := by
          have := Function.iterate_minimalPeriod (f := f) (x := δ)
          rw [hper] at this
          simpa using this
        have hδ1 : iform δ (f δ) = -1 := by
          have h := hpair
          simp only [Function.iterate_one] at h
          rw [outer_iform_self_of_simplyLaced hsl hδr] at h
          omega
        have hnδΨ := hΨ.neg_mem δ hδ.1
        have hnδ2 : f (f (-δ)) = -δ := by
          rw [hf.neg δ hδ.1, hf.neg _ hfδ, hδ2]
        have hnδ1 : iform (-δ) (f (-δ)) = -1 := by
          rw [hf.neg δ hδ.1, outer_iform_neg_left, outer_iform_neg_right, neg_neg, hδ1]
        have hωr : IsRoot τ (δ + f δ) := hΨ.isRoot _ hω.1
        have e : -δ + f (-δ) = -(δ + f δ) := by rw [hf.neg δ hδ.1, neg_add]
        have hU := outer_three_block_omega S hsl hq hT i hs1 hz₀' hφ₁ hf hpos hpin hδ.1 hδ2 hδ1 z
          hcomm
        have hU' := outer_three_block_omega S hsl hq hT i hs1 hz₀' hφ₁ hf hpos hpin hnδΨ hnδ2
          hnδ1 z hcomm
        rw [e] at hU'
        have hQω := outer_commute_rankOne_of_pm hωr hU hU'
        have hQω' : ∀ x ∈ rootRankOneGroup τ L (-δ + f (-δ)), Commute z (z₀ * x * z₀⁻¹) := by
          rw [e]
          refine outer_commute_rankOne_of_pm (IsRoot.neg hωr) hU' ?_
          intro c
          rw [neg_neg]
          exact hU c
        exact ⟨(outer_three_block_root S hsl hq hT i hs1 hz₀' hφ₁ hf hpos hpin hδ.1 hδ2 hδ1 z
          hcomm hQω).1, (outer_three_block_root S hsl hq hT i hs1 hz₀' hφ₁ hf hpos hpin hnδΨ
          hnδ2 hnδ1 z hcomm hQω').1⟩
      · have hk2 : 2 ≤ k := by omega
        refine hfromQ δ hδr (outer_commute_second S hτ hT i hq3 hz₀' hφ₁ hφ₁S hf hpos hpin hδ hb
          (hQ4m k hk2) z hcomm fun j B => ?_)
        refine hfirst _ (outerRoots_iterate_mem hf j hω.1) k hk2 ?_ ?_ B
        · rw [← Function.iterate_add_apply, Nat.add_comm k j, Function.iterate_add_apply,
            outerRoots_block_fixed hΨ hf hpos hδ hb]
        · intro n hn hnk
          rw [← Function.iterate_add_apply,
            outerRoots_iform_iterate hf hω.1 (Nat.le_add_left j n), Nat.add_sub_cancel]
          exact outerRoots_block_orthogonal hΨ hf hpos hδ hb hn hnk
  have hnonfixed : ∀ β ∈ componentRoots (rootCharHom a) i, f β ≠ β →
      ∀ t, Commute z (z₀ * pinnedX τ L β t * z₀⁻¹) := by
    intro β hβ hβf
    rcases mem_posRoots_or_mem_negRoots hΨ hβ with hp | hn
    · exact (hstage1 β hp hβf).1
    · have hnβf : f (-β) ≠ -β := by
        rw [hf.neg β hβ]
        intro h
        exact hβf (neg_inj.1 h)
      have h := (hstage1 (-β) hn hnβf).2
      rwa [neg_neg] at h
  have hall : ∀ δ ∈ componentRoots (rootCharHom a) i, ∀ t,
      Commute z (z₀ * pinnedX τ L δ t * z₀⁻¹) := by
    intro δ hδ
    by_cases hδf : f δ = δ
    · obtain ⟨β, hβ, hβf, hsubΨ, hsubf⟩ := outer_exists_nonfixed_sub hΨ hf hδ hδf hnf
      have hβr := hΨ.isRoot β hβ
      have hsubr := hΨ.isRoot _ hsubΨ
      have hδr := hΨ.isRoot δ hδ
      have hsum : β + (δ - β) = δ := by abel
      have hβn := outer_iform_self_of_simplyLaced hsl hβr
      have hne1 : β ≠ δ - β := fun h => by
        have e : δ = β + β := by
          nth_rewrite 2 [h]
          exact hsum.symm
        have hn := outer_iform_self_of_simplyLaced hsl hδr
        rw [e] at hn
        simp only [iform_add_left, iform_add_right, hβn] at hn
        omega
      have hne2 : β ≠ -(δ - β) := fun h => by
        have e : β + (δ - β) = 0 := by
          calc β + (δ - β) = -(δ - β) + (δ - β) := by rw [← h]
            _ = 0 := neg_add_cancel _
        rw [hsum] at e
        rw [e] at hδr
        exact hδr.ne_zero rfl
      have h := outer_commute_pinnedX_of_sum hsl hβr hsubr (by rw [hsum]; exact hδr) hne1 hne2
        (hnonfixed β hβ hβf) (hnonfixed _ hsubΨ hsubf)
      rwa [hsum] at h
    · exact hnonfixed δ hδ hδf
  have hmap : (rootSpan τ L (componentRoots (rootCharHom a) i)).map
      (MulAut.conj z₀).toMonoidHom ≤ Subgroup.centralizer {z} := by
    simp only [rootSpan, Subgroup.map_iSup]
    refine iSup₂_le fun γ hγ => ?_
    rw [rootSubgroup, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 (hall γ hγ t).symm.eq
  intro g hg
  have hg' : z₀⁻¹ * g * z₀ ∈ rootSpan τ L (componentRoots (rootCharHom a) i) := by
    refine (hz₀n _).2 ?_
    have : z₀ * (z₀⁻¹ * g * z₀) * z₀⁻¹ = g := by group
    rw [this]
    exact hg
  have hcalc : (MulAut.conj z₀).toMonoidHom (z₀⁻¹ * g * z₀) = g := by
    show z₀ * (z₀⁻¹ * g * z₀) * z₀⁻¹ = g
    group
  have hmem : g ∈ Subgroup.centralizer {z} := hmap (Subgroup.mem_map.2 ⟨_, hg', hcalc⟩)
  exact Commute.symm (Subgroup.mem_centralizer_singleton_iff.1 hmem)

end Assembly

theorem anyKindCommuteThreeFull_holds : CrossChar.AnyKindCommuteThreeFull := by
  intro τ L _ _ p S hsl hq a hT i hrk z hcomm
  have hτ : τ ≠ .G2 := by rcases hsl with h | h | h | h <;> rw [h] <;> decide
  obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
  by_cases hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1
  · by_cases hin : twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)])
    · have hsl1 : ∀ j, τ.symmetrizer j j = 1 := by
        rcases hsl with h | h | h | h <;> subst h <;> intro j <;> simp [Tag.symmetrizer]
      exact commute_rootSpan_of_commute_component_three_T S hτ hsl1 hT i hin hs1 hq (hrk hs1) z
        hcomm
    · exact commute_rootSpan_of_commute_component_outer_three S hsl hq hT i hs1 hin z hcomm
  · have hQ4 : 4 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) := by
      rw [hq]
      calc 4 ≤ 3 ^ 2 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact commute_rootSpan_of_commute_component_anyT S hτ hT i (by omega) hQ4 z hcomm

end CFSG.HardMathSupport.Timmesfeld.LangTorus
