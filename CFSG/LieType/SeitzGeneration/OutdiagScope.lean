module

public import CFSG.LieType.SeitzGeneration.OutdiagPlane
public import CFSG.LieType.SeitzGeneration.NonabLinear
public import CFSG.RankThree.PartOne.KC.LinearCommutantSemi
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartOne.KCLinComm CFSG.Open

section Bridge

variable {F : Type} [Field F]

theorem conjAut_proj_eq_of_mem_FixSL {g : GL (Fin 3) F} {k : SpecialLinearGroup (Fin 3) F}
    (hk : k ∈ FixSL (g : Matrix (Fin 3) (Fin 3) F)) :
    conjAut 3 F g (proj 3 F k) = proj 3 F k := by
  obtain ⟨ζ, hζ⟩ := hk
  have hdet : (g : Matrix (Fin 3) (Fin 3) F).det ≠ 0 := by
    have := (Matrix.GeneralLinearGroup.det g).ne_zero
    rwa [Matrix.GeneralLinearGroup.val_det_apply] at this
  have hζ3 : ζ ^ 3 = 1 := by
    have h := congrArg Matrix.det hζ
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_mul, k.2, Fintype.card_fin] at h
    have h' : (ζ ^ 3 - 1) * (g : Matrix (Fin 3) (Fin 3) F).det = 0 := by linear_combination -h
    exact sub_eq_zero.1 ((mul_eq_zero.1 h').resolve_right hdet)
  have hζ0 : ζ ≠ 0 := fun h => by rw [h] at hζ3; norm_num at hζ3
  obtain ⟨u, hu⟩ : ∃ u : Fˣ, (u : F) = ζ := ⟨Units.mk0 ζ hζ0, rfl⟩
  have hu3 : u ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hu, hζ3, Units.val_one])
  have hz : proj 3 F (scalarElement u hu3) = 1 :=
    proj_eq_one_iff.2 (scalarElement_mem_scalars u hu3)
  rw [conjAut_proj]
  have hconj : CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F g k =
      k * scalarElement u hu3 := by
    apply Subtype.ext
    rw [coe_slConjugation, Matrix.SpecialLinearGroup.coe_mul, coe_scalarElement,
      Matrix.scalar_apply, ← Matrix.smul_eq_mul_diagonal, hu, hζ, Matrix.smul_mul, Matrix.mul_assoc,
      Units.mul_inv, Matrix.mul_one]
  rw [hconj, map_mul, hz, mul_one]

theorem conj_mem_linearAutGroup {n : ℕ} (p : projectiveSL n F) :
    (MulAut.conj p : MulAut (projectiveSL n F)) ∈ linearAutGroup n F := by
  obtain ⟨k, rfl⟩ := proj_surjective n F p
  refine mem_linearAutGroup_iff.2 ⟨SpecialLinearGroup.toGL k, ?_⟩
  ext g'
  obtain ⟨g, rfl⟩ := proj_surjective n F g'
  have h : CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n F
      (SpecialLinearGroup.toGL k) g = k * g * k⁻¹ := by
    apply Subtype.ext
    rw [coe_slConjugation, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      ← map_inv SpecialLinearGroup.toGL k]
    rfl
  rw [conjAut_proj, h, map_mul, map_mul, map_inv, MulAut.conj_apply]

variable [Finite F]

theorem planeGen_of_planeFix {E : Subgroup (MulAut (projectiveSL 3 F))} {x y : GL (Fin 3) F}
    (hx : conjAut 3 F x ∈ E) (hy : conjAut 3 F y ∈ E) (h₁ : NonScalarGL x) (h₂ : NonScalarGL y)
    (h₃ : NonScalarGL (x * y)) (h₄ : NonScalarGL (x * y ^ 2))
    (hgen : Subgroup.closure (planeFix x y) = ⊤) : PlaneGen E := by
  have hne : ∀ g : GL (Fin 3) F, NonScalarGL g → conjAut 3 F g ≠ 1 := fun g hg h => by
    obtain ⟨c, hc⟩ := (conjAut_eq_one_iff (le_refl 3) g).1 h
    exact hg c hc.symm
  have key : ∀ g : GL (Fin 3) F, conjAut 3 F g ∈ E → NonScalarGL g →
      ∀ k ∈ FixSL (g : Matrix (Fin 3) (Fin 3) F),
        proj 3 F k ∈ {k' | ∃ e ∈ E, e ≠ 1 ∧ e k' = k'} := fun g hgE hgn k hk =>
    ⟨conjAut 3 F g, hgE, hne g hgn, conjAut_proj_eq_of_mem_FixSL hk⟩
  have hxy : conjAut 3 F (x * y) ∈ E := by rw [map_mul]; exact E.mul_mem hx hy
  have hxy2 : conjAut 3 F (x * y ^ 2) ∈ E := by
    rw [map_mul, map_pow]; exact E.mul_mem hx (E.pow_mem hy 2)
  unfold PlaneGen planeClosure
  rw [eq_top_iff]
  have hle : (Subgroup.closure (planeFix x y)).map (proj 3 F) ≤
      Subgroup.closure {k' : projectiveSL 3 F | ∃ e ∈ E, e ≠ 1 ∧ e k' = k'} := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    refine Subgroup.subset_closure ?_
    rcases hk with ((hk | hk) | hk) | hk
    · exact key x hx h₁ k hk
    · exact key y hy h₂ k hk
    · exact key (x * y) hxy h₃ k hk
    · exact key (x * y ^ 2) hxy2 h₄ k hk
  rw [hgen, Subgroup.map_top_of_surjective _ (proj_surjective 3 F)] at hle
  exact hle

theorem planeGen_of_linearAut (hcore : OuterHeisCore) (hF3 : 3 ∣ Nat.card F - 1)
    (h4 : 4 < Nat.card F) {E : Subgroup (MulAut (projectiveSL 3 F))} (hE : IsElemAbelian 3 E)
    (hc : Nat.card E = 3 ^ 2) (hlin : E ≤ linearAutGroup 3 F) : PlaneGen E := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hζ := exists_primitiveRoot_of_dvd_card_sub_one hp hF3
  obtain ⟨e₁, he₁, e₂, he₂, he₂1, he₁₂⟩ := exists_independent_pair hp E hE.2 hc
  have hcomm : e₂ * e₁ = e₁ * e₂ :=
    congrArg Subtype.val (hE.1.is_comm.comm (⟨e₂, he₂⟩ : E) ⟨e₁, he₁⟩)
  have hsc := fun c : Fˣ => (conjAut_eq_one_iff (n := 3) (K := F) (le_refl 3)
    (Matrix.GeneralLinearGroup.scalar (Fin 3) c)).2 ⟨c, rfl⟩
  obtain ⟨x, rfl⟩ := mem_linearAutGroup_iff.1 (hlin he₁)
  obtain ⟨y, rfl⟩ := mem_linearAutGroup_iff.1 (hlin he₂)
  set H : Subgroup (GL (Fin 3) F) := E.comap (conjAut 3 F) with hH
  have hHs : ∀ c : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ H := fun c => by
    rw [hH, Subgroup.mem_comap, hsc c]; exact E.one_mem
  obtain ⟨α, hα⟩ : ∃ α : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) α = x ^ 3 :=
    (conjAut_eq_one_iff (le_refl 3) _).1 (by rw [map_pow]; exact hE.2 _ he₁)
  obtain ⟨β, hβ⟩ : ∃ β : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) β = y ^ 3 :=
    (conjAut_eq_one_iff (le_refl 3) _).1 (by rw [map_pow]; exact hE.2 _ he₂)
  obtain ⟨ω, hω⟩ : ∃ ω : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) ω = y * x * (x * y)⁻¹ :=
    (conjAut_eq_one_iff (le_refl 3) _).1 (by
      rw [map_mul, map_mul, map_inv, map_mul, hcomm]; exact mul_inv_cancel _)
  have hyx : y * x = Matrix.GeneralLinearGroup.scalar (Fin 3) ω * (x * y) := by
    rw [hω, inv_mul_cancel_right]
  have hind : ∀ a b : ℕ,
      (∃ c : Fˣ, x ^ a * y ^ b = Matrix.GeneralLinearGroup.scalar (Fin 3) c) → 3 ∣ a ∧ 3 ∣ b := by
    rintro a b ⟨c, hcab⟩
    have h1 : conjAut 3 F x ^ a * conjAut 3 F y ^ b = 1 := by
      rw [← map_pow, ← map_pow, ← map_mul, hcab, hsc c]
    have h3x : conjAut 3 F x ^ 3 = 1 := hE.2 _ he₁
    have ha : 3 ∣ a := by
      by_contra ha
      apply he₁₂
      have h2 : conjAut 3 F x ^ a ∈ Subgroup.zpowers (conjAut 3 F y) := by
        have : conjAut 3 F x ^ a = (conjAut 3 F y ^ b)⁻¹ := eq_inv_of_mul_eq_one_left h1
        rw [this]
        exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) b)
      rcases (by omega : a % 3 = 1 ∨ a % 3 = 2) with h | h
      · rwa [pow_eq_pow_mod a h3x, h, pow_one] at h2
      · have h5 : conjAut 3 F x = (conjAut 3 F x ^ a) ^ 2 := by
          rw [← pow_mul, pow_eq_pow_mod (a * 2) h3x, show a * 2 % 3 = 1 by omega, pow_one]
        rw [h5]
        exact Subgroup.pow_mem _ h2 2
    refine ⟨ha, ?_⟩
    obtain ⟨k, rfl⟩ := ha
    have h6 : conjAut 3 F y ^ b = 1 := by
      rw [pow_mul, h3x, one_pow, one_mul] at h1; exact h1
    rw [← orderOf_eq_prime (hE.2 _ he₂) he₂1]
    exact orderOf_dvd_of_pow_eq_one h6
  obtain ⟨x', hx', y', hy', n₁, n₂, n₃, n₄, hgen⟩ := exists_pair_closure_planeFix hcore hF3 h4 hζ H
    hHs (Subgroup.mem_comap.2 he₁) (Subgroup.mem_comap.2 he₂) hyx hα.symm hβ.symm hind
  exact planeGen_of_planeFix (Subgroup.mem_comap.1 hx') (Subgroup.mem_comap.1 hy') n₁ n₂ n₃ n₄
    hgen

end Bridge

section Catalog

noncomputable def linearModel {q : TauCeti.PrimePower} [Fact q.p.Prime]
    (hv : (TauCeti.LieTypeIndex.A 2 q).Valid) :
    Cat ⟨.A 2 q, hv⟩ ≃* projectiveSL 3 (GaloisField q.p q.exponent) :=
  (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv).trans
    (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 _)

theorem planeGen_outer_A2_linear (hcore : OuterHeisCore) {q : TauCeti.PrimePower}
    [Fact q.p.Prime] (hv : (TauCeti.LieTypeIndex.A 2 q).Valid) (hq3 : 3 ∣ q.card - 1)
    (h4 : q.card ≠ 4)
    {E : Subgroup (MulAut (Cat ⟨.A 2 q, hv⟩))} (hE : IsElemAbelian 3 E) (hc : Nat.card E = 3 ^ 2)
    (hlin : E.map (MulAut.congr (linearModel hv)).toMonoidHom ≤
      linearAutGroup 3 (GaloisField q.p q.exponent)) : PlaneGen E := by
  have hcardF : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  have hq1 : 1 < q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact Nat.one_lt_pow q.exponent_pos.ne' q.prime_p.one_lt
  have hF3 : 3 ∣ Nat.card (GaloisField q.p q.exponent) - 1 := by rw [hcardF]; exact hq3
  have hF4 : 4 < Nat.card (GaloisField q.p q.exponent) := by rw [hcardF]; omega
  refine (planeGen_map_congr (linearModel hv) E).1 ?_
  refine planeGen_of_linearAut hcore hF3 hF4 ?_ ?_ hlin
  · exact CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hE _
  · rw [Subgroup.card_map_of_injective (MulAut.congr (linearModel hv)).injective, hc]

end Catalog

end CFSG.LieType.SeitzGeneration
