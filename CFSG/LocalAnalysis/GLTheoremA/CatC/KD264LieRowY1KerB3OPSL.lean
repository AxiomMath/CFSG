module

public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalThreeSimilarityGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KB3O

open Matrix QuadraticMap Module CFSG.ComponentClassification.CatalogueBOrthogonal
  CFSG.ComponentClassification.CatalogueBOrthogonalThreeSimilarity

section Basic

variable {K : Type} [Field K] [Finite K]

theorem not_dvd_card_of_ne_zero {ℓ : ℕ} (hℓ : ℓ.Prime) (hK : (ℓ : K) ≠ 0) :
    ¬ ℓ ∣ Nat.card K := by
  intro hdvd
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  rw [← Nat.card_eq_fintype_card] at hn
  rw [hn] at hdvd
  have h1 : ℓ ∣ ringChar K := hℓ.dvd_of_dvd_pow hdvd
  have h2 : ℓ = ringChar K := (Nat.prime_dvd_prime_iff_eq hℓ hp).mp h1
  apply hK
  rw [h2]
  exact CharP.cast_eq_zero K (ringChar K)

theorem odd_card (h2 : (2 : K) ≠ 0) : Odd (Nat.card K) := by
  have h : ¬ 2 ∣ Nat.card K := not_dvd_card_of_ne_zero Nat.prime_two (by exact_mod_cast h2)
  exact Nat.odd_iff.mpr (by omega)

theorem four_le_card (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) : 4 ≤ Nat.card K := by
  have hodd := odd_card h2
  have hne3 : ¬ 3 ∣ Nat.card K := not_dvd_card_of_ne_zero Nat.prime_three (by exact_mod_cast h3)
  have hpos : 1 < Nat.card K := Finite.one_lt_card
  obtain ⟨m, hm⟩ := hodd
  omega

theorem not_comm_of_perfect {G : Type*} [Group G] [Nontrivial G] (hp : Group.IsPerfect G) :
    ¬ ∀ x y : G, x * y = y * x := by
  intro h
  have h2 : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ ≤ ⊥ := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact h a b
  have h3 : (⊤ : Subgroup G) ≤ ⊥ := by
    rw [← hp.commutator_eq_top]
    exact h2
  obtain ⟨a, b, hab⟩ := exists_pair_ne G
  have ha := Subgroup.mem_bot.mp (h3 (Subgroup.mem_top a))
  have hb := Subgroup.mem_bot.mp (h3 (Subgroup.mem_top b))
  exact hab (ha.trans hb.symm)

end Basic

section PSL2

variable {K : Type} [Field K] [Finite K]

theorem psl2_isSimple (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := by
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact four_le_card h2 h3)
  exact (CFSG.LinearGroups.linear_projective_simple (K := K) (n := 2) le_rfl
    (Or.inr ⟨s, hs⟩)).2.1

theorem psl2_isPerfect (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := by
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact four_le_card h2 h3)
  exact CFSG.LinearGroups.linear_projective_perfect (K := K) (n := 2) le_rfl (Or.inr ⟨s, hs⟩)

theorem psl2_card (h2 : (2 : K) ≠ 0) :
    2 * Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) =
      Nat.card K * (Nat.card K ^ 2 - 1) := by
  have hodd := odd_card h2
  have hiso := Nat.card_congr
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).toEquiv
  have h := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := K) (n := 2)
    (by norm_num)
  rw [← hiso] at h
  have hgcd : Nat.gcd 2 (Nat.card K - 1) = 2 := by
    obtain ⟨m, hm⟩ := hodd
    apply Nat.gcd_eq_left
    omega
  rw [h, hgcd]
  simp only [show 2 * (2 - 1) / 2 = 1 by norm_num, pow_one, Finset.Icc_self,
    Finset.prod_singleton]
  have hdvd : 2 ∣ Nat.card K * (Nat.card K ^ 2 - 1) := by
    obtain ⟨m, hm⟩ := hodd
    apply Dvd.dvd.mul_left
    have : Nat.card K ^ 2 - 1 = (2 * m + 1) ^ 2 - 1 := by rw [hm]
    rw [this]
    exact ⟨2 * m * m + 2 * m, by ring_nf; omega⟩
  rw [Nat.mul_div_cancel' hdvd]

theorem three_dvd_psl2 (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    3 ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := by
  have hc := psl2_card h2
  have hq3 : ¬ 3 ∣ Nat.card K := not_dvd_card_of_ne_zero Nat.prime_three (by exact_mod_cast h3)
  have hsq : 3 ∣ Nat.card K ^ 2 - 1 := by
    obtain ⟨k, hk⟩ : ∃ k, Nat.card K = 3 * k + 1 ∨ Nat.card K = 3 * k + 2 :=
      ⟨Nat.card K / 3, by omega⟩
    rcases hk with hk | hk <;> rw [hk]
    · exact ⟨3 * k * k + 2 * k, by ring_nf; omega⟩
    · exact ⟨3 * k * k + 4 * k + 1, by ring_nf; omega⟩
  have h2' : 3 ∣ 2 * Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := by
    rw [hc]
    exact Dvd.dvd.mul_left hsq _
  exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num : Nat.Coprime 3 2) h2')

end PSL2

section PGL

def pslHom (K : Type) [Field K] : Matrix.SpecialLinearGroup (Fin 2) K →*
    Matrix.ProjGenLinGroup (Fin 2) K :=
  Matrix.ProjGenLinGroup.mk.comp (Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := K))

theorem pslHom_ker_eq (K : Type) [Field K] :
    (pslHom K).ker = Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) := by
  apply Subgroup.ext
  intro x
  rw [MonoidHom.mem_ker]
  unfold pslHom
  rw [MonoidHom.comp_apply, Matrix.ProjGenLinGroup.mk_eq_one,
    GeneralLinearGroup.mem_center_iff_val_mem_range_scalar, Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨c, hc⟩
    have hdet : (Matrix.scalar (Fin 2) c).det = 1 := by rw [hc]; exact Matrix.SpecialLinearGroup.det_coe x
    rw [Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_two] at hdet
    exact ⟨c, by rw [Fintype.card_fin, pow_two]; exact hdet, hc⟩
  · rintro ⟨r, -, hrx⟩
    have hr : r ≠ 0 := by
      rintro rfl
      have := Matrix.SpecialLinearGroup.det_coe x
      rw [← hrx, Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_two] at this
      simp at this
    exact ⟨Units.mk0 r hr, by simp [hrx]⟩

theorem pslHom_range_normal (K : Type) [Field K] (x : Matrix.ProjGenLinGroup (Fin 2) K)
    {y : Matrix.ProjGenLinGroup (Fin 2) K} (hy : y ∈ (pslHom K).range) :
    x * y * x⁻¹ ∈ (pslHom K).range := by
  obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective x
  obtain ⟨s, rfl⟩ := hy
  have h1 : (A : Matrix (Fin 2) (Fin 2) K).det * (A⁻¹ : GL (Fin 2) K).val.det = 1 := by
    rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
  have hdet : ((A : Matrix (Fin 2) (Fin 2) K) * (s : Matrix (Fin 2) (Fin 2) K) *
      ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe s, mul_one, h1]
  refine ⟨⟨_, hdet⟩, ?_⟩
  show Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL
    (⟨_, hdet⟩ : Matrix.SpecialLinearGroup (Fin 2) K)) =
      Matrix.ProjGenLinGroup.mk A * Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL s) *
        (Matrix.ProjGenLinGroup.mk A)⁻¹
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Units.ext
  simp [Matrix.SpecialLinearGroup.toGL]

noncomputable def pslIso (K : Type) [Field K] :
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) K ≃* (pslHom K).range :=
  (QuotientGroup.quotientMulEquivOfEq (pslHom_ker_eq K).symm).trans
    (QuotientGroup.quotientKerEquivRange (pslHom K))

end PGL

section Core

open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.ComponentClassification.CatalogueBLinearTwo

theorem inl_injective' (G H : Type) [Group G] [Group H] :
    Function.Injective (MonoidHom.inl G H) :=
  fun a b h => by simpa using congrArg Prod.fst h

noncomputable def psdND (K : Type) [Field K] : Subgroup (coordinateD K) :=
  ((pslHom K).range).map (pglEquivCoordinateD_all_fields K).toMonoidHom

noncomputable def psdN1 (K : Type) [Field K] : Subgroup (coordinateD K × rootsOfUnity 2 K) :=
  (psdND K).map (MonoidHom.inl (coordinateD K) (rootsOfUnity 2 K))

theorem psdND_normal (K : Type) [Field K] (g : coordinateD K) {n : coordinateD K}
    (hn : n ∈ psdND K) : g * n * g⁻¹ ∈ psdND K := by
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hn
  obtain ⟨x, rfl⟩ := (pglEquivCoordinateD_all_fields K).surjective g
  exact Subgroup.mem_map.mpr ⟨x * y * x⁻¹, pslHom_range_normal K x hy, by simp⟩

theorem psdN1_normal (K : Type) [Field K] (g : coordinateD K × rootsOfUnity 2 K)
    {n : coordinateD K × rootsOfUnity 2 K} (hn : n ∈ psdN1 K) : g * n * g⁻¹ ∈ psdN1 K := by
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hn
  refine Subgroup.mem_map.mpr ⟨g.1 * y * g.1⁻¹, psdND_normal K g.1 hy, ?_⟩
  ext
  · simp
  · simp

end Core

section Core2

open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.ComponentClassification.CatalogueBLinearTwo

variable {K : Type} [Field K] [Finite K]

theorem three_component {U : Type} [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) (Q : QuadraticForm K U)
    (hnd : (polarBilin Q).Nondegenerate) (hdim : Module.finrank K U = 3) :
    ∃ N : Subgroup (U ≃ₗ[K] U), N ≤ TauCeti.QuadraticMap.orthogonalGroup Q ∧
      (∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, ∀ n ∈ N, g * n * g⁻¹ ∈ N) ∧
      IsSimpleGroup N ∧ Group.IsPerfect N ∧ (¬ ∀ x y : N, x * y = y * x) ∧ 3 ∣ Nat.card N := by
  classical
  have hodd : Odd (Nat.card K) := odd_card h2
  obtain ⟨d, psi, e, -, -, -⟩ :=
    exists_trace_zero_similarity_and_orthogonal_equiv hodd Q hnd hdim
  obtain ⟨Θ, -⟩ := trace_zero_three_full_orthogonal_isometry h2
  let Ψ : TauCeti.QuadraticMap.orthogonalGroup Q ≃* (coordinateD K × rootsOfUnity 2 K) :=
    e.trans Θ.symm
  let NQ : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q) := (psdN1 K).comap Ψ.toMonoidHom
  have hNQ : ∀ g : TauCeti.QuadraticMap.orthogonalGroup Q, ∀ n ∈ NQ, g * n * g⁻¹ ∈ NQ := by
    intro g n hn
    rw [Subgroup.mem_comap] at hn ⊢
    have hc : Ψ.toMonoidHom (g * n * g⁻¹) = Ψ g * Ψ n * (Ψ g)⁻¹ := by simp
    rw [hc]
    exact psdN1_normal K (Ψ g) hn
  have hΨ : NQ.map Ψ.toMonoidHom = psdN1 K :=
    Subgroup.map_comap_eq_self_of_surjective Ψ.surjective (psdN1 K)
  have A1 : NQ.map (TauCeti.QuadraticMap.orthogonalGroup Q).subtype ≃* NQ :=
    (NQ.equivMapOfInjective _ (TauCeti.QuadraticMap.orthogonalGroup Q).subtype_injective).symm
  have A2 : NQ ≃* psdN1 K := (MulEquiv.subgroupMap Ψ NQ).trans (MulEquiv.subgroupCongr hΨ)
  have A3 : psdN1 K ≃* psdND K :=
    ((psdND K).equivMapOfInjective (MonoidHom.inl (coordinateD K) (rootsOfUnity 2 K))
      (inl_injective' _ _)).symm
  have A4 : psdND K ≃* (pslHom K).range :=
    (((pslHom K).range).equivMapOfInjective (pglEquivCoordinateD_all_fields K).toMonoidHom
      (pglEquivCoordinateD_all_fields K).injective).symm
  let Φ : NQ.map (TauCeti.QuadraticMap.orthogonalGroup Q).subtype ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
    A1.trans (A2.trans (A3.trans (A4.trans (pslIso K).symm)))
  refine ⟨NQ.map (TauCeti.QuadraticMap.orthogonalGroup Q).subtype, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · intro g hg n hn
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hn
    have key := hNQ ⟨g, hg⟩ m hm
    exact Subgroup.mem_map.mpr ⟨_, key, by simp⟩
  · haveI := psl2_isSimple h2 h3
    exact Φ.isSimpleGroup
  · haveI := psl2_isPerfect h2 h3
    exact Group.IsPerfect.ofSurjective (f := Φ.symm.toMonoidHom) Φ.symm.surjective
  · haveI := (psl2_isSimple h2 h3).toNontrivial
    haveI : Nontrivial (NQ.map (TauCeti.QuadraticMap.orthogonalGroup Q).subtype) :=
      Φ.toEquiv.nontrivial
    haveI := psl2_isPerfect h2 h3
    exact not_comm_of_perfect (Group.IsPerfect.ofSurjective (f := Φ.symm.toMonoidHom)
      Φ.symm.surjective)
  · rw [Nat.card_congr Φ.toEquiv]
    exact three_dvd_psl2 h2 h3

end Core2

end KB3O

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
