module

public import CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding.RankOneTorus
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding.PlaneConj
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding.PlanePair
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding.ClassInvariant
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding.QuadExt
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding.StdTransport
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding.SylowCentral

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.RF4 CFSG.Quasithin.G2U CFSG.RankThree.Chevalley
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.RankThree.QuadraticSL2 CFSG.RankThree.Classical
  CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator
  CFSG.ComponentClassification.UnbalancedCatalog

section Fin3

theorem fin3_mem_span : ∀ j₂ j : Fin 3, j₂ ≠ 0 → j = 0 ∨ j = j₂ ∨ j = j₂ + j₂ := by decide

theorem fin3_shear : ∀ i j : Fin 3, i ≠ 0 → ∃ k : Fin 3, j + k * i = i := by decide

theorem fin3_double_ne : ∀ i : Fin 3, i ≠ 0 → i + i ≠ 0 := by decide

theorem fin3_ne_zero : ∀ j : Fin 3, j ≠ 0 → j = 1 ∨ j = 2 := by decide

end Fin3

theorem mem_zpowers_conj_iff {G : Type*} [Group G] (x z e : G) :
    x * e * x⁻¹ ∈ Subgroup.zpowers (x * z * x⁻¹) ↔ e ∈ Subgroup.zpowers z := by
  constructor
  · rintro ⟨k, hk⟩
    have : (MulAut.conj x) (z ^ k) = (MulAut.conj x) e := by
      rw [map_zpow]
      simpa [MulAut.conj_apply] using hk
    exact ⟨k, (MulAut.conj x).injective this⟩
  · rintro ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    simp

section Torus

variable {L : Type} [Field L]

theorem not_conj_A2 {ζ : Lˣ} (hζ : orderOf ζ = 3) {j : Fin 3} (hj : j ≠ 0) {i : Fin 3}
    (hi : i ≠ 0) (j' : Fin 3) (y : ModGL .G2 L) :
    y * rootDiagUnit .G2 (cubeTuple3 ζ 0 j) * y⁻¹ ≠ rootDiagUnit .G2 (cubeTuple3 ζ i j') := by
  intro h
  rcases fin3_ne_zero j hj with rfl | rfl
  · exact not_conj_rootDiag_A2_A1 hζ j' hi y h
  · have hmul : rootDiagUnit .G2 (cubeTuple3 ζ 0 1) =
        rootDiagUnit .G2 (cubeTuple3 ζ 0 2) * rootDiagUnit .G2 (cubeTuple3 ζ 0 2) := by
      rw [← rootDiagUnit_mul, cubeTuple3_mul hζ]
      rfl
    refine not_conj_rootDiag_A2_A1 hζ (j' + j') (fin3_double_ne i hi) y ?_
    rw [hmul]
    calc y * (rootDiagUnit .G2 (cubeTuple3 ζ 0 2) * rootDiagUnit .G2 (cubeTuple3 ζ 0 2)) * y⁻¹
        = (y * rootDiagUnit .G2 (cubeTuple3 ζ 0 2) * y⁻¹) *
          (y * rootDiagUnit .G2 (cubeTuple3 ζ 0 2) * y⁻¹) := by group
      _ = rootDiagUnit .G2 (cubeTuple3 ζ (i + i) (j' + j')) := by
        rw [h, ← rootDiagUnit_mul, cubeTuple3_mul hζ]

end Torus

variable {K K₂ : Type} [Field K] [Finite K] [Field K₂] [Algebra K K₂] [Finite K₂]
  {σ : K₂ ≃+* K₂}

theorem exists_orderOf_three_of_finrank (hdeg : Module.finrank K K₂ = 2)
    (h3 : 3 ∣ Nat.card K + 1) : ∃ ζ : K₂ˣ, orderOf ζ = 3 := by
  have hq2 : Nat.card K₂ = Nat.card K ^ 2 := natCard_eq_sq_of_finrank_eq_two hdeg
  have h3₂ : 3 ∣ Nat.card K₂ - 1 := by
    rw [hq2]
    have : Nat.card K ^ 2 - 1 = (Nat.card K - 1) * (Nat.card K + 1) := by
      have hq1 : 1 ≤ Nat.card K := Nat.card_pos
      zify [hq1, Nat.one_le_pow 2 _ hq1]
      ring
    rw [this]
    exact Dvd.dvd.mul_left h3 _
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : 3 ∣ Nat.card K₂ˣ := by
    rw [Nat.card_units]
    exact h3₂
  exact exists_prime_orderOf_dvd_card' 3 hcard

theorem QPlusModel.sylow_pair_normal_form
    (M : QPlusModel K σ) (hdeg : Module.finrank K K₂ = 2)
    (hσ : ∀ c, σ c = c ^ Nat.card K) (h3 : 3 ∣ Nat.card K + 1)
    (P : Sylow 3 (adjointGroup .G2 K)) {z : adjointGroup .G2 K} (_hzP : z ∈ P)
    (hzc : ∀ x ∈ P, x * z = z * x) (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1)
    {e : adjointGroup .G2 K} (heP : e ∈ P) (he1 : e ≠ 1) (he3 : e ^ 3 = 1)
    (hez : e ∉ Subgroup.zpowers z) :
    ∃ x : adjointGroup .G2 K, x * z * x⁻¹ = zStd K ∧ x * e * x⁻¹ = eStd K := by
  have : Finite (Module.End K₂ (RootModule .G2 K₂)) := Module.finite_of_finite K₂
  have : Finite (Module.End K (RootModule .G2 K)) := Module.finite_of_finite K
  have : Finite (adjointGroup .G2 K) := inferInstance
  obtain ⟨ζ, hζ⟩ := exists_orderOf_three_of_finrank hdeg h3
  obtain ⟨P₀, n, hE, hnP, hnm, hnw⟩ := M.exists_sylow_E0G hdeg hσ hζ
  obtain ⟨x₁, hx₁⟩ := MulAction.exists_smul_eq (adjointGroup .G2 K) P P₀
  set z₁ := x₁ * z * x₁⁻¹ with hz₁
  set e₁ := x₁ * e * x₁⁻¹ with he₁
  have hz₁c : ∀ y ∈ P₀, y * z₁ = z₁ * y := by
    rw [← hx₁]
    exact mem_smul_sylow_comm P hzc x₁
  have he₁P : e₁ ∈ P₀ := by
    rw [← hx₁, ← SetLike.mem_coe, Sylow.coe_smul]
    exact ⟨e, heP, by simp only [MulAut.smul_def, MulAut.conj_apply]; rfl⟩
  have hz₁1 : z₁ ≠ 1 := fun h => hz1 (by simpa [hz₁] using h)
  have he₁1 : e₁ ≠ 1 := fun h => he1 (by simpa [he₁] using h)
  have hz₁3 : z₁ ^ 3 = 1 := by simp [hz₁, conj_pow, hz3]
  have he₁3 : e₁ ^ 3 = 1 := by simp [he₁, conj_pow, he3]
  have hez₁ : e₁ ∉ Subgroup.zpowers z₁ := fun h => hez ((mem_zpowers_conj_iff x₁ z e).1 h)
  obtain ⟨j₁, hj₁, hψz₁⟩ := M.central_mem_E0 hσ h3 hζ (P₀ := P₀) (n := n) hE hnP hnm hnw
    hz₁c hz₁1 hz₁3
  have hcomm : z₁ * e₁ = e₁ * z₁ := (hz₁c e₁ he₁P).symm
  obtain ⟨E, hzE, heE, hEel, hEcard⟩ := exists_plane_of_pair hcomm hz₁3 he₁3 hz₁1 hez₁
  obtain ⟨y, hyΓ, hy⟩ := M.exists_conj_plane_to_torsion hdeg hσ h3 E hEcard
  obtain ⟨y₀, rfl⟩ := M.exists_twistEmb_eq hyΓ
  have hconjE : ∀ t ∈ E, twistEmb (K := K) M.g (y₀ * t * y₀⁻¹) ∈ torusTorsion K₂ 3 := by
    intro t ht
    have : (MulAut.conj (twistEmb (K := K) M.g y₀)).toMonoidHom (twistEmb (K := K) M.g t) ∈
        (E.map (twistEmb (K := K) M.g)).map (MulAut.conj (twistEmb (K := K) M.g y₀)).toMonoidHom :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ ht)
    rw [hy] at this
    simpa [MulAut.conj_apply, map_mul, map_inv] using this
  set z₂ := y₀ * z₁ * y₀⁻¹ with hz₂
  set e₂ := y₀ * e₁ * y₀⁻¹ with he₂
  have hz₂E : twistEmb (K := K) M.g z₂ ∈ torusTorsion K₂ 3 := hconjE z₁ hzE
  have he₂E : twistEmb (K := K) M.g e₂ ∈ torusTorsion K₂ 3 := hconjE e₁ heE
  have hz₂1 : z₂ ≠ 1 := fun h => hz₁1 (by simpa [hz₂] using h)
  have he₂1 : e₂ ≠ 1 := fun h => he₁1 (by simpa [he₂] using h)
  have hz₂3 : z₂ ^ 3 = 1 := by simp [hz₂, conj_pow, hz₁3]
  have he₂3 : e₂ ^ 3 = 1 := by simp [he₂, conj_pow, he₁3]
  have hez₂ : e₂ ∉ Subgroup.zpowers z₂ := fun h => hez₁ ((mem_zpowers_conj_iff y₀ z₁ e₁).1 h)
  obtain ⟨i₂, j₂, hψz₂⟩ := exists_cubeTuple3_of_mem_torusTorsion hζ hz₂E
  have hi₂ : i₂ = 0 := by
    by_contra hi
    refine not_conj_A2 hζ hj₁ hi j₂ (twistEmb (K := K) M.g y₀) ?_
    rw [← hψz₁, ← hψz₂, hz₂]
    simp [map_mul, map_inv]
  subst hi₂
  have hj₂ : j₂ ≠ 0 := by
    rintro rfl
    apply hz₂1
    apply twistEmb_injective (K := K) M.g
    rw [hψz₂, cubeTuple3_zero, rootDiagUnit_one, map_one]
  obtain ⟨i, j, hψe₂⟩ := exists_cubeTuple3_of_mem_torusTorsion hζ he₂E
  have hi : i ≠ 0 := by
    rintro rfl
    apply hez₂
    rcases fin3_mem_span j₂ j hj₂ with rfl | rfl | rfl
    · exfalso
      apply he₂1
      apply twistEmb_injective (K := K) M.g
      rw [hψe₂, cubeTuple3_zero, rootDiagUnit_one, map_one]
    · have : e₂ = z₂ := by
        apply twistEmb_injective (K := K) M.g
        rw [hψe₂, hψz₂]
      rw [this]
      exact Subgroup.mem_zpowers z₂
    · have : e₂ = z₂ ^ 2 := by
        apply twistEmb_injective (K := K) M.g
        rw [hψe₂, map_pow, hψz₂, pow_two, ← rootDiagUnit_mul, cubeTuple3_mul hζ, add_zero]
      rw [this]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers z₂) 2
  obtain ⟨k, hk⟩ := fin3_shear i j hi
  have hkn : Fin.ofNat 3 k.val = k := Fin.ext (by simp [Fin.ofNat, Nat.mod_eq_of_lt k.2])
  set z₃ := n ^ k.val * z₂ * (n ^ k.val)⁻¹ with hz₃
  set e₃ := n ^ k.val * e₂ * (n ^ k.val)⁻¹ with he₃'
  have hψz₃ : twistEmb (K := K) M.g z₃ = rootDiagUnit .G2 (cubeTuple3 ζ 0 j₂) := by
    rw [hz₃, map_mul, map_mul, map_inv, map_pow, hψz₂,
      conj_pow_cubeTuple3 hζ hnm hnw 0 j₂ k.val]
    simp
  have hψe₃ : twistEmb (K := K) M.g e₃ = rootDiagUnit .G2 (cubeTuple3 ζ i i) := by
    rw [he₃', map_mul, map_mul, map_inv, map_pow, hψe₂,
      conj_pow_cubeTuple3 hζ hnm hnw i j k.val, hkn, hk]
  have hz₃1 : z₃ ≠ 1 := fun h => hz₂1 (by simpa [hz₃] using h)
  have he₃1 : e₃ ≠ 1 := fun h => he₂1 (by simpa [he₃'] using h)
  have hz₃3 : z₃ ^ 3 = 1 := by simp [hz₃, conj_pow, hz₂3]
  have he₃3 : e₃ ^ 3 = 1 := by simp [he₃', conj_pow, he₂3]
  obtain ⟨Cz, hCz⟩ := rootDiagUnit_cubeTuple3_zero_mem_v (ζ := ζ) (L := K₂) j₂
  obtain ⟨Ce, hCe⟩ := rootDiagUnit_cubeTuple3_diag_mem_a (L := K₂) hζ i
  obtain ⟨x₄, hx₄z, hx₄e⟩ := M.exists_conj_std hdeg hσ h3 hz₃3 he₃3 hz₃1 he₃1
    ⟨Cz, hψz₃.trans hCz⟩ ⟨Ce, hψe₃.trans hCe⟩
  refine ⟨x₄ * (n ^ k.val * y₀ * x₁), ?_, ?_⟩
  · have : x₄ * (n ^ k.val * y₀ * x₁) * z * (x₄ * (n ^ k.val * y₀ * x₁))⁻¹ =
        x₄ * z₃ * x₄⁻¹ := by
      rw [hz₃, hz₂, hz₁]; group
    rw [this, hx₄z]
  · have : x₄ * (n ^ k.val * y₀ * x₁) * e * (x₄ * (n ^ k.val * y₀ * x₁))⁻¹ =
        x₄ * e₃ * x₄⁻¹ := by
      rw [he₃', he₂, he₁]; group
    rw [this, hx₄e]

theorem g2SylowPairNormalForm :
    G2SylowPairNormalForm := by
  intro K _ _ _hK h3 P z hzP hzc hz1 hz3 e heP he1 he3 hez
  obtain ⟨K₂, _, _, hdeg, σ, hσ⟩ := exists_quadratic_frobenius_all K
  have : Finite K₂ := (quadratic_frobenius hdeg σ hσ).1
  have hM : Nonempty (QPlusModel K σ) := by
    by_cases h2 : ringChar K = 2
    · have : CharP K 2 := ringChar.of_eq h2
      exact QPlusModel.nonempty_of_charTwo hdeg hσ
    · have : Fintype K := Fintype.ofFinite K
      obtain ⟨p, hcp, n, hp, hcard⟩ := FiniteField.card' (K := K)
      have hpeq : p = ringChar K := CharP.eq K hcp (ringChar.charP K)
      have hp2 : p ≠ 2 := fun h => h2 (hpeq ▸ h)
      have hpo : Odd p := hp.eq_two_or_odd'.resolve_left hp2
      have hodd : Odd (Nat.card K) := by
        rw [Nat.card_eq_fintype_card, hcard]
        exact hpo.pow
      exact QPlusModel.nonempty_of_odd hodd hdeg hσ
  obtain ⟨M⟩ := hM
  obtain ⟨x, hx1, hx2⟩ := M.sylow_pair_normal_form hdeg hσ h3 P hzP hzc hz1 hz3 heP he1 he3 hez
  exact ⟨x, Or.inl hx1, Or.inl hx2⟩

omit [Finite K] [Field K₂] [Algebra K K₂] [Finite K₂] in
theorem g2SylowPairNormalForm_of_instances :
    G2SylowPairNormalForm :=
  g2SylowPairNormalForm

end CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding
