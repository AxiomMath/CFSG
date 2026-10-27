module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3BTorusOrbit
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BTorusDiag
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BTorusArith
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BAutAbelian

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.PartTwo.KFacts Matrix
  CFSG.Open CFSG.ComponentClassification
open scoped Pointwise

variable {K : Type} [Field K]

@[expose] noncomputable def torusSL (H : Subgroup Kˣ) :
    Subgroup (Matrix.SpecialLinearGroup (Fin 3) K) :=
  (diagTorus H).comap Matrix.SpecialLinearGroup.toGL

@[expose] noncomputable def torusPSL (H : Subgroup Kˣ) : Subgroup (projectiveSL 3 K) :=
  (torusSL H).map (proj 3 K)

theorem mem_torusSL {H : Subgroup Kˣ} {g : Matrix.SpecialLinearGroup (Fin 3) K} :
    g ∈ torusSL H ↔ ∃ d : Fin 3 → Kˣ, (∀ i, d i ∈ H) ∧
      (g : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal (fun i => (d i : K)) := by
  unfold torusSL
  rw [Subgroup.mem_comap, mem_diagTorus]
  constructor
  · rintro ⟨d, hd, h⟩
    exact ⟨d, hd, by simpa [coe_diagHom] using (congrArg Units.val h).symm⟩
  · rintro ⟨d, hd, h⟩
    exact ⟨d, hd, Units.ext (by simpa [coe_diagHom] using h.symm)⟩

theorem torusSL_exponent {H : Subgroup Kˣ} (hH : H ≤ coprimeThreeTorsion Kˣ)
    {g : Matrix.SpecialLinearGroup (Fin 3) K} (hg : g ∈ torusSL H) :
    ∃ N, Nat.Coprime 3 N ∧ g ^ N = 1 := by
  obtain ⟨N, hN, h⟩ := exists_pow_eq_one_of_mem_diagTorus hH (Subgroup.mem_comap.1 hg)
  refine ⟨N, hN, Matrix.SpecialLinearGroup.toGL_injective ?_⟩
  rw [map_pow, map_one]
  exact h

theorem coprime_card_torusPSL {H : Subgroup Kˣ} [Finite K] (hH : H ≤ coprimeThreeTorsion Kˣ) :
    Nat.Coprime 3 (Nat.card (torusPSL H)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
  intro h3
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
  obtain ⟨g, hg, hgx⟩ := x.2
  obtain ⟨N, hN, hgN⟩ := torusSL_exponent hH hg
  have h1 : (x : projectiveSL 3 K) ^ N = 1 := by
    rw [← hgx, ← map_pow, hgN, map_one]
  have h2 : orderOf x ∣ N := by
    rw [orderOf_dvd_iff_pow_eq_one]
    exact Subtype.ext (by simpa using h1)
  rw [hx] at h2
  exact absurd (Nat.Coprime.eq_one_of_dvd hN h2) (by norm_num)

theorem torusPSL_ne_bot {H : Subgroup Kˣ} (hH : ∃ a ∈ H, a ≠ 1) : torusPSL H ≠ ⊥ := by
  obtain ⟨a, haH, ha1⟩ := hH
  let d : Fin 3 → Kˣ := ![a, a⁻¹, 1]
  have hd : ∀ i, d i ∈ H := by
    intro i
    fin_cases i
    · exact haH
    · exact H.inv_mem haH
    · exact H.one_mem
  have hdet : (Matrix.diagonal (fun i => (d i : K))).det = 1 := by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    simp [d]
  let g : Matrix.SpecialLinearGroup (Fin 3) K := ⟨Matrix.diagonal (fun i => (d i : K)), hdet⟩
  have hg : g ∈ torusSL H := mem_torusSL.2 ⟨d, hd, rfl⟩
  intro hbot
  have hmem : proj 3 K g ∈ torusPSL H := Subgroup.mem_map_of_mem _ hg
  rw [hbot, Subgroup.mem_bot, proj_eq_one_iff] at hmem
  obtain ⟨c, -, hc⟩ := hmem
  have h0 := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 0 0) hc
  have h2 := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 2 2) hc
  simp [g, d] at h0 h2
  exact ha1 (Units.ext (by rw [h0, ← h2]; rfl))

theorem map_conjAut_torusPSL_le (H : Subgroup Kˣ) {A : GL (Fin 3) K}
    (hA : A ∈ Subgroup.normalizer (diagTorus H : Set (GL (Fin 3) K))) :
    (torusPSL H).map (conjAut 3 K A).toMonoidHom ≤ torusPSL H := by
  rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
  refine ⟨CatalogueBHigherLinearAction.slConjugation 3 K A g, ?_, (conjAut_proj A g).symm⟩
  show _ ∈ (diagTorus H).comap _
  rw [Subgroup.mem_comap, CatalogueBHigherLinearAction.toGL_slConjugation]
  exact (Subgroup.mem_normalizer_iff.1 hA _).1 (Subgroup.mem_comap.1 hg)

theorem map_fieldAut_torusPSL_le (H : Subgroup Kˣ)
    (hH : ∀ σ : K ≃+* K, ∀ a ∈ H, Units.map (σ : K →* K) a ∈ H) (σ : K ≃+* K) :
    (torusPSL H).map (fieldAut 3 K σ).toMonoidHom ≤ torusPSL H := by
  rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
  refine ⟨Matrix.SpecialLinearGroup.map σ.toRingHom g, ?_, (fieldAut_proj σ g).symm⟩
  obtain ⟨d, hd, hgd⟩ := mem_torusSL.1 hg
  refine mem_torusSL.2 ⟨fun i => Units.map (σ : K →* K) (d i), fun i => hH σ _ (hd i), ?_⟩
  ext i j
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    hgd, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem map_dualAut_torusPSL_le (H : Subgroup Kˣ) :
    (torusPSL H).map (dualAut 3 K).toMonoidHom ≤ torusPSL H := by
  rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
  refine ⟨(g⁻¹).transpose, ?_, (dualAut_proj g).symm⟩
  obtain ⟨d, hd, hgd⟩ := mem_torusSL.1 hg
  refine mem_torusSL.2 ⟨fun i => ∏ j ∈ Finset.univ.erase i, d j,
    fun i => prod_mem fun j _ => hd j, ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_transpose, Matrix.SpecialLinearGroup.coe_inv, hgd,
    Matrix.adjugate_diagonal, Matrix.diagonal_transpose]
  congr 1
  funext i
  simp only [Units.coe_prod]

theorem map_standardFieldGraph_torusPSL [Finite K] (H : Subgroup Kˣ)
    (hH : ∀ σ : K ≃+* K, ∀ a ∈ H, Units.map (σ : K →* K) a ∈ H)
    {r : MulAut (projectiveSL 3 K)} (hr : r ∈ standardFieldGraph 3 K) :
    (torusPSL H).map r.toMonoidHom = torusPSL H := by
  let St : Subgroup (MulAut (projectiveSL 3 K)) :=
    MulAction.stabilizer (MulAut (projectiveSL 3 K)) (torusPSL H)
  have hst : ∀ r : MulAut (projectiveSL 3 K),
      r ∈ St ↔ (torusPSL H).map r.toMonoidHom = torusPSL H := fun r => Iff.rfl
  have hle : standardFieldGraph 3 K ≤ St := by
    rw [standardFieldGraph, Subgroup.closure_le]
    rintro e (⟨σ, rfl⟩ | rfl)
    · exact (hst _).2 (map_eq_of_map_le _ _ (map_fieldAut_torusPSL_le H hH σ))
    · exact (hst _).2 (map_eq_of_map_le _ _ (map_dualAut_torusPSL_le H))
  exact (hst r).1 (hle hr)

theorem fixedTorus_projectiveSL [Finite K] (h3 : Nat.card K % 3 = 1) (h4 : Nat.card K ≠ 4) :
    FixedTorus (projectiveSL 3 K) := by
  have hH : ∀ σ : K ≃+* K, ∀ a ∈ coprimeThreeTorsion Kˣ,
      Units.map (σ : K →* K) a ∈ coprimeThreeTorsion Kˣ := by
    rintro σ a ⟨n, hn, ha⟩
    exact ⟨n, hn, by rw [← map_pow, ha, map_one]⟩
  obtain ⟨a, ha1, ha⟩ := exists_unit_ne_one_coprime_three K h3 h4
  refine fixedTorus_of_decomposition (conjAut 3 K) (standardFieldGraph 3 K)
    (monomialGroup ⊤) (torusPSL (coprimeThreeTorsion Kˣ)) ?_ ?_ ?_ ?_
    (torusPSL_ne_bot ⟨a, ha, ha1⟩) (coprime_card_torusPSL le_rfl)
  · intro α
    obtain ⟨A, r, hr, rfl⟩ := exists_conjAut_mul_mem_standardFieldGraph (le_refl 3) α
    exact ⟨A, r, hr, rfl⟩
  · intro r hr
    exact map_standardFieldGraph_torusPSL _ hH hr
  · intro A hA
    exact map_eq_of_map_le _ _
      (map_conjAut_torusPSL_le _ (monomialGroup_le_normalizer ⊤ _ hA))
  · have := Fintype.ofFinite K
    have hq : 1 < Nat.card K := Finite.one_lt_card
    have hcard := Subgroup.card_mul_index (monomialGroup (K := K) ⊤)
    rw [card_monomialGroup, Subgroup.card_top, Nat.card_units, Matrix.card_GL_field,
      ← Nat.card_eq_fintype_card] at hcard
    rw [mul_comm] at hcard
    exact not_dvd_index_gl _ _ h3 hq hcard

theorem fixedTorus_statedProj_sl [Finite K] (h3 : Nat.card K % 3 = 1) (h4 : Nat.card K ≠ 4) :
    FixedTorus (StatedProj (StatedSL 3 K)) :=
  FixedTorus.of_mulEquiv (psiPSL K) (fixedTorus_projectiveSL h3 h4)

end CFSG.HardMathSupport.Solomon.Coordinator
