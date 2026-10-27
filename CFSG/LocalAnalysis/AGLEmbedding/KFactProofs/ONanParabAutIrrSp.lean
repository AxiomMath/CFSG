module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrTorus
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrLin
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartTwo.KFacts.AutPSp

public section

namespace CFSG.AGLEmbedding.ParabAutIrr

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne.OutStructure
open scoped commutatorElement

section Flag

variable {r : ℕ} {K : Type} [Field K]

theorem spCoordImage_isoFlag (σ : K ≃+* K) (i : ℕ) :
    spCoordImage (r := r) σ (isoFlag r K i) = isoFlag r K i := by
  ext v
  rw [mem_spCoordImage, mem_isoFlag, mem_isoFlag]
  simp only [map_eq_zero_iff _ σ.symm.injective]

theorem fieldSp_mem_stabilizer_isoFlag (σ : K ≃+* K) {g : StatedSp r K} {i : ℕ}
    (h : g ∈ stabilizer r K (isoFlag r K i)) :
    fieldSp r K σ g ∈ stabilizer r K (isoFlag r K i) := by
  have h2 : fieldSp r K σ g ∈
      (stabilizer r K (isoFlag r K i)).map (fieldSp r K σ).toMonoidHom := ⟨g, h, rfl⟩
  rwa [map_stabilizer_fieldSp, spCoordImage_isoFlag] at h2

theorem fieldSp_mem_borelSubgroup (σ : K ≃+* K) {g : StatedSp r K} (hg : g ∈ borelSubgroup r K) :
    fieldSp r K σ g ∈ borelSubgroup r K := by
  rw [mem_borelSubgroup_iff_isoFlag] at hg ⊢
  exact fun i h1 h2 => fieldSp_mem_stabilizer_isoFlag σ (hg i h1 h2)

theorem diagEntry_fieldSp (σ : K ≃+* K) (g : StatedSp r K) (i : Fin r) :
    diagEntry (fieldSp r K σ g) i = σ (diagEntry g i) := rfl

theorem mem_unipotent_iff_diagEntry {g : StatedSp r K} :
    g ∈ unipotent r K ↔ ∃ _ : g ∈ borelSubgroup r K, ∀ i, diagEntry g i = 1 := by
  constructor
  · intro hu
    have hB : g ∈ borelSubgroup r K := unipotent_le_borelSubgroup hu
    refine ⟨hB, fun i => ?_⟩
    have hk : (⟨g, hB⟩ : borelSubgroup r K) ∈ (SymplecticFlag.diagHom r K).ker := by
      rw [ker_diagHom]
      exact hu
    have h1 := congrFun (MonoidHom.mem_ker.1 hk) i
    have h2 := congrArg Units.val h1
    simpa [coe_diagHom_apply, diagEntry] using h2
  · rintro ⟨hB, hd⟩
    have hk : (⟨g, hB⟩ : borelSubgroup r K) ∈ (SymplecticFlag.diagHom r K).ker := by
      rw [MonoidHom.mem_ker]
      funext i
      apply Units.ext
      simpa [coe_diagHom_apply, diagEntry] using hd i
    rw [ker_diagHom] at hk
    exact hk

theorem fieldSp_mem_unipotent (σ : K ≃+* K) {g : StatedSp r K} (hg : g ∈ unipotent r K) :
    fieldSp r K σ g ∈ unipotent r K := by
  obtain ⟨hB, hd⟩ := mem_unipotent_iff_diagEntry.1 hg
  refine mem_unipotent_iff_diagEntry.2 ⟨fieldSp_mem_borelSubgroup σ hB, fun i => ?_⟩
  rw [diagEntry_fieldSp, hd i, map_one]

theorem fieldSp_mul_pow_inv_mem_unipotent {σ : K ≃+* K} {k : ℕ} (hk : ∀ x : K, σ x = x ^ k)
    {g : StatedSp r K} (hg : g ∈ borelSubgroup r K) :
    fieldSp r K σ g * (g ^ k)⁻¹ ∈ unipotent r K := by
  set g' : borelSubgroup r K := ⟨g, hg⟩ with hg'
  set h' : borelSubgroup r K := ⟨fieldSp r K σ g, fieldSp_mem_borelSubgroup σ hg⟩ with hh'
  have hdiag : SymplecticFlag.diagHom r K h' = (SymplecticFlag.diagHom r K g') ^ k := by
    funext i
    apply Units.ext
    simp only [Pi.pow_apply, Units.val_pow_eq_pow_val, coe_diagHom_apply]
    exact hk _
  have hc : h' * (g' ^ k)⁻¹ ∈ (SymplecticFlag.diagHom r K).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, hdiag, mul_inv_cancel]
  rw [ker_diagHom, Subgroup.mem_subgroupOf] at hc
  simpa [hg', hh'] using hc

theorem commutator_mem_unipotent {g h : StatedSp r K} (hg : g ∈ borelSubgroup r K)
    (hh : h ∈ borelSubgroup r K) : ⁅g, h⁆ ∈ unipotent r K := by
  set g' : borelSubgroup r K := ⟨g, hg⟩
  set h' : borelSubgroup r K := ⟨h, hh⟩
  have hc : ⁅g', h'⁆ ∈ (SymplecticFlag.diagHom r K).ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)
  rw [ker_diagHom, Subgroup.mem_subgroupOf] at hc
  simpa [g', h', commutatorElement_def] using hc

end Flag

section Proj

variable {r : ℕ} {K : Type} [Field K]

theorem fieldAut_mem_projUnipotent_iff (σ : K ≃+* K) (w : StatedProj (StatedSp r K)) :
    w ∈ projUnipotent r K ↔ fieldAut r K σ w ∈ projUnipotent r K := by
  have key : ∀ (τ : K ≃+* K) (w : StatedProj (StatedSp r K)), w ∈ projUnipotent r K →
      fieldAut r K τ w ∈ projUnipotent r K := by
    rintro τ _ ⟨g, hg, rfl⟩
    rw [fieldAut_proj]
    exact ⟨_, fieldSp_mem_unipotent τ hg, rfl⟩
  refine ⟨key σ w, fun hw => ?_⟩
  have := key σ⁻¹ _ hw
  rwa [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply] at this

theorem commutator_mem_projUnipotent {b c : StatedProj (StatedSp r K)} (hb : b ∈ projBorel r K)
    (hc : c ∈ projBorel r K) : ⁅b, c⁆ ∈ projUnipotent r K := by
  obtain ⟨g, hg, rfl⟩ := hb
  obtain ⟨h, hh, rfl⟩ := hc
  exact ⟨⁅g, h⁆, commutator_mem_unipotent hg hh, map_commutatorElement _ _ _⟩

theorem fieldAut_power_map {σ : K ≃+* K} {k : ℕ} (hk : ∀ x : K, σ x = x ^ k)
    {b : StatedProj (StatedSp r K)} (hb : b ∈ projBorel r K) :
    fieldAut r K σ b * (b ^ k)⁻¹ ∈ projUnipotent r K := by
  obtain ⟨g, hg, rfl⟩ := hb
  refine ⟨fieldSp r K σ g * (g ^ k)⁻¹, fieldSp_mul_pow_inv_mem_unipotent hk hg, ?_⟩
  rw [map_mul, map_inv, map_pow, fieldAut_proj]

end Proj

section Aut

variable {r : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

omit [CharP K 2] in
theorem mem_spSemilinearAutGroup_of_pow (hr : 2 ≤ r) {α : MulAut (StatedProj (StatedSp r K))}
    {e : ℕ} (hodd : Odd e) (hα : α ^ e ∈ inn (StatedProj (StatedSp r K))) :
    α ∈ spSemilinearAutGroup r K := by
  rcases Nat.eq_or_lt_of_le hr with rfl | hr3
  · obtain ⟨-, -, -, hidx⟩ :=
      CFSG.ComponentClassification.CatalogueBSymplecticTwo.kernel_generation (K := K)
    refine mem_of_pow_mem_of_index_le_two _ hidx hodd ?_
    obtain ⟨A, hA⟩ := CFSG.RankThree.PartTwo.KFacts.innAut_le_range_spConjAut 2 K hα
    rw [← hA]
    exact spLinearAutGroup_le_spSemilinearAutGroup (conjAut_mem_spLinearAutGroup A)
  · exact (automorphism_generation (K := K) hr3).1 ▸ Subgroup.mem_top α

theorem autScalarTorus_projSp (hr : 2 ≤ r) : AutScalarTorus (StatedProj (StatedSp r K)) := by
  have : NeZero r := ⟨by omega⟩
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨S₁, hS₁⟩ := exists_sylow_projUnipotent (K := K) 2 (r := r) (by omega)
  have hN : Subgroup.normalizer ((S₁ : Subgroup (StatedProj (StatedSp r K))) : Set _) =
      projBorel r K := by
    rw [hS₁]
    exact normalizer_projUnipotent 2 (by omega)
  refine AutScalarTorus.of_decomp S₁ ?_ ?_
  · intro b hb c hc
    rw [hN] at hb hc
    rw [hS₁]
    exact commutator_mem_projUnipotent hb hc
  · rintro α ⟨e, he, he6, hinn⟩
    have hodd : Odd e :=
      Nat.Coprime.odd_of_right (Nat.Coprime.coprime_dvd_right (by norm_num) he6)
    obtain ⟨A, σ, hασ⟩ :=
      mem_spSemilinearAutGroup_iff.mp (mem_spSemilinearAutGroup_of_pow hr hodd hinn)
    obtain ⟨j, hj⟩ := exists_pow_two_of_ringEquiv σ
    have hA : conjAut r K A ∈ inn (StatedProj (StatedSp r K)) :=
      conjAut_mem_inner_of_isSquare (FiniteField.isSquare_of_char_two (ringChar.eq K 2) _)
    obtain ⟨x, hx⟩ := hA
    refine ⟨x, fieldAut r K σ, 2 ^ j, by rw [hασ, ← hx], fun w => ?_, fun b hb => ?_⟩
    · rw [hS₁]
      exact fieldAut_mem_projUnipotent_iff σ w
    · rw [hN] at hb
      rw [hS₁]
      exact fieldAut_power_map hj hb

theorem outPInner_projSp_two {p : ℕ} (hK : Nat.card K = 2) (hr : 3 ≤ r) :
    OutPInner (StatedProj (StatedSp r K)) p := by
  have : NeZero r := ⟨by omega⟩
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨-, hgen⟩ := automorphism_generation (K := K) hr
  intro P _ x _
  obtain ⟨A, σ, rfl⟩ := hgen x
  have hσ : σ = 1 := by
    obtain ⟨-, -, -, -, hcard, -⟩ := finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (le_refl 1) (show Nat.card K = 2 ^ 1 by simpa using hK)
    have := (Nat.card_eq_one_iff_unique.1 hcard).1
    exact Subsingleton.elim _ _
  rw [hσ, map_one, mul_one]
  exact conjAut_mem_inner_of_isSquare (FiniteField.isSquare_of_char_two (ringChar.eq K 2) _)

end Aut

section Model

theorem exists_equiv_projSp {Y : Type} [Group Y] {n f : ℕ}
    (h : StatedClassicalModel Y .PSp n 2 f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ f ∧
      Nonempty (Y ≃* StatedProj (StatedSp n K)) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, ⟨e⟩⟩

theorem outPTwoGen_psp {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : StatedClassicalModel Y .PSp n 2 f) {p : ℕ} (hp : p.Prime) : OutPTwoGen Y p := by
  have hn : 2 ≤ n := h.1.2.2.1
  rcases Nat.eq_or_lt_of_le hn with rfl | hn3
  · exact OutPTwoGen.of_outPNice (outPNice_PSp_two hp h)
  · exact OutPTwoGen.of_outPNice (outPNice_PSp_ge_three hp hn3 h)

theorem outPInner_psp_two {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (h : StatedClassicalModel Y .PSp n 2 1) {p : ℕ} : OutPInner Y p := by
  have hn : 2 ≤ n := h.1.2.2.1
  have hn2 : n ≠ 2 := fun h2 => h.1.2.2.2 (by simp [h2])
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_equiv_projSp h
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 :=
    charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card]; exact hK)
  exact OutPInner.of_mulEquiv e.symm (outPInner_projSp_two (by simpa using hK) (by omega))

theorem autScalarTorus_psp {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : StatedClassicalModel Y .PSp n 2 f) : AutScalarTorus Y := by
  have hn : 2 ≤ n := h.1.2.2.1
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_equiv_projSp h
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hK)
  exact AutScalarTorus.of_mulEquiv e.symm (autScalarTorus_projSp hn)

end Model

end CFSG.AGLEmbedding.ParabAutIrr
