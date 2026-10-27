module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusUnitaryBasic
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherBorelOvergroups
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSylow

public section

namespace CFSG.AGLEmbedding

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.LinearGroups CFSG.Assembly.LowTwoRank
  Matrix
open scoped Pointwise

namespace ToralCensus

variable {K : Type} [Field K]

theorem conj_mem_normalizer_conj_smul {G : Type*} [Group G] {H : Subgroup G} {b : G}
    (hb : b ∈ Subgroup.normalizer (H : Set G)) (g : G) :
    g * b * g⁻¹ ∈ Subgroup.normalizer ((MulAut.conj g • H : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [MulAut.smul_def, MulAut.conj_inv_apply]
  rw [Subgroup.mem_normalizer_iff.mp hb (g⁻¹ * x * g)]
  constructor <;> intro hx <;> convert hx using 1 <;> group

theorem exists_eq_stab_hypFlag_of_normalizer_le {p f r ε : ℕ} (h : UnitaryFieldData p f K)
    (hr : 1 ≤ r) (hε : ε ≤ 1) (T : Sylow p (hypSU h r ε)) (J : Subgroup (hypSU h r ε))
    (hTJ : Subgroup.normalizer ((T : Subgroup (hypSU h r ε)) : Set (hypSU h r ε)) ≤ J) :
    ∃ (g : hypSU h r ε) (I : Set ℕ), I ⊆ Set.Icc 1 r ∧
      ∀ y : hypSU h r ε, y ∈ J ↔ ∀ i ∈ I, y • (g • hypFlag h r ε i) = g • hypFlag h r ε i := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : Finite K := h.finite
  obtain ⟨U', hU'⟩ := (unitary_order_and_Sylow h hr hε).2.1
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (hypSU h r ε) U' T
  obtain ⟨c, hc, hc0⟩ := exists_mem_traceZero_ne_zero' h
  set A : Subgroup (hypSU h r ε) := J.comap (MulAut.conj g).toMonoidHom with hAdef
  have hmemA : ∀ x, x ∈ A ↔ g * x * g⁻¹ ∈ J := fun x => Iff.rfl
  have hBA : hypBorel h r ε ≤ A := by
    intro b hb
    rw [hmemA]
    apply hTJ
    rw [← hg, Sylow.coe_subgroup_smul, hU']
    exact conj_mem_normalizer_conj_smul (by rw [normalizer_hypUnitriangular h hr hε]; exact hb) g
  have hA := eq_flagStabilizer_overgroupCuts h hr hε hc hc0 A hBA
  have hIsub := overgroupCuts_subset h hc A
  generalize overgroupCuts ε h c hc A = I at hA hIsub
  refine ⟨g, I, hIsub, fun y => ?_⟩
  have key : y ∈ J ↔ g⁻¹ * y * g ∈ A := by
    rw [hmemA, show g * (g⁻¹ * y * g) * g⁻¹ = y by group]
  rw [key, hA, mem_flagStabilizer]
  refine forall₂_congr fun i _ => ?_
  rw [mul_smul, mul_smul, inv_smul_eq_iff]

theorem smul_eq_iff_mulVec_mem {n : ℕ} (g : GL (Fin n) K) (W : Submodule K (Fin n → K)) :
    g • W = W ↔ ∀ w ∈ W, (g : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W := by
  constructor
  · intro hg w hw
    rw [← hg]
    exact (Submodule.mem_smul_pointwise_iff_exists _ g W).mpr ⟨w, hw, rfl⟩
  · intro hw
    have hle : g • W ≤ W := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists x g W).mp hx
      exact hw y hy
    exact Submodule.eq_of_le_of_finrank_eq hle
      (LinearEquiv.finrank_map_eq (DistribMulAction.toLinearEquiv K _ g) W)

theorem eq_one_of_le_one {f n : ℕ} (h : UnitaryFieldData 2 f K) (hn : n ≤ 1)
    (y : StatedSU n (2 ^ f) K) : y = 1 := by
  have hdet := ((mem_unitarySU_iff h).mp y.2).1
  apply Subtype.ext
  apply Units.ext
  ext i j
  obtain rfl : n = 1 := by have := i.2; omega
  obtain rfl : i = 0 := Subsingleton.elim i 0
  obtain rfl : j = 0 := Subsingleton.elim j 0
  rw [Matrix.det_unique] at hdet
  simpa using hdet

end ToralCensus

theorem flagLinkSU :
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (n q : ℕ), Nat.card K = q ^ 2 →
      ∀ (J : Subgroup (StatedSU n q K)) (S₀ : Sylow 2 (StatedSU n q K)),
        Subgroup.normalizer ((S₀ : Subgroup (StatedSU n q K)) : Set (StatedSU n q K)) ≤ J →
        J ≠ ⊤ →
        ∃ 𝒲 : Set (Submodule K (Fin n → K)), 𝒲.Nonempty ∧
          (∀ W ∈ 𝒲, W ≠ ⊥ ∧ IsTotallyIsotropicSU q W) ∧
          ∀ y : StatedSU n q K, y ∈ J ↔ ∀ W ∈ 𝒲, ∀ w ∈ W,
            ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W := by
  intro K _ _ _ n q hK J S₀ hNJ hJ
  obtain ⟨f, hf, rfl⟩ := ToralCensus.exists_eq_two_pow_of_card_eq_sq hK
  have h := ToralCensus.unitaryFieldData_of_card_eq_sq hK hf
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn2 : 2 ≤ n := by
    by_contra hn
    refine hJ (eq_top_iff.mpr fun y _ => ?_)
    rw [ToralCensus.eq_one_of_le_one h (by omega) y]
    exact J.one_mem
  obtain ⟨r, ε, hr, hε, rfl⟩ : ∃ r ε, 1 ≤ r ∧ ε ≤ 1 ∧ n = 2 * r + ε :=
    ⟨n / 2, n % 2, by omega, by omega, by omega⟩
  obtain ⟨R, hR⟩ := exists_isHypTransport h (r := r) (ε := ε)
  set φ : hypSU h r ε ≃* StatedSU (2 * r + ε) (2 ^ f) K := hypTransport h hR with hφ
  set J' : Subgroup (hypSU h r ε) := J.comap φ.toMonoidHom with hJ'
  have hmemJ' : ∀ x, x ∈ J' ↔ φ x ∈ J := fun x => Iff.rfl
  let T : Sylow 2 (hypSU h r ε) :=
    Sylow.mapSurjective (f := φ.symm.toMonoidHom) φ.symm.surjective S₀
  have hTc : (T : Subgroup (hypSU h r ε)) = (S₀ : Subgroup _).map φ.symm.toMonoidHom := rfl
  have hTJ : Subgroup.normalizer ((T : Subgroup (hypSU h r ε)) : Set (hypSU h r ε)) ≤ J' := by
    intro x hx
    rw [hTc, ← Subgroup.map_equiv_normalizer_eq] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [hmemJ']
    simpa using hNJ hy
  obtain ⟨g, I, hI, hJI⟩ := ToralCensus.exists_eq_stab_hypFlag_of_normalizer_le h hr hε T J' hTJ
  have hchain := isIsotropicChain_hypFlag h (r := r) hε
  refine ⟨(fun i => transportSubspace h hR (g • hypFlag h r ε i)) '' I, ?_, ?_, fun y => ?_⟩
  · by_contra hne
    rw [Set.image_nonempty, Set.not_nonempty_iff_eq_empty] at hne
    refine hJ (eq_top_iff.mpr fun y _ => ?_)
    have hy : φ.symm y ∈ J' := (hJI _).mpr fun i hi => by rw [hne] at hi; exact absurd hi id
    rwa [hmemJ', MulEquiv.apply_symm_apply] at hy
  · rintro _ ⟨i, hi, rfl⟩
    obtain ⟨hi1, hir⟩ := hI hi
    dsimp only
    refine ⟨fun hbot => ?_, ?_⟩
    · have hdim := finrank_transportSubspace hR (g • hypFlag h r ε i)
      rw [hbot, finrank_bot, finrank_smul, hchain.1 i hir] at hdim
      omega
    · rw [ToralCensus.isTotallyIsotropicSU_iff h]
      exact (isTotallyIsotropic_transportSubspace hR _).mp
        (smul_isotropic g (hchain.2.2 i hir))
  · have hy : y ∈ J ↔ φ.symm y ∈ J' := by rw [hmemJ', MulEquiv.apply_symm_apply]
    rw [hy, hJI, Set.forall_mem_image]
    refine forall₂_congr fun i _ => ?_
    rw [← ToralCensus.smul_eq_iff_mulVec_mem, ← Subgroup.smul_def]
    have e := transportSubspace_smul hR (φ.symm y) (g • hypFlag h r ε i)
    rw [← hφ, MulEquiv.apply_symm_apply] at e
    rw [← e, (transportSubspace h hR).injective.eq_iff]

theorem exists_isTotallyIsotropicSU_of_normalizer_le {K : Type} [Field K] [Finite K]
    [CharP K 2] {n q : ℕ} (hK : Nat.card K = q ^ 2) {J : Subgroup (StatedSU n q K)}
    {S₀ : Sylow 2 (StatedSU n q K)}
    (hNJ : Subgroup.normalizer ((S₀ : Subgroup (StatedSU n q K)) : Set (StatedSU n q K)) ≤ J)
    (hJ : J ≠ ⊤) :
    ∃ W : Submodule K (Fin n → K), W ≠ ⊥ ∧ IsTotallyIsotropicSU q W ∧
      ∀ y ∈ J, ∀ w ∈ W, ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W := by
  obtain ⟨𝒲, ⟨W, hW⟩, h𝒲, hJ𝒲⟩ := flagLinkSU K n q hK J S₀ hNJ hJ
  exact ⟨W, (h𝒲 W hW).1, (h𝒲 W hW).2, fun y hy => (hJ𝒲 y).mp hy W hW⟩

end CFSG.AGLEmbedding
