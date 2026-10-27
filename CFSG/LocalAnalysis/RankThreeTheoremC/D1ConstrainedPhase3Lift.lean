module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConstrainedPhase3Basic
public import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoBalance

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding (D1Extremal D1Escape D1PhaseThree glbPrimeCore_le glbPrimeCore_normal
  glbPrimeCore_coprime le_normalizer_glbPrimeCore pCoreOf_le_glbPrimeCore)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}

omit [Finite G] in
theorem le_of_glbIsMaxTwoLocal_of_le_sup {H A V₁ : Subgroup G} (hH : GLBIsMaxTwoLocal H)
    (hA : pCoreOf 2 A ≠ ⊥) (hV : V₁ ≤ Subgroup.normalizer (A : Set G)) (hle : H ≤ A ⊔ V₁) :
    A ≤ H := by
  have hX : A ⊔ V₁ ≤ Subgroup.normalizer (pCoreOf 2 A : Set G) :=
    sup_le (localGroup_le_normalizer_pCoreOf 2 A)
      (hV.trans (normalizer_localGroup_le_normalizer_pCoreOf 2 A))
  have h2 : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 A : Set G)) :=
    ⟨pCoreOf 2 A, hA, CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 A, rfl⟩
  have heq := hH.2 _ h2 (hle.trans hX)
  exact (le_sup_left.trans hX).trans heq.le

omit [Finite G] in
theorem conj_mem_centralizer_of_mem_normalizer_zpowers {z v : G}
    (hv : v ∈ Subgroup.normalizer (Subgroup.zpowers z : Set G)) {y : G}
    (hy : y ∈ Subgroup.centralizer ({z} : Set G)) :
    v * y * v⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
  have h1 : v⁻¹ * z * v⁻¹⁻¹ ∈ Subgroup.zpowers z :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hv) z).mp (Subgroup.mem_zpowers z)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
  have hkz : v⁻¹ * z * v = z ^ k := by simpa using hk.symm
  have hcomm : y * (v⁻¹ * z * v) = (v⁻¹ * z * v) * y := by
    rw [hkz]
    exact ((Commute.zpow_right (hy : Commute y z) k).eq)
  calc v * y * v⁻¹ * z = v * (y * (v⁻¹ * z * v)) * v⁻¹ := by group
    _ = v * ((v⁻¹ * z * v) * y) * v⁻¹ := by rw [hcomm]
    _ = z * (v * y * v⁻¹) := by group

omit [Finite G] in
theorem normalizer_zpowers_le_normalizer_primeCore_centralizer (p : ℕ) {z v : G}
    (hv : v ∈ Subgroup.normalizer (Subgroup.zpowers z : Set G)) :
    v ∈ Subgroup.normalizer (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)) : Set G) := by
  have hC : (Subgroup.centralizer ({z} : Set G)).map (MulAut.conj v).toMonoidHom =
      Subgroup.centralizer ({z} : Set G) := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact conj_mem_centralizer_of_mem_normalizer_zpowers hv hy
    · intro x hx
      refine ⟨v⁻¹ * x * v⁻¹⁻¹, conj_mem_centralizer_of_mem_normalizer_zpowers
        (Subgroup.inv_mem _ hv) hx, ?_⟩
      show v * (v⁻¹ * x * v⁻¹⁻¹) * v⁻¹ = x
      group
  have key := glbPrimeCore_map_automorphism p (Subgroup.centralizer ({z} : Set G))
    (MulAut.conj v)
  rw [hC] at key
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr key

omit [Finite G] in
theorem le_of_glbIsMaxTwoLocal_of_decomp {H M N O V₁ : Subgroup G} (hH : GLBIsMaxTwoLocal H)
    (hM : GLBIsMaxTwoLocal M) (hNM : N ≤ M) (hOM : O ≤ M) (hQN : pCoreOf 2 M ≤ N)
    (hVN : V₁ ≤ Subgroup.normalizer (N : Set G)) (hVO : V₁ ≤ Subgroup.normalizer (O : Set G))
    (hdec : ∀ g ∈ H, ∃ n ∈ N, ∃ v ∈ V₁, g = n * v) : O ≤ H := by
  have hVA : V₁ ≤ Subgroup.normalizer ((N ⊔ O : Subgroup G) : Set G) :=
    fun v hv => Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hVN hv, hVO hv⟩
  have hAM : N ⊔ O ≤ M := sup_le hNM hOM
  have hQA : pCoreOf 2 M ≤ N ⊔ O := hQN.trans le_sup_left
  have hQcore : pCoreOf 2 M ≤ pCoreOf 2 (N ⊔ O) :=
    normal_pGroup_le_pCoreOf 2 _ _ hQA
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hQA).mpr
        (hAM.trans (localGroup_le_normalizer_pCoreOf 2 M)))
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M)
  have hne : pCoreOf 2 (N ⊔ O) ≠ ⊥ := fun hbot =>
    twoLocal_pCoreOf_ne_bot M hM.1 (le_bot_iff.mp (hbot ▸ hQcore))
  have hHle : H ≤ (N ⊔ O) ⊔ V₁ := fun g hg => by
    obtain ⟨n, hn, v, hv, rfl⟩ := hdec g hg
    exact Subgroup.mul_mem_sup (Subgroup.mem_sup_left hn) hv
  exact (le_sup_right (a := N)).trans (le_of_glbIsMaxTwoLocal_of_le_sup hH hne hVA hHle)

theorem _root_.CFSG.AGLEmbedding.D1PhaseThree.primeCore_centralizer_le
    (h : D1PhaseThree p P M H R) (hcon : HasPrimeConstraint (G := H) p) {z : G} (hzR : z ∈ R)
    (hzc : z ∈ Subgroup.centralizer (R : Set G)) (hzp : orderOf z = p)
    (hOM : GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)) ≤ M) :
    GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)) ≤ H := by
  have hp := h.prime
  have hp2 : p.Coprime 2 := (Nat.coprime_primes hp Nat.prime_two).mpr h.ne_two
  refine le_of_glbIsMaxTwoLocal_of_decomp (M := M) (V₁ := H ⊓ Subgroup.normalizer
    (Subgroup.zpowers z : Set G)) h.maxTwoLocal_H h.maxTwoLocal_M h.primeCore_le hOM
    ((h.twoCore_M_le h.twoCore_inf).trans (pCoreOf_le_glbPrimeCore Nat.prime_two hp2 H))
    (fun v hv => le_normalizer_glbPrimeCore p H hv.1)
    (fun v hv => normalizer_zpowers_le_normalizer_primeCore_centralizer p hv.2) ?_
  intro g hg
  obtain ⟨n, hn, v, hvH, hvN, rfl⟩ :=
    h.toD1Escape.exists_mul_normalizer_zpowers hcon hzR hzc hzp g hg
  exact ⟨n, hn, v, ⟨hvH, hvN⟩, rfl⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
