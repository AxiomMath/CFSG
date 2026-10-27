module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15P812Glue
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15P812MatB

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.P812

open CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.SubgroupLists
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] {A : Subgroup G}
variable {f : Multiplicative (Fin 3 → ZMod 3) ≃* A} {a : Fin 3 → G}

theorem psi_eq_xiK (hf : IsAdapted f a) {k : Fin 3} (hk : k ≠ 0) {t : G}
    (ht : t ∈ Subgroup.normalizer (A : Set G))
    (h : t * a 0 * t⁻¹ = a 0 * a k ∧ t * a 1 * t⁻¹ = a 1 ∧ t * a 2 * t⁻¹ = a 2) :
    psi f ⟨t, ht⟩ = xiK k hk := by
  have e0 : ((psi f ⟨t, ht⟩ : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ ev 0 =
      ((xiK k hk : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ ev 0 := by
    rw [xiK_mulVec]
    refine psi_mulVec_ev f ⟨t, ht⟩ 0 _ ?_
    rw [adapted_ev hf]
    have : ((f (Multiplicative.ofAdd (ev 0 + ev 0 0 • ev k)) : A) : G) = a 0 * a k := by
      simp only [ofAdd_add, map_mul, Subgroup.coe_mul]
      rw [adapted_ev hf, show ev 0 0 • ev k = (1 : ZMod 3) • ev k by simp [ev], one_smul,
        adapted_ev hf]
    rw [this]
    exact h.1
  have e1 : ((psi f ⟨t, ht⟩ : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ ev 1 =
      ((xiK k hk : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ ev 1 := by
    rw [xiK_mulVec]
    have h0 : ev 1 0 = 0 := by simp [ev]
    rw [h0, zero_smul, add_zero]
    exact psi_mulVec_ev f ⟨t, ht⟩ 1 (ev 1) (by rw [adapted_ev hf]; exact h.2.1)
  have e2 : ((psi f ⟨t, ht⟩ : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ ev 2 =
      ((xiK k hk : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ ev 2 := by
    rw [xiK_mulVec]
    have h0 : ev 2 0 = 0 := by simp [ev]
    rw [h0, zero_smul, add_zero]
    exact psi_mulVec_ev f ⟨t, ht⟩ 2 (ev 2) (by rw [adapted_ev hf]; exact h.2.2)
  apply gl_eq_of_mulVec_ev
  intro j
  fin_cases j
  · exact e0
  · exact e1
  · exact e2

theorem caseII_normalizer_le_of_fixes [Finite G]
    {M A : Subgroup G} {a : Fin 3 → G} {t₁ t₂ x : G} {k : Fin 3} (hk : k ≠ 0)
    (hk12 : k = 1 ∨ k = 2)
    (hAel : CFSG.Open.IsElemAbelian 3 A) (h27 : Nat.card A = 27)
    (haA : ∀ i, a i ∈ A) (hgen : Subgroup.closure {a 0, a 1, a 2} = A)
    (ht₁ : t₁ ∈ Subgroup.normalizer (A : Set G)) (ht₂ : t₂ ∈ Subgroup.normalizer (A : Set G))
    (hx : x ∈ Subgroup.normalizer (A : Set G))
    (h₁ : t₁ * a 0 * t₁⁻¹ = a 0 ∧ t₁ * a 1 * t₁⁻¹ = (a 1)⁻¹ ∧ t₁ * a 2 * t₁⁻¹ = a 2)
    (h₂ : t₂ * a 0 * t₂⁻¹ = a 0 ∧ t₂ * a 1 * t₂⁻¹ = a 1 ∧ t₂ * a 2 * t₂⁻¹ = (a 2)⁻¹)
    (hxk : x * a 0 * x⁻¹ = a 0 * a k ∧ x * a 1 * x⁻¹ = a 1 ∧ x * a 2 * x⁻¹ = a 2)
    (hN1 : Subgroup.normalizer (Subgroup.zpowers (a 1) : Set G) ≤ M)
    (hN2 : Subgroup.normalizer (Subgroup.zpowers (a 2) : Set G) ≤ M)
    (hN12 : Subgroup.normalizer
      ((Subgroup.zpowers (a 1) ⊔ Subgroup.zpowers (a 2) : Subgroup G) : Set G) ≤ M)
    (hNM : ∀ g ∈ Subgroup.normalizer (A : Set G), g ∈ M → ∀ j : Fin 3, (j = 1 ∨ j = 2) →
      g * a j * g⁻¹ = a j →
      g ∈ Subgroup.normalizer (Subgroup.zpowers (a 1) : Set G) ∧
        g ∈ Subgroup.normalizer (Subgroup.zpowers (a 2) : Set G)) :
    Subgroup.normalizer (A : Set G) ≤ M := by
  classical
  by_contra hW
  have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAel.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  obtain ⟨f, -, -, -, hfv⟩ :=
    Sec11.exists_coords_triple hcomm hAel.2 h27 (haA 0) (haA 1) (haA 2) hgen
  have hf : IsAdapted f a := hfv
  have ha3 : ∀ i, a i ^ 3 = 1 := fun i => hAel.2 _ (haA i)
  have hdA : dA ∈ (psi f).range := ⟨⟨t₁, ht₁⟩, psi_eq_dA hf ht₁ h₁⟩
  have hdB : dB ∈ (psi f).range := ⟨⟨t₂, ht₂⟩, psi_eq_dB hf ht₂ h₂⟩
  have hxi : xiK k hk ∈ (psi f).range := ⟨⟨x, hx⟩, psi_eq_xiK hf hk hx hxk⟩
  obtain ⟨w, hwN, hwM⟩ := SetLike.not_le_iff_exists.mp hW
  have hline : ∀ i, Subgroup.normalizer (Subgroup.zpowers (a i) : Set G) ≤ M →
      ∀ g : Subgroup.normalizer (A : Set G), (g : G) ∉ M →
        ¬ (∀ v ∈ cline i,
          ((psi f g : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v ∈ cline i) := by
    intro i hi g hg hpres
    apply hg
    apply hi
    rw [← coordSub_cline hf ha3 i]
    exact (mem_normalizer_coordSub_iff f (cline i) g).mpr hpres
  refine caseB_matrix (psi f).range k hk hk12 hdA hdB hxi ⟨psi f ⟨w, hwN⟩, ⟨⟨w, hwN⟩, rfl⟩, ?_, ?_, ?_⟩ ?_
  · exact hline 1 hN1 ⟨w, hwN⟩ hwM
  · exact hline 2 hN2 ⟨w, hwN⟩ hwM
  · intro hpres
    apply hwM
    apply hN12
    rw [← coordSub_cplane_sup hf ha3 (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide)
      (by decide)]
    exact (mem_normalizer_coordSub_iff f (cplane 0) ⟨w, hwN⟩).mpr hpres
  ·
    rintro _ ⟨n, rfl⟩ j hj hfix
    have hnj : (n : G) * a j * (n : G)⁻¹ = a j := by
      have h1 := psi_conj f n (ev j)
      rw [hfix, adapted_ev hf] at h1
      exact h1.symm
    have hnM : (n : G) ∈ M := by
      have hcent : (n : G) ∈ Subgroup.centralizer (Subgroup.zpowers (a j) : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        obtain ⟨m, rfl⟩ := hy
        have hc : (n : G) * a j = a j * (n : G) := by
          calc (n : G) * a j = (n : G) * a j * (n : G)⁻¹ * (n : G) := by group
            _ = a j * (n : G) := by rw [hnj]
        exact (Commute.zpow_left (show Commute (a j) (n : G) from hc.symm) m).eq
      have hnN := Subgroup.centralizer_le_normalizer _ hcent
      rcases hj with rfl | rfl
      · exact hN1 hnN
      · exact hN2 hnN
    obtain ⟨hn1, hn2⟩ := hNM n n.2 hnM j hj hnj
    constructor
    · rw [← coordSub_cline hf ha3 1] at hn1
      exact (mem_normalizer_coordSub_iff f (cline 1) n).mp hn1
    · rw [← coordSub_cline hf ha3 2] at hn2
      exact (mem_normalizer_coordSub_iff f (cline 2) n).mp hn2

theorem caseII_normalizer_le [Finite G]
    {M A : Subgroup G} {a : Fin 3 → G} {t₁ t₂ x : G} {k : Fin 3} (hk : k ≠ 0)
    (hk12 : k = 1 ∨ k = 2)
    (hAel : CFSG.Open.IsElemAbelian 3 A) (h27 : Nat.card A = 27)
    (haA : ∀ i, a i ∈ A) (hgen : Subgroup.closure {a 0, a 1, a 2} = A)
    (ht₁ : t₁ ∈ Subgroup.normalizer (A : Set G)) (ht₂ : t₂ ∈ Subgroup.normalizer (A : Set G))
    (hx : x ∈ Subgroup.normalizer (A : Set G))
    (h₁ : t₁ * a 0 * t₁⁻¹ = a 0 ∧ t₁ * a 1 * t₁⁻¹ = (a 1)⁻¹ ∧ t₁ * a 2 * t₁⁻¹ = a 2)
    (h₂ : t₂ * a 0 * t₂⁻¹ = a 0 ∧ t₂ * a 1 * t₂⁻¹ = a 1 ∧ t₂ * a 2 * t₂⁻¹ = (a 2)⁻¹)
    (hxk : x * a 0 * x⁻¹ = a 0 * a k ∧ x * a 1 * x⁻¹ = a 1 ∧ x * a 2 * x⁻¹ = a 2)
    (hN1 : Subgroup.normalizer (Subgroup.zpowers (a 1) : Set G) ≤ M)
    (hN2 : Subgroup.normalizer (Subgroup.zpowers (a 2) : Set G) ≤ M)
    (hN12 : Subgroup.normalizer
      ((Subgroup.zpowers (a 1) ⊔ Subgroup.zpowers (a 2) : Subgroup G) : Set G) ≤ M)
    (hNM : ∀ g ∈ Subgroup.normalizer (A : Set G), g ∈ M →
      g ∈ Subgroup.normalizer (Subgroup.zpowers (a 1) : Set G) ∧
        g ∈ Subgroup.normalizer (Subgroup.zpowers (a 2) : Set G)) :
    Subgroup.normalizer (A : Set G) ≤ M :=
  caseII_normalizer_le_of_fixes hk hk12 hAel h27 haA hgen ht₁ ht₂ hx h₁ h₂ hxk hN1 hN2 hN12
    fun g hg hgM _ _ _ => hNM g hg hgM

end CFSG.LocalAnalysis.RankThreeUC.S15.P812
