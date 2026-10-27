module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma82
public import CFSG.LocalAnalysis.GLTheoremB.CentralizerLift
public import CFSG.LocalAnalysis.GLTheoremB.PCompBasics
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7ToolsB

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6C

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.UniquenessMaximal

variable {G : Type} [Group G] [Finite G]

theorem commutator_mem_glaPPrimeCoreOf_of_ne {X I K : Subgroup G}
    (hI : GLAPComponent 3 X I) (hK : GLAPComponent 3 X K) (hne : I ≠ K) {i k : G} (hi : i ∈ I)
    (hk : k ∈ K) : i * k * i⁻¹ * k⁻¹ ∈ GLAPPrimeCoreOf 3 X := by
  have hbar : barX 3 X I ≠ barX 3 X K := fun h => hne (glaPComponent_unique hI hK h)
  have hcomm : ⁅barX 3 X I, barX 3 X K⁆ = ⊥ :=
    CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hI.2.2.1 hK.2.2.1 hbar
  have hiX : i ∈ X := hI.1 hi
  have hkX : k ∈ X := hK.1 hk
  have hmI : (QuotientGroup.mk (⟨i, hiX⟩ : ↥X) : ↥X ⧸ GLAPPrimeCore 3 ↥X) ∈ barX 3 X I :=
    ⟨⟨i, hiX⟩, (Subgroup.mem_subgroupOf).2 hi, rfl⟩
  have hmK : (QuotientGroup.mk (⟨k, hkX⟩ : ↥X) : ↥X ⧸ GLAPPrimeCore 3 ↥X) ∈ barX 3 X K :=
    ⟨⟨k, hkX⟩, (Subgroup.mem_subgroupOf).2 hk, rfl⟩
  have h1 := Subgroup.commutator_mem_commutator hmI hmK
  rw [hcomm, Subgroup.mem_bot] at h1
  have h2 : (QuotientGroup.mk (⟨i, hiX⟩ * ⟨k, hkX⟩ * ⟨i, hiX⟩⁻¹ * ⟨k, hkX⟩⁻¹ : ↥X) :
      ↥X ⧸ GLAPPrimeCore 3 ↥X) = 1 := by
    rw [← h1, commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv]
  rw [QuotientGroup.eq_one_iff] at h2
  exact ⟨_, h2, by simp⟩

theorem nine_dvd_card_inf_centralizer {I A : Subgroup G} (hI : IsLThreeFour (↥I ⧸ GLAPPrimeCore 3 ↥I))
    (hA : IsPGroup 3 A) (hAI : A ≤ Subgroup.normalizer (I : Set G))
    (hAc : ∀ a ∈ A, ∀ g ∈ I, a * g * a⁻¹ * g⁻¹ ∈ GLAPPrimeCoreOf 3 I) :
    9 ∣ Nat.card (I ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  set H : Subgroup G := I ⊓ Subgroup.centralizer (A : Set G) with hH
  have hHI : H ≤ I := inf_le_left
  have htop : barX 3 I H = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨v, hv, hfix⟩ := exists_fixed_in_coset' (p := 3) (U := A)
      (V := GLAPPrimeCoreOf 3 I) hA (not_dvd_card_glaPPrimeCoreOf hp I)
      (le_normalizer_glaPPrimeCoreOf_of_le_normalizer hAI)
      (le_normalizer_glaPPrimeCoreOf 3 I g.2) (fun u hu => hAc u hu g g.2)
    have hvI : v ∈ I := (Subgroup.map_subtype_le _) hv
    have hmem : (g : G) * v ∈ H := by
      refine ⟨I.mul_mem g.2 hvI, ?_⟩
      show (g : G) * v ∈ Subgroup.centralizer (A : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have := hfix u hu
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this
    refine ⟨⟨(g : G) * v, I.mul_mem g.2 hvI⟩, (Subgroup.mem_subgroupOf).2 hmem, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq]
    obtain ⟨v', hv', hv'e⟩ := hv
    have hv'e' : (v' : G) = v := hv'e
    have : (⟨(g : G) * v, I.mul_mem g.2 hvI⟩ : ↥I)⁻¹ * g = v'⁻¹ := by
      apply Subtype.ext
      simp [hv'e']
    rw [this]
    exact inv_mem hv'
  have hcard : Nat.card (barX 3 I H) = 20160 := by
    rw [htop, Subgroup.card_top]
    exact card_eq_of_isLThreeFour hI
  have hdvd : Nat.card (barX 3 I H) ∣ Nat.card H := by
    have h1 : Nat.card (barX 3 I H) ∣ Nat.card (H.subgroupOf I) :=
      Subgroup.card_map_dvd _ _
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHI).toEquiv] at h1
  rw [hcard] at hdvd
  exact (by norm_num : 9 ∣ 20160).trans hdvd

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6C
