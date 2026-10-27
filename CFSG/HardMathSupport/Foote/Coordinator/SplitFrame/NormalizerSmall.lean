module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.FrameCentralizer
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Frames
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.OuterSL

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE8F

set_option linter.unusedSectionVars false


variable {τ : Tag} {K : Type} [Field K]

theorem mem_torusGroup_of_mem_centralizer_rootSpan_fam {S : Set (Fin τ.rank → ℤ)}
    (F : Set (Fin τ.rank → Kˣ)) (hF : ∀ a ∈ F, rootDiagUnit τ a ∈ rootSpan τ K S)
    (hker : ∀ α, IsRoot τ α → ∃ a ∈ F, rootChar a α ≠ 1)
    (R : Set (Fin τ.rank → ℤ)) (hRS : R ⊆ S) (hRpos : ∀ α ∈ R, IsRoot τ α ∧ 0 < height α)
    (hRw : ∀ w : WeylGroup τ, (∀ α ∈ R, w • α = α) → w = 1)
    {g : ModGL τ K} (hg : g ∈ adjointGroup τ K)
    (hc : g ∈ Subgroup.centralizer (rootSpan τ K S : Set (ModGL τ K))) :
    g ∈ torusGroup τ K := by
  classical
  have hcomm : ∀ a ∈ F, rootDiagUnit τ a * g * (rootDiagUnit τ a)⁻¹ = g := by
    intro a ha
    have h := Subgroup.mem_centralizer_iff.1 hc _ (hF a ha)
    rw [h]
    group
  obtain ⟨w, -, h, hh, u, hu, v, hv, hgeq⟩ := fam_factor F hg hcomm
  have hker0 : famKernel F = ∅ := by
    ext α
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨hα, hall⟩
    obtain ⟨a, ha, hne⟩ := hker α hα
    exact hne (hall a ha)
  have hbot : ∀ T : Set (Fin τ.rank → ℤ), rootSpan τ K (∅ ∩ T) = ⊥ := by
    intro T
    rw [Set.empty_inter]
    exact le_bot_iff.1 (iSup₂_le fun α hα => absurd hα (Set.notMem_empty α))
  rw [hker0, hbot, Subgroup.mem_bot] at hu hv
  subst hu hv
  have hgw : g = h * canonicalRep (coxeterSystem τ) K w := by
    rw [hgeq, mul_one, mul_one]
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  have hwR : ∀ α ∈ R, w • α = α := by
    intro α hα
    obtain ⟨hαr, hαp⟩ := hRpos α hα
    obtain ⟨ε, hε, hconj⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K w hαr
    have hcα : g * pinnedX τ K α 1 * g⁻¹ = pinnedX τ K α 1 := by
      have := Subgroup.mem_centralizer_iff.1 hc (pinnedX τ K α 1) (pinnedX_mem_rootSpan (hRS hα) 1)
      rw [← this]
      group
    have e1 : g * pinnedX τ K α 1 * g⁻¹ =
        pinnedX τ K (w • α) ((rootChar b (w • α) : K) * (ε * 1)) := by
      rw [hgw, ← rootDiagUnit_conj_pinnedX b (CFSG.LieType.Chevalley.IsRoot.smul hαr w), ← hconj]
      group
    have hne : ((rootChar b (w • α) : K) * (ε * 1)) ≠ 0 := by
      refine mul_ne_zero (Units.ne_zero _) ?_
      rw [mul_one]
      intro h0
      rw [h0, mul_zero] at hε
      exact zero_ne_one hε
    exact eq_of_pinnedX_eq_pinnedX (CFSG.LieType.Chevalley.IsRoot.smul hαr w) ⟨hαr, hαp⟩ hne
      (e1.symm.trans hcα)
  have hw1 : w = 1 := hRw w hwR
  rw [hgw, hw1, canonicalRep_one, mul_one]
  exact hh

theorem commute_of_mem_centralizer_cosetRoots_fam {i₀ : Fin τ.rank} {n : ℕ}
    {θ : Fin τ.rank → ℤ} (hθ : IsRoot τ θ)
    (hθp : 0 < height θ) (hθn : (n : ℤ) ∣ θ i₀) (hθ0 : θ i₀ ≠ 0)
    (F : Set (Fin τ.rank → Kˣ))
    (hF : ∀ a ∈ F, rootDiagUnit τ a ∈ rootSpan τ K (cosetRoots τ i₀ n))
    (hker : ∀ α, IsRoot τ α → ∃ a ∈ F, rootChar a α ≠ 1)
    {c d : ModGL τ K}
    (hc : c ∈ Subgroup.centralizer (rootSpan τ K (cosetRoots τ i₀ n) : Set (ModGL τ K)) ⊓
      adjointGroup τ K)
    (hd : d ∈ Subgroup.centralizer (rootSpan τ K (cosetRoots τ i₀ n) : Set (ModGL τ K)) ⊓
      adjointGroup τ K) :
    Commute c d := by
  classical
  have hsingle : ∀ k, k ≠ i₀ → (Pi.single k 1 : Fin τ.rank → ℤ) i₀ = 0 := fun k hk => by
    simp [Ne.symm hk]
  have hJ : ∀ k, k ≠ i₀ →
      (Pi.single k 1 : Fin τ.rank → ℤ) ∈ cosetRoots τ i₀ n := by
    intro k hk
    refine ⟨IsRoot.basis k, ?_⟩
    rw [hsingle k hk]
    exact dvd_zero _
  set R : Set (Fin τ.rank → ℤ) := {α | (∃ k, k ≠ i₀ ∧ α = Pi.single k 1) ∨ α = θ} with hR
  have hRS : R ⊆ cosetRoots τ i₀ n := by
    rintro α (⟨k, hk, rfl⟩ | rfl)
    · exact hJ k hk
    · exact ⟨hθ, hθn⟩
  have hRpos : ∀ α ∈ R, IsRoot τ α ∧ 0 < height α := by
    rintro α (⟨k, hk, rfl⟩ | rfl)
    · refine ⟨IsRoot.basis k, ?_⟩
      simp [height, Finset.sum_pi_single']
    · exact ⟨hθ, hθp⟩
  have hRw : ∀ w : WeylGroup τ, (∀ α ∈ R, w • α = α) → w = 1 := by
    intro w hw
    exact eq_one_of_smul_single_of_smul (i₀ := i₀) (fun k hk => hw _ (Or.inl ⟨k, hk, rfl⟩))
      (hw θ (Or.inr rfl)) hθ0
  have hT : ∀ {g : ModGL τ K},
      g ∈ Subgroup.centralizer (rootSpan τ K (cosetRoots τ i₀ n) : Set (ModGL τ K)) ⊓
        adjointGroup τ K → g ∈ torusGroup τ K := fun {g} hg =>
    mem_torusGroup_of_mem_centralizer_rootSpan_fam F hF hker R hRS hRpos hRw hg.2 hg.1
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hT hc)
  rw [ha]
  exact rootDiagUnit_mul_comm_of_mem_torusGroup a (hT hd)

theorem neg_one_zpow_ne_one {m : ℤ} (hm : Odd m) (h2 : (2 : K) ≠ 0) :
    ((-1 : Kˣ) ^ m) ≠ 1 := by
  rw [hm.neg_one_zpow]
  intro h
  have := congrArg (fun u : Kˣ => (u : K)) h
  simp only [Units.val_neg, Units.val_one] at this
  apply h2
  linear_combination (-1 : K) * this

theorem cartan_odd_pairing_E8 : ∀ α ∈ rootFinset .E8, ∃ k : Fin Tag.E8.rank,
    k ≠ ⟨4, by decide⟩ ∧ (∑ j, Tag.E8.cartan k j * α j) % 2 = 1 := by
  decide +kernel

theorem two_ne_zero_of_card_three (K : Type) [Field K] [Finite K] (hK : Nat.card K = 3) :
    (2 : K) ≠ 0 := by
  intro h
  have h1 : addOrderOf (1 : K) ∣ 2 := addOrderOf_dvd_of_nsmul_eq_zero (by simpa using h)
  have h3 : addOrderOf (1 : K) ∣ 3 := hK ▸ addOrderOf_dvd_natCard _
  have h4 : addOrderOf (1 : K) ∣ 1 := by
    have := Nat.dvd_gcd h1 h3
    simp at this
  exact one_ne_zero (AddMonoid.addOrderOf_eq_one_iff.1 (Nat.dvd_one.1 h4))

@[expose] def thetaE8 : Fin (Tag.rank .E8) → ℤ := ![2, 3, 4, 6, 5, 4, 3, 2]

theorem thetaE8_mem : thetaE8 ∈ rootFinset .E8 := by decide +kernel

@[expose] def negOneTuple (τ : Tag) (K : Type) [Field K] (k : Fin τ.rank) : Fin τ.rank → Kˣ :=
  fun j => (-1 : Kˣ) ^ τ.cartan k j

theorem frameNormalizerSolvable_E8_three
    (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 3) : FrameNormalizerSolvable .E8 K (cosetRoots .E8 4 5) := by
  have h2 := two_ne_zero_of_card_three K hK
  intro P hPG hPN hPX
  obtain ⟨ψA, ψB, hA, hB, hcomm, hrange⟩ := exists_splitFrame_E8 K
  rw [← hrange] at hPN hPX
  refine isSolvable_of_le_normalizer_frame (isQuasisimple_SL (by norm_num))
    (isSolvable_out_SL (by norm_num)) hA hB hcomm (Gh := adjointGroup .E8 K)
    (hrange ▸ rootSpan_le_adjointGroup K _) (fun c hc d hd => ?_) hPG hPN hPX
  rw [hrange] at hc hd
  have hsingle : ∀ k : Fin Tag.E8.rank, k ≠ ⟨4, by decide⟩ →
      (Pi.single k 1 : Fin Tag.E8.rank → ℤ) ⟨4, by decide⟩ = 0 := fun k hk => by
    simp [Ne.symm hk]
  refine commute_of_mem_centralizer_cosetRoots_fam (mem_rootFinset.1 thetaE8_mem)
    (by decide) (by decide) (by decide)
    {a | ∃ k : Fin Tag.E8.rank, k ≠ ⟨4, by decide⟩ ∧ a = negOneTuple .E8 K k} ?_ ?_ hc hd
  · rintro a ⟨k, hk, rfl⟩
    have h1 : (Pi.single k 1 : Fin Tag.E8.rank → ℤ) ∈ cosetRoots .E8 4 5 :=
      ⟨IsRoot.basis k, by rw [show (4 : Fin Tag.E8.rank) = ⟨4, by decide⟩ from rfl, hsingle k hk]
                          exact dvd_zero _⟩
    have h2' : (-Pi.single k 1 : Fin Tag.E8.rank → ℤ) ∈ cosetRoots .E8 4 5 :=
      ⟨isRoot_neg_single _ k, by
        rw [show (4 : Fin Tag.E8.rank) = ⟨4, by decide⟩ from rfl, Pi.neg_apply, hsingle k hk,
          neg_zero]
        exact dvd_zero _⟩
    unfold negOneTuple
    rw [← torusElt_eq_rootDiagUnit (i := k) (u := (-1 : Kˣ))]
    exact torusElt_mem_rootSpan h1 h2' (-1)
  · intro α hα
    obtain ⟨k, hk, hodd⟩ := cartan_odd_pairing_E8 α (mem_rootFinset.2 hα)
    refine ⟨negOneTuple .E8 K k, ⟨k, hk, rfl⟩, ?_⟩
    have := rootChar_cartan_zpow (K := K) (τ := .E8) (-1 : Kˣ) k α
    unfold negOneTuple
    rw [this]
    exact neg_one_zpow_ne_one (Int.odd_iff.2 hodd) h2

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
