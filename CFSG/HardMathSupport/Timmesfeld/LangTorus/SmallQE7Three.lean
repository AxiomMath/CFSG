module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.GoodClass
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.GoodA2Two
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.SmallQCommute
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.SmallQRankOneTwo

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Lattice CFSG.LieType.SeitzGeneration CFSG.LieType.Steinberg.Adjoint
open scoped Matrix

set_option linter.unusedSectionVars false


section E7


variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

private abbrev M7 : Matrix (Fin Tag.E7.rank) (Fin Tag.E7.rank) ℤ := toMat Tag.E7.rank e7ThreeMat

private theorem e7_A2_data : ∀ i : Fin Tag.E7.rank, i.val ≤ 5 →
    iform (Pi.single i 1 : Fin Tag.E7.rank → ℤ) (M7 *ᵥ Pi.single i 1) = -1 ∧
    M7 *ᵥ (M7 *ᵥ (Pi.single i 1 : Fin Tag.E7.rank → ℤ)) =
      -(Pi.single i 1 + M7 *ᵥ Pi.single i 1) ∧
    M7 *ᵥ (M7 *ᵥ (M7 *ᵥ (Pi.single i 1 : Fin Tag.E7.rank → ℤ))) = Pi.single i 1 := by
  decide +kernel

private theorem rho_iter_two (S : LangSetup .E7 L p) (hρ : RhoIs S e7ThreeMat)
    {γ : Fin Tag.E7.rank → ℤ} (hγ : IsRoot Tag.E7 γ) :
    S.ρ γ = M7 *ᵥ γ ∧ S.ρ (S.ρ γ) = M7 *ᵥ (M7 *ᵥ γ) := by
  have h1 : S.ρ γ = M7 *ᵥ γ := hρ γ hγ
  exact ⟨h1, by rw [hρ _ ((S.frob.isRoot_iff γ).2 hγ), h1]⟩

private theorem isGoodRoot_E7_two_of_orbit (S : LangSetup .E7 L p) (hρ : RhoIs S e7ThreeMat)
    (hq : S.D.q = 2) (hp : p = 7) {β : Fin Tag.E7.rank → ℤ} (hβ : IsRoot Tag.E7 β)
    (hab : iform β (M7 *ᵥ β) = -1) (h2 : M7 *ᵥ (M7 *ᵥ β) = -(β + M7 *ᵥ β))
    (h3 : M7 *ᵥ (M7 *ᵥ (M7 *ᵥ β)) = β) : IsGoodRoot S β := by
  have hβ' : IsRoot Tag.E7 (S.ρ β) := (S.frob.isRoot_iff β).2 hβ
  obtain ⟨hρβ, hρρβ⟩ := rho_iter_two S hρ hβ
  have hρ3 : S.ρ (-(β + S.ρ β)) = β := by
    have hroot : IsRoot Tag.E7 (S.ρ (S.ρ β)) := (S.frob.isRoot_iff _).2 hβ'
    have e : -(β + S.ρ β) = S.ρ (S.ρ β) := by rw [hρρβ, h2, hρβ]
    rw [e, hρ _ hroot, hρρβ, h3]
  exact isGoodRoot_of_A2orbit_two S (Or.inr (Or.inl rfl)) hq hp hβ hβ' (by rw [hρβ]; exact hab)
    (by rw [hρρβ, hρβ]; exact h2) hρ3

private abbrev b0 : Fin Tag.E7.rank → ℤ := toVec Tag.E7.rank [0, 0, 0, 0, 0, 1, 1]

private theorem b0_isRoot : IsRoot Tag.E7 b0 := by
  rw [isRoot_iff_mem_artifactRoots]
  decide +kernel

private theorem e7_rankOneOrbit_b0 (S : LangSetup .E7 L p) (hρ : RhoIs S e7ThreeMat) :
    RankOneOrbit S.ρ b0 3 ∧ (S.ρ : (Fin Tag.E7.rank → ℤ) → _)^[3] b0 = b0 := by
  have hR : ∀ r ∈ Tag.E7.artifactRoots, r.length = Tag.E7.rank := by decide +kernel
  have hchk : RankOneChk Tag.E7.rank (cartanList Tag.E7) e7ThreeMat Tag.E7.artifactRoots
      [0, 0, 0, 0, 0, 1, 1] 3 := by decide +kernel
  refine ⟨rankOneOrbit_of_check S (Or.inr (Or.inr (Or.inl rfl))) (toMat_cartanList _) hρ hR hchk,
    ?_⟩
  have horb : orbL Tag.E7.rank e7ThreeMat [0, 0, 0, 0, 0, 1, 1] 3 = [0, 0, 0, 0, 0, 1, 1] := by
    decide +kernel
  rw [toVec_orbL S hρ b0_isRoot 3, horb]

private theorem e7_link_plus :
    (-(Pi.single 5 1 : Fin Tag.E7.rank → ℤ)) ≠ b0 ∧ (-(Pi.single 5 1 : Fin Tag.E7.rank → ℤ)) ≠ -b0 ∧
    (-(Pi.single 5 1 : Fin Tag.E7.rank → ℤ)) + b0 = Pi.single 6 1 ∧
    (-(Pi.single 5 1 : Fin Tag.E7.rank → ℤ)) ≠ M7 *ᵥ b0 ∧
    (-(Pi.single 5 1 : Fin Tag.E7.rank → ℤ)) ≠ -(M7 *ᵥ b0) ∧
    (-(Pi.single 5 1 : Fin Tag.E7.rank → ℤ)) ≠ M7 *ᵥ (M7 *ᵥ b0) ∧
    (-(Pi.single 5 1 : Fin Tag.E7.rank → ℤ)) ≠ -(M7 *ᵥ (M7 *ᵥ b0)) := by
  decide +kernel

private theorem e7_link_plus_roots :
    ¬ IsRoot Tag.E7 ((-(Pi.single 5 1 : Fin Tag.E7.rank → ℤ)) + M7 *ᵥ b0) ∧
    ¬ IsRoot Tag.E7 ((-(Pi.single 5 1 : Fin Tag.E7.rank → ℤ)) + M7 *ᵥ (M7 *ᵥ b0)) := by
  simp only [isRoot_iff_mem_artifactRoots]
  decide +kernel

private theorem e7_link_minus :
    (Pi.single 5 1 : Fin Tag.E7.rank → ℤ) ≠ -b0 ∧ (Pi.single 5 1 : Fin Tag.E7.rank → ℤ) ≠ -(-b0) ∧
    (Pi.single 5 1 : Fin Tag.E7.rank → ℤ) + -b0 = -(Pi.single 6 1) ∧
    (Pi.single 5 1 : Fin Tag.E7.rank → ℤ) ≠ M7 *ᵥ (-b0) ∧
    (Pi.single 5 1 : Fin Tag.E7.rank → ℤ) ≠ -(M7 *ᵥ (-b0)) ∧
    (Pi.single 5 1 : Fin Tag.E7.rank → ℤ) ≠ M7 *ᵥ (M7 *ᵥ (-b0)) ∧
    (Pi.single 5 1 : Fin Tag.E7.rank → ℤ) ≠ -(M7 *ᵥ (M7 *ᵥ (-b0))) := by
  decide +kernel

private theorem e7_link_minus_roots :
    ¬ IsRoot Tag.E7 ((Pi.single 5 1 : Fin Tag.E7.rank → ℤ) + M7 *ᵥ (-b0)) ∧
    ¬ IsRoot Tag.E7 ((Pi.single 5 1 : Fin Tag.E7.rank → ℤ) + M7 *ᵥ (M7 *ᵥ (-b0))) := by
  simp only [isRoot_iff_mem_artifactRoots]
  decide +kernel

private theorem rank_ofNat_seven : ∀ i : Fin Tag.E7.rank, ¬ i.val ≤ 5 → i = 6 := by
  decide

theorem centralizerTrivial_E7_two (S : LangSetup .E7 L p) (hρ : RhoIs S e7ThreeMat)
    (hq : S.D.q = 2) (hp : p = 7) {D₁ : Subgroup (ModGL .E7 L)} (hD₁E : D₁ ≤ S.E)
    (hD₁c : Nat.card D₁ = p ^ 2) : CentralizerTrivial S D₁ := by
  refine centralizerTrivial_of_simple S D₁ fun z hz i => ?_
  have hgood : ∀ j : Fin Tag.E7.rank, j.val ≤ 5 →
      ∀ x ∈ rootRankOneGroup .E7 L (Pi.single j 1), Commute z x := by
    intro j hj
    obtain ⟨h1, h2, h3⟩ := e7_A2_data j hj
    have hg : IsGoodRoot S (Pi.single j 1) :=
      isGoodRoot_E7_two_of_orbit S hρ hq hp (isRoot_single _ j) h1 h2 h3
    obtain ⟨Y, hYbig, hYc, -⟩ := goodRoot_subset_bigComponentSet S hD₁E hD₁c hg
    exact hYc z fun y hy => hz y (Or.inl (hYbig hy))
  by_cases hi : i.val ≤ 5
  · exact hgood i hi
  · rw [rank_ofNat_seven i hi]
    obtain ⟨hm, h3⟩ := e7_rankOneOrbit_b0 S hρ
    have hN := norm_mem_bigComponentSet_of_rankOneOrbit_two S (Or.inr (Or.inr (Or.inl rfl))) hm
      h3 hq hp hD₁E hD₁c
    have hb0 := b0_isRoot
    have h5 : IsRoot Tag.E7 (Pi.single 5 1 : Fin Tag.E7.rank → ℤ) := isRoot_single _ 5
    have hz5 := hgood 5 (by decide)
    have hτ7 : Tag.E7 = .D4 ∨ Tag.E7 = .E6 ∨ Tag.E7 = .E7 ∨ Tag.E7 = .E8 :=
      Or.inr (Or.inr (Or.inl rfl))
    have h₁ : ∀ s : L, Commute z (pinnedX .E7 L (Pi.single 6 1) s) := by
      obtain ⟨c₀, c₁, c₂, hc₀, hc₁, hc₂, hmem⟩ := hN b0 (Set.mem_insert _ _)
      obtain ⟨hρ1, hρ2⟩ := rho_iter_two S hρ hb0
      rw [hρ2, hρ1] at hmem
      obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := e7_link_plus
      obtain ⟨r1, r2⟩ := e7_link_plus_roots
      have hα : IsRoot Tag.E7 (-(Pi.single 5 1 : Fin Tag.E7.rank → ℤ)) := IsRoot.neg h5
      have hβ1 : IsRoot Tag.E7 (M7 *ᵥ b0) := by
        rw [← hρ1]; exact (S.frob.isRoot_iff _).2 hb0
      have hβ2 : IsRoot Tag.E7 (M7 *ᵥ (M7 *ᵥ b0)) := by
        rw [← hρ2]; exact (S.frob.isRoot_iff _).2 ((S.frob.isRoot_iff _).2 hb0)
      have hzα : ∀ s : L, Commute z (pinnedX .E7 L (-(Pi.single 5 1 : Fin Tag.E7.rank → ℤ)) s) :=
        fun s => hz5 _ (pinnedX_mem_rootRankOneGroup h5 (Or.inr rfl) s)
      have key := commute_pinnedX_add_of_commutator hτ7 (z := z) hα hb0 e1 e2
        (by rw [e3]; exact isRoot_single _ 6)
        (R := pinnedX .E7 L (M7 *ᵥ b0) c₁ * pinnedX .E7 L (M7 *ᵥ (M7 *ᵥ b0)) c₂)
        (fun s => (commute_pinnedX_of_not_root hτ7 hα hβ1 e4 e5 r1 s c₁).mul_right
          (commute_pinnedX_of_not_root hτ7 hα hβ2 e6 e7 r2 s c₂)) hc₀ hzα
        (by rw [← mul_assoc]; exact hz _ (Or.inl hmem))
      intro s
      have := key s
      rwa [e3] at this
    have h₂ : ∀ s : L, Commute z (pinnedX .E7 L (-(Pi.single 6 1)) s) := by
      obtain ⟨c₀, c₁, c₂, hc₀, hc₁, hc₂, hmem⟩ := hN (-b0) (Set.mem_insert_of_mem _ rfl)
      have hnb0 : IsRoot Tag.E7 (-b0) := IsRoot.neg hb0
      obtain ⟨hρ1, hρ2⟩ := rho_iter_two S hρ hnb0
      rw [hρ2, hρ1] at hmem
      obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := e7_link_minus
      obtain ⟨r1, r2⟩ := e7_link_minus_roots
      have hβ1 : IsRoot Tag.E7 (M7 *ᵥ (-b0)) := by
        rw [← hρ1]; exact (S.frob.isRoot_iff _).2 hnb0
      have hβ2 : IsRoot Tag.E7 (M7 *ᵥ (M7 *ᵥ (-b0))) := by
        rw [← hρ2]; exact (S.frob.isRoot_iff _).2 ((S.frob.isRoot_iff _).2 hnb0)
      have hzα : ∀ s : L, Commute z (pinnedX .E7 L (Pi.single 5 1 : Fin Tag.E7.rank → ℤ) s) :=
        fun s => hz5 _ (pinnedX_mem_rootRankOneGroup h5 (Or.inl rfl) s)
      have key := commute_pinnedX_add_of_commutator hτ7 (z := z) h5 hnb0 e1 e2
        (by rw [e3]; exact IsRoot.neg (isRoot_single _ 6))
        (R := pinnedX .E7 L (M7 *ᵥ (-b0)) c₁ * pinnedX .E7 L (M7 *ᵥ (M7 *ᵥ (-b0))) c₂)
        (fun s => (commute_pinnedX_of_not_root hτ7 h5 hβ1 e4 e5 r1 s c₁).mul_right
          (commute_pinnedX_of_not_root hτ7 h5 hβ2 e6 e7 r2 s c₂)) hc₀ hzα
        (by rw [← mul_assoc]; exact hz _ (Or.inl hmem))
      intro s
      have := key s
      rwa [e3] at this
    exact commute_rankOne_of_pinnedX_pm (isRoot_single _ 6) h₁ h₂

theorem smallQ_E7_three : SmallQ_E7_three := by
  intro L _ _ p S hp7 hAlg he hρ hq
  have hp : p = 7 := by
    have he' : orderOf (((2 : ℕ)) : ZMod p) = 3 := by rw [← hq]; exact he
    have h8 : ((2 : ℕ) : ZMod p) ^ 3 = 1 := by
      rw [← he']
      exact pow_orderOf_eq_one _
    have h7 : ((7 : ℕ) : ZMod p) = 0 := by
      push_cast at h8 ⊢
      linear_combination h8
    have hd : p ∣ 7 := (ZMod.natCast_eq_zero_iff 7 p).1 h7
    exact (Nat.prime_dvd_prime_iff_eq S.hp (by norm_num)).1 hd
  exact setupRigid_E7 S (by omega) hAlg (fun D₁ _ _ => noFrobeniusInner_of_q_eq_two S hq D₁)
    (fun D₁ hD₁E hD₁c => centralizerTrivial_E7_two S hρ hq hp hD₁E hD₁c)

end E7

end CFSG.HardMathSupport.Timmesfeld.LangTorus
