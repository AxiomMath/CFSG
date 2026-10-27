module

public import CFSG.RankThree.PartOne.D4RC.SpecialLines
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWUnitaryFrame

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne
  CFSG.RankThree.Lattice CFSG.RankThree.Chevalley.TrialityFold CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.D4RC (rcl_lines_abstract)

set_option linter.unusedSectionVars false

local notation "𝒞[" K ", " σ "]" => graphFixedRootGroup TwistTag.D4 K (RingEquiv.toRingHom σ)

section Lines

variable {ℓ f : ℕ} [Fact ℓ.Prime] {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {ε : ℤ}
  {p : ℕ} {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]

theorem d4phi_char_data_of_conj (F : D4PhiFrame ℓ f K σ ε p L) (E : Subgroup 𝒞[K, σ])
    (c : 𝒞[K, σ]) (hc : ∀ y ∈ E, F.g0⁻¹ * triEmb K σ L (c * y * c⁻¹) * F.g0 ∈
      twistedTorusOf F.n (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f))) :
    ∃ β : E →* (Fin TwistTag.D4.tag.rank → Lˣ),
      (∀ y : E, rootDiagUnit TwistTag.D4.tag (β y) =
        F.g0⁻¹ * triEmb K σ L (c * (y : 𝒞[K, σ]) * c⁻¹) * F.g0) ∧
      (∀ y : E, rootDiagUnit TwistTag.D4.tag (β y) ∈
        twistedTorusOf F.n (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f))) ∧
      (∀ y : E, β y ∈ fixedCharTuples (d4T36M ε) (iterateFrobenius L ℓ f)) := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hT := twistedTorus_D4_eq_map_of_weylImage (iterateFrobenius L ℓ f) F.hn F.w F.hnw
    (d4T36M ε) F.hw
  have hex : ∀ y : E, ∃ b ∈ fixedCharTuples (d4T36M ε) (iterateFrobenius L ℓ f),
      rootDiagUnit TwistTag.D4.tag b =
        F.g0⁻¹ * triEmb K σ L (c * (y : 𝒞[K, σ]) * c⁻¹) * F.g0 := fun y => by
    have h := hc y y.2
    rw [hT] at h
    obtain ⟨b, hb, hbb⟩ := h
    exact ⟨b, hb, hbb⟩
  choose β hβfix hβ using hex
  have hmul : ∀ y y' : E, β (y * y') = β y * β y' := fun y y' => by
    apply rootDiagUnit_injective (τ := TwistTag.D4.tag) (K := L)
    have e1 : c * ((y * y' : E) : 𝒞[K, σ]) * c⁻¹ =
        (c * (y : 𝒞[K, σ]) * c⁻¹) * (c * (y' : 𝒞[K, σ]) * c⁻¹) := by
      rw [Subgroup.coe_mul]
      group
    rw [rootDiagUnit_mul, hβ (y * y'), hβ y, hβ y', e1, map_mul]
    group
  refine ⟨MonoidHom.mk' β hmul, hβ, fun y => ?_, hβfix⟩
  have h := hc y y.2
  rw [← hβ y] at h
  exact h

theorem d4phi_special_lines_of_conj (F : D4PhiFrame ℓ f K σ ε p L) (E : Subgroup 𝒞[K, σ])
    (hEp : ∀ y ∈ E, y ^ p = 1) (hEc : Nat.card E = p ^ 2) (c : 𝒞[K, σ])
    (hc : ∀ y ∈ E, F.g0⁻¹ * triEmb K σ L (c * y * c⁻¹) * F.g0 ∈
      twistedTorusOf F.n (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f))) :
    ∃ x : Fin 4 → 𝒞[K, σ],
      (∀ j, x j ∈ E ∧ x j ≠ 1) ∧
      (∀ j, ∃ sp : D4PhiSpecial F (x j) j, sp.c = c) ∧
      (∀ j j', Subgroup.zpowers (x j) = Subgroup.zpowers (x j') → j = j') ∧
      (∀ j (y : 𝒞[K, σ]) (sp : D4PhiSpecial F y j), y ∈ E → sp.c = c →
        y ∈ Subgroup.zpowers (x j)) ∧
      (∀ y ∈ E, y ≠ 1 → (∃ j, y ∈ Subgroup.zpowers (x j)) ∨
        ∃ b : Fin TwistTag.D4.tag.rank → Lˣ,
          rootDiagUnit TwistTag.D4.tag b = F.g0⁻¹ * triEmb K σ L (c * y * c⁻¹) * F.g0 ∧
          rootCharKernel b = ∅) := by
  classical
  have hp := F.hp
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [hEc]; exact pow_ne_zero 2 hp.ne_zero)
  have hEp' : ∀ y : E, y ^ p = 1 := fun y =>
    Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hEp y y.2)
  obtain ⟨β, hβ, hβT, hβfix⟩ := d4phi_char_data_of_conj F E c hc
  have hβ1 : ∀ y : E, y ≠ 1 → β y ≠ 1 := by
    intro y hy h1
    apply hy
    have h2 : F.g0⁻¹ * triEmb K σ L (c * (y : 𝒞[K, σ]) * c⁻¹) * F.g0 = 1 := by
      rw [← hβ y, h1, rootDiagUnit_one]
    have h3 : triEmb K σ L (c * (y : 𝒞[K, σ]) * c⁻¹) = 1 := by
      have := congrArg (fun z => F.g0 * z * F.g0⁻¹) h2
      simpa [mul_assoc] using this
    have h4 : c * (y : 𝒞[K, σ]) * c⁻¹ = 1 := triEmb_injective (h3.trans (map_one _).symm)
    exact Subtype.ext (conj_eq_one_iff.1 h4)
  obtain ⟨χ, hχ⟩ : ∃ χ : (Fin TwistTag.D4.tag.rank → ℤ) → (E →* Lˣ),
      ∀ u g, χ u g = rootChar (β g) u :=
    ⟨fun u => MonoidHom.mk' (fun g => rootChar (β g) u) (fun a b => by
      rw [map_mul]; exact CTTorus.rootChar_mul _ _ _), fun _ _ => rfl⟩
  have hT : ∀ g : E, g ≠ 1 → rootCharKernel (β g) = ∅ ∨
      ∃ j : Fin 4, rootCharKernel (β g) = d4Sigma j :=
    fun g hg => d4T36_rootCharKernel_cases F.hε (hβfix g) (hβ1 g hg)
  obtain ⟨x, hx1, hx2, hx3, hx4⟩ := rcl_lines_abstract (G := E)
    (R := Fin TwistTag.D4.tag.rank → ℤ) (J := Fin 4) hp hEc hEp' χ
    (fun α => IsRoot TwistTag.D4.tag α) (fun j => d4Sigma j)
    (fun j α hα => isRoot_of_mem_d4Sigma hα)
    (fun j => ⟨trialityU j, mem_trialitySigma.2 List.mem_cons_self⟩)
    (fun j j' h => pairwise_disjoint_trialitySigma h) (fun g => rootCharKernel (β g))
    (fun g α => by rw [hχ]; exact Iff.rfl) hT
  have hzp : ∀ (j : Fin 4) (g : E), g ∈ Subgroup.zpowers (x j) →
      (g : 𝒞[K, σ]) ∈ Subgroup.zpowers ((x j : E) : 𝒞[K, σ]) := by
    intro j g hg
    obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    exact Subgroup.mem_zpowers_iff.2 ⟨a, by rw [Subgroup.coe_zpow]⟩
  have hzp' : ∀ j j' : Fin 4, ((x j' : E) : 𝒞[K, σ]) ∈ Subgroup.zpowers ((x j : E) : 𝒞[K, σ]) →
      x j' ∈ Subgroup.zpowers (x j) := by
    intro j j' h
    obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.1 h
    exact Subgroup.mem_zpowers_iff.2 ⟨a, Subtype.ext (by rw [Subgroup.coe_zpow]; exact ha)⟩
  refine ⟨fun j => (x j : 𝒞[K, σ]),
    fun j => ⟨(x j).2, fun h => (hx1 j).1 (Subtype.ext h)⟩, ?_, ?_, ?_, ?_⟩
  · intro j
    have hne : ((x j : E) : 𝒞[K, σ]) ≠ 1 := fun h => (hx1 j).1 (Subtype.ext h)
    have hord : orderOf ((x j : E) : 𝒞[K, σ]) = p := orderOf_eq_prime (hEp _ (x j).2) hne
    exact ⟨⟨c, β (x j), hord, hβ (x j), hβT (x j), (hx1 j).2⟩, rfl⟩
  · intro j j' h
    have h1 : ((x j' : E) : 𝒞[K, σ]) ∈ Subgroup.zpowers ((x j : E) : 𝒞[K, σ]) := by
      rw [h]
      exact Subgroup.mem_zpowers _
    exact (hx2 j j' (hzp' j j' h1)).symm
  · intro j y sp hy hc
    have hb : sp.b = β ⟨y, hy⟩ := by
      apply rootDiagUnit_injective (τ := TwistTag.D4.tag) (K := L)
      rw [sp.hb, hβ ⟨y, hy⟩, hc]
    have hk : rootCharKernel (β ⟨y, hy⟩) = d4Sigma j := by
      rw [← hb]
      exact sp.hker
    exact hzp j ⟨y, hy⟩ (hx3 j ⟨y, hy⟩ hk)
  · intro y hy hne
    rcases hx4 ⟨y, hy⟩ (fun h => hne (congrArg Subtype.val h)) with ⟨j, hj⟩ | hempty
    · exact Or.inl ⟨j, hzp j _ hj⟩
    · exact Or.inr ⟨β ⟨y, hy⟩, hβ ⟨y, hy⟩, hempty⟩

end Lines

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
