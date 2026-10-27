module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWJMain
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWInvolutionU
public import CFSG.GH74.GLS.SP.Local.SPLRestrict
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4Phi36Plane
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.Cover
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport.FamilyProved
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.ThreeQ1
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.ClosingOddProved
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.OuterThree
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.Phi6RouteW
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWSylow
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LieType.SeitzGeneration.ExcOuterTriality
public import CFSG.LieType.SeitzGeneration.OrthLift
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotAlignCores
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR7Split
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiCaseLTorus
public import CFSG.RankThree.PartOne.SEITZ6.G2MaxDone
public import Certificates.Kernel.SporSch.Th.Plane2320
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWSymForm
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWJPsi

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartOne.K1214
  CFSG.RankThree.PartOne.K128 CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.RankThree.Lattice

open scoped Matrix MatrixGroups

local notation "𝒞[" K ", " σ "]" => graphFixedRootGroup TwistTag.D4 K (RingEquiv.toRingHom σ)



section Out

theorem exists_phi6_J_datum {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f)
    (hℓ2 : ℓ ≠ 2) (hq3 : 3 ≤ ℓ ^ f) (K : Type) [Field K] [Finite K] [CharP K ℓ]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {r : ℕ}
    (hr : r.Prime) (hr3 : 3 < r)
    (hrd : (r : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + (-1) * ((ℓ ^ f : ℕ) : ℤ) + 1) :
    ∃ F : D4PhiFrame ℓ f K σ (-1) r (AlgebraicClosure K), ∃ E : Subgroup 𝒞[K, σ],
      (∀ y ∈ E, y ^ r = 1) ∧ Nat.card E = r ^ 2 ∧
      (∀ y ∈ E, F.g0⁻¹ * triEmb K σ (AlgebraicClosure K) y * F.g0 ∈
        twistedTorusOf F.n (twistHom TwistTag.D4 (AlgebraicClosure K)
          (iterateFrobenius (AlgebraicClosure K) ℓ f))) ∧
      ∃ s ∈ torusGroup TwistTag.D4.tag (AlgebraicClosure K), ∃ w : 𝒞[K, σ],
        triEmb K σ (AlgebraicClosure K) w =
          F.g0 * (s * trialityOpposition (AlgebraicClosure K)) * F.g0⁻¹ ∧
        w * w = 1 ∧ (∀ y ∈ E, w * y * w⁻¹ = y⁻¹) ∧
        fieldActor (t := TwistTag.D4) σ σ w = w ∧
        (∃ P : Sylow r 𝒞[K, σ], E ≤ (P : Subgroup 𝒞[K, σ]) ∧
          (∀ x ∈ (P : Subgroup 𝒞[K, σ]), ∀ y ∈ (P : Subgroup 𝒞[K, σ]), x * y = y * x) ∧
          (∀ x ∈ (P : Subgroup 𝒞[K, σ]), x ^ r = 1 → x ∈ E)) ∧
        (∃ x₁ ∈ E, x₁ ≠ 1 ∧ ∃ u : 𝒞[K, σ],
          u ≠ 1 ∧ u * u = 1 ∧ u * x₁ = x₁ * u ∧ u * w = w * u) ∧
        (∃ c ∈ E, c ≠ 1 ∧ fieldActor (t := TwistTag.D4) σ σ c = c) ∧
        ∃ x₀ ∈ E, x₀ ≠ 1 ∧ ∃ sp : D4PhiSpecial F x₀ 0, sp.c = 1 ∧
          ∃ θ : SL(2, fixSubfield σ) →* 𝒞[K, σ], (∀ t, θ t ∈ d4phiPx sp) ∧
            (∀ t, θ t * w = w * θ t) ∧ (∀ t, θ t = 1 ↔ t = 1 ∨ t = -1) ∧
            Nat.card θ.range = ℓ ^ f * ((ℓ ^ f) ^ 2 - 1) / 2 ∧
            (4 ≤ ℓ ^ f → ⁅θ.range, θ.range⁆ = θ.range ∧ IsSimpleGroup θ.range) ∧
            ∀ t, fieldActor (t := TwistTag.D4) σ σ (θ t) = θ t := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : Fact r.Prime := ⟨hr⟩
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
  set L := AlgebraicClosure K with hL
  have : IsAlgClosed L := inferInstance
  have : NeZero r := ⟨hr.ne_zero⟩
  have hn₂C : jRep L jW2 ∈ adjointGroup TwistTag.D4.tag L :=
    monomialSubgroup_le_adjointGroup' (jRep_mem_monomial jW2)
  have hn₂P : diagramMap TwistTag.D4 L * jRep L jW2 = jRep L jW2 * diagramMap TwistTag.D4 L :=
    diagramMap_comm_canonicalRep ((mem_relWeylTwist TwistTag.D4).2 weylTwist_jW2)
  obtain ⟨g₂, hg₂C, hg₂P, hg₂F⟩ := exists_lang_g2_D4 (ℓ := ℓ) hf (jRep L jW2) hn₂C hn₂P
  let F : D4PhiFrame ℓ f K σ (-1) r L :=
    d4phiFrameOfG0 hf hK hσ (Or.inr rfl) hr hr3 hrd (jN L jU jW2) (jN_mem_monomial jU jW2)
      (jU * jW2 * (weylTwist TwistTag.D4 jU)⁻¹) (weylQuotientHom_jN jU jW2)
      jWeyl_zero_spec.2.2.1 (jG0 L jU g₂) (jG0_mem_adjointGroup jU hg₂C)
      (twistHom_jG0 _ jU jW2 hg₂F)
  have hg0 : F.g0 = jG0 L jU g₂ := rfl
  have hg₂F' : twistHom TwistTag.D4 L (iterateFrobenius L ℓ f) g₂ = g₂ * jRep L jW2 := hg₂F
  have hshape := sylowShape_D4_36 (ℓ := ℓ) hf K hK σ hσ (ε := -1) (Or.inr rfl) hr hr3 hrd
  have hd0 : d4T36d (-1) (ℓ ^ f) ≠ 0 := ((d4T36d_odd (Or.inr rfl) hq1).pos).ne'
  have hdvd : r ∣ d4T36d (-1) (ℓ ^ f) := by
    have h := d4T36d_cast (Or.inr rfl : (-1 : ℤ) = 1 ∨ (-1 : ℤ) = -1) hq1
    rw [← h] at hrd
    exact_mod_cast hrd
  have he : 1 ≤ (d4T36d (-1) (ℓ ^ f)).factorization r :=
    hr.factorization_pos_of_dvd hd0 hdvd
  let S : Sylow r 𝒞[K, σ] := default
  obtain ⟨φ⟩ := hshape (S : Subgroup 𝒞[K, σ]) S.isPGroup' S.not_dvd_index
  obtain ⟨E₁, hE₁S, hE₁p, hE₁c, hE₁Ω, hScomm⟩ := exists_plane_of_sylowShape_omega he
    (S : Subgroup 𝒞[K, σ]) φ
  have hE₁P : IsPGroup r E₁ := S.isPGroup'.to_le hE₁S
  obtain ⟨c, hc⟩ := F.hconj E₁ hE₁P
  set E : Subgroup 𝒞[K, σ] := E₁.map (MulAut.conj c).toMonoidHom with hEdef
  have htor : ∀ y ∈ E, F.g0⁻¹ * triEmb K σ L y * F.g0 ∈
      twistedTorusOf F.n (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f)) := by
    rintro _ ⟨y, hy, rfl⟩
    exact hc y hy
  have hEp : ∀ y ∈ E, y ^ r = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    change (c * y * c⁻¹) ^ r = 1
    rw [conj_pow, hE₁p y hy]
    group
  have hEc : Nat.card E = r ^ 2 := by
    rw [hEdef, Subgroup.card_map_of_injective (MulAut.conj c).injective]
    exact hE₁c
  obtain ⟨s, hsT, w, hwι, hww, hwfix, hinv⟩ := exists_J_involution hσ F hg₂C hg₂P hg₂F' hg0
  have hwE : ∀ y ∈ E, w * y * w⁻¹ = y⁻¹ := by
    intro y hy
    have h := hinv y (htor y hy)
    apply triEmb_injective (K := K) (σ := σ) (L := L)
    rw [map_inv]
    have h2 : (F.g0⁻¹ * triEmb K σ L y * F.g0)⁻¹ =
        F.g0⁻¹ * (triEmb K σ L y)⁻¹ * F.g0 := by group
    rw [h2] at h
    exact mul_left_cancel (mul_right_cancel h)
  obtain ⟨P, hEP, hPcomm, hPΩ⟩ := conj_sylow_data S E₁ hE₁S hE₁Ω hScomm c
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    hPcomm a (hEP ha) b (hEP hb)
  have : IsMulCommutative E := ⟨⟨fun a b => Subtype.ext (hEcomm a a.2 b b.2)⟩⟩
  have hEA : CFSG.IsElementaryAbelian r E := by
    refine { exponent_dvd_p := ?_ }
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun g => ?_
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hEp g g.2
  obtain ⟨x₁, hx₁, hx₁1, hscd⟩ := exists_singularData_of_plane hℓ hf K hK σ hσ
    (Or.inr rfl : (-1 : ℤ) = 1 ∨ (-1 : ℤ) = -1) hr hr3 hrd E hEA hEc
  have heven := even_card_of_quasisimple_commutator _ hscd.1
  obtain ⟨u, hu1, huu, hux, huw⟩ := exists_involution_commuting_of_inverted hww (hwE x₁ hx₁) heven
  obtain ⟨c0, hc0pl, hc01, hc0fix⟩ := exists_c_in_plane F hg₂P hg0
  have hEsub : (E : Set 𝒞[K, σ]) ⊆ planeSet F := fun y hy => ⟨hEp y hy, htor y hy⟩
  have hEn : (E : Set 𝒞[K, σ]).ncard = r * r := by
    rw [← Nat.card_coe_set_eq]
    change Nat.card E = _
    rw [hEc, pow_two]
  have hEeq : (E : Set 𝒞[K, σ]) = planeSet F :=
    Set.eq_of_subset_of_ncard_le hEsub (by rw [hEn]; exact ncard_planeSet_le F) (Set.toFinite _)
  have hc0E : c0 ∈ E := by
    have : c0 ∈ (E : Set 𝒞[K, σ]) := by rw [hEeq]; exact hc0pl
    exact this
  have h2 : (2 : fixSubfield σ) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : K) = 0 := by
      have h2K := map_ofNat (fixSubfield σ).subtype 2
      rw [Nat.cast_ofNat, ← h2K]
      change ((2 : fixSubfield σ) : K) = 0
      rw [h]
      rfl
    rw [CharP.cast_eq_zero_iff K ℓ] at h'
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 h')
  have hC2 : ∀ B : Matrix (Fin 3) (Fin 3) (fixSubfield σ), Bᵀ = B → B.det ≠ 0 →
      ∃ (P : GL (Fin 3) (fixSubfield σ)) (a : fixSubfield σ), B = a •
        ((P : Matrix (Fin 3) (Fin 3) (fixSubfield σ)) * sym2Form (fixSubfield σ) *
          (P : Matrix (Fin 3) (Fin 3) (fixSubfield σ))ᵀ) := fun B hB hdet => by
    obtain ⟨P, c, hc⟩ := exists_sym_form_equiv h2 B hB hdet
    exact ⟨P, (c : fixSubfield σ), hc⟩
  have hc1 : ∀ y ∈ E, F.g0⁻¹ * triEmb K σ L ((1 : 𝒞[K, σ]) * y * (1 : 𝒞[K, σ])⁻¹) * F.g0 ∈
      twistedTorusOf F.n (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f)) := fun y hy => by
    rw [one_mul, inv_one, mul_one]
    exact htor y hy
  obtain ⟨x, hx1, hx2, -, -, -⟩ := d4phi_special_lines_of_conj F E hEp hEc 1 hc1
  obtain ⟨sp, hsp⟩ := hx2 0
  obtain ⟨D⟩ := d4phi_exists_algData F 0
  obtain ⟨θ, hθP, hθw, hθker, hθcard, hθps⟩ := exists_Px_hom_three F hℓ2 hq3 sp hsp D w s hsT
    hww hwι hC2
  exact ⟨F, E, hEp, hEc, htor, s, hsT, w, hwι, hww, hwE, hwfix,
    ⟨P, hEP, hPcomm, hPΩ⟩, ⟨x₁, hx₁, hx₁1, u, hu1, huu, hux, huw⟩, ⟨c0, hc0E, hc01, hc0fix⟩,
    x 0, (hx1 0).1, (hx1 0).2, sp, hsp, θ, hθP, hθw, hθker, hθcard, hθps,
    fun t => fieldActor_eq_of_mem_Px hσ F hg₂P hg0 sp hsp (hθP t)⟩

end Out

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
