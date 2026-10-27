module

public import CFSG.LocalAnalysis.ComponentClassification.Foote47P4A
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm47Statement
public import CFSG.LocalAnalysis.ComponentClassification.Foote47P4B

public section

namespace CFSG.ComponentClassification.Foote47

open CFSG Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer

theorem foote_theorem_4_7_of_inputs (hA5 : GSThmB.AschbacherTheorem5Input)
    (hE8 : FooteL2FourgroupE8) (hK : AschbacherKnownGroup.AschbacherKnownGroupFacts)
    (hcalc : FooteSmallCentralizers) (hFI : FooteFourgroupInner)
    (hCI : Foote47CentralInvolution) (hOF : Foote47OuterOrderFour)
    (hFG : Foote47FourgroupGeneration) : FooteThm47Statement := by
  intro G _ _ L h M hM t ht htC
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hlt
  rw [not_le] at hlt
  have hv : Viol L M t := ⟨hM, ht, htC, (noEight_iff _).mpr hlt⟩
  set X : Set (Subgroup G × Subgroup G) := {x | Viol L x.1 t ∧ IsPGroup 2 x.2 ∧
    x.2 ≤ coreActionKernel x.1 ⊓ centralizer ({t} : Set G)} with hX
  have hXne : X.Nonempty := ⟨(M, ⊥), hv, IsPGroup.of_bot, bot_le⟩
  obtain ⟨⟨M₀, Q⟩, ⟨hv₀, hQp, hQle⟩, hmax⟩ :=
    Set.exists_max_image X (fun x => Nat.card x.2) (Set.toFinite X) hXne
  have hQsyl : IsSylowOf 2 Q (coreActionKernel M₀ ⊓ centralizer ({t} : Set G)) := by
    obtain ⟨Q', hQ', hQQ'⟩ := exists_isSylowOf_ge_of_le hQle hQp
    have h1 := hmax (M₀, Q') ⟨hv₀, hQ'.isPGroup, hQ'.le⟩
    have h2 : Q' = Q := (Subgroup.eq_of_le_of_card_ge hQQ' h1).symm
    rw [← h2]
    exact hQ'
  obtain ⟨T, hT, hQT⟩ := exists_isSylowOf_ge_of_le (hQle.trans inf_le_left) hQp
  have hQeq : T ⊓ centralizer ({t} : Set G) = Q :=
    hQsyl.eq_of_le (le_inf hQT (hQle.trans inf_le_right))
      (inf_le_inf_right _ hT.le) (hT.isPGroup.to_le inf_le_left)
  have htt : t * t = 1 := by rw [← sq, ← ht]; exact pow_orderOf_eq_one t
  have htQ : t ∈ Q := by
    have hnorm : zpowers t ≤ normalizer ((Q : Subgroup G) : Set G) := by
      refine zpowers_le.mpr (mem_normalizer_iff.mpr fun x => ?_)
      have hc : ∀ y ∈ Q, t * y * t⁻¹ = y := fun y hy => by
        rw [← (mem_centralizer_singleton_iff.mp (mem_inf.mp (hQle hy)).2), mul_inv_cancel_right]
      constructor
      · intro hx
        rw [hc x hx]
        exact hx
      · intro hx
        have h1 := hc _ hx
        rw [show t * (t * x * t⁻¹) * t⁻¹ = t * t * x * (t * t)⁻¹ by group, htt, one_mul,
          inv_one, mul_one] at h1
        rw [h1]
        exact hx
    have htp : IsPGroup 2 (zpowers t) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
    have hsup : Q ⊔ zpowers t = Q := hQsyl.eq_of_le le_sup_left
      (sup_le hQle (zpowers_le.mpr (mem_inf.mpr ⟨hv₀.htC, mem_centralizer_singleton_iff.mpr rfl⟩)))
      (hQp.to_sup_of_normal_left' htp hnorm)
    exact hsup ▸ mem_sup_right (mem_zpowers t)
  have htT : t ∈ T := hQT htQ
  have hmax' : ∀ M' Q' : Subgroup G, Viol L M' t → IsPGroup 2 Q' →
      Q' ≤ coreActionKernel M' ⊓ centralizer ({t} : Set G) →
      Nat.card Q' ≤ Nat.card ↥(T ⊓ centralizer ({t} : Set G)) := by
    intro M' Q' hv' hQ'p hQ'le
    rw [hQeq]
    exact hmax (M', Q') ⟨hv', hQ'p, hQ'le⟩
  obtain ⟨E, hET, hE2, hE8'⟩ := exists_card_eight_le_of_isSylowOf h hv₀.hM hT
  obtain ⟨z, Q₀, hd⟩ := exists_twoData hT.isPGroup hET hE2 hE8' htT ht
    (fun F hF hF2 hF8 => hv₀.hno F (hF.trans (inf_le_inf_right _ hT.le)) hF2 hF8)
  have hQX := isSylowOf_inf_centralizer_footeF h hv₀ hT htT hd hmax'
  obtain ⟨M₁, T₁, S, P, hc, -⟩ := exists_conf h hv₀ hT htT hd hQX
  obtain ⟨w, d⟩ := exists_p4Data h hA5 hE8 hK hcalc hFG hc
  obtain ⟨g, hg⟩ := d.exists_valid h
  by_cases hB : ∃ g : G, Valid P t z w g ∧ g * t * g⁻¹ ∈ innerAct (footeF L t)
  · obtain ⟨g, hg, hin⟩ := hB
    obtain ⟨g', q, hg'P, hq, hg't⟩ := d.exists_normalizer_of_inner h hg hin
    exact d.false_of_normalizer h h.hOut hOF hg'P hq hg't
  · push Not at hB
    exact d.false_of_outer h h.hOut hFI hCI hB hg

end CFSG.ComponentClassification.Foote47
