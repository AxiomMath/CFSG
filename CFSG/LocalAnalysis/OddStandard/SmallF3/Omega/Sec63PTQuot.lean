module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PFbar
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PTMain
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PTPocket

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec63PT_factAt_of_quotient {A P : Type} [Group A] [Finite A] [Group P]
    (e : A ⧸ oddCore A ≃* P) (hcen : oddCore A ≤ center A) {σ : MulAut A} {α : MulAut P}
    (hσ : σ * σ = 1) (hασ : ∀ a : A, e (QuotientGroup.mk (σ a)) = α (e (QuotientGroup.mk a)))
    (hF : Sec63PTFactAt P α) : Sec63PTFactAt A σ := by
  haveI : Finite P := Finite.of_surjective (⇑e) e.surjective
  let ρ : A →* P := e.toMonoidHom.comp (QuotientGroup.mk' (oddCore A))
  have h : OddCentralCover ρ := sec63PT_oddCentralCover_of_equiv e hcen
  unfold Sec63PTFactAt at hF ⊢
  intro V hV hVL b hbV hb2
  have hbb : b * b = 1 := by
    have h' := pow_orderOf_eq_one b
    rw [hb2] at h'
    simpa [pow_two] using h'
  have hfix : (fixSub σ).map ρ = fixSub α :=
    sec63PT_map_fixSub h hσ (fun a => hασ a)
  have hVc : IsComponentIn (V.map ρ) (fixSub α) := by
    rw [← hfix]
    exact sec63PT_isComponentIn_map ρ h.ker_le_center hV
  have hVL' : IsL29 (V.map ρ) := sec63PT_isL29_map h hVL
  have hρbb : ρ b * ρ b = 1 := by rw [← map_mul, hbb, map_one]
  have hρbne : ρ b ≠ 1 := by
    intro h1
    have hbker : b ∈ ρ.ker := MonoidHom.mem_ker.mpr h1
    have hdvd : orderOf b ∣ Nat.card ρ.ker := Subgroup.orderOf_dvd_natCard ρ.ker hbker
    rw [hb2] at hdvd
    exact (Nat.not_even_iff_odd.mpr h.odd_card_ker) (even_iff_two_dvd.mpr hdvd)
  have hρb2 : orderOf (ρ b) = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using hρbb) hρbne
  rcases hF (V.map ρ) hVc hVL' (ρ b) (Subgroup.mem_map_of_mem ρ hbV) hρb2 with
    hpocket | ⟨X, hXc, hXL, hXu, h2, R, hR2, hRle, hR8, hRgen⟩
  · exact Or.inl (sec63PT_isI4PlusIn_top_of_equiv e hb2 hpocket)
  · obtain ⟨hc, hmap, huniq⟩ := sec63PT_lift_unique h hbb hXc hXu
    refine Or.inr ⟨coverDerived ρ X, hc, sec63PT_isL29_coverDerived h hXc.isQuasisimple hXL,
      huniq, ?_, ?_⟩
    · refine sec63PT_two_bound h ?_
      intro Q hQ hQle
      apply h2 Q hQ
      rwa [← hmap]
    · exact sec63PT_R_lift h hbb hR2 hRle hR8 hRgen

end CFSG.OddStandard.SmallF3.Omega
