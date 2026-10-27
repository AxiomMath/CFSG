module

public import CFSG.RankThree.PartTwo.KFacts.AutKindsCentral
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenBasics
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.ThreeTenDvdP1

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open Matrix
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LocalAnalysis.AGL81TheoremCD.Section12 (ThreeTenTorusExclusion)
open CFSG.RankThree.PartTwo.KFacts (IsInnerAut isInnerAut_congr isInnerAut_descendAut_iff)

theorem exists_conj_of_threeTenHyp {H : Type} [Group H] [Finite H]
    {I D P Y : Subgroup H} {p d : ℕ} (hhyp : ThreeTenHyp I D P Y p d)
    (e : ↥I ≃* SpecialLinearGroup (Fin 3) (ZMod p))
    (htor : ThreeTenTorusExclusion p d)
    {δ : H} (hδ : δ ∈ D) :
    ∃ t : ↥I, ∀ x : ↥I, δ * (x : H) * δ⁻¹ = (t : H) * (x : H) * (t : H)⁻¹ := by
  obtain ⟨hp, -, hd, hd2, -, hI, hD, -, -, -, -, -⟩ := hhyp
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact d.Prime := ⟨hd⟩
  haveI hInormal : I.Normal := normal_of_oPPrimeHull_eq hI
  let Θ : H →* MulAut ↥I := MulAut.conjNormal
  let ψ : ↥D →* MulAut (projectiveSL 3 (ZMod p)) :=
    (descendAut 3 (ZMod p)).comp ((MulAut.congr e).toMonoidHom.comp (Θ.comp D.subtype))
  have hOutdvd : Nat.card (Outer (projectiveSL 3 (ZMod p))) ∣ 2 * Nat.gcd 3 (p - 1) := by
    have hk : Nat.card (ZMod p) = p ^ 1 := by rw [pow_one, Nat.card_zmod]
    have h := higher_linear_outer_order_divides_field_gcd_bound
      (k := ZMod p) (p := p) (f := 1) (n := 3) hp le_rfl (by norm_num) hk
    simpa using h
  have hOutNotDvd : ¬ d ∣ Nat.card (Outer (projectiveSL 3 (ZMod p))) := by
    have hdvd2 : ¬ d ∣ 2 := by
      intro h
      rcases (Nat.dvd_prime Nat.prime_two).1 h with h1 | h1
      · exact hd.ne_one h1
      · exact hd2 h1
    have hnotgcd : ¬ d ∣ Nat.gcd 3 (p - 1) := fun h =>
      htor.1 (h.trans (Nat.gcd_dvd_right 3 (p - 1)))
    intro h
    rcases (Nat.Prime.dvd_mul hd).1 (h.trans hOutdvd) with h2 | hg
    · exact hdvd2 h2
    · exact hnotgcd hg
  have hψinner : IsInnerAut (ψ ⟨δ, hδ⟩) := by
    let f : ↥D →* Outer (projectiveSL 3 (ZMod p)) :=
      (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner
        (projectiveSL 3 (ZMod p)))).comp ψ
    haveI hAutFin : Finite (MulAut (projectiveSL 3 (ZMod p))) :=
      Finite.of_injective
        (fun φ => (φ : projectiveSL 3 (ZMod p) → projectiveSL 3 (ZMod p)))
        (fun a b h => MulEquiv.ext (congrFun h))
    haveI hOutFin : Finite (Outer (projectiveSL 3 (ZMod p))) :=
      Finite.of_surjective (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner
        (projectiveSL 3 (ZMod p))))
        (QuotientGroup.mk'_surjective _)
    have hrange : IsPGroup d ↥f.range :=
      hD.isPGroup.of_surjective f.rangeRestrict f.rangeRestrict_surjective
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hrange
    have hk1 : Nat.card ↥f.range ∣ Nat.card (Outer (projectiveSL 3 (ZMod p))) :=
      Subgroup.card_subgroup_dvd_card f.range
    have hk2 : Nat.card ↥f.range ∣ d ^ k := by rw [hk]
    have hcop : Nat.Coprime (Nat.card (Outer (projectiveSL 3 (ZMod p)))) (d ^ k) :=
      hd.coprime_pow_of_not_dvd hOutNotDvd
    have hone : Nat.card ↥f.range = 1 := Nat.eq_one_of_dvd_coprimes hcop hk1 hk2
    have hf : f = 1 := MonoidHom.range_eq_bot_iff.mp (Subgroup.card_eq_one.mp hone)
    have hmem : ψ ⟨δ, hδ⟩ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
        (projectiveSL 3 (ZMod p)) := by
      refine (QuotientGroup.eq_one_iff _).mp ?_
      show f ⟨δ, hδ⟩ = 1
      rw [hf]
      rfl
    exact hmem
  have hτinner : IsInnerAut (MulAut.congr e (Θ δ)) :=
    (isInnerAut_descendAut_iff (K := ZMod p) (n := 3) (by norm_num)).mp hψinner
  have hinnerΘ : IsInnerAut (Θ δ) :=
    (isInnerAut_congr e (Θ δ)).mp hτinner
  obtain ⟨t, ht⟩ := MonoidHom.mem_range.mp hinnerΘ
  refine ⟨t, fun x => ?_⟩
  have hx : ((MulAut.conj t) x : H) = ((Θ δ) x : H) :=
    congrArg (fun φ : MulAut ↥I => (φ x : H)) ht
  have hL : ((MulAut.conj t) x : H) = (t : H) * (x : H) * (t : H)⁻¹ := by
    rw [MulAut.conj_apply]
    rfl
  have hR : ((Θ δ) x : H) = δ * (x : H) * δ⁻¹ := by
    change ((MulAut.conjNormal (H := I) (D.subtype ⟨δ, hδ⟩)) x : H) =
      δ * (x : H) * δ⁻¹
    rw [MulAut.conjNormal_apply]
    rfl
  rw [hR, hL] at hx
  exact hx.symm

end CFSG.LocalAnalysis.AGL81I.Section3
