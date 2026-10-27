module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.Faithful
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.Squares
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.Words
public import CFSG.Sporadic.Schreier.RuIso
public import Certificates.Certificate15024
public import Certificates.Certificate15026

public section

namespace CFSG.EvenSporadicStandard.TwoRu

open Subgroup CFSG.Sporadic.RuSchreier CFSG.Sporadic.Recognition.RuMultiplier
  CFSG.Sporadic.SmallF2

section Involutions

@[expose] noncomputable def ruAEl : ruP := ⟨ruA0, ruA0_mem⟩

@[expose] def twoAClass : Set ruP := {s | (s : Equiv.Perm (Fin 4060)) ∈ ruZP}

theorem involution_dichotomy
    {s : ruP} (hs2 : s ^ 2 = 1) (hs1 : s ≠ 1) :
    (∃ g : ruP, s = g * ruAEl * g⁻¹) ∨ s ∈ twoAClass := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : (s : Equiv.Perm (Fin 4060)) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, hs2, OneMemClass.coe_one]
  have hp1 : (s : Equiv.Perm (Fin 4060)) ≠ 1 := fun h => hs1 (Subtype.ext h)
  have hmem : (s : Equiv.Perm (Fin 4060)) ∈ {t | t ∈ ruP ∧ orderOf t = 2} :=
    ⟨s.2, orderOf_eq_prime hp2 hp1⟩
  rw [ruInvolutions_eq] at hmem
  rcases hmem with hz | ⟨g, hg, hgs⟩
  · exact Or.inr hz
  · exact Or.inl ⟨⟨g, hg⟩, Subtype.ext hgs.symm⟩

theorem twoAClass_conj {s s' : ruP} (hs : s ∈ twoAClass) (hs' : s' ∈ twoAClass) :
    ∃ g : ruP, s' = g * s * g⁻¹ := by
  obtain ⟨g₁, hg₁, h₁⟩ := hs
  obtain ⟨g₂, hg₂, h₂⟩ := hs'
  refine ⟨⟨g₂ * g₁⁻¹, ruP.mul_mem hg₂ (ruP.inv_mem hg₁)⟩, Subtype.ext ?_⟩
  show (s' : Equiv.Perm (Fin 4060)) = g₂ * g₁⁻¹ * (s : Equiv.Perm (Fin 4060)) * (g₂ * g₁⁻¹)⁻¹
  rw [← h₂, ← h₁]
  group

theorem not_sq_conj_a
    {w : ruP} (hw4 : w ^ 4 = 1)
    (hw2 : w ^ 2 ≠ 1) (g : ruP) : w ^ 2 ≠ g * ruAEl * g⁻¹ := by
  intro h
  refine ru_sq_not_mem_ruAP w.2 ?_ ?_ ⟨(g : Equiv.Perm (Fin 4060)), g.2, ?_⟩
  · rw [← Subgroup.coe_pow, hw4, OneMemClass.coe_one]
  · intro h1
    exact hw2 (Subtype.ext (by rw [Subgroup.coe_pow]; exact h1))
  · have := congrArg Subtype.val h
    rw [Subgroup.coe_pow] at this
    exact this.symm

end Involutions

theorem exists_equiv_ruP_J :
    ∃ e : ruP ≃* J ruVec, e ruAEl = a ruVec := by
  refine ⟨ruJEquivP.symm, ?_⟩
  rw [MulEquiv.symm_apply_eq]
  exact (Subtype.ext ruJtoP_a).symm

theorem exists_cover_J
    {L : Type} [Group L] {q : L →* ruP}
    (hq : Function.Surjective q) {t : L} (hker : q.ker = zpowers t) :
    ∃ qJ : L →* J ruVec, Function.Surjective qJ ∧ qJ.ker = zpowers t ∧
      ∀ (v : L) (g : ruP), q v = g * ruAEl * g⁻¹ → ∃ h : J ruVec, qJ v = h * a ruVec * h⁻¹ := by
  obtain ⟨e, he⟩ := exists_equiv_ruP_J
  refine ⟨MonoidHom.comp (MulEquiv.toMonoidHom e) q, e.surjective.comp hq, ?_, fun v g hv => ?_⟩
  · rw [← hker]
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    exact map_eq_one_iff _ e.injective
  · refine ⟨e g, ?_⟩
    show e (q v) = _
    rw [hv, map_mul, map_mul, map_inv, he]

theorem ru_lift_sq
    {L : Type} [Group L] [Finite L] [Group.IsPerfect L]
    {q : L →* ruP} (hq : Function.Surjective q) {t : L} (ht : orderOf t = 2)
    (hker : q.ker = zpowers t) (hcen : zpowers t ≤ center L) :
    ∀ (v : L) (g : ruP), q v = g * ruAEl * g⁻¹ → v ^ 2 = t := by
  intro v g hv
  obtain ⟨qJ, hqJ, hkerJ, hconj⟩ := exists_cover_J hq hker
  obtain ⟨h, hh⟩ := hconj v g hv
  exact sq_eq_of_lift_conj_a Certificates.certificate15024
    Certificates.certificate15025 Certificates.certificate15026 qJ hqJ ht hkerJ hcen hh

set_option maxRecDepth 20000 in
theorem ru_fourthPowerDichotomy
    {L : Type} [Group L] [Finite L] [Group.IsPerfect L] {q : L →* ruP}
    (hq : Function.Surjective q) {t : L} (ht : orderOf t = 2) (hker : q.ker = zpowers t)
    (hcen : zpowers t ≤ center L) : FourthPowerDichotomy L t := by
  have hTab : RuTabFact := Certificates.certificate15024
  have hRho : ruRhoCheck = true := Certificates.certificate15025
  have hL0 := Certificates.certificate15026
  have : IsSimpleGroup ruP := isSimpleGroup_ruP
  obtain ⟨qJ, hqJ, hkerJ, -⟩ := exists_cover_J hq hker
  have hkerc : qJ.ker ≤ center L := hkerJ ▸ hcen
  obtain ⟨hfin, hle⟩ := card_ruCover_le hTab hL0
  have hcardL : Nat.card L = 291852288000 := by
    rw [qJ.ker.card_eq_card_quotient_mul_card_subgroup,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hqJ).toEquiv,
      CFSG.Sporadic.Bridge.Ru.card_J, hkerJ, Nat.card_zpowers, ht]
  obtain ⟨φ, hφ, hcomp⟩ := CFSG.Sporadic.Recognition.CoverTransfer.exists_bijective_of_card_le
    isPresentation_ruGen ruCommW_mem_commutator (lift_ruCommW hTab) qJ hqJ hkerc (hcardL ▸ hle)
  let e : RuCover ≃* L := MulEquiv.ofBijective φ hφ
  let ρ : RuCover →* Equiv.Perm (Fin 16240) := ruRho' hRho
  let ψ : L →* Equiv.Perm (Fin 16240) := ρ.comp e.symm.toMonoidHom
  have hψe : ∀ x, ψ (φ x) = ρ x := fun x => by
    show ρ (e.symm (e x)) = ρ x
    rw [MulEquiv.symm_apply_apply]
  obtain ⟨hρz, ⟨h8₁, h4₁, hz₁, hf₁⟩, ⟨h8₂, h4₂, hz₂, hf₂⟩⟩ := ruFourth_facts
  have hzP : ruWE ruZWord = ruP0E ^ 2 := by
    rw [pow_two, ruZWord, ruWE_append]
    rfl
  have hzP1 : ruWE ruZWord ≠ 1 := by rw [hzP]; exact ruP0E_sq_ne_one hRho
  have hzPker : ruπ hTab (ruWE ruZWord) = 1 := by rw [hzP, map_pow, ruπ_ruP0E, a_sq]
  have hφz : φ (ruWE ruZWord) = t := by
    have hmem : φ (ruWE ruZWord) ∈ qJ.ker := by
      rw [MonoidHom.mem_ker, ← MonoidHom.comp_apply, hcomp]
      exact hzPker
    rw [hkerJ] at hmem
    rcases eq_one_or_eq_of_mem_zpowers ht hmem with h1 | h1
    · exact absurd (hφ.1 (h1.trans (map_one φ).symm)) hzP1
    · exact h1
  have hψt : ψ t = ρ (ruWE ruZWord) := by rw [← hφz, hψe]
  have hψinj : Function.Injective ψ :=
    injective_of_ker_zpowers hq ht hker ψ (by rw [hψt]; exact hρz)
  set a₁ : L := φ (ruWE ruFourthW1) with ha₁
  set a₂ : L := φ (ruWE ruFourthW2) with ha₂
  have hψa₁ : ψ a₁ = ρ (ruWE ruFourthW1) := hψe _
  have hψa₂ : ψ a₂ = ρ (ruWE ruFourthW2) := hψe _
  have h₁ : a₁ ^ 8 = 1 := hψinj (by rw [map_pow, hψa₁, map_one]; exact h8₁)
  have h₂ : a₂ ^ 8 = 1 := hψinj (by rw [map_pow, hψa₂, map_one]; exact h8₂)
  have h₁' : a₁ ^ 4 ≠ 1 := fun h => h4₁ (by
    have := congrArg ψ h
    rwa [map_pow, hψa₁, map_one] at this)
  have h₂' : a₂ ^ 4 ≠ 1 := fun h => h4₂ (by
    have := congrArg ψ h
    rwa [map_pow, hψa₂, map_one] at this)
  have h₁t : a₁ ^ 4 ≠ t := fun h => hz₁ (by
    have := congrArg ψ h
    rwa [map_pow, hψa₁, hψt] at this)
  have h₂t : a₂ ^ 4 ≠ t := fun h => hz₂ (by
    have := congrArg ψ h
    rwa [map_pow, hψa₂, hψt] at this)
  have hnc : ¬ IsConj (a₁ ^ 4) (a₂ ^ 4) := by
    intro hc
    obtain ⟨c, hc⟩ := isConj_iff.1 hc
    have h := congrArg ψ hc
    rw [map_mul, map_mul, map_inv, map_pow, map_pow, hψa₁, hψa₂] at h
    have h' := ncard_fixSet_conj (ψ c) (ρ (ruWE ruFourthW1) ^ 4)
    rw [h, hf₂, hf₁] at h'
    exact absurd h' (by norm_num)
  exact fourthPowerDichotomy_of_facts hq ht hker hcen twoAClass
    (ru_lift_sq hq ht hker hcen) (fun w hw4 hw2 g => not_sq_conj_a hw4 hw2 g)
    (fun s hs2 hs1 => involution_dichotomy hs2 hs1)
    (fun s hs s' hs' => twoAClass_conj hs hs') h₁ h₂ h₁' h₂' h₁t h₂t hnc

end CFSG.EvenSporadicStandard.TwoRu
