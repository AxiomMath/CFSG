module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzHyp31A
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzDBridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzOuterSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzOuterReduce
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.OddCentralFacts
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Sporadic.SuzOddCore CFSG.ComponentClassification.PerfectAutomorphisms Cover
  CFSG.ComponentClassification.PSL3Four CFSG.EvenSporadicStandard.SuzOuter
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section SFacts


theorem card_involutions_S : 315 ≤ Nat.card {t : ↥S // t * t = 1 ∧ t ≠ 1} := by
  obtain ⟨-, -, -, -, -, hord, -, h315, -, -, -, hmem, -⟩ := involution_enumeration
  rw [← h315]
  have hinv : ∀ x : (ConjClasses.mk r₁R).carrier,
      orderOf (x.1 : ↥R) = 2 ∧ IsConj x.1 r₁R := by
    intro x
    have hx : ConjClasses.mk x.1 = ConjClasses.mk r₁R := ConjClasses.mem_carrier_iff_mk_eq.1 x.2
    have hc : IsConj x.1 r₁R := ConjClasses.mk_eq_mk_iff_isConj.1 hx
    exact ⟨(hord x.1).2 (Or.inl hc), hc⟩
  refine Nat.card_le_card_of_injective
    (fun x : (ConjClasses.mk r₁R).carrier =>
      (⟨⟨(x.1 : Equiv.Perm (Fin 42)), hmem x.1 (hinv x).2⟩, ?_, ?_⟩ :
        {t : ↥S // t * t = 1 ∧ t ≠ 1})) ?_
  · apply Subtype.ext
    have h2 : x.1 * x.1 = 1 := by
      have := pow_orderOf_eq_one x.1
      rwa [(hinv x).1, pow_two] at this
    simpa using congrArg Subtype.val h2
  · intro h
    have h1 : x.1 = 1 := Subtype.ext (by simpa using congrArg Subtype.val h)
    have := (hinv x).1
    rw [h1, orderOf_one] at this
    omega
  · intro a b hab
    have := congrArg (fun z : {t : ↥S // t * t = 1 ∧ t ≠ 1} => (z.1 : Equiv.Perm (Fin 42))) hab
    exact Subtype.ext (Subtype.ext this)

theorem card_centralizer_involution_S' :
    ∀ t : ↥S, t * t = 1 → t ≠ 1 → Nat.card (centralizer ({t} : Set ↥S)) = 64 := by
  intro t ht ht1
  exact (facts_of_equiv_S.{0, 0} (MulEquiv.refl ↥S)).2.1 t
    (orderOf_eq_prime (by rw [pow_two]; exact ht) ht1)

end SFacts

section Main


theorem suzOuterNoLink_proved : SuzOuterNoLink := by
  intro H _ _ L K hL hKL hKq hKs σ hσ hfix
  have hLperf : Group.IsPerfect ↥L := hL.1.1
  by_cases hinn : ∃ g : ↥L, σ = MulAut.conj g
  · exact hinn
  exfalso
  have σbdef : centerQuotientHom ↥L σ = onCenterQuotient σ := rfl
  set σb := centerQuotientHom ↥L σ with hσb
  have hσb2 : σb * σb = 1 := by rw [hσb, ← map_mul, hσ, map_one]
  have hσbout : σb ∉ (MulAut.conj : (↥L ⧸ center ↥L) →* MulAut (↥L ⧸ center ↥L)).range := by
    rintro ⟨y, hy⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    refine hinn ⟨g, centerQuotientHom_injective ↥L ?_⟩
    rw [CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_conj]
    exact hy.symm
  have hσb1 : σb ≠ 1 := fun h => hσbout ⟨1, by rw [map_one, h]⟩
  have hord : orderOf σb = 2 := orderOf_eq_prime (by rw [pow_two]; exact hσb2) hσb1
  obtain ⟨e⟩ := hL.2.2
  have hKodd : Odd (Nat.card (center ↥K)) := odd_center_of_isKSuz_quot hKq hKs
  obtain ⟨e₁⟩ := cq_equiv_of_isKSuz_quot hKq hKs
  obtain ⟨e₂⟩ := CFSG.ComponentClassification.CatFactsSmall.nonempty_equiv_psl34_of_lieModel
    suzD_lieModel
  let eS : (↥K ⧸ center ↥K) ≃* ↥S := e₁.trans e₂
  have hScard : Nat.card ↥S = 20160 := card_S
  let ψ : ↥K →* (↥L ⧸ center ↥L) := (q ↥L).comp (Subgroup.inclusion hKL)
  have hψfix : ∀ k : ↥K, σb (ψ k) = ψ k := by
    intro k
    show onCenterQuotient σ (q ↥L (Subgroup.inclusion hKL k)) = q ↥L (Subgroup.inclusion hKL k)
    rw [q_apply, ← QuotientGroup.mk'_apply, onCenterQuotient_apply_mk]
    have := hfix (Subgroup.inclusion hKL k) k.2
    rw [this]
  have hψker : ψ.ker ≤ center ↥K := by
    intro k hk
    have hk' : q ↥L (Subgroup.inclusion hKL k) = 1 := hk
    rw [q_eq_one_iff] at hk'
    rw [Subgroup.mem_center_iff]
    intro x
    have h2 : ((x * k : ↥K) : H) = ((k * x : ↥K) : H) := by
      have := Subgroup.mem_center_iff.1 hk' (Subgroup.inclusion hKL x)
      exact congrArg (fun z : ↥L => (z : H)) this
    exact Subtype.ext h2
  let ψ' : ↥K →* fixedSubgroup σb :=
    ψ.codRestrict (fixedSubgroup σb) (fun k => hψfix k)
  have hψ'ker : ψ'.ker ≤ center ↥K := by
    intro k hk
    apply hψker
    rw [MonoidHom.mem_ker] at hk ⊢
    exact congrArg Subtype.val hk
  rcases suz_outer_fixedSubgroup_equiv e hord hσbout with hι | hι
  ·
    obtain ⟨ι⟩ := hι
    let Ψ : ↥K →* ↥(centM (suzInv 2)) := ι.toMonoidHom.comp ψ'
    have hker : Ψ.ker ≤ center ↥K := by
      intro k hk
      apply hψ'ker
      rw [MonoidHom.mem_ker] at hk ⊢
      exact ι.injective (by rw [map_one]; exact hk)
    obtain ⟨-, -, -, h7⟩ := facts_of_cover eS hKodd hScard card_involutions_S
      card_centralizer_involution_S' Ψ hker
    have hcard : Nat.card ↥(centM (suzInv 2)) = 190080 := by
      rw [← invE_eq_centM (by norm_num : 2 < 4)]
      simpa [invInnerOrders] using card_invE (i := 2) (by norm_num)
    have hdvd : Nat.card ↥Ψ.range ∣ Nat.card ↥(centM (suzInv 2)) :=
      Subgroup.card_subgroup_dvd_card _
    rw [hcard] at hdvd
    exact absurd (h7.trans hdvd) (by norm_num)
  ·
    obtain ⟨ι⟩ := hι
    let Ψ : ↥K →* Equiv.Perm (Fin 1782) :=
      (centM (suzInv 3)).subtype.comp (ι.toMonoidHom.comp ψ')
    have hker : Ψ.ker ≤ center ↥K := by
      intro k hk
      apply hψ'ker
      rw [MonoidHom.mem_ker] at hk ⊢
      have h1 : ι (ψ' k) = 1 := Subtype.ext hk
      exact ι.injective (by rw [h1, map_one])
    obtain ⟨hcount, hcent, h128, -⟩ := facts_of_cover eS hKodd hScard card_involutions_S
      card_centralizer_involution_S' Ψ hker
    have hle : Ψ.range ≤ CC := by
      rintro _ ⟨k, rfl⟩
      have heq : centM (suzInv 3) = CC := (invE_eq_centM (by norm_num : 3 < 4)).symm
      exact heq.le (ι (ψ' k)).2
    exact no_group_in_invE3 Ψ.range hle hcount hcent h128

end Main

end CFSG.EvenSporadicStandard.Induction
