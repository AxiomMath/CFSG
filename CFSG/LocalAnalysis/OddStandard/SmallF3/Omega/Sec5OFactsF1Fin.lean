module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OFactsF1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OFactsF1Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeZ2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem u43OddAutTwoPlusCent_of (hOut : U43OuterOdd) (hCent : U43CentTwoPlus) :
    U43OddAutTwoPlusCent := by
  intro X _ _ hq htwo Q₁ Q₂ hQ₁ hQ₂ hcomm hcard hcent α hodd hfix x
  let O : Subgroup X := oddCore X
  haveI : O.Normal := by simpa [O] using oddCore_normal X
  let U := X ⧸ O
  let mk : X →* U := QuotientGroup.mk' O
  have hmapα : O.map α.toMonoidHom = O := by
    change (CFSG.Open.componentClassificationOddCore X).map α.toMonoidHom =
      CFSG.Open.componentClassificationOddCore X
    exact CFSG.ComponentClassification.OddCore.char_invariant α
  let Φ : MulAut X →* MulAut U :=
    { toFun := fun β => QuotientGroup.congr O O β (by
        change (CFSG.Open.componentClassificationOddCore X).map β.toMonoidHom =
          CFSG.Open.componentClassificationOddCore X
        exact CFSG.ComponentClassification.OddCore.char_invariant β)
      map_one' := by
        ext y
        induction y using QuotientGroup.induction_on
        rfl
      map_mul' := by
        intro β γ
        ext y
        induction y using QuotientGroup.induction_on
        rfl }
  let ᾱ : MulAut U := QuotientGroup.congr O O α hmapα
  have hOZ : O ≤ Subgroup.center X := by
    simpa [O] using CFSG.EvenSporadicStandard.Induction.oddCore_le_center_of_isQuasisimple hq
  have hαmk : ∀ y : X, ᾱ (mk y) = mk (α y) := by
    intro y
    simpa [mk, ᾱ, O, U] using QuotientGroup.congr_mk O O α hmapα y
  have hdvdα : orderOf ᾱ ∣ orderOf α := by
    simpa [ᾱ, Φ] using orderOf_map_dvd Φ α
  have hoddα : Odd (orderOf ᾱ) := hodd.of_dvd_nat hdvdα
  have hqU : IsQuasisimple U := by
    simpa [U, O] using isQuasisimple_quotient_oddCore hq
  let Qbar₁ : Subgroup U := Q₁.map mk
  let Qbar₂ : Subgroup U := Q₂.map mk
  have hQ₁O : Q₁ ⊓ O = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    have hzsup : z ∈ (Q₁ ⊔ Q₂) ⊓ Subgroup.center X :=
      ⟨Subgroup.mem_sup_left hz.1, hOZ hz.2⟩
    rw [hcent] at hzsup
    exact hzsup
  have hQ₂O : Q₂ ⊓ O = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    have hzsup : z ∈ (Q₁ ⊔ Q₂) ⊓ Subgroup.center X :=
      ⟨Subgroup.mem_sup_right hz.1, hOZ hz.2⟩
    rw [hcent] at hzsup
    exact hzsup
  have hQO : (Q₁ ⊔ Q₂) ⊓ O = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    have hzsup : z ∈ (Q₁ ⊔ Q₂) ⊓ Subgroup.center X := ⟨hz.1, hOZ hz.2⟩
    rw [hcent] at hzsup
    exact hzsup
  have hinj_mk {Q : Subgroup X} (hQO : Q ⊓ O = ⊥) :
      Function.Injective (mk.subgroupMap Q) := by
    intro a b hab
    have hab' : mk (a : X) = mk (b : X) := congrArg Subtype.val hab
    have hdiv : (a : X) / (b : X) ∈ O := QuotientGroup.eq_iff_div_mem.mp hab'
    have hdivQ : (a : X) / (b : X) ∈ Q := Q.div_mem a.2 b.2
    have hbot : (a : X) / (b : X) ∈ (⊥ : Subgroup X) := by
      rw [← hQO]
      exact ⟨hdivQ, hdiv⟩
    have h1 : (a : X) / (b : X) = 1 := Subgroup.mem_bot.mp hbot
    exact Subtype.ext (div_eq_one.mp h1)
  have hinjQ₁ := hinj_mk hQ₁O
  have hinjQ₂ := hinj_mk hQ₂O
  have hinjQ := hinj_mk hQO
  have hQbar₁ : Nonempty (↥Qbar₁ ≃* QuaternionGroup 2) := by
    obtain ⟨e⟩ := hQ₁
    exact ⟨(MulEquiv.ofBijective (mk.subgroupMap Q₁)
      ⟨hinjQ₁, mk.subgroupMap_surjective Q₁⟩).symm.trans e⟩
  have hQbar₂ : Nonempty (↥Qbar₂ ≃* QuaternionGroup 2) := by
    obtain ⟨e⟩ := hQ₂
    exact ⟨(MulEquiv.ofBijective (mk.subgroupMap Q₂)
      ⟨hinjQ₂, mk.subgroupMap_surjective Q₂⟩).symm.trans e⟩
  have hsup_eq : Qbar₁ ⊔ Qbar₂ = (Q₁ ⊔ Q₂).map mk := by
    simpa [Qbar₁, Qbar₂] using (Subgroup.map_sup Q₁ Q₂ mk).symm
  have hcommbar : ⁅Qbar₁, Qbar₂⁆ = ⊥ := by
    rw [← Subgroup.map_commutator Q₁ Q₂ mk, hcomm, Subgroup.map_bot]
  have hcardbar : Nat.card ↥(Qbar₁ ⊔ Qbar₂) = 32 := by
    have hcardmap : Nat.card ↥((Q₁ ⊔ Q₂).map mk) = Nat.card ↥(Q₁ ⊔ Q₂) := by
      exact (Nat.card_congr (MulEquiv.ofBijective (mk.subgroupMap (Q₁ ⊔ Q₂))
        ⟨hinjQ, mk.subgroupMap_surjective (Q₁ ⊔ Q₂)⟩).toEquiv).symm
    rw [hsup_eq, hcardmap, hcard]
  haveI : Group.IsPerfect X := hq.1
  have hcenter_map : (Subgroup.center X).map mk = Subgroup.center U := by
    exact CFSG.ComponentClassification.Quasisimple.center_map_of_central_kernel mk
      (QuotientGroup.mk'_surjective O)
      (by
        rw [show mk.ker = O from QuotientGroup.ker_mk' O]
        exact hOZ)
  have hcenter_bar : (Qbar₁ ⊔ Qbar₂) ⊓ Subgroup.center U = ⊥ := by
    rw [hsup_eq, ← hcenter_map, Subgroup.eq_bot_iff_forall]
    intro y hy
    obtain ⟨hyQ, hyC⟩ := Subgroup.mem_inf.mp hy
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hyQ
    obtain ⟨c, hc, hcq⟩ := Subgroup.mem_map.mp hyC
    have hqC : q ∈ Subgroup.center X := by
      have hdiv : q / c ∈ O := QuotientGroup.eq_iff_div_mem.mp hcq.symm
      have hqeq : q = (q / c) * c := (div_mul_cancel q c).symm
      rw [hqeq]
      exact (Subgroup.center X).mul_mem (hOZ hdiv) hc
    have hqbot : q ∈ (Q₁ ⊔ Q₂) ⊓ Subgroup.center X := ⟨hq, hqC⟩
    rw [hcent] at hqbot
    rw [Subgroup.mem_bot.mp hqbot, map_one]
  have hcentU : IsPGroup 2 (Subgroup.centralizer ((Qbar₁ ⊔ Qbar₂ : Subgroup U) : Set U)) :=
    hCent U hqU (by simpa [U, O] using htwo) Qbar₁ Qbar₂ hQbar₁ hQbar₂ hcommbar hcardbar hcenter_bar
  obtain ⟨u, hu⟩ := hOut U hqU (by simpa [U, O] using htwo) ᾱ hoddα
  have hfixbar : ∀ q ∈ Qbar₁ ⊔ Qbar₂, ᾱ q = q := by
    intro q hq
    rw [hsup_eq] at hq
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hq
    rw [hαmk y, hfix y hy]
  have hu_cent : u ∈ Subgroup.centralizer ((Qbar₁ ⊔ Qbar₂ : Subgroup U) : Set U) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hqfix := hfixbar q hq
    rw [hu, MulAut.conj_apply] at hqfix
    calc q * u = (u * q * u⁻¹) * u := by rw [hqfix]
      _ = u * q := by group
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hcentU) ⟨u, hu_cent⟩
  have hk' : orderOf u = 2 ^ k := by
    simpa using hk
  have hdvd_conj : orderOf (MulAut.conj u) ∣ 2 ^ k := by
    rw [← hk']
    exact orderOf_map_dvd (MulAut.conj : U →* MulAut U) u
  have hoddConj : Odd (orderOf (MulAut.conj u)) := by
    rw [← hu]
    exact hoddα
  have hone : orderOf (MulAut.conj u) = 1 := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd_conj
    have hoddj : Odd (2 ^ j) := hj ▸ hoddConj
    have hj0 : j = 0 := by
      cases j with
      | zero => rfl
      | succ j =>
          exfalso
          have heven : Even (2 ^ (j + 1)) := ⟨2 ^ j, by rw [pow_succ']; ring⟩
          exact (Nat.not_even_iff_odd.mpr hoddj) heven
    rw [hj, hj0, pow_zero]
  have hᾱ1 : ᾱ = 1 := hu.trans (orderOf_eq_one_iff.mp hone)
  calc QuotientGroup.mk (s := oddCore X) (α x)
      = ᾱ (QuotientGroup.mk (s := oddCore X) x) := by
        simpa [mk, O, U] using (hαmk x).symm
    _ = QuotientGroup.mk (s := oddCore X) x := by rw [hᾱ1]; rfl


end CFSG.OddStandard.SmallF3.Omega
