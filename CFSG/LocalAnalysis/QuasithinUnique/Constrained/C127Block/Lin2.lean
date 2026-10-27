module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127MAut
import CFSG.CharacterTheory.Burnside
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank
open scoped commutatorElement

namespace L246C127

namespace C127Block

open MAut

variable {G : Type} [Group G] [Finite G]

private theorem isSolvable_of_card_six {A : Type*} [Group A] [Finite A] (h : Nat.card A = 6) :
    Group.IsSolvable A := by
  have := Fintype.ofFinite A
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 1) (b := 1)
    Nat.prime_two Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, h]; norm_num)

theorem natural_realizes_injective {V : Type} [CommGroup V] {K' : Type} [Field K']
    {H : Subgroup (MulAut V)} {U Z : Subgroup V} {π : ↥(StatedSL 2 K') →* ↥H}
    (h : (FFModel.nat (StatedSL 2 K')).RealizesVia H U Z π) : Function.Injective π := by
  obtain ⟨hπsurj, hZU, hkerU, hUinv, hZinv, hsecinv, hkerinv, β, hβsurj, hβker, hβeq⟩ := h
  rw [injective_iff_map_eq_one]
  intro γ hγ
  have hact : ∀ x : Multiplicative (Fin 2 → K'), natAct (StatedSL 2 K') γ x = x := by
    intro x
    obtain ⟨u, hu⟩ := hβsurj (QuotientGroup.mk (⟨x, Subgroup.mem_top x⟩ :
      ↥(FFModel.nat (StatedSL 2 K')).sec))
    have hu' : ((π γ : ↥H) : MulAut V) (u : V) ∈ U := hUinv (π γ) u u.2
    have key := hβeq γ u ⟨x, Subgroup.mem_top x⟩ hu' (Subgroup.mem_top _) hu
    have hπ1 : (⟨((π γ : ↥H) : MulAut V) (u : V), hu'⟩ : ↥U) = u := by
      apply Subtype.ext
      simp [hγ]
    have key' : β u = (QuotientGroup.mk (⟨natAct (StatedSL 2 K') γ x, Subgroup.mem_top _⟩ :
        ↥(FFModel.nat (StatedSL 2 K')).sec) :
        ↥(FFModel.nat (StatedSL 2 K')).sec ⧸ (FFModel.nat (StatedSL 2 K')).ker.subgroupOf
          (FFModel.nat (StatedSL 2 K')).sec) := by
      rw [← hπ1]
      exact key
    rw [hu] at key'
    have key2 := QuotientGroup.eq.1 key'
    rw [Subgroup.mem_subgroupOf] at key2
    have key3 : x⁻¹ * natAct (StatedSL 2 K') γ x = 1 := by
      have h := Subgroup.mem_bot.1 key2
      exact h
    exact (inv_mul_eq_one.1 key3).symm
  apply Subtype.ext
  apply Units.ext
  ext i j
  have h1 := hact (Multiplicative.ofAdd (Pi.single j 1))
  have h2 := congrFun (congrArg Multiplicative.toAdd h1) i
  simp [natAct, Matrix.mulVec_single_one] at h2
  simpa [Matrix.one_apply, Pi.single_apply] using h2

theorem isSolvable_statedSL_of_card_two {K' : Type} [Field K'] [Finite K'] (h : Nat.card K' = 2) :
    Group.IsSolvable ↥(StatedSL 2 K') := by
  have hc : Nat.card ↥(StatedSL 2 K') = 6 := by
    rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 2 K').toEquiv,
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, h]
    norm_num
  haveI : Finite ↥(StatedSL 2 K') :=
    Finite.of_equiv _ (specialLinearGroupEquivStatedSL 2 K').toEquiv
  exact isSolvable_of_card_six hc

theorem isLin2Type_of_natural_shape {V K : Subgroup G} (hV : IsElemAbelian 2 V)
    (hKN : K ≤ Subgroup.normalizer (V : Set G)) (hshort : IsShort2 K) (hUV : blockU K ≤ V)
    (hVK : ⁅V, K⁆ ≤ blockU K) (hker : (toAutI hV K hKN).ker = CFSG.pCore 2 ↥K)
    (hq : CFSG.IsQuasisimple ↥(autI hV K)) {e : ℕ} (he : 1 ≤ e)
    (hnat : BinaryNaturalSL (autI hV K) (commV (autI hV K))
      (commV (autI hV K) ⊓ fixV (autI hV K)) 2 e) :
    ∃ n : ℕ, 1 < n ∧ IsLin2Type K n := by
  obtain ⟨K', iF, iFin, hcard, π, hπsurj, hZU, hkerU, hUinv, hZinv, hsecinv, hkerinv, β, hβsurj,
    hβker, hβeq⟩ := hnat
  have hreal : (FFModel.nat (StatedSL 2 K')).RealizesVia (autI hV K) (commV (autI hV K))
      (commV (autI hV K) ⊓ fixV (autI hV K)) π :=
    ⟨hπsurj, hZU, hkerU, hUinv, hZinv, hsecinv, hkerinv, β, hβsurj, hβker, hβeq⟩
  have hinj := natural_realizes_injective hreal
  have he2 : 2 ≤ e := by
    by_contra hlt
    have he1 : e = 1 := by omega
    subst he1
    have hK2 : Nat.card K' = 2 := by simpa using hcard
    have hs : Group.IsSolvable ↥(StatedSL 2 K') := isSolvable_statedSL_of_card_two hK2
    have hsL : Group.IsSolvable ↥(autI hV K) := by
      haveI : Group.IsSolvable (FFModel.nat (StatedSL 2 K')).Gam := hs
      exact Group.isSolvable_of_surjective hπsurj
    haveI : Nontrivial ↥(autI hV K) := CFSG.LocalCores.isQuasisimple_nontrivial hq
    haveI : Group.IsPerfect ↥(autI hV K) := hq.1
    exact Group.IsPerfect.not_isSolvable (autI hV K) hsL
  refine ⟨e, he2, ?_⟩
  letI : Fintype K' := Fintype.ofFinite K'
  let D := FFModel.nat (StatedSL 2 K')
  have hkerle : D.ker.subgroupOf D.sec ≤ (D.sec.subtype).ker := by
    intro a ha
    rw [MonoidHom.mem_ker]
    have h1 : (a : D.Amb) ∈ D.ker := Subgroup.mem_subgroupOf.1 ha
    have hb : D.ker = ⊥ := rfl
    rw [hb] at h1
    exact Subgroup.mem_bot.1 h1
  let ιh : (↥D.sec ⧸ D.ker.subgroupOf D.sec) →* D.Amb :=
    QuotientGroup.lift _ D.sec.subtype hkerle
  have hιinj : Function.Injective ιh := by
    intro a b hab
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    have hab' : (a' : D.Amb) = (b' : D.Amb) := hab
    exact congrArg QuotientGroup.mk (Subtype.ext hab')
  have hιsurj : Function.Surjective ιh := by
    intro x
    exact ⟨QuotientGroup.mk (⟨x, Subgroup.mem_top x⟩ : ↥D.sec), rfl⟩
  let β' : ↥(commV (autI hV K)) →* Multiplicative (Fin 2 → K') := ιh.comp β
  let eqv : ↥(StatedSL 2 K') ≃* ↥(autI hV K) := MulEquiv.ofBijective π ⟨hinj, hπsurj⟩
  let eSL : ↥(autI hV K) ≃* Matrix.SpecialLinearGroup (Fin 2) K' :=
    eqv.symm.trans (specialLinearGroupEquivStatedSL 2 K').symm
  have hnat' : E2.IsL2Natural (autI hV K) (fixV (autI hV K)) e := by
    refine ⟨he, K', iF, inferInstance, ?_, eSL, β', ?_, ?_, ?_⟩
    · rw [← Nat.card_eq_fintype_card]
      exact hcard
    · exact hιsurj.comp hβsurj
    · ext u
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro h1
        have h2 : β u = 1 := hιinj (by rw [map_one]; exact h1)
        exact (hβker u).1 h2
      · intro h1
        have h2 := (hβker u).2 h1
        show ιh (β u) = 1
        rw [h2, map_one]
    · intro h u hu
      obtain ⟨γ, rfl⟩ := hπsurj h
      obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u)
      have hmem : D.act γ (m : D.Amb) ∈ D.sec := Subgroup.mem_top _
      have key := hβeq γ u m hu hmem hm.symm
      have e1 : β' u = (m : D.Amb) := by
        show ιh (β u) = _
        rw [← hm]
        rfl
      have e2 : β' ⟨((π γ : ↥(autI hV K)) : MulAut (IntMod V hV)) (u : IntMod V hV), hu⟩ =
          D.act γ (m : D.Amb) := by
        show ιh (β _) = _
        rw [key]
        rfl
      let γ' : ↥(StatedSL 2 K') := γ
      have hsymm : eqv.symm (π γ) = γ' := eqv.symm_apply_apply γ'
      have hcoe : ((eSL (π γ) : Matrix.SpecialLinearGroup (Fin 2) K') :
          Matrix (Fin 2) (Fin 2) K') = ((γ' : GL (Fin 2) K') : Matrix (Fin 2) (Fin 2) K') := by
        show (((specialLinearGroupEquivStatedSL 2 K').symm (eqv.symm (π γ)) :
          Matrix.SpecialLinearGroup (Fin 2) K') : Matrix (Fin 2) (Fin 2) K') = _
        rw [hsymm]
        have h2 := specialLinearGroupEquivStatedSL_coe 2 K'
          ((specialLinearGroupEquivStatedSL 2 K').symm γ')
        rw [MulEquiv.apply_symm_apply] at h2
        exact h2.symm
      show Multiplicative.toAdd (β' _) = _
      rw [e2, e1, hcoe]
      rfl
  have hC : ∀ u : ↥(blockU K), iotaU hV hUV u ∈ fixV (autI hV K) ↔ (u : G) ∈ blockZ K := by
    intro u
    rw [mem_fixV_autI hV hKN, iotaU_val]
    constructor
    · intro h1
      exact Subgroup.mem_inf.2 ⟨u.2, h1⟩
    · intro h1
      exact (Subgroup.mem_inf.1 h1).2
  exact MAut.isLin2Type_of_natural hV hKN hshort hUV hVK hker hC hnat'

end C127Block

end L246C127

end CFSG.QuasithinUnique
