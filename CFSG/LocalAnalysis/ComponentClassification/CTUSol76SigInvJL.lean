module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigL39Bal
public import CFSG.LocalAnalysis.ComponentClassification.TBLitL34PTriv
public import CFSG.Sporadic.Schreier.J1Outer
public import CFSG.Sporadic.Schreier.J1OddCore

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

section General

variable {L : Type} [Group L] [Finite L]

theorem involutionOddCore_one_eq_bot_of_simple [IsSimpleGroup L] (heven : Even (Nat.card L)) :
    Assembly.Dichotomy.involutionOddCore (1 : L) = ⊥ := by
  set O := Assembly.Dichotomy.involutionOddCore (1 : L) with hO
  have hOn : O.Normal := ⟨fun y hy g => ClassicalInvolution.Balance.conj_mem_involutionOddCore
    (mem_centralizer_singleton_iff.mpr (by rw [one_mul, mul_one])) hy⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal O with hb | ht
  · exact hb
  · exfalso
    have hOodd : Odd (Nat.card O) := by
      rw [hO, ClassicalInvolution.Balance.involutionOddCore_eq_oddCoreCentralizer]
      exact ClassicalInvolution.Balance.odd_card_oddCoreCentralizer _
    rw [ht, Subgroup.card_top] at hOodd
    exact (Nat.not_even_iff_odd.mpr hOodd) heven

theorem center_eq_bot_of_simple_of_two_dvd [IsSimpleGroup L] (h2 : 2 ∣ Nat.card L)
    (hne : Nat.card L ≠ 2) : center L = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center L) with hb | ht
  · exact hb
  · exfalso
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hn : (zpowers g).Normal := ⟨fun n _ k => by
      have hk : k ∈ center L := ht ▸ mem_top k
      rwa [← mem_center_iff.mp hk n, mul_inv_cancel_right]⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (zpowers g) with hb | ht'
    · rw [zpowers_eq_bot] at hb
      rw [hb, orderOf_one] at hg
      norm_num at hg
    · have h1 := Nat.card_zpowers g
      rw [ht', Subgroup.card_top, hg] at h1
      exact hne h1

omit [Finite L] in
theorem exists_mul_ne_of_center_eq_bot [Nontrivial L] (hZ : center L = ⊥) :
    ∃ a b : L, a * b ≠ b * a := by
  by_contra h
  push Not at h
  obtain ⟨a, ha⟩ := exists_ne (1 : L)
  have : a ∈ center L := mem_center_iff.mpr fun b => h b a
  rw [hZ, mem_bot] at this
  exact ha this

theorem isInvolutionCoreFree_of_forall_inner (hZ : center L = ⊥)
    (hinner : ∀ φ : MulAut L, ∃ g : L, φ = MulAut.conj g)
    (hO : ∀ x : L, x * x = 1 → Assembly.Dichotomy.involutionOddCore x = ⊥) :
    IsInvolutionCoreFree L := by
  intro H hH x hx2
  have : Finite (MulAut L) := inferInstance
  have hinj := GrSLit.conj_injective_of_center_eq_bot hZ
  let ι : L →* H := (MulAut.conj : L →* MulAut L).codRestrict H fun l => hH ⟨l, rfl⟩
  have hιinj : Function.Injective ι := fun a b hab => hinj (congrArg Subtype.val hab)
  have hιsurj : Function.Surjective ι := fun h => by
    obtain ⟨g, hg⟩ := hinner h
    exact ⟨g, Subtype.ext hg.symm⟩
  let e : L ≃* H := MulEquiv.ofBijective ι ⟨hιinj, hιsurj⟩
  have hex : e x = ⟨MulAut.conj x, hH ⟨x, rfl⟩⟩ := rfl
  have ha2 : (⟨MulAut.conj x, hH ⟨x, rfl⟩⟩ : H) * ⟨MulAut.conj x, hH ⟨x, rfl⟩⟩ = 1 := by
    rw [← hex, ← map_mul, hx2, map_one]
  have hle := ClassicalInvolution.Balance.map_involutionOddCore_le e.symm.toMonoidHom
    e.symm.surjective (ClassicalInvolution.Balance.isPGroup_zpowers_of_mul_self_eq_one ha2)
  have h1 : e.symm.toMonoidHom ⟨MulAut.conj x, hH ⟨x, rfl⟩⟩ = x := by
    rw [← hex]
    exact e.symm_apply_apply x
  rw [h1, hO x hx2] at hle
  exact (map_eq_bot_iff_of_injective _ e.symm.injective).mp (le_bot_iff.mp hle)

end General

section J1

theorem isInvolutionCoreFree_J1 :
    IsInvolutionCoreFree Blueprint.NativeSporadic.J1 := by
  have hs := CFSG.Sporadic.J1.isSimpleGroup_J1
  have hcard := CFSG.Sporadic.J1.card_J1
  have : Finite Blueprint.NativeSporadic.J1 := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hZ : center Blueprint.NativeSporadic.J1 = ⊥ :=
    center_eq_bot_of_simple_of_two_dvd (by rw [hcard]; norm_num) (by rw [hcard]; norm_num)
  refine isInvolutionCoreFree_of_forall_inner hZ CFSG.Sporadic.Schreier.at_j1_schreier.2.1
    fun x hx2 => ?_
  by_cases hx1 : x = 1
  · subst hx1
    exact involutionOddCore_one_eq_bot_of_simple (by rw [hcard]; decide)
  · have hx : orderOf x = 2 := orderOf_eq_prime (by rw [sq, hx2]) hx1
    have h := (CFSG.Sporadic.Schreier.ctugs_j1_involution_centralizer_odd_core_free
      ⟨MulEquiv.refl _⟩ x hx).2.2.1
    rw [Assembly.Dichotomy.involutionOddCore, Assembly.Dichotomy.oddCore_eq_pPrimeCore, h,
      Subgroup.map_bot]

theorem isInvolutionCoreFree_of_mulEquiv_J1
    {L : Type} [Group L] [Finite L]
    (e : L ≃* ↥CFSG.Open.properTwoGenCoreJ1) : IsInvolutionCoreFree L :=
  isInvolutionCoreFree_of_mulEquiv (e.trans CFSG.ProperTwoGeneratedCore.j1_exact_model_equiv).symm
    isInvolutionCoreFree_J1

end J1

section L34

theorem isInvolutionCoreFree_of_psl34
    {L : Type} [Group L] [Finite L] (h : CFSG.Open.StatedClassicalModel L .PSL 3 2 2) :
    IsInvolutionCoreFree L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eS⟩ := nonempty_equiv_of_stated L h
  have hs : IsSimpleGroup L := @MulEquiv.isSimpleGroup _ _ _ _ TBLit.L34P.isSimpleGroup_S eS
  have hcard : Nat.card L = 20160 := (Nat.card_congr eS.toEquiv).trans card_S
  have hZ : center L = ⊥ :=
    center_eq_bot_of_simple_of_two_dvd (by rw [hcard]; norm_num) (by rw [hcard]; norm_num)
  have hnab : ∃ a b : L, a * b ≠ b * a := exists_mul_ne_of_center_eq_bot hZ
  intro H hH x hx2
  by_cases hx1 : x = 1
  · subst hx1
    refine involutionOddCore_eq_bot_of_rigidAt hZ
      (involutionOddCore_one_eq_bot_of_simple (by rw [hcard]; decide)) (fun β _ hβ => ?_) H hH
    exact MulEquiv.ext fun g => hβ g (mem_centralizer_singleton_iff.mpr (by rw [one_mul, mul_one]))
  · have hsF := GrSLit.isSimpleGroup_generalizedFitting hnab hH
    have hnabF := GrSLit.exists_mul_ne_generalizedFitting hnab hH
    obtain ⟨eF⟩ := GrSLit.nonempty_generalizedFitting_equiv hnab hH
    have hmodelL : Blueprint.LieModel L .PSL 3 2 2 := Or.inl ⟨by decide, h⟩
    have hmodel : Blueprint.LieModel (GeneralizedFitting.subgroup H) .PSL 3 2 2 :=
      LieType.CurtisTits.lieModel_of_mulEquiv eF.symm hmodelL
    obtain ⟨ψ, hinj, hR, hF, hS⟩ := GrSLit.exists_psl34Embedding hsF hnabF hmodel
    set a : H := ⟨MulAut.conj x, hH ⟨x, rfl⟩⟩ with ha
    have hinjc := GrSLit.conj_injective_of_center_eq_bot hZ
    have ha2 : orderOf a = 2 := by
      refine orderOf_eq_prime ?_ ?_
      · rw [sq]
        apply Subtype.ext
        show MulAut.conj x * MulAut.conj x = 1
        rw [← map_mul, hx2, map_one]
      · intro h1
        apply hx1
        apply hinjc
        rw [map_one]
        exact congrArg Subtype.val h1
    have haF : a ∈ GeneralizedFitting.subgroup H := by
      rw [GrSLit.generalizedFitting_eq_inn hnab hH]
      exact ⟨x, rfl⟩
    have hψa : ψ a ∈ S := (hF a).mp haF
    have hu : ¬ IsConj (⟨ψ a, hR a⟩ : R) r₄R := fun hc =>
      not_mem_S_of_isConj hc not_mem_S_r₄ hψa
    have h0 := GrSLit.pPrimeCore_eq_bot_of_not_unitary hinj hR hF hS ha2 hu
    rw [Assembly.Dichotomy.involutionOddCore, Assembly.Dichotomy.oddCore_eq_pPrimeCore, h0,
      Subgroup.map_bot]

end L34

@[expose] def InvolutionCoreFreeA9 : Prop :=
  ∀ (L : Type) [Group L] [Finite L], Nonempty (L ≃* alternatingGroup (Fin 9)) →
    IsInvolutionCoreFree L

theorem involutionCoreFreeJLA_of_A9
    (h : InvolutionCoreFreeA9) : InvolutionCoreFreeJLA := by
  intro L _ _ hL
  rcases hL with hJ | hL | hA
  · obtain ⟨e⟩ := hJ
    exact isInvolutionCoreFree_of_mulEquiv_J1 e
  · exact isInvolutionCoreFree_of_psl34 hL
  · exact h L hA

end CFSG.ComponentClassification.Sol76.Sig
