module

public import CFSG.CGT.PushingUpLit.BHS.TwoSixteenAlt
public import CFSG.CGT.PushingUpLit.BHS.ThreeNormalizer
public import CFSG.Quasithin.EmptyFaithful.S145Cop
public import CFSG.Quasithin.Background.D2Coprime

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.G6
open scoped commutatorElement

theorem card_coreMod_three' : Nat.card (coreMod 3) = 4 := by
  show Nat.card {x : PermMod 3 // ∑ i, Multiplicative.toAdd x i = 0} = 4
  rw [Nat.card_eq_fintype_card]
  decide +kernel

section ThreeWrap

variable {V : Type} [CommGroup V] [Finite V]

theorem three_facts (hV : ∀ v : V, v ^ 2 = 1) {E : Subgroup (MulAut V)} {W : Subgroup V}
    (hWE : commV E = W) (θ : E ≃* alternatingGroup (Fin 3)) (β : ↥W →* coreMod 3)
    (hβs : Function.Surjective β) (hβk : β.ker = (W ⊓ fixV E).subgroupOf W) :
    Nat.card E = 3 ∧ W ⊓ fixV E = ⊥ ∧ Nat.card ↥W = 4 := by
  have hEcard : Nat.card E = 3 := by
    rw [Nat.card_congr θ.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have hinf : W ⊓ fixV E = ⊥ := by
    have hodd : Odd (Nat.card E) := by
      rw [hEcard]
      decide
    have h := (isCompl_fixV_commV_of_odd E hodd hV).inf_eq_bot
    rw [← hWE, inf_comm]
    exact h
  have hβinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have h : w ∈ β.ker := hw
    rw [hβk, hinf, Subgroup.bot_subgroupOf] at h
    exact Subgroup.mem_bot.mp h
  refine ⟨hEcard, hinf, ?_⟩
  rw [Nat.card_congr (Equiv.ofBijective β ⟨hβinj, hβs⟩)]
  exact card_coreMod_three'

theorem two_sixteen_three_gen (hV : ∀ v : V, v ^ 2 = 1) {A E : Subgroup (MulAut V)}
    {W : Subgroup V} (hWE : commV E = W) (θ : E ≃* alternatingGroup (Fin 3))
    (β : ↥W →* coreMod 3) (hβs : Function.Surjective β)
    (hβk : β.ker = (W ⊓ fixV E).subgroupOf W)
    (hβe : ∀ (x : E) (p : ↥W) (hp : (x : MulAut V) p ∈ W),
      β ⟨(x : MulAut V) p, hp⟩ =
        coreAct 3 ((θ x : alternatingGroup (Fin 3)) : Equiv.Perm (Fin 3)) (β p))
    (hAN : A ≤ Subgroup.normalizer (E : Set (MulAut V))) (hAoff : IsOff A) (hEA : ⁅E, A⁆ ≠ ⊥) :
    W ⊓ fixV E = ⊥ ∧ Nat.card (autSub A W) = 2 ∧
      (∀ a ∈ A, ∀ a' ∈ A, ∀ w ∈ W, a' (a w * w⁻¹) = a w * w⁻¹) ∧
      (fixV A).relIndex W = (cenIn A W).relIndex A := by
  classical
  have hEst : E ≤ stabSub W := by
    rw [← hWE]
    exact Subgroup.le_normalizer.trans (normalizer_commV_le_stabSub E)
  have hAst : A ≤ stabSub W := by
    rw [← hWE]
    exact hAN.trans (normalizer_commV_le_stabSub E)
  obtain ⟨hEcard, hinf, hcardW⟩ := three_facts hV hWE θ β hβs hβk
  have hW' : ∀ w : ↥W, w ^ 2 = 1 := fun w => Subtype.ext (by
    rw [SubgroupClass.coe_pow]
    exact hV w)
  have hrk : rk ↥W = 2 := by
    have h := card_eq_two_pow_rk hW'
    rw [hcardW] at h
    have h2 : (2 : ℕ) ^ rk ↥W = 2 ^ 2 := by
      rw [← h]
      norm_num
    exact Nat.pow_right_injective le_rfl h2
  have hautcard : Nat.card (MulAut ↥W) = 6 := by
    rw [card_mulAut_eq hW', hrk]
    simp [Fin.prod_univ_two]
  have hEcen : E ⊓ centSub W = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun e he => ?_
    obtain ⟨heE, hecen⟩ := he
    have h1 : θ ⟨e, heE⟩ = 1 := by
      apply Subtype.ext
      apply coreAct_injective (le_refl 3)
      apply MulEquiv.ext
      intro d
      obtain ⟨p, rfl⟩ := hβs d
      have hp : (e : MulAut V) p ∈ W := by rw [hecen p p.2]; exact p.2
      have := hβe ⟨e, heE⟩ p hp
      have hp' : (⟨e p, hp⟩ : ↥W) = p := Subtype.ext (hecen p p.2)
      rw [hp'] at this
      exact this.symm
    have : (⟨e, heE⟩ : ↥E) = 1 := θ.injective (by rw [h1, map_one])
    exact congrArg Subtype.val this
  have hel : IsElemAbelian2 (autSub A W) := isElemAbelian2_autSub hAoff.2.2.1
  have hEA' : ⁅autSub E W, autSub A W⁆ ≠ ⊥ :=
    commutator_autSub_ne_bot hEst hAst hAN hEcen hEA
  have hAbar_ne : autSub A W ≠ ⊥ := by
    intro h
    apply hEA'
    rw [h]
    exact Subgroup.commutator_bot_right _
  have hcardA : Nat.card (autSub A W) = 2 := by
    have hdvd : Nat.card (autSub A W) ∣ 6 := hautcard ▸ Subgroup.card_subgroup_dvd_card _
    have hpow : Nat.card (autSub A W) = 2 ^ rk ↥(autSub A W) :=
      card_eq_two_pow_of_isPGroup hel.isPGroup
    have hne : Nat.card (autSub A W) ≠ 1 := fun h => hAbar_ne (Subgroup.card_eq_one.mp h)
    rw [hpow] at hdvd hne ⊢
    have hr : rk ↥(autSub A W) ≤ 2 := by
      by_contra hlt
      have h8 : 2 ^ 3 ≤ 2 ^ rk ↥(autSub A W) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega
    generalize rk ↥(autSub A W) = r at hr hdvd hne ⊢
    interval_cases r
    · exact absurd rfl hne
    · rfl
    · norm_num at hdvd
  have hcA : (cenIn A W).relIndex A = 2 := by
    rw [← card_autSub_eq_relIndex hAst]
    exact hcardA
  have hge : 2 ≤ (fixV A).relIndex W := by
    by_contra hlt
    push Not at hlt
    have hmul := Subgroup.relIndex_mul_card (fixV A) W
    have h1 : (fixV A).relIndex W = 1 := by
      rcases Nat.lt_or_ge ((fixV A).relIndex W) 1 with h0 | h0
      · have h0' : (fixV A).relIndex W = 0 := by omega
        rw [h0', zero_mul] at hmul
        omega
      · omega
    have hWle : W ≤ fixV A := Subgroup.relIndex_eq_one.mp h1
    apply hAbar_ne
    refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
    obtain ⟨g, hgA, rfl⟩ := mem_autSub.mp hx
    apply MulEquiv.ext
    intro w
    apply Subtype.ext
    exact hWle w.2 g hgA
  have hd : (fixV A).relIndex W = (cenIn A W).relIndex A := by
    have hle := offender_card_le hAoff W
    omega
  refine ⟨hinf, hcardA, ?_, hd⟩
  intro a ha a' ha' w hw
  by_cases h' : resHom W ⟨a', hAst ha'⟩ = 1
  · have hfix : ∀ x : ↥W, (resHom W ⟨a', hAst ha'⟩) x = x := fun x => by rw [h']; rfl
    have hx : a w * w⁻¹ ∈ W := W.mul_mem ((hAst ha w).2 hw) (W.inv_mem hw)
    have := hfix ⟨a w * w⁻¹, hx⟩
    exact congrArg Subtype.val this
  · set t := resHom W ⟨a', hAst ha'⟩ with ht
    have htA : t ∈ autSub A W := mem_autSub.mpr ⟨⟨a', hAst ha'⟩, ha', rfl⟩
    have ht2 : t ^ 2 = 1 := hel.2 t htA
    have hzp : Subgroup.zpowers t = autSub A W := by
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · rw [Subgroup.zpowers_le]
        exact htA
      · have hord : orderOf t = 2 := by
          have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
          exact orderOf_eq_prime ht2 h'
        rw [Nat.card_zpowers, hord, hcardA]
    have hs : resHom W ⟨a, hAst ha⟩ ∈ Subgroup.zpowers t := by
      rw [hzp]
      exact mem_autSub.mpr ⟨⟨a, hAst ha⟩, ha, rfl⟩
    have hgen : (resHom W ⟨a, hAst ha⟩) ⟨w, hw⟩ * (⟨w, hw⟩ : ↥W)⁻¹ ∈ commV (Subgroup.zpowers t) :=
      Subgroup.subset_closure ⟨resHom W ⟨a, hAst ha⟩, hs, ⟨w, hw⟩, rfl⟩
    have := (isQuadratic_zpowers hW' ht2 hgen) t (Subgroup.mem_zpowers t)
    exact congrArg Subtype.val this

end ThreeWrap

theorem pCoreOf_le_pCoreOf_of_isSubnormal {Γ : Type*} [Group Γ] [Finite Γ] (p : ℕ) [Fact p.Prime]
    {H K : Subgroup Γ} (h : CFSG.Open.IsSubnormal H K) :
    CFSG.Open.pCoreOf p H ≤ CFSG.Open.pCoreOf p K := by
  induction h with
  | refl H => exact le_rfl
  | @step H M K hHM hnorm _ ih =>
    refine le_trans ?_ ih
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer p
      ((CFSG.LieType.BorelTits.pCoreOf_le p H).trans hHM) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup p H)
    exact ((Subgroup.normal_subgroupOf_iff_le_normalizer hHM).1 hnorm).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf p H)

theorem two_sixteen_three {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {G A E : Subgroup (MulAut V)} (hA : IsOff A) (hAG : A ≤ G)
    (hsub : CFSG.Open.IsSubnormal E G)
    (hnat : IsAltNatSection E (commV E) (commV E ⊓ fixV E) 3) (hEA : ⁅E, A⁆ ≠ ⊥) :
    A ≤ Subgroup.normalizer (E : Set (MulAut V)) ∧ commV E ⊓ fixV E = ⊥ ∧
      Nat.card (autSub A (commV E)) = 2 ∧
      (∀ a ∈ A, ∀ a' ∈ A, ∀ w ∈ commV E, a' (a w * w⁻¹) = a w * w⁻¹) ∧
      (fixV A).relIndex (commV E) = (cenIn A (commV E)).relIndex A := by
  obtain ⟨-, θ, β, hβs, hβk, hβe⟩ := hnat
  obtain ⟨hEcard, -, hcardW⟩ := three_facts hV rfl θ β hβs hβk
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE3 : IsPGroup 3 E := IsPGroup.of_card (n := 1) (by rw [hEcard]; norm_num)
  have hEN : E ≤ CFSG.Open.pCoreOf 3 G :=
    (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 3 le_rfl Subgroup.le_normalizer
      hE3).trans (pCoreOf_le_pCoreOf_of_isSubnormal 3 hsub)
  have hAN : A ≤ Subgroup.normalizer (E : Set (MulAut V)) :=
    offender_le_normalizer_of_card_three hV hA (CFSG.LieType.BorelTits.pCoreOf_isPGroup 3 G)
      (fun a ha n hn => (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 3 G (hAG ha)) n).mp hn)
      hEN hEcard hcardW
  obtain ⟨hinf, hcardA, hquad, hidx⟩ :=
    two_sixteen_three_gen hV rfl θ β hβs hβk hβe hAN hA hEA
  exact ⟨hAN, hinf, hcardA, hquad, hidx⟩

end CFSG.CGT.PushingUpLit.BHS
