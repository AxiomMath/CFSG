module

public import CFSG.LieType.Steinberg.CentralExt.SpinMinus
public import CFSG.LocalAnalysis.SectionRank.EvenCover.SLTwo
public import CFSG.LieType.Steinberg.Classical.SpinPlus

public section

namespace CFSG.ClassicalInvolution.ModelFacts.OrthAut

open CFSG.LieType.Steinberg CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.CentralExt CFSG.SectionRank

@[expose] def CentralPSection (p : ℕ) (K : Type) [Group K] : Prop :=
  ∀ (E : Type) [Group E] [Finite E] (π : E →* K), Function.Surjective π →
    π.ker ≤ Subgroup.center E → ¬ p ∣ Nat.card π.ker →
      ∃! s : K →* E, ∀ g, π (s g) = g

section Abstract

variable {p : ℕ} {K : Type} [Group K] [Finite K]

theorem CentralPSection.existsUnique_lift (h : CentralPSection p K) {E G : Type} [Group E]
    [Finite E] [Group G] {π : E →* G} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (hC : ¬ p ∣ Nat.card π.ker) (α : K →* G) :
    ∃! α' : K →* E, π.comp α' = α := by
  obtain ⟨σ, hσ, huniq⟩ := h (EvenCover.pullback π α) (EvenCover.pullbackFst π α)
    (EvenCover.pullbackFst_surjective hπ α) (EvenCover.pullbackFst_ker_le_center hcen α)
    (fun hd => hC (hd.trans (EvenCover.card_pullbackFst_ker_dvd π α)))
  refine ⟨_, EvenCover.comp_snd_section σ hσ, fun τ hτ => ?_⟩
  let τ' : K →* EvenCover.pullback π α :=
    { toFun := fun g => ⟨(g, τ g), by
        change α g = π (τ g)
        rw [← hτ, MonoidHom.comp_apply]⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp) }
  have h1 := huniq τ' fun g => rfl
  ext g
  exact congrArg (fun f : K →* EvenCover.pullback π α => ((f g : EvenCover.pullback π α) : K × E).2) h1

theorem CentralPSection.exists_mulEquiv_lift (h : CentralPSection p K) {X : Type} [Group X]
    (θ : K →* X) (hθ : Function.Surjective θ) (hker : θ.ker ≤ Subgroup.center K)
    (hC : ¬ p ∣ Nat.card θ.ker) (σ : X ≃* X) :
    ∃ α : K ≃* K, ∀ x, θ (α x) = σ (θ x) := by
  obtain ⟨α, hα, -⟩ := h.existsUnique_lift hθ hker hC (σ.toMonoidHom.comp θ)
  obtain ⟨α', hα', -⟩ := h.existsUnique_lift hθ hker hC (σ.symm.toMonoidHom.comp θ)
  obtain ⟨β, -, huniq⟩ := h.existsUnique_lift hθ hker hC θ
  have hαx : ∀ x, θ (α x) = σ (θ x) := fun x => DFunLike.congr_fun hα x
  have hαx' : ∀ x, θ (α' x) = σ.symm (θ x) := fun x => DFunLike.congr_fun hα' x
  have h1 : α.comp α' = MonoidHom.id _ :=
    (huniq _ (MonoidHom.ext fun x => by
      simp only [MonoidHom.comp_apply, hαx, hαx', MulEquiv.apply_symm_apply])).trans
      (huniq _ (MonoidHom.ext fun x => by simp)).symm
  have h2 : α'.comp α = MonoidHom.id _ :=
    (huniq _ (MonoidHom.ext fun x => by
      simp only [MonoidHom.comp_apply, hαx, hαx', MulEquiv.symm_apply_apply])).trans
      (huniq _ (MonoidHom.ext fun x => by simp)).symm
  exact ⟨{ toFun := α
           invFun := α'
           left_inv := fun x => DFunLike.congr_fun h2 x
           right_inv := fun x => DFunLike.congr_fun h1 x
           map_mul' := α.map_mul }, hαx⟩

theorem not_dvd_card_center_of_forall [Fact p.Prime]
    (h : ∀ x ∈ Subgroup.center K, x ^ p = 1 → x = 1) :
    ¬ p ∣ Nat.card (Subgroup.center K) := by
  intro hd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hd
  have h1 : (x : K) ^ p = 1 := by
    rw [← Subgroup.coe_pow, ← hx, pow_orderOf_eq_one, Subgroup.coe_one]
  have h2 : (x : K) = 1 := h x x.2 h1
  have h3 : x = 1 := Subtype.ext h2
  rw [h3, orderOf_one] at hx
  exact (Fact.out : p.Prime).one_lt.ne hx

end Abstract

section Families

variable {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]

omit [Finite F] [Fact (Nat.Prime p)] in
theorem ringChar_ne_two_of_ne_two (hp2 : p ≠ 2) : ringChar F ≠ 2 := by
  rw [ringChar.eq F p]
  exact hp2

theorem centralPSection_spinOdd (hp2 : p ≠ 2) {n : ℕ} (hn : 3 ≤ n) :
    CentralPSection p (spinGroup (quadOdd n F)) := by
  intro E _ _ π hπ hcen hC
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two_of_ne_two (F := F) hp2)
  refine existsUnique_section_of_sl2_lift (p := p)
    (oddDatum_isCTGroupDatum n F (oddDatum_iSup_eq_top n F h2 hn)) (oddDatum_steinbergExtras h2)
    SpinOdd.isParametrization SpinOdd.rankOne hπ hcen hC fun ρ => ?_
  obtain ⟨ρ', hρ', -⟩ := EvenCover.sl2_existsUnique_lift hπ hcen hC ρ
  exact ⟨ρ', fun g => congrArg (· g) hρ'⟩

theorem centralPSection_spinPlus {n : ℕ} (hn : 3 ≤ n) :
    CentralPSection p (spinGroup (quadPlus n F)) := by
  intro E _ _ π hπ hcen hC
  refine existsUnique_section_of_sl2_lift (p := p) (SpinPlus.isCTGroupDatum hn)
    (plusDatum_steinbergExtras hn) (SpinPlus.isParametrization hn) (SpinPlus.rankOne hn) hπ hcen
    hC fun ρ => ?_
  obtain ⟨ρ', hρ', -⟩ := EvenCover.sl2_existsUnique_lift hπ hcen hC ρ
  exact ⟨ρ', fun g => congrArg (· g) hρ'⟩

theorem centralPSection_spinMinus (hp2 : p ≠ 2) {n : ℕ} (hn : 4 ≤ n) {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    CentralPSection p (spinGroup (quadMinus n F b c)) := by
  intro E _ _ π hπ hker hC
  have hk : ringChar F ≠ 2 := ringChar_ne_two_of_ne_two (F := F) hp2
  have := fact_shortField hirr
  have := finite_shortField (b := b) (c := c)
  have : CharP (ShortField b c) p :=
    charP_of_injective_algebraMap (algebraMap F (ShortField b c)).injective p
  refine existsUnique_section_of_rankOne_lift (minusDatum_isCTGroupDatum n hirr hn)
    (minusDatum_steinbergExtras n hirr) (fun _ hγ => isPGroup_minusRootGroup hirr hγ) hπ hker hC
    fun i => ?_
  by_cases hi : i.val + 1 < n - 1
  · obtain ⟨ρ', hρ', -⟩ := EvenCover.sl2_existsUnique_lift hπ hker hC
      ((minusFrame n b c).longSL2 (succ_ne_of_lt n hi) true false)
    exact exists_lift_of_injective (SpinFrame.longSL2_injective _ _ _ _)
      (rankOne_minusRootGroup_of_lt n hirr hi).le fun g => DFunLike.congr_fun hρ' g
  · exact exists_rankOne_lift_of_rankOneRels (minusDatum_steinbergExtras n hirr) i
      (shortRels n hirr i) (mem_minusRootGroup_single_iff hirr hi)
      (mem_minusRootGroup_neg_single_iff hirr hi) (shortRels_x_injective hirr i)
      (fun t ht h1 => shortRels_h_eq_one hirr (Ring.two_ne_zero hk) i ht h1) hπ hker hC

end Families

end CFSG.ClassicalInvolution.ModelFacts.OrthAut
