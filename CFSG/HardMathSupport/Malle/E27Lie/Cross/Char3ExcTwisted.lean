module

public import CFSG.HardMathSupport.Malle.E27Lie.Defining.AbelianKill
public import CFSG.Adapters.TauCetiExceptional.EvenAll
public import CFSG.HardMathSupport.Lang.Triality.HeightLayers
public import CFSG.Timmesfeld.Orders.ExceptionalTwistedUnipotent

public noncomputable section

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Foote.E27
  CFSG.HardMathSupport.Lang.Triality CFSG.Timmesfeld.ExceptionalOrders

section Twisted


variable (t : TwistTag) {F : Type} [Field F] [Finite F] (σ : F →+* F)

@[expose] def rootsGe (k : ℕ) : Set (Fin t.tag.rank → ℤ) :=
  {α | IsRoot t.tag α ∧ 0 < height α ∧ (k : ℤ) ≤ height α}

theorem rootsGe_subset_pos (k : ℕ) : rootsGe t k ⊆ {α | IsRoot t.tag α ∧ 0 < height α} :=
  fun _ h => ⟨h.1, h.2.1⟩

theorem heightSeries_eq_rootSpan (k : ℕ) :
    heightSeries t.tag F (k : ℤ) = rootSpan t.tag F (rootsGe t k) := rfl

theorem rootSpan_rootsGe_inf_le (k : ℕ) :
    rootSpan t.tag F (rootsGe t k) ⊓ twistedFixedGroup t F σ ≤ graphFixedRootGroup t F σ := by
  intro x hx
  have h1 : x ∈ posUnipotent t.tag F := rootSpan_mono (rootsGe_subset_pos t k) hx.1
  exact (le_sup_left : graphFixedPosUnipotent t F σ ≤ _) ⟨h1, hx.2⟩

theorem card_layerSub_eq (k : ℕ) :
    Nat.card (layerSub t σ k) =
      Nat.card ↥(rootSpan t.tag F (rootsGe t k) ⊓ twistedFixedGroup t F σ) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨(x.1 : ↥(graphFixedRootGroup t F σ)).1,
        ⟨by rw [← heightSeries_eq_rootSpan]; exact x.2, graphFixedRootGroup_le t F σ x.1.2⟩⟩
      invFun := fun y => ⟨⟨y.1, rootSpan_rootsGe_inf_le t σ k y.2⟩, by
        rw [mem_layerSub, heightSeries_eq_rootSpan]; exact y.2.1⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }

variable {t σ}

theorem card_layerSub {q : ℕ} (hσs : Function.Surjective σ)
    (hq : ∀ a, Nat.card (orbitField t F σ a) = q ^ (t.orbit a).card) {k : ℕ} (hk : 1 ≤ k) :
    Nat.card (layerSub t σ k) = q ^ (rootsGe t k).ncard := by
  rw [card_layerSub_eq]
  refine card_rootSpan_inf_twistedFixedGroup hσs hq (fun α h => ⟨h.1, h.2.1⟩)
    (fun α h => ⟨h.1.permLattice t.cartan_perm, by rw [height_permLattice]; exact h.2.1,
      by rw [height_permLattice]; exact h.2.2⟩) ?_
  intro α hα β hβ a b ha hb hr
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk
  refine ⟨hr, ?_, ?_⟩ <;> rw [height_nsmul_add_nsmul] <;>
    nlinarith [hα.2.1, hα.2.2, hβ.2.1, hβ.2.2]

theorem finite_rootsGe (k : ℕ) : (rootsGe t k).Finite :=
  (finite_setOf_isRoot t.tag).subset fun _ h => h.1

theorem rank_add_ncard_le :
    (rootsGe t 2).ncard + t.tag.rank ≤ (rootsGe t 1).ncard := by
  set S : Set (Fin t.tag.rank → ℤ) := Set.range fun i : Fin t.tag.rank => Pi.single i 1 with hS
  have hSf : S.Finite := Set.finite_range _
  have hdisj : Disjoint (rootsGe t 2) S := by
    rw [Set.disjoint_left]
    rintro α hα ⟨i, rfl⟩
    have := hα.2.2
    rw [height_single] at this
    norm_num at this
  have hsub : rootsGe t 2 ∪ S ⊆ rootsGe t 1 := by
    rintro α (h | ⟨i, rfl⟩)
    · exact ⟨h.1, h.2.1, by have := h.2.2; push_cast at this ⊢; omega⟩
    · refine ⟨isRoot_single t.tag i, ?_, ?_⟩ <;> rw [height_single] <;> norm_num
  have hcard : S.ncard = t.tag.rank := by
    rw [hS, Set.ncard_range_of_injective]
    · simp
    · intro i j h
      have := congrFun h i
      by_contra hne
      simp [Pi.single_apply, hne] at this
  calc (rootsGe t 2).ncard + t.tag.rank = (rootsGe t 2 ∪ S).ncard := by
        rw [Set.ncard_union_eq hdisj (finite_rootsGe 2) hSf, hcard]
    _ ≤ (rootsGe t 1).ncard := Set.ncard_le_ncard hsub (finite_rootsGe 1)

theorem rank_le_card_range_layerHom {q : ℕ} (hq0 : 0 < q) (hσs : Function.Surjective σ)
    (hq : ∀ a, Nat.card (orbitField t F σ a) = q ^ (t.orbit a).card)
    (hh : 0 < ((1 : ℕ) : ℤ)) :
    q ^ t.tag.rank ≤ Nat.card (layerHom t σ 1 hh).range := by
  have h1 := card_layerSub hσs hq (k := 1) le_rfl
  have h2 := card_layerSub hσs hq (k := 2) (by norm_num)
  have hker : Nat.card (layerHom t σ 1 hh).ker ≤ Nat.card (layerSub t σ 2) := by
    have := layerHom_ker_le t σ 1 hh
    rw [← Subgroup.card_map_of_injective (layerSub t σ 1).subtype_injective]
    exact Subgroup.card_le_of_le this
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (layerHom t σ 1 hh).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (layerHom t σ 1 hh)).toEquiv] at hmul
  have hncard := rank_add_ncard_le (t := t)
  have hpow : q ^ ((rootsGe t 2).ncard + t.tag.rank) ≤ q ^ (rootsGe t 1).ncard :=
    Nat.pow_le_pow_right hq0 hncard
  rw [pow_add] at hpow
  have hpos : 0 < q ^ (rootsGe t 2).ncard := pow_pos hq0 _
  refine Nat.le_of_mul_le_mul_left ?_ hpos
  calc q ^ (rootsGe t 2).ncard * q ^ t.tag.rank ≤ q ^ (rootsGe t 1).ncard := hpow
    _ = Nat.card (layerHom t σ 1 hh).range * Nat.card (layerHom t σ 1 hh).ker := by
        rw [← h1]; exact hmul
    _ ≤ Nat.card (layerHom t σ 1 hh).range * q ^ (rootsGe t 2).ncard := by
        rw [← h2]; exact Nat.mul_le_mul_left _ hker
    _ = q ^ (rootsGe t 2).ncard * Nat.card (layerHom t σ 1 hh).range := mul_comm _ _

theorem layerSub_one_card [Fact (Nat.Prime 3)] [CharP F 3] (σ' : F ≃+* F) :
    Nat.card (layerSub t σ'.toRingHom 1) =
      3 ^ (Nat.card ↥(graphFixedRootGroup t F σ'.toRingHom)).factorization 3 := by
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem t.tag).length
  obtain ⟨⟨P, hP⟩, -⟩ := exceptional_fixed_Sylow_opposition t F 3 σ' w₀ hw₀
  have hlayer : layerSub t σ'.toRingHom 1 =
      (P : Subgroup ↥(graphFixedRootGroup t F σ'.toRingHom)) := by
    have e : heightSeries t.tag F ((1 : ℕ) : ℤ) = posUnipotent t.tag F := by
      rw [Nat.cast_one]
      exact heightSeries_one
    rw [hP]
    ext x
    rw [mem_layerSub, e, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      exact ⟨hx, graphFixedRootGroup_le t F σ'.toRingHom x.2⟩
    · intro hx
      exact hx.1
  rw [hlayer]
  exact P.card_eq_multiplicity

variable {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}

theorem false_of_twisted_char_three (h : E27Config X K R T z) (hz : z ∈ K) {p f : ℕ}
    (hp3 : p = 3) [CharP F p] (hf : 1 ≤ f) (hK : Nat.card F = (p ^ f) ^ t.order)
    (σ' : F ≃+* F) (hσ : ∀ c, σ' c = c ^ (p ^ f)) (hr : 4 ≤ t.tag.rank)
    (ψ : ↥K ≃* ↥(graphFixedRootGroup t F σ'.toRingHom)) : False := by
  subst hp3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq : ∀ a, Nat.card (orbitField t F σ'.toRingHom a) = (3 ^ f) ^ (t.orbit a).card :=
    card_orbitField Nat.prime_three hf hK (fun c => hσ c)
  have hh : 0 < ((1 : ℕ) : ℤ) := by norm_num
  have hq0 : 0 < 3 ^ f := by positivity
  refine E27Config.false_of_sylow_hom_comm h hz ψ (layerSub t σ'.toRingHom 1)
    (layerSub_one_card σ') (layerHom t σ'.toRingHom 1 hh).rangeRestrict
    (layerHom t σ'.toRingHom 1 hh).rangeRestrict_surjective ?_
  have hrange := rank_le_card_range_layerHom (t := t) hq0 σ'.surjective hq hh
  calc 81 = 3 ^ 4 := by norm_num
    _ ≤ (3 ^ f) ^ 4 := Nat.pow_le_pow_left (Nat.le_self_pow (by omega) 3) 4
    _ ≤ (3 ^ f) ^ t.tag.rank := Nat.pow_le_pow_right hq0 hr
    _ ≤ _ := hrange

end Twisted

section Index


variable {t : TwistTag} {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}

theorem false_of_twisted_of_model (h : E27Config X K R T z) (hz : z ∈ K) {p f : ℕ}
    (hp3 : p = 3) (hp : p.Prime) (hf : 1 ≤ f) {F : Type} [Field F] [Finite F] [CharP F p]
    (hK : Nat.card F = (p ^ f) ^ t.order) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (hr : 4 ≤ t.tag.rank)
    (e : ↥K ≃* DerivedCentralQuotient (twistedFixedGroup t F σ.toRingHom)) : False := by
  obtain ⟨-, -, hder, -⟩ := finite_fixed_root_group_perfect t hp hf F hK σ.toRingHom hσ
  have hc : Subgroup.center ↥(graphFixedRootGroup t F σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  let e₁ : ↥⁅twistedFixedGroup t F σ.toRingHom, twistedFixedGroup t F σ.toRingHom⁆ ≃*
      ↥(graphFixedRootGroup t F σ.toRingHom) := MulEquiv.subgroupCongr hder
  have hcH : Subgroup.center ↥⁅twistedFixedGroup t F σ.toRingHom,
      twistedFixedGroup t F σ.toRingHom⁆ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : e₁ x ∈ Subgroup.center ↥(graphFixedRootGroup t F σ.toRingHom) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨w, rfl⟩ := e₁.surjective y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx w]
    rw [hc, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.2 (e₁.injective (by rw [h1, map_one]))
  let e₂ : DerivedCentralQuotient (twistedFixedGroup t F σ.toRingHom) ≃*
      ↥(graphFixedRootGroup t F σ.toRingHom) :=
    ((QuotientGroup.quotientMulEquivOfEq hcH).trans QuotientGroup.quotientBot).trans e₁
  exact false_of_twisted_char_three h hz hp3 hf hK σ hσ hr (e.trans e₂)

open TauCeti in
theorem false_of_twisted_bridge {c : PrimePower → LieTypeIndex} {t : TwistTag}
    (hb : CFSG.TauCetiBridge.Even.TwistedBridgeAll t c) (hr : 4 ≤ t.tag.rank)
    (h : E27Config X K R T z) (hz : z ∈ K) (q : PrimePower) (hv : (c q).Valid) (hp : q.p = 3)
    (e : ↥K ≃* ValidLieTypeIndex.Group ⟨c q, hv⟩) : False := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hf := q.exponent_pos
  have hcard : Nat.card (GaloisField q.p (q.exponent * t.order)) = q.card ^ t.order := by
    rw [GaloisField.card q.p (q.exponent * t.order) (by have := t.order_pos; positivity),
      PrimePower.card_def, pow_mul]
  have hK : Nat.card (GaloisField q.p (q.exponent * t.order)) = (q.p ^ q.exponent) ^ t.order := by
    rw [hcard, PrimePower.card_def]
  have hinj := RingHom.injective (iterateFrobenius (GaloisField q.p (q.exponent * t.order)) q.p
    q.exponent)
  let σ : GaloisField q.p (q.exponent * t.order) ≃+* GaloisField q.p (q.exponent * t.order) :=
    RingEquiv.ofBijective (iterateFrobenius (GaloisField q.p (q.exponent * t.order)) q.p
      q.exponent) ⟨hinj, Finite.surjective_of_injective hinj⟩
  have hσ : ∀ c, σ c = c ^ q.card := fun c => by
    show iterateFrobenius (GaloisField q.p (q.exponent * t.order)) q.p q.exponent c = _
    rw [iterateFrobenius_def, PrimePower.card_def]
  have hσ' : ∀ c, σ c = c ^ (q.p ^ q.exponent) := fun c => by rw [hσ, PrimePower.card_def]
  obtain ⟨br⟩ := hb q hv (GaloisField q.p (q.exponent * t.order)) hcard σ.toRingHom hσ
  exact false_of_twisted_of_model h hz hp q.prime_p hf hK σ hσ' hr (e.trans br.symm)

open TauCeti in
theorem false_of_typeTwistedE6_char_three (h : E27Config X K R T z) (hz : z ∈ K) (q : PrimePower)
    (hv : (LieTypeIndex.twistedE6 q).Valid) (hp : q.p = 3)
    (e : ↥K ≃* (CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group) : False :=
  false_of_twisted_bridge (t := .E6) (CFSG.TauCetiBridge.Even.chevalleyBridgesAll.twistedE6)
    (by decide) h hz q hv hp e

open TauCeti in
theorem false_of_typeTrialityD4_char_three (h : E27Config X K R T z) (hz : z ∈ K)
    (q : PrimePower) (hv : (LieTypeIndex.trialityD4 q).Valid) (hp : q.p = 3)
    (e : ↥K ≃* (CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group) : False :=
  false_of_twisted_bridge (t := .D4) (CFSG.TauCetiBridge.Even.chevalleyBridgesAll.trialityD4)
    (by decide) h hz q hv hp e

end Index

end CFSG.HardMathSupport.Malle.E27Lie

end
