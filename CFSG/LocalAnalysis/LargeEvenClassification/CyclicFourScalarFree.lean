module

public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourNorm
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoGeneratorStrata
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourEvenGenerators

public section

namespace CFSG.LargeEvenClassification.Helpers

open scoped commutatorElement

theorem cyclicFourAut_isPGroup (n : ℕ) : IsPGroup 2 (CyclicFourAut n) :=
  IsPGroup.of_card (cyclicFourAut_card n)

theorem cyclicFour_no_delta_residual_injective (n : ℕ) (H : Subgroup (CyclicFourAut n))
    (hdelta : cyclicFourDelta n ∉ H) :
    Function.Injective ((cyclicFourResidual n).comp H.subtype) := by
  let P := Subgroup.zpowers (cyclicFourC n)
  let δ : P := ⟨cyclicFourDelta n, Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _⟩
  have horder : orderOf δ = 2 :=
    (orderOf_injective P.subtype Subtype.val_injective δ).symm.trans (cyclicFourDelta_order n)
  have hintersection : H.subgroupOf P = ⊥ := by
    by_contra hne
    have hmem := cyclic_two_group_subgroup_contains_involution
      ((cyclicFourAut_isPGroup n).to_subgroup P) δ horder (H.subgroupOf P) hne
    exact hdelta hmem
  let f := (cyclicFourResidual n).comp H.subtype
  apply (f.ker_eq_bot_iff).mp
  apply le_antisymm _ bot_le
  intro x hx
  have hxP : x.val ∈ P := (cyclicFourResidual_kernel_scalar n).le hx
  have hxIntersection : (⟨x.val, hxP⟩ : P) ∈ H.subgroupOf P := x.property
  rw [hintersection] at hxIntersection
  have hone := congrArg Subtype.val (Subgroup.mem_bot.mp hxIntersection)
  exact Subgroup.mem_bot.mpr (Subtype.ext hone)

theorem cyclicFour_no_delta_E_central (n : ℕ) (H : Subgroup (CyclicFourAut n))
    (hdelta : cyclicFourDelta n ∉ H) (e : CyclicFourAut n)
    (he : e ∈ cyclicFourE n) (heH : e ∈ H) (g : H) : Commute e g.val := by
  have hd : ⁅e, g.val⁆ ∈ Subgroup.zpowers (cyclicFourDelta n) :=
    cyclicFourE_commutator_bound n (Subgroup.commutator_mem_commutator he (Subgroup.mem_top _))
  have hp : ⁅e, g.val⁆ ∈ Subgroup.zpowers (cyclicFourC n) :=
    (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _)) hd
  have hcH : ⁅e, g.val⁆ ∈ H := H.mul_mem (H.mul_mem (H.mul_mem heH g.property) (H.inv_mem heH))
    (H.inv_mem g.property)
  let c : H := ⟨⁅e, g.val⁆, hcH⟩
  have hc : cyclicFourResidual n c.val = 1 := (cyclicFourResidual_kernel_scalar n).symm.le hp
  have hone : c = 1 := cyclicFour_no_delta_residual_injective n H hdelta
    (hc.trans (map_one ((cyclicFourResidual n).comp H.subtype)).symm)
  apply commutatorElement_eq_one_iff_commute.mp
  exact congrArg Subtype.val hone

theorem cyclicFour_no_delta_mixed_excluded {S : Type*} [Group S] [Finite S]
    (A : Subgroup S) [A.Normal] (hcommutative : IsMulCommutative A)
    (hselfCentralizing : Subgroup.centralizer (A : Set S) = A)
    (hnoEight : ∀ E : Subgroup S, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8)
    (n : ℕ) (coordinates : Additive A ≃+ CyclicFourSpace n)
    (hdelta : cyclicFourDelta n ∉
      ((cyclicFourAutomorphismEquiv hcommutative n coordinates).toMonoidHom.comp
        (MulAut.conjNormal (H := A))).range) (e : ZMod 2) :
    cyclicFourElementaryHom n (Multiplicative.ofAdd e, (Multiplicative.ofAdd 1, Multiplicative.ofAdd 1)) ∉
      ((cyclicFourAutomorphismEquiv hcommutative n coordinates).toMonoidHom.comp
        (MulAut.conjNormal (H := A))).range := by
  let action := (cyclicFourAutomorphismEquiv hcommutative n coordinates).toMonoidHom.comp
    (MulAut.conjNormal (H := A))
  let g := cyclicFourElementaryHom n
    (Multiplicative.ofAdd e, (Multiplicative.ofAdd (1 : ZMod 2), Multiplicative.ofAdd (1 : ZMod 2)))
  intro hg
  have hcentral (s : S) : Commute g (action s) := cyclicFour_no_delta_E_central n action.range
    hdelta g ⟨_, rfl⟩ hg ⟨action s, ⟨s, rfl⟩⟩
  exact cyclicFour_mixed_action_excluded A hcommutative hselfCentralizing hnoEight n coordinates e
    hcentral hg

@[expose] noncomputable def cyclicFourElementaryShears (n : ℕ) : cyclicFourE n →*
    (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :=
  (MonoidHom.snd _ _).comp (MonoidHom.ofInjective (cyclicFourElementaryHom_injective n)).symm.toMonoidHom

theorem cyclicFourElementaryShears_spec (n : ℕ)
    (x : Multiplicative (ZMod 2) × (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) :
    cyclicFourElementaryShears n ⟨cyclicFourElementaryHom n x, ⟨x, rfl⟩⟩ = x.2 := by
  have h := (MonoidHom.ofInjective (cyclicFourElementaryHom_injective n)).symm_apply_apply x
  exact congrArg Prod.snd h

theorem cyclicFour_E_intersection_card (n : ℕ) (H : Subgroup (CyclicFourAut n))
    (hdelta : cyclicFourDelta n ∉ H)
    (hmixed : ∀ e : ZMod 2, cyclicFourElementaryHom n
      (Multiplicative.ofAdd e, (Multiplicative.ofAdd 1, Multiplicative.ofAdd 1)) ∉ H) :
    Nat.card (H.subgroupOf (cyclicFourE n)) ≤ 2 := by
  let T := H.subgroupOf (cyclicFourE n)
  let f := (cyclicFourElementaryShears n).comp T.subtype
  have hinjective : Function.Injective f := by
    apply (f.ker_eq_bot_iff).mp
    apply le_antisymm _ bot_le
    intro t ht
    obtain ⟨x, hx⟩ := t.val.property
    have hxShear : x.2 = 1 := by
      change cyclicFourElementaryShears n t.val = 1 at ht
      have heq : t.val = ⟨cyclicFourElementaryHom n x, ⟨x, rfl⟩⟩ := Subtype.ext hx.symm
      rw [heq, cyclicFourElementaryShears_spec] at ht
      exact ht
    have hcases : ∀ e : ZMod 2, e = 0 ∨ e = 1 := by decide +kernel
    rcases hcases x.1.toAdd with he | he
    · have hxOne : x = 1 := Prod.ext (Multiplicative.toAdd.injective he) hxShear
      have htOne : t.val.val = 1 := by rw [← hx, hxOne, map_one]
      exact Subgroup.mem_bot.mpr (Subtype.ext (Subtype.ext htOne))
    · have htDelta : t.val.val = cyclicFourDelta n := by
        rw [← hx, cyclicFourElementaryHom_spec]
        rw [hxShear]
        change cyclicFourDelta n ^ x.1.toAdd.val *
          ((cyclicFourU n ^ 2) ^ (0 : ZMod 2).val * (cyclicFourV n ^ 2) ^ (0 : ZMod 2).val) = _
        simp only [he, ZMod.val_one, ZMod.val_zero, pow_zero, pow_one, mul_one]
      exact (hdelta (htDelta ▸ t.property)).elim
  have hpT : IsPGroup 2 T :=
    ((cyclicFourAut_isPGroup n).to_subgroup (cyclicFourE n)).to_subgroup T
  obtain ⟨r, hr⟩ := hpT.exists_card_eq
  have hcard : Nat.card T ≤ 4 := by
    have h := Nat.card_le_card_of_injective f hinjective
    have hc : Nat.card (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) = 4 := by
      rw [Nat.card_eq_fintype_card]
      decide +kernel
    rwa [hc] at h
  have hnotFull : Nat.card T ≠ 4 := by
    intro hfull
    have hrange : f.range = ⊤ := by
      apply Subgroup.eq_of_le_of_card_ge le_top
      rw [Nat.card_congr (Subgroup.topEquiv (G := Multiplicative (ZMod 2) × Multiplicative (ZMod 2))).toEquiv,
        ← Nat.card_congr (MonoidHom.ofInjective hinjective).toEquiv, hfull,
        Nat.card_eq_fintype_card]
      decide +kernel
    obtain ⟨t, ht⟩ := MonoidHom.range_eq_top.mp hrange
      (Multiplicative.ofAdd (1 : ZMod 2), Multiplicative.ofAdd (1 : ZMod 2))
    obtain ⟨x, hx⟩ := t.val.property
    have hxShear : x.2 = (Multiplicative.ofAdd 1, Multiplicative.ofAdd 1) := by
      change cyclicFourElementaryShears n t.val = _ at ht
      have heq : t.val = ⟨cyclicFourElementaryHom n x, ⟨x, rfl⟩⟩ := Subtype.ext hx.symm
      rw [heq, cyclicFourElementaryShears_spec] at ht
      exact ht
    apply hmixed x.1.toAdd
    have heq : x = (Multiplicative.ofAdd x.1.toAdd, (Multiplicative.ofAdd 1, Multiplicative.ofAdd 1)) :=
      Prod.ext rfl hxShear
    exact heq ▸ hx.symm ▸ t.property
  have hrle : r ≤ 2 := by
    have hpow : 2 ^ r ≤ 2 ^ 2 := hr.symm ▸ hcard
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hpow
  have hrl : r ≤ 1 := by
    by_contra h
    have heq : r = 2 := by omega
    exact hnotFull (by rw [hr, heq]; norm_num)
  rw [hr]
  exact (Nat.pow_le_pow_right (by decide : 0 < 2) hrl).trans (by decide)

theorem cyclicFour_scalar_free_shear_rank (n : ℕ) (Q : Subgroup (CyclicFourAut n))
    (hdelta : cyclicFourDelta n ∉ Q)
    (hmixed : ∀ e : ZMod 2, cyclicFourElementaryHom n
      (Multiplicative.ofAdd e, (Multiplicative.ofAdd 1, Multiplicative.ofAdd 1)) ∉ Q) :
    pGeneratorRank 2 (cyclicFourShearPreimage n |>.comap Q.subtype) ≤ 1 := by
  let V := (cyclicFourShearPreimage n).comap Q.subtype
  let f := (cyclicFourResidual n).comp Q.subtype
  have hf := cyclicFour_no_delta_residual_injective n Q hdelta
  have hVcomm : IsMulCommutative V := by
    apply IsMulCommutative.of_comm
    intro v w
    apply (hf.comp Subtype.val_injective)
    have hv : f v.val ∈ residualZeroShear.range := by
      rw [← residualZeroDiagonal_kernel]
      exact v.property
    have hw : f w.val ∈ residualZeroShear.range := by
      rw [← residualZeroDiagonal_kernel]
      exact w.property
    obtain ⟨x, hx⟩ := hv
    obtain ⟨y, hy⟩ := hw
    change f (v.val * w.val) = f (w.val * v.val)
    rw [map_mul, map_mul, ← hx, ← hy, ← map_mul residualZeroShear, ← map_mul residualZeroShear]
    exact congrArg residualZeroShear (mul_comm x y)
  let : CommGroup V := { (inferInstance : Group V) with mul_comm := @mul_comm' V _ hVcomm }
  let K := (powMonoidHom 2 : V →* V).ker
  let T := Q.subgroupOf (cyclicFourE n)
  let i : K → T := fun v => ⟨⟨v.val.val.val, cyclicFourShearPreimage_square_one n _ v.val.property
    (congrArg (fun x : V => x.val.val) v.property)⟩, v.val.val.property⟩
  have hi : Function.Injective i := by
    intro v w h
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun t : T => t.val.val) h
  have hKcard : Nat.card K ≤ 2 :=
    (Nat.card_le_card_of_injective i hi).trans (cyclicFour_E_intersection_card n Q hdelta hmixed)
  have hpV := ((cyclicFourAut_isPGroup n).to_subgroup Q).to_subgroup V
  change Nat.log 2 (Nat.card (V ⧸ frattini V)) ≤ 1
  rw [commutative_frattini_card_eq_power_kernel Nat.prime_two hpV]
  exact (Nat.log_mono_right hKcard).trans (by decide)

theorem cyclicFour_scalar_free_action_rank (n : ℕ) (Q : Subgroup (CyclicFourAut n))
    (hdelta : cyclicFourDelta n ∉ Q)
    (hmixed : ∀ e : ZMod 2, cyclicFourElementaryHom n
      (Multiplicative.ofAdd e, (Multiplicative.ofAdd 1, Multiplicative.ofAdd 1)) ∉ Q) :
    pGeneratorRank 2 Q ≤ 3 := by
  let f := (cyclicFourOuter n).comp Q.subtype
  let V := (cyclicFourShearPreimage n).comap Q.subtype
  have hk : f.ker = V := rfl
  let : V.Normal := hk ▸ f.normal_ker
  have hpr := ((cyclicFourAut_isPGroup n).to_subgroup Q)
  have hr : pGeneratorRank 2 f.range ≤ 2 := by
    have he := MulEquiv.prodCongr fourUnitSignEquiv.symm fourUnitSignEquiv.symm
    let embedding := he.toMonoidHom.comp f.range.subtype
    have hi : Function.Injective embedding := he.injective.comp Subtype.val_injective
    let E := Multiplicative (ZMod 2) × Multiplicative (ZMod 2)
    have hpE : IsPGroup 2 E := IsPGroup.of_card (by
      rw [Nat.card_eq_fintype_card]; decide +kernel : Nat.card E = 2 ^ 2)
    have hEexp : ∀ e : E, e ^ 2 = 1 := by
      change ∀ e : Multiplicative (ZMod 2) × Multiplicative (ZMod 2), e ^ 2 = 1
      decide +kernel
    have hrE : pGeneratorRank 2 E = 2 := by
      have h := elementary_pGeneratorRank_eq_log_card Nat.prime_two hEexp
      change pGeneratorRank 2 (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) = 2
      change pGeneratorRank 2 (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) =
        Nat.log 2 (Nat.card (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) at h
      rw [h, Nat.card_eq_fintype_card]
      decide +kernel
    exact (commutative_pGeneratorRank_embedding_le Nat.prime_two hpE embedding hi).trans hrE.le
  have hquotient : pGeneratorRank 2 (Q ⧸ V) = pGeneratorRank 2 f.range :=
    pGeneratorRank_mulEquiv Nat.prime_two (hpr.to_quotient V)
      (QuotientGroup.quotientKerEquivRange f)
  have h := pGeneratorRank_extension_le Nat.prime_two hpr V
  rw [hquotient] at h
  have hVr := cyclicFour_scalar_free_shear_rank n Q hdelta hmixed
  change pGeneratorRank 2 V ≤ 1 at hVr
  omega

theorem cyclicFour_three_action_shear_involution (n : ℕ) (Q : Subgroup (CyclicFourAut n))
    (hrank : pGeneratorRank 2 Q = 3) :
    ∃ q : Q, (q : CyclicFourAut n) ∈ cyclicFourShearPreimage n ∧ orderOf q = 2 := by
  let V := (cyclicFourOuter n |>.comp Q.subtype).ker
  let f := (cyclicFourOuter n).comp Q.subtype
  have hpQ := (cyclicFourAut_isPGroup n).to_subgroup Q
  have hVr : Nat.card V ≠ 1 := by
    intro hcard
    have hVrank : pGeneratorRank 2 V ≤ 0 := by
      have hq := Nat.card_le_card_of_surjective (QuotientGroup.mk' (frattini V))
        (QuotientGroup.mk'_surjective _)
      rw [hcard] at hq
      change Nat.log 2 (Nat.card (V ⧸ frattini V)) ≤ 0
      exact (Nat.log_mono_right hq).trans (by decide)
    have hfr : pGeneratorRank 2 f.range ≤ 2 := by
      have hq := Nat.card_le_card_of_surjective (QuotientGroup.mk' (frattini f.range))
        (QuotientGroup.mk'_surjective _)
      have hi := Nat.card_le_card_of_injective f.range.subtype Subtype.val_injective
      have hc : Nat.card ((ZMod 4)ˣ × (ZMod 4)ˣ) = 4 := by
        rw [Nat.card_eq_fintype_card]
        decide +kernel
      rw [hc] at hi
      change Nat.log 2 (Nat.card (f.range ⧸ frattini f.range)) ≤ 2
      exact (Nat.log_mono_right (hq.trans hi)).trans (by decide)
    have hq : pGeneratorRank 2 (Q ⧸ V) = pGeneratorRank 2 f.range :=
      pGeneratorRank_mulEquiv Nat.prime_two (hpQ.to_quotient V) (QuotientGroup.quotientKerEquivRange f)
    have h := pGeneratorRank_extension_le Nat.prime_two hpQ V
    rw [hrank, hq] at h
    omega
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdiv : 2 ∣ Nat.card V := ((hpQ.to_subgroup V).card_eq_or_dvd).resolve_left hVr
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' 2 hdiv
  refine ⟨v.val, v.property, ?_⟩
  exact (orderOf_injective V.subtype Subtype.val_injective v).trans hv

theorem rank_two_cyclic_times_four_scalar_free_four_generators {S : Type*} [Group S] [Finite S]
    (hpgroup : IsPGroup 2 S) (A : Subgroup S) [A.Normal]
    (hcommutative : IsMulCommutative A)
    (hselfCentralizing : Subgroup.centralizer (A : Set S) = A)
    (hnoEight : ∀ E : Subgroup S, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8)
    (n : ℕ) (coordinates : Additive A ≃+ CyclicFourSpace n)
    (hdelta : cyclicFourDelta n ∉
      ((cyclicFourAutomorphismEquiv hcommutative n coordinates).toMonoidHom.comp
        (MulAut.conjNormal (H := A))).range)
    (U : Subgroup S) : ∃ X : Finset U, Subgroup.closure (X : Set U) = ⊤ ∧ X.card ≤ 4 := by
  let : CommGroup A := { (inferInstance : Group A) with mul_comm := @mul_comm' _ _ hcommutative }
  let e := cyclicFourAutomorphismEquiv hcommutative n coordinates
  let ambientAction := e.toMonoidHom.comp (MulAut.conjNormal (H := A))
  let H := ambientAction.range
  have hHmixed := cyclicFour_no_delta_mixed_excluded A hcommutative hselfCentralizing hnoEight n coordinates hdelta
  let action := ambientAction.comp U.subtype
  let Q := action.range
  let quotient := action.rangeRestrict
  have hQle : Q ≤ H := by
    rintro g ⟨u, rfl⟩
    exact ⟨u.val, rfl⟩
  have hQdelta : cyclicFourDelta n ∉ Q := fun h => hdelta (hQle h)
  have hQmixed : ∀ i : ZMod 2, cyclicFourElementaryHom n
      (Multiplicative.ofAdd i, (Multiplicative.ofAdd 1, Multiplicative.ofAdd 1)) ∉ Q :=
    fun i h => hHmixed i (hQle h)
  have hQrank := cyclicFour_scalar_free_action_rank n Q hQdelta hQmixed
  have hkernel : quotient.ker = A.comap U.subtype := by
    rw [MonoidHom.ker_rangeRestrict]
    change ambientAction.ker.comap U.subtype = A.comap U.subtype
    have hnative : ambientAction.ker = A := by
      have hk : (MulAut.conjNormal (H := A)).ker = A :=
        (conjNormal_ker_eq_centralizer A).trans hselfCentralizing
      ext s
      change e (MulAut.conjNormal (H := A) s) = 1 ↔ s ∈ A
      have hs : s ∈ A ↔ MulAut.conjNormal (H := A) s = 1 := (Subgroup.ext_iff.mp hk s).symm
      rw [hs, ← map_one e, e.injective.eq_iff]
    exact congrArg (Subgroup.comap U.subtype) hnative
  let embedding : quotient.ker →* A := {
    toFun b := ⟨b.val.val, hkernel.le b.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hinjective : Function.Injective embedding := by
    intro b c h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun a : A => a.val) h
  have hArank : pGeneratorRank 2 A ≤ 2 := by
    obtain ⟨X, hX, hcard⟩ := no_normal_eight_abelian_normal_two_generators hpgroup hnoEight A hcommutative
    exact (pGeneratorRank_le_generators Nat.prime_two (hpgroup.to_subgroup A) X hX).trans hcard
  have hcritical (hrank : pGeneratorRank 2 Q = 3) :
      ∃ u : U, ∃ b : quotient.ker, (b : U) = u ^ 2 ∧ ∀ a : A, embedding b ≠ a ^ 2 := by
    obtain ⟨q, hqC, hqOrder⟩ := cyclicFour_three_action_shear_involution n Q hrank
    have hqSquare : q.val ^ 2 = 1 := by
      have h : q ^ 2 = 1 := by simpa only [hqOrder] using pow_orderOf_eq_one q
      exact congrArg Subtype.val h
    have hqE : q.val ∈ cyclicFourE n := cyclicFourShearPreimage_square_one n q.val hqC hqSquare
    have hqne : q.val ≠ 1 := by
      intro h
      have hqone : q = 1 := Subtype.ext h
      rw [hqone, orderOf_one] at hqOrder
      norm_num at hqOrder
    obtain ⟨u, hu⟩ := q.property
    have hcentral (s : S) : Commute q.val (ambientAction s) :=
      cyclicFour_no_delta_E_central n H hdelta q.val hqE (hQle q.property) ⟨ambientAction s, ⟨s, rfl⟩⟩
    obtain ⟨a, ha, hprimitive, _⟩ := cyclicFour_central_action_primitive_square A hcommutative
      hselfCentralizing hnoEight n coordinates q.val hqE hqne hcentral u.val hu
    have hmem : u ^ 2 ∈ quotient.ker := by
      rw [hkernel]
      change (u.val ^ 2 : S) ∈ A
      exact ha ▸ a.property
    let b : quotient.ker := ⟨u ^ 2, hmem⟩
    have hb : embedding b = a := Subtype.ext ha.symm
    exact ⟨u, b, rfl, fun x => hb ▸ hprimitive x⟩
  exact abelian_kernel_three_action_primitive_square_four_generators (hpgroup.to_subgroup U)
    (hpgroup.to_subgroup A) quotient action.rangeRestrict_surjective embedding hinjective hArank hQrank hcritical

theorem rank_two_cyclic_times_four_scalar_free_ambient_four_generators {S : Type*} [Group S] [Finite S]
    (hpgroup : IsPGroup 2 S) (A : Subgroup S) [A.Normal]
    (hcommutative : IsMulCommutative A)
    (hselfCentralizing : Subgroup.centralizer (A : Set S) = A)
    (hnoEight : ∀ E : Subgroup S, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8)
    (n : ℕ) (coordinates : Additive A ≃+ CyclicFourSpace n)
    (hdelta : cyclicFourDelta n ∉
      ((cyclicFourAutomorphismEquiv hcommutative n coordinates).toMonoidHom.comp
        (MulAut.conjNormal (H := A))).range)
    (U : Subgroup S) : ∃ X : Finset S, X.card ≤ 4 ∧ Subgroup.closure (X : Set S) = U := by
  classical
  obtain ⟨X, hX, hcard⟩ := rank_two_cyclic_times_four_scalar_free_four_generators hpgroup A hcommutative
    hselfCentralizing hnoEight n coordinates hdelta U
  refine ⟨X.image U.subtype, Finset.card_image_le.trans hcard, ?_⟩
  rw [Finset.coe_image, ← MonoidHom.map_closure, hX, Subgroup.map_top]
  exact U.range_subtype

end CFSG.LargeEvenClassification.Helpers
