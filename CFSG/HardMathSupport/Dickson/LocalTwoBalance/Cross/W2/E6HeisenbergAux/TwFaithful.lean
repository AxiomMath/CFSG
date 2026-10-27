module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigidTest
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialOuterT
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialOuterThree
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ToralCentralizerGenerated

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley

set_option linter.unusedSectionVars false

open scoped Pointwise


theorem centralizer_twE6_trivial {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (h3 : ¬ 3 ∣ ℓ ^ f) (hq4 : 4 ≤ ℓ ^ f) {c : ModGL Tag.E6 (AlgebraicClosure K)}
    (hc : c ∈ adjointGroup Tag.E6 (AlgebraicClosure K))
    (h : ∀ x : twistedE6RootGroup K σ,
      Commute c (baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K))) :
    c = 1 := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  set L := AlgebraicClosure K with hL
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  set ι : K →+* L := algebraMap K L with hι
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ x, Fr x = x ^ (ℓ ^ f) := fun x => by rw [hFrdef, iterateFrobenius_def]
  have hg1C : (1 : ModGL TwistTag.E6.tag L) ∈ adjointGroup TwistTag.E6.tag L := one_mem _
  let D₁ : LangDatum TwistTag.E6.tag L := LangDatum.ofTwist TwistTag.E6 Fr (ℓ ^ f) hFr 1 hg1C
    (by rw [map_one, canonicalRep_one, one_mul])
  have hΦ : D₁.Φ = twistHom TwistTag.E6 L Fr := rfl
  have hfin := finite_model_twistedE6 hℓ hf hK hσ hFr D₁ hΦ
  obtain ⟨ρ, hρ⟩ := frobeniusOnRoots_proved TwistTag.E6.tag L D₁
  have hqpow : IsPrimePow D₁.q ∧ ((D₁.q : ℕ) : L) = 0 := by
    refine ⟨hℓ.isPrimePow.pow (by omega), ?_⟩
    change ((ℓ ^ f : ℕ) : L) = 0
    rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow (by omega)]
  let S₁ : LangSetup TwistTag.E6.tag L 3 :=
    D₁.toSetup 3 ρ hρ Nat.prime_three (Or.inr hq4) hqpow h3 hfin
  have hSq : S₁.D.q = ℓ ^ f := rfl
  set φ : twistedE6RootGroup K σ ≃* S₁.Γ := twistedE6EquivΓ hℓ hf hK hσ hFr D₁ hΦ with hφdef
  have hφ : ∀ x : twistedE6RootGroup K σ, ((φ x : S₁.Γ) : ModGL TwistTag.E6.tag L) =
      baseChangeGL ι (x : ModGL TwistTag.E6.tag K) := fun x =>
    (coe_twistedE6EquivΓ hℓ hf hK hσ hFr D₁ hΦ x).trans (by
      change (1 : ModGL TwistTag.E6.tag L)⁻¹ * _ * 1 = _
      rw [inv_one, one_mul, mul_one])
  have h3L : ((3 : ℕ) : L) ≠ 0 := by
    intro h0
    have hdvd : ℓ ∣ 3 := (CharP.cast_eq_zero_iff L ℓ 3).1 h0
    have hℓ3 : ℓ = 3 := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 hdvd
    exact h3 (hℓ3 ▸ dvd_pow_self ℓ (by omega))
  have : NeZero ((3 : ℕ) : L) := ⟨h3L⟩
  obtain ⟨ω₀, hω₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L 3
  set ω : Lˣ := (hω₀.isUnit (by norm_num)).unit with hωdef
  have hωord : orderOf ω = 3 := (IsPrimitiveRoot.coe_units_iff.1 hω₀).eq_orderOf.symm
  have hω3 : ω ^ 3 = 1 := by rw [← hωord]; exact pow_orderOf_eq_one ω
  have hω1 : ω ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hωord
    omega
  set q : ℕ := ℓ ^ f with hq
  have hq2 : q ^ 2 % 3 = 1 := by
    have h : q % 3 = 1 ∨ q % 3 = 2 := by omega
    rcases h with h | h <;> simp [Nat.pow_mod, h]
  have hFrω : Units.map Fr.toMonoidHom ω = ω ^ q :=
    Units.ext (by simp [hFr, Units.val_pow_eq_pow_val])
  have hFrωq : Units.map Fr.toMonoidHom (ω ^ q) = ω := by
    rw [map_pow, hFrω, ← pow_mul, ← pow_two, pow_eq_pow_mod _ hω3, hq2, pow_one]
  have hpair : ∀ i j : Fin TwistTag.E6.tag.rank, i ≠ j → TwistTag.E6.perm i = j →
      TwistTag.E6.perm j = i →
      rootDiagUnit TwistTag.E6.tag (fun k => if k = i then ω else if k = j then ω ^ q else 1) ∈
        S₁.D.torus := by
    intro i j hij hi hj
    set a : Fin TwistTag.E6.tag.rank → Lˣ := fun k => if k = i then ω else if k = j then ω ^ q
      else 1 with ha
    have ha_i : a i = ω := by simp [ha]
    have ha_j : a j = ω ^ q := by simp [ha, hij.symm]
    have ha_o : ∀ k, k ≠ i → k ≠ j → a k = 1 := fun k hki hkj => by simp [ha, hki, hkj]
    refine mem_twistedTorusOf.2 ⟨rootDiagUnit_mem_torusGroup _, ?_⟩
    have hn : S₁.D.n = 1 := canonicalRep_one _ _
    have hΦ' : S₁.D.Φ = twistHom TwistTag.E6 L Fr := rfl
    rw [hn, hΦ', inv_one, one_mul, mul_one, twistHom_rootDiagUnit_eq]
    congr 1
    funext k
    have hsymi : TwistTag.E6.perm.symm i = j := by rw [Equiv.symm_apply_eq]; exact hj.symm
    have hsymj : TwistTag.E6.perm.symm j = i := by rw [Equiv.symm_apply_eq]; exact hi.symm
    by_cases hki : k = i
    · rw [hki, hsymi, ha_j, ha_i]
      exact hFrωq
    by_cases hkj : k = j
    · rw [hkj, hsymj, ha_i, ha_j]
      exact hFrω
    · have h1 : TwistTag.E6.perm.symm k ≠ i := fun h => hkj (by
        rw [Equiv.symm_apply_eq] at h; rw [h, hi])
      have h2 : TwistTag.E6.perm.symm k ≠ j := fun h => hki (by
        rw [Equiv.symm_apply_eq] at h; rw [h, hj])
      rw [ha_o _ hki hkj, ha_o _ h1 h2, map_one]
  set a₁ : Fin TwistTag.E6.tag.rank → Lˣ := fun k => if k = 0 then ω else if k = 5 then ω ^ q
    else 1 with ha₁
  set a₂ : Fin TwistTag.E6.tag.rank → Lˣ := fun k => if k = 2 then ω else if k = 4 then ω ^ q
    else 1 with ha₂
  have hd₁T : rootDiagUnit TwistTag.E6.tag a₁ ∈ S₁.D.torus :=
    hpair 0 5 (by decide) (by decide) (by decide)
  have hd₂T : rootDiagUnit TwistTag.E6.tag a₂ ∈ S₁.D.torus :=
    hpair 2 4 (by decide) (by decide) (by decide)
  have hωq3 : (ω ^ q) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow]
  have ha₁3 : a₁ ^ 3 = 1 := funext fun k => by
    by_cases h0 : k = 0
    · simp [ha₁, h0, hω3]
    by_cases h5 : k = 5
    · simp [ha₁, h5, hωq3]
    · simp [ha₁, h0, h5]
  have ha₂3 : a₂ ^ 3 = 1 := funext fun k => by
    by_cases h0 : k = 2
    · simp [ha₂, h0, hω3]
    by_cases h5 : k = 4
    · simp [ha₂, h5, hωq3]
    · simp [ha₂, h0, h5]
  set d₁ := rootDiagUnit TwistTag.E6.tag a₁ with hd₁def
  set d₂ := rootDiagUnit TwistTag.E6.tag a₂ with hd₂def
  have hd₁3 : d₁ ^ 3 = 1 := by rw [hd₁def, rootDiagUnit_pow, ha₁3, rootDiagUnit_one]
  have hd₂3 : d₂ ^ 3 = 1 := by rw [hd₂def, rootDiagUnit_pow, ha₂3, rootDiagUnit_one]
  have hd₁1 : d₁ ≠ 1 := by
    intro h1
    have h2 : a₁ = 1 :=
      CFSG.LieType.Chevalley.rootDiagUnit_injective (h1.trans rootDiagUnit_one.symm)
    have h3' := congrFun h2 0
    simp [ha₁] at h3'
    exact hω1 h3'
  have hcomm : Commute d₁ d₂ :=
    (Commute.all a₁ a₂).map (rootDiagUnitHom TwistTag.E6.tag L)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord₁ : orderOf d₁ = 3 := orderOf_eq_prime hd₁3 hd₁1
  have hA3 : Nat.card (Subgroup.zpowers d₁) = 3 := by rw [Nat.card_zpowers, hord₁]
  have hAfin : (Subgroup.zpowers d₁ : Set (ModGL TwistTag.E6.tag L)).Finite :=
    finite_zpowers.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨3, by norm_num, hd₁3⟩)
  have hBfin : (Subgroup.zpowers d₂ : Set (ModGL TwistTag.E6.tag L)).Finite :=
    finite_zpowers.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨3, by norm_num, hd₂3⟩)
  have hcommAB : ∀ x ∈ Subgroup.zpowers d₁, ∀ y ∈ Subgroup.zpowers d₂, x * y = y * x := by
    intro x hx y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (hcomm.zpow_zpow k m).eq
  set D0 : Subgroup (ModGL TwistTag.E6.tag L) := Subgroup.zpowers d₁ ⊔ Subgroup.zpowers d₂
    with hD0
  have hAnorm : Subgroup.zpowers d₁ ≤
      Subgroup.normalizer (Subgroup.zpowers d₂ : Set (ModGL TwistTag.E6.tag L)) := by
    intro x hx
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hcommAB x hx y hy).symm
  have hmul : (D0 : Set (ModGL TwistTag.E6.tag L)) =
      (Subgroup.zpowers d₁ : Set (ModGL TwistTag.E6.tag L)) *
        (Subgroup.zpowers d₂ : Set (ModGL TwistTag.E6.tag L)) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hAnorm
  haveI hD0fin : Finite D0 := by
    have : (D0 : Set (ModGL TwistTag.E6.tag L)).Finite := by
      rw [hmul]
      exact hAfin.mul hBfin
    exact this.to_subtype
  have hD0pow : ∀ x ∈ D0, x ^ 3 = 1 := by
    intro x hx
    rw [← SetLike.mem_coe, hmul] at hx
    obtain ⟨u, hu, v, hv, rfl⟩ := hx
    have hcuv : Commute u v := hcommAB u hu v hv
    rw [hcuv.mul_pow]
    have h1 : u ^ 3 = 1 := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hd₁3, one_zpow]
    have h2 : v ^ 3 = 1 := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hd₂3, one_zpow]
    rw [h1, h2, one_mul]
  have hD0T : D0 ≤ S₁.D.torus :=
    sup_le (Subgroup.zpowers_le.2 hd₁T) (Subgroup.zpowers_le.2 hd₂T)
  have hD0card : 3 < Nat.card D0 := by
    have hAle : Subgroup.zpowers d₁ ≤ D0 := le_sup_left
    have hge : 3 ≤ Nat.card D0 := hA3 ▸ Subgroup.card_le_of_le hAle
    by_contra hlt
    have heq : Nat.card D0 = 3 := by omega
    have hAeq : Subgroup.zpowers d₁ = D0 :=
      Subgroup.eq_of_le_of_card_ge hAle (le_of_eq (by rw [hA3, heq]))
    have hd₂mem : d₂ ∈ D0 := (le_sup_right : Subgroup.zpowers d₂ ≤ D0) (Subgroup.mem_zpowers d₂)
    rw [← hAeq] at hd₂mem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hd₂mem
    have h1 : rootDiagUnit TwistTag.E6.tag (a₁ ^ k) = rootDiagUnit TwistTag.E6.tag a₂ := by
      rw [← hd₂def, ← hk, hd₁def]
      exact map_zpow (rootDiagUnitHom TwistTag.E6.tag L) a₁ k
    have h2 := congrFun (CFSG.LieType.Chevalley.rootDiagUnit_injective h1) 2
    simp [ha₁, ha₂] at h2
    exact hω1 h2.symm
  have hz : ∀ x ∈ bigComponentSet S₁ D0, Commute c x := by
    intro x hx
    obtain ⟨y, hy⟩ := φ.surjective ⟨x, bigComponentSet_subset_Γ S₁ D0 hx⟩
    have h1 := hφ y
    rw [hy] at h1
    exact (congrArg (fun m => Commute c m) h1.symm).mp (h y)
  have hall := commute_adjointGroup_of_torus anyKindCommuteT_holds threeBigComponents_holds S₁
    (by decide) (by rw [hSq]; exact hq4) hD0T hD0pow hD0card hz
  have hcent : (⟨c, hc⟩ : adjointGroup Tag.E6 L) ∈ Subgroup.center (adjointGroup Tag.E6 L) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hall g.1 g.2).symm.eq
  rw [center_adjointGroup_eq_bot_field, Subgroup.mem_bot] at hcent
  exact congrArg Subtype.val hcent

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis
