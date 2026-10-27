module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.BadThreeNonsplit
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeNonsplit

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.LieType.SeitzGeneration CFSG.LieType.Chevalley
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.TauCetiBridge CFSG.RankThree.Chevalley

theorem localDeltaIn_eq_bot_of_core_eq_bot {M : Type*} [Group M] {p : ℕ} {H D : Subgroup M}
    {d : M} (hd : d ∈ D) (hd1 : d ≠ 1)
    (h : GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({d} : Set M)) = ⊥) :
    localDeltaIn p H D = ⊥ :=
  eq_bot_iff.2 fun _ hg => h ▸ le_core_of_mem_localDeltaIn hg hd hd1

section Two

variable {τ : Tag} {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem not_hasSplitToralPlane_of_card_two (hK : Nat.card K = 2) {p : ℕ} (hp : p.Prime)
    (D : Subgroup (MulAut (adjointGroup τ K))) : ¬ HasSplitToralPlane p D := by
  rintro ⟨E, -, -, hEc, ψ, hψ⟩
  have hunits : ∀ u : Kˣ, u = 1 := by
    have h1 : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK]
    intro u
    exact (Nat.card_eq_one_iff_unique.1 h1).1.elim u 1
  have htriv : ∀ y ∈ E, y = 1 := by
    intro y hy
    obtain ⟨a, ha⟩ := hψ ⟨y, hy, rfl⟩
    have ha1 : a = 1 := funext fun i => hunits (a i)
    have hy1 : (MulAut.conj ψ).toMonoidHom y = 1 := by
      rw [← ha, ha1, map_one]
    exact (MulAut.conj ψ).injective (hy1.trans (map_one _).symm)
  have hbot : E = ⊥ := (Subgroup.eq_bot_iff_forall E).2 htriv
  rw [hbot, Subgroup.card_bot] at hEc
  have := hp.two_le
  nlinarith

end Two

@[expose] def SmallQThreeF4 : Prop :=
  ∀ (K : Type) [Field K] [Finite K], (Nat.card K = 2 ∨ Nat.card K = 4) →
    ∀ D : Subgroup (MulAut (adjointGroup Tag.F4 K)), IsElemAbelian 3 D → Nat.card D = 3 ^ 3 →
      D ≤ innerAut (adjointGroup Tag.F4 K) → ¬ HasSplitToralPlane 3 D →
      ∀ H : Subgroup (MulAut (adjointGroup Tag.F4 K)), innerAut (adjointGroup Tag.F4 K) ≤ H →
        D ≤ Subgroup.normalizer (H : Set (MulAut (adjointGroup Tag.F4 K))) →
          localDeltaIn 3 H D = ⊥

@[expose] def SmallQThreeE6 : Prop :=
  ∀ (K : Type) [Field K] [Finite K], (Nat.card K = 2 ∨ Nat.card K = 4) →
    ∀ D : Subgroup (MulAut (adjointGroup Tag.E6 K)), IsElemAbelian 3 D → Nat.card D = 3 ^ 3 →
      D ≤ innerAut (adjointGroup Tag.E6 K) → ¬ HasSplitToralPlane 3 D →
      ∀ H : Subgroup (MulAut (adjointGroup Tag.E6 K)), innerAut (adjointGroup Tag.E6 K) ≤ H →
        D ≤ Subgroup.normalizer (H : Set (MulAut (adjointGroup Tag.E6 K))) →
          localDeltaIn 3 H D = ⊥

@[expose] def SmallQThreeE6Diag :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 4 →
    ∀ D : Subgroup (MulAut (adjointGroup Tag.E6 K)), IsElemAbelian 3 D → Nat.card D = 3 ^ 3 →
      D ≤ e6Inndiag K → ¬ D ≤ innerAut (adjointGroup Tag.E6 K) → ¬ HasSplitToralPlane 3 D →
      ∀ H : Subgroup (MulAut (adjointGroup Tag.E6 K)), innerAut (adjointGroup Tag.E6 K) ≤ H →
        D ≤ Subgroup.normalizer (H : Set (MulAut (adjointGroup Tag.E6 K))) →
          localDeltaIn 3 H D = ⊥

@[expose] def SmallQThreeTwE6 :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 4 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ 2) →
    IsInnerLocallyBalanced 3 (twistedE6RootGroup K σ)

@[expose] def SmallQThreeTwE6Diag :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 4 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ 2) →
    ∀ D : Subgroup (MulAut (twistedE6RootGroup K σ)), IsElemAbelian 3 D → Nat.card D = 3 ^ 3 →
      D ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ → ¬ D ≤ innerAut (twistedE6RootGroup K σ) →
      ∀ H : Subgroup (MulAut (twistedE6RootGroup K σ)), innerAut (twistedE6RootGroup K σ) ≤ H →
        D ≤ Subgroup.normalizer (H : Set (MulAut (twistedE6RootGroup K σ))) →
          localDeltaIn 3 H D = ⊥

@[expose] def SmallQThreeE7 : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
    ∀ D : Subgroup (MulAut (adjointGroup Tag.E7 K)), IsElemAbelian 3 D → Nat.card D = 3 ^ 3 →
      D ≤ innerAut (adjointGroup Tag.E7 K) → ¬ HasSplitToralPlane 3 D →
      ∀ H : Subgroup (MulAut (adjointGroup Tag.E7 K)), innerAut (adjointGroup Tag.E7 K) ≤ H →
        D ≤ Subgroup.normalizer (H : Set (MulAut (adjointGroup Tag.E7 K))) →
          localDeltaIn 3 H D = ⊥

@[expose] def SmallQThreeE8 : Prop :=
  ∀ (K : Type) [Field K] [Finite K], (Nat.card K = 2 ∨ Nat.card K = 4) →
    ∀ D : Subgroup (MulAut (adjointGroup Tag.E8 K)), IsElemAbelian 3 D → Nat.card D = 3 ^ 3 →
      D ≤ innerAut (adjointGroup Tag.E8 K) → ¬ HasSplitToralPlane 3 D →
      ∀ H : Subgroup (MulAut (adjointGroup Tag.E8 K)), innerAut (adjointGroup Tag.E8 K) ≤ H →
        D ≤ Subgroup.normalizer (H : Set (MulAut (adjointGroup Tag.E8 K))) →
          localDeltaIn 3 H D = ⊥

section Splits


theorem f4ThreeInnerNonsplit_of_smallQ
    (hlarge : ∀ (K : Type) [Field K] [Finite K], ¬ 3 ∣ Nat.card K → Nat.card K ≠ 2 →
      Nat.card K ≠ 4 → ∀ D : Subgroup (MulAut (adjointGroup Tag.F4 K)), IsElemAbelian 3 D →
        Nat.card D = 3 ^ 3 → D ≤ innerAut (adjointGroup Tag.F4 K) →
        ¬ HasSplitToralPlane 3 D →
        ∀ H : Subgroup (MulAut (adjointGroup Tag.F4 K)), innerAut (adjointGroup Tag.F4 K) ≤ H →
          D ≤ Subgroup.normalizer (H : Set (MulAut (adjointGroup Tag.F4 K))) →
            localDeltaIn 3 H D = ⊥)
    (hsmall : SmallQThreeF4) : F4ThreeInnerNonsplit := by
  intro K _ _ h3 D hD hcard hDin hs H hH hDH
  by_cases h24 : Nat.card K = 2 ∨ Nat.card K = 4
  · exact hsmall K h24 D hD hcard hDin hs H hH hDH
  · push Not at h24
    exact hlarge K h3 h24.1 h24.2 D hD hcard hDin hs H hH hDH

theorem e6ThreeInnerNonsplit_of_smallQ
    (hlarge : ∀ ℓ f : ℕ, ℓ.Prime → ℓ ≠ 3 → 1 ≤ f → ℓ ^ f ≠ 2 → ℓ ^ f ≠ 4 →
      ∀ (K : Type) [Field K] [Finite K], Nat.card K = ℓ ^ f →
      ∀ D : Subgroup (MulAut (adjointGroup Tag.E6 K)), IsElemAbelian 3 D → Nat.card D = 3 ^ 3 →
        D ≤ innerAut (adjointGroup Tag.E6 K) → ¬ HasSplitToralPlane 3 D →
        ∀ H : Subgroup (MulAut (adjointGroup Tag.E6 K)), innerAut (adjointGroup Tag.E6 K) ≤ H →
          D ≤ Subgroup.normalizer (H : Set (MulAut (adjointGroup Tag.E6 K))) →
            localDeltaIn 3 H D = ⊥)
    (hsmall : SmallQThreeE6) : E6ThreeInnerNonsplit := by
  intro ℓ f hℓ hℓ3 hf K _ _ hK D hD hcard hDin hs H hH hDH
  by_cases h24 : ℓ ^ f = 2 ∨ ℓ ^ f = 4
  · exact hsmall K (hK ▸ h24) D hD hcard hDin hs H hH hDH
  · push Not at h24
    exact hlarge ℓ f hℓ hℓ3 hf h24.1 h24.2 K hK D hD hcard hDin hs H hH hDH

theorem e6ThreeDiagonalNonsplit_of_smallQ
    (hlarge : ∀ ℓ f : ℕ, ℓ.Prime → ℓ ≠ 3 → 1 ≤ f → 3 ∣ ℓ ^ f - 1 → ℓ ^ f ≠ 4 →
      ∀ (K : Type) [Field K] [Finite K], Nat.card K = ℓ ^ f →
      ∀ D : Subgroup (MulAut (adjointGroup Tag.E6 K)), IsElemAbelian 3 D → Nat.card D = 3 ^ 3 →
        D ≤ e6Inndiag K → ¬ D ≤ innerAut (adjointGroup Tag.E6 K) → ¬ HasSplitToralPlane 3 D →
        ∀ H : Subgroup (MulAut (adjointGroup Tag.E6 K)), innerAut (adjointGroup Tag.E6 K) ≤ H →
          D ≤ Subgroup.normalizer (H : Set (MulAut (adjointGroup Tag.E6 K))) →
            localDeltaIn 3 H D = ⊥)
    (hsmall : SmallQThreeE6Diag) : E6ThreeDiagonalNonsplit := by
  intro ℓ f hℓ hℓ3 hf h3 K _ _ hK D hD hcard hDd hDin hs H hH hDH
  by_cases h4 : ℓ ^ f = 4
  · exact hsmall K (hK.trans h4) D hD hcard hDd hDin hs H hH hDH
  · exact hlarge ℓ f hℓ hℓ3 hf h3 h4 K hK D hD hcard hDd hDin hs H hH hDH

theorem e7ThreeInnerNonsplit_of_smallQ
    (hlarge : ∀ ℓ f : ℕ, ℓ.Prime → ℓ ≠ 3 → 1 ≤ f → ℓ ^ f ≠ 2 →
      ∀ (K : Type) [Field K] [Finite K], Nat.card K = ℓ ^ f →
      ∀ D : Subgroup (MulAut (adjointGroup Tag.E7 K)), IsElemAbelian 3 D → Nat.card D = 3 ^ 3 →
        D ≤ innerAut (adjointGroup Tag.E7 K) → ¬ HasSplitToralPlane 3 D →
        ∀ H : Subgroup (MulAut (adjointGroup Tag.E7 K)), innerAut (adjointGroup Tag.E7 K) ≤ H →
          D ≤ Subgroup.normalizer (H : Set (MulAut (adjointGroup Tag.E7 K))) →
            localDeltaIn 3 H D = ⊥)
    (hsmall : SmallQThreeE7) : E7ThreeInnerNonsplit := by
  intro ℓ f hℓ hℓ3 hf K _ _ hK D hD hcard hDin hs H hH hDH
  by_cases h2 : ℓ ^ f = 2
  · exact hsmall K (hK.trans h2) D hD hcard hDin hs H hH hDH
  · exact hlarge ℓ f hℓ hℓ3 hf h2 K hK D hD hcard hDin hs H hH hDH

theorem e8ThreeInnerNonsplit_of_smallQ
    (hlarge : ∀ ℓ f : ℕ, ℓ.Prime → ℓ ≠ 3 → 1 ≤ f → ℓ ^ f ≠ 2 → ℓ ^ f ≠ 4 →
      ∀ (K : Type) [Field K] [Finite K], Nat.card K = ℓ ^ f →
      ∀ D : Subgroup (MulAut (adjointGroup Tag.E8 K)), IsElemAbelian 3 D → Nat.card D = 3 ^ 3 →
        D ≤ innerAut (adjointGroup Tag.E8 K) → ¬ HasSplitToralPlane 3 D →
        ∀ H : Subgroup (MulAut (adjointGroup Tag.E8 K)), innerAut (adjointGroup Tag.E8 K) ≤ H →
          D ≤ Subgroup.normalizer (H : Set (MulAut (adjointGroup Tag.E8 K))) →
            localDeltaIn 3 H D = ⊥)
    (hsmall : SmallQThreeE8) : E8ThreeInnerNonsplit := by
  intro ℓ f hℓ hℓ3 hf K _ _ hK D hD hcard hDin hs H hH hDH
  by_cases h24 : ℓ ^ f = 2 ∨ ℓ ^ f = 4
  · exact hsmall K (hK ▸ h24) D hD hcard hDin hs H hH hDH
  · push Not at h24
    exact hlarge ℓ f hℓ hℓ3 hf h24.1 h24.2 K hK D hD hcard hDin hs H hH hDH

end Splits

theorem pow_two_mul_eq_four {ℓ f : ℕ} (h : ℓ ^ f = 2) : ℓ ^ (2 * f) = 4 := by
  rw [mul_comm, pow_mul, h]
  norm_num

section TwistedSplits


theorem twistedE6ThreeDiagonal_of_smallQ
    (hlarge : ∀ ℓ f : ℕ, ℓ.Prime → ℓ ≠ 3 → 1 ≤ f → 3 ∣ ℓ ^ f + 1 → ℓ ^ f ≠ 2 →
      ∀ (K : Type) [Field K] [Finite K], Nat.card K = ℓ ^ (2 * f) →
      ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) →
      ∀ D : Subgroup (MulAut (twistedE6RootGroup K σ)), IsElemAbelian 3 D →
        Nat.card D = 3 ^ 3 → D ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ →
        ¬ D ≤ innerAut (twistedE6RootGroup K σ) →
        ∀ H : Subgroup (MulAut (twistedE6RootGroup K σ)),
          innerAut (twistedE6RootGroup K σ) ≤ H →
          D ≤ Subgroup.normalizer (H : Set (MulAut (twistedE6RootGroup K σ))) →
            localDeltaIn 3 H D = ⊥)
    (hsmall : SmallQThreeTwE6Diag) : TwistedE6ThreeDiagonal := by
  intro ℓ f hℓ hℓ3 hf h3 K _ _ hK σ hσ D hD hcard hDd hDin H hH hDH
  by_cases h2 : ℓ ^ f = 2
  · exact hsmall K (hK.trans (pow_two_mul_eq_four h2)) σ (fun c => by rw [hσ, h2]) D hD hcard
      hDd hDin H hH hDH
  · exact hlarge ℓ f hℓ hℓ3 hf h3 h2 K hK σ hσ D hD hcard hDd hDin H hH hDH

theorem crossCharInnerAt_twistedE6_three_of_smallQ
    (hlarge : CrossCharInnerAt .twistedE6 fun idx p =>
      p = 3 ∧ ∃ q : TauCeti.PrimePower, idx.1 = .twistedE6 q ∧ q.card ≠ 2)
    (hsmall : SmallQThreeTwE6) : CrossCharInnerAt .twistedE6 fun _ p => p = 3 := by
  rintro ⟨d, hv⟩ hk p hp hp2 hc rfl
  obtain ⟨q, hq⟩ : ∃ q, d = TauCeti.LieTypeIndex.twistedE6 q := hk
  subst hq
  by_cases hq2 : q.card = 2
  · obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
    have hpe : q.p ^ q.exponent = 2 := (TauCeti.PrimePower.card_def q).symm.trans hq2
    have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK, hpe]; norm_num)
    refine IsInnerLocallyBalanced.of_mulEquiv e (hsmall K (by rw [hK, hpe]; norm_num) σ
      (fun c => by rw [hσ, hpe]))
  · exact hlarge ⟨_, hv⟩ ⟨q, rfl⟩ 3 hp hp2 hc ⟨rfl, q, rfl, hq2⟩

end TwistedSplits

@[expose] def InnerOneBalanceThree (K : Type*) [Group K] : Prop :=
  ∀ d ∈ innerAut K, d ^ 3 = 1 → d ≠ 1 → ∀ H : Subgroup (MulAut K), innerAut K ≤ H →
    GLAPPrimeCoreOf 3 (H ⊓ Subgroup.centralizer ({d} : Set (MulAut K))) = ⊥

theorem localDeltaIn_eq_bot_of_innerOneBalanceThree {K : Type*} [Group K]
    (h : InnerOneBalanceThree K) {D : Subgroup (MulAut K)} (hD : IsElemAbelian 3 D)
    {d : MulAut K} (hdD : d ∈ D) (hdin : d ∈ innerAut K) (hd1 : d ≠ 1)
    {H : Subgroup (MulAut K)} (hH : innerAut K ≤ H) : localDeltaIn 3 H D = ⊥ :=
  localDeltaIn_eq_bot_of_core_eq_bot hdD hd1 (h d hdin (hD.2 d hdD) hd1 H hH)

theorem exists_ne_one_of_card_eq_27 {M : Type*} [Group M] {D : Subgroup M}
    (hcard : Nat.card D = 3 ^ 3) : ∃ d ∈ D, d ≠ 1 := by
  by_contra hall
  push Not at hall
  have : D = ⊥ := (Subgroup.eq_bot_iff_forall D).2 hall
  rw [this, Subgroup.card_bot] at hcard
  norm_num at hcard

section OneBalance


theorem smallQThreeF4_of_innerOneBalance (h : ∀ (K : Type) [Field K] [Finite K],
    (Nat.card K = 2 ∨ Nat.card K = 4) → InnerOneBalanceThree (adjointGroup Tag.F4 K)) :
    SmallQThreeF4 := by
  intro K _ _ hK D hD hcard hDin _ H hH _
  obtain ⟨d, hdD, hd1⟩ := exists_ne_one_of_card_eq_27 hcard
  exact localDeltaIn_eq_bot_of_innerOneBalanceThree (h K hK) hD hdD (hDin hdD) hd1 hH

theorem smallQThreeE6_of_innerOneBalance (h : ∀ (K : Type) [Field K] [Finite K],
    (Nat.card K = 2 ∨ Nat.card K = 4) → InnerOneBalanceThree (adjointGroup Tag.E6 K)) :
    SmallQThreeE6 := by
  intro K _ _ hK D hD hcard hDin _ H hH _
  obtain ⟨d, hdD, hd1⟩ := exists_ne_one_of_card_eq_27 hcard
  exact localDeltaIn_eq_bot_of_innerOneBalanceThree (h K hK) hD hdD (hDin hdD) hd1 hH

theorem smallQThreeE7_of_innerOneBalance (h : ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = 2 → InnerOneBalanceThree (adjointGroup Tag.E7 K)) : SmallQThreeE7 := by
  intro K _ _ hK D hD hcard hDin _ H hH _
  obtain ⟨d, hdD, hd1⟩ := exists_ne_one_of_card_eq_27 hcard
  exact localDeltaIn_eq_bot_of_innerOneBalanceThree (h K hK) hD hdD (hDin hdD) hd1 hH

theorem smallQThreeE8_of_innerOneBalance (h : ∀ (K : Type) [Field K] [Finite K],
    (Nat.card K = 2 ∨ Nat.card K = 4) → InnerOneBalanceThree (adjointGroup Tag.E8 K)) :
    SmallQThreeE8 := by
  intro K _ _ hK D hD hcard hDin _ H hH _
  obtain ⟨d, hdD, hd1⟩ := exists_ne_one_of_card_eq_27 hcard
  exact localDeltaIn_eq_bot_of_innerOneBalanceThree (h K hK) hD hdD (hDin hdD) hd1 hH

end OneBalance

section OneBalanceTwisted


theorem smallQThreeTwE6_of_innerOneBalance (h : ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = 4 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ 2) →
      InnerOneBalanceThree (twistedE6RootGroup K σ)) : SmallQThreeTwE6 := by
  intro K _ _ hK σ hσ D hD hcard hDin H hH _
  obtain ⟨d, hdD, hd1⟩ := exists_ne_one_of_card_eq_27 hcard
  exact localDeltaIn_eq_bot_of_innerOneBalanceThree (h K hK σ hσ) hD hdD (hDin hdD) hd1 hH

theorem exists_inner_ne_one_of_le_e6Inndiag (K : Type) [Field K] [Finite K]
    {D : Subgroup (MulAut (adjointGroup Tag.E6 K))} (hcard : Nat.card D = 3 ^ 3)
    (hDd : D ≤ e6Inndiag K) : ∃ d ∈ D, d ∈ innerAut (adjointGroup Tag.E6 K) ∧ d ≠ 1 := by
  classical
  obtain ⟨Φ, -, hker, hdvd⟩ := exists_outer_hom_E (K := K) (τ := Tag.E6) (Or.inl rfl)
  set N := CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup Tag.E6 K)
    with hN
  set π := QuotientGroup.mk' N with hπ
  by_contra hno
  push Not at hno
  have hinj : Function.Injective (π.domRestrict D) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨d, hd⟩ hk
    have hk' : π d = 1 := hk
    have hdN : d ∈ N := (QuotientGroup.eq_one_iff d).1 hk'
    rw [Subgroup.mem_bot]
    exact Subtype.ext (hno d hd hdN)
  have himg : D.map π ≤ Φ.ker := by
    rintro _ ⟨d, hd, rfl⟩
    have hdd : d ∈ ((N ⊔ (rootDiagAutHom Tag.E6 K).range : Subgroup _) : Set _) := hDd hd
    rw [Subgroup.normal_mul] at hdd
    obtain ⟨i, hi, r, ⟨a, rfl⟩, rfl⟩ := hdd
    rw [hker]
    refine ⟨a, ?_⟩
    change π (rootDiagAutHom Tag.E6 K a) = π (i * rootDiagAutHom Tag.E6 K a)
    have hpi : π i = 1 := (QuotientGroup.eq_one_iff i).2 hi
    rw [map_mul, hpi, one_mul]
  have h3 : Nat.card Φ.ker ∣ 3 := by
    have h := hdvd
    rwa [show Tag.E6.cartan.det.natAbs = 3 by rw [det_cartan_E6]; rfl] at h
  have hle : Nat.card (D.map π) ≤ 3 :=
    (Subgroup.card_le_of_le himg).trans (Nat.le_of_dvd (by norm_num) h3)
  have heq : Nat.card (D.map π) = Nat.card D := by
    rw [← MonoidHom.domRestrict_range]
    exact Nat.card_range_of_injective hinj
  rw [heq, hcard] at hle
  norm_num at hle

theorem smallQThreeE6Diag_of_innerOneBalance (h : ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = 4 → InnerOneBalanceThree (adjointGroup Tag.E6 K)) : SmallQThreeE6Diag := by
  intro K _ _ hK D hD hcard hDd _ _ H hH _
  obtain ⟨d, hdD, hdin, hd1⟩ := exists_inner_ne_one_of_le_e6Inndiag K hcard hDd
  exact localDeltaIn_eq_bot_of_innerOneBalanceThree (h K hK) hD hdD hdin hd1 hH

theorem card_twistedE6Diag_le_nine (K : Type) [Field K] [Finite K] (hK : Nat.card K = 4)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2) : Nat.card (twistedE6Diag K σ) ≤ 9 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hunits : ∀ a : Fin TwistTag.E6.foldedTag.rank,
      Nat.card (orbitField TwistTag.E6 K σ.toRingHom a)ˣ ≤ 3 := by
    intro a
    set ι : orbitField TwistTag.E6 K σ.toRingHom a →* K :=
      (orbitField TwistTag.E6 K σ.toRingHom a).subtype.toMonoidHom with hι
    have hinj : Function.Injective (Units.map ι) := fun u v h =>
      Units.ext (Subtype.ext (by
        have h1 := congrArg (fun w : Kˣ => (w : K)) h
        simp only [Units.coe_map] at h1
        exact h1))
    calc Nat.card (orbitField TwistTag.E6 K σ.toRingHom a)ˣ ≤ Nat.card Kˣ :=
          Nat.card_le_card_of_injective _ hinj
      _ = 3 := by rw [Nat.card_units, hK]
  have hfix : ∀ a : Fin TwistTag.E6.foldedTag.rank, (TwistTag.E6.orbit a).card = 1 →
      Nat.card (orbitField TwistTag.E6 K σ.toRingHom a)ˣ ≤ 1 := by
    intro a ha
    have : Finite (orbitField TwistTag.E6 K σ.toRingHom a)ˣ := inferInstance
    refine Finite.card_le_one_iff_subsingleton.2 ⟨fun u v => ?_⟩
    have h1 : ∀ w : (orbitField TwistTag.E6 K σ.toRingHom a)ˣ, w = 1 := by
      intro w
      have hw : (σ.toRingHom ^ (TwistTag.E6.orbit a).card) ((w : orbitField TwistTag.E6 K
          σ.toRingHom a) : K) = (w : orbitField TwistTag.E6 K σ.toRingHom a) :=
        mem_orbitField.1 (w : orbitField TwistTag.E6 K σ.toRingHom a).2
      rw [ha, pow_one] at hw
      change σ _ = _ at hw
      rw [hσ] at hw
      have h0 : ((w : orbitField TwistTag.E6 K σ.toRingHom a) : K) ≠ 0 := by
        intro h0
        have := w.ne_zero
        exact this (Subtype.ext h0)
      have h2 : ((w : orbitField TwistTag.E6 K σ.toRingHom a) : K) = 1 := by
        have h3 : ((w : orbitField TwistTag.E6 K σ.toRingHom a) : K) *
            (((w : orbitField TwistTag.E6 K σ.toRingHom a) : K) - 1) = 0 := by
          rw [mul_sub, mul_one, ← pow_two, hw, sub_self]
        rcases mul_eq_zero.1 h3 with h4 | h4
        · exact absurd h4 h0
        · exact sub_eq_zero.1 h4
      exact Units.ext (Subtype.ext h2)
    rw [h1 u, h1 v]
  have hdom : Nat.card ((a : Fin TwistTag.E6.foldedTag.rank) →
      (orbitField TwistTag.E6 K σ.toRingHom a)ˣ) ≤ 9 := by
    rw [Nat.card_pi]
    change ∏ a : Fin 4, Nat.card (orbitField TwistTag.E6 K σ.toRingHom a)ˣ ≤ 9
    rw [Fin.prod_univ_four]
    have h0 := hunits 0
    have h1 := hunits 1
    have h2 := hfix 2 (by decide)
    have h3 := hfix 3 (by decide)
    calc _ ≤ 3 * 3 * 1 * 1 := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h0 h1) h2) h3
      _ = 9 := by norm_num
  calc Nat.card (twistedE6Diag K σ) ≤ Nat.card ((a : Fin TwistTag.E6.foldedTag.rank) →
        (orbitField TwistTag.E6 K σ.toRingHom a)ˣ) :=
      Nat.card_le_card_of_surjective _
        (compatDiagAutHom TwistTag.E6 K σ.toRingHom).rangeRestrict_surjective
    _ ≤ 9 := hdom

theorem exists_inner_ne_one_of_le_twistedE6Inndiag (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 4) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2)
    {D : Subgroup (MulAut (twistedE6RootGroup K σ))} (hcard : Nat.card D = 3 ^ 3)
    (hDd : D ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ) :
    ∃ d ∈ D, d ∈ innerAut (twistedE6RootGroup K σ) ∧ d ≠ 1 := by
  classical
  set N := twistedE6Inn K σ with hN
  have : N.Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal (twistedE6RootGroup K σ)
  set π := QuotientGroup.mk' N with hπ
  by_contra hno
  push Not at hno
  have hinj : Function.Injective (π.domRestrict D) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨d, hd⟩ hk
    have hk' : π d = 1 := hk
    have hdN : d ∈ N := (QuotientGroup.eq_one_iff d).1 hk'
    rw [Subgroup.mem_bot]
    exact Subtype.ext (hno d hd hdN)
  have himg : D.map π ≤ (twistedE6Diag K σ).map π := by
    rintro _ ⟨d, hd, rfl⟩
    have hdd : d ∈ ((N ⊔ twistedE6Diag K σ : Subgroup _) : Set _) := hDd hd
    rw [Subgroup.normal_mul] at hdd
    obtain ⟨i, hi, r, hr, rfl⟩ := hdd
    refine ⟨r, hr, ?_⟩
    have hpi : π i = 1 := (QuotientGroup.eq_one_iff i).2 hi
    change π r = π (i * r)
    rw [map_mul, hpi, one_mul]
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have : Finite (MulAut (twistedE6RootGroup K σ)) := inferInstance
  have hle : Nat.card (D.map π) ≤ 9 := by
    calc Nat.card (D.map π) ≤ Nat.card ((twistedE6Diag K σ).map π) :=
          Subgroup.card_le_of_le himg
      _ ≤ Nat.card (twistedE6Diag K σ) :=
          Nat.card_le_card_of_surjective _ (π.subgroupMap_surjective (twistedE6Diag K σ))
      _ ≤ 9 := card_twistedE6Diag_le_nine K hK σ hσ
  have heq : Nat.card (D.map π) = Nat.card D := by
    rw [← MonoidHom.domRestrict_range]
    exact Nat.card_range_of_injective hinj
  rw [heq, hcard] at hle
  norm_num at hle

theorem smallQThreeTwE6Diag_of_innerOneBalance (h : ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = 4 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ 2) →
      InnerOneBalanceThree (twistedE6RootGroup K σ)) : SmallQThreeTwE6Diag := by
  intro K _ _ hK σ hσ D hD hcard hDd _ H hH _
  obtain ⟨d, hdD, hdin, hd1⟩ := exists_inner_ne_one_of_le_twistedE6Inndiag K hK σ hσ hcard hDd
  exact localDeltaIn_eq_bot_of_innerOneBalanceThree (h K hK σ hσ) hD hdD hdin hd1 hH

@[expose] def SmallQThreeOneBalance : Prop :=
  (∀ (K : Type) [Field K] [Finite K], (Nat.card K = 2 ∨ Nat.card K = 4) →
      InnerOneBalanceThree (adjointGroup Tag.F4 K)) ∧
    (∀ (K : Type) [Field K] [Finite K], (Nat.card K = 2 ∨ Nat.card K = 4) →
      InnerOneBalanceThree (adjointGroup Tag.E6 K)) ∧
    (∀ (K : Type) [Field K] [Finite K], Nat.card K = 4 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ 2) →
      InnerOneBalanceThree (twistedE6RootGroup K σ)) ∧
    (∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
      InnerOneBalanceThree (adjointGroup Tag.E7 K)) ∧
    (∀ (K : Type) [Field K] [Finite K], (Nat.card K = 2 ∨ Nat.card K = 4) →
      InnerOneBalanceThree (adjointGroup Tag.E8 K))

theorem smallQThree_of_oneBalance (h : SmallQThreeOneBalance) :
    SmallQThreeF4 ∧ SmallQThreeE6 ∧ SmallQThreeE6Diag ∧ SmallQThreeTwE6 ∧ SmallQThreeTwE6Diag ∧
      SmallQThreeE7 ∧ SmallQThreeE8 := by
  obtain ⟨hF4, hE6, hTw, hE7, hE8⟩ := h
  exact ⟨smallQThreeF4_of_innerOneBalance hF4, smallQThreeE6_of_innerOneBalance hE6,
    smallQThreeE6Diag_of_innerOneBalance fun K _ _ hK => hE6 K (Or.inr hK),
    smallQThreeTwE6_of_innerOneBalance hTw, smallQThreeTwE6Diag_of_innerOneBalance hTw,
    smallQThreeE7_of_innerOneBalance hE7, smallQThreeE8_of_innerOneBalance hE8⟩

end OneBalanceTwisted

end CFSG.HardMathSupport.Timmesfeld.CrossChar
