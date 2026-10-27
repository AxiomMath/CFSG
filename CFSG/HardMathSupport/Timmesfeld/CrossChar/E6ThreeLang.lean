module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeToralPlane
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFiveLang
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeLarge
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6Center

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE CFSG.LieType.SeitzGeneration

section Residuals


open CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny in
@[expose] def E6IsotropicToral : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ¬ 3 ∣ Nat.card K →
    ∀ E₀ : Subgroup (adjointGroup Tag.E6 K), (∀ x ∈ E₀, x ^ 3 = 1) → Nat.card E₀ = 3 ^ 2 →
      (∀ x ∈ E₀.comap (e6Isogeny K), ∀ y ∈ E₀.comap (e6Isogeny K), x * y = y * x) →
      ∃ w : WeylGroup Tag.E6, ∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K,
        (∀ c, Fr c = c ^ Nat.card K) ∧
        ∃ g0 ∈ adjointGroup Tag.E6 (AlgebraicClosure K),
          Units.map (entrywiseHom Fr) g0 =
            g0 * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w ∧
          ∀ x ∈ E₀, baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL Tag.E6 K) ∈
            (twistedTorusOf (canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w)
              (Units.map (entrywiseHom Fr))).map (MulAut.conj g0).toMonoidHom


open CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Isogeny in
@[expose] def TwistedE6IsotropicToral : Prop :=
  ∀ ℓ f : ℕ, ℓ.Prime → ℓ ≠ 3 → 1 ≤ f → ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = (ℓ ^ f) ^ 2 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) →
    ∀ E₀ : Subgroup (twistedE6RootGroup K σ), (∀ x ∈ E₀, x ^ 3 = 1) → Nat.card E₀ = 3 ^ 2 →
      (∀ x y : fixedGroup K σ.toRingHom,
        e6IsogenyFixed σ.toRingHom x ∈ E₀.map (twistedE6RootGroup K σ).subtype →
        e6IsogenyFixed σ.toRingHom y ∈ E₀.map (twistedE6RootGroup K σ).subtype → x * y = y * x) →
      ∃ v : WeylGroup TwistTag.E6.tag, ∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K,
        (∀ c, Fr c = c ^ (ℓ ^ f)) ∧
        ∃ g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K),
          twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
            g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v ∧
          ∀ x ∈ E₀, baseChangeGL (algebraMap K (AlgebraicClosure K))
              (x : ModGL TwistTag.E6.tag K) ∈
            (twistedTorusOf
              (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
              (twistHom TwistTag.E6 (AlgebraicClosure K) Fr)).map (MulAut.conj g0).toMonoidHom

end Residuals

theorem comap_conj_props {C : Type*} [Group C]
    (hinj : Function.Injective (MulAut.conj : C →* MulAut C)) {E : Subgroup (MulAut C)}
    (hEin : E ≤ innerAut C) (hE3 : ∀ x ∈ E, x ^ 3 = 1) (hE9 : 3 ^ 2 ≤ Nat.card E) :
    (∀ x ∈ E.comap (MulAut.conj : C →* MulAut C), x ^ 3 = 1) ∧
      3 < Nat.card (E.comap (MulAut.conj : C →* MulAut C)) ∧
      (E.comap (MulAut.conj : C →* MulAut C)).map (MulAut.conj : C →* MulAut C) = E := by
  have hmap : (E.comap (MulAut.conj : C →* MulAut C)).map (MulAut.conj : C →* MulAut C) = E :=
    Subgroup.map_comap_eq_self hEin
  refine ⟨fun x hx => hinj (by rw [map_pow, map_one]; exact hE3 _ hx), ?_, hmap⟩
  rw [← Subgroup.card_map_of_injective hinj, hmap]
  omega

theorem sigma_sigma_of_card {K : Type} [Field K] [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ q) (c : K) : σ (σ c) = c := by
  have : Fintype K := Fintype.ofFinite K
  rw [hσ, hσ, ← pow_mul, ← sq, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]

theorem exists_plane_le {G : Type*} [Group G] {E₀ : Subgroup G} (hexp : ∀ x ∈ E₀, x ^ 3 = 1)
    (hcard : 3 < Nat.card E₀) : ∃ E₁ : Subgroup G, E₁ ≤ E₀ ∧ Nat.card E₁ = 3 ^ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfin : Finite E₀ := Nat.finite_of_card_ne_zero (by omega)
  have hp : IsPGroup 3 E₀ := fun x => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (by simpa using hexp x x.2)⟩
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hn2 : 2 ≤ n := by
    by_contra h
    have : n ≤ 1 := by omega
    have : Nat.card E₀ ≤ 3 := by
      rw [hn]
      calc 3 ^ n ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
        _ = 3 := by norm_num
    omega
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 3
    (hn ▸ pow_dvd_pow 3 hn2 : 3 ^ 2 ∣ Nat.card E₀)
  refine ⟨K.map E₀.subtype, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rw [← hK]
    exact Subgroup.card_map_of_injective E₀.subtype_injective

section E6


theorem e6ThreeInnerNonsplitLarge_of_toral (htor : E6IsotropicToral)
    (hT1 : ∀ w : WeylGroup Tag.E6,
      LangTorusPlaneBalance Tag.E6 w 3 fun q => ¬ 3 ∣ q ∧ q ≠ 2 ∧ q ≠ 4) :
    E6ThreeInnerNonsplitLarge := by
  intro ℓ f hℓ hℓ3 hf hq2 hq4 K _ _ hK D hD hcard hDin _ H hH _
  have h3 : ¬ 3 ∣ Nat.card K := by
    rw [hK]
    intro h
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
  obtain ⟨E, hED, hE9, hEab⟩ := exists_isotropic_plane_E6 K hDin hD hcard
  have hinj := mulAut_conj_injective_adjointGroup (τ := Tag.E6) (K := K)
  obtain ⟨hpow, hcard₀, hmap⟩ := comap_conj_props hinj (hED.trans hDin)
    (fun x hx => hD.2 x (hED hx)) hE9
  have hab : ∀ x ∈ (E.comap (MulAut.conj : adjointGroup Tag.E6 K →* _)).comap
      (CFSG.LieType.Steinberg.Isogeny.e6Isogeny K), ∀ y ∈ (E.comap (MulAut.conj :
        adjointGroup Tag.E6 K →* _)).comap (CFSG.LieType.Steinberg.Isogeny.e6Isogeny K),
      x * y = y * x := fun x hx y hy => hEab x hx y hy
  obtain ⟨E₁, hE₁, hE₁c⟩ := exists_plane_le hpow hcard₀
  have hab₁ : ∀ x ∈ E₁.comap (CFSG.LieType.Steinberg.Isogeny.e6Isogeny K),
      ∀ y ∈ E₁.comap (CFSG.LieType.Steinberg.Isogeny.e6Isogeny K), x * y = y * x :=
    fun x hx y hy => hab x (hE₁ hx) y (hE₁ hy)
  have hpow₁ : ∀ x ∈ E₁, x ^ 3 = 1 := fun x hx => hpow x (hE₁ hx)
  obtain ⟨w, Fr, hFr, g0, hg0C, hg0, hin⟩ := htor K h3 E₁ hpow₁ hE₁c hab₁
  have h := hT1 w K ⟨h3, hK ▸ hq2, hK ▸ hq4⟩ Fr hFr g0 hg0C hg0 E₁ hpow₁
    (by rw [hE₁c]; norm_num) hin H hH
  have hle : E₁.map (MulAut.conj : adjointGroup Tag.E6 K →* MulAut _) ≤ D := by
    rw [← hmap] at hED
    exact (Subgroup.map_mono hE₁).trans hED
  exact le_bot_iff.1 ((localDeltaIn_antitone H hle).trans h.le)

end E6

section TwistedE6


open CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed CFSG.LieType.Simplicity

theorem exists_isotropic_plane_twistedE6 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {D : Subgroup (MulAut (twistedE6RootGroup K σ))}
    (hDin : D ≤ innerAut (twistedE6RootGroup K σ)) (hD : IsElemAbelian 3 D)
    (hcard : Nat.card D = 3 ^ 3) :
    ∃ E : Subgroup (MulAut (twistedE6RootGroup K σ)), E ≤ D ∧ 3 ^ 2 ≤ Nat.card E ∧
      ∀ x y : fixedGroup K σ.toRingHom,
        e6IsogenyFixed σ.toRingHom x ∈
          (E.comap (MulAut.conj : twistedE6RootGroup K σ →* _)).map
            (twistedE6RootGroup K σ).subtype →
        e6IsogenyFixed σ.toRingHom y ∈
          (E.comap (MulAut.conj : twistedE6RootGroup K σ →* _)).map
            (twistedE6RootGroup K σ).subtype → x * y = y * x := by
  classical
  have hq2 : 2 ≤ ℓ ^ f := le_trans hℓ.two_le (Nat.le_self_pow (by omega) ℓ)
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    nlinarith
  have hθ : ∀ c, σ.toRingHom (σ.toRingHom c) = c := sigma_sigma_of_card hK hσ
  have hσ' : ∀ c, σ.toRingHom c = c ^ (ℓ ^ f) := hσ
  have hder := (CFSG.LieType.Chevalley.finite_fixed_root_group_perfect TwistTag.E6 hℓ hf K hK
    σ.toRingHom hσ').2.2.1
  set ψ : fixedGroup K σ.toRingHom →* twistedE6RootGroup K σ :=
    (MulEquiv.subgroupCongr hder).toMonoidHom.comp (twistedIsogeny σ.toRingHom hθ hK4) with hψ
  have hψcoe : ∀ x, ((ψ x : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
      e6IsogenyFixed σ.toRingHom x := fun x => rfl
  have hψsurj : Function.Surjective ψ :=
    (MulEquiv.subgroupCongr hder).surjective.comp (twistedIsogeny_surjective σ.toRingHom hθ hK4)
  have hinj : Function.Injective (MulAut.conj : twistedE6RootGroup K σ →* MulAut _) :=
    mulAut_conj_injective_of_center_eq_bot
      (center_graphFixedRootGroup_eq_bot σ.surjective)
  set π : fixedGroup K σ.toRingHom →* MulAut (twistedE6RootGroup K σ) :=
    (MulAut.conj : twistedE6RootGroup K σ →* MulAut _).comp ψ with hπ
  have hker : π.ker = Subgroup.center (fixedGroup K σ.toRingHom) := by
    rw [hπ, MonoidHom.ker_comp_of_injective _ _ hinj, hψ,
      MonoidHom.ker_comp_of_injective _ _ (MulEquiv.subgroupCongr hder).injective,
      ker_twistedIsogeny_eq_center hθ hK4]
  have hrange : π.range = innerAut (twistedE6RootGroup K σ) := by
    rw [hπ, MonoidHom.range_comp, MonoidHom.range_eq_top.2 hψsurj, Subgroup.map_top]
    rfl
  have hker3 : Nat.card π.ker ∣ 3 := by
    rw [hker, (card_center_fixedGroup hK hσ').1]
    exact Nat.gcd_dvd_left 3 _
  obtain ⟨E, hED, hE9, hEab⟩ := exists_le_comap_commute_of_ker_dvd_three π
    (hker.le) hker3 (by rw [hrange]; exact hDin) hD hcard
  refine ⟨E, hED, hE9, fun x y hx hy => hEab x ?_ y ?_⟩
  · obtain ⟨z, hz, hzx⟩ := hx
    have : z = ψ x := Subtype.ext (hzx.trans (hψcoe x).symm)
    subst this
    exact hz
  · obtain ⟨z, hz, hzy⟩ := hy
    have : z = ψ y := Subtype.ext (hzy.trans (hψcoe y).symm)
    subst this
    exact hz

theorem twistedE6ThreeInnerLarge_of_toral
    (htor : TwistedE6IsotropicToral)
    (hT1 : ∀ v : WeylGroup TwistTag.E6.tag,
      TwistedE6LangTorusPlaneBalance v 3 fun q => ¬ 3 ∣ q ∧ q ≠ 2) :
    TwistedE6ThreeInnerLarge := by
  rintro ⟨d, hv⟩ hk p hp hp2 hc ⟨rfl, q, hq, hq2⟩
  change d = _ at hq
  subst hq
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  have hℓ := q.prime_p
  have hf := q.exponent_pos
  have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have hℓ3 : q.p ≠ 3 := fun h => hc (by simp [h])
  have h3 : ¬ 3 ∣ q.p ^ q.exponent := by
    intro h
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
  refine IsInnerLocallyBalanced.of_mulEquiv e ?_
  intro D hD hcard hDin H hH _
  obtain ⟨E, hED, hE9, hEab⟩ := exists_isotropic_plane_twistedE6 hℓ hf hK hσ hDin hD hcard
  have hinj : Function.Injective (MulAut.conj : twistedE6RootGroup K σ →* MulAut _) :=
    mulAut_conj_injective_of_center_eq_bot
      (center_graphFixedRootGroup_eq_bot σ.surjective)
  obtain ⟨hpow, hcard₀, hmap⟩ := comap_conj_props hinj (hED.trans hDin)
    (fun x hx => hD.2 x (hED hx)) hE9
  obtain ⟨E₁, hE₁, hE₁c⟩ := exists_plane_le hpow hcard₀
  have hpow₁ : ∀ x ∈ E₁, x ^ 3 = 1 := fun x hx => hpow x (hE₁ hx)
  have hEab₁ : ∀ x y : fixedGroup K σ.toRingHom,
      e6IsogenyFixed σ.toRingHom x ∈ E₁.map (twistedE6RootGroup K σ).subtype →
      e6IsogenyFixed σ.toRingHom y ∈ E₁.map (twistedE6RootGroup K σ).subtype → x * y = y * x :=
    fun x y hx hy => hEab x y (Subgroup.map_mono hE₁ hx) (Subgroup.map_mono hE₁ hy)
  obtain ⟨v, Fr, hFr, g0, hg0C, hg0, hin⟩ :=
    htor q.p q.exponent hℓ hℓ3 hf K hK σ hσ E₁ hpow₁ hE₁c hEab₁
  have h := hT1 v q.p q.exponent hℓ hf ⟨h3, hqc ▸ hq2⟩ K hK σ hσ Fr hFr g0 hg0C hg0 E₁ hpow₁
    (by rw [hE₁c]; norm_num) hin H hH
  have hle : E₁.map (MulAut.conj : twistedE6RootGroup K σ →* MulAut _) ≤ D := by
    rw [← hmap] at hED
    exact (Subgroup.map_mono hE₁).trans hED
  exact le_bot_iff.1 ((localDeltaIn_antitone H hle).trans h.le)

end TwistedE6

end CFSG.HardMathSupport.Timmesfeld.CrossChar
