module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang.Root
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagTwisted

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups

theorem exists_langSetup_of_inner_twE6_of_prime_descent {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    {K : Type} [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hpℓ : p ≠ ℓ)
    {p₀ : ℕ} (hp₀ : p₀.Prime) (hp₀ℓ : p₀ ≠ ℓ) (hq₀ : 5 ≤ p₀ ∨ 4 ≤ ℓ ^ f)
    (hmon : MonomialToralAt Tag.E6 p)
    (β : MulAut ↥(twistedE6RootGroup K σ)) (h : ModGL TwistTag.E6.tag K)
    (hh : h ∈ CFSG.Blueprint.twistedFixedGroup TwistTag.E6 K σ.toRingHom)
    (hβ : ∀ c, (β c : ModGL TwistTag.E6.tag K) = h * c * h⁻¹) (hp1 : h ^ p = 1) (hh1 : h ≠ 1) :
    ∃ (S : LangSetup Tag.E6 (AlgebraicClosure K) p₀)
      (a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ)
      (ι : ↥(twistedE6RootGroup K σ) →* ModGL Tag.E6 (AlgebraicClosure K)),
      S.D.q = ℓ ^ f ∧
      (∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ (ℓ ^ f)) ∧
        S.D.Φ = twistHom TwistTag.E6 (AlgebraicClosure K) Fr) ∧
      rootDiagUnit Tag.E6 a ∈ S.D.torus ∧ (∀ i, a i ^ p = 1) ∧ rootDiagUnit Tag.E6 a ≠ 1 ∧
      Function.Injective ι ∧ ι.range = S.Γ ∧
      (∀ c, ι (β c) = rootDiagUnit Tag.E6 a * ι c * (rootDiagUnit Tag.E6 a)⁻¹) ∧
      ∃ g : ModGL TwistTag.E6.tag (AlgebraicClosure K),
        rootDiagUnit TwistTag.E6.tag a = g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) h * g ∧
        ∀ c, ι c = g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (c : ModGL TwistTag.E6.tag K) * g := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hK0 : Nat.card K ≠ 0 := by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero)
  haveI : Finite K := Nat.finite_of_card_ne_zero hK0
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  set L := AlgebraicClosure K with hLdef
  haveI : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  set ι₁ : K →+* L := algebraMap K L with hι₁
  have hFr : ∀ c : L, iterateFrobenius L ℓ f c = c ^ (ℓ ^ f) := fun c =>
    iterateFrobenius_def ℓ f c
  have hcomm : ι₁.comp σ.toRingHom = (iterateFrobenius L ℓ f).comp ι₁ := by
    refine RingHom.ext fun c => ?_
    change ι₁ (σ c) = iterateFrobenius L ℓ f (ι₁ c)
    rw [hσ c, iterateFrobenius_def, map_pow]
  have hhG : h ∈ adjointGroup TwistTag.E6.tag K := hh.1
  have hhfix : twistHom TwistTag.E6 K σ.toRingHom h = h := hh.2
  set u : ModGL TwistTag.E6.tag L := baseChangeGL ι₁ h with hu
  have huG : u ∈ adjointGroup TwistTag.E6.tag L :=
    CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup ι₁ hhG
  have hufix : twistHom TwistTag.E6 L (iterateFrobenius L ℓ f) u = u := by
    rw [hu, twistHom_baseChangeGL ι₁ hcomm, hhfix]
  have hup : u ^ p = 1 := by rw [hu, ← map_pow, hp1, map_one]
  have hu1 : u ≠ 1 := fun h' => hh1 (baseChangeGL_injective ι₁ (by rw [map_one]; exact h'))
  have hconj := exists_conj_torusGroup_of_pow_eq_one hp hmon hpℓ.symm
    (isAlgebraic_zmod_algebraicClosure_of_finite K ℓ) huG hup
  obtain ⟨D, hΦ, hDq, hmem⟩ := exists_langDatum_of_toral_twisted TwistTag.E6 f hf hufix hconj
  set ι₀ : ↥(twistedE6RootGroup K σ) →* ModGL TwistTag.E6.tag L :=
    (baseChangeGL ι₁).comp (twistedE6RootGroup K σ).subtype with hι₀
  have hι₀inj : Function.Injective ι₀ :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  have hrange₀ : ι₀.range = (twistedE6RootGroup K σ).map (baseChangeGL ι₁) := by
    rw [hι₀, MonoidHom.range_comp, Subgroup.range_subtype]
  have hΓ : D.Γ = ι₀.range.map (MulAut.conj D.g0⁻¹).toMonoidHom := by
    rw [hrange₀]
    exact Γ_eq_map_twistedE6RootGroup hℓ hf hK hσ hFr D hΦ
  have hfin : Finite D.model := finite_model_twistedE6 hℓ hf hK hσ hFr D hΦ
  have hβ' : ∀ c, ι₀ (β c) = u * ι₀ c * u⁻¹ := fun c => by
    change baseChangeGL ι₁ (β c : ModGL TwistTag.E6.tag K) = baseChangeGL ι₁ h *
      baseChangeGL ι₁ (c : ModGL TwistTag.E6.tag K) * (baseChangeGL ι₁ h)⁻¹
    rw [hβ c, map_mul, map_mul, map_inv]
  have hq' : 5 ≤ p₀ ∨ 4 ≤ D.q := by
    rw [hDq]
    exact hq₀
  obtain ⟨S, a, ι, rfl, hT, hap, h1, hda, hι, hinj, hrange, hconjι⟩ :=
    exists_langSetup_of_toral_datum_of_prime_descent hℓ hf D hDq hp₀ hp₀ℓ hq' hfin ι₀ hι₀inj hΓ β hβ' hmem
      hup hu1
  exact ⟨S, a, ι, hDq, ⟨iterateFrobenius L ℓ f, hFr, hΦ⟩, hT, hap, h1, hinj, hrange,
    hconjι, S.D.g0, hda, hι⟩

theorem exists_langSetup_of_inner_twE6_of_prime {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    {K : Type} [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hpℓ : p ≠ ℓ)
    {p₀ : ℕ} (hp₀ : p₀.Prime) (hp₀ℓ : p₀ ≠ ℓ) (hq₀ : 5 ≤ p₀ ∨ 4 ≤ ℓ ^ f)
    (hmon : MonomialToralAt Tag.E6 p)
    (β : MulAut ↥(twistedE6RootGroup K σ)) (h : ModGL TwistTag.E6.tag K)
    (hh : h ∈ CFSG.Blueprint.twistedFixedGroup TwistTag.E6 K σ.toRingHom)
    (hβ : ∀ c, (β c : ModGL TwistTag.E6.tag K) = h * c * h⁻¹) (hp1 : h ^ p = 1) (hh1 : h ≠ 1) :
    ∃ (S : LangSetup Tag.E6 (AlgebraicClosure K) p₀)
      (a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ)
      (ι : ↥(twistedE6RootGroup K σ) →* ModGL Tag.E6 (AlgebraicClosure K)),
      S.D.q = ℓ ^ f ∧
      (∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ (ℓ ^ f)) ∧
        S.D.Φ = twistHom TwistTag.E6 (AlgebraicClosure K) Fr) ∧
      rootDiagUnit Tag.E6 a ∈ S.D.torus ∧ (∀ i, a i ^ p = 1) ∧ rootDiagUnit Tag.E6 a ≠ 1 ∧
      Function.Injective ι ∧ ι.range = S.Γ ∧
      ∀ c, ι (β c) = rootDiagUnit Tag.E6 a * ι c * (rootDiagUnit Tag.E6 a)⁻¹ := by
  obtain ⟨S, a, ι, hq, hFr, hT, hap, h1, hinj, hrange, hconj, -⟩ :=
    exists_langSetup_of_inner_twE6_of_prime_descent hℓ hf hK σ hσ hp hpℓ hp₀ hp₀ℓ hq₀
      hmon β h hh hβ hp1 hh1
  exact ⟨S, a, ι, hq, hFr, hT, hap, h1, hinj, hrange, hconj⟩

theorem exists_langSetup_of_inner_twE6_of_prime_eq {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    {K : Type} [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hpℓ : p ≠ ℓ)
    {p₀ : ℕ} (hp₀ : p₀.Prime) (hp₀ℓ : p₀ ≠ ℓ) (hq₀ : 5 ≤ p₀ ∨ 4 ≤ ℓ ^ f)
    (hmon : MonomialToralAt Tag.E6 p) (x : ↥(twistedE6RootGroup K σ))
    (hxp : x ^ p = 1) (hx1 : x ≠ 1) :
    ∃ (S : LangSetup Tag.E6 (AlgebraicClosure K) p₀)
      (a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ)
      (ι : ↥(twistedE6RootGroup K σ) →* ModGL Tag.E6 (AlgebraicClosure K)),
      S.D.q = ℓ ^ f ∧
      (∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ (ℓ ^ f)) ∧
        S.D.Φ = twistHom TwistTag.E6 (AlgebraicClosure K) Fr) ∧
      rootDiagUnit Tag.E6 a ∈ S.D.torus ∧ (∀ i, a i ^ p = 1) ∧ rootDiagUnit Tag.E6 a ≠ 1 ∧
      Function.Injective ι ∧ ι.range = S.Γ ∧ ι x = rootDiagUnit Tag.E6 a ∧
      ∀ c, ι (MulAut.conj x c) = rootDiagUnit Tag.E6 a * ι c * (rootDiagUnit Tag.E6 a)⁻¹ := by
  have hh : (x : ModGL TwistTag.E6.tag K) ∈ twistedFixedGroup TwistTag.E6 K σ.toRingHom :=
    graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom x.2
  have hp1 : (x : ModGL TwistTag.E6.tag K) ^ p = 1 := by
    exact congrArg Subtype.val hxp
  have hh1 : (x : ModGL TwistTag.E6.tag K) ≠ 1 := fun h => hx1 (Subtype.ext h)
  obtain ⟨S, a, ι, hq, hFr, hT, hap, h1, hinj, hrange, hconj, g, hda, hι⟩ :=
    exists_langSetup_of_inner_twE6_of_prime_descent hℓ hf hK σ hσ hp hpℓ hp₀ hp₀ℓ hq₀
      hmon (MulAut.conj x) (x : ModGL TwistTag.E6.tag K) hh
      (fun c => rfl) hp1 hh1
  exact ⟨S, a, ι, hq, hFr, hT, hap, h1, hinj, hrange, (hι x).trans hda.symm, hconj⟩

theorem exists_langSetup_of_inndiag_twE6_of_prime {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    {K : Type} [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hpℓ : p ≠ ℓ)
    {p₀ : ℕ} (hp₀ : p₀.Prime) (hp₀ℓ : p₀ ≠ ℓ) (hq₀ : 5 ≤ p₀ ∨ 4 ≤ ℓ ^ f)
    (hmon : MonomialToralAt Tag.E6 p)
    (β : MulAut ↥(twistedE6RootGroup K σ)) (h : ModGL TwistTag.E6.tag K)
    (hh : h ∈ twistedE6InndiagGL K σ)
    (hβ : ∀ c, (β c : ModGL TwistTag.E6.tag K) = h * c * h⁻¹) (hp1 : h ^ p = 1) (hh1 : h ≠ 1) :
    ∃ (S : LangSetup Tag.E6 (AlgebraicClosure K) p₀)
      (a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ)
      (ι : ↥(twistedE6RootGroup K σ) →* ModGL Tag.E6 (AlgebraicClosure K)),
      S.D.q = ℓ ^ f ∧
      (∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ (ℓ ^ f)) ∧
        S.D.Φ = twistHom TwistTag.E6 (AlgebraicClosure K) Fr) ∧
      rootDiagUnit Tag.E6 a ∈ S.D.torus ∧ (∀ i, a i ^ p = 1) ∧ rootDiagUnit Tag.E6 a ≠ 1 ∧
      Function.Injective ι ∧ ι.range = S.Γ ∧
      ∀ c, ι (β c) = rootDiagUnit Tag.E6 a * ι c * (rootDiagUnit Tag.E6 a)⁻¹ := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hK0 : Nat.card K ≠ 0 := by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero)
  haveI : Finite K := Nat.finite_of_card_ne_zero hK0
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  set L := AlgebraicClosure K with hLdef
  haveI : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  set ι₁ : K →+* L := algebraMap K L with hι₁
  have hFr : ∀ c : L, iterateFrobenius L ℓ f c = c ^ (ℓ ^ f) := fun c =>
    iterateFrobenius_def ℓ f c
  set u : ModGL TwistTag.E6.tag L := baseChangeGL ι₁ h with hu
  have huF : u ∈ twistedFixedGroup TwistTag.E6 L (iterateFrobenius L ℓ f) :=
    map_twistedE6InndiagGL_le_twistedFixedGroup hℓ hf hK σ hσ (iterateFrobenius L ℓ f) hFr
      ⟨h, hh, rfl⟩
  have huG : u ∈ adjointGroup TwistTag.E6.tag L := huF.1
  have hufix : twistHom TwistTag.E6 L (iterateFrobenius L ℓ f) u = u := huF.2
  have hup : u ^ p = 1 := by rw [hu, ← map_pow, hp1, map_one]
  have hu1 : u ≠ 1 := fun h' => hh1 (baseChangeGL_injective ι₁ (by rw [map_one]; exact h'))
  have hconj := exists_conj_torusGroup_of_pow_eq_one hp hmon hpℓ.symm
    (isAlgebraic_zmod_algebraicClosure_of_finite K ℓ) huG hup
  obtain ⟨D, hΦ, hDq, hmem⟩ := exists_langDatum_of_toral_twisted TwistTag.E6 f hf hufix hconj
  set ι₀ : ↥(twistedE6RootGroup K σ) →* ModGL TwistTag.E6.tag L :=
    (baseChangeGL ι₁).comp (twistedE6RootGroup K σ).subtype with hι₀
  have hι₀inj : Function.Injective ι₀ :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  have hrange₀ : ι₀.range = (twistedE6RootGroup K σ).map (baseChangeGL ι₁) := by
    rw [hι₀, MonoidHom.range_comp, Subgroup.range_subtype]
  have hΓ : D.Γ = ι₀.range.map (MulAut.conj D.g0⁻¹).toMonoidHom := by
    rw [hrange₀]
    exact Γ_eq_map_twistedE6RootGroup hℓ hf hK hσ hFr D hΦ
  have hfin : Finite D.model := finite_model_twistedE6 hℓ hf hK hσ hFr D hΦ
  have hβ' : ∀ c, ι₀ (β c) = u * ι₀ c * u⁻¹ := fun c => by
    change baseChangeGL ι₁ (β c : ModGL TwistTag.E6.tag K) = baseChangeGL ι₁ h *
      baseChangeGL ι₁ (c : ModGL TwistTag.E6.tag K) * (baseChangeGL ι₁ h)⁻¹
    rw [hβ c, map_mul, map_mul, map_inv]
  have hq' : 5 ≤ p₀ ∨ 4 ≤ D.q := by
    rw [hDq]
    exact hq₀
  obtain ⟨S, a, ι, rfl, hT, hap, h1, hinj, hrange, hconjι⟩ :=
    exists_langSetup_of_toral_datum_of_prime hℓ hf D hDq hp₀ hp₀ℓ hq' hfin ι₀ hι₀inj hΓ β hβ' hmem
      hup hu1
  exact ⟨S, a, ι, hDq, ⟨iterateFrobenius L ℓ f, hFr, hΦ⟩, hT, hap, h1, hinj, hrange, hconjι⟩

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
