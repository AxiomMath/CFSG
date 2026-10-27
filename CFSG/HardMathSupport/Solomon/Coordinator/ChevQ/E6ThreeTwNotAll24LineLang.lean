module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnComp
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24Types

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSNotAll24

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Seitz CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6UniqAbs

set_option linter.unusedSectionVars false

section Lang


theorem exists_langSetup_conj_of_inndiag_twE6' {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
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
      rootDiagUnit Tag.E6 a ∈ S.D.torus ∧ (∀ i, a i ^ p = 1) ∧ rootDiagUnit Tag.E6 a ≠ 1 ∧
      Function.Injective ι ∧ ι.range = S.Γ ∧
      (∀ c, ι (β c) = rootDiagUnit Tag.E6 a * ι c * (rootDiagUnit Tag.E6 a)⁻¹) ∧
      S.D.g0 * rootDiagUnit Tag.E6 a * S.D.g0⁻¹ =
        baseChangeGL (algebraMap K (AlgebraicClosure K)) h ∧
      ∃ (t : TwistTag) (ht : t.tag = .E6) (Fr : AlgebraicClosure K →+* AlgebraicClosure K),
        (∀ c, Fr c = c ^ S.D.q) ∧
        ∀ g, S.D.Φ g = diagramAt .E6 (AlgebraicClosure K) t ht * Units.map (entrywiseHom Fr) g *
          (diagramAt .E6 (AlgebraicClosure K) t ht)⁻¹ := by
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
  obtain ⟨S, a, ι, rfl, hT, hap, h1, hinj, hrange, hconjι, hg0⟩ :=
    exists_langSetup_conj_of_toral_datum hℓ hf D hDq hp₀ hp₀ℓ hq' hfin ι₀ hι₀inj hΓ β hβ' hmem
      hup hu1
  refine ⟨S, a, ι, hDq, hT, hap, h1, hinj, hrange, hconjι, hg0, TwistTag.E6, rfl,
    iterateFrobenius L ℓ f, fun c => ?_, fun g => ?_⟩
  · rw [hDq]
    exact hFr c
  · rw [hΦ]
    rfl

structure TwE6LineLang (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ)
    (h : twistedE6InndiagGL K σ) where
  e : ℕ
  he : 0 < e
  hqe : q = ringChar K ^ e
  hℓ : (ringChar K).Prime
  hK' : Nat.card K = (ringChar K ^ e) ^ 2
  hσ' : ∀ c, σ c = c ^ (ringChar K ^ e)
  hL3 : ((3 : ℕ) : AlgebraicClosure K) ≠ 0
  hchar : CharP (AlgebraicClosure K) (ringChar K)
  p₀ : ℕ
  hp₀ : p₀.Prime
  hp₀ℓ : p₀ ≠ ringChar K
  hq₀ : 5 ≤ p₀ ∨ 4 ≤ ringChar K ^ e
  S : LangSetup Tag.E6 (AlgebraicClosure K) p₀
  a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ
  ι : ↥(twistedE6RootGroup K σ) →* ModGL Tag.E6 (AlgebraicClosure K)
  hSq : S.D.q = ringChar K ^ e
  hT : rootDiagUnit Tag.E6 a ∈ S.D.torus
  hap : ∀ i, a i ^ 3 = 1
  h1 : rootDiagUnit Tag.E6 a ≠ 1
  hinj : Function.Injective ι
  hrange : ι.range = S.Γ
  hconj : ∀ c, ι (twistedE6InndiagConj K σ h c) =
    rootDiagUnit Tag.E6 a * ι c * (rootDiagUnit Tag.E6 a)⁻¹
  hg0 : S.D.g0 * rootDiagUnit Tag.E6 a * S.D.g0⁻¹ =
    baseChangeGL (algebraMap K (AlgebraicClosure K)) (h : ModGL TwistTag.E6.tag K)
  hS : ∃ (t : TwistTag) (h : t.tag = .E6) (Fr : AlgebraicClosure K →+* AlgebraicClosure K),
    (∀ c, Fr c = c ^ S.D.q) ∧
    ∀ g, S.D.Φ g = diagramAt .E6 (AlgebraicClosure K) t h * Units.map (entrywiseHom Fr) g *
      (diagramAt .E6 (AlgebraicClosure K) t h)⁻¹
  hker : twE6MatFixDim K σ h = 6 + (kernelRoots (rootCharHom a)).ncard
  hTame : ∀ i : KernelComponent (rootCharHom a),
    CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
      Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i)

theorem nonempty_twE6LineLang (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ)
    (hK3 : ringChar K ≠ 3) (hσ : ∀ c, σ c = c ^ q) (hKq : Nat.card K = q ^ 2) (hq2 : 2 ≤ q)
    (h : twistedE6InndiagGL K σ) (hh1 : h ≠ 1) (hh3 : h ^ 3 = 1) :
    Nonempty (TwE6LineLang K σ q h) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨hp, f, hf, hqf⟩ := prime_ringChar_and_eq_pow_of_card_sq K q hKq hq2
  have hK' : Nat.card K = (ringChar K ^ f) ^ 2 := by rw [← hqf]; exact hKq
  have hσ' : ∀ c, σ c = c ^ (ringChar K ^ f) := by intro c; rw [← hqf]; exact hσ c
  have hpℓ : 3 ≠ ringChar K := fun h' => hK3 h'.symm
  obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ := exists_setup_prime hp hf Nat.prime_three (by norm_num) hpℓ
  have hh3' : (h : ModGL TwistTag.E6.tag K) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hh3]
    rfl
  have hh1' : (h : ModGL TwistTag.E6.tag K) ≠ 1 := fun h' => hh1 (Subtype.ext h')
  obtain ⟨S, a, ι, hSq, hT, hap, h1, hinj, hrange, hconj, hg0, hS⟩ :=
    exists_langSetup_conj_of_inndiag_twE6' hp hf hK' σ hσ' Nat.prime_three hpℓ hp₀ hp₀ℓ hq₀
      monomialToralAt_E6_three (twistedE6InndiagConj K σ h) (h : ModGL TwistTag.E6.tag K) h.2
      (twistedE6InndiagConj_apply h) hh3' hh1'
  have hL3 : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 :=
    natCast_ne_zero_algebraicClosure_of_ne hp Nat.prime_three hK' hpℓ
  haveI : CharP K (ringChar K) := ringChar.charP K
  haveI hchar : CharP (AlgebraicClosure K) (ringChar K) :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective _
  exact ⟨{
    e := f, he := hf, hqe := hqf, hℓ := hp, hK' := hK', hσ' := hσ', hL3 := hL3, hchar := hchar,
    p₀ := p₀, hp₀ := hp₀, hp₀ℓ := hp₀ℓ, hq₀ := hq₀, S := S, a := a, ι := ι, hSq := hSq,
    hT := hT, hap := hap, h1 := h1, hinj := hinj, hrange := hrange, hconj := hconj, hg0 := hg0,
    hS := hS, hker := twE6MatFixDim_eq_of_conj σ h S.D.g0 a hg0,
    hTame := langSetup_hTame_of_prime S Nat.prime_three hL3 (fun h => absurd h (by decide)) hT
      hap h1 }⟩

namespace TwE6LineLang

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {q : ℕ} {h : twistedE6InndiagGL K σ}
  (D : TwE6LineLang K σ q h)

theorem map_fixedPoints :
    (fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h))).map D.ι =
      D.S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 D.a} := by
  rw [← fixSubgroup_eq_fixedPoints, map_fixSubgroup_eq_of_conj D.ι D.hinj _ _ D.hconj, D.hrange]

theorem eq_of_map_eq {A B : Subgroup (twistedE6RootGroup K σ)} (hAB : A.map D.ι = B.map D.ι) :
    A = B :=
  Subgroup.map_injective D.hinj hAB

theorem exists_rationalComponent {J : Subgroup (twistedE6RootGroup K σ)}
    (hJ : IsComponentOf J (fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h)))) :
    ∃ i : KernelComponent (rootCharHom D.a),
      CFSG.IsQuasisimple (rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i) ∧
        J.map D.ι = rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i := by
  rw [← fixSubgroup_eq_fixedPoints] at hJ
  exact components_of_langSetup D.S Nat.prime_three D.ι D.hinj D.hrange
    (twistedE6InndiagConj K σ h) D.hconj D.hT D.hap D.h1 D.hTame hJ

theorem isComponentOf_comap (i : KernelComponent (rootCharHom D.a))
    (hq : CFSG.IsQuasisimple (rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i)) :
    IsComponentOf ((rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i).comap D.ι)
      (fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h))) := by
  have hCd : D.S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 D.a} ≤ D.ι.range := fun x hx => by
    rw [D.hrange]
    exact (Subgroup.mem_inf.1 hx).1
  have hcomapfix : (D.S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 D.a}).comap D.ι =
      fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h)) := by
    rw [← D.map_fixedPoints]
    exact Subgroup.comap_map_eq_self_of_injective D.hinj _
  have hcompR : IsComponentOf (rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i)
      (D.S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 D.a}) := by
    obtain ⟨hle, hsub⟩ := langSubnormal_of_mem_torus D.S D.hT i
    exact ⟨hle, (CFSG.Open.IsSubnormal.iff_subgroupOf hle).2 hsub, open_isQuasisimple hq⟩
  have := isComponentOf_comap_of_injective D.ι D.hinj (hcompR.1.trans hCd) hCd hcompR
  rwa [hcomapfix] at this

end TwE6LineLang

theorem exists_twE6LineLang_of_cube {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {q : ℕ}
    {E : Subgroup (MulAut (twistedE6RootGroup K σ))} (hE : TwE6Cube K σ q E)
    {f : MulAut (twistedE6RootGroup K σ)} (hf : f ∈ E) (hf1 : f ≠ 1) {d : ℕ}
    (hd : TwE6LineDim K σ f d) :
    ∃ h : twistedE6InndiagGL K σ, twistedE6InndiagConj K σ h = f ∧ h ≠ 1 ∧ h ^ 3 = 1 ∧
      twE6MatFixDim K σ h = d ∧ Nonempty (TwE6LineLang K σ q h) := by
  have hq2 : 2 ≤ q := by
    have := Nat.le_of_dvd (by omega) hE.three_dvd
    omega
  obtain ⟨h, hh, hdim⟩ := hd
  have hinj := twE6_conj_injective K σ q hE.frob hE.card_field hq2
  have hh1 : h ≠ 1 := by
    rintro rfl
    exact hf1 (hh.symm.trans (map_one _))
  have hh3 : h ^ 3 = 1 := by
    apply hinj
    rw [map_pow, hh, map_one]
    exact hE.elemAbelian.2 f hf
  exact ⟨h, hh, hh1, hh3, hdim,
    nonempty_twE6LineLang K σ q hE.char_ne_three hE.frob hE.card_field hq2 h hh1 hh3⟩

end Lang

end KSNotAll24

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
