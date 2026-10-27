module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagTwisted
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.FamOpen
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4Cont
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6HeisenbergAux.LangStep
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6HeisenbergAux.Pair
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6HeisenbergAux.Rigid
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6HeisenbergAux.TwLang
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiag
public import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagAssembly
public import CFSG.Sporadic.Suz.Simple

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.PartOne.KE

section FR


structure LangMatData (τ : Tag) (K : Type) [Field K] [Finite K] where
  w : WeylGroup τ
  Fr : AlgebraicClosure K →+* AlgebraicClosure K
  hFr : ∀ c, Fr c = c ^ Nat.card K
  g0 : ModGL τ (AlgebraicClosure K)
  hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K)
  hg0 : Units.map (entrywiseHom Fr) g0 =
    g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w

theorem e6_normalized_of_fixedRoot
    (K : Type) [Field K] [Finite K] (hK3 : ringChar K ≠ 3) {ι : Type} (xs : ι → ModGL Tag.E6 K)
    (hxsN : ∀ i, ∀ g ∈ adjointGroup Tag.E6 K, xs i * g * (xs i)⁻¹ ∈ adjointGroup Tag.E6 K)
    (D : LangMatData Tag.E6 K)
    (hxs : ∀ i, baseChangeGL (algebraMap K (AlgebraicClosure K)) (xs i) ∈
      (twistedTorusOf (canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) D.w)
        (Units.map (entrywiseHom D.Fr))).map (MulAut.conj D.g0).toMonoidHom)
    (β : Fin Tag.E6.rank → ℤ) (hβ : IsRoot Tag.E6 β) (hw : D.w • β = β) :
    ∃ R : Subgroup (ModGL Tag.E6 K), R ≤ adjointGroup Tag.E6 K ∧ R ≠ ⊥ ∧
      IsPGroup (ringChar K) R ∧ ∀ i, ∀ r ∈ R, xs i * r * (xs i)⁻¹ ∈ R := by
  classical
  obtain ⟨e, he, hcard⟩ := card_eq_pow_ringChar K
  haveI : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  set L := AlgebraicClosure K with hL
  have hFrEq : D.Fr = iterateFrobenius L (ringChar K) e :=
    RingHom.ext fun c => by rw [D.hFr c, iterateFrobenius_def, hcard]
  have hFrob : ∀ g : ModGL Tag.E6 L,
      Units.map (entrywiseHom D.Fr) g = entrywiseFrobGL Tag.E6 L (ringChar K) e g := by
    intro g
    rw [hFrEq]
  set n := canonicalRep (coxeterSystem Tag.E6) L D.w with hn
  set Φ := frobTwistGL Tag.E6 L (ringChar K) e n with hΦ
  have hΦapp : ∀ g, Φ g = n * Units.map (entrywiseHom D.Fr) g * n⁻¹ := fun g => by
    rw [hΦ, frobTwistGL_apply, hFrob]
  set U := rootSubgroup Tag.E6 L β with hU
  set RL : Subgroup (ModGL Tag.E6 L) := U ⊓ Φ.eqLocus (MonoidHom.id _) with hRL
  have hRLmem : ∀ x, x ∈ RL ↔ x ∈ U ∧ Φ x = x := fun x => Iff.rfl
  obtain ⟨s0, hs0⟩ := exists_sign_family (L := L) (τ := Tag.E6) D.w
  obtain ⟨v, hvspan, hvF, hv1, hvp⟩ := exists_cycle_element (L := L) (ringChar K) e he D.w 1
    one_pos (fun _ => β) (fun _ => rfl) (fun _ => hβ)
    (fun k l hk hl hkl => absurd (by omega : k = l) hkl) (fun _ => by simpa using hw) {β}
    (fun _ => Set.mem_singleton _)
  have hvU : v ∈ U := by
    rw [hU, ← rootSpan_singleton]
    exact hvspan
  have hvRL : v ∈ RL := ⟨hvU, hvF⟩
  have hg0F : entrywiseFrobGL Tag.E6 L (ringChar K) e D.g0 = D.g0 * n := by
    rw [← hFrob]; exact D.hg0
  have huLad : D.g0 * v * D.g0⁻¹ ∈ adjointGroup Tag.E6 L := by
    refine mul_mem (mul_mem D.hg0C ?_) (inv_mem D.hg0C)
    have := rootSpan_le_adjointGroup (τ := Tag.E6) (K := L) ({β} : Set (Fin Tag.E6.rank → ℤ))
    exact this (by rw [rootSpan_singleton]; exact hvU)
  have hFv : entrywiseFrobGL Tag.E6 L (ringChar K) e v = n⁻¹ * v * n := by
    have h1 : n * entrywiseFrobGL Tag.E6 L (ringChar K) e v * n⁻¹ = v := by
      have := hvF
      rw [frobTwistGL_apply] at this
      exact this
    calc entrywiseFrobGL Tag.E6 L (ringChar K) e v
        = n⁻¹ * (n * entrywiseFrobGL Tag.E6 L (ringChar K) e v * n⁻¹) * n := by group
      _ = n⁻¹ * v * n := by rw [h1]
  have huLF : Units.map (entrywiseHom D.Fr) (D.g0 * v * D.g0⁻¹) = D.g0 * v * D.g0⁻¹ := by
    rw [hFrob, map_mul, map_mul, map_inv, hg0F, hFv]
    group
  have huL1 : D.g0 * v * D.g0⁻¹ ≠ 1 := by
    intro h
    apply hv1
    calc v = D.g0⁻¹ * (D.g0 * v * D.g0⁻¹) * D.g0 := by group
      _ = 1 := by rw [h]; group
  have huLo : (D.g0 * v * D.g0⁻¹) ^ ringChar K = 1 := by
    rw [conj_pow, hvp]; group
  have hcop : ringChar K ≠ 3 → Nat.Coprime 3 (orderOf (D.g0 * v * D.g0⁻¹)) := by
    intro h
    rw [orderOf_eq_prime huLo huL1]
    exact (Nat.coprime_primes Nat.prime_three Fact.out).2 (Ne.symm h)
  obtain ⟨r₀, hr₀mem, hr₀eq⟩ := Subgroup.mem_map.1
    (CFSG.HardMathSupport.Malle.SeitzCube.mem_map_baseChange_of_frobenius_fixed_E6 D.Fr D.hFr
      huLad huLF hcop)
  have hinj := baseChangeGL_injective (τ := Tag.E6) (algebraMap K L)
  set R : Subgroup (ModGL Tag.E6 K) :=
    adjointGroup Tag.E6 K ⊓ (RL.map (MulAut.conj D.g0).toMonoidHom).comap
      (baseChangeGL (algebraMap K L)) with hR
  have hRmem : ∀ r, r ∈ R ↔ r ∈ adjointGroup Tag.E6 K ∧
      ∃ y ∈ RL, D.g0 * y * D.g0⁻¹ = baseChangeGL (algebraMap K L) r := by
    intro r
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨y, hy, hyr⟩ := h2
      exact ⟨h1, y, hy, hyr⟩
    · rintro ⟨h1, y, hy, hyr⟩
      exact ⟨h1, y, hy, hyr⟩
  refine ⟨R, inf_le_left, ?_, ?_, ?_⟩
  · intro h
    have hr₀R : r₀ ∈ R := (hRmem r₀).2 ⟨hr₀mem, v, hvRL, hr₀eq.symm⟩
    rw [h] at hr₀R
    have : r₀ = 1 := Subgroup.mem_bot.1 hr₀R
    apply huL1
    rw [← hr₀eq, this, map_one]
  · intro g
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨hgad, y, hy, hyr⟩ := (hRmem (g : ModGL Tag.E6 K)).1 g.2
    rw [pow_one]
    apply hinj
    simp only [Subgroup.coe_pow, Subgroup.coe_one, map_pow, map_one]
    rw [← hyr, conj_pow]
    obtain ⟨c, hc⟩ := mem_rootSubgroup.1 hy.1
    rw [← hc, pinnedX_pow_char (ringChar K) β c]
    group
  · intro i r hr
    obtain ⟨hrad, y, hy, hyr⟩ := (hRmem r).1 hr
    refine (hRmem _).2 ⟨hxsN i r hrad, ?_⟩
    obtain ⟨t, ht, hxt⟩ := Subgroup.mem_map.1 (hxs i)
    obtain ⟨htT, htF⟩ := mem_twistedTorusOf.1 ht
    refine ⟨t * y * t⁻¹, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup htT
        have := map_conj_rootDiagUnit_rootSubgroup (K := L) a hβ
        have hyU : y ∈ U := hy.1
        have h2 : (MulAut.conj (rootDiagUnit Tag.E6 a)).toMonoidHom y ∈
            (rootSubgroup Tag.E6 L β).map (MulAut.conj (rootDiagUnit Tag.E6 a)).toMonoidHom :=
          Subgroup.mem_map_of_mem _ hyU
        rw [this] at h2
        rw [ha]
        simpa [MulAut.conj_apply] using h2
      · have htΦ : Φ t = t := by
          rw [hΦapp]; exact htF
        have hyΦ : Φ y = y := hy.2
        change Φ (t * y * t⁻¹) = t * y * t⁻¹
        rw [map_mul, map_mul, map_inv, htΦ, hyΦ]
    · rw [map_mul, map_mul, map_inv, ← hxt, ← hyr]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

end FR

end CFSG.LieType.SeitzGeneration.ExcHighThree

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.CTP CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Fischer CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross (E6DiagIsotropic TwistedE6DiagIsotropic)


theorem exists_outer_matrix (K : Type) [Field K] [Finite K]
    (E : Subgroup (MulAut (adjointGroup Tag.E6 K))) (hE : E ≤ e6Inndiag K)
    (hnin : ¬ E ≤ innerAut (adjointGroup Tag.E6 K)) :
    ∃ x ∈ e6PlanePre K E, x ∉ adjointGroup Tag.E6 K := by
  by_contra h
  push Not at h
  apply hnin
  intro ε hε
  have hεr : ε ∈ (e6InndiagConj K).range := by
    rw [range_e6InndiagConj]
    exact hE hε
  obtain ⟨g, rfl⟩ := hεr
  have hg : (g : ModGL Tag.E6 K) ∈ e6PlanePre K E := (mem_e6PlanePre_iff K E _).2 ⟨g, rfl, hε⟩
  refine ⟨⟨g, h _ hg⟩, ?_⟩
  ext y
  rfl

theorem exists_langGLData (htor : E6PlaneToralLang) {K : Type} [Field K] [Finite K]
    (hK3 : ringChar K ≠ 3) (hK4 : 4 ≤ Nat.card K)
    (K₁ : IntermediateField K (AlgebraicClosure K)) [Finite K₁]
    (hroot : ∀ c : Kˣ, ∃ u : K₁ˣ, u ^ 3 = Units.map (algebraMap K K₁).toMonoidHom c)
    (E : Subgroup (MulAut (adjointGroup Tag.E6 K))) (hE : CFSG.IsElementaryAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 2) (hd : E ≤ e6Inndiag K)
    (hiso : E6DiagIsotropic K K₁ E) :
    Nonempty (LangGLData Tag.E6 K (e6PlanePre K E)) := by
  have h3 : ¬ 3 ∣ Nat.card K := not_three_dvd_card_of_ringChar K hK3
  have hinj := e6InndiagConj_injective K hK4
  have hEr : E ≤ (e6InndiagConj K).range := by
    rw [range_e6InndiagConj]; exact hd
  have hmap : (E.comap (e6InndiagConj K)).map (e6InndiagConj K) = E :=
    Subgroup.map_comap_eq_self hEr
  have hexp : ∀ x ∈ E.comap (e6InndiagConj K), x ^ 3 = 1 := fun x hx =>
    hinj (by rw [map_pow, map_one]; exact CFSG.elemPow_eq_one_of_isElementaryAbelian _ hx)
  have hcard₀ : Nat.card (E.comap (e6InndiagConj K)) = 3 ^ 2 := by
    rw [← Subgroup.card_map_of_injective hinj, hmap]; exact hcard
  have hC₁ : ∀ x ∈ E.comap (e6InndiagConj K), baseChangeGL (algebraMap K K₁)
      (x : ModGL Tag.E6 K) ∈ adjointGroup Tag.E6 K₁ := fun x _ =>
    map_e6InndiagGL_le _ hroot (Subgroup.mem_map_of_mem _ x.2)
  obtain ⟨w, Fr, hFr, g0, hg0C, hg0, hin⟩ :=
    e6IsotropicToralInndiag_of_planeToralLang htor K h3 K₁ (E.comap (e6InndiagConj K)) hexp hcard₀
      hC₁ (fun x y hx hy => hiso x y hx hy)
  refine ⟨⟨w, Fr, hFr, g0, hg0C, hg0, 1, one_mem _, fun x hx => ?_⟩⟩
  obtain ⟨y, hy, rfl⟩ := hx
  simpa using hin y hy

@[expose] def E6HeisenbergParabolic : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 3 →
    ∀ (K₁ : IntermediateField K (AlgebraicClosure K)) [Finite K₁],
      (∀ c : Kˣ, ∃ u : K₁ˣ, u ^ 3 = Units.map (algebraMap K K₁).toMonoidHom c) →
      ∀ E : Subgroup (MulAut (adjointGroup Tag.E6 K)), CFSG.IsElementaryAbelian 3 E →
        Nat.card E = 3 ^ 2 → E ≤ e6Inndiag K → ¬ E ≤ innerAut (adjointGroup Tag.E6 K) →
        ¬ E6DiagIsotropic K K₁ E → E6NormalizesR K E

theorem e6InndiagTorality_of_heisenberg (hH : E6HeisenbergParabolic) : E6InndiagTorality := by
  intro K _ _ hK3 E hE hEab hcard hnin
  obtain ⟨K₁, hK₁, hroot⟩ := exists_cubeExt K
  have hK4 := four_le_card_of_not_innerAut K hK3 E hE hnin
  by_cases hiso : E6DiagIsotropic K K₁ E
  · left
    obtain ⟨D⟩ := exists_langGLData e6PlaneToralLang_proved hK3 hK4 K₁ hroot E hEab hcard hE hiso
    exact ⟨D, exists_outer_matrix K E hE hnin⟩
  · right
    exact hH K hK3 K₁ hroot E hEab hcard hE hnin hiso

theorem e6NormalizesR_of_matrix {K : Type} [Field K] [Finite K]
    (E : Subgroup (MulAut (adjointGroup Tag.E6 K))) (hE : E ≤ e6Inndiag K)
    (R : Subgroup (ModGL Tag.E6 K)) (hRC : R ≤ adjointGroup Tag.E6 K) (hR1 : R ≠ ⊥)
    (hRp : IsPGroup (ringChar K) R)
    (hRn : ∀ x ∈ e6PlanePre K E, ∀ r ∈ R, x * r * x⁻¹ ∈ R) : E6NormalizesR K E := by
  classical
  refine ⟨R.subgroupOf (adjointGroup Tag.E6 K), ?_, ?_, ?_⟩
  · intro h
    apply hR1
    rw [eq_bot_iff]
    intro r hr
    have h0 : (⟨r, hRC hr⟩ : ↥(adjointGroup Tag.E6 K)) ∈ R.subgroupOf (adjointGroup Tag.E6 K) := hr
    rw [h] at h0
    exact Subgroup.mem_bot.2 (congrArg Subtype.val (Subgroup.mem_bot.1 h0))
  · exact hRp.comap_of_injective (adjointGroup Tag.E6 K).subtype
      (adjointGroup Tag.E6 K).subtype_injective
  · have key : ∀ ε ∈ E, (R.subgroupOf (adjointGroup Tag.E6 K)).map ε.toMonoidHom ≤
        R.subgroupOf (adjointGroup Tag.E6 K) := by
      intro ε hε
      obtain ⟨g, rfl⟩ : ε ∈ (e6InndiagConj K).range := by
        rw [range_e6InndiagConj]
        exact hE hε
      have hg : (g : ModGL Tag.E6 K) ∈ e6PlanePre K E :=
        (mem_e6PlanePre_iff K E _).2 ⟨g, rfl, hε⟩
      rintro _ ⟨r, hr, rfl⟩
      change ((e6InndiagConj K g r : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) ∈ R
      rw [e6InndiagConj_apply]
      exact hRn _ hg _ hr
    intro ε hε
    refine le_antisymm (key ε hε) fun x hx => ?_
    refine ⟨ε⁻¹ x, key ε⁻¹ (inv_mem hε) ⟨x, hx, rfl⟩, ?_⟩
    simp

theorem matrix_of_e6NormalizesR {K : Type} [Field K] [Finite K]
    (E : Subgroup (MulAut (adjointGroup Tag.E6 K))) (hE : E ≤ e6Inndiag K)
    (h : E6NormalizesR K E) :
    ∃ R : Subgroup (ModGL Tag.E6 K), R ≤ adjointGroup Tag.E6 K ∧ R ≠ ⊥ ∧
      IsPGroup (ringChar K) R ∧ e6PlanePre K E ≤ Subgroup.normalizer (R : Set (ModGL Tag.E6 K)) := by
  obtain ⟨R, hR1, hRp, hRn⟩ := h
  refine ⟨R.map (adjointGroup Tag.E6 K).subtype, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨r, -, rfl⟩
    exact r.2
  · intro hbot
    apply hR1
    exact (Subgroup.map_eq_bot_iff_of_injective R (adjointGroup Tag.E6 K).subtype_injective).1 hbot
  · exact hRp.map _
  · intro x hx
    obtain ⟨g, rfl, hgE⟩ := (mem_e6PlanePre_iff K E x).1 hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨r, hr, rfl⟩
      have hr' : e6InndiagConj K g r ∈ R.map (e6InndiagConj K g).toMonoidHom := ⟨r, hr, rfl⟩
      rw [hRn _ hgE] at hr'
      exact ⟨_, hr', by simp [e6InndiagConj_apply]⟩
    · rintro ⟨r', hr', hy⟩
      have hr'' : r' ∈ R.map (e6InndiagConj K g).toMonoidHom := by rw [hRn _ hgE]; exact hr'
      obtain ⟨r, hr, rfl⟩ := hr''
      refine ⟨r, hr, ?_⟩
      have h1 : (g : ModGL Tag.E6 K) * (r : ModGL Tag.E6 K) * (g : ModGL Tag.E6 K)⁻¹ =
          (g : ModGL Tag.E6 K) * y * (g : ModGL Tag.E6 K)⁻¹ := by
        rw [← e6InndiagConj_apply]
        exact hy
      have := mul_left_cancel (mul_right_cancel h1)
      exact this

@[expose] def E6RegularOuterFixedRoot : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 3 →
    ∀ E : Subgroup (MulAut (adjointGroup Tag.E6 K)), E ≤ e6Inndiag K →
      CFSG.IsElementaryAbelian 3 E → Nat.card E = 3 ^ 2 →
      ∀ D : LangGLData Tag.E6 K (e6PlanePre K E),
        (¬ ∃ α : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 α ∧ D.Kills α) →
        (∃ x ∈ e6PlanePre K E, x ∉ adjointGroup Tag.E6 K) →
        ∃ β : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 β ∧ D.w • β = β

theorem e6DiagRegularOuter_of_fixedRoot (hR : E6RegularOuterFixedRoot) : E6DiagRegularOuter := by
  intro K _ _ hK3 E hE hEab hcard D hreg hout
  obtain ⟨β, hβ, hw⟩ := hR K hK3 E hE hEab hcard D hreg hout
  have hnormA : ∀ x ∈ e6PlanePre K E, x ∈ Subgroup.normalizer
      (adjointGroup Tag.E6 K : Set (ModGL Tag.E6 K)) := fun x hx => by
    obtain ⟨g, rfl, -⟩ := (mem_e6PlanePre_iff K E x).1 hx
    exact e6InndiagGL_le_normalizer K g.2
  have hcxc : ∀ x ∈ e6PlanePre K E, D.c * x * D.c⁻¹ ∈ Subgroup.normalizer
      (adjointGroup Tag.E6 K : Set (ModGL Tag.E6 K)) := fun x hx =>
    mul_mem (mul_mem D.hcN (hnormA x hx)) (inv_mem D.hcN)
  obtain ⟨R, hRC, hR1, hRp, hRn⟩ := ExcHighThree.e6_normalized_of_fixedRoot K hK3
    (ι := ↥(e6PlanePre K E)) (fun x => D.c * (x : ModGL Tag.E6 K) * D.c⁻¹)
    (fun x g hg => (Subgroup.mem_normalizer_iff.1 (hcxc x.1 x.2) g).1 hg)
    ⟨D.w, D.Fr, D.hFr, D.g0, D.hg0C, D.hg0⟩ (fun x => D.hc x.1 x.2) β hβ hw
  have hcn : ∀ y, y ∈ adjointGroup Tag.E6 K ↔ D.c * y * D.c⁻¹ ∈ adjointGroup Tag.E6 K :=
    fun y => Subgroup.mem_normalizer_iff.1 D.hcN y
  refine e6NormalizesR_of_matrix E hE (R.map (MulAut.conj D.c⁻¹).toMonoidHom) ?_ ?_ ?_ ?_
  · rintro _ ⟨r, hr, rfl⟩
    have := hcn (D.c⁻¹ * r * D.c)
    rw [show D.c * (D.c⁻¹ * r * D.c) * D.c⁻¹ = r by group] at this
    exact this.2 (hRC hr)
  · intro h
    apply hR1
    have := (Subgroup.map_eq_bot_iff_of_injective R (MulAut.conj D.c⁻¹).injective).1 h
    exact this
  · exact hRp.map _
  · rintro x hx _ ⟨r, hr, rfl⟩
    refine ⟨D.c * x * D.c⁻¹ * r * (D.c * x * D.c⁻¹)⁻¹, hRn ⟨x, hx⟩ r hr, ?_⟩
    simp [MulAut.conj_apply]
    group

@[expose] def E6InndiagCentralizerGeneration : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (r : ℕ) [Fact r.Prime] [CharP K r], r ≠ 3 →
    ∀ (A : Subgroup (ModGL Tag.E6 K)), A ≤ e6InndiagGL K → CFSG.IsElementaryAbelian 3 A →
      3 ^ 2 ≤ Nat.card A →
      ∀ R : Subgroup (ModGL Tag.E6 K), R ≤ adjointGroup Tag.E6 K → IsPGroup r R → R ≠ ⊥ →
        A ≤ Subgroup.normalizer (R : Set (ModGL Tag.E6 K)) →
        (⨆ a ∈ A, ⨆ (_ : a ≠ 1), adjointGroup Tag.E6 K ⊓
          Subgroup.centralizer ({a} : Set (ModGL Tag.E6 K))) = adjointGroup Tag.E6 K

theorem e6InndiagParabolic_of_generic (hG : E6InndiagCentralizerGeneration) :
    E6InndiagParabolic := by
  intro K _ _ hK3 E hE hEab hcard hnin hnorm
  classical
  have hK4 := four_le_card_of_not_innerAut K hK3 E hE hnin
  have hinj := e6InndiagConj_injective K hK4
  obtain ⟨R, hRC, hR1, hRp, hRn⟩ := matrix_of_e6NormalizesR E hE hnorm
  haveI : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  haveI : CharP K (ringChar K) := ringChar.charP K
  have hAle : e6PlanePre K E ≤ e6InndiagGL K := by
    rintro _ hx
    obtain ⟨g, rfl, -⟩ := (mem_e6PlanePre_iff K E _).1 hx
    exact g.2
  have hAcomm : ∀ a ∈ e6PlanePre K E, ∀ b ∈ e6PlanePre K E, a * b = b * a := by
    intro a ha b hb
    obtain ⟨g, rfl, hg⟩ := (mem_e6PlanePre_iff K E a).1 ha
    obtain ⟨h, rfl, hh⟩ := (mem_e6PlanePre_iff K E b).1 hb
    have : g * h = h * g := by
      apply hinj
      rw [map_mul, map_mul]
      exact congrArg Subtype.val (hEab.is_comm.comm ⟨_, hg⟩ ⟨_, hh⟩)
    exact congrArg Subtype.val this
  have hAEA : CFSG.IsElementaryAbelian 3 (e6PlanePre K E) :=
    CFSG.IsElementaryAbelian.of_forall hAcomm fun a ha =>
      pow_three_eq_one_of_mem_e6PlanePre K hK4 E ha
  have hAcard : Nat.card (e6PlanePre K E) = 3 ^ 2 := by
    rw [card_e6PlanePre K hK4 E hE]
    exact hcard
  have hgen := hG K (ringChar K) hK3 (e6PlanePre K E) hAle hAEA hAcard.ge R hRC hRp hR1 hRn
  have hsub : ∀ a ∈ e6PlanePre K E, a ≠ 1 → adjointGroup Tag.E6 K ⊓ Subgroup.centralizer ({a} : Set (ModGL Tag.E6 K)) ≤
      (Subgroup.closure (fixUnion E)).map (adjointGroup Tag.E6 K).subtype := by
    intro a ha ha1 y hy
    obtain ⟨g, rfl, hgE⟩ := (mem_e6PlanePre_iff K E a).1 ha
    have hyC : y ∈ adjointGroup Tag.E6 K := hy.1
    have hcomm : (g : ModGL Tag.E6 K) * y = y * (g : ModGL Tag.E6 K) := by
      exact Subgroup.mem_centralizer_iff.1 hy.2 (g : ModGL Tag.E6 K) rfl
    refine ⟨⟨y, hyC⟩, Subgroup.subset_closure ?_, rfl⟩
    refine ⟨Subgroup.zpowers (e6InndiagConj K g), ?_, ?_, ?_⟩
    · rw [Subgroup.zpowers_le]
      exact hgE
    · intro hbot
      have hmem : e6InndiagConj K g ∈ (⊥ : Subgroup (MulAut ↥(adjointGroup Tag.E6 K))) := hbot ▸ Subgroup.mem_zpowers _
      have : g = 1 := hinj (by simpa using hmem)
      exact ha1 (by rw [this]; rfl)
    · intro φ hφ
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hφ
      rw [← map_zpow]
      apply Subtype.ext
      rw [e6InndiagConj_apply]
      have hc : Commute (y : ModGL Tag.E6 K) ((g ^ n : ↥(e6InndiagGL K)) : ModGL Tag.E6 K) := by
        have h1 : Commute (y : ModGL Tag.E6 K) (g : ModGL Tag.E6 K) := hcomm.symm
        simpa using h1.zpow_right n
      calc ((g ^ n : ↥(e6InndiagGL K)) : ModGL Tag.E6 K) * y *
            ((g ^ n : ↥(e6InndiagGL K)) : ModGL Tag.E6 K)⁻¹
          = y * ((g ^ n : ↥(e6InndiagGL K)) : ModGL Tag.E6 K) *
              ((g ^ n : ↥(e6InndiagGL K)) : ModGL Tag.E6 K)⁻¹ := by rw [hc.eq]
        _ = y := by group
  have hle : adjointGroup Tag.E6 K ≤ (Subgroup.closure (fixUnion E)).map (adjointGroup Tag.E6 K).subtype := by
    exact le_trans (le_of_eq hgen.symm) (iSup₂_le fun a ha => iSup_le fun ha1 => hsub a ha ha1)
  rw [eq_top_iff]
  intro y _
  obtain ⟨t, ht, hty⟩ := hle y.2
  have : t = y := Subtype.ext hty
  rw [← this]
  exact ht

end CFSG.LieType.SeitzGeneration.ExcWideThree

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.CTP CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Fischer CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross (E6DiagIsotropic TwistedE6DiagIsotropic)


@[expose] def TwE6InndiagTorality' : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ), ringChar K ≠ 3 → (∀ c, σ c = c ^ q) →
    Nat.card K = q ^ 2 →
    ∀ E : Subgroup (MulAut (twistedE6RootGroup K σ)),
      E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ → CFSG.IsElementaryAbelian 3 E →
      Nat.card E = 3 ^ 2 → ¬ E ≤ innerAut (twistedE6RootGroup K σ) →
      (∃ D : TwLangData K σ q (twPlanePre K σ E), ∃ x ∈ twPlanePre K σ E,
          x ∉ twistedE6RootGroup K σ) ∨ TwE6NormalizesR K σ E

@[expose] def TwE6InndiagParabolic' : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ), ringChar K ≠ 3 → (∀ c, σ c = c ^ q) →
    Nat.card K = q ^ 2 →
    ∀ E : Subgroup (MulAut (twistedE6RootGroup K σ)),
      E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ → CFSG.IsElementaryAbelian 3 E →
      Nat.card E = 3 ^ 2 → ¬ E ≤ innerAut (twistedE6RootGroup K σ) → TwE6NormalizesR K σ E →
      Subgroup.closure (fixUnion E) = ⊤

theorem twistedE6ThreeDiagPlanes_of_open' (hT : TwE6InndiagTorality') (hO : TwE6DiagRegularGen)
    (hKR : TwE6KillRoot) (hP : TwE6InndiagParabolic') : TwistedE6ThreeDiagPlanes := by
  intro ℓ f hℓ hℓ3 hf K _ _ hK σ hσ E hEab hcard hE hnin
  have hp : ringChar K = ℓ := ringChar_eq_of_card_pow hℓ hf K hK
  have hK3 : ringChar K ≠ 3 := by
    rw [hp]
    exact hℓ3
  have hK' : Nat.card K = (ℓ ^ f) ^ 2 := by
    rw [hK, ← pow_mul, mul_comm]
  rcases hT K σ (ℓ ^ f) hK3 hσ hK' E hE hEab hcard hnin with ⟨D, x, hxA, hxout⟩ | hnorm
  · by_cases hkillex : ∃ α : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag α ∧
        ∀ x ∈ twPlanePre K σ E, ∃ a : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ,
          rootDiagUnit TwistTag.E6.tag a = D.g0⁻¹ *
            baseChangeGL (algebraMap K (AlgebraicClosure K))
              (D.c * x * D.c⁻¹ : ModGL TwistTag.E6.tag K) * D.g0 ∧ rootChar a α = 1
    swap
    · exact hO K σ (ℓ ^ f) hK3 hσ hK' E hE hEab hcard hnin D hkillex
    obtain ⟨α, hα, hkill⟩ := hkillex
    obtain ⟨u, hu, hu1, ⟨n, hn⟩, hcomm⟩ :=
      hKR K σ (ℓ ^ f) hK3 hσ hK' (twPlanePre K σ E) D α hα hkill
    set U : twistedE6RootGroup K σ := ⟨u, hu⟩ with hUdef
    have hU1 : U ≠ 1 := by
      intro h
      apply hu1
      have := congrArg Subtype.val h
      simpa [hUdef] using this
    have hUn : U ^ (ringChar K ^ n) = 1 := by
      apply Subtype.ext
      simpa [hUdef] using hn
    have hRp : IsPGroup (ringChar K) (Subgroup.zpowers U) := by
      intro g
      refine ⟨n, Subtype.ext ?_⟩
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 g.2
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hUn, one_zpow]
    refine hP K σ (ℓ ^ f) hK3 hσ hK' E hE hEab hcard hnin ⟨Subgroup.zpowers U, ?_, hRp, ?_⟩
    · exact fun h => hU1 (Subgroup.zpowers_eq_bot.1 h)
    · intro ε hεE
      have hεr : ε ∈ (twistedE6InndiagConj K σ).range := by
        rw [range_twistedE6InndiagConj]
        exact hE hεE
      obtain ⟨g, rfl⟩ := hεr
      have hgA : (g : ModGL TwistTag.E6.tag K) ∈ twPlanePre K σ E :=
        (mem_twPlanePre_iff K σ E _).2 ⟨g, rfl, hεE⟩
      have hfix : twistedE6InndiagConj K σ g U = U := by
        apply Subtype.ext
        rw [twistedE6InndiagConj_apply]
        show (g : ModGL TwistTag.E6.tag K) * u * (g : ModGL TwistTag.E6.tag K)⁻¹ = u
        rw [mul_inv_eq_iff_eq_mul]
        exact (hcomm _ hgA).symm
      have hfix' : (twistedE6InndiagConj K σ g).toMonoidHom U = U := hfix
      rw [MonoidHom.map_zpowers, hfix']
  · exact hP K σ (ℓ ^ f) hK3 hσ hK' E hE hEab hcard hnin hnorm

theorem exists_outer_matrix_tw (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (E : Subgroup (MulAut (twistedE6RootGroup K σ))) (hE : E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ)
    (hnin : ¬ E ≤ innerAut (twistedE6RootGroup K σ)) :
    ∃ x ∈ twPlanePre K σ E, x ∉ twistedE6RootGroup K σ := by
  by_contra h
  push Not at h
  apply hnin
  intro ε hε
  have hεr : ε ∈ (twistedE6InndiagConj K σ).range := by
    rw [range_twistedE6InndiagConj]
    exact hE hε
  obtain ⟨g, rfl⟩ := hεr
  have hg : (g : ModGL TwistTag.E6.tag K) ∈ twPlanePre K σ E :=
    (mem_twPlanePre_iff K σ E _).2 ⟨g, rfl, hε⟩
  refine ⟨⟨g, h _ hg⟩, ?_⟩
  ext y
  rfl

theorem exists_twLangData (htor : TwistedE6PlaneToralLang) (ℓ f : ℕ) (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3)
    (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (K₁ : IntermediateField K (AlgebraicClosure K)) [Finite K₁]
    (hroot : ∀ c : Kˣ, ∃ u : K₁ˣ, u ^ 3 = Units.map (algebraMap K K₁).toMonoidHom c)
    (E : Subgroup (MulAut (twistedE6RootGroup K σ))) (hE : CFSG.IsElementaryAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 2) (hd : E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ)
    (hiso : TwistedE6DiagIsotropic K σ K₁ E) :
    Nonempty (TwLangData K σ (ℓ ^ f) (twPlanePre K σ E)) := by
  have hinj := twistedE6InndiagConj_injective hℓ hf hK σ hσ
  have hEr : E ≤ (twistedE6InndiagConj K σ).range := by
    rw [range_twistedE6InndiagConj]; exact hd
  have hmap : (E.comap (twistedE6InndiagConj K σ)).map (twistedE6InndiagConj K σ) = E :=
    Subgroup.map_comap_eq_self hEr
  have hexp : ∀ x ∈ E.comap (twistedE6InndiagConj K σ), x ^ 3 = 1 := fun x hx =>
    hinj (by rw [map_pow, map_one]; exact CFSG.elemPow_eq_one_of_isElementaryAbelian _ hx)
  have hcard₀ : Nat.card (E.comap (twistedE6InndiagConj K σ)) = 3 ^ 2 := by
    rw [← Subgroup.card_map_of_injective hinj, hmap]; exact hcard
  have hC₁ : ∀ x ∈ E.comap (twistedE6InndiagConj K σ), baseChangeGL (algebraMap K K₁)
      (x : ModGL TwistTag.E6.tag K) ∈ adjointGroup Tag.E6 K₁ := fun x _ =>
    map_twistedE6InndiagGL_le σ _ hroot (Subgroup.mem_map_of_mem _ x.2)
  obtain ⟨v, Fr, hFr, g0, hg0C, hg0, hin⟩ :=
    twistedE6IsotropicToralInndiag_of_planeToralLang htor ℓ f hℓ hℓ3 hf K hK σ hσ K₁
      (E.comap (twistedE6InndiagConj K σ)) hexp hcard₀ hC₁ (fun x y hx hy => hiso x y hx hy)
  refine ⟨⟨v, Fr, hFr, g0, hg0C, hg0, 1, one_mem _, fun x hx => ?_⟩⟩
  obtain ⟨y, hy, rfl⟩ := hx
  simpa using hin y hy

@[expose] def TwE6HeisenbergParabolic : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ), ringChar K ≠ 3 → (∀ c, σ c = c ^ q) →
    Nat.card K = q ^ 2 →
    ∀ (K₁ : IntermediateField K (AlgebraicClosure K)) [Finite K₁],
      (∀ c : Kˣ, ∃ u : K₁ˣ, u ^ 3 = Units.map (algebraMap K K₁).toMonoidHom c) →
      ∀ E : Subgroup (MulAut (twistedE6RootGroup K σ)),
        E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ → CFSG.IsElementaryAbelian 3 E →
        Nat.card E = 3 ^ 2 → ¬ E ≤ innerAut (twistedE6RootGroup K σ) →
        ¬ TwistedE6DiagIsotropic K σ K₁ E → TwE6NormalizesR K σ E

theorem twE6InndiagTorality'_of_heisenberg (hH : TwE6HeisenbergParabolic) :
    TwE6InndiagTorality' := by
  intro K _ _ σ q hK3 hσ hK E hE hEab hcard hnin
  obtain ⟨hp, f, hf, rfl⟩ := ExcHighThree.exists_pow_ringChar_of_card_sq K q hK
    (by
      by_contra h
      have hq : q ≤ 1 := by omega
      have : Nat.card K ≤ 1 := by
        rw [hK]; nlinarith [Nat.zero_le q]
      have h2 : 2 ≤ Nat.card K := Finite.one_lt_card
      omega)
  obtain ⟨K₁, hK₁, hroot⟩ := exists_cubeExt K
  by_cases hiso : TwistedE6DiagIsotropic K σ K₁ E
  · left
    obtain ⟨D⟩ := exists_twLangData twistedE6PlaneToralLang_proved (ringChar K) f hp hK3 hf hK σ hσ
      K₁ hroot E hEab hcard hE hiso
    exact ⟨D, exists_outer_matrix_tw K σ E hE hnin⟩
  · right
    exact hH K σ _ hK3 hσ hK K₁ hroot E hE hEab hcard hnin hiso

end CFSG.LieType.SeitzGeneration.ExcWideThree

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.CTP CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Fischer CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny


@[expose] def TwE6InndiagCentralizerGeneration : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ), ringChar K ≠ 3 → (∀ c, σ c = c ^ q) →
    Nat.card K = q ^ 2 →
    ∀ (A : Subgroup (ModGL TwistTag.E6.tag K)), A ≤ twistedE6InndiagGL K σ →
      CFSG.IsElementaryAbelian 3 A → 3 ^ 2 ≤ Nat.card A →
      ∀ R : Subgroup (ModGL TwistTag.E6.tag K), R ≤ twistedE6RootGroup K σ →
        IsPGroup (ringChar K) R → R ≠ ⊥ →
        A ≤ Subgroup.normalizer (R : Set (ModGL TwistTag.E6.tag K)) →
        (⨆ a ∈ A, ⨆ (_ : a ≠ 1), twistedE6RootGroup K σ ⊓
          Subgroup.centralizer ({a} : Set (ModGL TwistTag.E6.tag K))) = twistedE6RootGroup K σ

theorem matrix_of_twE6NormalizesR {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (E : Subgroup (MulAut (twistedE6RootGroup K σ)))
    (hE : E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ) (h : TwE6NormalizesR K σ E) :
    ∃ R : Subgroup (ModGL TwistTag.E6.tag K), R ≤ twistedE6RootGroup K σ ∧ R ≠ ⊥ ∧
      IsPGroup (ringChar K) R ∧
      twPlanePre K σ E ≤ Subgroup.normalizer (R : Set (ModGL TwistTag.E6.tag K)) := by
  obtain ⟨R, hR1, hRp, hRn⟩ := h
  refine ⟨R.map (twistedE6RootGroup K σ).subtype, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨r, -, rfl⟩
    exact r.2
  · intro hbot
    apply hR1
    exact (Subgroup.map_eq_bot_iff_of_injective R (twistedE6RootGroup K σ).subtype_injective).1 hbot
  · exact hRp.map _
  · intro x hx
    obtain ⟨g, rfl, hgE⟩ := (mem_twPlanePre_iff K σ E x).1 hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨r, hr, rfl⟩
      have hr' : twistedE6InndiagConj K σ g r ∈ R.map (twistedE6InndiagConj K σ g).toMonoidHom :=
        ⟨r, hr, rfl⟩
      rw [hRn _ hgE] at hr'
      exact ⟨_, hr', by simp [twistedE6InndiagConj_apply]⟩
    · rintro ⟨r', hr', hy⟩
      have hr'' : r' ∈ R.map (twistedE6InndiagConj K σ g).toMonoidHom := by
        rw [hRn _ hgE]; exact hr'
      obtain ⟨r, hr, rfl⟩ := hr''
      refine ⟨r, hr, ?_⟩
      have h1 : (g : ModGL TwistTag.E6.tag K) * (r : ModGL TwistTag.E6.tag K) *
          (g : ModGL TwistTag.E6.tag K)⁻¹ =
          (g : ModGL TwistTag.E6.tag K) * y * (g : ModGL TwistTag.E6.tag K)⁻¹ := by
        rw [← twistedE6InndiagConj_apply]
        exact hy
      exact mul_left_cancel (mul_right_cancel h1)

theorem twE6InndiagParabolic'_of_generic (hG : TwE6InndiagCentralizerGeneration) :
    TwE6InndiagParabolic' := by
  intro K _ _ σ q hK3 hσ hK E hE hEab hcard hnin hnorm
  classical
  obtain ⟨hp, f, hf, rfl⟩ := ExcHighThree.exists_pow_ringChar_of_card_sq K q hK
    (by
      by_contra h
      have hq : q ≤ 1 := by omega
      have : Nat.card K ≤ 1 := by
        rw [hK]; nlinarith [Nat.zero_le q]
      have h2 : 2 ≤ Nat.card K := Finite.one_lt_card
      omega)
  have hinj := twistedE6InndiagConj_injective hp hf hK σ hσ
  obtain ⟨R, hRC, hR1, hRp, hRn⟩ := matrix_of_twE6NormalizesR σ E hE hnorm
  haveI : Fact (ringChar K).Prime := ⟨hp⟩
  haveI : CharP K (ringChar K) := ringChar.charP K
  have hAle : twPlanePre K σ E ≤ twistedE6InndiagGL K σ := by
    rintro _ hx
    obtain ⟨g, rfl, -⟩ := (mem_twPlanePre_iff K σ E _).1 hx
    exact g.2
  have hAcomm : ∀ a ∈ twPlanePre K σ E, ∀ b ∈ twPlanePre K σ E, a * b = b * a := by
    intro a ha b hb
    obtain ⟨g, rfl, hg⟩ := (mem_twPlanePre_iff K σ E a).1 ha
    obtain ⟨h, rfl, hh⟩ := (mem_twPlanePre_iff K σ E b).1 hb
    have : g * h = h * g := by
      apply hinj
      rw [map_mul, map_mul]
      exact congrArg Subtype.val (hEab.is_comm.comm ⟨_, hg⟩ ⟨_, hh⟩)
    exact congrArg Subtype.val this
  have hAEA : CFSG.IsElementaryAbelian 3 (twPlanePre K σ E) :=
    CFSG.IsElementaryAbelian.of_forall hAcomm fun a ha =>
      pow_three_eq_one_of_mem_twPlanePre _ f hp hf K hK σ hσ E ha
  have hAcard : Nat.card (twPlanePre K σ E) = 3 ^ 2 := by
    rw [card_twPlanePre _ f hp hf K hK σ hσ E hE]
    exact hcard
  have hgen := hG K σ (ringChar K ^ f) hK3 hσ hK (twPlanePre K σ E) hAle hAEA hAcard.ge R hRC hRp
    hR1 hRn
  have hsub : ∀ a ∈ twPlanePre K σ E, a ≠ 1 →
      twistedE6RootGroup K σ ⊓ Subgroup.centralizer ({a} : Set (ModGL TwistTag.E6.tag K)) ≤
      (Subgroup.closure (fixUnion E)).map (twistedE6RootGroup K σ).subtype := by
    intro a ha ha1 y hy
    obtain ⟨g, rfl, hgE⟩ := (mem_twPlanePre_iff K σ E a).1 ha
    have hyC : y ∈ twistedE6RootGroup K σ := hy.1
    have hcomm : (g : ModGL TwistTag.E6.tag K) * y = y * (g : ModGL TwistTag.E6.tag K) :=
      Subgroup.mem_centralizer_iff.1 hy.2 (g : ModGL TwistTag.E6.tag K) rfl
    refine ⟨⟨y, hyC⟩, Subgroup.subset_closure ?_, rfl⟩
    refine ⟨Subgroup.zpowers (twistedE6InndiagConj K σ g), ?_, ?_, ?_⟩
    · rw [Subgroup.zpowers_le]
      exact hgE
    · intro hbot
      have hmem : twistedE6InndiagConj K σ g ∈ (⊥ : Subgroup (MulAut ↥(twistedE6RootGroup K σ))) :=
        hbot ▸ Subgroup.mem_zpowers _
      have : g = 1 := hinj (by simpa using hmem)
      exact ha1 (by rw [this]; rfl)
    · intro φ hφ
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hφ
      rw [← map_zpow]
      apply Subtype.ext
      rw [twistedE6InndiagConj_apply]
      have hc : Commute (y : ModGL TwistTag.E6.tag K)
          ((g ^ n : ↥(twistedE6InndiagGL K σ)) : ModGL TwistTag.E6.tag K) := by
        have h1 : Commute (y : ModGL TwistTag.E6.tag K) (g : ModGL TwistTag.E6.tag K) := hcomm.symm
        simpa using h1.zpow_right n
      calc ((g ^ n : ↥(twistedE6InndiagGL K σ)) : ModGL TwistTag.E6.tag K) * y *
            ((g ^ n : ↥(twistedE6InndiagGL K σ)) : ModGL TwistTag.E6.tag K)⁻¹
          = y * ((g ^ n : ↥(twistedE6InndiagGL K σ)) : ModGL TwistTag.E6.tag K) *
              ((g ^ n : ↥(twistedE6InndiagGL K σ)) : ModGL TwistTag.E6.tag K)⁻¹ := by rw [hc.eq]
        _ = y := by group
  have hle : twistedE6RootGroup K σ ≤
      (Subgroup.closure (fixUnion E)).map (twistedE6RootGroup K σ).subtype := by
    exact le_trans (le_of_eq hgen.symm) (iSup₂_le fun a ha => iSup_le fun ha1 => hsub a ha ha1)
  rw [eq_top_iff]
  intro y _
  obtain ⟨t, ht, hty⟩ := hle y.2
  have : t = y := Subtype.ext hty
  rw [← this]
  exact ht

theorem e6ThreeDiagPlanes_of_leaves (hH : E6HeisenbergParabolic) (hR : E6RegularOuterFixedRoot)
    (hG : E6InndiagCentralizerGeneration) : E6ThreeDiagPlanes :=
  e6ThreeDiagPlanes_of_open (e6InndiagTorality_of_heisenberg hH)
    (e6DiagRegularOuter_of_fixedRoot hR) (e6InndiagParabolic_of_generic hG)

theorem twistedE6ThreeDiagPlanes_of_leaves (hH : TwE6HeisenbergParabolic)
    (hO : TwE6DiagRegularGen) (hKR : TwE6KillRoot) (hG : TwE6InndiagCentralizerGeneration) :
    TwistedE6ThreeDiagPlanes :=
  twistedE6ThreeDiagPlanes_of_open' (twE6InndiagTorality'_of_heisenberg hH) hO hKR
    (twE6InndiagParabolic'_of_generic hG)

end CFSG.LieType.SeitzGeneration.ExcWideThree

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.CTP CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Fischer CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross (E6DiagIsotropic TwistedE6DiagIsotropic)
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross


structure E6HeisenbergFrame (K : Type) [Field K] [Finite K]
    (E : Subgroup (MulAut (adjointGroup Tag.E6 K))) where
  w' : WeylGroup Tag.E6
  Fr : AlgebraicClosure K →+* AlgebraicClosure K
  hFr : ∀ c, Fr c = c ^ Nat.card K
  g0 : ModGL Tag.E6 (AlgebraicClosure K)
  hg0C : g0 ∈ adjointGroup Tag.E6 (AlgebraicClosure K)
  hg0 : Units.map (entrywiseHom Fr) g0 =
    g0 * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w'
  a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ
  b : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ
  w : WeylGroup Tag.E6
  ha3 : ∀ i, a i ^ 3 = 1
  hw : w ∈ rootCharStabilizer a
  hsh : rootChar a (e6Shift w) ≠ 1
  hT : rootDiagUnit Tag.E6 a ∈ twistedTorusOf
    (canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w') (Units.map (entrywiseHom Fr))
  u : ModGL Tag.E6 (AlgebraicClosure K)
  hu : u ∈ rootSpan Tag.E6 (AlgebraicClosure K) (rootCharKernel a)
  g₁ : ↥(e6InndiagGL K)
  g₂ : ↥(e6InndiagGL K)
  hg₁ : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (g₁ : ModGL Tag.E6 K) * g0 =
    rootDiagUnit Tag.E6 a
  hg₂ : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (g₂ : ModGL Tag.E6 K) * g0 =
    u⁻¹ * (rootDiagUnit Tag.E6 b *
      canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w) * u
  hE₁ : e6InndiagConj K g₁ ∈ E
  hE₂ : e6InndiagConj K g₂ ∈ E
  hgen : E = Subgroup.closure {e6InndiagConj K g₁, e6InndiagConj K g₂}

theorem exists_e6HeisenbergFrame {K : Type} [Field K] [Finite K] (hK3 : ringChar K ≠ 3)
    (hK4 : 4 ≤ Nat.card K) (K₁ : IntermediateField K (AlgebraicClosure K)) [Finite K₁]
    (hroot : ∀ c : Kˣ, ∃ u : K₁ˣ, u ^ 3 = Units.map (algebraMap K K₁).toMonoidHom c)
    (E : Subgroup (MulAut (adjointGroup Tag.E6 K))) (hE : CFSG.IsElementaryAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 2) (hd : E ≤ e6Inndiag K) (hnoniso : ¬ E6DiagIsotropic K K₁ E) :
    Nonempty (E6HeisenbergFrame K E) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have h3 : ¬ 3 ∣ Nat.card K := not_three_dvd_card_of_ringChar K hK3
  have hinj := e6InndiagConj_injective K hK4
  have hnoniso' : ∃ s t : ↥(e6Data_valid.minGroup K₁),
      (e6Isogeny K₁ s : ModGL Tag.E6 K₁) ∈
        ((E.comap (e6InndiagConj K)).map (e6InndiagGL K).subtype).map
          (baseChangeGL (algebraMap K K₁)) ∧
      (e6Isogeny K₁ t : ModGL Tag.E6 K₁) ∈
        ((E.comap (e6InndiagConj K)).map (e6InndiagGL K).subtype).map
          (baseChangeGL (algebraMap K K₁)) ∧ s * t ≠ t * s := by
    unfold E6DiagIsotropic at hnoniso
    push Not at hnoniso
    exact hnoniso
  obtain ⟨s, t, hs, ht, hst⟩ := hnoniso'
  obtain ⟨_, ⟨g₁, hg₁, rfl⟩, hs1⟩ := hs
  obtain ⟨_, ⟨g₂, hg₂, rfl⟩, ht1⟩ := ht
  have hg₁3 : g₁ ^ 3 = 1 := hinj (by
    rw [map_pow, map_one]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian (A := E) _ hg₁)
  have hg₂3 : g₂ ^ 3 = 1 := hinj (by
    rw [map_pow, map_one]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian (A := E) _ hg₂)
  have hcomm₀ : g₁ * g₂ = g₂ * g₁ := by
    refine hinj ?_
    have := congrArg Subtype.val
      (hE.is_comm.comm ⟨e6InndiagConj K g₁, hg₁⟩ ⟨e6InndiagConj K g₂, hg₂⟩)
    rw [map_mul, map_mul]
    exact this
  have hd₁3 : (g₁ : ModGL Tag.E6 K) ^ 3 = 1 := by
    simpa using congrArg Subtype.val hg₁3
  have hd₂3 : (g₂ : ModGL Tag.E6 K) ^ 3 = 1 := by
    simpa using congrArg Subtype.val hg₂3
  have hcomm : (g₁ : ModGL Tag.E6 K) * g₂ = g₂ * g₁ := by
    simpa using congrArg Subtype.val hcomm₀
  obtain ⟨c₂, hc₂, a, b, w, ha3, hw, hsh, hca, hcb⟩ :=
    E6Heis.pair_normal_form h3 K₁ (g₁ : ModGL Tag.E6 K) (g₂ : ModGL Tag.E6 K) g₁.2 g₂.2 hd₁3
      hd₂3 hcomm s t hs1.symm ht1.symm hst
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have : CharP K (ringChar K) := ringChar.charP K
  set ℓ := ringChar K with hℓdef
  have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  set L := AlgebraicClosure K with hL
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective _
  set ι₀ : K →+* L := algebraMap K L with hι₀
  set Fr : L →+* L := iterateFrobenius L ℓ (f : ℕ) with hFrdef
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hFrdef, iterateFrobenius_def, Nat.card_eq_fintype_card, hf]
  have hcomp : Fr.comp ι₀ = ι₀ := by
    refine RingHom.ext fun c => ?_
    change Fr (ι₀ c) = ι₀ c
    rw [hFr, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hFix : Units.map (entrywiseHom Fr) (baseChangeGL ι₀ (g₁ : ModGL Tag.E6 K)) =
      baseChangeGL ι₀ (g₁ : ModGL Tag.E6 K) := by
    rw [CFSG.LieType.Chevalley.units_map_entrywiseHom_eq_baseChangeGL,
      CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL, hcomp]
  have hpq : Nat.Coprime 3 (ℓ ^ (f : ℕ)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2
      (by rw [← hf, ← Nat.card_eq_fintype_card]; exact h3)
  have hga : (c₂⁻¹)⁻¹ * baseChangeGL ι₀ (g₁ : ModGL Tag.E6 K) * c₂⁻¹ = rootDiagUnit Tag.E6 a := by
    rw [inv_inv]
    exact hca
  obtain ⟨w', z, hz, hu, hga', hT⟩ := E6Heis.lang_step_single (L := L) (ℓ := ℓ) (f : ℕ) f.pos hpq
    (inv_mem hc₂) a ha3 hga hFix
  have hzC : z ∈ adjointGroup Tag.E6 L :=
    sup_le torusGroup_le_adjointGroup' (rootSpan_le_adjointGroup L _) hz
  have hg0C : c₂⁻¹ * z ∈ adjointGroup Tag.E6 L := mul_mem (inv_mem hc₂) hzC
  obtain ⟨u, b', hu', hconj⟩ := E6Heis.exists_rootSpan_conj_form a b w (m := z) hz
  have hg₂' : (c₂⁻¹ * z)⁻¹ * baseChangeGL ι₀ (g₂ : ModGL Tag.E6 K) * (c₂⁻¹ * z) =
      u⁻¹ * (rootDiagUnit Tag.E6 b' * canonicalRep (coxeterSystem Tag.E6) L w) * u := by
    rw [← hconj, ← hcb]
    group
  have hker : ∀ g g' : ↥(e6Data_valid.minGroup K₁),
      ((e6Isogeny K₁ g : adjointGroup Tag.E6 K₁) : ModGL Tag.E6 K₁) =
        ((e6Isogeny K₁ g' : adjointGroup Tag.E6 K₁) : ModGL Tag.E6 K₁) →
      g'⁻¹ * g ∈ Subgroup.center ↥(e6Data_valid.minGroup K₁) := by
    intro g g' hgg'
    rw [← CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center]
    rw [MonoidHom.mem_ker]
    change e6Isogeny K₁ (g'⁻¹ * g) = 1
    rw [map_mul, map_inv, inv_mul_eq_one]
    exact Subtype.ext hgg'.symm
  have hnot : ∀ k : ℤ, g₂ ≠ g₁ ^ k := by
    intro k hk
    apply hst
    have hπ : ((e6Isogeny K₁ t : adjointGroup Tag.E6 K₁) : ModGL Tag.E6 K₁) =
        ((e6Isogeny K₁ (s ^ k) : adjointGroup Tag.E6 K₁) : ModGL Tag.E6 K₁) := by
      rw [← ht1, hk, map_zpow (e6Isogeny K₁) s k, Subgroup.coe_zpow, ← hs1]
      simp [map_zpow]
    have hz1 := hker t (s ^ k) hπ
    have hsz : Commute s ((s ^ k)⁻¹ * t) := Subgroup.mem_center_iff.1 hz1 s
    have hsk : Commute s (s ^ k) := (Commute.refl s).zpow_right k
    have hct : Commute s t := by
      have := hsk.mul_right hsz
      rwa [mul_inv_cancel_left] at this
    exact hct.eq
  have he₁1 : e6InndiagConj K g₁ ≠ 1 := by
    intro h
    have hg1 : g₁ = 1 := hinj (h.trans (map_one _).symm)
    have hπ : ((e6Isogeny K₁ s : adjointGroup Tag.E6 K₁) : ModGL Tag.E6 K₁) =
        ((e6Isogeny K₁ (1 : ↥(e6Data_valid.minGroup K₁)) : adjointGroup Tag.E6 K₁) :
          ModGL Tag.E6 K₁) := by
      rw [← hs1, hg1]
      simp
    have hz1 := hker s 1 hπ
    have hs_c : s ∈ Subgroup.center ↥(e6Data_valid.minGroup K₁) := by simpa using hz1
    exact hst (Subgroup.mem_center_iff.1 hs_c t).symm
  have he₂n : e6InndiagConj K g₂ ∉ Subgroup.zpowers (e6InndiagConj K g₁) := by
    rintro ⟨k, hk⟩
    apply hnot k
    apply hinj
    rw [map_zpow]
    exact hk.symm
  have hgen : E = Subgroup.closure {e6InndiagConj K g₁, e6InndiagConj K g₂} := by
    have hle : Subgroup.closure {e6InndiagConj K g₁, e6InndiagConj K g₂} ≤ E := by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact hg₁
      · exact hg₂
    have hz₁ : Subgroup.zpowers (e6InndiagConj K g₁) ≤
        Subgroup.closure {e6InndiagConj K g₁, e6InndiagConj K g₂} := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.subset_closure (Set.mem_insert _ _)
    have he₂c : e6InndiagConj K g₂ ∈ Subgroup.closure {e6InndiagConj K g₁, e6InndiagConj K g₂} :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    have he₁o : orderOf (e6InndiagConj K g₁) = 3 := by
      refine orderOf_eq_prime ?_ he₁1
      rw [← map_pow, hg₁3, map_one]
    have hc1 : Nat.card (Subgroup.zpowers (e6InndiagConj K g₁)) = 3 := by
      rw [Nat.card_zpowers, he₁o]
    have hdvd1 : 3 ∣ Nat.card (Subgroup.closure {e6InndiagConj K g₁, e6InndiagConj K g₂}) := by
      rw [← hc1]
      exact Subgroup.card_dvd_of_le hz₁
    have hdvd2 : Nat.card (Subgroup.closure {e6InndiagConj K g₁, e6InndiagConj K g₂}) ∣ 3 ^ 2 := by
      rw [← hcard]
      exact Subgroup.card_dvd_of_le hle
    have hne : Subgroup.zpowers (e6InndiagConj K g₁) ≠
        Subgroup.closure {e6InndiagConj K g₁, e6InndiagConj K g₂} := fun h =>
      he₂n (h ▸ he₂c)
    have hne3 : Nat.card (Subgroup.closure {e6InndiagConj K g₁, e6InndiagConj K g₂}) ≠ 3 := by
      intro h3'
      apply hne
      exact Subgroup.eq_of_le_of_card_ge hz₁ (by rw [hc1, h3'])
    have h9 : Nat.card (Subgroup.closure {e6InndiagConj K g₁, e6InndiagConj K g₂}) = 3 ^ 2 := by
      have := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd2
      obtain ⟨m, hm, hm'⟩ := this
      interval_cases m
      · rw [hm', pow_zero] at hdvd1
        omega
      · exact absurd (by rw [hm']; norm_num) hne3
      · exact hm'
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h9, hcard])).symm
  exact ⟨⟨w', Fr, hFr, c₂⁻¹ * z, hg0C, hu, a, b', w, ha3, hw, hsh, hT, u, hu', g₁, g₂, hga', hg₂',
    hg₁, hg₂, hgen⟩⟩


structure TwE6HeisenbergFrame (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ)
    (E : Subgroup (MulAut (twistedE6RootGroup K σ))) where
  w' : WeylGroup TwistTag.E6.tag
  Fr : AlgebraicClosure K →+* AlgebraicClosure K
  hFr : ∀ c, Fr c = c ^ q
  g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)
  hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K)
  hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
    g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w'
  a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ
  b : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ
  w : WeylGroup Tag.E6
  ha3 : ∀ i, a i ^ 3 = 1
  hw : w ∈ rootCharStabilizer a
  hsh : rootChar a (e6Shift w) ≠ 1
  hT : rootDiagUnit TwistTag.E6.tag a ∈ twistedTorusOf
    (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w')
    (twistHom TwistTag.E6 (AlgebraicClosure K) Fr)
  u : ModGL Tag.E6 (AlgebraicClosure K)
  hu : u ∈ rootSpan Tag.E6 (AlgebraicClosure K) (rootCharKernel a)
  g₁ : ↥(twistedE6InndiagGL K σ)
  g₂ : ↥(twistedE6InndiagGL K σ)
  hg₁ : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (g₁ : ModGL TwistTag.E6.tag K) * g0 =
    rootDiagUnit TwistTag.E6.tag a
  hg₂ : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (g₂ : ModGL TwistTag.E6.tag K) * g0 =
    u⁻¹ * (rootDiagUnit Tag.E6 b *
      canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w) * u
  hE₁ : twistedE6InndiagConj K σ g₁ ∈ E
  hE₂ : twistedE6InndiagConj K σ g₂ ∈ E
  hgen : E = Subgroup.closure {twistedE6InndiagConj K σ g₁, twistedE6InndiagConj K σ g₂}

theorem exists_twE6HeisenbergFrame (ℓ f : ℕ) (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (K₁ : IntermediateField K (AlgebraicClosure K)) [Finite K₁]
    (hroot : ∀ c : Kˣ, ∃ u : K₁ˣ, u ^ 3 = Units.map (algebraMap K K₁).toMonoidHom c)
    (E : Subgroup (MulAut (twistedE6RootGroup K σ))) (hE : CFSG.IsElementaryAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 2) (hd : E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ)
    (hnoniso : ¬ TwistedE6DiagIsotropic K σ K₁ E) :
    Nonempty (TwE6HeisenbergFrame K σ (ℓ ^ f) E) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fintype K := Fintype.ofFinite K
  have h3 : ¬ 3 ∣ ℓ ^ f := fun h => hℓ3
    ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1 (Nat.prime_three.dvd_of_dvd_pow h)).symm
  have h3K : ¬ 3 ∣ Nat.card K := by
    rw [hK]
    intro h
    exact h3 (Nat.prime_three.dvd_of_dvd_pow h)
  have hinj := twistedE6InndiagConj_injective hℓ hf hK σ hσ
  have hnoniso' : ∃ s t : ↥(e6Data_valid.minGroup K₁),
      (e6Isogeny K₁ s : ModGL Tag.E6 K₁) ∈
        ((E.comap (twistedE6InndiagConj K σ)).map (twistedE6InndiagGL K σ).subtype).map
          (baseChangeGL (algebraMap K K₁)) ∧
      (e6Isogeny K₁ t : ModGL Tag.E6 K₁) ∈
        ((E.comap (twistedE6InndiagConj K σ)).map (twistedE6InndiagGL K σ).subtype).map
          (baseChangeGL (algebraMap K K₁)) ∧ s * t ≠ t * s := by
    unfold TwistedE6DiagIsotropic at hnoniso
    push Not at hnoniso
    exact hnoniso
  obtain ⟨s, t, hs, ht, hst⟩ := hnoniso'
  obtain ⟨_, ⟨g₁, hg₁, rfl⟩, hs1⟩ := hs
  obtain ⟨_, ⟨g₂, hg₂, rfl⟩, ht1⟩ := ht
  have hg₁3 : g₁ ^ 3 = 1 := hinj (by
    rw [map_pow, map_one]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian (A := E) _ hg₁)
  have hg₂3 : g₂ ^ 3 = 1 := hinj (by
    rw [map_pow, map_one]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian (A := E) _ hg₂)
  have hcomm₀ : g₁ * g₂ = g₂ * g₁ := by
    refine hinj ?_
    have := congrArg Subtype.val
      (hE.is_comm.comm ⟨twistedE6InndiagConj K σ g₁, hg₁⟩ ⟨twistedE6InndiagConj K σ g₂, hg₂⟩)
    rw [map_mul, map_mul]
    exact this
  have hd₁3 : (g₁ : ModGL TwistTag.E6.tag K) ^ 3 = 1 := by
    simpa using congrArg Subtype.val hg₁3
  have hd₂3 : (g₂ : ModGL TwistTag.E6.tag K) ^ 3 = 1 := by
    simpa using congrArg Subtype.val hg₂3
  have hcomm : (g₁ : ModGL TwistTag.E6.tag K) * g₂ = g₂ * g₁ := by
    simpa using congrArg Subtype.val hcomm₀
  obtain ⟨c₂, hc₂, a, b, w, ha3, hw, hsh, hca, hcb⟩ :=
    E6Heis.pair_normal_form_tw h3K K₁ (g₁ : ModGL TwistTag.E6.tag K)
      (g₂ : ModGL TwistTag.E6.tag K) (twistedE6InndiagGL_le_e6InndiagGL K σ g₁.2)
      (twistedE6InndiagGL_le_e6InndiagGL K σ g₂.2) hd₁3 hd₂3 hcomm s t hs1.symm ht1.symm hst
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  set L := AlgebraicClosure K with hL
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  set ι₀ : K →+* L := algebraMap K L with hι₀
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => by rw [hFrdef, iterateFrobenius_def]
  have hFix : twistHom TwistTag.E6 L Fr (baseChangeGL ι₀ (g₁ : ModGL TwistTag.E6.tag K)) =
      baseChangeGL ι₀ (g₁ : ModGL TwistTag.E6.tag K) :=
    ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 L Fr).1
      (map_twistedE6InndiagGL_le_twistedFixedGroup hℓ hf hK σ hσ Fr hFr
        (Subgroup.mem_map_of_mem _ g₁.2))).2
  have hga : (c₂⁻¹)⁻¹ * baseChangeGL ι₀ (g₁ : ModGL TwistTag.E6.tag K) * c₂⁻¹ =
      rootDiagUnit TwistTag.E6.tag a := by
    rw [inv_inv]
    exact hca
  obtain ⟨w', z, hz, hu, hga', hT⟩ :=
    E6Heis.lang_step_single_tw (L := L) (ℓ := ℓ) f hf (inv_mem hc₂) a ha3 hga hFix
  have hzC : z ∈ adjointGroup TwistTag.E6.tag L :=
    sup_le torusGroup_le_adjointGroup' (rootSpan_le_adjointGroup L _) hz
  have hg0C : c₂⁻¹ * z ∈ adjointGroup TwistTag.E6.tag L := mul_mem (inv_mem hc₂) hzC
  obtain ⟨u, b', hu', hconj⟩ := E6Heis.exists_rootSpan_conj_form a b w (m := z) hz
  have hg₂' : (c₂⁻¹ * z)⁻¹ * baseChangeGL ι₀ (g₂ : ModGL TwistTag.E6.tag K) * (c₂⁻¹ * z) =
      u⁻¹ * (rootDiagUnit Tag.E6 b' * canonicalRep (coxeterSystem Tag.E6) L w) * u := by
    have e1 : (c₂⁻¹ * z)⁻¹ * baseChangeGL ι₀ (g₂ : ModGL TwistTag.E6.tag K) * (c₂⁻¹ * z) =
        z⁻¹ * (c₂ * baseChangeGL ι₀ (g₂ : ModGL TwistTag.E6.tag K) * c₂⁻¹) * z := by group
    rw [e1, hcb]
    exact hconj
  have hker : ∀ g g' : ↥(e6Data_valid.minGroup K₁),
      ((e6Isogeny K₁ g : adjointGroup Tag.E6 K₁) : ModGL Tag.E6 K₁) =
        ((e6Isogeny K₁ g' : adjointGroup Tag.E6 K₁) : ModGL Tag.E6 K₁) →
      g'⁻¹ * g ∈ Subgroup.center ↥(e6Data_valid.minGroup K₁) := by
    intro g g' hgg'
    rw [← CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center]
    rw [MonoidHom.mem_ker]
    change e6Isogeny K₁ (g'⁻¹ * g) = 1
    rw [map_mul, map_inv, inv_mul_eq_one]
    exact Subtype.ext hgg'.symm
  have hnot : ∀ k : ℤ, g₂ ≠ g₁ ^ k := by
    intro k hk
    apply hst
    have hπ : ((e6Isogeny K₁ t : adjointGroup Tag.E6 K₁) : ModGL Tag.E6 K₁) =
        ((e6Isogeny K₁ (s ^ k) : adjointGroup Tag.E6 K₁) : ModGL Tag.E6 K₁) := by
      rw [← ht1, hk, map_zpow (e6Isogeny K₁) s k, Subgroup.coe_zpow, ← hs1]
      simp [map_zpow]
      <;> rfl
    have hz1 := hker t (s ^ k) hπ
    have hsz : Commute s ((s ^ k)⁻¹ * t) := Subgroup.mem_center_iff.1 hz1 s
    have hsk : Commute s (s ^ k) := (Commute.refl s).zpow_right k
    have hct : Commute s t := by
      have := hsk.mul_right hsz
      rwa [mul_inv_cancel_left] at this
    exact hct.eq
  have he₁1 : twistedE6InndiagConj K σ g₁ ≠ 1 := by
    intro h
    have hg1 : g₁ = 1 := hinj (h.trans (map_one _).symm)
    have hπ : ((e6Isogeny K₁ s : adjointGroup Tag.E6 K₁) : ModGL Tag.E6 K₁) =
        ((e6Isogeny K₁ (1 : ↥(e6Data_valid.minGroup K₁)) : adjointGroup Tag.E6 K₁) :
          ModGL Tag.E6 K₁) := by
      rw [← hs1, hg1]
      simp
      <;> rfl
    have hz1 := hker s 1 hπ
    have hs_c : s ∈ Subgroup.center ↥(e6Data_valid.minGroup K₁) := by simpa using hz1
    exact hst (Subgroup.mem_center_iff.1 hs_c t).symm
  have he₂n : twistedE6InndiagConj K σ g₂ ∉ Subgroup.zpowers (twistedE6InndiagConj K σ g₁) := by
    rintro ⟨k, hk⟩
    apply hnot k
    apply hinj
    rw [map_zpow]
    exact hk.symm
  have hgen : E = Subgroup.closure {twistedE6InndiagConj K σ g₁, twistedE6InndiagConj K σ g₂} := by
    have hle : Subgroup.closure {twistedE6InndiagConj K σ g₁, twistedE6InndiagConj K σ g₂} ≤ E := by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact hg₁
      · exact hg₂
    have hz₁ : Subgroup.zpowers (twistedE6InndiagConj K σ g₁) ≤
        Subgroup.closure {twistedE6InndiagConj K σ g₁, twistedE6InndiagConj K σ g₂} := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.subset_closure (Set.mem_insert _ _)
    have he₂c : twistedE6InndiagConj K σ g₂ ∈
        Subgroup.closure {twistedE6InndiagConj K σ g₁, twistedE6InndiagConj K σ g₂} :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    have he₁o : orderOf (twistedE6InndiagConj K σ g₁) = 3 := by
      refine orderOf_eq_prime ?_ he₁1
      rw [← map_pow, hg₁3, map_one]
    have hc1 : Nat.card (Subgroup.zpowers (twistedE6InndiagConj K σ g₁)) = 3 := by
      rw [Nat.card_zpowers, he₁o]
    have hdvd1 : 3 ∣ Nat.card (Subgroup.closure
        {twistedE6InndiagConj K σ g₁, twistedE6InndiagConj K σ g₂}) := by
      rw [← hc1]
      exact Subgroup.card_dvd_of_le hz₁
    have hdvd2 : Nat.card (Subgroup.closure
        {twistedE6InndiagConj K σ g₁, twistedE6InndiagConj K σ g₂}) ∣ 3 ^ 2 := by
      rw [← hcard]
      exact Subgroup.card_dvd_of_le hle
    have hne : Subgroup.zpowers (twistedE6InndiagConj K σ g₁) ≠
        Subgroup.closure {twistedE6InndiagConj K σ g₁, twistedE6InndiagConj K σ g₂} := fun h =>
      he₂n (h ▸ he₂c)
    have hne3 : Nat.card (Subgroup.closure
        {twistedE6InndiagConj K σ g₁, twistedE6InndiagConj K σ g₂}) ≠ 3 := by
      intro h3'
      apply hne
      exact Subgroup.eq_of_le_of_card_ge hz₁ (by rw [hc1, h3'])
    have h9 : Nat.card (Subgroup.closure
        {twistedE6InndiagConj K σ g₁, twistedE6InndiagConj K σ g₂}) = 3 ^ 2 := by
      have := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd2
      obtain ⟨m, hm, hm'⟩ := this
      interval_cases m
      · rw [hm', pow_zero] at hdvd1
        omega
      · exact absurd (by rw [hm']; norm_num) hne3
      · exact hm'
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h9, hcard])).symm
  exact ⟨⟨w', Fr, hFr, c₂⁻¹ * z, hg0C, hu, a, b', w, ha3, hw, hsh, hT, u, hu', g₁, g₂, hga', hg₂',
    hg₁, hg₂, hgen⟩⟩


end CFSG.LieType.SeitzGeneration.ExcWideThree

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.CTP CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Fischer CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.SeitzGeneration.ExcHighThree CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.Torality
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross (E6DiagIsotropic TwistedE6DiagIsotropic)


theorem rootChar_eq_one_iff_dvd {L : Type} [Field L] {ω : Lˣ} (hω : IsPrimitiveRoot ω 3)
    {a : Fin Tag.E6.rank → Lˣ} {k : Fin Tag.E6.rank → ℕ} (hak : ∀ i, a i = ω ^ k i)
    (v : Fin Tag.E6.rank → ℤ) :
    rootChar a v = 1 ↔ (3 : ℤ) ∣ ∑ i, v i * (k i : ℤ) := by
  have h1 : rootChar a v = ω ^ (∑ i, v i * (k i : ℤ)) := by
    rw [rootChar, ← prod_zpow_eq_zpow_sum_of_group]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hak i, ← zpow_natCast, ← zpow_mul, mul_comm]
  rw [h1]
  have := hω.zpow_eq_one_iff_dvd (∑ i, v i * (k i : ℤ))
  simpa using this

theorem rootChar_eq_one_iff_triPairing {L : Type} [Field L] {ω : Lˣ} (hω : IsPrimitiveRoot ω 3)
    {a : Fin Tag.E6.rank → Lˣ} {k : Fin Tag.E6.rank → ℕ} (hak : ∀ i, a i = ω ^ k i)
    (v : Fin Tag.E6.rank → ℤ) :
    rootChar a v = 1 ↔ triPairing (fun i => ((k i : ℕ) : ZMod 3)) v = 0 := by
  rw [rootChar_eq_one_iff_dvd hω hak v]
  have : triPairing (fun i => ((k i : ℕ) : ZMod 3)) v = ((∑ i, v i * (k i : ℤ) : ℤ) : ZMod 3) := by
    simp only [triPairing]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [this]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).symm

theorem langGL_rootChar_frob {K : Type} [Field K] [Finite K] {A : Subgroup (ModGL Tag.E6 K)}
    (D : LangGLData Tag.E6 K A) {x : ModGL Tag.E6 K}
    {a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ}
    (ha : rootDiagUnit Tag.E6 a = D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (D.c * x * D.c⁻¹ : ModGL Tag.E6 K) * D.g0)
    (v : Fin Tag.E6.rank → ℤ) :
    rootChar a (D.w • v) = rootChar a v ^ Nat.card K := by
  classical
  obtain ⟨e, he, hcard⟩ := card_eq_pow_ringChar K
  haveI : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  have hFrEq : D.Fr = iterateFrobenius (AlgebraicClosure K) (ringChar K) e :=
    RingHom.ext fun c => by rw [D.hFr c, iterateFrobenius_def, hcard]
  have hFrob : ∀ g : ModGL Tag.E6 (AlgebraicClosure K),
      Units.map (entrywiseHom D.Fr) g =
        entrywiseFrobGL Tag.E6 (AlgebraicClosure K) (ringChar K) e g := by
    intro g
    rw [hFrEq]
  have hg0F : entrywiseFrobGL Tag.E6 (AlgebraicClosure K) (ringChar K) e D.g0 =
      D.g0 * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) D.w := by
    rw [← hFrob]
    exact D.hg0
  have hBF : ∀ z : ModGL Tag.E6 K, entrywiseFrobGL Tag.E6 (AlgebraicClosure K) (ringChar K) e
      (baseChangeGL (algebraMap K (AlgebraicClosure K)) z) =
      baseChangeGL (algebraMap K (AlgebraicClosure K)) z := by
    intro z
    rw [← hFrob]
    exact CFSG.RankThree.PartOne.KE.baseChangeGL_frobenius_fixed D.Fr D.hFr z
  have hF : entrywiseFrobGL Tag.E6 (AlgebraicClosure K) (ringChar K) e (rootDiagUnit Tag.E6 a) =
      (canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) D.w)⁻¹ * rootDiagUnit Tag.E6 a *
        canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) D.w := by
    rw [ha, map_mul, map_mul, map_inv, hg0F, hBF]
    group
  have hconj : rootDiagUnit Tag.E6 a =
      canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) D.w *
        entrywiseFrobGL Tag.E6 (AlgebraicClosure K) (ringChar K) e (rootDiagUnit Tag.E6 a) *
        (canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) D.w)⁻¹ := by
    rw [hF]
    group
  rw [rootChar_frob_of_conj a D.w hconj v, ← hcard]

theorem langGL_mem_rootCharStabilizer {K : Type} [Field K] [Finite K] {A : Subgroup (ModGL Tag.E6 K)}
    (D : LangGLData Tag.E6 K A) {x : ModGL Tag.E6 K}
    {a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ}
    (ha : rootDiagUnit Tag.E6 a = D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (D.c * x * D.c⁻¹ : ModGL Tag.E6 K) * D.g0)
    (ha3 : ∀ i, a i ^ 3 = 1) (h3 : 3 ∣ Nat.card K - 1) : D.w ∈ rootCharStabilizer a := by
  intro v
  rw [langGL_rootChar_frob D ha v]
  have hK1 : 1 ≤ Nat.card K := Nat.card_pos
  obtain ⟨m, hm⟩ := h3
  have hq : Nat.card K = 1 + 3 * m := by omega
  have hcube : (rootChar a v) ^ 3 = 1 := by
    simp only [rootChar, ← prod_zpow_eq_zpow_sum_of_group]
    rw [← Finset.prod_pow]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    simp [← zpow_natCast, ha3 i]
  rw [hq, pow_add, pow_mul, hcube, one_pow, pow_one, mul_one]

theorem four_le_card_of_outer_matrix (K : Type) [Field K] [Finite K] (hK3 : ringChar K ≠ 3)
    {x : ModGL Tag.E6 K} (E : Subgroup (MulAut (adjointGroup Tag.E6 K)))
    (hx : x ∈ e6PlanePre K E) (hxn : x ∉ adjointGroup Tag.E6 K) : 4 ≤ Nat.card K := by
  classical
  by_contra h
  push Not at h
  have h2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hK2 : Nat.card K = 2 := by
    by_contra h2'
    have h3 : Nat.card K = 3 := by omega
    obtain ⟨e, he, hcard⟩ := card_eq_pow_ringChar K
    have hp : (ringChar K).Prime := CharP.char_is_prime K (ringChar K)
    have : ringChar K ∣ 3 := by
      rw [← h3, hcard]
      exact dvd_pow_self _ (by omega)
    exact hK3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 this)
  have hu : Subsingleton Kˣ := by
    have : Fintype K := Fintype.ofFinite K
    have hc : Fintype.card Kˣ = 1 := by
      rw [Fintype.card_units, ← Nat.card_eq_fintype_card, hK2]
    exact Fintype.card_le_one_iff_subsingleton.1 (by omega)
  obtain ⟨g, rfl, -⟩ := (mem_e6PlanePre_iff K E x).1 hx
  apply hxn
  have hle : e6InndiagGL K ≤ adjointGroup Tag.E6 K := by
    refine sup_le le_rfl ?_
    rintro _ ⟨a, rfl⟩
    have : a = 1 := Subsingleton.elim _ _
    rw [this, map_one]
    exact one_mem _
  exact hle g.2

theorem three_dvd_card_sub_one_of_outer_matrix (K : Type) [Field K] [Finite K]
    (hK4 : 4 ≤ Nat.card K) (E : Subgroup (MulAut (adjointGroup Tag.E6 K))) (hE : E ≤ e6Inndiag K)
    {x : ModGL Tag.E6 K} (hx : x ∈ e6PlanePre K E) (hxn : x ∉ adjointGroup Tag.E6 K) :
    3 ∣ Nat.card K - 1 := by
  by_contra h
  have hdiag : e6Inndiag K = innerAut (adjointGroup Tag.E6 K) :=
    e6Inndiag_eq_innerAut_of_not_dvd K h
  obtain ⟨g, rfl, hgE⟩ := (mem_e6PlanePre_iff K E x).1 hx
  have hmem : e6InndiagConj K g ∈ innerAut (adjointGroup Tag.E6 K) := hdiag ▸ hE hgE
  obtain ⟨h', hh'⟩ := hmem
  have hinj := e6InndiagConj_injective K hK4
  have hg : g = ⟨(h' : ModGL Tag.E6 K), adjointGroup_le_e6InndiagGL K h'.2⟩ := by
    apply hinj
    ext y
    rw [← hh']
    simp [e6InndiagConj_apply, MulAut.conj_apply]
  apply hxn
  rw [hg]
  exact h'.2

theorem langGL_kills_of_generators {K : Type} [Field K] [Finite K] {A : Subgroup (ModGL Tag.E6 K)}
    (D : LangGLData Tag.E6 K A) {x₁ x₂ : ModGL Tag.E6 K}
    (hgen : Subgroup.closure ({x₁, x₂} : Set (ModGL Tag.E6 K)) = A)
    {a₁ a₂ : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ}
    (ha₁ : rootDiagUnit Tag.E6 a₁ = D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (D.c * x₁ * D.c⁻¹ : ModGL Tag.E6 K) * D.g0)
    (ha₂ : rootDiagUnit Tag.E6 a₂ = D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (D.c * x₂ * D.c⁻¹ : ModGL Tag.E6 K) * D.g0)
    {α : Fin Tag.E6.rank → ℤ} (hr₁ : rootChar a₁ α = 1) (hr₂ : rootChar a₂ α = 1) :
    D.Kills α := by
  set Sg : Subgroup (ModGL Tag.E6 K) :=
    ((rootCharHom (τ := Tag.E6) (L := AlgebraicClosure K) α).ker.map
      (rootDiagUnitHom Tag.E6 (AlgebraicClosure K))).comap (diagMapGL D) with hSg
  have hker : ∀ a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ, rootChar a α = 1 →
      a ∈ (rootCharHom (τ := Tag.E6) (L := AlgebraicClosure K) α).ker :=
    fun a h => MonoidHom.mem_ker.2
      (show rootCharHom (τ := Tag.E6) (L := AlgebraicClosure K) α a = 1 from h)
  have hmem : ∀ (x : ModGL Tag.E6 K) (a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ),
      rootDiagUnit Tag.E6 a = D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (D.c * x * D.c⁻¹ : ModGL Tag.E6 K) * D.g0 → rootChar a α = 1 → x ∈ Sg := by
    intro x a hax hr
    refine Subgroup.mem_comap.2 (Subgroup.mem_map.2 ⟨a, hker a hr, ?_⟩)
    rw [diagMapGL_apply]
    exact hax
  have hx₁S : x₁ ∈ Sg := hmem x₁ a₁ ha₁ hr₁
  have hx₂S : x₂ ∈ Sg := hmem x₂ a₂ ha₂ hr₂
  have hAS : A ≤ Sg := by
    rw [← hgen]
    refine (Subgroup.closure_le Sg).2 ?_
    intro z hz
    rcases hz with rfl | rfl
    · exact hx₁S
    · exact hx₂S
  intro y hy
  obtain ⟨a, ha, hay⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 (hAS hy))
  refine ⟨a, ?_, ?_⟩
  · rw [diagMapGL_apply] at hay
    exact hay
  · exact (show rootCharHom (τ := Tag.E6) (L := AlgebraicClosure K) α a = 1 from
      MonoidHom.mem_ker.1 ha)

@[expose] def E6RegularFixedRootCheck : Prop :=
  ∀ (b₁ b₂ : Fin Tag.E6.rank → ZMod 3),
    (∀ α : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 α → ¬ (triPairing b₁ α = 0 ∧ triPairing b₂ α = 0)) →
    ∀ w : WeylGroup Tag.E6, w ∈ charStabilizer (triChar b₁) → w ∈ charStabilizer (triChar b₂) →
      triPairing b₁ (e6Shift w) ≠ 0 → ∃ β : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 β ∧ w • β = β

@[expose] def E6LiftBridge : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 3 → 3 ∣ Nat.card K - 1 →
    ∀ (Fr : AlgebraicClosure K →+* AlgebraicClosure K), (∀ c, Fr c = c ^ Nat.card K) →
    ∀ (w : WeylGroup Tag.E6) (g0 : ModGL Tag.E6 (AlgebraicClosure K)),
      g0 ∈ adjointGroup Tag.E6 (AlgebraicClosure K) →
      Units.map (entrywiseHom Fr) g0 =
        g0 * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w →
      ∀ (a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ), (∀ i, a i ^ 3 = 1) →
        ∏ i, a i ^ e6DiagCoeff i = 1 → w ∈ rootCharStabilizer a → rootChar a (e6Shift w) = 1 →
        ∀ y : ModGL Tag.E6 K,
          baseChangeGL (algebraMap K (AlgebraicClosure K)) y = g0 * rootDiagUnit Tag.E6 a * g0⁻¹ →
            y ∈ adjointGroup Tag.E6 K

theorem e6RegularOuterFixedRoot_of_F2_B (hF2 : E6RegularFixedRootCheck) (hB : E6LiftBridge) :
    E6RegularOuterFixedRoot := by
  intro K _ _ hK3 E hE hEab hcard D hreg hout
  classical
  obtain ⟨x₁, hx₁, hx₁n⟩ := hout
  have hK4 := four_le_card_of_outer_matrix K hK3 E hx₁ hx₁n
  have h3q := three_dvd_card_sub_one_of_outer_matrix K hK4 E hE hx₁ hx₁n
  have hexp : ∀ x ∈ e6PlanePre K E, x ^ 3 = 1 := fun x hx =>
    pow_three_eq_one_of_mem_e6PlanePre K hK4 E hx
  have hAcard : Nat.card (e6PlanePre K E) = 3 ^ 2 := by
    rw [card_e6PlanePre K hK4 E hE]
    exact hcard
  have hx₁1 : x₁ ≠ 1 := fun h => hx₁n (h ▸ one_mem _)
  obtain ⟨x₂, hx₂, hx₂n⟩ :=
    exists_mem_not_mem_zpowers (e6PlanePre K E) hAcard hx₁ (hexp x₁ hx₁) hx₁1
  have hgen : Subgroup.closure ({x₁, x₂} : Set (ModGL Tag.E6 K)) = e6PlanePre K E :=
    closure_pair_eq_of_not_mem (e6PlanePre K E) hAcard hx₁ hx₂ (hexp x₁ hx₁) hx₁1 hx₂n
  obtain ⟨ω, hω⟩ := exists_primCubeRoot K hK3
  have hω' : IsPrimitiveRoot ω 3 := IsPrimitiveRoot.coe_units_iff.1 hω
  have hω3 : ω ^ 3 = 1 := hω'.pow_eq_one
  obtain ⟨a₁, ha₁, k₁, hk₁⟩ := langGL_diag_exponent D ω hω hx₁ (hexp x₁ hx₁)
  obtain ⟨a₂, ha₂, k₂, hk₂⟩ := langGL_diag_exponent D ω hω hx₂ (hexp x₂ hx₂)
  have hcube : ∀ {k : Fin Tag.E6.rank → ℕ} {a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ},
      (∀ i, a i = ω ^ k i) → ∀ i, a i ^ 3 = 1 := fun {k a} hk i => by
    rw [hk i, ← pow_mul, mul_comm, pow_mul, hω3, one_pow]
  have ha₁3 := hcube hk₁
  have ha₂3 := hcube hk₂
  have hreg' : ∀ α : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 α →
      ¬ (triPairing (fun i => ((k₁ i : ℕ) : ZMod 3)) α = 0 ∧
        triPairing (fun i => ((k₂ i : ℕ) : ZMod 3)) α = 0) := by
    rintro α hα ⟨h1, h2⟩
    exact hreg ⟨α, hα, langGL_kills_of_generators D hgen ha₁ ha₂
      ((rootChar_eq_one_iff_triPairing hω' hk₁ α).2 h1)
      ((rootChar_eq_one_iff_triPairing hω' hk₂ α).2 h2)⟩
  have hstab : ∀ {k : Fin Tag.E6.rank → ℕ} {a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ}
      {x : ModGL Tag.E6 K}, (∀ i, a i = ω ^ k i) →
      rootDiagUnit Tag.E6 a = D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (D.c * x * D.c⁻¹ : ModGL Tag.E6 K) * D.g0 →
      D.w ∈ charStabilizer (triChar (fun i => ((k i : ℕ) : ZMod 3))) := by
    intro k a x hk ha v
    have hw := langGL_mem_rootCharStabilizer D ha (hcube hk) h3q v
    have h1 : rootChar a (D.w • v - v) = 1 := by
      rw [rootChar_sub, hw, mul_inv_cancel]
    have h2 := (rootChar_eq_one_iff_triPairing hω' hk (D.w • v - v)).1 h1
    rw [triChar_apply, triChar_apply]
    congr 1
    have h3 : triPairing (fun i => ((k i : ℕ) : ZMod 3)) (D.w • v) =
        triPairing (fun i => ((k i : ℕ) : ZMod 3)) (D.w • v - v) +
          triPairing (fun i => ((k i : ℕ) : ZMod 3)) v := by
      rw [← triPairing_add, sub_add_cancel]
    rw [h3, h2, zero_add]
  have hw₁ := hstab hk₁ ha₁
  have hw₂ := hstab hk₂ ha₂
  have hsh : triPairing (fun i => ((k₁ i : ℕ) : ZMod 3)) (e6Shift D.w) ≠ 0 := by
    intro hzero
    have hsh1 : rootChar a₁ (e6Shift D.w) = 1 :=
      (rootChar_eq_one_iff_triPairing hω' hk₁ _).2 hzero
    have hdiv : (3 : ℤ) ∣ ∑ i, e6DiagCoeff i * (k₁ i : ℤ) := by
      by_contra hout'
      exact hreg (langGL_kills_of_outer hexp hAcard D ω hω hx₁ hx₁1 a₁ ha₁ k₁ hk₁ hout')
    have hc : ∏ i, a₁ i ^ e6DiagCoeff i = 1 := rootChar_eq_one_of_dvd hω3 hk₁ hdiv
    have hy : baseChangeGL (algebraMap K (AlgebraicClosure K)) (D.c * x₁ * D.c⁻¹) =
        D.g0 * rootDiagUnit Tag.E6 a₁ * D.g0⁻¹ := by
      rw [ha₁]
      group
    have hmemC := hB K hK3 h3q D.Fr D.hFr D.w D.g0 D.hg0C D.hg0 a₁ ha₁3 hc
      (langGL_mem_rootCharStabilizer D ha₁ ha₁3 h3q) hsh1 _ hy
    exact hx₁n ((Subgroup.mem_normalizer_iff.1 D.hcN x₁).2 hmemC)
  exact hF2 _ _ hreg' D.w hw₁ hw₂ hsh

end CFSG.LieType.SeitzGeneration.ExcWideThree
