module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagLift
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeTorality

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE CFSG.LieType.SeitzGeneration
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny

theorem card_inf_innerAut_of_le_e6Inndiag
    (K : Type) [Field K] [Finite K] {D : Subgroup (MulAut (adjointGroup Tag.E6 K))}
    (hcard : Nat.card D = 3 ^ 3) (hDd : D ≤ e6Inndiag K)
    (hDin : ¬ D ≤ innerAut (adjointGroup Tag.E6 K)) :
    Nat.card ↥(D ⊓ innerAut (adjointGroup Tag.E6 K)) = 3 ^ 2 := by
  classical
  obtain ⟨Φ, -, hker, hdvd⟩ := exists_outer_hom_E (K := K) (τ := Tag.E6) (Or.inl rfl)
  set N := CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup Tag.E6 K)
    with hN
  set π := QuotientGroup.mk' N with hπ
  set φ : ↥D →* _ := π.comp D.subtype with hφ
  have hrange : φ.range ≤ Φ.ker := by
    rintro _ ⟨⟨d, hd⟩, rfl⟩
    have hdd : d ∈ ((N ⊔ (rootDiagAutHom Tag.E6 K).range : Subgroup _) : Set _) := hDd hd
    rw [Subgroup.normal_mul] at hdd
    obtain ⟨i, hi, r, ⟨a, rfl⟩, rfl⟩ := hdd
    rw [hker]
    refine ⟨a, ?_⟩
    change π (rootDiagAutHom Tag.E6 K a) = π (i * rootDiagAutHom Tag.E6 K a)
    have hpi : π i = 1 := (QuotientGroup.eq_one_iff i).2 hi
    rw [map_mul, hpi, one_mul]
  have h3 : Nat.card φ.range ∣ 3 := by
    refine (Subgroup.card_dvd_of_le hrange).trans ?_
    have h := hdvd
    rwa [show Tag.E6.cartan.det.natAbs = 3 by rw [det_cartan_E6]; rfl] at h
  have hkerφ : φ.ker = N.subgroupOf D := by
    rw [hφ, ← MonoidHom.comap_ker, hπ, QuotientGroup.ker_mk']
    rfl
  have hcardker : Nat.card φ.ker = Nat.card ↥(D ⊓ innerAut (adjointGroup Tag.E6 K)) := by
    rw [hkerφ, ← Subgroup.card_map_of_injective D.subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_comm]
    rfl
  have hmul : Nat.card φ.ker * Nat.card φ.range = 3 ^ 3 := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index, hcard]
  rw [hcardker] at hmul
  rcases (Nat.dvd_prime Nat.prime_three).1 h3 with h1 | h1
  · rw [h1, mul_one] at hmul
    have : Finite D := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
    have heq : D ⊓ innerAut (adjointGroup Tag.E6 K) = D :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hmul, hcard])
    exact absurd (inf_eq_left.1 heq) hDin
  · rw [h1] at hmul
    omega

section Residuals

@[expose] def LangTorusPlaneBalanceInndiag (w : WeylGroup Tag.E6) (p : ℕ) (Q : ℕ → Prop) : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Q (Nat.card K) →
    ∀ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ Nat.card K) →
    ∀ g0 ∈ adjointGroup Tag.E6 (AlgebraicClosure K),
      Units.map (entrywiseHom Fr) g0 =
        g0 * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w →
    ∀ D₀ : Subgroup ↥(e6InndiagGL K), (∀ x ∈ D₀, x ^ p = 1) → p < Nat.card D₀ →
      (∀ x ∈ D₀, baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL Tag.E6 K) ∈
        (twistedTorusOf (canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w)
          (Units.map (entrywiseHom Fr))).map (MulAut.conj g0).toMonoidHom) →
    ∀ H : Subgroup (MulAut (adjointGroup Tag.E6 K)), innerAut (adjointGroup Tag.E6 K) ≤ H →
      localDeltaIn p H (D₀.map (e6InndiagConj K)) = ⊥

end Residuals

section Torality

theorem e6IsotropicToralInndiag_of_planeToralLang (h : E6PlaneToralLang) :
    ∀ (K : Type) [Field K] [Finite K], ¬ 3 ∣ Nat.card K →
      ∀ (K₁ : IntermediateField K (AlgebraicClosure K)) [Finite K₁],
      ∀ E₀ : Subgroup ↥(e6InndiagGL K), (∀ x ∈ E₀, x ^ 3 = 1) → Nat.card E₀ = 3 ^ 2 →
        (∀ x ∈ E₀, baseChangeGL (algebraMap K K₁) (x : ModGL Tag.E6 K) ∈ adjointGroup Tag.E6 K₁) →
        (∀ x y : ↥(e6Data_valid.minGroup K₁),
          (e6Isogeny K₁ x : ModGL Tag.E6 K₁) ∈
            (E₀.map (e6InndiagGL K).subtype).map (baseChangeGL (algebraMap K K₁)) →
          (e6Isogeny K₁ y : ModGL Tag.E6 K₁) ∈
            (E₀.map (e6InndiagGL K).subtype).map (baseChangeGL (algebraMap K K₁)) →
          x * y = y * x) →
        ∃ w : WeylGroup Tag.E6, ∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K,
          (∀ c, Fr c = c ^ Nat.card K) ∧
          ∃ g0 ∈ adjointGroup Tag.E6 (AlgebraicClosure K),
            Units.map (entrywiseHom Fr) g0 =
              g0 * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w ∧
            ∀ x ∈ E₀, baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL Tag.E6 K) ∈
              (twistedTorusOf (canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w)
                (Units.map (entrywiseHom Fr))).map (MulAut.conj g0).toMonoidHom := by
  intro K _ _ h3 K₁ _ E₀ hexp hcard hC₁ hab
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have : CharP K (ringChar K) := ringChar.charP K
  set ℓ := ringChar K with hℓdef
  have : CharP (AlgebraicClosure K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective _
  set ι₀ : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K) with hι₀
  set ι₁ : K →+* K₁ := algebraMap K K₁ with hι₁
  set ι : K₁ →+* AlgebraicClosure K := K₁.val.toRingHom with hι
  have hcomp₁ : ι.comp ι₁ = ι₀ := RingHom.ext fun _ => rfl
  set Fr : AlgebraicClosure K →+* AlgebraicClosure K := iterateFrobenius _ ℓ (f : ℕ) with hFrdef
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hFrdef, iterateFrobenius_def, Nat.card_eq_fintype_card, hf]
  have hcomp : Fr.comp ι₀ = ι₀ := by
    refine RingHom.ext fun c => ?_
    change Fr (ι₀ c) = ι₀ c
    rw [hFr, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  set P := (E₀.map (e6InndiagGL K).subtype).map (baseChangeGL ι₁) with hP
  set S : Subgroup ↥(e6Data_valid.minGroup K₁) :=
    P.comap ((adjointGroup Tag.E6 K₁).subtype.comp (e6Isogeny K₁)) with hS
  have hSab : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := fun x hx y hy => hab x y hx hy
  set φ : ↥(e6InndiagGL K) →* ModGL Tag.E6 (AlgebraicClosure K) :=
    (baseChangeGL ι₀).comp (e6InndiagGL K).subtype with hφ
  have hφinj : Function.Injective φ := (baseChangeGL_injective ι₀).comp Subtype.val_injective
  have hAS : E₀.map φ ≤ S.map (e6ScToBar K₁ ι) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy⟩ := e6Isogeny_surjective K₁ ⟨_, hC₁ x hx⟩
    have hyv : ((e6Isogeny K₁ y : adjointGroup Tag.E6 K₁) : ModGL Tag.E6 K₁) =
        baseChangeGL ι₁ (x : ModGL Tag.E6 K) := congrArg Subtype.val hy
    refine ⟨y, ?_, ?_⟩
    · change ((e6Isogeny K₁ y : adjointGroup Tag.E6 K₁) : ModGL Tag.E6 K₁) ∈ P
      rw [hyv]
      exact ⟨x, ⟨x, hx, rfl⟩, rfl⟩
    · change baseChangeGL ι ((e6Isogeny K₁ y : adjointGroup Tag.E6 K₁) : ModGL Tag.E6 K₁) =
        baseChangeGL ι₀ (x : ModGL Tag.E6 K)
      rw [hyv, CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL, hcomp₁]
  have hexpA : ∀ x ∈ E₀.map φ, x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hexp x hx, map_one]
  have hcardA : Nat.card (E₀.map φ) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective hφinj, hcard]
  have hFix : ∀ x ∈ E₀.map φ, Units.map (entrywiseHom Fr) x = x := by
    rintro _ ⟨x, -, rfl⟩
    change Units.map (entrywiseHom Fr) (baseChangeGL ι₀ (x : ModGL Tag.E6 K)) =
      baseChangeGL ι₀ (x : ModGL Tag.E6 K)
    rw [CFSG.LieType.Chevalley.units_map_entrywiseHom_eq_baseChangeGL,
      CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL, hcomp]
  obtain ⟨w, g0, hg0C, hg0, hin⟩ := h K h3 K₁ ι S hSab (E₀.map φ) hAS hexpA hcardA Fr hFr hFix
  exact ⟨w, Fr, hFr, g0, hg0C, hg0, fun x hx => hin _ ⟨x, hx, rfl⟩⟩

end Torality

section Diagonal

theorem e6ThreeDiagonalNonsplitLarge_of_inndiag (htor : E6PlaneToralLang)
    (hT1 : ∀ w : WeylGroup Tag.E6,
      LangTorusPlaneBalanceInndiag w 3 fun q => ¬ 3 ∣ q ∧ 3 ∣ q - 1 ∧ q ≠ 4) :
    E6ThreeDiagonalNonsplitLarge := by
  have htorI := e6IsotropicToralInndiag_of_planeToralLang htor
  intro ℓ f hℓ hℓ3 hf hq1 hq4 K _ _ hK D hD hcard hDd _ _ H hH _
  have h3 : ¬ 3 ∣ Nat.card K := by
    rw [hK]
    intro h
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
  have hK4 : 4 ≤ Nat.card K := by
    have h2 : 2 ≤ ℓ ^ f := le_trans hℓ.two_le (Nat.le_self_pow (by omega) ℓ)
    have h3' : 3 ≤ ℓ ^ f - 1 := Nat.le_of_dvd (by omega) hq1
    omega
  obtain ⟨K₁, hK₁, hroot⟩ := exists_cubeExt K
  obtain ⟨E, hED, hE9, hEab⟩ :=
    exists_isotropic_plane_e6Inndiag K hK4 (algebraMap K K₁) hroot hDd hD hcard
  have hinj := e6InndiagConj_injective K hK4
  have hEr : E ≤ (e6InndiagConj K).range := by
    rw [range_e6InndiagConj]
    exact hED.trans hDd
  have hmap : (E.comap (e6InndiagConj K)).map (e6InndiagConj K) = E :=
    Subgroup.map_comap_eq_self hEr
  have hpow : ∀ x ∈ E.comap (e6InndiagConj K), x ^ 3 = 1 := fun x hx =>
    hinj (by rw [map_pow, map_one]; exact hD.2 _ (hED hx))
  have hcard₀ : 3 < Nat.card (E.comap (e6InndiagConj K)) := by
    rw [← Subgroup.card_map_of_injective hinj, hmap]
    omega
  obtain ⟨E₁, hE₁, hE₁c⟩ := exists_plane_le hpow hcard₀
  have hpow₁ : ∀ x ∈ E₁, x ^ 3 = 1 := fun x hx => hpow x (hE₁ hx)
  have hC₁ : ∀ x ∈ E₁, baseChangeGL (algebraMap K K₁) (x : ModGL Tag.E6 K) ∈
      adjointGroup Tag.E6 K₁ := fun x _ =>
    map_e6InndiagGL_le _ hroot (Subgroup.mem_map_of_mem _ x.2)
  have hmono : (E₁.map (e6InndiagGL K).subtype).map (baseChangeGL (algebraMap K K₁)) ≤
      ((E.comap (e6InndiagConj K)).map (e6InndiagGL K).subtype).map
        (baseChangeGL (algebraMap K K₁)) :=
    Subgroup.map_mono (Subgroup.map_mono hE₁)
  obtain ⟨w, Fr, hFr, g0, hg0C, hg0, hin⟩ := htorI K h3 K₁ E₁ hpow₁ hE₁c hC₁
    fun x y hx hy => hEab x y (hmono hx) (hmono hy)
  have h := hT1 w K ⟨h3, hK ▸ hq1, hK ▸ hq4⟩ Fr hFr g0 hg0C hg0 E₁ hpow₁
    (by rw [hE₁c]; norm_num) hin H hH
  have hle : E₁.map (e6InndiagConj K) ≤ D := by
    rw [← hmap] at hED
    exact (Subgroup.map_mono hE₁).trans hED
  exact le_bot_iff.1 ((localDeltaIn_antitone H hle).trans h.le)

end Diagonal

end CFSG.HardMathSupport.Timmesfeld.CrossChar
