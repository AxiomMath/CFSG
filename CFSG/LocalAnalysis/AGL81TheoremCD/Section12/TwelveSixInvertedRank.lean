module

public import CFSG.Open.LocalVocabulary

import CFSG.LinearAlgebra.CoprimeActions.AbelianCoprimeWeightSpaceDecomposition
import CFSG.LinearAlgebra.CoprimeActions.RepresentationScalarExtensionVocabulary

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open
open CFSG.LinearAlgebra.CoprimeActions.CharacterWeightSpaceIndependence

private theorem card_range_eq_three {F : Type*} [Field F] {V : Type*} [Group V]
    (hpow : ∀ v : V, v ^ 3 = 1) {χ : V →* Fˣ} {v : V} (hv : χ v ≠ 1) :
    Nat.card χ.range = 3 := by
  have hfact : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsub : χ.range ≤ rootsOfUnity 3 F := by
    intro y hy
    obtain ⟨u, rfl⟩ := hy
    rw [mem_rootsOfUnity, ← map_pow, hpow u, map_one]
  have hfin : Finite χ.range :=
    Finite.of_injective (Subgroup.inclusion hsub) (Subgroup.inclusion_injective hsub)
  have hx3 : χ v ^ 3 = 1 := by rw [← map_pow, hpow v, map_one]
  have horder : orderOf (χ v) = 3 := orderOf_eq_prime hx3 hv
  have hcard3 : Nat.card (Subgroup.zpowers (χ v)) = 3 := by
    rw [Nat.card_zpowers, horder]
  have hdvd : 3 ∣ Nat.card χ.range := by
    rw [← hcard3]
    exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr ⟨v, rfl⟩)
  have hle : Nat.card χ.range ≤ 3 :=
    (Nat.card_le_card_of_injective (Subgroup.inclusion hsub)
      (Subgroup.inclusion_injective hsub)).trans (card_rootsOfUnity F 3)
  obtain ⟨k, hk⟩ := hdvd
  have hpos : 0 < Nat.card χ.range := Nat.card_pos
  have : k = 1 := by omega
  omega

private theorem card_eq_three_mul_card_ker {F : Type*} [Field F] {V : Type*} [Group V]
    [Finite V] {χ : V →* Fˣ}
    (h : Nat.card χ.range = 3) : Nat.card V = 3 * Nat.card χ.ker := by
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup χ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange χ).toEquiv, h] at hcard
  omega

private noncomputable def charsTrivialOn {F : Type*} [Field F] {V : Type*} [Group V]
    (S : Finset (V →* Fˣ)) (K : Subgroup V) : Finset (V →* Fˣ) := by
  classical
  exact S.filter (fun χ => ∀ k : K, χ (k : V) = 1)

private noncomputable def charsNontrivialOn {F : Type*} [Field F] {V : Type*} [Group V]
    (S : Finset (V →* Fˣ)) (K : Subgroup V) : Finset (V →* Fˣ) := by
  classical
  exact S.filter (fun χ => ¬ ∀ k : K, χ (k : V) = 1)

private theorem two_le_card_trivial_on_ker {F : Type*} [Field F] {V : Type*} [Group V]
    (hpow : ∀ v : V, v ^ 3 = 1) {χ₀ : V →* Fˣ} {S : Finset (V →* Fˣ)}
    (hneg : ∀ χ ∈ S, χ⁻¹ ∈ S) (hχ₀S : χ₀ ∈ S) {v₀ : V} (hχ₀v : χ₀ v₀ ≠ 1) :
    2 ≤ (charsTrivialOn S χ₀.ker).card := by
  classical
  have hχ₀K : ∀ k : χ₀.ker, χ₀ (k : V) = 1 := fun k => MonoidHom.mem_ker.mp k.2
  have h1 : χ₀ ∈ charsTrivialOn S χ₀.ker :=
    Finset.mem_filter.mpr ⟨hχ₀S, hχ₀K⟩
  have h2 : χ₀⁻¹ ∈ charsTrivialOn S χ₀.ker := by
    refine Finset.mem_filter.mpr ⟨hneg χ₀ hχ₀S, fun k => ?_⟩
    rw [MonoidHom.inv_apply, hχ₀K k, inv_one]
  have hne : χ₀ ≠ χ₀⁻¹ := by
    intro h
    have h' : χ₀ v₀ = (χ₀ v₀)⁻¹ := by
      simpa [MonoidHom.inv_apply] using congrArg (fun f : V →* Fˣ => f v₀) h
    have hx2 : χ₀ v₀ * χ₀ v₀ = 1 := by
      have h2 := congrArg (fun y => y * χ₀ v₀) h'
      rwa [inv_mul_cancel] at h2
    have hx3 : χ₀ v₀ ^ 3 = 1 := by rw [← map_pow, hpow v₀, map_one]
    have hx1 : χ₀ v₀ = 1 := by
      have h3 : χ₀ v₀ ^ 3 = χ₀ v₀ := by rw [pow_succ, sq, hx2, one_mul]
      rw [← h3, hx3]
    exact hχ₀v hx1
  exact Finset.one_lt_card.mpr ⟨χ₀, h1, χ₀⁻¹, h2, hne⟩

private theorem two_mul_succ_le_card {F : Type*} [Field F] {V : Type*} [Group V] [Finite V]
    {n : ℕ} {χ₀ : V →* Fˣ} {S : Finset (V →* Fˣ)}
    (ihK : ∀ T : Finset (χ₀.ker →* Fˣ), (∀ χ ∈ T, χ⁻¹ ∈ T) →
      (∀ k : χ₀.ker, k ≠ 1 → ∃ χ ∈ T, χ k ≠ 1) → 2 * n ≤ T.card)
    (hneg : ∀ χ ∈ S, χ⁻¹ ∈ S)
    (hsep : ∀ v : V, v ≠ 1 → ∃ χ ∈ S, χ v ≠ 1)
    (hS1 : 2 ≤ (charsTrivialOn S χ₀.ker).card) : 2 * (n + 1) ≤ S.card := by
  classical
  let S₁ : Finset (V →* Fˣ) := charsTrivialOn S χ₀.ker
  let S₂ : Finset (V →* Fˣ) := charsNontrivialOn S χ₀.ker
  let T : Finset (χ₀.ker →* Fˣ) := S₂.image (fun χ => χ.comp χ₀.ker.subtype)
  have hTneg : ∀ ψ ∈ T, ψ⁻¹ ∈ T := by
    intro ψ hψ
    obtain ⟨χ, hχS₂, rfl⟩ := Finset.mem_image.mp hψ
    refine Finset.mem_image.mpr ⟨χ⁻¹, ?_, rfl⟩
    refine Finset.mem_filter.mpr ⟨hneg χ (Finset.mem_filter.mp hχS₂).1, fun h1 => ?_⟩
    exact (Finset.mem_filter.mp hχS₂).2 fun k => by
      have := h1 k
      rwa [MonoidHom.inv_apply, inv_eq_one] at this
  have hTsep : ∀ k : χ₀.ker, k ≠ 1 → ∃ ψ ∈ T, ψ k ≠ 1 := by
    intro k hk
    obtain ⟨χ, hχS, hχk⟩ := hsep (k : V) fun h => hk (Subtype.ext h)
    exact ⟨χ.comp χ₀.ker.subtype, Finset.mem_image.mpr ⟨χ,
      Finset.mem_filter.mpr ⟨hχS, fun h1 => hχk (h1 k)⟩, rfl⟩, hχk⟩
  have hTcard : 2 * n ≤ T.card := ihK T hTneg hTsep
  have hTle : T.card ≤ S₂.card := Finset.card_image_le
  have hsum : S₁.card + S₂.card = S.card := by
    simp only [S₁, S₂, charsTrivialOn, charsNontrivialOn]
    exact Finset.card_filter_add_card_filter_not
      (s := S) (p := fun χ : V →* Fˣ => ∀ k : χ₀.ker, χ (k : V) = 1)
  have hS1' : 2 ≤ S₁.card := by simpa [S₁, charsTrivialOn] using hS1
  omega

private theorem two_mul_le_card_of_chars {F : Type*} [Field F] (r : ℕ) :
    ∀ (V : Type*) [Group V] [Finite V], (∀ v : V, v ^ 3 = 1) →
      Nat.card V = 3 ^ r → ∀ S : Finset (V →* Fˣ),
        (∀ χ ∈ S, χ⁻¹ ∈ S) →
          (∀ v : V, v ≠ 1 → ∃ χ ∈ S, χ v ≠ 1) → 2 * r ≤ S.card := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro V _ _ hpow hVc S hneg hsep
    rcases r with _ | n
    · simp
    classical
    let hVfin : Fintype V := Fintype.ofFinite V
    have hcard_gt : 1 < Nat.card V := by
      rw [hVc]
      calc 1 < 3 ^ 1 := by norm_num
        _ ≤ 3 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    obtain ⟨v₀, hv₀⟩ := Fintype.exists_ne_of_one_lt_card
      (by simpa [Nat.card_eq_fintype_card] using hcard_gt) (1 : V)
    obtain ⟨χ₀, hχ₀S, hχ₀v⟩ := hsep v₀ hv₀
    have hrange3 : Nat.card χ₀.range = 3 := card_range_eq_three hpow hχ₀v
    have hKcard : Nat.card χ₀.ker = 3 ^ n := by
      have h := card_eq_three_mul_card_ker hrange3
      rw [hVc, Nat.pow_succ] at h
      have h2 : 3 * Nat.card χ₀.ker = 3 * 3 ^ n := by
        rw [← h, mul_comm (3 ^ n) 3, mul_comm 3 (3 ^ n)]
      exact Nat.mul_left_cancel (by norm_num) h2
    have ihK : ∀ T : Finset (χ₀.ker →* Fˣ), (∀ χ ∈ T, χ⁻¹ ∈ T) →
        (∀ k : χ₀.ker, k ≠ 1 → ∃ χ ∈ T, χ k ≠ 1) → 2 * n ≤ T.card :=
      fun T hTneg hTsep => ih n (by omega) ↥χ₀.ker
        (fun k => Subtype.ext (hpow (k : V))) hKcard T hTneg hTsep
    exact two_mul_succ_le_card ihK hneg hsep (two_le_card_trivial_on_ker hpow hneg hχ₀S hχ₀v)

private theorem units_injective {F W : Type*} [Field F] [AddCommGroup W] [Module F W]
    (u : (Module.End F W)ˣ) : Function.Injective (↑u : Module.End F W) := by
  have hmul : (↑u⁻¹ * ↑u : Module.End F W) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  intro a b hab
  calc a = (↑u⁻¹ * ↑u : Module.End F W) a := by rw [hmul]; rfl
    _ = (↑u⁻¹ : Module.End F W) ((↑u : Module.End F W) a) := rfl
    _ = (↑u⁻¹ : Module.End F W) ((↑u : Module.End F W) b) := by rw [hab]
    _ = (↑u⁻¹ * ↑u : Module.End F W) b := rfl
    _ = b := by rw [hmul]; rfl

private theorem units_inv_apply_of_eq_smul {F W : Type*} [Field F] [AddCommGroup W]
    [Module F W] (u : (Module.End F W)ˣ) {c : F} (hc : c ≠ 0) {w : W}
    (h : (↑u : Module.End F W) w = c • w) : (↑u⁻¹ : Module.End F W) w = c⁻¹ • w := by
  have hmul : (↑u * ↑u⁻¹ : Module.End F W) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  refine units_injective u ?_
  have h1 : (↑u : Module.End F W) ((↑u⁻¹ : Module.End F W) w) = w := by
    rw [show (↑u : Module.End F W) ((↑u⁻¹ : Module.End F W) w) =
      (↑u * ↑u⁻¹ : Module.End F W) w from rfl, hmul]
    rfl
  rw [h1, map_smul, h, smul_smul, inv_mul_cancel₀ hc, one_smul]

private theorem weightSpace_inv_ne_bot {F W V : Type*} [Field F] [AddCommGroup W] [Module F W]
    [Group V] (ρ : Representation F V W) (χ : V →* Fˣ) (A : (Module.End F W)ˣ)
    (hA : ∀ v : V, A * ρ.toHomUnits v * A⁻¹ = ρ.toHomUnits v⁻¹)
    (h : weightSpace ρ χ ≠ ⊥) : weightSpace ρ χ⁻¹ ≠ ⊥ := by
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff (weightSpace ρ χ)).mp h
  have hAne : (↑A : Module.End F W) w ≠ 0 := fun h0 => hw0 (units_injective A (by simpa using h0))
  refine (Submodule.ne_bot_iff (weightSpace ρ χ⁻¹)).mpr ⟨(↑A : Module.End F W) w, ?_, hAne⟩
  rw [mem_weightSpace]
  intro v
  let B : (Module.End F W)ˣ := ρ.toHomUnits v
  have hBw : (↑B : Module.End F W) w = ((χ v : Fˣ) : F) • w :=
    (mem_weightSpace ρ χ w).mp hw v
  have hBinvw : (↑(B⁻¹) : Module.End F W) w = ((χ v : Fˣ) : F)⁻¹ • w :=
    units_inv_apply_of_eq_smul B (Units.ne_zero (χ v)) hBw
  have hBAu : B * A = A * B⁻¹ := by
    have h := hA v⁻¹
    rw [show ρ.toHomUnits v⁻¹ = B⁻¹ from map_inv ρ.toHomUnits v] at h
    have h' : A * B⁻¹ * A⁻¹ = B := by simpa [B] using h
    calc B * A = (A * B⁻¹ * A⁻¹) * A := by rw [h']
      _ = A * B⁻¹ := by group
  have hBA : (↑B : Module.End F W) * (↑A : Module.End F W) =
      (↑A : Module.End F W) * (↑(B⁻¹) : Module.End F W) := by
    rw [show (↑B : Module.End F W) * (↑A : Module.End F W) = ↑(B * A) from rfl,
      show (↑A : Module.End F W) * (↑(B⁻¹) : Module.End F W) = ↑(A * B⁻¹) from rfl, hBAu]
  calc ρ v ((↑A : Module.End F W) w) = ((↑B : Module.End F W) * (↑A : Module.End F W)) w := rfl
    _ = ((↑A : Module.End F W) * (↑(B⁻¹) : Module.End F W)) w := by rw [hBA]
    _ = (↑A : Module.End F W) ((↑(B⁻¹) : Module.End F W) w) := rfl
    _ = (↑A : Module.End F W) (((χ v : Fˣ) : F)⁻¹ • w) := by rw [hBinvw]
    _ = ((χ v : Fˣ) : F)⁻¹ • ((↑A : Module.End F W) w) := by rw [map_smul]
    _ = ((χ⁻¹) v : F) • ((↑A : Module.End F W) w) := by
          rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]

private theorem eq_one_of_forall_weightSpace_eq {F W V : Type*} [Field F] [AddCommGroup W]
    [Module F W] [Group V] (ρ : Representation F V W) (S : Finset (V →* Fˣ))
    (hsup : ⨆ χ ∈ S, weightSpace ρ χ = ⊤) {v : V} (h : ∀ χ ∈ S, χ v = 1) : ρ v = 1 := by
  have heig : Module.End.eigenspace (ρ v) (1 : F) = ⊤ := by
    rw [eq_top_iff, ← hsup]
    refine iSup₂_le fun χ hχ w hw => ?_
    rw [mem_weightSpace] at hw
    rw [Module.End.mem_eigenspace_iff]
    simpa [h χ hχ] using hw v
  ext w
  have hw : w ∈ Module.End.eigenspace (ρ v) (1 : F) := by rw [heig]; exact Submodule.mem_top
  simpa [Module.End.mem_eigenspace_iff] using hw

private theorem iSup_weightSpace_eq_top_of_mem {F W V : Type*} [Field F] [AddCommGroup W]
    [Module F W] [Group V] (ρ : Representation F V W) (S : Finset (V →* Fˣ))
    (hmem : ∀ χ : V →* Fˣ, weightSpace ρ χ ≠ ⊥ → χ ∈ S)
    (hspan : ⨆ χ : V →* Fˣ, weightSpace ρ χ = ⊤) :
    ⨆ χ ∈ S, weightSpace ρ χ = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← hspan]
  refine iSup_le fun χ => ?_
  by_cases hχ : χ ∈ S
  · exact le_iSup₂_of_le χ hχ le_rfl
  · have hbot : weightSpace ρ χ = ⊥ := by
      by_contra hne
      exact hχ (hmem χ hne)
    rw [hbot]
    exact bot_le

private theorem two_mul_le_finrank_of_inverted_algClosed {F : Type*} [Field F] [IsAlgClosed F]
    (h3 : (3 : F) ≠ 0) {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    {X : Type*} [Group X] [Finite X] (φ : X →* (Module.End F W)ˣ) {V : Subgroup X}
    (hV : IsElemAbelian 3 V) {r : ℕ} (hVc : Nat.card V = 3 ^ r) (hinj : V ⊓ φ.ker = ⊥)
    {τ : X} (hτ : ∀ v ∈ V, τ * v * τ⁻¹ = v⁻¹) : 2 * r ≤ Module.finrank F W := by
  classical
  let ρX : Representation F X W := (Units.coeHom (Module.End F W)).comp φ
  let ρV : Representation F V W := ρX.comp V.subtype
  have hcomm : IsMulCommutative V := hV.1
  let hVcomm : CommGroup V := IsMulCommutative.instCommGroup
  have hpow : ∀ v : V, v ^ 3 = 1 := fun v => Subtype.ext (hV.2 v v.2)
  have hcard : (Nat.card V : F) ≠ 0 := by
    rw [hVc, Nat.cast_pow]
    exact pow_ne_zero r h3
  have hspan : ⨆ χ : V →* Fˣ, weightSpace ρV χ = ⊤ :=
    CFSG.LinearAlgebra.CoprimeActions.AbelianCoprimeWeightSpaceDecomposition.span_eq_top ρV hcard
  have hind : iSupIndep (fun χ : V →* Fˣ => weightSpace ρV χ) :=
    independent ρV (fun χ => χ) Function.injective_id
  let hVchar : Fintype (V →* Fˣ) := Fintype.ofFinite (V →* Fˣ)
  let S : Finset (V →* Fˣ) := Finset.univ.filter (fun χ => weightSpace ρV χ ≠ ⊥)
  have hsup : (⨆ χ ∈ S, weightSpace ρV χ) = ⊤ :=
    iSup_weightSpace_eq_top_of_mem ρV S
      (fun χ hχ => Finset.mem_filter.mpr ⟨Finset.mem_univ χ, hχ⟩) hspan
  have hdim : S.card ≤ Module.finrank F W := by
    let hVne : Fintype {χ : V →* Fˣ // weightSpace ρV χ ≠ ⊥} :=
      hind.fintypeNeBotOfFiniteDimensional
    have hScard : S.card = Fintype.card {χ : V →* Fˣ // weightSpace ρV χ ≠ ⊥} := by
      rw [Fintype.card_subtype]
    rw [hScard]
    exact hind.subtype_ne_bot_le_finrank
  have hinv : ∀ v : V, φ τ * ρV.toHomUnits v * (φ τ)⁻¹ = ρV.toHomUnits v⁻¹ := by
    intro v
    have h1 : ρV.toHomUnits v = φ (v : X) := Units.ext rfl
    have h2 : ρV.toHomUnits v⁻¹ = φ ((v : X)⁻¹) := Units.ext rfl
    rw [h1, h2]
    calc φ τ * φ (v : X) * (φ τ)⁻¹ = φ τ * φ (v : X) * φ (τ⁻¹) := by rw [← map_inv]
      _ = φ (τ * (v : X) * τ⁻¹) := by rw [← map_mul, ← map_mul]
      _ = φ ((v : X)⁻¹) := by rw [hτ (v : X) v.2]
  have hneg : ∀ χ ∈ S, χ⁻¹ ∈ S := fun χ hχ => Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    weightSpace_inv_ne_bot ρV χ (φ τ) hinv (by simpa [S] using hχ)⟩
  have hsep : ∀ v : V, v ≠ 1 → ∃ χ ∈ S, χ v ≠ 1 := by
    intro v hv
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    have hv1 : ρV v = 1 := eq_one_of_forall_weightSpace_eq ρV S hsup h
    have hker : (v : X) ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      apply Units.ext
      simpa [ρV, ρX] using hv1
    have hmem : (v : X) ∈ V ⊓ φ.ker := ⟨v.2, hker⟩
    rw [hinj] at hmem
    exact hv (Subtype.ext (Subgroup.mem_bot.mp hmem))
  have hcount := two_mul_le_card_of_chars r V hpow hVc S hneg hsep
  omega

theorem two_mul_le_finrank_of_inverted {K : Type*} [Field K] (h3 : (3 : K) ≠ 0)
    {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {X : Type*} [Group X] [Finite X] (φ : X →* (Module.End K W)ˣ) {V : Subgroup X}
    (hV : IsElemAbelian 3 V) {r : ℕ} (hVc : Nat.card V = 3 ^ r) (hinj : V ⊓ φ.ker = ⊥)
    {τ : X} (hτ : ∀ v ∈ V, τ * v * τ⁻¹ = v⁻¹) : 2 * r ≤ Module.finrank K W := by
  classical
  let ρK : Representation K X W := (Units.coeHom (Module.End K W)).comp φ
  let ρF : Representation (AlgebraicClosure K) X
      (TensorProduct K (AlgebraicClosure K) W) :=
    CFSG.LinearAlgebra.CoprimeActions.RepresentationScalarExtensionVocabulary.extend ρK
  have h3F : (3 : AlgebraicClosure K) ≠ 0 := by
    intro h
    apply h3
    have h' : algebraMap K (AlgebraicClosure K) (3 : K) =
        algebraMap K (AlgebraicClosure K) 0 := by
      rw [map_ofNat, map_zero]
      exact h
    exact FaithfulSMul.algebraMap_injective K (AlgebraicClosure K) h'
  have hinjF : V ⊓ ρF.toHomUnits.ker = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Subgroup.mem_inf] at hv
    obtain ⟨hvV, hvker⟩ := hv
    rw [Subgroup.mem_bot]
    have h1 : ρF.toHomUnits v = 1 := hvker
    have h2 : ρF v = 1 := by
      have := MonoidHom.coe_toHomUnits ρF v
      rw [h1] at this
      simpa using this.symm
    have h3' : (ρK v).baseChange (AlgebraicClosure K) = 1 := by
      simpa [ρF,
        CFSG.LinearAlgebra.CoprimeActions.RepresentationScalarExtensionVocabulary.extend_apply]
        using h2
    have h4 : LinearMap.baseChangeHom K (AlgebraicClosure K) W W (ρK v) = 1 := by
      simpa using h3'
    have h5 : ρK v = 1 := by
      apply LinearMap.baseChangeHom_injective K W (AlgebraicClosure K)
      rw [h4, LinearMap.baseChangeHom_apply, LinearMap.baseChange_one]
    have h6 : φ v = 1 := by
      apply Units.ext
      simpa [ρK] using h5
    have hmem : v ∈ V ⊓ φ.ker := ⟨hvV, MonoidHom.mem_ker.mpr h6⟩
    rw [hinj] at hmem
    simpa using Subgroup.mem_bot.mp hmem
  calc 2 * r ≤ Module.finrank (AlgebraicClosure K) (TensorProduct K (AlgebraicClosure K) W) :=
        two_mul_le_finrank_of_inverted_algClosed h3F ρF.toHomUnits hV hVc hinjF hτ
    _ = Module.finrank K W := Module.finrank_baseChange

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
