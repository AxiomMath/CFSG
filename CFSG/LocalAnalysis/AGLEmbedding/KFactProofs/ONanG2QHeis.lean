module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG2QExp
public import CFSG.LieType.AlgebraicGroups.AllCharacteristicLang
public import CFSG.RankThree.Chevalley.G2F4FiniteFieldFixedMatrices

public section

namespace CFSG.AGLEmbedding.KFactProofs.G2Q

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups

set_option linter.unusedSectionVars false


section Frobenius

variable {L : Type} [Field L]

theorem frob_weylElt (σ : L →+* L) (i : Fin Tag.G2.rank) (t : Lˣ) :
    Units.map (entrywiseHom σ) (weylElt .G2 L i t) =
      weylElt .G2 L i (Units.map (σ : L →* L) t) := by
  rw [weylElt_eq_xUnit_mul, weylElt_eq_xUnit_mul, map_mul, map_mul,
    units_map_entrywiseHom_xUnit, units_map_entrywiseHom_yUnit]
  simp

theorem frob_torusElt (σ : L →+* L) (i : Fin Tag.G2.rank) (t : Lˣ) :
    Units.map (entrywiseHom σ) (torusElt .G2 L i t) =
      torusElt .G2 L i (Units.map (σ : L →* L) t) := by
  have h1 := frob_weylElt σ i (-1)
  rw [torusElt, torusElt, map_mul, frob_weylElt, h1]
  simp

theorem frob_tz (σ : L →+* L) (s t : Lˣ) :
    Units.map (entrywiseHom σ) (tz s t : ModGL .G2 L) =
      tz (Units.map (σ : L →* L) s) (Units.map (σ : L →* L) t) := by
  rw [tz, tz, map_mul, frob_torusElt, frob_torusElt]

theorem frob_n0 (σ : L →+* L) : Units.map (entrywiseHom σ) (n0 : ModGL .G2 L) = n0 := by
  rw [n0, frob_weylElt]
  simp

theorem frob_n1 (σ : L →+* L) : Units.map (entrywiseHom σ) (n1 : ModGL .G2 L) = n1 := by
  rw [n1, frob_weylElt]
  simp

theorem frob_yq (σ : L →+* L) : Units.map (entrywiseHom σ) (yq : ModGL .G2 L) = yq := by
  rw [yq, map_mul, map_mul, frob_n0, frob_n1]

@[expose] noncomputable def nw0 : ModGL .G2 L := n0 * n1 * yq

theorem nw0_tz (s t : Lˣ) : (nw0 : ModGL .G2 L) * tz s t * nw0⁻¹ = tz s⁻¹ t⁻¹ := by
  have key : ∀ a b c z : ModGL .G2 L, (a * b * c) * z * (a * b * c)⁻¹ =
      a * (b * (c * z * c⁻¹) * b⁻¹) * a⁻¹ := by
    intros; group
  rw [nw0, key, yq_tz, n1_tz, n0_tz]
  congr 1
  · apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    module
  · apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    module

theorem nw0_comm_yq : (nw0 : ModGL .G2 L) * yq = yq * nw0 := by
  rw [nw0, yq]
  group

theorem frob_nw0 (σ : L →+* L) : Units.map (entrywiseHom σ) (nw0 : ModGL .G2 L) = nw0 := by
  rw [nw0, map_mul, map_mul, frob_n0, frob_n1, frob_yq]

theorem nw0_mem_adjointGroup : (nw0 : ModGL .G2 L) ∈ adjointGroup .G2 L :=
  mul_mem (mul_mem (weylElt_mem_adjointGroup ia 1) (weylElt_mem_adjointGroup ir 1))
    yq_mem_adjointGroup

end Frobenius

theorem exists_rational_conj (K : Type) [Field K] [Finite K] :
    ∃ F : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, F c = c ^ Nat.card K) ∧
      ∀ n ∈ adjointGroup .G2 (AlgebraicClosure K),
        ∃ g ∈ adjointGroup .G2 (AlgebraicClosure K),
          ∀ s ∈ adjointGroup .G2 (AlgebraicClosure K),
            n * Units.map (entrywiseHom F) s * n⁻¹ = s →
            g * s * g⁻¹ ∈ (adjointGroup .G2 K).map
              (baseChangeGL (algebraMap K (AlgebraicClosure K))) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  set q := Nat.card K with hq
  have hℓ : (ringChar K).Prime := CharP.char_is_prime K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  obtain ⟨e, -, hqe⟩ := FiniteField.card K (ringChar K)
  let L := AlgebraicClosure K
  have : CharP L (ringChar K) := charP_of_injective_algebraMap (algebraMap K L).injective _
  have : ExpChar L (ringChar K) := ExpChar.prime hℓ
  set F : L →+* L := iterateFrobenius L (ringChar K) e
  have hF : ∀ c : L, F c = c ^ q := fun c => by
    rw [iterateFrobenius_def, hq, Nat.card_eq_fintype_card, hqe]
  refine ⟨F, hF, fun n hn => ?_⟩
  obtain ⟨S₁, hS, hLang⟩ :=
    (exceptional_all_characteristic_field_Lang_surjectivity (ringChar K) L (e : ℕ) e.pos).1 .G2
  obtain ⟨g₀, hg₀⟩ := hLang ⟨n, hn⟩
  set g : ModGL .G2 L := (g₀ : ModGL .G2 L) with hgdef
  have hFg : Units.map (entrywiseHom F) g = g * n := by
    have h := congrArg Subtype.val hg₀
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
    rw [hS] at h
    rw [h, mul_inv_cancel_left]
  refine ⟨g, g₀.2, fun s hs hns => ?_⟩
  have hfix := (CFSG.RankThree.Chevalley.G2_F4_exact_finite_field_fixed_root_matrices
    (τ := .G2) (Or.inl rfl) K (AlgebraicClosure K) F hF).1
  rw [← hfix]
  refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem g₀.2 hs) (inv_mem g₀.2), ?_⟩
  change Units.map (entrywiseHom F) (g * s * g⁻¹) = g * s * g⁻¹
  rw [map_mul, map_mul, map_inv, hFg]
  calc g * n * Units.map (entrywiseHom F) s * (g * n)⁻¹
      = g * (n * Units.map (entrywiseHom F) s * n⁻¹) * g⁻¹ := by group
    _ = g * s * g⁻¹ := by rw [hns]


noncomputable def baseChangeToMod (K L : Type) [Field K] [Field L] [Algebra K L] :
    adjointGroup .G2 K →* ModGL .G2 L :=
  (baseChangeGL (algebraMap K L)).comp (adjointGroup .G2 K).subtype

theorem baseChangeToMod_injective (K L : Type) [Field K] [Field L] [Algebra K L] :
    Function.Injective (baseChangeToMod K L) :=
  (baseChangeGL_injective (τ := .G2) (algebraMap K L)).comp Subtype.val_injective

theorem exists_pair_not_dvd_three {K : Type} [Field K] [Finite K] (h3 : ¬ 3 ∣ Nat.card K) :
    ∃ x y : adjointGroup .G2 K, x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y ≠ y * x ∧
      IsPGroup 3 (Subgroup.closure ({x, y} : Set (adjointGroup .G2 K))) := by
  classical
  have hne : (3 : K) ≠ 0 := by
    intro h
    apply h3
    have hℓ : (ringChar K).Prime := CharP.char_is_prime K (ringChar K)
    have hp : ringChar K = 3 := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1
      ((CharP.cast_eq_zero_iff K (ringChar K) 3).1 (by exact_mod_cast h))
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨e, -, hqe⟩ := FiniteField.card K (ringChar K)
    rw [Nat.card_eq_fintype_card, hqe, hp]
    exact dvd_pow_self 3 e.ne_zero
  have : NeZero ((3 : ℕ) : K) := ⟨by exact_mod_cast hne⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.prim (M := AlgebraicClosure K) (n := 3)
  set ω : (AlgebraicClosure K)ˣ := (hζ.isUnit (by norm_num)).unit with hωdef
  have hω3 : ω ^ 3 = 1 := Units.ext (by simpa [hωdef] using hζ.pow_eq_one)
  have hω1 : ω ≠ 1 := fun h =>
    hζ.ne_one (by norm_num) (by simpa [hωdef] using congrArg Units.val h)
  obtain ⟨F, hF, hTW⟩ := exists_rational_conj K
  have hq3 : Nat.card K % 3 = 1 ∨ Nat.card K % 3 = 2 := by omega
  have hFω : Units.map (F : AlgebraicClosure K →* AlgebraicClosure K) ω = ω ^ Nat.card K :=
    Units.ext (by simp [hF])
  obtain ⟨n, hn, hnx, hny⟩ : ∃ n : ModGL .G2 (AlgebraicClosure K),
      n ∈ adjointGroup .G2 (AlgebraicClosure K) ∧
      n * Units.map (entrywiseHom F) (tz ω 1 : ModGL .G2 (AlgebraicClosure K)) * n⁻¹ = tz ω 1 ∧
      n * Units.map (entrywiseHom F) (yq : ModGL .G2 (AlgebraicClosure K)) * n⁻¹ = yq := by
    rcases hq3 with h1 | h2
    · have hωq : ω ^ Nat.card K = ω := by
        rw [← Nat.div_add_mod (Nat.card K) 3, h1, pow_add, pow_mul, hω3, one_pow, one_mul,
          pow_one]
      refine ⟨1, one_mem _, ?_, ?_⟩
      · rw [frob_tz, hFω, hωq, map_one]
        group
      · rw [frob_yq]
        group
    · have hωq : ω ^ Nat.card K = ω⁻¹ := by
        rw [← Nat.div_add_mod (Nat.card K) 3, h2, pow_add, pow_mul, hω3, one_pow, one_mul]
        refine eq_inv_of_mul_eq_one_left ?_
        rw [← pow_succ]
        exact hω3
      refine ⟨nw0, nw0_mem_adjointGroup, ?_, ?_⟩
      · rw [frob_tz, hFω, hωq, map_one, nw0_tz, inv_inv, inv_one]
      · rw [frob_yq, nw0_comm_yq]
        group
  obtain ⟨g, hg, hrat⟩ := hTW n hn
  obtain ⟨x', hx'G, hx'⟩ := hrat _ (tz_mem_adjointGroup ω 1) hnx
  obtain ⟨y', hy'G, hy'⟩ := hrat _ yq_mem_adjointGroup hny
  set φ : adjointGroup .G2 K →* ModGL .G2 (AlgebraicClosure K) :=
    baseChangeToMod K (AlgebraicClosure K) with hφ
  have hφx : φ ⟨x', hx'G⟩ = g * tz ω 1 * g⁻¹ := hx'
  have hφy : φ ⟨y', hy'G⟩ = g * yq * g⁻¹ := hy'
  have hφinj : Function.Injective φ := baseChangeToMod_injective K _
  have hx0 : (tz ω 1 : ModGL .G2 (AlgebraicClosure K)) ^ 3 = 1 := by
    rw [tz_pow, hω3, one_pow, tz_one_one]
  refine ⟨⟨x', hx'G⟩, ⟨y', hy'G⟩, hφinj ?_, hφinj ?_, ?_, ?_⟩
  · rw [map_pow, hφx, conj_pow, hx0, map_one]
    group
  · rw [map_pow, hφy, conj_pow, yq_pow_three, map_one]
    group
  · intro h
    have h1 := congrArg φ h
    rw [map_mul, map_mul, hφx, hφy] at h1
    have h2 : g * (tz ω 1 * yq) * g⁻¹ = g * (yq * tz ω 1) * g⁻¹ := by
      simpa [mul_assoc] using h1
    have h3 : (tz ω 1 : ModGL .G2 (AlgebraicClosure K)) * yq = yq * tz ω 1 :=
      mul_left_cancel (mul_right_cancel h2)
    have h4 : (yq : ModGL .G2 (AlgebraicClosure K)) * tz ω 1 * yq⁻¹ = tz ω 1 := by
      rw [← h3]
      group
    rw [yq_tz] at h4
    have := (tz_injective h4).2
    apply hω1
    simpa using this
  · have hS := ext3_tz3 hω1
    let S := extSub hS
    have hxS : (tz ω 1 : ModGL .G2 (AlgebraicClosure K)) ∈ S :=
      le_extSub hS ⟨ω, 1, hω3, one_pow _, rfl⟩
    have hyS : (yq : ModGL .G2 (AlgebraicClosure K)) ∈ S := y_mem_extSub hS
    have hC : Subgroup.closure ({⟨x', hx'G⟩, ⟨y', hy'G⟩} : Set (adjointGroup .G2 K)) ≤
        (S.map (MulAut.conj g).toMonoidHom).comap φ := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ (rfl | rfl)
      · exact ⟨_, hxS, by rw [hφx]; rfl⟩
      · exact ⟨_, hyS, by rw [hφy]; rfl⟩
    intro z
    refine ⟨1, ?_⟩
    obtain ⟨s, hs, hsz⟩ := hC z.2
    have hz3 : (φ (z : adjointGroup .G2 K)) ^ 3 = 1 := by
      rw [← hsz]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [conj_pow, pow_three_of_mem_extSub hω1 hs]
      group
    apply Subtype.ext
    apply hφinj
    rw [pow_one, Subgroup.coe_pow, map_pow, hz3, Subgroup.coe_one, map_one]

end CFSG.AGLEmbedding.KFactProofs.G2Q
