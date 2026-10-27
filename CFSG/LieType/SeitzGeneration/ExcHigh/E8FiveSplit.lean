module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.Defs
public import CFSG.HardMathSupport.Malle.SeitzCube.Landing
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigidTools
public import CFSG.RankThree.PartOne.KE.SuzukiDescent

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG.Blueprint.Chevalley CFSG.LieType.SeitzGeneration.ExcHighThree
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Group

theorem e8Split_normalizesRIn_of_conj {M : Type*} [Group M] (r : ℕ) (E U : Subgroup M) (k : M)
    (hU : ∃ u ∈ U, u ≠ 1) (hexp : ∀ u ∈ U, u ^ r = 1)
    (hnorm : ∀ x ∈ E, ∀ m : M, m ∈ U ↔ k * x * k⁻¹ * m * (k * x * k⁻¹)⁻¹ ∈ U) :
    NormalizesRIn r E := by
  obtain ⟨u, huU, hu1⟩ := hU
  refine ⟨U.comap (MulAut.conj k).toMonoidHom, ?_, ?_, ?_⟩
  · intro hbot
    have hmem : k⁻¹ * u * k ∈ U.comap (MulAut.conj k).toMonoidHom := by
      rw [Subgroup.mem_comap]
      show k * (k⁻¹ * u * k) * k⁻¹ ∈ U
      rwa [show k * (k⁻¹ * u * k) * k⁻¹ = u by group]
    rw [hbot, Subgroup.mem_bot] at hmem
    apply hu1
    calc u = k * (k⁻¹ * u * k) * k⁻¹ := by group
      _ = 1 := by rw [hmem]; group
  · intro h
    refine ⟨1, Subtype.ext ?_⟩
    have hh : k * (h : M) * k⁻¹ ∈ U := h.2
    have h2 : (k * (h : M) * k⁻¹) ^ r = 1 := hexp _ hh
    rw [conj_pow] at h2
    simp only [Subgroup.coe_pow, Subgroup.coe_one, pow_one]
    calc (h : M) ^ r = k⁻¹ * (k * (h : M) ^ r * k⁻¹) * k := by group
      _ = 1 := by rw [h2]; group
  · intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    show k * h * k⁻¹ ∈ U ↔ k * (x * h * x⁻¹) * k⁻¹ ∈ U
    have e : k * (x * h * x⁻¹) * k⁻¹ = k * x * k⁻¹ * (k * h * k⁻¹) * (k * x * k⁻¹)⁻¹ := by
      group
    rw [e]
    exact hnorm x hx _

end Group

section Split


theorem e8Split_pinnedX_pow (τ : Tag) {K : Type} [Field K] (α : Fin τ.rank → ℤ) (c : K) (n : ℕ) :
    pinnedX τ K α c ^ n = pinnedX τ K α (n • c) := by
  induction n with
  | zero => simp [pinnedX_zero]
  | succ n ih => rw [pow_succ, ih, succ_nsmul, pinnedX_add]

theorem e8Split_pow_ringChar (τ : Tag) {K : Type} [Field K] (α : Fin τ.rank → ℤ) {u : ModGL τ K}
    (hu : u ∈ rootSubgroup τ K α) : u ^ ringChar K = 1 := by
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hu
  rw [e8Split_pinnedX_pow, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, pinnedX_zero]

theorem e8Split_conj_mem_iff (τ : Tag) {K : Type} [Field K] {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (b : Fin τ.rank → Kˣ) (m : ModGL τ K) :
    m ∈ rootSubgroup τ K α ↔
      rootDiagUnit τ b * m * (rootDiagUnit τ b)⁻¹ ∈ rootSubgroup τ K α := by
  have key : ∀ (b' : Fin τ.rank → Kˣ) (m' : ModGL τ K), m' ∈ rootSubgroup τ K α →
      rootDiagUnit τ b' * m' * (rootDiagUnit τ b')⁻¹ ∈ rootSubgroup τ K α := by
    intro b' m' hm'
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hm'
    exact mem_rootSubgroup.2 ⟨_, (CFSG.LieType.Chevalley.rootDiagUnit_conj_pinnedX b' hα c).symm⟩
  refine ⟨key b m, fun h => ?_⟩
  have h' := key b⁻¹ _ h
  have e : rootDiagUnit τ b⁻¹ * (rootDiagUnit τ b * m * (rootDiagUnit τ b)⁻¹) *
      (rootDiagUnit τ b⁻¹)⁻¹ = m := by
    rw [← CFSG.LieType.Chevalley.rootDiagUnit_inv]
    group
  rwa [e] at h'

theorem e8Split_mem_U_iff_conj (τ : Tag) {K : Type} [Field K] {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) {y : adjointGroup τ K} {b : Fin τ.rank → Kˣ}
    (hb : (y : ModGL τ K) = rootDiagUnit τ b) (m : adjointGroup τ K) :
    m ∈ (rootSubgroup τ K α).subgroupOf (adjointGroup τ K) ↔
      y * m * y⁻¹ ∈ (rootSubgroup τ K α).subgroupOf (adjointGroup τ K) := by
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv, hb]
  exact e8Split_conj_mem_iff τ hα b _

theorem e8Split_rational_of_torus (τ : Tag) {K : Type} [Field K] [Finite K]
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {y : ModGL τ K}
    (hT : CFSG.LieType.Chevalley.baseChangeGL (algebraMap K (AlgebraicClosure K)) y ∈
      CFSG.LieType.Chevalley.torusGroup τ (AlgebraicClosure K))
    (hF : Units.map (entrywiseHom Fr)
        (CFSG.LieType.Chevalley.baseChangeGL (algebraMap K (AlgebraicClosure K)) y) =
      CFSG.LieType.Chevalley.baseChangeGL (algebraMap K (AlgebraicClosure K)) y) :
    ∃ b : Fin τ.rank → Kˣ, y = rootDiagUnit τ b := by
  obtain ⟨a, ha⟩ := CFSG.LieType.Chevalley.exists_rootDiagUnit_eq_of_mem_torusGroup hT
  rw [ha, CFSG.HardMathSupport.Timmesfeld.CrossChar.units_map_entrywiseHom_rootDiagUnit] at hF
  have hfix : ∀ i, Units.map Fr.toMonoidHom (a i) = a i := fun i =>
    congrFun (CFSG.LieType.Chevalley.rootDiagUnit_injective hF) i
  have hrange : ∀ i, ∃ s : K, algebraMap K (AlgebraicClosure K) s = (a i : AlgebraicClosure K) := by
    intro i
    apply Set.mem_range.1
    apply CFSG.RankThree.PartOne.KE.mem_range_algebraMap_of_pow_card_eq
    rw [← hFr]
    have h := congrArg Units.val (hfix i)
    simpa using h
  choose b hb using hrange
  have hb0 : ∀ i, b i ≠ 0 := fun i h => (a i).ne_zero (by rw [← hb i, h, map_zero])
  refine ⟨fun i => Units.mk0 (b i) (hb0 i), ?_⟩
  apply CFSG.LieType.Chevalley.baseChangeGL_injective (algebraMap K (AlgebraicClosure K))
  rw [ha, CFSG.LieType.Chevalley.baseChangeGL_rootDiagUnit]
  congr 1
  funext i
  exact Units.ext (hb i).symm

theorem e8_normalizesRNative_of_split_datum {K : Type} [Field K] [Finite K]
    {E₀ : Subgroup (adjointGroup Tag.E8 K)} (D : LangPlaneData Tag.E8 K E₀)
    (hw : D.w = 1) : NormalizesRNative Tag.E8 K E₀ := by
  obtain ⟨w, Fr, hFr, g0, hg0C, hg0, c, hc⟩ := D
  subst hw
  rw [CFSG.LieType.Chevalley.canonicalRep_one, mul_one] at hg0
  rw [CFSG.LieType.Chevalley.canonicalRep_one] at hc
  obtain ⟨γ, hγ, hγg⟩ := Subgroup.mem_map.1
    (CFSG.HardMathSupport.Malle.SeitzCube.mem_map_baseChange_of_frobenius_fixed_E8 Fr hFr hg0C hg0)
  obtain ⟨g', hg'⟩ : ∃ g' : adjointGroup Tag.E8 K, (g' : ModGL Tag.E8 K) = γ := ⟨⟨γ, hγ⟩, rfl⟩
  have hg'B : CFSG.LieType.Chevalley.baseChangeGL (algebraMap K (AlgebraicClosure K))
      (g' : ModGL Tag.E8 K) = g0 := by
    rw [hg']
    exact hγg
  obtain ⟨α, hα⟩ : ∃ α : Fin Tag.E8.rank → ℤ, IsRoot Tag.E8 α :=
    ⟨_, isRoot_single Tag.E8 ⟨0, by decide⟩⟩
  obtain ⟨k, hk⟩ : ∃ k : adjointGroup Tag.E8 K, k = g'⁻¹ * c := ⟨_, rfl⟩
  have hrat : ∀ x ∈ E₀, ∃ b : Fin Tag.E8.rank → Kˣ,
      ((k * x * k⁻¹ : adjointGroup Tag.E8 K) : ModGL Tag.E8 K) = rootDiagUnit Tag.E8 b := by
    intro x hx
    obtain ⟨t, ht, htb⟩ := Subgroup.mem_map.1 (hc x hx)
    have htb' : g0 * t * g0⁻¹ = CFSG.LieType.Chevalley.baseChangeGL
        (algebraMap K (AlgebraicClosure K))
          ((c * x * c⁻¹ : adjointGroup Tag.E8 K) : ModGL Tag.E8 K) :=
      htb
    have e : ((k * x * k⁻¹ : adjointGroup Tag.E8 K) : ModGL Tag.E8 K) =
        (g' : ModGL Tag.E8 K)⁻¹ * ((c * x * c⁻¹ : adjointGroup Tag.E8 K) : ModGL Tag.E8 K) *
          (g' : ModGL Tag.E8 K) := by
      rw [hk]
      simp only [mul_inv_rev, inv_inv, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have hyb : CFSG.LieType.Chevalley.baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((k * x * k⁻¹ : adjointGroup Tag.E8 K) : ModGL Tag.E8 K) = t := by
      rw [e, map_mul, map_mul, map_inv, hg'B, ← htb']
      group
    have ht' := CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.1 ht
    have hT : CFSG.LieType.Chevalley.baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((k * x * k⁻¹ : adjointGroup Tag.E8 K) : ModGL Tag.E8 K) ∈
          CFSG.LieType.Chevalley.torusGroup Tag.E8 (AlgebraicClosure K) := by
      rw [hyb]
      exact ht'.1
    have hF : Units.map (entrywiseHom Fr)
        (CFSG.LieType.Chevalley.baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((k * x * k⁻¹ : adjointGroup Tag.E8 K) : ModGL Tag.E8 K)) =
        CFSG.LieType.Chevalley.baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((k * x * k⁻¹ : adjointGroup Tag.E8 K) : ModGL Tag.E8 K) := by
      rw [hyb]
      simpa using ht'.2
    exact e8Split_rational_of_torus Tag.E8 Fr hFr hT hF
  refine e8Split_normalizesRIn_of_conj (ringChar K) E₀
    ((rootSubgroup Tag.E8 K α).subgroupOf (adjointGroup Tag.E8 K)) k ?_ ?_ ?_
  · refine ⟨⟨pinnedX Tag.E8 K α 1, pinnedX_mem_adjointGroup α 1⟩, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      exact mem_rootSubgroup.2 ⟨1, rfl⟩
    · intro h
      have h1 : pinnedX Tag.E8 K α (1 : K) ≠ 1 := by
        intro h1
        have h0 : pinnedX Tag.E8 K α (1 : K) = pinnedX Tag.E8 K α 0 := by
          rw [h1, pinnedX_zero]
        exact one_ne_zero (pinnedX_injective Tag.E8 K α h0)
      exact h1 (congrArg Subtype.val h)
  · intro u hu
    rw [Subgroup.mem_subgroupOf] at hu
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact e8Split_pow_ringChar Tag.E8 α hu
  · intro x hx m
    obtain ⟨b, hb⟩ := hrat x hx
    exact e8Split_mem_U_iff_conj Tag.E8 hα hb m

end Split

end CFSG.LieType.SeitzGeneration.ExcHigh
