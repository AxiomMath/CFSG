module

public import CFSG.HardMathSupport.Timmesfeld.Steinberg.PrimeCentralizer
public import CFSG.LieType.SeitzGeneration.ExcHighThree.PurityLang
public import CFSG.RankThree.PartOne.KE.SuzukiDescent
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangInner

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.SeitzGeneration.ExcHighThree

set_option linter.unusedSectionVars false

section Descent


theorem mem_map_baseChange_of_frobenius_fixed_E8_of_bijective {K L : Type} [Field K] [Finite K]
    [Field L] [Algebra K L] (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hbij : Function.Bijective Fr) {g : ModGL Tag.E8 L} (hg : g ∈ adjointGroup Tag.E8 L)
    (hfix : Units.map (entrywiseHom Fr) g = g) :
    g ∈ (adjointGroup Tag.E8 K).map (baseChangeGL (algebraMap K L)) := by
  set σ : L ≃+* L := RingEquiv.ofBijective Fr hbij
  have hσ : σ.toRingHom = Fr := RingHom.ext fun _ => rfl
  have hσfix : ∀ c, σ c = c → c ∈ Set.range (algebraMap K L) := fun c hc =>
    CFSG.RankThree.PartOne.KE.mem_range_algebraMap_of_pow_card_eq (by rw [← hFr]; exact hc)
  have hg' : g ∈ entrywiseFixedGroup Tag.E8 σ := ⟨hg, by
    change Units.map (entrywiseHom σ.toRingHom) g = g
    rw [hσ]
    exact hfix⟩
  obtain ⟨h, hh, j, hj, rfl⟩ := mem_mul_of_mem_entrywiseFixedGroup hg'
  obtain ⟨hhT, -, hhF⟩ := hh
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hhT
  have hbσ : (fun i => Units.map σ.toRingHom.toMonoidHom (b i)) = b := by
    apply rootDiagUnit_injective (τ := Tag.E8) (K := L)
    rw [← baseChangeGL_rootDiagUnit, ← units_map_entrywiseHom_eq_baseChangeGL]
    exact hhF
  have hbK : ∀ i, ∃ c : Kˣ, Units.map (algebraMap K L).toMonoidHom c = b i := by
    intro i
    obtain ⟨c, hc⟩ := hσfix (b i : L) (by
      have := congrArg Units.val (congrFun hbσ i)
      simpa using this)
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [map_zero] at hc
      exact (b i).ne_zero hc.symm
    exact ⟨Units.mk0 c hc0, Units.ext (by simpa using hc)⟩
  choose bK hbK using hbK
  have hjK : j ∈ (adjointGroup Tag.E8 K).map (baseChangeGL (algebraMap K L)) := by
    rw [fixedFieldImage_eq_closure] at hj
    refine (Subgroup.closure_le _).2 ?_ hj
    rintro _ ⟨i, c, hc, rfl | rfl⟩
    · obtain ⟨c', rfl⟩ := hσfix c hc
      exact ⟨xUnit Tag.E8 K i c', xUnit_mem_adjointGroup i c', baseChangeGL_xUnit _ i c'⟩
    · obtain ⟨c', rfl⟩ := hσfix c hc
      exact ⟨yUnit Tag.E8 K i c', yUnit_mem_adjointGroup i c', baseChangeGL_yUnit _ i c'⟩
  obtain ⟨jK, hjKC, rfl⟩ := hjK
  have hb : rootDiagUnit Tag.E8 b = baseChangeGL (algebraMap K L) (rootDiagUnit Tag.E8 bK) := by
    rw [baseChangeGL_rootDiagUnit]
    congr 1
    funext i
    exact (hbK i).symm
  rw [hb]
  exact ⟨rootDiagUnit Tag.E8 bK * jK, mul_mem
    (CFSG.StandardType.RecipeExcLang.rootDiagUnit_mem_adjointGroup_of_det_one
      (Or.inr (Or.inr rfl)) bK) hjKC, map_mul _ _ _⟩

end Descent

section Lang


theorem lang_centralizer_E8_five {Ω : Type} [Field Ω] [IsAlgClosed Ω] {p : ℕ} [Fact p.Prime]
    [CharP Ω p] (hp5 : p ≠ 5) {f : ℕ} (hf : 1 ≤ f) (ζ : Ωˣ) (hζ : orderOf ζ = 5)
    (Dz Q : ModGL Tag.E8 Ω) (hQ : Q ∈ adjointGroup Tag.E8 Ω) {s : ℕ} (hs : ¬ 5 ∣ s)
    (hDz : Dz ∈ adjointGroup Tag.E8 Ω)
    (hFDz : entrywiseFrobGL Tag.E8 Ω p f Dz = Dz * Q)
    (hQd : Q * rootDiagUnit Tag.E8 (Pi.mulSingle 4 ζ) * Q⁻¹ =
      rootDiagUnit Tag.E8 (Pi.mulSingle 4 ζ) ^ s) :
    ∀ c ∈ adjointGroup Tag.E8 Ω,
      c * (Dz * rootDiagUnit Tag.E8 (Pi.mulSingle 4 ζ) * Dz⁻¹) =
        (Dz * rootDiagUnit Tag.E8 (Pi.mulSingle 4 ζ) * Dz⁻¹) * c →
      ∃ y ∈ adjointGroup Tag.E8 Ω,
        y * (Dz * rootDiagUnit Tag.E8 (Pi.mulSingle 4 ζ) * Dz⁻¹) =
          (Dz * rootDiagUnit Tag.E8 (Pi.mulSingle 4 ζ) * Dz⁻¹) * y ∧
        y⁻¹ * entrywiseFrobGL Tag.E8 Ω p f y = c := by
  intro c hc hcz
  have h5 : ∀ i : Fin Tag.E8.rank,
      (Pi.mulSingle 4 ζ : Fin Tag.E8.rank → Ωˣ) i ^ 5 = 1 := by
    intro i
    by_cases hi : i = 4
    · subst hi
      rw [Pi.mulSingle_eq_same, ← hζ, pow_orderOf_eq_one]
    · rw [Pi.mulSingle_eq_of_ne hi, one_pow]
  have hc₀ : Dz⁻¹ * c * Dz ∈ toralCentralizer Tag.E8 Ω (Pi.mulSingle 4 ζ) := by
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem (inv_mem hDz) hc) hDz, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (Dz⁻¹ * c * Dz) * rootDiagUnit Tag.E8 (Pi.mulSingle 4 ζ)
        = Dz⁻¹ * (c * (Dz * rootDiagUnit Tag.E8 (Pi.mulSingle 4 ζ) * Dz⁻¹)) * Dz := by group
      _ = Dz⁻¹ * ((Dz * rootDiagUnit Tag.E8 (Pi.mulSingle 4 ζ) * Dz⁻¹) * c) * Dz := by rw [hcz]
      _ = rootDiagUnit Tag.E8 (Pi.mulSingle 4 ζ) * (Dz⁻¹ * c * Dz) := by group
  obtain ⟨y₀, hy₀, hy₀eq⟩ :=
    (toral_centralizer_Lang_E8_five p Ω hp5 _ h5 f hf hQ hs hQd) (Dz⁻¹ * c * Dz) hc₀
  rw [frobTwistGL_apply] at hy₀eq
  have hy₀mem : y₀ ∈ adjointGroup Tag.E8 Ω := (Subgroup.mem_inf.1 hy₀).1
  have hy₀comm : y₀ * rootDiagUnit Tag.E8 (Pi.mulSingle 4 ζ) =
      rootDiagUnit Tag.E8 (Pi.mulSingle 4 ζ) * y₀ :=
    Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hy₀).2
  refine ⟨Dz * y₀ * Dz⁻¹, mul_mem (mul_mem hDz hy₀mem) (inv_mem hDz), ?_, ?_⟩
  · calc (Dz * y₀ * Dz⁻¹) * (Dz * rootDiagUnit Tag.E8 (Pi.mulSingle 4 ζ) * Dz⁻¹)
        = Dz * (y₀ * rootDiagUnit Tag.E8 (Pi.mulSingle 4 ζ)) * Dz⁻¹ := by group
      _ = Dz * (rootDiagUnit Tag.E8 (Pi.mulSingle 4 ζ) * y₀) * Dz⁻¹ := by rw [hy₀comm]
      _ = (Dz * rootDiagUnit Tag.E8 (Pi.mulSingle 4 ζ) * Dz⁻¹) * (Dz * y₀ * Dz⁻¹) := by group
  · have hFy : entrywiseFrobGL Tag.E8 Ω p f (Dz * y₀ * Dz⁻¹) =
        Dz * (Q * entrywiseFrobGL Tag.E8 Ω p f y₀ * Q⁻¹) * Dz⁻¹ := by
      rw [map_mul, map_mul, map_inv, hFDz]
      group
    rw [hFy]
    calc (Dz * y₀ * Dz⁻¹)⁻¹ * (Dz * (Q * entrywiseFrobGL Tag.E8 Ω p f y₀ * Q⁻¹) * Dz⁻¹)
        = Dz * (y₀⁻¹ * (Q * entrywiseFrobGL Tag.E8 Ω p f y₀ * Q⁻¹)) * Dz⁻¹ := by group
      _ = Dz * (Dz⁻¹ * c * Dz) * Dz⁻¹ := by rw [hy₀eq]
      _ = c := by group

theorem lang_core_five {K : Type} [Field K] [Finite K] {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    [Algebra K Ω] {p f : ℕ} [Fact p.Prime] [CharP Ω p] (hp5 : p ≠ 5) (hf : 1 ≤ f)
    (hq : Nat.card K = p ^ f) (ζ : Ωˣ) (hζ : orderOf ζ = 5)
    (Dz Q : ModGL Tag.E8 Ω) (hDz : Dz ∈ adjointGroup Tag.E8 Ω) (hQ : Q ∈ adjointGroup Tag.E8 Ω)
    {s : ℕ} (hs : ¬ 5 ∣ s) (hFDz : entrywiseFrobGL Tag.E8 Ω p f Dz = Dz * Q)
    (hQd : Q * rootDiagUnit Tag.E8 (Pi.mulSingle 4 ζ) * Q⁻¹ =
      rootDiagUnit Tag.E8 (Pi.mulSingle 4 ζ) ^ s)
    (z : adjointGroup Tag.E8 K)
    (hz : baseChangeGL (algebraMap K Ω) (z : ModGL Tag.E8 K) =
      Dz * rootDiagUnit Tag.E8 (Pi.mulSingle 4 ζ) * Dz⁻¹)
    (P : ModGL Tag.E8 Ω) (hP : P ∈ adjointGroup Tag.E8 Ω)
    (e₀ : adjointGroup Tag.E8 K) (a : Fin Tag.E8.rank → Ωˣ)
    (ha : rootDiagUnit Tag.E8 a = P⁻¹ * baseChangeGL (algebraMap K Ω) (e₀ : ModGL Tag.E8 K) * P)
    (u : WeylGroup Tag.E8)
    (hu : ∀ v : Fin Tag.E8.rank → ℤ, rootChar a (u • v) = rootChar (Pi.mulSingle 4 ζ) v) :
    ∃ g : adjointGroup Tag.E8 K, g * e₀ * g⁻¹ = z := by
  classical
  have hFr : ∀ c : Ω, iterateFrobenius Ω p f c = c ^ Nat.card K := fun c => by
    rw [iterateFrobenius_def, hq]
  have hbij : Function.Bijective (iterateFrobenius Ω p f) := by
    refine ⟨(iterateFrobenius Ω p f).injective, fun y => ?_⟩
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (pow_pos (Fact.out : p.Prime).pos f)
    exact ⟨x, by rw [iterateFrobenius_def]; exact hx⟩
  have hrat : ∀ w : ModGL Tag.E8 K,
      entrywiseFrobGL Tag.E8 Ω p f (baseChangeGL (algebraMap K Ω) w) =
        baseChangeGL (algebraMap K Ω) w :=
    fun w => CFSG.RankThree.PartOne.KE8F.baseChangeGL_frob_fixed (iterateFrobenius Ω p f) hFr w
  have hFmem : ∀ g ∈ adjointGroup Tag.E8 Ω,
      entrywiseFrobGL Tag.E8 Ω p f g ∈ adjointGroup Tag.E8 Ω := fun g hg =>
    entrywiseFrobGL_mem p f hg
  have hnconj : rootDiagUnit Tag.E8 a = canonicalRep (coxeterSystem Tag.E8) Ω u *
      rootDiagUnit Tag.E8 (Pi.mulSingle 4 ζ) * (canonicalRep (coxeterSystem Tag.E8) Ω u)⁻¹ :=
    (rootDiagUnit_eq_conj_canonicalRep_iff a _ u).2 hu
  have hnmem : canonicalRep (coxeterSystem Tag.E8) Ω u ∈ adjointGroup Tag.E8 Ω :=
    canonicalRep_mem_adjointGroup (τ := Tag.E8) (coxeterSystem Tag.E8) Ω u
  have hē : baseChangeGL (algebraMap K Ω) (e₀ : ModGL Tag.E8 K) =
      P * rootDiagUnit Tag.E8 a * P⁻¹ := by
    rw [ha]
    group
  have hconj' : baseChangeGL (algebraMap K Ω) (e₀ : ModGL Tag.E8 K) =
      (P * canonicalRep (coxeterSystem Tag.E8) Ω u * Dz⁻¹) *
        baseChangeGL (algebraMap K Ω) (z : ModGL Tag.E8 K) *
        (P * canonicalRep (coxeterSystem Tag.E8) Ω u * Dz⁻¹)⁻¹ := by
    rw [hz, hē, hnconj]
    group
  have hh : P * canonicalRep (coxeterSystem Tag.E8) Ω u * Dz⁻¹ ∈ adjointGroup Tag.E8 Ω :=
    mul_mem (mul_mem hP hnmem) (inv_mem hDz)
  have hlang : ∀ c ∈ adjointGroup Tag.E8 Ω,
      c * baseChangeGL (algebraMap K Ω) (z : ModGL Tag.E8 K) =
        baseChangeGL (algebraMap K Ω) (z : ModGL Tag.E8 K) * c →
      ∃ y ∈ adjointGroup Tag.E8 Ω,
        y * baseChangeGL (algebraMap K Ω) (z : ModGL Tag.E8 K) =
          baseChangeGL (algebraMap K Ω) (z : ModGL Tag.E8 K) * y ∧
        y⁻¹ * entrywiseFrobGL Tag.E8 Ω p f y = c := by
    intro c hc hcz
    rw [hz] at hcz ⊢
    exact lang_centralizer_E8_five hp5 hf ζ hζ Dz Q hQ hs hDz hFDz hQd c hc hcz
  obtain ⟨g, hgG, hgF, hgconj⟩ := lang_fix (entrywiseFrobGL Tag.E8 Ω p f) (adjointGroup Tag.E8 Ω)
    (baseChangeGL (algebraMap K Ω) (z : ModGL Tag.E8 K))
    (baseChangeGL (algebraMap K Ω) (e₀ : ModGL Tag.E8 K))
    (P * canonicalRep (coxeterSystem Tag.E8) Ω u * Dz⁻¹)
    hh (hFmem _ hh) (hrat _) (hrat _) hconj' hlang
  have hgmem : g ∈ (adjointGroup Tag.E8 K).map (baseChangeGL (algebraMap K Ω)) :=
    mem_map_baseChange_of_frobenius_fixed_E8_of_bijective (iterateFrobenius Ω p f) hFr hbij
      hgG hgF
  obtain ⟨e₁, he₁, he₁g⟩ := Subgroup.mem_map.1 hgmem
  have hconjK : e₁ * (z : ModGL Tag.E8 K) * e₁⁻¹ = (e₀ : ModGL Tag.E8 K) := by
    apply baseChangeGL_injective (algebraMap K Ω)
    rw [map_mul, map_mul, map_inv, he₁g]
    exact hgconj
  refine ⟨⟨e₁⁻¹, inv_mem he₁⟩, Subtype.ext ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
  rw [← hconjK]
  group

end Lang

end CFSG.LieType.SeitzGeneration.ExcHigh
