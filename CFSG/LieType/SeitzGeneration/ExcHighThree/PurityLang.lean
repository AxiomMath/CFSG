module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.PurityOrbit
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCharCentralizer
public import CFSG.HardMathSupport.Lang.AnisoE6.E6InF4
public import CFSG.RankThree.PartOne.KE8F.BaseCase
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwistedFrame

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

section Generic

variable {G : Type*} [Group G]

theorem finite_of_le_of_finite {E H : Subgroup G} [Finite E] (h : H ≤ E) : Finite H :=
  Finite.of_injective (Set.inclusion (SetLike.coe_subset_coe.2 h))
    (Set.inclusion_injective _)

theorem plane_closure_of_ne_one {E : Subgroup G} (hE : Nat.card E = 3 ^ 2)
    (hexp : ∀ x ∈ E, x ^ 3 = 1) {e : G} (he : e ∈ E) (he1 : e ≠ 1) :
    ∃ e' ∈ E, E = Subgroup.closure {e, e'} := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hE]; norm_num)
  have hord : orderOf e = 3 := orderOf_eq_prime (hexp e he) he1
  have hcardZ : Nat.card (Subgroup.zpowers e) = 3 := by rw [Nat.card_zpowers, hord]
  have hex : ∃ e' ∈ E, e' ∉ Subgroup.zpowers e := by
    by_contra hcon
    have hle : E ≤ Subgroup.zpowers e := fun x hx => by
      by_contra h
      exact hcon ⟨x, hx, h⟩
    haveI : Finite (Subgroup.zpowers e) := finite_of_le_of_finite (Subgroup.zpowers_le.2 he)
    have := Subgroup.card_le_of_le hle
    rw [hE, hcardZ] at this
    norm_num at this
  obtain ⟨e', he'E, he'Z⟩ := hex
  set H := Subgroup.closure ({e, e'} : Set G) with hH
  have hHE : H ≤ E := (Subgroup.closure_le E).2 (by
    intro x hx
    rcases hx with rfl | rfl
    · exact he
    · exact he'E)
  haveI : Finite H := finite_of_le_of_finite hHE
  have hZH : Subgroup.zpowers e ≤ H := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.subset_closure (by simp)
  haveI : Finite (Subgroup.zpowers e) := finite_of_le_of_finite (Subgroup.zpowers_le.2 he)
  have he'H : e' ∈ H := Subgroup.subset_closure (by simp)
  have hne : Subgroup.zpowers e ≠ H := fun h => he'Z (h ▸ he'H)
  have hdvdE : Nat.card H ∣ 3 ^ 2 := hE ▸ Subgroup.card_dvd_of_le hHE
  have hdvdZ : 3 ∣ Nat.card H := by
    rw [← hcardZ]
    exact Subgroup.card_dvd_of_le hZH
  have hne3 : Nat.card H ≠ 3 := by
    intro h3
    apply hne
    apply Subgroup.eq_of_le_of_card_ge hZH
    rw [h3, hcardZ]
  have hH9 : Nat.card H = 9 := by
    have hmem : Nat.card H ∈ Nat.divisors 9 := Nat.mem_divisors.2 ⟨hdvdE, by norm_num⟩
    have hdiv : Nat.divisors 9 = {1, 3, 9} := by decide
    rw [hdiv] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h
    · omega
    · exact absurd h hne3
    · exact h
  refine ⟨e', he'E, ?_⟩
  exact (Subgroup.eq_of_le_of_card_ge hHE (by rw [hH9, hE]; norm_num)).symm

theorem pred_of_closure {S : Set G} (P : G → Prop) (h1 : P 1)
    (hmul : ∀ x y, P x → P y → P (x * y)) (hinv : ∀ x, P x → P x⁻¹)
    (hS : ∀ x ∈ S, P x) {x : G} (hx : x ∈ Subgroup.closure S) : P x := by
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => exact h1
  | mul x y _ _ hx hy => exact hmul x y hx hy
  | inv x _ hx => exact hinv x hx

theorem lang_fix (F : G →* G) (H : Subgroup G) (z ē h : G) (hh : h ∈ H) (hFh : F h ∈ H)
    (hz : F z = z) (hē : F ē = ē) (hconj : ē = h * z * h⁻¹)
    (hlang : ∀ c ∈ H, c * z = z * c → ∃ y ∈ H, y * z = z * y ∧ y⁻¹ * F y = c) :
    ∃ g ∈ H, F g = g ∧ g * z * g⁻¹ = ē := by
  have hFz' : F h * z * (F h)⁻¹ = ē := by
    rw [← hē, hconj, map_mul, map_mul, map_inv, hz]
  have hFhz : F h * z = ē * F h := by
    rw [← hFz']; group
  have hc : h⁻¹ * F h ∈ H := H.mul_mem (H.inv_mem hh) hFh
  have hcomm : (h⁻¹ * F h) * z = z * (h⁻¹ * F h) := by
    calc (h⁻¹ * F h) * z = h⁻¹ * (F h * z) := by group
      _ = h⁻¹ * (ē * F h) := by rw [hFhz]
      _ = h⁻¹ * (h * z * h⁻¹) * F h := by rw [hconj]; group
      _ = z * (h⁻¹ * F h) := by group
  obtain ⟨y, hyH, hyz, hy⟩ := hlang _ hc hcomm
  refine ⟨h * y⁻¹, H.mul_mem hh (H.inv_mem hyH), ?_, ?_⟩
  ·
    have hFy : F y = y * (h⁻¹ * F h) := by rw [← hy]; group
    rw [map_mul, map_inv, hFy, mul_inv_rev]
    group
  · have hyzc : y⁻¹ * z * y = z := by
      rw [mul_assoc, ← hyz, inv_mul_cancel_left]
    calc h * y⁻¹ * z * (h * y⁻¹)⁻¹ = h * (y⁻¹ * z * y) * h⁻¹ := by group
      _ = h * z * h⁻¹ := by rw [hyzc]
      _ = ē := hconj.symm

end Generic


section Lang

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.Tables.T1b
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE
  CFSG.RankThree.Chevalley CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

set_option linter.unusedSectionVars false


theorem zpow_sum_finset {G : Type*} [CommGroup G] {ι : Type*} (s : Finset ι) (f : ι → ℤ) (a : G) :
    a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, zpow_add, ih]

theorem rootChar_pow_exponents {Ω : Type} [Field Ω] {τ : Tag} (ω : Ωˣ) (k : Fin τ.rank → ℕ)
    (v : Fin τ.rank → ℤ) :
    rootChar (fun i => ω ^ k i) v = ω ^ (∑ i, v i * (k i : ℤ)) := by
  unfold rootChar
  rw [zpow_sum_finset]
  refine Finset.prod_congr rfl fun i _ => ?_
  dsimp only
  rw [← zpow_natCast ω (k i), ← zpow_mul, mul_comm]

theorem exists_pow_of_cube {Ω : Type} [Field Ω] (ω : Ωˣ) (hω : orderOf ω = 3) (x : Ωˣ)
    (hx : x ^ 3 = 1) : ∃ k : ℕ, k < 3 ∧ x = ω ^ k := by
  have hprim : IsPrimitiveRoot (ω : Ω) 3 := by
    have h := IsPrimitiveRoot.orderOf (ω : Ω)
    rwa [orderOf_units, hω] at h
  obtain ⟨k, hk, hkx⟩ := hprim.eq_pow_of_pow_eq_one (ξ := (x : Ω)) (by
    rw [← Units.val_pow_eq_pow_val, hx, Units.val_one])
  exact ⟨k, hk, Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hkx.symm)⟩

theorem rootChar_exp_eq_one_iff {Ω : Type} [Field Ω] {τ : Tag} (ω : Ωˣ) (hω : orderOf ω = 3)
    (k : Fin τ.rank → ℕ) (v : Fin τ.rank → ℤ) :
    rootChar (fun i => ω ^ k i) v = 1 ↔ (3 : ℤ) ∣ ∑ i, v i * (k i : ℤ) := by
  rw [rootChar_pow_exponents, ← orderOf_dvd_iff_zpow_eq_one, hω]
  norm_cast

theorem weylAct_eq_of_row {Ω : Type} [Field Ω] (ω : Ωˣ) (hω : orderOf ω = 3)
    (m : List (Fin Tag.F4.rank)) (k : Fin Tag.F4.rank → ℕ)
    (hrow : ∀ i : Fin Tag.F4.rank, wordMat Tag.F4 m 1 i % 3 = ((k i : ℕ) : ℤ) % 3) :
    CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct (((coxeterSystem Tag.F4).wordProd m)⁻¹) (Pi.mulSingle (1 : Fin Tag.F4.rank) ω) =
      fun i => ω ^ k i := by
  funext i
  unfold CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct
  rw [inv_inv, wordProd_smul_eq_wordMat_mulVec, rootChar_mulSingle_eq_zpow]
  have hM : (Matrix.mulVec (wordMat Tag.F4 m) (Pi.single i 1)) 1 = wordMat Tag.F4 m 1 i := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  show ω ^ (Matrix.mulVec (wordMat Tag.F4 m) (Pi.single i 1)) 1 = ω ^ k i
  rw [hM]
  exact (zpow_eq_of_emod hω (hrow i)).trans (zpow_natCast ω (k i))

theorem weylAct_twice_threeA {Ω : Type} [Field Ω] (ω : Ωˣ) (hω : orderOf ω = 3) :
    CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct (τ := TwClass.f4Six.tag) (K := Ω) TwClass.f4Six.w
        (Pi.mulSingle (⟨1, by decide⟩ : Fin TwClass.f4Six.tag.rank) ω) =
      (Pi.mulSingle (⟨1, by decide⟩ : Fin TwClass.f4Six.tag.rank) ω) ^ 2 := by
  funext i
  unfold CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct
  rw [Pi.pow_apply, rootChar_mulSingle_eq_zpow]
  have hm := f4Six_row' i
  by_cases hi : i = (⟨1, by decide⟩ : Fin TwClass.f4Six.tag.rank)
  · rw [if_pos hi] at hm
    rw [Pi.mulSingle_apply, if_pos hi, zpow_eq_of_emod hω (n := 2) (hm.trans (by norm_num)),
      zpow_ofNat]
  · rw [if_neg hi] at hm
    rw [Pi.mulSingle_apply, if_neg hi, one_pow, zpow_eq_of_emod hω (n := 0) (hm.trans (by norm_num)),
      zpow_zero]

theorem lang_centralizer {Ω : Type} [Field Ω] [IsAlgClosed Ω] {p : ℕ} [Fact p.Prime]
    [CharP Ω p] (hp3 : p ≠ 3) {f : ℕ} (hf : 1 ≤ f) (ω : Ωˣ) (hω : orderOf ω = 3)
    (Dz Q : ModGL Tag.F4 Ω) (hQ : Q ∈ adjointGroup Tag.F4 Ω) {s : ℕ} (hs : ¬ 3 ∣ s)
    (hDz : Dz ∈ adjointGroup Tag.F4 Ω)
    (hFDz : entrywiseFrobGL Tag.F4 Ω p f Dz = Dz * Q)
    (hQd : Q * rootDiagUnit Tag.F4 (Pi.mulSingle 1 ω) * Q⁻¹ =
      rootDiagUnit Tag.F4 (Pi.mulSingle 1 ω) ^ s) :
    ∀ c ∈ adjointGroup Tag.F4 Ω,
      c * (Dz * rootDiagUnit Tag.F4 (Pi.mulSingle 1 ω) * Dz⁻¹) =
        (Dz * rootDiagUnit Tag.F4 (Pi.mulSingle 1 ω) * Dz⁻¹) * c →
      ∃ y ∈ adjointGroup Tag.F4 Ω,
        y * (Dz * rootDiagUnit Tag.F4 (Pi.mulSingle 1 ω) * Dz⁻¹) =
          (Dz * rootDiagUnit Tag.F4 (Pi.mulSingle 1 ω) * Dz⁻¹) * y ∧
        y⁻¹ * entrywiseFrobGL Tag.F4 Ω p f y = c := by
  intro c hc hcz
  have h3 : ∀ i : Fin Tag.F4.rank, (Pi.mulSingle (1 : Fin Tag.F4.rank) ω : Fin Tag.F4.rank → Ωˣ) i ^ 3 = 1 := by
    intro i
    by_cases hi : i = 1
    · subst hi
      rw [Pi.mulSingle_eq_same, ← hω, pow_orderOf_eq_one]
    · rw [Pi.mulSingle_eq_of_ne hi, one_pow]
  have hc₀ : Dz⁻¹ * c * Dz ∈ toralCentralizer Tag.F4 Ω (Pi.mulSingle (1 : Fin Tag.F4.rank) ω) := by
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem (inv_mem hDz) hc) hDz, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (Dz⁻¹ * c * Dz) * rootDiagUnit Tag.F4 (Pi.mulSingle 1 ω)
        = Dz⁻¹ * (c * (Dz * rootDiagUnit Tag.F4 (Pi.mulSingle 1 ω) * Dz⁻¹)) * Dz := by group
      _ = Dz⁻¹ * ((Dz * rootDiagUnit Tag.F4 (Pi.mulSingle 1 ω) * Dz⁻¹) * c) * Dz := by rw [hcz]
      _ = rootDiagUnit Tag.F4 (Pi.mulSingle 1 ω) * (Dz⁻¹ * c * Dz) := by group
  obtain ⟨y₀, hy₀, hy₀eq⟩ :=
    (toral_centralizer_Lang_F4_three p Ω hp3 _ h3 f hf hQ hs hQd) (Dz⁻¹ * c * Dz) hc₀
  rw [frobTwistGL_apply] at hy₀eq
  have hy₀mem : y₀ ∈ adjointGroup Tag.F4 Ω := (Subgroup.mem_inf.1 hy₀).1
  have hy₀comm : y₀ * rootDiagUnit Tag.F4 (Pi.mulSingle 1 ω) =
      rootDiagUnit Tag.F4 (Pi.mulSingle 1 ω) * y₀ :=
    Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hy₀).2
  refine ⟨Dz * y₀ * Dz⁻¹, mul_mem (mul_mem hDz hy₀mem) (inv_mem hDz), ?_, ?_⟩
  · calc (Dz * y₀ * Dz⁻¹) * (Dz * rootDiagUnit Tag.F4 (Pi.mulSingle 1 ω) * Dz⁻¹)
        = Dz * (y₀ * rootDiagUnit Tag.F4 (Pi.mulSingle 1 ω)) * Dz⁻¹ := by group
      _ = Dz * (rootDiagUnit Tag.F4 (Pi.mulSingle 1 ω) * y₀) * Dz⁻¹ := by rw [hy₀comm]
      _ = (Dz * rootDiagUnit Tag.F4 (Pi.mulSingle 1 ω) * Dz⁻¹) * (Dz * y₀ * Dz⁻¹) := by group
  · have hFy : entrywiseFrobGL Tag.F4 Ω p f (Dz * y₀ * Dz⁻¹) =
        Dz * (Q * entrywiseFrobGL Tag.F4 Ω p f y₀ * Q⁻¹) * Dz⁻¹ := by
      rw [map_mul, map_mul, map_inv, hFDz]
      group
    rw [hFy]
    calc (Dz * y₀ * Dz⁻¹)⁻¹ * (Dz * (Q * entrywiseFrobGL Tag.F4 Ω p f y₀ * Q⁻¹) * Dz⁻¹)
        = Dz * (y₀⁻¹ * (Q * entrywiseFrobGL Tag.F4 Ω p f y₀ * Q⁻¹)) * Dz⁻¹ := by group
      _ = Dz * (Dz⁻¹ * c * Dz) * Dz⁻¹ := by rw [hy₀eq]
      _ = c := by group

theorem rootDiagUnit_mul_eq {Ω : Type} [Field Ω] (a b : Fin Tag.F4.rank → Ωˣ) :
    rootDiagUnit Tag.F4 (a * b) = rootDiagUnit Tag.F4 a * rootDiagUnit Tag.F4 b :=
  map_mul (rootDiagUnitHom Tag.F4 Ω) a b

theorem rootDiagUnit_inv_eq {Ω : Type} [Field Ω] (a : Fin Tag.F4.rank → Ωˣ) :
    rootDiagUnit Tag.F4 a⁻¹ = (rootDiagUnit Tag.F4 a)⁻¹ :=
  map_inv (rootDiagUnitHom Tag.F4 Ω) a

theorem lang_core_three {K : Type} [Field K] [Finite K] {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    [Algebra K Ω] {p f : ℕ} [Fact p.Prime] [CharP Ω p] (hp3 : p ≠ 3) (hf : 1 ≤ f)
    (hq : Nat.card K = p ^ f) (ω : Ωˣ) (hω : orderOf ω = 3)
    (Dz Q : ModGL Tag.F4 Ω) (hDz : Dz ∈ adjointGroup Tag.F4 Ω) (hQ : Q ∈ adjointGroup Tag.F4 Ω)
    {s : ℕ} (hs : ¬ 3 ∣ s)
    (hFDz : entrywiseFrobGL Tag.F4 Ω p f Dz = Dz * Q)
    (hQd : Q * rootDiagUnit Tag.F4 (Pi.mulSingle 1 ω) * Q⁻¹ =
      rootDiagUnit Tag.F4 (Pi.mulSingle 1 ω) ^ s)
    (z : adjointGroup Tag.F4 K)
    (hz : baseChangeGL (algebraMap K Ω) (z : ModGL Tag.F4 K) =
      Dz * rootDiagUnit Tag.F4 (Pi.mulSingle 1 ω) * Dz⁻¹)
    (E₀ : Subgroup (adjointGroup Tag.F4 K)) (hE9 : Nat.card E₀ = 3 ^ 2)
    (hE3 : ∀ x ∈ E₀, x ^ 3 = 1)
    (P : ModGL Tag.F4 Ω) (hP : P ∈ adjointGroup Tag.F4 Ω)
    (hT : ∀ x ∈ E₀, ∃ a : Fin Tag.F4.rank → Ωˣ, rootDiagUnit Tag.F4 a =
      P⁻¹ * baseChangeGL (algebraMap K Ω) (x : ModGL Tag.F4 K) * P)
    (hR : ∀ α : Fin Tag.F4.rank → ℤ, IsRoot Tag.F4 α → ∃ x ∈ E₀, ∀ a : Fin Tag.F4.rank → Ωˣ,
      rootDiagUnit Tag.F4 a = P⁻¹ * baseChangeGL (algebraMap K Ω) (x : ModGL Tag.F4 K) * P →
        rootChar a α ≠ 1)
    (e₀ : adjointGroup Tag.F4 K) (he₀ : e₀ ∈ E₀) (he1 : e₀ ≠ 1) :
    ∃ g : adjointGroup Tag.F4 K, g * e₀ * g⁻¹ = z := by
  classical
  have hFr : ∀ c : Ω, iterateFrobenius Ω p f c = c ^ Nat.card K := fun c => by
    rw [iterateFrobenius_def, hq]
  have hbij : Function.Bijective (iterateFrobenius Ω p f) := by
    refine ⟨(iterateFrobenius Ω p f).injective, fun y => ?_⟩
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (pow_pos (Fact.out : p.Prime).pos f)
    exact ⟨x, by rw [iterateFrobenius_def]; exact hx⟩
  have hrat : ∀ w : ModGL Tag.F4 K,
      entrywiseFrobGL Tag.F4 Ω p f (baseChangeGL (algebraMap K Ω) w) =
        baseChangeGL (algebraMap K Ω) w :=
    fun w => CFSG.RankThree.PartOne.KE8F.baseChangeGL_frob_fixed (iterateFrobenius Ω p f) hFr w
  have hFmem : ∀ g ∈ adjointGroup Tag.F4 Ω,
      entrywiseFrobGL Tag.F4 Ω p f g ∈ adjointGroup Tag.F4 Ω := by
    intro g hg
    have h := CFSG.HardMathSupport.Lang.AnisoE6.baseChangeGL_mem_adjointGroup_of_mem (iterateFrobenius Ω p f) hg
    rwa [← units_map_entrywiseHom_eq_baseChangeGL_self] at h
  have hdiag : ∀ x ∈ E₀, ∃ a : Fin Tag.F4.rank → Ωˣ, ∃ k : Fin Tag.F4.rank → ℕ,
      rootDiagUnit Tag.F4 a = P⁻¹ * baseChangeGL (algebraMap K Ω) (x : ModGL Tag.F4 K) * P ∧
        (∀ i, k i < 3) ∧ ∀ i, a i = ω ^ k i := by
    intro x hx
    obtain ⟨a, ha⟩ := hT x hx
    have hx3 : (baseChangeGL (algebraMap K Ω) (x : ModGL Tag.F4 K)) ^ 3 = 1 := by
      rw [← map_pow, ← Subgroup.coe_pow, hE3 x hx, Subgroup.coe_one, map_one]
    have hconj3 : (P⁻¹ * baseChangeGL (algebraMap K Ω) (x : ModGL Tag.F4 K) * P) ^ 3 = 1 := by
      have h := (show (P⁻¹ * baseChangeGL (algebraMap K Ω) (x : ModGL Tag.F4 K) * P) ^ 3 =
          P⁻¹ * (baseChangeGL (algebraMap K Ω) (x : ModGL Tag.F4 K)) ^ 3 * P by
        simp only [pow_succ, pow_zero, one_mul]; group)
      rw [h, hx3]; group
    have hpow : rootDiagUnit Tag.F4 (a ^ 3) = 1 := by
      have h1 : rootDiagUnit Tag.F4 (a ^ 3) = rootDiagUnit Tag.F4 a ^ 3 := by
        show rootDiagUnitHom Tag.F4 Ω (a ^ 3) = (rootDiagUnitHom Tag.F4 Ω a) ^ 3
        rw [map_pow]
      rw [h1, ha, hconj3]
    have ha3 : a ^ 3 = 1 := rootDiagUnit_injective (hpow.trans (rootDiagUnit_one (τ := Tag.F4)
      (K := Ω)).symm)
    have hcube : ∀ i, a i ^ 3 = 1 := fun i => by
      have := congrFun ha3 i
      simpa using this
    choose k hk hka using fun i => exists_pow_of_cube ω hω (a i) (hcube i)
    exact ⟨a, k, ha, hk, hka⟩
  obtain ⟨e', he'E, hgen⟩ := plane_closure_of_ne_one hE9 hE3 he₀ he1
  have hpair : ∀ α : Fin Tag.F4.rank → ℤ, IsRoot Tag.F4 α →
      ¬ ((∃ a : Fin Tag.F4.rank → Ωˣ, rootDiagUnit Tag.F4 a =
            P⁻¹ * baseChangeGL (algebraMap K Ω) (e₀ : ModGL Tag.F4 K) * P ∧ rootChar a α = 1) ∧
          (∃ a : Fin Tag.F4.rank → Ωˣ, rootDiagUnit Tag.F4 a =
            P⁻¹ * baseChangeGL (algebraMap K Ω) (e' : ModGL Tag.F4 K) * P ∧ rootChar a α = 1)) := by
    rintro α hα ⟨⟨a₁, ha₁, hc₁⟩, ⟨a₂, ha₂, hc₂⟩⟩
    obtain ⟨x, hxE, hxa⟩ := hR α hα
    have hall : ∀ y : adjointGroup Tag.F4 K, y ∈ Subgroup.closure ({e₀, e'} : Set (adjointGroup Tag.F4 K)) →
        ∃ a : Fin Tag.F4.rank → Ωˣ, rootDiagUnit Tag.F4 a =
          P⁻¹ * baseChangeGL (algebraMap K Ω) (y : ModGL Tag.F4 K) * P ∧ rootChar a α = 1 := by
      intro y hy
      refine pred_of_closure (fun y : adjointGroup Tag.F4 K => ∃ a : Fin Tag.F4.rank → Ωˣ,
          rootDiagUnit Tag.F4 a = P⁻¹ * baseChangeGL (algebraMap K Ω) (y : ModGL Tag.F4 K) * P ∧
            rootChar a α = 1) ?_ ?_ ?_ ?_ hy
      · refine ⟨1, ?_, ?_⟩
        · rw [rootDiagUnit_one, Subgroup.coe_one, map_one]; group
        · exact CFSG.RankThree.PartOne.KE.CTTorus.rootChar_one α
      · rintro x y ⟨a, ha, hca⟩ ⟨b, hb, hcb⟩
        refine ⟨a * b, ?_, ?_⟩
        · rw [rootDiagUnit_mul_eq, ha, hb, Subgroup.coe_mul, map_mul]; group
        · rw [CFSG.RankThree.PartOne.KE.CTTorus.rootChar_mul, hca, hcb, one_mul]
      · rintro x ⟨a, ha, hca⟩
        refine ⟨a⁻¹, ?_, ?_⟩
        · rw [rootDiagUnit_inv_eq, ha, Subgroup.coe_inv, map_inv]; group
        · have h := CFSG.RankThree.PartOne.KE.CTTorus.rootChar_mul a⁻¹ a α
          rw [inv_mul_cancel, CFSG.RankThree.PartOne.KE.CTTorus.rootChar_one, hca, mul_one] at h
          exact h.symm
      · intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact ⟨a₁, ha₁, hc₁⟩
        · exact ⟨a₂, ha₂, hc₂⟩
    obtain ⟨a, ha, hca⟩ := hall x (by rw [← hgen]; exact hxE)
    exact hxa a ha hca
  obtain ⟨a₁, k₁, ha₁, hk₁, hka₁⟩ := hdiag e₀ he₀
  obtain ⟨a₂, k₂, ha₂, hk₂, hka₂⟩ := hdiag e' he'E
  have hkill₁ : ∀ α : Fin Tag.F4.rank → ℤ,
      rootChar a₁ α = 1 ↔ (3 : ℤ) ∣ ∑ i, α i * (k₁ i : ℤ) := by
    intro α
    rw [show a₁ = fun i => ω ^ k₁ i from funext hka₁, rootChar_exp_eq_one_iff ω hω]
  have hkill₂ : ∀ α : Fin Tag.F4.rank → ℤ,
      rootChar a₂ α = 1 ↔ (3 : ℤ) ∣ ∑ i, α i * (k₂ i : ℤ) := by
    intro α
    rw [show a₂ = fun i => ω ^ k₂ i from funext hka₂, rootChar_exp_eq_one_iff ω hω]
  have hreg : ∀ a ∈ f4ArtifactRoots, ¬ (rootDot a (List.ofFn k₁) % 3 = 0 ∧
      rootDot a (List.ofFn k₂) % 3 = 0) := by
    intro a ha ⟨h1, h2⟩
    have hl : a.length = 4 := length_of_mem_artifactRoots (τ := Tag.F4) ha
    obtain ⟨x0, x1, x2, x3, rfl⟩ : ∃ x0 x1 x2 x3 : ℤ, a = [x0, x1, x2, x3] := by
      match a, hl with
      | [x0, x1, x2, x3], _ => exact ⟨x0, x1, x2, x3, rfl⟩
    obtain ⟨α, hofn⟩ : ∃ α : Fin Tag.F4.rank → ℤ, List.ofFn α = [x0, x1, x2, x3] :=
      ⟨fun i => [x0, x1, x2, x3].getD i.val 0, rfl⟩
    have hα : IsRoot Tag.F4 α :=
      (CFSG.Blueprint.Chevalley.isRoot_iff_mem_artifactRoots (τ := Tag.F4)).2 (by rw [hofn]; exact ha)
    have hdot : ∀ v : Fin Tag.F4.rank → ℕ, rootDot [x0, x1, x2, x3] (List.ofFn v) =
        ∑ i, α i * (v i : ℤ) := by
      intro v
      have h := rootDot_ofFn Tag.F4.rank α v
      rw [hofn] at h
      exact h
    rw [hdot] at h1 h2
    have h1' : (3 : ℤ) ∣ ∑ i, α i * (k₁ i : ℤ) := Int.dvd_of_emod_eq_zero h1
    have h2' : (3 : ℤ) ∣ ∑ i, α i * (k₂ i : ℤ) := Int.dvd_of_emod_eq_zero h2
    exact hpair α hα ⟨⟨a₁, ha₁, (hkill₁ α).2 h1'⟩, ⟨a₂, ha₂, (hkill₂ α).2 h2'⟩⟩
  have hv3 : ∀ x ∈ List.ofFn k₁, x < 3 := fun x hx => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    exact hk₁ i
  have hu3 : ∀ x ∈ List.ofFn k₂, x < 3 := fun x hx => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    exact hk₂ i
  have hv0 : ∃ x ∈ List.ofFn k₁, x ≠ 0 := by
    by_contra hcon
    apply he1
    have hk0 : ∀ i, k₁ i = 0 := fun i => by
      by_contra h
      exact hcon ⟨k₁ i, List.mem_ofFn.2 ⟨i, rfl⟩, h⟩
    have ha1 : a₁ = 1 := by
      funext i
      rw [hka₁ i, hk0 i, pow_zero, Pi.one_apply]
    have hX : baseChangeGL (algebraMap K Ω) (e₀ : ModGL Tag.F4 K) = 1 := by
      have h1 : P⁻¹ * baseChangeGL (algebraMap K Ω) (e₀ : ModGL Tag.F4 K) * P = 1 := by
        rw [← ha₁, ha1, rootDiagUnit_one]
      calc baseChangeGL (algebraMap K Ω) (e₀ : ModGL Tag.F4 K)
          = P * (P⁻¹ * baseChangeGL (algebraMap K Ω) (e₀ : ModGL Tag.F4 K) * P) * P⁻¹ := by group
        _ = 1 := by rw [h1]; group
    have h1K : (e₀ : ModGL Tag.F4 K) = 1 := by
      apply baseChangeGL_injective (algebraMap K Ω)
      rw [hX, map_one]
    exact Subtype.ext (by rw [Subgroup.coe_one]; exact h1K)
  have hcount : (f4ArtifactRoots.filter fun r => rootDot r (List.ofFn k₁) % 3 = 0).length = 12 :=
    f4_regular_threeA List.length_ofFn List.length_ofFn hv3 hu3 hv0 hreg
  obtain ⟨m, hm⟩ := f4_row_orbit k₁ hk₁ hcount
  have hw : CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct
      (((coxeterSystem Tag.F4).wordProd m)⁻¹) (Pi.mulSingle (1 : Fin Tag.F4.rank) ω) = a₁ := by
    rw [weylAct_eq_of_row ω hω m k₁ hm]
    funext i
    exact (hka₁ i).symm
  have hnconj : rootDiagUnit Tag.F4 a₁ =
      canonicalRep (coxeterSystem Tag.F4) Ω (((coxeterSystem Tag.F4).wordProd m)⁻¹) *
        rootDiagUnit Tag.F4 (Pi.mulSingle (1 : Fin Tag.F4.rank) ω) *
        (canonicalRep (coxeterSystem Tag.F4) Ω (((coxeterSystem Tag.F4).wordProd m)⁻¹))⁻¹ := by
    rw [CFSG.HardMathSupport.Timmesfeld.Tables.T1b.canonicalRep_conj_rootDiagUnit, hw]
  have hnmem : canonicalRep (coxeterSystem Tag.F4) Ω (((coxeterSystem Tag.F4).wordProd m)⁻¹) ∈
      adjointGroup Tag.F4 Ω :=
    canonicalRep_mem_adjointGroup (τ := Tag.F4) (coxeterSystem Tag.F4) Ω _
  have hē : baseChangeGL (algebraMap K Ω) (e₀ : ModGL Tag.F4 K) =
      P * (canonicalRep (coxeterSystem Tag.F4) Ω (((coxeterSystem Tag.F4).wordProd m)⁻¹) *
        rootDiagUnit Tag.F4 (Pi.mulSingle (1 : Fin Tag.F4.rank) ω) *
        (canonicalRep (coxeterSystem Tag.F4) Ω (((coxeterSystem Tag.F4).wordProd m)⁻¹))⁻¹) * P⁻¹ := by
    rw [← hnconj, ha₁]
    group
  have hconj' : baseChangeGL (algebraMap K Ω) (e₀ : ModGL Tag.F4 K) =
      (P * canonicalRep (coxeterSystem Tag.F4) Ω (((coxeterSystem Tag.F4).wordProd m)⁻¹) * Dz⁻¹) *
        baseChangeGL (algebraMap K Ω) (z : ModGL Tag.F4 K) *
        (P * canonicalRep (coxeterSystem Tag.F4) Ω (((coxeterSystem Tag.F4).wordProd m)⁻¹) * Dz⁻¹)⁻¹ := by
    rw [hz, hē]
    group
  have hh : P * canonicalRep (coxeterSystem Tag.F4) Ω (((coxeterSystem Tag.F4).wordProd m)⁻¹) *
      Dz⁻¹ ∈ adjointGroup Tag.F4 Ω :=
    mul_mem (mul_mem hP hnmem) (inv_mem hDz)
  have hlang : ∀ c ∈ adjointGroup Tag.F4 Ω,
      c * baseChangeGL (algebraMap K Ω) (z : ModGL Tag.F4 K) =
        baseChangeGL (algebraMap K Ω) (z : ModGL Tag.F4 K) * c →
      ∃ y ∈ adjointGroup Tag.F4 Ω,
        y * baseChangeGL (algebraMap K Ω) (z : ModGL Tag.F4 K) =
          baseChangeGL (algebraMap K Ω) (z : ModGL Tag.F4 K) * y ∧
        y⁻¹ * entrywiseFrobGL Tag.F4 Ω p f y = c := by
    intro c hc hcz
    rw [hz] at hcz ⊢
    exact lang_centralizer hp3 hf ω hω Dz Q hQ hs hDz hFDz hQd c hc hcz
  obtain ⟨g, hgG, hgF, hgconj⟩ := lang_fix (entrywiseFrobGL Tag.F4 Ω p f) (adjointGroup Tag.F4 Ω)
    (baseChangeGL (algebraMap K Ω) (z : ModGL Tag.F4 K))
    (baseChangeGL (algebraMap K Ω) (e₀ : ModGL Tag.F4 K))
    (P * canonicalRep (coxeterSystem Tag.F4) Ω (((coxeterSystem Tag.F4).wordProd m)⁻¹) * Dz⁻¹)
    hh (hFmem _ hh) (hrat _) (hrat _) hconj' hlang
  have hgmem : g ∈ (adjointGroup Tag.F4 K).map (baseChangeGL (algebraMap K Ω)) :=
    mem_map_adjointGroup_of_frobenius_fixed (τ := Tag.F4) (Or.inr rfl) (iterateFrobenius Ω p f)
      hFr hbij hgG hgF
  obtain ⟨e₁, he₁, he₁g⟩ := Subgroup.mem_map.1 hgmem
  have hconjK : e₁ * (z : ModGL Tag.F4 K) * e₁⁻¹ = (e₀ : ModGL Tag.F4 K) := by
    apply baseChangeGL_injective (algebraMap K Ω)
    rw [map_mul, map_mul, map_inv, he₁g]
    exact hgconj
  refine ⟨⟨e₁⁻¹, inv_mem he₁⟩, Subtype.ext ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
  rw [← hconjK]
  group

end Lang

end CFSG.LieType.SeitzGeneration.ExcHighThree
