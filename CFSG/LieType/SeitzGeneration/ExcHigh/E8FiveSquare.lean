module

public import CFSG.LieType.SeitzGeneration.ExcHigh.E8FiveInputs
public import CFSG.LieType.SeitzGeneration.ExcHigh.E8FiveWeyl
public import CFSG.LieType.SeitzGeneration.ExcHighThree.Killed
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LieType.SeitzGeneration.ExcHighThree CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.E6 (charVal weylMatrix weylMatrix_mulVec)


namespace E8FiveSq

theorem dvd_of_pow_mul_pow_eq_one {G : Type*} [Group G] {p : ℕ} [hp : Fact p.Prime]
    {E : Subgroup G} (hcard : Nat.card E = p ^ 2) {x₀ x₁ : G} (h₀ : x₀ ^ p = 1)
    (h₁ : x₁ ^ p = 1) (hx₀ : x₀ ≠ 1) (hgen : E ≤ Subgroup.closure {x₀, x₁}) {i j : ℕ}
    (hij : x₀ ^ i * x₁ ^ j = 1) : p ∣ i ∧ p ∣ j := by
  have hord₀ : orderOf x₀ = p := orderOf_eq_prime h₀ hx₀
  by_cases hj : p ∣ j
  · refine ⟨?_, hj⟩
    obtain ⟨m, rfl⟩ := hj
    rw [pow_mul, h₁, one_pow, mul_one] at hij
    rw [← hord₀]
    exact orderOf_dvd_of_pow_eq_one hij
  · exfalso
    have hcop : Nat.Coprime j p :=
      Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hj)
    have hAB : (j : ℤ) * Nat.gcdA j p + (p : ℤ) * Nat.gcdB j p = 1 := by
      have h := Nat.gcd_eq_gcd_ab j p
      rw [hcop.gcd_eq_one, Nat.cast_one] at h
      exact h.symm
    have hx₁mem : x₁ ∈ Subgroup.zpowers x₀ := by
      have hrw : x₁ = ((x₀ ^ i)⁻¹) ^ Nat.gcdA j p := by
        calc x₁ = x₁ ^ ((j : ℤ) * Nat.gcdA j p + (p : ℤ) * Nat.gcdB j p) := by
              rw [hAB, zpow_one]
          _ = (x₁ ^ j) ^ Nat.gcdA j p * (x₁ ^ p) ^ Nat.gcdB j p := by
              rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
          _ = ((x₀ ^ i)⁻¹) ^ Nat.gcdA j p := by
              rw [h₁, one_zpow, mul_one, eq_inv_of_mul_eq_one_right hij]
      rw [hrw]
      exact Subgroup.zpow_mem _
        (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers x₀) i)) _
    have hle : E ≤ Subgroup.zpowers x₀ := hgen.trans ((Subgroup.closure_le _).2 (by
      rintro y (rfl | rfl)
      · exact Subgroup.mem_zpowers _
      · exact hx₁mem))
    haveI : Finite (Subgroup.zpowers x₀) :=
      Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hord₀]; exact hp.out.ne_zero)
    have hc := Subgroup.card_le_of_le hle
    rw [hcard, Nat.card_zpowers, hord₀] at hc
    have h2 := hp.out.two_le
    nlinarith

theorem sq_eq_neg_one_of_orderOf_eq_four {r : ZMod 5} (h : orderOf r = 4) : r ^ 2 = -1 := by
  have h4 : r ^ 4 = 1 := by rw [← h]; exact pow_orderOf_eq_one r
  have h2 : r ^ 2 ≠ 1 := fun h2 => by
    have hd := orderOf_dvd_of_pow_eq_one h2
    rw [h] at hd
    norm_num at hd
  have key : ∀ x : ZMod 5, x ^ 4 = 1 → x ^ 2 ≠ 1 → x ^ 2 = -1 := by decide
  exact key r h4 h2

theorem natCast_prime_ne_zero_of_not_dvd {K L : Type} [Field K] [Finite K] [Field L]
    [Algebra K L] {p : ℕ} (hp : p.Prime) (h : ¬ p ∣ Nat.card K) : ((p : ℕ) : L) ≠ 0 := by
  intro h0
  have hK0 : ((p : ℕ) : K) = 0 := by
    rw [← map_natCast (algebraMap K L)] at h0
    exact (map_eq_zero_iff _ (algebraMap K L).injective).1 h0
  have hdvd : ringChar K ∣ p := (ringChar.spec K p).1 hK0
  haveI := ringChar.charP K
  haveI : Fintype K := Fintype.ofFinite K
  have hne : ringChar K ≠ 0 := CharP.char_ne_zero_of_finite K (ringChar K)
  have hpK : (ringChar K).Prime :=
    (CharP.char_is_prime_or_zero K (ringChar K)).resolve_right hne
  have hp' : ringChar K = p := (Nat.prime_dvd_prime_iff_eq hpK hp).1 hdvd
  obtain ⟨n, -, hcard⟩ := FiniteField.card K (ringChar K)
  apply h
  rw [Nat.card_eq_fintype_card, hcard, hp']
  exact dvd_pow_self p n.ne_zero

theorem exists_orderOf_eq_five_of_not_dvd {K : Type} [Field K] [Finite K]
    (h : ¬ 5 ∣ Nat.card K) : ∃ ω : (AlgebraicClosure K)ˣ, orderOf ω = 5 := by
  have hne : ((5 : ℕ) : AlgebraicClosure K) ≠ 0 :=
    natCast_prime_ne_zero_of_not_dvd Nat.prime_five h
  haveI : NeZero ((5 : ℕ) : AlgebraicClosure K) := ⟨hne⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) 5
  have hζu : IsUnit ζ := hζ.isUnit (by norm_num)
  have hprim : IsPrimitiveRoot hζu.unit 5 :=
    IsPrimitiveRoot.coe_units_iff.1 (by rw [hζu.unit_spec]; exact hζ)
  exact ⟨hζu.unit, hprim.eq_orderOf.symm⟩

theorem exists_pow_eq_of_orderOf_five {L : Type} [Field L] {ζ : Lˣ} (hζ : orderOf ζ = 5)
    {b : Lˣ} (hb : b ^ 5 = 1) : ∃ n : ℕ, b = ζ ^ n := by
  have hprim : IsPrimitiveRoot ((ζ : Lˣ) : L) 5 :=
    IsPrimitiveRoot.coe_units_iff.2 (IsPrimitiveRoot.iff_orderOf.2 hζ)
  have hi : ((b : Lˣ) : L) ^ 5 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hb, Units.val_one]
  obtain ⟨n, -, hn⟩ := hprim.eq_pow_of_pow_eq_one hi
  exact ⟨n, Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hn.symm)⟩

theorem charVal_natCast_eq {n : ℕ} {τ : Tag} (k : Fin τ.rank → ℕ) (l : Fin τ.rank → ℤ) :
    charVal (fun i => ((k i : ℕ) : ZMod n)) l = (((∑ i, (k i : ℤ) * l i : ℤ)) : ZMod n) := by
  simp only [charVal, Int.cast_sum, Int.cast_mul, Int.cast_natCast]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem charVal_eq_of_rootChar_eq_pow {τ : Tag} {M : Type} [Field M] {ω : Mˣ}
    (hω : orderOf ω = 5) {k : Fin τ.rank → ℕ} {a : Fin τ.rank → Mˣ} (ha : ∀ i, a i = ω ^ k i)
    {l l' : Fin τ.rank → ℤ} {m : ℕ} (h : rootChar a l = rootChar a l' ^ m) :
    charVal (fun i => ((k i : ℕ) : ZMod 5)) l =
      (m : ZMod 5) * charVal (fun i => ((k i : ℕ) : ZMod 5)) l' := by
  rw [rootChar_eq_zpow k a ha, rootChar_eq_zpow k a ha, ← zpow_natCast, ← zpow_mul,
    zpow_eq_zpow_iff_modEq, hω] at h
  have hc := (ZMod.intCast_eq_intCast_iff _ _ 5).2 h
  rw [charVal_natCast_eq, charVal_natCast_eq, hc, Int.cast_mul, Int.cast_natCast, mul_comm]

theorem rootChar_eq_one_of_charVal_eq_zero {τ : Tag} {M : Type} [Field M] {ω : Mˣ}
    (hω : orderOf ω = 5) {k : Fin τ.rank → ℕ} {a : Fin τ.rank → Mˣ} (ha : ∀ i, a i = ω ^ k i)
    {α : Fin τ.rank → ℤ} (h : charVal (fun i => ((k i : ℕ) : ZMod 5)) α = 0) :
    rootChar a α = 1 := by
  rw [charVal_natCast_eq, ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  obtain ⟨m, hm⟩ := h
  have h5 : ω ^ ((5 : ℕ) : ℤ) = 1 := by rw [zpow_natCast, ← hω, pow_orderOf_eq_one]
  rw [rootChar_eq_zpow k a ha, hm, zpow_mul, h5, one_zpow]

theorem diagMap_mem_twistedTorusOf {τ : Tag} {K : Type} [Field K] [Finite K]
    {A : Subgroup (adjointGroup τ K)} (D : LangPlaneData τ K A) {x : adjointGroup τ K}
    (hx : x ∈ A) :
    diagMap D x ∈ twistedTorusOf (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) D.w)
      (Units.map (entrywiseHom D.Fr)) := by
  obtain ⟨t, ht, hte⟩ := D.hc x hx
  have : diagMap D x = t := by
    rw [diagMap_apply, ← hte]
    simp [MulAut.conj_apply, mul_assoc]
  rw [this]
  exact ht

theorem rootChar_smul_eq_pow_of_mem {τ : Tag} {K : Type} [Field K] [Finite K]
    {A : Subgroup (adjointGroup τ K)} (D : LangPlaneData τ K A) {x : adjointGroup τ K}
    (hx : x ∈ A) {a : Fin τ.rank → (AlgebraicClosure K)ˣ} (ha : rootDiagUnit τ a = diagMap D x)
    (v : Fin τ.rank → ℤ) : rootChar a (D.w • v) = rootChar a v ^ Nat.card K := by
  have hfix := (mem_twistedTorusOf.1 (diagMap_mem_twistedTorusOf D hx)).2
  rw [← ha, CFSG.HardMathSupport.Timmesfeld.CrossChar.units_map_entrywiseHom_rootDiagUnit] at hfix
  rw [(rootDiagUnit_eq_conj_canonicalRep_iff _ _ D.w).1 hfix.symm v,
    ← CFSG.HardMathSupport.Timmesfeld.CrossChar.units_map_rootChar]
  exact Units.ext (by simp [D.hFr])

theorem pow_five_eq_one_of_rootDiagUnit_eq {K : Type} [Field K] [Finite K]
    {E₀ : Subgroup (adjointGroup Tag.E8 K)} (hE₀p : ∀ x ∈ E₀, x ^ 5 = 1)
    (D : LangPlaneData Tag.E8 K E₀) {x : adjointGroup Tag.E8 K} (hx : x ∈ E₀)
    {a : Fin Tag.E8.rank → (AlgebraicClosure K)ˣ} (ha : rootDiagUnit Tag.E8 a = diagMap D x) :
    a ^ 5 = 1 := by
  have h3 : rootDiagUnit Tag.E8 (a ^ 5) = rootDiagUnit Tag.E8 1 := by
    have e1 : rootDiagUnit Tag.E8 (a ^ 5) = (rootDiagUnit Tag.E8 a) ^ 5 :=
      map_pow (rootDiagUnitHom Tag.E8 (AlgebraicClosure K)) a 5
    have e2 : rootDiagUnit Tag.E8 (1 : Fin Tag.E8.rank → (AlgebraicClosure K)ˣ) = 1 :=
      map_one (rootDiagUnitHom Tag.E8 (AlgebraicClosure K))
    rw [e1, ha, e2, ← map_pow, hE₀p x hx, map_one]
  exact CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_injective h3

theorem exists_planeColumns {K : Type} [Field K] [Finite K] {ω : (AlgebraicClosure K)ˣ}
    (hω : orderOf ω = 5) {E₀ : Subgroup (adjointGroup Tag.E8 K)}
    (hE₀p : ∀ x ∈ E₀, x ^ 5 = 1) (hE₀c : Nat.card E₀ = 5 ^ 2) (D : LangPlaneData Tag.E8 K E₀)
    (hreg : ∀ α, IsRoot Tag.E8 α → ¬ D.Kills α) :
    ∃ x₀ ∈ E₀, ∃ x₁ ∈ E₀, x₀ ≠ 1 ∧ E₀ ≤ Subgroup.closure {x₀, x₁} ∧
      ∃ k₀ k₁ : Fin Tag.E8.rank → ℕ,
        rootDiagUnit Tag.E8 (fun l => ω ^ k₀ l) = diagMap D x₀ ∧
        rootDiagUnit Tag.E8 (fun l => ω ^ k₁ l) = diagMap D x₁ ∧
        ∀ α, IsRoot Tag.E8 α → charVal (fun i => ((k₀ i : ℕ) : ZMod 5)) α = 0 →
          charVal (fun i => ((k₁ i : ℕ) : ZMod 5)) α = 0 → False := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨x₀, hx₀, x₁, hx₁, hx₀1, -, hgen⟩ := exists_gens_of_plane (p := 5) hE₀p hE₀c
  have hcol : ∀ x ∈ E₀, ∃ k : Fin Tag.E8.rank → ℕ,
      rootDiagUnit Tag.E8 (fun l => ω ^ k l) = diagMap D x := by
    intro x hx
    obtain ⟨a, ha⟩ := exists_rootDiagUnit_of_mem_torusGroup (diagMap_mem_torusGroup D hx)
    have h5 := pow_five_eq_one_of_rootDiagUnit_eq hE₀p D hx ha
    choose k hk using fun i =>
      exists_pow_eq_of_orderOf_five hω (by simpa using congrFun h5 i)
    refine ⟨k, ?_⟩
    rw [← ha]
    congr 1
    funext l
    exact (hk l).symm
  obtain ⟨k₀, ha₀⟩ := hcol x₀ hx₀
  obtain ⟨k₁, ha₁⟩ := hcol x₁ hx₁
  refine ⟨x₀, hx₀, x₁, hx₁, hx₀1, hgen, k₀, k₁, ha₀, ha₁, fun α hα h₀ h₁ => hreg α hα ?_⟩
  set Sg : Subgroup (adjointGroup Tag.E8 K) :=
    ((rootCharHom (L := AlgebraicClosure K) α).ker.map
      (rootDiagUnitHom Tag.E8 (AlgebraicClosure K))).comap (diagMap D) with hSg
  have hmemS : ∀ (x : adjointGroup Tag.E8 K) (a : Fin Tag.E8.rank → (AlgebraicClosure K)ˣ),
      rootDiagUnit Tag.E8 a = diagMap D x → rootChar a α = 1 → x ∈ Sg := by
    intro x a hax hα1
    refine Subgroup.mem_comap.2 (Subgroup.mem_map.2 ⟨a, ?_, hax⟩)
    exact hα1
  have hx₀S : x₀ ∈ Sg :=
    hmemS x₀ _ ha₀ (rootChar_eq_one_of_charVal_eq_zero hω (fun _ => rfl) h₀)
  have hx₁S : x₁ ∈ Sg :=
    hmemS x₁ _ ha₁ (rootChar_eq_one_of_charVal_eq_zero hω (fun _ => rfl) h₁)
  have hAS : E₀ ≤ Sg := hgen.trans ((Subgroup.closure_le Sg).2 (by
    rintro y (rfl | rfl)
    · exact hx₀S
    · exact hx₁S))
  intro x hx
  obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 (hAS hx))
  exact ⟨a, by rw [← diagMap_apply]; exact hax, ha⟩

theorem exists_eigenPair_of_langPlaneData {K : Type} [Field K] [Finite K]
    (hpK : ¬ 5 ∣ Nat.card K) {E₀ : Subgroup (adjointGroup Tag.E8 K)}
    (hE₀p : ∀ x ∈ E₀, x ^ 5 = 1) (hE₀c : Nat.card E₀ = 5 ^ 2) (D : LangPlaneData Tag.E8 K E₀)
    (hreg : ∀ α, IsRoot Tag.E8 α → ¬ D.Kills α) :
    ∃ z₀ z₁ : Fin Tag.E8.rank → ZMod 5, EigenPair D.w ((Nat.card K : ℕ) : ZMod 5) z₀ z₁ := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨ω, hω⟩ := exists_orderOf_eq_five_of_not_dvd hpK
  obtain ⟨x₀, hx₀, x₁, hx₁, hx₀1, hgen, k₀, k₁, ha₀, ha₁, hreg'⟩ :=
    exists_planeColumns hω hE₀p hE₀c D hreg
  set a₀ : Fin Tag.E8.rank → (AlgebraicClosure K)ˣ := fun l => ω ^ k₀ l
  set a₁ : Fin Tag.E8.rank → (AlgebraicClosure K)ˣ := fun l => ω ^ k₁ l
  have hk₀ : ∀ i, a₀ i = ω ^ k₀ i := fun _ => rfl
  have hk₁ : ∀ i, a₁ i = ω ^ k₁ i := fun _ => rfl
  have h5 : ω ^ 5 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  refine ⟨fun i => (k₀ i : ZMod 5), fun i => (k₁ i : ZMod 5), ⟨?_, ?_, ?_, hreg'⟩⟩
  ·
    intro b₀ b₁ hb
    have hone : a₀ ^ b₀.val * a₁ ^ b₁.val = 1 := by
      funext l
      have hl := congrFun hb l
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hl
      have hdvd : 5 ∣ k₀ l * b₀.val + k₁ l * b₁.val := by
        rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_mul, Nat.cast_mul,
          ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
        linear_combination hl
      obtain ⟨m, hm⟩ := hdvd
      simp only [Pi.mul_apply, Pi.pow_apply, Pi.one_apply]
      rw [hk₀ l, hk₁ l, ← pow_mul, ← pow_mul, ← pow_add, hm, pow_mul, h5, one_pow]
    have hrel : x₀ ^ b₀.val * x₁ ^ b₁.val = 1 := by
      apply diagMap_injective D
      rw [map_mul, map_pow, map_pow, ← ha₀, ← ha₁, map_one]
      have e : rootDiagUnit Tag.E8 (a₀ ^ b₀.val * a₁ ^ b₁.val) =
          rootDiagUnit Tag.E8 a₀ ^ b₀.val * rootDiagUnit Tag.E8 a₁ ^ b₁.val := by
        have h := map_mul (rootDiagUnitHom Tag.E8 (AlgebraicClosure K)) (a₀ ^ b₀.val)
          (a₁ ^ b₁.val)
        rw [map_pow, map_pow] at h
        exact h
      rw [← e, hone]
      exact map_one (rootDiagUnitHom Tag.E8 (AlgebraicClosure K))
    obtain ⟨h₀, h₁⟩ :=
      dvd_of_pow_mul_pow_eq_one hE₀c (hE₀p x₀ hx₀) (hE₀p x₁ hx₁) hx₀1 hgen hrel
    have hv : ∀ b : ZMod 5, 5 ∣ b.val → b = 0 := fun b hb => by
      have hlt := ZMod.val_lt b
      have : b.val = 0 := by omega
      exact (ZMod.val_eq_zero b).1 this
    exact ⟨hv b₀ h₀, hv b₁ h₁⟩
  · intro v
    exact charVal_eq_of_rootChar_eq_pow hω hk₀ (rootChar_smul_eq_pow_of_mem D hx₀ ha₀ v)
  · intro v
    exact charVal_eq_of_rootChar_eq_pow hω hk₁ (rootChar_smul_eq_pow_of_mem D hx₁ ha₁ v)

theorem exists_weyl_neg_E8_five :
    ∃ w₀ : WeylGroup Tag.E8, ∀ u : Fin Tag.E8.rank → ℤ, w₀ • u = -u := by
  refine ⟨(coxeterSystem Tag.E8).wordProd
    (List.replicate 15 ([0, 1, 2, 3, 4, 5, 6, 7] : List (Fin Tag.E8.rank))).flatten, fun u => ?_⟩
  have h : weylMatrix ((coxeterSystem Tag.E8).wordProd
      (List.replicate 15 ([0, 1, 2, 3, 4, 5, 6, 7] : List (Fin Tag.E8.rank))).flatten) = -1 :=
    CFSG.RankThree.PartOne.KE8F.weylMatrix_wordProd_of5 (by decide +kernel)
  rw [← weylMatrix_mulVec, h, Matrix.neg_mulVec, Matrix.one_mulVec]

end E8FiveSq

theorem e8FiveFourSquare_holds : E8FiveFourSquare := by
  intro K _ _ hord E₀ hE₀p hE₀c D hreg
  have hpK : ¬ 5 ∣ Nat.card K := by
    intro hd
    rw [← ZMod.natCast_eq_zero_iff] at hd
    rw [hd, orderOf_zero] at hord
    omega
  obtain ⟨z₀, z₁, hE⟩ := E8FiveSq.exists_eigenPair_of_langPlaneData hpK hE₀p hE₀c D hreg
  obtain ⟨w₀, hw₀⟩ := E8FiveSq.exists_weyl_neg_E8_five
  exact E8FiveSq.e8FiveSquare_weyl hw₀ (E8FiveSq.sq_eq_neg_one_of_orderOf_eq_four hord) hE

end CFSG.LieType.SeitzGeneration.ExcHigh
