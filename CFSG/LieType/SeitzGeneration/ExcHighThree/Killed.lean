module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.Defs
public import CFSG.LieType.SeitzGeneration.ExcHighThree.RootChecks
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerF4Toral

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar

section Killed


@[expose] def rootCharHom {τ : Tag} {L : Type} [Field L] (α : Fin τ.rank → ℤ) :
    (Fin τ.rank → Lˣ) →* Lˣ where
  toFun a := rootChar a α
  map_one' := by simp [rootChar]
  map_mul' a b := by simp only [rootChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

theorem exists_rootDiagUnit_of_mem_torusGroup {τ : Tag} {L : Type} [Field L] {h : ModGL τ L}
    (hh : h ∈ torusGroup τ L) : ∃ a : Fin τ.rank → Lˣ, rootDiagUnit τ a = h := by
  have hle : torusGroup τ L ≤ (rootDiagUnitHom τ L).range := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨⟨i, u⟩, rfl⟩
    exact ⟨fun j => u ^ τ.cartan i j, (torusElt_eq_rootDiagUnit i u).symm⟩
  obtain ⟨a, ha⟩ := hle hh
  exact ⟨a, ha⟩

@[expose] def diagMap {τ : Tag} {K : Type} [Field K] [Finite K] {A : Subgroup (adjointGroup τ K)}
    (D : LangPlaneData τ K A) : adjointGroup τ K →* ModGL τ (AlgebraicClosure K) :=
  (MulAut.conj D.g0⁻¹).toMonoidHom.comp
    ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
      ((adjointGroup τ K).subtype.comp (MulAut.conj D.c).toMonoidHom))

theorem diagMap_apply {τ : Tag} {K : Type} [Field K] [Finite K] {A : Subgroup (adjointGroup τ K)}
    (D : LangPlaneData τ K A) (x : adjointGroup τ K) :
    diagMap D x = D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((D.c * x * D.c⁻¹ : adjointGroup τ K) : ModGL τ K) * D.g0 := by
  simp [diagMap, MulAut.conj_apply]

theorem diagMap_injective {τ : Tag} {K : Type} [Field K] [Finite K]
    {A : Subgroup (adjointGroup τ K)} (D : LangPlaneData τ K A) :
    Function.Injective (diagMap D) := by
  intro x y h
  rw [diagMap_apply, diagMap_apply] at h
  have h1 := mul_left_cancel (mul_right_cancel h)
  have h2 := baseChangeGL_injective (algebraMap K (AlgebraicClosure K)) h1
  have h3 : D.c * x * D.c⁻¹ = D.c * y * D.c⁻¹ := Subtype.ext h2
  simpa using h3

theorem diagMap_mem_torusGroup {τ : Tag} {K : Type} [Field K] [Finite K]
    {A : Subgroup (adjointGroup τ K)} (D : LangPlaneData τ K A) {x : adjointGroup τ K} (hx : x ∈ A) :
    diagMap D x ∈ torusGroup τ (AlgebraicClosure K) := by
  obtain ⟨t, ht, hte⟩ := D.hc x hx
  have : diagMap D x = t := by
    rw [diagMap_apply, ← hte]
    simp [MulAut.conj_apply, mul_assoc]
  rw [this]
  exact (Subgroup.mem_inf.1 ht).1

theorem natCast_three_ne_zero_of_not_dvd {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L]
    (h : ¬ 3 ∣ Nat.card K) : ((3 : ℕ) : L) ≠ 0 := by
  intro h0
  have hK0 : ((3 : ℕ) : K) = 0 := by
    rw [← map_natCast (algebraMap K L)] at h0
    exact (map_eq_zero_iff _ (algebraMap K L).injective).1 h0
  have hdvd : ringChar K ∣ 3 := (ringChar.spec K 3).1 hK0
  haveI := ringChar.charP K
  haveI : Fintype K := Fintype.ofFinite K
  have hne : ringChar K ≠ 0 := CharP.char_ne_zero_of_finite K (ringChar K)
  have hp : (ringChar K).Prime := (CharP.char_is_prime_or_zero K (ringChar K)).resolve_right hne
  have h3 : ringChar K = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hdvd
  obtain ⟨n, -, hcard⟩ := FiniteField.card K (ringChar K)
  apply h
  rw [Nat.card_eq_fintype_card, hcard, h3]
  exact dvd_pow_self 3 n.ne_zero

theorem prod_zpow_eq_zpow_sum_of_group {G ι : Type*} [CommGroup G] (ξ : G) (s : Finset ι)
    (f : ι → ℤ) : ∏ i ∈ s, ξ ^ f i = ξ ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, zpow_add, ih]

theorem rootChar_eq_one_of_dvd {τ : Tag} {L : Type} [Field L] {ω : Lˣ} (hω : ω ^ 3 = 1)
    {a : Fin τ.rank → Lˣ} {k : Fin τ.rank → ℕ} (hak : ∀ i, a i = ω ^ k i)
    {α : Fin τ.rank → ℤ} (hd : (3 : ℤ) ∣ ∑ i, α i * (k i : ℤ)) : rootChar a α = 1 := by
  obtain ⟨m, hm⟩ := hd
  have h1 : rootChar a α = ω ^ (∑ i, α i * (k i : ℤ)) := by
    rw [rootChar, ← prod_zpow_eq_zpow_sum_of_group]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hak i, ← zpow_natCast, ← zpow_mul, mul_comm]
  rw [h1, hm, zpow_mul]
  have : ω ^ (3 : ℤ) = 1 := by simpa using hω
  rw [this, one_zpow]

theorem langPlaneKilled_of_planeKilled {τ : Tag}
    (hcert : ∀ k₁ k₂ : Fin τ.rank → ℕ, (∃ i, ¬ 3 ∣ k₁ i) →
      ∃ α : Fin τ.rank → ℤ, IsRoot τ α ∧ (3 : ℤ) ∣ ∑ i, α i * (k₁ i : ℤ) ∧
        (3 : ℤ) ∣ ∑ i, α i * (k₂ i : ℤ)) : LangPlaneKilled τ := by
  intro K _ _ hnd A hA hcard D
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hne3 : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 := natCast_three_ne_zero_of_not_dvd (K := K) hnd
  haveI : NeZero ((3 : ℕ) : AlgebraicClosure K) := ⟨hne3⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) 3
  have hζu : IsUnit ζ := hζ.isUnit (by norm_num)
  obtain ⟨ω, hωζ⟩ : ∃ ω : (AlgebraicClosure K)ˣ, (ω : AlgebraicClosure K) = ζ :=
    ⟨hζu.unit, hζu.unit_spec⟩
  have hω3 : ω ^ 3 = 1 := Units.ext (by simp [hωζ, hζ.pow_eq_one])
  have hpow : ∀ b : (AlgebraicClosure K)ˣ, b ^ 3 = 1 → ∃ k : ℕ, b = ω ^ k := by
    intro b hb
    have hb' : (b : AlgebraicClosure K) ^ 3 = 1 := by
      have := congrArg (fun u : (AlgebraicClosure K)ˣ => (u : AlgebraicClosure K)) hb
      simpa using this
    obtain ⟨k, -, hk⟩ := hζ.eq_pow_of_pow_eq_one hb'
    exact ⟨k, Units.ext (by simp [hωζ, hk])⟩
  obtain ⟨x₁, hx₁, x₂, hx₂, hx₁1, hx₂1, hgen⟩ := exists_gens_of_plane (p := 3) hA hcard
  have hdiag : ∀ x ∈ A, ∃ a : Fin τ.rank → (AlgebraicClosure K)ˣ,
      rootDiagUnit τ a = diagMap D x ∧ ∀ i, a i ^ 3 = 1 := by
    intro x hx
    obtain ⟨a, ha⟩ := exists_rootDiagUnit_of_mem_torusGroup (diagMap_mem_torusGroup D hx)
    refine ⟨a, ha, fun i => ?_⟩
    have h3 : rootDiagUnit τ (a ^ 3) = rootDiagUnit τ 1 := by
      have e1 : rootDiagUnit τ (a ^ 3) = (rootDiagUnit τ a) ^ 3 :=
        map_pow (rootDiagUnitHom τ (AlgebraicClosure K)) a 3
      have e2 : rootDiagUnit τ (1 : Fin τ.rank → (AlgebraicClosure K)ˣ) = 1 :=
        map_one (rootDiagUnitHom τ (AlgebraicClosure K))
      rw [e1, ha, e2, ← map_pow, hA x hx, map_one]
    have h4 : a ^ 3 = 1 := CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_injective h3
    simpa using congrFun h4 i
  obtain ⟨a₁, ha₁, hc₁⟩ := hdiag x₁ hx₁
  obtain ⟨a₂, ha₂, hc₂⟩ := hdiag x₂ hx₂
  choose k₁ hk₁ using fun i => hpow (a₁ i) (hc₁ i)
  choose k₂ hk₂ using fun i => hpow (a₂ i) (hc₂ i)
  have hnt : ∃ i, ¬ 3 ∣ k₁ i := by
    by_contra hcon
    push Not at hcon
    apply hx₁1
    apply diagMap_injective D
    have ha1 : a₁ = 1 := by
      funext i
      obtain ⟨m, hm⟩ := hcon i
      rw [hk₁ i, hm, pow_mul, hω3, one_pow]
      rfl
    rw [map_one, ← ha₁, ha1]
    exact map_one (rootDiagUnitHom τ (AlgebraicClosure K))
  obtain ⟨α, hα, hd₁, hd₂⟩ := hcert k₁ k₂ hnt
  refine ⟨α, hα, ?_⟩
  set Sg : Subgroup (adjointGroup τ K) :=
    ((rootCharHom (L := AlgebraicClosure K) α).ker.map (rootDiagUnitHom τ (AlgebraicClosure K))).comap
      (diagMap D) with hSg
  have hmemS : ∀ (x : adjointGroup τ K) (a : Fin τ.rank → (AlgebraicClosure K)ˣ),
      rootDiagUnit τ a = diagMap D x → rootChar a α = 1 → x ∈ Sg := by
    intro x a hax hα1
    refine Subgroup.mem_comap.2 (Subgroup.mem_map.2 ⟨a, ?_, hax⟩)
    exact hα1
  have hx₁S : x₁ ∈ Sg := hmemS x₁ a₁ ha₁ (rootChar_eq_one_of_dvd hω3 hk₁ hd₁)
  have hx₂S : x₂ ∈ Sg := hmemS x₂ a₂ ha₂ (rootChar_eq_one_of_dvd hω3 hk₂ hd₂)
  have hAS : A ≤ Sg := hgen.trans ((Subgroup.closure_le Sg).2 (by
    rintro y (rfl | rfl)
    · exact hx₁S
    · exact hx₂S))
  intro x hx
  obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 (hAS hx))
  exact ⟨a, by rw [← diagMap_apply]; exact hax, ha⟩

theorem langPlaneKilled_E7 : LangPlaneKilled .E7 :=
  langPlaneKilled_of_planeKilled e7_planeKilled

theorem langPlaneKilled_E8 : LangPlaneKilled .E8 :=
  langPlaneKilled_of_planeKilled e8_planeKilled

end Killed

end CFSG.LieType.SeitzGeneration.ExcHighThree
