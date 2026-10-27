module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.F4ThreeGraphTab
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.F4ThreeGraphTorus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.F4ThreeGraphOrder
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.F4ThreeLangEven

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Classical CFSG.RankThree.PartOne.KE
  CFSG.LieType.Steinberg.Adjoint
open scoped MatrixGroups

set_option linter.unusedSectionVars false

theorem f4Graph_exists_coord {L : Type} [Field L] {ω : Lˣ} (hω : orderOf ω = 3) {x : Lˣ}
    (hx : x ^ 3 = 1) : ∃ k : Fin 3, x = ω ^ (k : ℕ) := by
  have hprim : IsPrimitiveRoot (ω : L) 3 :=
    IsPrimitiveRoot.coe_units_iff.2 (hω ▸ IsPrimitiveRoot.orderOf ω)
  have hx' : (x : L) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hx, Units.val_one]
  obtain ⟨k, hk, hkx⟩ := hprim.eq_pow_of_pow_eq_one hx'
  refine ⟨⟨k, hk⟩, Units.ext ?_⟩
  rw [Units.val_pow_eq_pow_val]
  exact hkx.symm

theorem f4Graph_rootChar_eq {L : Type} [Field L] {ω : Lˣ} {a : Fin Tag.F4.rank → Lˣ}
    {c : Fin 4 → Fin 3} (hc : ∀ i, a i = ω ^ ((c i : ℕ))) (γ : Fin Tag.F4.rank → ℤ) :
    rootChar a γ = ω ^ (∑ i : Fin 4, ((c i : ℕ) : ℤ) * γ i) := by
  rw [graphTorus_zpow_sum]
  simp only [rootChar]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hc i, ← zpow_natCast, ← zpow_mul]

theorem f4Graph_mem_kernelRoots_iff {L : Type} [Field L] {ω : Lˣ} (hω : orderOf ω = 3)
    {a : Fin Tag.F4.rank → Lˣ} {c : Fin 4 → Fin 3} (hc : ∀ i, a i = ω ^ ((c i : ℕ)))
    (γ : Fin Tag.F4.rank → ℤ) :
    γ ∈ kernelRoots (rootCharHom a) ↔ IsRoot Tag.F4 γ ∧ f4Kills c γ := by
  rw [kernelRoots_rootCharHom]
  change IsRoot Tag.F4 γ ∧ rootChar a γ = 1 ↔ _
  rw [f4Graph_rootChar_eq hc, ← orderOf_dvd_iff_zpow_eq_one, hω]
  unfold f4Kills
  push_cast
  exact and_congr_right fun _ => Int.dvd_iff_emod_eq_zero

theorem f4vec_ofFn (x : Fin 4 → ℤ) : f4vec (List.ofFn x) = x := by
  funext i
  fin_cases i <;> rfl

theorem f4Graph_mem_filter {c : Fin 4 → Fin 3} {x : Fin 4 → ℤ}
    (hx : List.ofFn x ∈ Tag.F4.artifactRoots) (hk : f4Kills c x) :
    List.ofFn x ∈ Tag.F4.artifactRoots.filter (fun l => decide (f4Kills c (f4vec l))) := by
  refine List.mem_filter.2 ⟨hx, ?_⟩
  rw [f4vec_ofFn]
  exact decide_eq_true hk

theorem f4Graph_closure {c : Fin 4 → Fin 3}
    (hcl : ∀ l ∈ Tag.F4.artifactRoots.filter (fun l => decide (f4Kills c (f4vec l))),
      ∀ l' ∈ Tag.F4.artifactRoots.filter (fun l => decide (f4Kills c (f4vec l))),
        f4iform (f4vec l) (f4vec l') ≠ 0 →
          (f4iform (f4vec l) (f4vec l) = 4 ↔ f4iform (f4vec l') (f4vec l') = 4))
    {x y : Fin 4 → ℤ} (hx : List.ofFn x ∈ Tag.F4.artifactRoots) (hkx : f4Kills c x)
    (hy : List.ofFn y ∈ Tag.F4.artifactRoots) (hky : f4Kills c y) (hxy : f4iform x y ≠ 0) :
    f4iform x x = 4 ↔ f4iform y y = 4 := by
  have := hcl _ (f4Graph_mem_filter hx hkx) _ (f4Graph_mem_filter hy hky)
  rw [f4vec_ofFn, f4vec_ofFn] at this
  exact this hxy

section Spans

variable {τ : Tag} {L : Type} [Field L]

theorem f4Graph_commute_of_ne {a : Fin τ.rank → Lˣ} {i j : KernelComponent (rootCharHom a)}
    (hij : i ≠ j) {x y : ModGL τ L}
    (hx : x ∈ rootSpan τ L (componentRoots (rootCharHom a) i))
    (hy : y ∈ rootSpan τ L (componentRoots (rootCharHom a) j)) : Commute x y := by
  obtain ⟨-, -, hc, -, -⟩ := root_character_kernel_orthogonal_central_product τ L (rootCharHom a)
  have h := (Subgroup.commutator_eq_bot_iff_le_centralizer.1 (hc i j hij)) hx
  exact (Subgroup.mem_centralizer_iff.1 h y hy).symm

theorem f4Graph_length_of_mk_eq {a : Fin τ.rank → Lˣ} {n : ℤ}
    (hcl : ∀ x ∈ kernelRoots (rootCharHom a), ∀ y ∈ kernelRoots (rootCharHom a),
      iform x y ≠ 0 → (iform x x = n ↔ iform y y = n))
    {x y : kernelRoots (rootCharHom a)}
    (h : (⟦x⟧ : KernelComponent (rootCharHom a)) = ⟦y⟧) :
    iform (x : Fin τ.rank → ℤ) x = n ↔ iform (y : Fin τ.rank → ℤ) y = n := by
  have h' := Quotient.exact h
  change Relation.EqvGen _ x y at h'
  clear h
  induction h' with
  | rel u v huv =>
    rw [dotProduct_mulVec_eq_iform] at huv
    exact hcl u u.2 v v.2 huv
  | refl => exact Iff.rfl
  | symm u v _ ih => exact ih.symm
  | trans u v w _ _ ih1 ih2 => exact ih1.trans ih2

end Spans

section Graph

variable (K : Type) [Field K] [Finite K] {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
  (hFr : ∀ c, Fr c = c ^ Nat.card K) {w : WeylGroup Tag.F4}
  {g0 : ModGL Tag.F4 (AlgebraicClosure K)} (hg0C : g0 ∈ adjointGroup Tag.F4 (AlgebraicClosure K))
  (hg0 : Units.map (entrywiseHom Fr) g0 =
    g0 * canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w)
  (S : LangSetup Tag.F4 (AlgebraicClosure K) 3)
  (hSD : S.D = LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0)

@[expose] noncomputable def f4GraphFix (S : LangSetup Tag.F4 (AlgebraicClosure K) 3)
    (δ : MulAut S.Γ) : Subgroup (ModGL Tag.F4 (AlgebraicClosure K)) :=
  (δ.toMonoidHom.eqLocus (MonoidHom.id S.Γ)).map S.Γ.subtype

include hSD in
theorem f4Graph_torus_mem (hK4 : 4 ≤ Nat.card K) {D₁ : Subgroup (ModGL Tag.F4 (AlgebraicClosure K))}
    (δ : MulAut S.Γ)
    (hfix : ∀ x : S.Γ, (x : ModGL Tag.F4 (AlgebraicClosure K)) ∈ rigidTestSet S D₁ → δ x = x)
    {a : Fin Tag.F4.rank → (AlgebraicClosure K)ˣ} (haD : rootDiagUnit Tag.F4 a ∈ D₁)
    (ha1 : rootDiagUnit Tag.F4 a ≠ 1) (i : KernelComponent (rootCharHom a))
    {z : ModGL Tag.F4 (AlgebraicClosure K)}
    {P : (Fin Tag.F4.rank → ℤ) → GL (Fin 2) (AlgebraicClosure K)}
    (hnorm : ∀ g : ModGL Tag.F4 (AlgebraicClosure K),
      g ∈ rootSpan Tag.F4 (AlgebraicClosure K) (componentRoots (rootCharHom a) i) ↔
        z * g * z⁻¹ ∈ rootSpan Tag.F4 (AlgebraicClosure K) (componentRoots (rootCharHom a) i))
    (hfixF : ∀ γ ∈ componentRoots (rootCharHom a) i, ∀ A : SL2 K,
      S.D.step (z * rootSL2 Tag.F4 (AlgebraicClosure K) γ (conjSL (P γ)
        (Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K)) A)) * z⁻¹) =
        z * rootSL2 Tag.F4 (AlgebraicClosure K) γ (conjSL (P γ)
          (Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K)) A)) * z⁻¹)
    (hall : ∀ γ ∈ componentRoots (rootCharHom a) i, ∀ ζ : (AlgebraicClosure K)ˣ,
      ζ ^ (Nat.card K + 1) = 1 →
        HSL ζ ∈ (Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K))).range.map
          (conjSL (P γ)))
    {ζ₀ : (AlgebraicClosure K)ˣ} (hζ₀ : orderOf ζ₀ = 3) (hζ₀q : ζ₀ ^ (Nat.card K + 1) = 1)
    {ξ : (AlgebraicClosure K)ˣ} (hξ : ξ ^ (Nat.card K + 1) = 1) {r : ℕ}
    {γ : Fin r → Fin Tag.F4.rank → ℤ} (hγ : ∀ k, γ k ∈ componentRoots (rootCharHom a) i)
    (u : Fin r → Subgroup.zpowers ξ) :
    graphTorusHom γ (Subgroup.zpowers ξ) z u ∈ f4GraphFix K S δ ∧
      graphTorusHom γ (Subgroup.zpowers ξ) z u ∈
        rootSpan Tag.F4 (AlgebraicClosure K) (componentRoots (rootCharHom a) i) := by
  have hγr : ∀ k, IsRoot Tag.F4 (γ k) := fun k => isRoot_of_mem_componentRoots (hγ k)
  have hpow : ∀ t : Subgroup.zpowers ξ, (t : (AlgebraicClosure K)ˣ) ^ (Nat.card K + 1) = 1 := by
    rintro ⟨_, k, rfl⟩
    change (ξ ^ k) ^ (Nat.card K + 1) = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hξ, one_zpow]
  rw [graphTorusHom_eq_prod hγr]
  refine ⟨Subgroup.list_prod_mem _ fun x hx => ?_, Subgroup.list_prod_mem _ fun x hx => ?_⟩
  · obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
    have hX := steinbergLang_mem_bigComponentSet S Nat.prime_three hK4 haD ha1 i hnorm (hγ k)
      (hfixF _ (hγ k)) hζ₀ (hall _ (hγ k) ζ₀ hζ₀q) (hall _ (hγ k) _ (hpow (u k)))
    have hXΓ := bigComponentSet_subset_Γ S D₁ hX
    exact ⟨⟨_, hXΓ⟩, hfix ⟨_, hXΓ⟩ (Or.inl hX), rfl⟩
  · obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
    exact (hnorm _).1 (steinbergLang_rootSL2_mem_component K i (hγ k) _)

theorem f4Graph_corootPair_self {τ : Tag} {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    corootPair β β = 2 := by
  rw [corootPair, Int.mul_ediv_cancel _ (iform_self_pos_of_isRoot hβ).ne']

theorem f4Graph_q_facts {q m : ℕ} (hm : 1 ≤ m) (hK : q = 2 ^ (2 * m + 1)) :
    8 ≤ q ∧ q % 2 = 0 ∧ q % 3 = 3 - 1 := by
  subst hK
  refine ⟨?_, ?_, ?_⟩
  · calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · rw [pow_succ]
    omega
  · have h4 : 4 ^ m % 3 = 1 := by
      rw [Nat.pow_mod]
      norm_num
    rw [pow_succ, pow_mul]
    norm_num
    omega

theorem f4Graph_coprime {q : ℕ} (hq : q % 2 = 0) {D : ℤ} (hD : D = 1 ∨ D = -1 ∨ D = 2 ∨ D = -2) :
    Nat.Coprime D.natAbs (q + 1) := by
  have hodd : Nat.Coprime 2 (q + 1) := Nat.coprime_two_left.2 (Nat.odd_iff.2 (by omega))
  rcases hD with rfl | rfl | rfl | rfl
  · exact Nat.coprime_one_left _
  · exact Nat.coprime_one_left _
  · exact hodd
  · exact hodd

theorem f4Graph_zpowers_pow {L : Type} [Field L] {ξ : Lˣ} {n : ℕ} (hξ : ξ ^ n = 1) :
    ∀ x ∈ Subgroup.zpowers ξ, x ^ n = 1 := by
  intro x hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hξ, one_zpow]

theorem f4Graph_card_domain {L : Type} [Field L] {ξ : Lˣ} {n : ℕ} (hξ : orderOf ξ = n) (r : ℕ) :
    Nat.card (Fin r → Subgroup.zpowers ξ) = n ^ r := by
  rw [Nat.card_fun, Nat.card_zpowers, hξ, Nat.card_fin]

include hSD in
theorem f4Graph_false_of_rank3 {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1))
    {D₁ : Subgroup (ModGL Tag.F4 (AlgebraicClosure K))} (hD₁E : D₁ ≤ S.E) (δ : MulAut S.Γ)
    (hδ2 : δ ^ 2 = 1) (hδo : δ ∉ (MulAut.conj : S.Γ →* MulAut S.Γ).range)
    (hfix : ∀ x : S.Γ, (x : ModGL Tag.F4 (AlgebraicClosure K)) ∈ rigidTestSet S D₁ → δ x = x)
    {a : Fin Tag.F4.rank → (AlgebraicClosure K)ˣ} (haD : rootDiagUnit Tag.F4 a ∈ D₁)
    (ha1 : rootDiagUnit Tag.F4 a ≠ 1) (i : KernelComponent (rootCharHom a))
    {γ : Fin 3 → Fin Tag.F4.rank → ℤ} (hγ : ∀ k, γ k ∈ componentRoots (rootCharHom a) i)
    {A : Fin 3 → Fin Tag.F4.rank → ℤ} {D : ℤ}
    (hA : ∀ k j, ∑ i, A k i * corootPair (γ j) (Pi.single i 1) = if k = j then D else 0)
    (hD : D = 1 ∨ D = -1 ∨ D = 2 ∨ D = -2) : False := by
  classical
  obtain ⟨hq8, hqeven, hq3⟩ := f4Graph_q_facts hm hK
  have hst : ∀ b : Fin Tag.F4.rank → (AlgebraicClosure K)ˣ, (∀ i, b i ^ 3 = 1) →
      rootCharStabilizerSubgroup b ≤ kernelReflectionGroup b := fun b hb =>
    (Steinberg.rootCharStabilizerSubgroup_eq_kernelReflectionGroup_F4_three b hb).le
  obtain ⟨z, P, hnorm, hfixF, hall⟩ := steinbergLang_exists_family_neg K hFr hg0C hg0 S hSD
    Nat.prime_three hst f4Neg_smul hq3 (hD₁E haD) i
  obtain ⟨ξ, hξord, hξq⟩ := exists_orderOf_eq_of_dvd_card_add_one K
    (L := AlgebraicClosure K) (dvd_refl (Nat.card K + 1))
  obtain ⟨ζ₀, hζ₀, hζ₀q⟩ := exists_orderOf_eq_of_dvd_card_add_one K
    (L := AlgebraicClosure K) (N := 3) (by omega)
  set Θ := graphTorusHom γ (Subgroup.zpowers ξ) z with hΘ
  have hinj : Function.Injective Θ :=
    graphTorusHom_injective z (f4Graph_zpowers_pow hξq) hA (f4Graph_coprime hqeven hD)
  have hle : Θ.range ≤ f4GraphFix K S δ := by
    rintro _ ⟨u, rfl⟩
    exact (f4Graph_torus_mem K hFr hg0C hg0 S hSD (by omega) δ hfix haD ha1 i (hnorm i) hfixF
      hall hζ₀ hζ₀q hξq hγ u).1
  have hcard : Nat.card Θ.range = (Nat.card K + 1) ^ 3 := by
    have h1 : Nat.card Θ.range = Nat.card (Set.range Θ) := by
      rw [← MonoidHom.coe_range]
      rfl
    rw [h1, ← Nat.card_congr (Equiv.ofInjective Θ hinj), f4Graph_card_domain hξord]
  have hdvd1 : Nat.card Θ.range ∣ Nat.card (f4GraphFix K S δ) := Subgroup.card_dvd_of_le hle
  have hdvd2 : Nat.card (f4GraphFix K S δ) ∣ reeF4Order (2 ^ (2 * m + 1)) := by
    rw [f4GraphFix, Subgroup.card_map_of_injective S.Γ.subtype_injective]
    exact f4Graph_card_dvd K hFr hg0C hg0 S hSD hK δ hδ2 hδo
  rw [hcard, hK] at hdvd1
  exact f4Graph_not_cube_dvd hm (hdvd1.trans hdvd2)

include hSD in
theorem f4Graph_false_of_rank22 {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1))
    {D₁ : Subgroup (ModGL Tag.F4 (AlgebraicClosure K))} (hD₁E : D₁ ≤ S.E) (δ : MulAut S.Γ)
    (hδ2 : δ ^ 2 = 1) (hδo : δ ∉ (MulAut.conj : S.Γ →* MulAut S.Γ).range)
    (hfix : ∀ x : S.Γ, (x : ModGL Tag.F4 (AlgebraicClosure K)) ∈ rigidTestSet S D₁ → δ x = x)
    {a : Fin Tag.F4.rank → (AlgebraicClosure K)ˣ} (haD : rootDiagUnit Tag.F4 a ∈ D₁)
    (ha1 : rootDiagUnit Tag.F4 a ≠ 1) {i j : KernelComponent (rootCharHom a)} (hij : i ≠ j)
    {γ γ' : Fin 2 → Fin Tag.F4.rank → ℤ} (hγ : ∀ k, γ k ∈ componentRoots (rootCharHom a) i)
    (hγ' : ∀ k, γ' k ∈ componentRoots (rootCharHom a) j)
    (h01 : corootPair (γ 0) (γ 1) = -1) (h10 : corootPair (γ 1) (γ 0) = -1)
    {A A' : Fin 2 → Fin Tag.F4.rank → ℤ} {D D' : ℤ}
    (hA : ∀ k l, ∑ i, A k i * corootPair (γ l) (Pi.single i 1) = if k = l then D else 0)
    (hA' : ∀ k l, ∑ i, A' k i * corootPair (γ' l) (Pi.single i 1) = if k = l then D' else 0)
    (hD : D = 1 ∨ D = -1 ∨ D = 2 ∨ D = -2) (hD' : D' = 1 ∨ D' = -1 ∨ D' = 2 ∨ D' = -2) :
    False := by
  classical
  obtain ⟨hq8, hqeven, hq3⟩ := f4Graph_q_facts hm hK
  have hst : ∀ b : Fin Tag.F4.rank → (AlgebraicClosure K)ˣ, (∀ i, b i ^ 3 = 1) →
      rootCharStabilizerSubgroup b ≤ kernelReflectionGroup b := fun b hb =>
    (Steinberg.rootCharStabilizerSubgroup_eq_kernelReflectionGroup_F4_three b hb).le
  obtain ⟨z₁, P₁, hnorm₁, hfixF₁, hall₁⟩ := steinbergLang_exists_family_neg K hFr hg0C hg0 S hSD
    Nat.prime_three hst f4Neg_smul hq3 (hD₁E haD) i
  obtain ⟨z₂, P₂, hnorm₂, hfixF₂, hall₂⟩ := steinbergLang_exists_family_neg K hFr hg0C hg0 S hSD
    Nat.prime_three hst f4Neg_smul hq3 (hD₁E haD) j
  obtain ⟨ξ, hξord, hξq⟩ := exists_orderOf_eq_of_dvd_card_add_one K
    (L := AlgebraicClosure K) (dvd_refl (Nat.card K + 1))
  obtain ⟨ζ₀, hζ₀, hζ₀q⟩ := exists_orderOf_eq_of_dvd_card_add_one K
    (L := AlgebraicClosure K) (N := 3) (by omega)
  set Θ₁ := graphTorusHom γ (Subgroup.zpowers ξ) z₁ with hΘ₁
  set Θ₂ := graphTorusHom γ' (Subgroup.zpowers ξ) z₂ with hΘ₂
  have hinj₂ : Function.Injective Θ₂ :=
    graphTorusHom_injective z₂ (f4Graph_zpowers_pow hξq) hA' (f4Graph_coprime hqeven hD')
  have hinj₁ : Function.Injective Θ₁ :=
    graphTorusHom_injective z₁ (f4Graph_zpowers_pow hξq) hA (f4Graph_coprime hqeven hD)
  have hmem₁ := f4Graph_torus_mem K hFr hg0C hg0 S hSD (by omega) δ hfix haD ha1 i (hnorm₁ i)
    hfixF₁ hall₁ hζ₀ hζ₀q hξq hγ
  have hmem₂ := f4Graph_torus_mem K hFr hg0C hg0 S hSD (by omega) δ hfix haD ha1 j (hnorm₂ j)
    hfixF₂ hall₂ hζ₀ hζ₀q hξq hγ'
  have hcomm : ∀ u v, Commute (Θ₁ u) (Θ₂ v) := fun u v =>
    f4Graph_commute_of_ne hij (hmem₁ u).2 (hmem₂ v).2
  set Θ := MonoidHom.noncommCoprod Θ₁ Θ₂ hcomm with hΘ
  have hle : Θ.range ≤ f4GraphFix K S δ := by
    rintro _ ⟨⟨u, v⟩, rfl⟩
    rw [MonoidHom.noncommCoprod_apply]
    exact mul_mem (hmem₁ u).1 (hmem₂ v).1
  have hγr : ∀ k, IsRoot Tag.F4 (γ k) := fun k => isRoot_of_mem_componentRoots (hγ k)
  have hcent : ∀ u, Θ₁ u ∈ rootSpan Tag.F4 (AlgebraicClosure K)
      (componentRoots (rootCharHom a) j) →
      ((u 0 : (AlgebraicClosure K)ˣ)) ^ 3 = 1 ∧ (u 1 : (AlgebraicClosure K)ˣ) = (u 0) ^ 2 := by
    intro u hu
    have hχ : ∀ k,
        rootChar (graphTorusChar γ fun l => (u l : (AlgebraicClosure K)ˣ)) (γ k) = 1 := by
      intro k
      set d := rootDiagUnit Tag.F4 (graphTorusChar γ fun l => (u l : (AlgebraicClosure K)ˣ))
      set y := rootSL2 Tag.F4 (AlgebraicClosure K) (γ k) (uSL 1)
      have hyS : z₁ * y * z₁⁻¹ ∈ rootSpan Tag.F4 (AlgebraicClosure K)
          (componentRoots (rootCharHom a) i) :=
        (hnorm₁ i _).1 (steinbergLang_rootSL2_mem_component K i (hγ k) _)
      have hc := f4Graph_commute_of_ne (Ne.symm hij) hu hyS
      have hdy : d * y * d⁻¹ = y := by
        have h1 : (z₁ * d * z₁⁻¹) * (z₁ * y * z₁⁻¹) = (z₁ * y * z₁⁻¹) * (z₁ * d * z₁⁻¹) := hc.eq
        have h2 : d * y = y * d := by
          have h3 := congrArg (fun x => z₁⁻¹ * x * z₁) h1
          simpa [mul_assoc] using h3
        rw [h2, mul_assoc, mul_inv_cancel, mul_one]
      rw [(rootDiagUnit_conj_rootSL2 _ (hγr k) 1).1, mul_one] at hdy
      have h4 := CFSG.RankThree.PartTwo.Census.Exceptional.rootSL2_injective (hγr k) hdy
      have h5 := congrArg (fun B : SL2 (AlgebraicClosure K) =>
        (B : Matrix (Fin 2) (Fin 2) (AlgebraicClosure K)) 0 1) h4
      simp only [coe_uSL] at h5
      exact Units.ext (by simpa using h5)
    have e0 := hχ 0
    have e1 := hχ 1
    rw [rootChar_graphTorusChar hγr, Fin.prod_univ_two, f4Graph_corootPair_self (hγr 0), h10] at e0
    rw [rootChar_graphTorusChar hγr, Fin.prod_univ_two, f4Graph_corootPair_self (hγr 1), h01] at e1
    have hu1 : (u 1 : (AlgebraicClosure K)ˣ) = (u 0) ^ 2 := by
      have := mul_inv_eq_one.1 (by simpa [zpow_neg, zpow_ofNat] using e0)
      exact this.symm
    refine ⟨?_, hu1⟩
    rw [hu1] at e1
    have : ((u 0 : (AlgebraicClosure K)ˣ)) ^ (-1 : ℤ) * ((u 0) ^ 2) ^ (2 : ℤ) =
        (u 0) ^ (3 : ℤ) := by
      rw [← zpow_natCast, ← zpow_mul, ← zpow_add]
      norm_num
    rw [this] at e1
    exact_mod_cast e1
  have hkerle : Nat.card Θ.ker ≤ 3 := by
    have hk : ∀ x : Θ.ker, ((x.1.1 0 : (AlgebraicClosure K)ˣ)) ^ 3 = 1 ∧
        (x.1.1 1 : (AlgebraicClosure K)ˣ) = (x.1.1 0) ^ 2 ∧ Θ₂ x.1.2 = (Θ₁ x.1.1)⁻¹ := by
      intro x
      have hx : Θ₁ x.1.1 * Θ₂ x.1.2 = 1 := by
        have := x.2
        rw [MonoidHom.mem_ker, MonoidHom.noncommCoprod_apply] at this
        exact this
      have h2 : Θ₂ x.1.2 = (Θ₁ x.1.1)⁻¹ := eq_inv_of_mul_eq_one_right hx
      have h3 : Θ₁ x.1.1 ∈ rootSpan Tag.F4 (AlgebraicClosure K)
          (componentRoots (rootCharHom a) j) := by
        rw [show Θ₁ x.1.1 = (Θ₂ x.1.2)⁻¹ by rw [h2, inv_inv]]
        exact inv_mem (hmem₂ x.1.2).2
      exact ⟨(hcent _ h3).1, (hcent _ h3).2, h2⟩
    let F : Θ.ker → rootsOfUnity 3 (AlgebraicClosure K) := fun x =>
      ⟨(x.1.1 0 : (AlgebraicClosure K)ˣ), (mem_rootsOfUnity 3 _).2 (hk x).1⟩
    have hF : Function.Injective F := by
      intro x y hxy
      have h0 : (x.1.1 0 : (AlgebraicClosure K)ˣ) = y.1.1 0 :=
        congrArg (fun t : rootsOfUnity 3 (AlgebraicClosure K) => (t : (AlgebraicClosure K)ˣ)) hxy
      have hu : x.1.1 = y.1.1 := by
        funext k
        apply Subtype.ext
        fin_cases k
        · exact h0
        · change (x.1.1 1 : (AlgebraicClosure K)ˣ) = y.1.1 1
          rw [(hk x).2.1, (hk y).2.1, h0]
      have hv : x.1.2 = y.1.2 := hinj₂ (by rw [(hk x).2.2, (hk y).2.2, hu])
      exact Subtype.ext (Prod.ext hu hv)
    exact (Nat.card_le_card_of_injective F hF).trans (card_rootsOfUnity _ 3)
  have : Finite (Subgroup.zpowers ξ) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hξord]; omega)
  have hcardG : Nat.card ((Fin 2 → Subgroup.zpowers ξ) × (Fin 2 → Subgroup.zpowers ξ)) =
      (Nat.card K + 1) ^ 4 := by
    rw [Nat.card_prod, f4Graph_card_domain hξord, ← pow_add]
  have hiso := Subgroup.card_eq_card_quotient_mul_card_subgroup Θ.ker
  rw [hcardG, Nat.card_congr (QuotientGroup.quotientKerEquivRange Θ).toEquiv] at hiso
  have hkerdvd : Nat.card Θ.ker ∣ 3 := by
    have hpos : 0 < Nat.card Θ.ker := Nat.card_pos
    have hdvd : Nat.card Θ.ker ∣ (Nat.card K + 1) ^ 4 := ⟨_, hiso.trans (mul_comm _ _)⟩
    have hodd : ¬ 2 ∣ (Nat.card K + 1) ^ 4 := by
      intro h2
      have := (Nat.prime_two.dvd_of_dvd_pow h2)
      omega
    interval_cases h : Nat.card Θ.ker
    · exact one_dvd 3
    · exact absurd hdvd hodd
    · exact dvd_refl 3
  have hdvd1 : Nat.card Θ.range ∣ Nat.card (f4GraphFix K S δ) := Subgroup.card_dvd_of_le hle
  have hdvd2 : Nat.card (f4GraphFix K S δ) ∣ reeF4Order (2 ^ (2 * m + 1)) := by
    rw [f4GraphFix, Subgroup.card_map_of_injective S.Γ.subtype_injective]
    exact f4Graph_card_dvd K hFr hg0C hg0 S hSD hK δ hδ2 hδo
  have hmain : (Nat.card K + 1) ^ 4 ∣ 3 * reeF4Order (2 ^ (2 * m + 1)) := by
    rw [hiso, mul_comm 3]
    exact mul_dvd_mul (hdvd1.trans hdvd2) hkerdvd
  rw [hK] at hmain
  exact f4Graph_not_fourth_dvd hm hmain

end Graph

theorem f4ThreeEvenGraphRigid_holds : F4ThreeEvenGraphRigid := by
  intro K _ _ m hm hK Fr hFr w g0 hg0C hg0 S hSD D₁ hD₁E hD₁c δ hδ2 hδo hfix
  obtain ⟨-, -, hq3⟩ := f4Graph_q_facts hm hK
  obtain ⟨ω, hω, -⟩ := exists_orderOf_eq_of_dvd_card_add_one K (L := AlgebraicClosure K)
    (N := 3) (by omega)
  obtain ⟨a, haD, ha1, -⟩ := steinbergLang_exists_plane_elt S hD₁E hD₁c (Pi.single 0 1)
  have hE := hD₁E haD
  have hcoord : ∀ i, ∃ k : Fin 3, a i = ω ^ (k : ℕ) := fun i =>
    f4Graph_exists_coord hω (steinbergLang_coord_pow S hE i)
  choose c' hc' using hcoord
  obtain ⟨c, hc⟩ : ∃ c : Fin 4 → Fin 3, ∀ i : Fin Tag.F4.rank, a i = ω ^ ((c i : ℕ)) :=
    ⟨c', hc'⟩
  have hc0 : c ≠ 0 := by
    intro h0
    apply ha1
    have : a = 1 := by
      funext i
      rw [hc i]
      have : c i = 0 := congrFun h0 i
      rw [this]
      simp
    rw [this, rootDiagUnit_one]
  have hker := f4Graph_mem_kernelRoots_iff hω hc
  rcases f4Graph_witness c hc0 with ⟨R, A, D, hR⟩ | ⟨R, A, D, R', A', D', hR⟩
  · obtain ⟨hmemR, hkill, h01, h12, hA, hD⟩ := hR
    have hγr : ∀ k : Fin 3, IsRoot Tag.F4 (f4row R k) := fun k =>
      (isRoot_iff_mem_artifactRoots (τ := Tag.F4) (v := f4row R k)).2 (hmemR k)
    have hγk : ∀ k : Fin 3, f4row R k ∈ kernelRoots (rootCharHom a) := fun k =>
      (hker _).2 ⟨hγr k, hkill k⟩
    have e01 : (⟦⟨f4row R 0, hγk 0⟩⟧ : KernelComponent (rootCharHom a)) = ⟦⟨f4row R 1, hγk 1⟩⟧ :=
      mk_eq_of_iform_ne_zero h01
    have e12 : (⟦⟨f4row R 1, hγk 1⟩⟧ : KernelComponent (rootCharHom a)) = ⟦⟨f4row R 2, hγk 2⟩⟧ :=
      mk_eq_of_iform_ne_zero h12
    refine f4Graph_false_of_rank3 K hFr hg0C hg0 S hSD hm hK hD₁E δ hδ2 hδo hfix haD ha1
      ⟦⟨f4row R 0, hγk 0⟩⟧ (γ := fun k => f4row R k) (fun k => ?_) (A := fun k => f4row A k) hA hD
    fin_cases k
    · exact ⟨hγk 0, rfl⟩
    · exact ⟨hγk 1, e01.symm⟩
    · exact ⟨hγk 2, (e01.trans e12).symm⟩
  · obtain ⟨hmemR, hmemR', hkill, hkill', h01, h10, h'01, hlong, hshort, hcl, hA, hA', hD, hD'⟩ :=
      hR
    have hγr : ∀ k : Fin 2, IsRoot Tag.F4 (f4row R k) := fun k =>
      (isRoot_iff_mem_artifactRoots (τ := Tag.F4) (v := f4row R k)).2 (hmemR k)
    have hγr' : ∀ k : Fin 2, IsRoot Tag.F4 (f4row R' k) := fun k =>
      (isRoot_iff_mem_artifactRoots (τ := Tag.F4) (v := f4row R' k)).2 (hmemR' k)
    have hγk : ∀ k : Fin 2, f4row R k ∈ kernelRoots (rootCharHom a) := fun k =>
      (hker _).2 ⟨hγr k, hkill k⟩
    have hγk' : ∀ k : Fin 2, f4row R' k ∈ kernelRoots (rootCharHom a) := fun k =>
      (hker _).2 ⟨hγr' k, hkill' k⟩
    have hne01 : iform (τ := Tag.F4) (f4row R 0) (f4row R 1) ≠ 0 := by
      intro h0
      have h1 : corootPair (τ := Tag.F4) (f4row R 0) (f4row R 1) = -1 := h01
      unfold corootPair at h1
      rw [h0] at h1
      simp at h1
    have e01 : (⟦⟨f4row R 0, hγk 0⟩⟧ : KernelComponent (rootCharHom a)) = ⟦⟨f4row R 1, hγk 1⟩⟧ :=
      mk_eq_of_iform_ne_zero hne01
    have e'01 : (⟦⟨f4row R' 0, hγk' 0⟩⟧ : KernelComponent (rootCharHom a)) =
        ⟦⟨f4row R' 1, hγk' 1⟩⟧ := mk_eq_of_iform_ne_zero h'01
    have hcl' : ∀ x ∈ kernelRoots (rootCharHom a), ∀ y ∈ kernelRoots (rootCharHom a),
        iform x y ≠ 0 → (iform x x = 4 ↔ iform y y = 4) := by
      intro x hx y hy hxy
      have hx' := (hker x).1 hx
      have hy' := (hker y).1 hy
      exact f4Graph_closure hcl ((isRoot_iff_mem_artifactRoots (τ := Tag.F4) (v := x)).1 hx'.1)
        hx'.2 ((isRoot_iff_mem_artifactRoots (τ := Tag.F4) (v := y)).1 hy'.1) hy'.2 hxy
    have hij : (⟦⟨f4row R 0, hγk 0⟩⟧ : KernelComponent (rootCharHom a)) ≠
        ⟦⟨f4row R' 0, hγk' 0⟩⟧ := by
      intro h
      exact hshort ((f4Graph_length_of_mk_eq hcl' h).1 hlong)
    refine f4Graph_false_of_rank22 K hFr hg0C hg0 S hSD hm hK hD₁E δ hδ2 hδo hfix haD ha1 hij
      (γ := fun k => f4row R k) (γ' := fun k => f4row R' k) (fun k => ?_) (fun k => ?_) h01 h10
      (A := fun k => f4row A k) (A' := fun k => f4row A' k) hA hA' hD hD'
    · fin_cases k
      · exact ⟨hγk 0, rfl⟩
      · exact ⟨hγk 1, e01.symm⟩
    · fin_cases k
      · exact ⟨hγk' 0, rfl⟩
      · exact ⟨hγk' 1, e'01.symm⟩

end CFSG.HardMathSupport.Timmesfeld.CrossChar
