module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXLangSel2
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256j

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.DX

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141f

section GroupTheory

open scoped commutatorElement

private theorem smallA1_s3 {G : Type*} [Group G] (V : Subgroup G) (hV : Nat.card V ∣ 6)
    {u v : G} (hu : u ∈ V) (hv : v ∈ V) (hu2 : u ^ 2 = 1) (hu1 : u ≠ 1) (hv2 : v ^ 2 = 1)
    (huv3 : (u * v) ^ 3 = 1) (huv1 : u * v ≠ 1) :
    Nat.card V = 6 ∧ ∀ z ∈ V, (∀ x ∈ ⁅V, V⁆, Commute z x) → (∃ n : ℕ, z ^ 2 ^ n = 1) → z = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hu_ord : orderOf u = 2 := orderOf_eq_prime hu2 hu1
  have huv_ord : orderOf (u * v) = 3 := orderOf_eq_prime huv3 huv1
  have h2 : 2 ∣ Nat.card V := by
    have := V.orderOf_dvd_natCard hu
    rwa [hu_ord] at this
  have h3 : 3 ∣ Nat.card V := by
    have := V.orderOf_dvd_natCard (V.mul_mem hu hv)
    rwa [huv_ord] at this
  have hcard : Nat.card V = 6 :=
    Nat.dvd_antisymm hV (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3)
  refine ⟨hcard, fun z hz hzc ⟨n, hn⟩ => ?_⟩
  by_contra hz1
  have hzo : orderOf z = 2 := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hn)
    have h6 : orderOf z ∣ 6 := by
      have := V.orderOf_dvd_natCard hz
      rwa [hcard] at this
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · interval_cases k
      · exact absurd (orderOf_eq_one_iff.1 (by simpa using hk)) hz1
      · simpa using hk
    · exfalso
      have h4 : 2 ^ 2 ∣ orderOf z := hk ▸ pow_dvd_pow 2 hk2
      have h46 := h4.trans h6
      norm_num at h46
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hu2)
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hv2)
  have key : ∀ t : G, t = t ^ 3 * (t ^ 2)⁻¹ := fun t => by group
  have hw : ⁅u, v⁆ = (u * v) ^ 2 := by
    rw [commutatorElement_def, hui, hvi, sq]
    group
  have hwV : ⁅u, v⁆ ∈ ⁅V, V⁆ := Subgroup.commutator_mem_commutator hu hv
  have hw3 : (⁅u, v⁆ : G) ^ 3 = 1 := by
    rw [hw, ← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, huv3, one_pow]
  have hw1 : (⁅u, v⁆ : G) ≠ 1 := by
    intro h
    rw [hw] at h
    apply huv1
    calc u * v = (u * v) ^ 3 * ((u * v) ^ 2)⁻¹ := key (u * v)
      _ = 1 := by rw [huv3, h]; simp
  have hw_ord : orderOf (⁅u, v⁆ : G) = 3 := orderOf_eq_prime hw3 hw1
  have hcomm : Commute z ⁅u, v⁆ := hzc _ hwV
  have hzw : orderOf (z * ⁅u, v⁆) = 6 := by
    rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hzo, hw_ord]; norm_num), hzo, hw_ord]
  have hzwV : z * ⁅u, v⁆ ∈ V := V.mul_mem hz (Subgroup.commutator_le_self V hwV)
  haveI : Finite V := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hcyc : IsCyclic V :=
    isCyclic_of_orderOf_eq_card (⟨z * ⁅u, v⁆, hzwV⟩ : V)
      (by rw [Subgroup.orderOf_mk, hzw, hcard])
  have huvc : u * v = v * u := by
    have := (IsCyclic.isMulCommutative (α := V)).is_comm.comm (⟨u, hu⟩ : V) ⟨v, hv⟩
    exact congrArg Subtype.val this
  apply huv1
  have h1 : (u * v) ^ 2 = 1 := by
    rw [(show Commute u v from huvc).mul_pow, hu2, hv2, one_mul]
  calc u * v = (u * v) ^ 3 * ((u * v) ^ 2)⁻¹ := key (u * v)
    _ = 1 := by rw [huv3, h1]; simp

end GroupTheory

section SL2

private theorem smallA1_sl2 {F : Type} [Field F] [CharP F 2] (hF : ∀ c : F, c = 0 ∨ c = 1) :
    Nat.card (SL2 F) = 6 ∧ (uSL (1 : F)) ^ 2 = 1 ∧ uSL (1 : F) ≠ 1 ∧ (vSL (1 : F)) ^ 2 = 1 ∧
      (uSL (1 : F) * vSL 1) ^ 3 = 1 ∧ uSL (1 : F) * vSL 1 ≠ 1 := by
  classical
  have h11 : (1 : F) + 1 = 0 := CharTwo.add_self_eq_zero 1
  have hU : ((uSL (1 : F) : SL2 F) : Matrix (Fin 2) (Fin 2) F) = !![1, 1; 0, 1] := rfl
  have hV : ((vSL (1 : F) : SL2 F) : Matrix (Fin 2) (Fin 2) F) = !![1, 0; 1, 1] := rfl
  have hx3 : ∀ x : SL2 F, x ^ 3 = x * x * x := fun x => by rw [pow_succ, pow_succ, pow_one]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · haveI : Finite F := Finite.of_surjective (fun b : Bool => bif b then (1 : F) else 0)
      (fun c => by
        rcases hF c with rfl | rfl
        · exact ⟨false, rfl⟩
        · exact ⟨true, rfl⟩)
    haveI : Fintype F := Fintype.ofFinite F
    have hc : Fintype.card F = 2 := by
      rw [← Finset.card_univ]
      have : (Finset.univ : Finset F) = {0, 1} := by
        ext c
        simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
        exact hF c
      rw [this, Finset.card_pair zero_ne_one]
    have hcard := Matrix.card_SL_field (𝔽 := F) 2
    rw [hc] at hcard
    simpa [Fin.prod_univ_two] using hcard
  · rw [sq]
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul, hU, Matrix.SpecialLinearGroup.coe_one]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h11]
  · intro h
    have := congrArg (fun g : SL2 F => (g : Matrix (Fin 2) (Fin 2) F) 0 1) h
    simp [hU] at this
  · rw [sq]
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul, hV, Matrix.SpecialLinearGroup.coe_one]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h11]
  · rw [hx3]
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, hU, hV, Matrix.SpecialLinearGroup.coe_one]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h11]
  · intro h
    have := congrArg (fun g : SL2 F => (g : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, hU, hV] at this
    simp [Matrix.mul_apply, Fin.sum_univ_two, h11] at this

end SL2


section Geometry

open scoped commutatorElement
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256j

private theorem smallA1_rootSpan_le {τ : Tag} {L : Type} [Field L]
    (Ψ : Set (Fin τ.rank → ℤ)) : rootSpan τ L Ψ ≤ adjointGroup τ L :=
  iSup₂_le fun γ _ => rootSubgroup_le_adjointGroup γ

private theorem smallA1_two_mem {τ : Tag} {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K = 2) {p₀ : ℕ} (S : LangSetup τ (AlgebraicClosure K) p₀)
    {a : Fin τ.rank → (AlgebraicClosure K)ˣ} (i : KernelComponent (rootCharHom a))
    (σ : AlgebraicClosure K ≃+* AlgebraicClosure K) (z : ModGL τ (AlgebraicClosure K))
    (hnorm : ∀ j : KernelComponent (rootCharHom a), ∀ g : ModGL τ (AlgebraicClosure K),
      g ∈ rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) j) ↔
        z * g * z⁻¹ ∈ rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) j))
    (hz : ∀ g ∈ rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) i),
      iterHom S.D.step 1 (z * g * z⁻¹) = z * frobGL σ g * z⁻¹)
    {y : ModGL τ (AlgebraicClosure K)}
    (hy : y ∈ rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) i))
    (hyF : iterHom S.D.step 1 y = y) {n : ℕ} (hn : y ^ 2 ^ n = 1) :
    z⁻¹ * y * z ∈ CQ σ i := by
  classical
  set v := z⁻¹ * y * z with hv
  have hzv : z * v * z⁻¹ = y := by rw [hv]; group
  have hvS : v ∈ rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) i) :=
    (hnorm i v).2 (by rw [hzv]; exact hy)
  have hvF : frobGL σ v = v := by
    have h1 := hz v hvS
    rw [hzv, hyF] at h1
    have h2 : frobGL σ v = z⁻¹ * y * z := by rw [h1]; group
    rw [h2]
  have hvn : v ^ 2 ^ n = 1 := by
    have h1 : v ^ 2 ^ n = (MulAut.conj z⁻¹) (y ^ 2 ^ n) := by
      rw [map_pow]
      congr 1
    rw [h1, hn, map_one]
  have hvU : v ∈ unionRootSpan (AlgebraicClosure K) (rootCharHom a)
      ({i} : Set (KernelComponent (rootCharHom a))) := by
    rw [unionRootSpan_singleton_charQ]
    exact hvS
  obtain ⟨t, ht, x, hx, hvtx, htF⟩ :=
    CFSG.HardMathSupport.Timmesfeld.LangTorus.exists_decomp (σ := σ) hvU
      (one_mem _) (by rw [one_mul]; exact hvF)
  have hcen1 : ∀ w ∈ unionRootSpan (AlgebraicClosure K) (rootCharHom a)
      ({i} : Set (KernelComponent (rootCharHom a))), w * 1 = 1 * w := fun _ _ => by
    rw [mul_one, one_mul]
  have hn' := torus_normalizes_CQ (σ := σ) ht hcen1 htF
  have htN' : t ∈ Subgroup.normalizer (CQ σ i : Set (ModGL τ (AlgebraicClosure K))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨fun hw => hn'.1 w hw, fun hw => ?_⟩
    have h1 := hn'.2 _ hw
    have e1 : t⁻¹ * (t * w * t⁻¹) * t = w := by group
    rwa [e1] at h1
  obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (unionTorus_le_torusGroup ht)
  obtain ⟨Nt, hNt, hlN⟩ := exists_coprime_pow_eq_one_algClosure Nat.prime_two hK2 l
  have htN : t ^ Nt = 1 := by
    rw [hl]
    exact rootDiagUnit_pow_eq_one_of_forall hlN
  rw [hvtx]
  exact mem_of_charElem_of_mul htN' htN hNt hx (by rw [← hvtx]; exact hvn)

private theorem smallA1_conj_mem {τ : Tag} {K : Type} [Field K] {p₀ : ℕ}
    (S : LangSetup τ (AlgebraicClosure K) p₀) {a : Fin τ.rank → (AlgebraicClosure K)ˣ}
    (i : KernelComponent (rootCharHom a))
    (σ : AlgebraicClosure K ≃+* AlgebraicClosure K) (z : ModGL τ (AlgebraicClosure K))
    (hnorm : ∀ j : KernelComponent (rootCharHom a), ∀ g : ModGL τ (AlgebraicClosure K),
      g ∈ rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) j) ↔
        z * g * z⁻¹ ∈ rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) j))
    (hz : ∀ g ∈ rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) i),
      iterHom S.D.step 1 (z * g * z⁻¹) = z * frobGL σ g * z⁻¹)
    {x : ModGL τ (AlgebraicClosure K)} (hx : x ∈ CQ σ i) :
    z * x * z⁻¹ ∈ orbitGroup S i := by
  have hxS : x ∈ rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) i) :=
    CQ_le_rootSpan σ i hx
  have hconj := (hnorm i x).1 hxS
  have hfix : S.D.step (z * x * z⁻¹) = z * x * z⁻¹ := by
    have h1 := hz x hxS
    rw [frobGL_eq_self_of_mem_CQ σ i hx] at h1
    exact h1
  have hsub : componentRoots (rootCharHom a) i ⊆ rationalRoots S.ρ (rootCharHom a) i :=
    fun γ hγ => ⟨0, γ, hγ, rfl⟩
  exact Subgroup.mem_inf.2 ⟨rootSpan_mono hsub hconj,
    Subgroup.mem_inf.2 ⟨smallA1_rootSpan_le _ hconj, hfix⟩⟩

private theorem smallA1_main {τ : Tag} {K : Type} [Field K] [Finite K] (hK2 : ringChar K = 2)
    {p₀ : ℕ} (S : LangSetup τ (AlgebraicClosure K) p₀) (hq2 : S.D.q = 2)
    {a : Fin τ.rank → (AlgebraicClosure K)ˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a))
    (hq3 : S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) ≤ 3)
    (hn2 : (componentRoots (rootCharHom a) i).ncard = 2) :
    Nat.card (twoClosure S i) = 6 ∧
      ∀ z ∈ twoClosure S i, (∀ x ∈ ⁅twoClosure S i, twoClosure S i⁆, Commute z x) →
        (∃ n : ℕ, z ^ 2 ^ n = 1) → z = 1 := by
  classical
  haveI : CharP K 2 := hK2 ▸ ringChar.charP K
  haveI hL2 : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨hs0, hs, -⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)
  have hs1 : s = 1 := by
    rw [hq2] at hq3
    by_contra hne
    have h4 : 4 ≤ 2 ^ s :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rw [hs1, Function.iterate_one] at hs
  have hΨ := isRootComponent_componentRoots (χ := rootCharHom a) i
  obtain ⟨x, y, hxy, hC⟩ := Set.ncard_eq_two.1 hn2
  have hx : x ∈ componentRoots (rootCharHom a) i := by
    rw [hC]
    exact Set.mem_insert _ _
  have hx0 : x ≠ 0 := (hΨ.isRoot x hx).ne_zero
  have hnxy : -x = y := by
    have hnx := hΨ.neg_mem x hx
    rw [hC] at hnx
    rcases hnx with h | h
    · exfalso
      apply hx0
      funext k
      have hk := congrFun h k
      simp only [Pi.neg_apply] at hk
      simp only [Pi.zero_apply]
      omega
    · exact h
  have hCeq : componentRoots (rootCharHom a) i = {x, -x} := by rw [hC, hnxy]
  have hrank : ∀ δ ∈ componentRoots (rootCharHom a) i, δ = x ∨ δ = -x := by
    intro δ hδ
    rw [hCeq] at hδ
    rcases hδ with h | h
    · exact Or.inl h
    · exact Or.inr (Set.mem_singleton_iff.1 h)
  have hαr : IsRoot τ x := hΨ.isRoot x hx
  have hmaps : ∀ γ ∈ componentRoots (rootCharHom a) i,
      S.ρ γ ∈ componentRoots (rootCharHom a) i := by
    intro γ hγ
    rw [← hs]
    exact ⟨γ, hγ, rfl⟩
  have hrat : rationalRoots S.ρ (rootCharHom a) i = componentRoots (rootCharHom a) i := by
    refine Set.Subset.antisymm ?_ fun γ hγ => ⟨0, γ, hγ, rfl⟩
    rintro _ ⟨k, δ, hδ, rfl⟩
    induction k with
    | zero => exact hδ
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact hmaps _ ih
  have hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[1]) := by
    rw [Function.iterate_one]
    have hρα : S.ρ x = x ∨ S.ρ x = -x := by
      have h1 := hmaps x hx
      rw [hCeq] at h1
      rcases h1 with h | h
      · exact Or.inl h
      · exact Or.inr (Set.mem_singleton_iff.1 h)
    rcases hρα with h | h
    · refine ⟨1, Subgroup.one_mem _, fun γ hγ => ?_⟩
      rw [hCeq] at hγ
      rcases hγ with hγ | hγ
      · rw [hγ, h, one_smul]
      · rw [Set.mem_singleton_iff] at hγ
        rw [hγ, S.frob.neg_eq, h, one_smul]
    · refine ⟨rootReflection x, Subgroup.subset_closure ⟨x, hx, rfl⟩, fun γ hγ => ?_⟩
      rw [hCeq] at hγ
      rcases hγ with hγ | hγ
      · rw [hγ, h, rootReflection_smul_self hαr]
      · rw [Set.mem_singleton_iff] at hγ
        rw [hγ, S.frob.neg_eq, h, smul_neg, rootReflection_smul_self hαr]
  obtain ⟨σ, z, hσ, hnorm, hz⟩ := exists_untwistT S hT i (s := 1) Nat.one_pos hinner
  have hσ2 : ∀ c, σ c = c ^ 2 := fun c => by rw [hσ, hq2, pow_one]
  haveI hcharF : CharP (fixSubfield σ) 2 :=
    RingHom.charP (fixSubfield σ).subtype (fixSubfield σ).subtype.injective 2
  have hF : ∀ c : fixSubfield σ, c = 0 ∨ c = 1 := by
    intro c
    have h1 : σ (c : AlgebraicClosure K) = c := c.2
    rw [hσ2] at h1
    have h3 : (c : AlgebraicClosure K) * ((c : AlgebraicClosure K) - 1) = 0 := by
      linear_combination h1
    rcases mul_eq_zero.1 h3 with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext (sub_eq_zero.1 h))
  obtain ⟨hSL6, hu2, hu1, hv2, huv3, huv1⟩ := smallA1_sl2 (F := fixSubfield σ) hF
  let ι : fixSubfield σ →+* AlgebraicClosure K := (fixSubfield σ).subtype
  let Θ₀ : SL2 (fixSubfield σ) →* ModGL τ (AlgebraicClosure K) :=
    (baseChangeGL ι).comp (rootSL2 τ (fixSubfield σ) x)
  let Θ : SL2 (fixSubfield σ) →* ModGL τ (AlgebraicClosure K) :=
    (MulAut.conj z).toMonoidHom.comp Θ₀
  have hΘ₀inj : Function.Injective Θ₀ := by
    have h1 := (CFSG.RankThree.Chevalley.even_Chevalley_pinned_root_SL2_maps τ (fixSubfield σ)
      hαr).1
    intro A B hAB
    exact h1 (baseChangeGL_injective ι hAB)
  have hΘinj : Function.Injective Θ := by
    intro A B hAB
    apply hΘ₀inj
    have h : z * Θ₀ A * z⁻¹ = z * Θ₀ B * z⁻¹ := hAB
    exact mul_left_cancel (mul_right_cancel h)
  have hΘ₀u : Θ₀ (uSL 1) = pinnedX τ (AlgebraicClosure K) x 1 := by
    show baseChangeGL ι (rootSL2 τ (fixSubfield σ) x (uSL 1)) = _
    rw [CFSG.RankThree.Chevalley.rootSL2_uSL_of_charTwo hαr, baseChangeGL_pinnedX, map_one]
  have hΘ₀v : Θ₀ (vSL 1) = pinnedX τ (AlgebraicClosure K) (-x) 1 := by
    show baseChangeGL ι (rootSL2 τ (fixSubfield σ) x (vSL 1)) = _
    rw [CFSG.RankThree.Chevalley.rootSL2_vSL_of_charTwo hαr, baseChangeGL_pinnedX, map_one]
  have hxU : x ∈ unionRoots (rootCharHom a) ({i} : Set (KernelComponent (rootCharHom a))) := by
    rw [unionRoots_singleton]
    exact hx
  have hnxU : -x ∈ unionRoots (rootCharHom a) ({i} : Set (KernelComponent (rootCharHom a))) := by
    rw [unionRoots_singleton]
    exact hΨ.neg_mem x hx
  have hσ1 : σ 1 = 1 := map_one σ
  have hu_orb : Θ (uSL 1) ∈ orbitGroup S i := by
    have h := smallA1_conj_mem S i σ z hnorm hz (pinnedX_mem_CQ hxU hσ1)
    have e : Θ (uSL 1) = z * pinnedX τ (AlgebraicClosure K) x 1 * z⁻¹ := by
      show z * Θ₀ (uSL 1) * z⁻¹ = _
      rw [hΘ₀u]
    rw [e]
    exact h
  have hv_orb : Θ (vSL 1) ∈ orbitGroup S i := by
    have h := smallA1_conj_mem S i σ z hnorm hz (pinnedX_mem_CQ hnxU hσ1)
    have e : Θ (vSL 1) = z * pinnedX τ (AlgebraicClosure K) (-x) 1 * z⁻¹ := by
      show z * Θ₀ (vSL 1) * z⁻¹ = _
      rw [hΘ₀v]
    rw [e]
    exact h
  have hu2' : (Θ (uSL 1)) ^ 2 = 1 := by rw [← map_pow, hu2, map_one]
  have hv2' : (Θ (vSL 1)) ^ 2 = 1 := by rw [← map_pow, hv2, map_one]
  have hu1' : Θ (uSL 1) ≠ 1 := fun h => hu1 (hΘinj (by rw [h, map_one]))
  have huv3' : (Θ (uSL 1) * Θ (vSL 1)) ^ 3 = 1 := by
    rw [← map_mul, ← map_pow, huv3, map_one]
  have huv1' : Θ (uSL 1) * Θ (vSL 1) ≠ 1 := fun h => huv1 (hΘinj (by rw [map_mul, h, map_one]))
  have hu_mem : Θ (uSL 1) ∈ twoClosure S i :=
    Subgroup.subset_closure ⟨hu_orb, 1, by rw [pow_one]; exact hu2'⟩
  have hv_mem : Θ (vSL 1) ∈ twoClosure S i :=
    Subgroup.subset_closure ⟨hv_orb, 1, by rw [pow_one]; exact hv2'⟩
  have hCQ_le : CQ σ i ≤ Θ₀.range := by
    rw [CQ_eq_map]
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨A, hA⟩ := componentRootSpan_le_range_of_rank_one (K := fixSubfield σ) i hx hrank hy
    exact ⟨A, by show baseChangeGL ι (rootSL2 τ (fixSubfield σ) x A) = _; rw [hA]⟩
  have hV_le : twoClosure S i ≤ Θ.range := by
    refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨hg, n, hn⟩
    have hg' : g ∈ rootSpan τ (AlgebraicClosure K) (rationalRoots S.ρ (rootCharHom a) i) ⊓
        S.D.model := hg
    obtain ⟨hgA, hgM⟩ := Subgroup.mem_inf.1 hg'
    rw [hrat] at hgA
    have hgF : iterHom S.D.step 1 g = g := (Subgroup.mem_inf.1 hgM).2
    have hv := smallA1_two_mem hK2 S i σ z hnorm hz hgA hgF hn
    obtain ⟨A, hA⟩ := hCQ_le hv
    refine ⟨A, ?_⟩
    show z * Θ₀ A * z⁻¹ = g
    rw [hA]
    group
  have hV6 : Nat.card (twoClosure S i) ∣ 6 := by
    have h1 := Subgroup.card_dvd_of_le hV_le
    have h2 := Subgroup.card_range_dvd Θ
    rw [hSL6] at h2
    exact h1.trans h2
  exact smallA1_s3 (twoClosure S i) hV6 hu_mem hv_mem hu2' hu1' hv2' huv3' huv1'

theorem smallFactsA1 (p : ℕ) : SmallFactsA1 p := by
  intro τ K _ _ hK2 p₀ S a hq2 _ hT i ⟨hq3, hn2⟩
  obtain ⟨hcard, hz⟩ := smallA1_main hK2 S hq2 hT i hq3 hn2
  refine ⟨hz, ?_, fun _ h8 => ?_⟩
  · rw [hcard]
    norm_num
  · rw [hcard] at h8
    omega

end Geometry

end CFSG.LocalAnalysis.GLTheoremA.T263.DX
