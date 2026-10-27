module

public import CFSG.Mathlib.FieldTheory.InfiniteUnitPowers
public import CFSG.RankThree.Chevalley.SteinbergBIRootSL2Tools
public import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Subnormal
public import CFSG.Blueprint.ChevalleyRootArtifact

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg.Adjoint
open scoped Matrix

theorem rootChar_zpow {τ : Tag} {L : Type} [Field L] (ζ : Lˣ) (x v : Fin τ.rank → ℤ) :
    rootChar (fun k => ζ ^ x k) v = ζ ^ (x ⬝ᵥ v) := by
  simp only [rootChar, dotProduct, ← zpow_mul]
  have key : ∀ s : Finset (Fin τ.rank), ∏ i ∈ s, ζ ^ (x i * v i) = ζ ^ (∑ i ∈ s, x i * v i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]
  exact key _

theorem isRoot_smul_single_iff {τ : Tag} (k : Fin τ.rank) (m : ℤ)
    (h : IsRoot τ (m • (Pi.single k 1 : Fin τ.rank → ℤ))) : m = 1 ∨ m = -1 := by
  have key : ∀ l ∈ τ.artifactRoots, ∀ k : ℕ, k < l.length →
      (∀ j : ℕ, j < l.length → j ≠ k → l.getD j 0 = 0) →
        l.getD k 0 = 1 ∨ l.getD k 0 = -1 ∨ l.getD k 0 = 0 := by
    cases τ <;> decide +kernel
  rw [isRoot_iff_mem_artifactRoots] at h
  have hlen : (List.ofFn (m • (Pi.single k 1 : Fin τ.rank → ℤ))).length = τ.rank :=
    List.length_ofFn
  have hget : ∀ j : ℕ, (hj : j < τ.rank) →
      (List.ofFn (m • (Pi.single k 1 : Fin τ.rank → ℤ))).getD j 0 =
        (m • (Pi.single k 1 : Fin τ.rank → ℤ)) ⟨j, hj⟩ := fun j hj => by
    rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hj), List.getElem_ofFn]
  have h1 := key _ h k.val (by rw [hlen]; exact k.2) fun j hj hjk => by
    rw [hlen] at hj
    rw [hget j hj]
    simp [Fin.ext_iff, hjk]
  rw [hget k.val k.2] at h1
  simp only [Fin.eta, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h1
  rcases h1 with h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1
  · exfalso
    subst h1
    rw [zero_smul] at h
    exact (isRoot_iff_mem_artifactRoots.2 h).ne_zero rfl

section RootSubgroups

variable {τ : Tag} {L : Type} [Field L]

theorem rootChar_eq_one_of_pinnedX_eq {γ δ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hδ : IsRoot τ δ) {s t : L} (hs : s ≠ 0) (h : pinnedX τ L γ s = pinnedX τ L δ t)
    (a : Fin τ.rank → Lˣ) (ha : rootChar a γ = 1) : rootChar a δ = 1 := by
  have ht : t ≠ 0 := by
    rintro rfl
    rw [pinnedX_zero] at h
    exact hs (pinnedX_injective τ L γ (h.trans (pinnedX_zero τ L γ).symm))
  have h1 := rootDiagUnit_conj_pinnedX a hγ s
  rw [ha, Units.val_one, one_mul, h, rootDiagUnit_conj_pinnedX a hδ t] at h1
  have h2 := pinnedX_injective τ L δ h1
  refine Units.ext ?_
  rw [Units.val_one]
  exact mul_right_cancel₀ ht (by rw [h2, one_mul])

theorem eq_zero_of_pinnedX_eq_neg {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) {s t : L}
    (h : pinnedX τ L γ s = pinnedX τ L (-γ) t) : s = 0 := by
  obtain ⟨ε, hε, hv⟩ := exists_rootSL2_vSL_eq (K := L) hγ
  have hu := rootSL2_uSL_eq (K := L) γ ((pinnedData τ γ).2.2 • s)
  have hs : (pinnedData τ γ).2.2 • ((pinnedData τ γ).2.2 • s) = s := by
    rcases pinnedSign_eq τ γ with h | h <;> rw [h] <;> simp
  rw [hs] at hu
  have hε' : ε * (ε * t) = t := by rw [← mul_assoc, hε, one_mul]
  have hv' := hv (ε * t)
  rw [hε'] at hv'
  rw [← hu, ← hv'] at h
  have h1 := congrArg (fun A : SL2 L => (A : Matrix (Fin 2) (Fin 2) L) 0 1)
    (CFSG.RankThree.Chevalley.rootSL2_injective_of_field γ h)
  simp only [uSL, vSL, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at h1
  rcases pinnedSign_eq τ γ with he | he <;> rw [he] at h1 <;> simpa using h1

theorem eq_of_pinnedX_mem_rootSubgroup [Infinite L] {γ δ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hδ : IsRoot τ δ) {s : L} (hs : s ≠ 0) (h : pinnedX τ L γ s ∈ rootSubgroup τ L δ) :
    γ = δ := by
  classical
  obtain ⟨t, ht⟩ := mem_rootSubgroup.1 h
  have hker := rootChar_eq_one_of_pinnedX_eq hγ hδ hs ht.symm
  obtain ⟨w, k, rfl⟩ := isRoot_iff_exists_smul_single.1 hγ
  set ε := w⁻¹ • δ with hε
  have hεj : ∀ j, j ≠ k → ε j = 0 := by
    intro j hjk
    by_contra hne
    obtain ⟨ζ, hζ⟩ := exists_units_zpow_ne_one (L := L) hne
    set b : Fin τ.rank → Lˣ := Function.update 1 j ζ with hb
    have hbk : rootChar b (Pi.single k 1) = 1 := by
      rw [CTTorus.rootChar_single, hb, Function.update_of_ne hjk.symm, Pi.one_apply]
    have h1 := hker (weylTuple w b) (by rw [rootChar_weylTuple, inv_smul_smul, hbk])
    rw [rootChar_weylTuple] at h1
    have h2 : rootChar b ε = ζ ^ ε j := by
      rw [rootChar]
      rw [Finset.prod_eq_single j (fun i _ hij => by
        rw [hb, Function.update_of_ne hij, Pi.one_apply, one_zpow]) (by simp)]
      rw [hb, Function.update_self]
    rw [← hε, h2] at h1
    exact hζ h1
  have hεe : ε = ε k • (Pi.single k 1 : Fin τ.rank → ℤ) := by
    funext j
    by_cases hj : j = k
    · subst hj
      simp
    · rw [hεj j hj]
      simp [hj]
  have hεroot : IsRoot τ ε := (isRoot_smul_iff w⁻¹).2 hδ
  rw [hεe] at hεroot
  rcases isRoot_smul_single_iff k _ hεroot with h1 | h1
  · rw [h1, one_smul] at hεe
    rw [hε] at hεe
    rw [← hεe, smul_inv_smul]
  · exfalso
    rw [h1, neg_one_smul] at hεe
    have hδe : δ = -(w • (Pi.single k 1 : Fin τ.rank → ℤ)) := by
      rw [← smul_neg, ← hεe, hε, smul_inv_smul]
    rw [hδe] at ht
    exact hs (eq_zero_of_pinnedX_eq_neg hγ ht.symm)

theorem eq_of_rootSubgroup_eq [Infinite L] {γ δ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hδ : IsRoot τ δ) (h : rootSubgroup τ L γ = rootSubgroup τ L δ) : γ = δ := by
  refine eq_of_pinnedX_mem_rootSubgroup hγ hδ (one_ne_zero : (1 : L) ≠ 0) ?_
  rw [← h]
  exact mem_rootSubgroup.2 ⟨1, rfl⟩

end RootSubgroups

section Untwisted

variable {τ : Tag} {L : Type} [Field L]

theorem LangDatum.exists_frob_of_untwisted (D : LangDatum τ L) (hτ : ∀ t : TwistTag, t.tag ≠ τ) :
    ∃ Fr : L →+* L, (∀ c, Fr c = c ^ D.q) ∧ D.Φ = Units.map (entrywiseHom Fr) := by
  obtain ⟨Fr, hFr, P, hP, hΦ⟩ := D.steinberg
  refine ⟨Fr, hFr, ?_⟩
  rcases hP with rfl | ⟨t, ht, -⟩
  · ext1 g
    rw [hΦ, one_mul, inv_one, mul_one]
  · exact absurd ht (hτ t)

theorem LangDatum.map_step_rootSubgroup (D : LangDatum τ L) {Fr : L →+* L}
    (hFr : Function.Surjective Fr) (hΦ : D.Φ = Units.map (entrywiseHom Fr)) {w : WeylGroup τ}
    (hn : D.n = canonicalRep (coxeterSystem τ) L w) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    (rootSubgroup τ L γ).map D.step = rootSubgroup τ L (w • γ) := by
  have h1 : (rootSubgroup τ L γ).map (Units.map (entrywiseHom Fr)) = rootSubgroup τ L γ := by
    rw [rootSubgroup, MonoidHom.map_closure, ← Set.range_comp]
    congr 1
    ext g
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨Fr c, (units_map_entrywiseHom_pinnedX Fr γ c).symm⟩
    · rintro ⟨d, rfl⟩
      obtain ⟨c, rfl⟩ := hFr d
      exact ⟨c, units_map_entrywiseHom_pinnedX Fr γ c⟩
  rw [LangDatum.step, ← Subgroup.map_map, hΦ, h1, hn]
  exact (canonical_weyl_root_transport τ L).2.1 w γ hγ

theorem LangSetup.rho_eq_smul_of_frob {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup τ L p) {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q)
    (hΦ : S.D.Φ = Units.map (entrywiseHom Fr)) {w : WeylGroup τ}
    (hn : S.D.n = canonicalRep (coxeterSystem τ) L w) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    S.ρ γ = w • γ := by
  have hq : 0 < S.D.q := Nat.pos_of_ne_zero fun h => by
    have h0 := hFr 0
    rw [map_zero, h, pow_zero] at h0
    exact zero_ne_one h0
  have hsurj : Function.Surjective Fr := fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y hq
    exact ⟨x, by rw [hFr, hx]⟩
  have h1 := S.frob.map_rootSubgroup γ hγ
  rw [S.D.map_step_rootSubgroup hsurj hΦ hn hγ] at h1
  exact (eq_of_rootSubgroup_eq ((isRoot_smul_iff w).2 hγ) ((S.frob.isRoot_iff γ).2 hγ) h1).symm

theorem LangSetup.rho_eq_smul [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
    (hτ : ∀ t : TwistTag, t.tag ≠ τ) {w : WeylGroup τ}
    (hn : S.D.n = canonicalRep (coxeterSystem τ) L w) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    S.ρ γ = w • γ := by
  obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted hτ
  exact S.rho_eq_smul_of_frob hFr hΦ hn hγ

end Untwisted

section Orbit

variable {τ : Tag} {L : Type} [Field L]

theorem iform_eq_zero_of_class_ne {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {β γ : Fin τ.rank → ℤ}
    (hβ : β ∈ kernelRoots χ) (hγ : γ ∈ kernelRoots χ)
    (h : (⟦⟨β, hβ⟩⟧ : KernelComponent χ) ≠ ⟦⟨γ, hγ⟩⟧) : iform β γ = 0 := by
  by_contra hne
  apply h
  exact Quotient.sound (Relation.EqvGen.rel _ _ (by
    change β ⬝ᵥ (τ.symmetrizedCartan *ᵥ γ) ≠ 0
    rw [dotProduct_mulVec_eq_iform]
    exact hne))

theorem LangSetup.rho_mem_componentRootsT [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
    {a : Fin τ.rank → Lˣ} (haT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a))
    (v : WeylGroup τ) {J : Set (Fin τ.rank)}
    (hΨ : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots τ J) {N : ℕ}
    (hN : ∀ s : Finset (Fin τ.rank → ℤ),
      (∀ β ∈ s, IsRoot τ β ∧ ∀ α ∈ parabolicRoots τ J, iform β α = 0) → s.card ≤ N)
    (hbig : ∃ s : Finset (Fin τ.rank → ℤ), (∀ α ∈ s, α ∈ parabolicRoots τ J) ∧ N < s.card) :
    ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i := by
  classical
  have hker : ∀ γ ∈ kernelRoots (rootCharHom a), S.ρ γ ∈ kernelRoots (rootCharHom a) := by
    rintro γ ⟨hγ, hγ1⟩
    refine ⟨(S.frob.isRoot_iff γ).2 hγ, ?_⟩
    change rootChar a (S.ρ γ) = 1
    change rootChar a γ = 1 at hγ1
    rw [S.frob.rootChar_eq a haT γ hγ, hγ1, one_pow]
  have hform := S.frob.iform_eq
  have hrel : ∀ x y : kernelRoots (rootCharHom a),
      (x : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (y : Fin τ.rank → ℤ)) ≠ 0 →
        S.ρ x ⬝ᵥ (τ.symmetrizedCartan *ᵥ S.ρ y) ≠ 0 := by
    intro x y h
    rwa [dotProduct_mulVec_eq_iform, hform, ← dotProduct_mulVec_eq_iform]
  let σ : kernelRoots (rootCharHom a) → kernelRoots (rootCharHom a) :=
    fun x => ⟨S.ρ x, hker x x.2⟩
  have hsame : ∀ γ (hγ : γ ∈ kernelRoots (rootCharHom a)),
      (⟦⟨γ, hγ⟩⟧ : KernelComponent (rootCharHom a)) = i →
      ∀ δ (hδ : δ ∈ kernelRoots (rootCharHom a)),
      (⟦⟨δ, hδ⟩⟧ : KernelComponent (rootCharHom a)) = i →
      (⟦σ ⟨γ, hγ⟩⟧ : KernelComponent (rootCharHom a)) = ⟦σ ⟨δ, hδ⟩⟧ := by
    intro γ hγk hγi δ hδk hδi
    apply Quotient.sound
    exact eqvGen_map σ (fun x y h => hrel x y h)
      ((kernelComponent_eq_iff _ _).1 (hγi.trans hδi.symm))
  by_contra hcon
  push Not at hcon
  obtain ⟨γ₀, hγ₀, hργ₀⟩ := hcon
  obtain ⟨hγ₀k, hγ₀i⟩ := hγ₀
  have hout : ∀ γ (hγ : γ ∈ componentRoots (rootCharHom a) i),
      (⟦σ ⟨γ, hγ.1⟩⟧ : KernelComponent (rootCharHom a)) ≠ i := by
    intro γ hγ h
    apply hργ₀
    have h2 := (hsame γ hγ.1 hγ.2 γ₀ hγ₀k hγ₀i).symm.trans h
    exact ⟨hker γ₀ hγ₀k, h2⟩
  have horth : ∀ γ ∈ componentRoots (rootCharHom a) i, ∀ δ ∈ componentRoots (rootCharHom a) i,
      iform (S.ρ γ) δ = 0 := by
    intro γ hγ δ hδ
    refine iform_eq_zero_of_class_ne (hker γ hγ.1) hδ.1 ?_
    rw [hδ.2]
    exact hout γ hγ
  obtain ⟨s, hs, hcard⟩ := hbig
  set f : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ) := fun α => v⁻¹ • S.ρ (v • α) with hf
  have hfinj : Function.Injective f := fun x y h => by
    have h1 := congrArg (fun z => v • z) h
    simp only [hf, smul_inv_smul] at h1
    exact smul_left_cancel v (S.ρ.injective h1)
  have hmemΨ : ∀ α ∈ parabolicRoots τ J, v • α ∈ componentRoots (rootCharHom a) i := by
    intro α hα
    rw [hΨ]
    exact ⟨α, hα, rfl⟩
  have h1 := hN (s.image f) (by
    intro β hβ
    obtain ⟨α, hα, rfl⟩ := Finset.mem_image.1 hβ
    have hαJ := hs α hα
    refine ⟨(isRoot_smul_iff v⁻¹).2 ((S.frob.isRoot_iff _).2 ((isRoot_smul_iff v).2 hαJ.1)),
      fun α' hα' => ?_⟩
    rw [hf]
    change iform (v⁻¹ • S.ρ (v • α)) α' = 0
    have := iform_smul v (v⁻¹ • S.ρ (v • α)) α'
    rw [smul_inv_smul] at this
    rw [← this]
    exact horth _ (hmemΨ α hαJ) _ (hmemΨ α' hα'))
  rw [Finset.card_image_of_injective _ hfinj] at h1
  omega

end Orbit

end CFSG.HardMathSupport.Timmesfeld.LangTorus
