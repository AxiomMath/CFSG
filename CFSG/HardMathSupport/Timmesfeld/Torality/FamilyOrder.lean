module

public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.HardMathSupport.Timmesfeld.Torality.Conjugacy

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.Torality

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise

set_option linter.unusedSectionVars false

variable {τ : Tag} {K : Type} [Field K] {ι : Type}

section


theorem card_rootSpan_familyKernel_inter [Finite K] (a : ι → Fin τ.rank → Kˣ)
    {S : Set (Fin τ.rank → ℤ)} (hS : S.Finite) (hSroot : ∀ α ∈ S, IsRoot τ α)
    (hcoll : ∀ {m : ℕ} (α : Fin m → Fin τ.rank → ℤ), Function.Injective α → Set.range α = S →
      Set.BijOn (fun c : Fin m → K => (List.ofFn fun k => pinnedX τ K (α k) (c k)).prod)
        Set.univ (rootSpan τ K S)) :
    Nat.card (rootSpan τ K (familyKernel a ∩ S)) = Nat.card K ^ (familyKernel a ∩ S).ncard := by
  classical
  have : Finite S := hS.to_subtype
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin S
  set α : Fin n → Fin τ.rank → ℤ := fun k => (e.symm k : Fin τ.rank → ℤ) with hαdef
  have hα : Function.Injective α := fun k k' h => e.symm.injective (Subtype.ext h)
  have hrange : Set.range α = S := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact (e.symm k).2
    · intro hx
      exact ⟨e ⟨x, hx⟩, by simp [α]⟩
  have hαS : ∀ k, α k ∈ S := fun k => (e.symm k).2
  have hbij := hcoll α hα hrange
  set f : (Fin n → K) → ModGL τ K := fun c => (List.ofFn fun k => pinnedX τ K (α k) (c k)).prod
    with hf
  set p : Fin n → Prop := fun k => ∀ i, rootChar (a i) (α k) = 1 with hp
  have hspan : ∀ u, u ∈ rootSpan τ K (familyKernel a ∩ S) ↔
      ∃ c : Fin n → K, (∀ k, ¬ p k → c k = 0) ∧ f c = u := by
    intro u
    constructor
    · intro hu
      have huS : u ∈ rootSpan τ K S := rootSpan_mono Set.inter_subset_right hu
      obtain ⟨c, -, hcu⟩ := hbij.2.2 huS
      refine ⟨c, ?_, hcu⟩
      have hfix : ∀ i, rootDiagUnit τ (a i) * f c * (rootDiagUnit τ (a i))⁻¹ = f c := by
        intro i
        have hle : rootSpan τ K (familyKernel a ∩ S) ≤
            Subgroup.centralizer {rootDiagUnit τ (a i)} :=
          rootSpan_le_centralizer (a i) (S := familyKernel a ∩ S) fun β hβ => ⟨hβ.1.1, hβ.1.2 i⟩
        exact conj_eq_iff_mem_centralizer.2 (hle (hcu ▸ hu))
      exact coords_eq_zero_of_conj_eq_family a α (fun k => hSroot _ (hαS k))
        (fun c c' h => hbij.2.1 (Set.mem_univ _) (Set.mem_univ _) h) hfix
    · rintro ⟨c, hc, rfl⟩
      refine Subgroup.list_prod_mem _ fun x hx => ?_
      obtain ⟨k, rfl⟩ := (List.mem_ofFn' _ _).1 hx
      by_cases hk : p k
      · exact le_iSup₂_of_le (f := fun β (_ : β ∈ familyKernel a ∩ S) => rootSubgroup τ K β)
          (α k) ⟨⟨hSroot _ (hαS k), hk⟩, hαS k⟩ le_rfl (Subgroup.subset_closure ⟨c k, rfl⟩)
      · show pinnedX τ K (α k) (c k) ∈ _
        rw [hc k hk, pinnedX_zero]
        exact one_mem _
  have hsub : Nat.card (rootSpan τ K (familyKernel a ∩ S)) =
      Nat.card {c : Fin n → K // ∀ k, ¬ p k → c k = 0} := by
    refine Nat.card_congr (Equiv.symm (Equiv.ofBijective
      (fun c => ⟨f c.1, (hspan _).2 ⟨c.1, c.2, rfl⟩⟩) ⟨?_, ?_⟩))
    · intro c c' h
      exact Subtype.ext (hbij.2.1 (Set.mem_univ _) (Set.mem_univ _) (congrArg Subtype.val h))
    · rintro ⟨u, hu⟩
      obtain ⟨c, hc, rfl⟩ := (hspan u).1 hu
      exact ⟨⟨c, hc⟩, rfl⟩
  have hcard : Nat.card {c : Fin n → K // ∀ k, ¬ p k → c k = 0} =
      Nat.card K ^ Nat.card {k // p k} := by
    have e2 : {c : Fin n → K // ∀ k, ¬ p k → c k = 0} ≃ ({k // p k} → K) :=
      { toFun := fun c k => c.1 k.1
        invFun := fun g => ⟨fun k => if h : p k then g ⟨k, h⟩ else 0, fun k hk => by simp [hk]⟩
        left_inv := fun c => by
          apply Subtype.ext
          funext k
          by_cases hk : p k
          · simp [hk]
          · simp [hk, c.2 k hk]
        right_inv := fun g => by
          funext k
          simp [k.2] }
    rw [Nat.card_congr e2, Nat.card_fun]
  have hker : familyKernel a ∩ S = α '' {k | p k} := by
    ext β
    constructor
    · rintro ⟨⟨hβr, hβ⟩, hβS⟩
      obtain ⟨k, rfl⟩ := hrange.symm ▸ hβS
      exact ⟨k, hβ, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨hSroot _ (hαS k), hk⟩, hαS k⟩
  rw [hsub, hcard, hker, Set.ncard_image_of_injective _ hα]
  congr 1

@[expose] def familyStabilizerSubgroup (a : ι → Fin τ.rank → Kˣ) : Subgroup (WeylGroup τ) :=
  ⨅ i, rootCharStabilizerSubgroup (a i)

theorem mem_familyStabilizerSubgroup {a : ι → Fin τ.rank → Kˣ} {w : WeylGroup τ} :
    w ∈ familyStabilizerSubgroup a ↔ w ∈ familyStabilizer a := by
  rw [familyStabilizerSubgroup, Subgroup.mem_iInf]
  exact forall_congr' fun i => Iff.rfl

theorem canonicalRep_mem_monomialSubgroup' (w : WeylGroup τ) :
    canonicalRep (coxeterSystem τ) K w ∈ monomialSubgroup τ K := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem τ).exists_isReduced w
  rw [canonicalRep_wordProd hω]
  exact Subgroup.list_prod_mem _ fun x hx => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact weylElt_mem_monomialSubgroup i

theorem exists_torus_mul_canonicalRep_of_mem_monomial {g : ModGL τ K}
    (hg : g ∈ monomialSubgroup τ K) :
    ∃ (w : WeylGroup τ) (t : ModGL τ K), t ∈ torusGroup τ K ∧
      g = t * canonicalRep (coxeterSystem τ) K w := by
  obtain ⟨huniq, ⟨ρ, -, hmaps, -, -, hker⟩, -⟩ := Weyl_normalizer_quotient τ K
  set w := ρ ⟨g, hg⟩ with hw
  have hnN := canonicalRep_mem_monomialSubgroup' (τ := τ) (K := K) w
  have hρn : ρ ⟨canonicalRep (coxeterSystem τ) K w, hnN⟩ = w :=
    (huniq _ hnN).unique (hmaps ⟨canonicalRep (coxeterSystem τ) K w, hnN⟩)
      (mapsRootLines_canonicalRep (R := K) w)
  have hker1 : (⟨g, hg⟩ : monomialSubgroup τ K) *
      (⟨canonicalRep (coxeterSystem τ) K w, hnN⟩ : monomialSubgroup τ K)⁻¹ ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hρn, mul_inv_cancel]
  rw [hker] at hker1
  refine ⟨w, g * (canonicalRep (coxeterSystem τ) K w)⁻¹, hker1, ?_⟩
  group

section Counting


theorem card_familyCentralizer_inf_monomial [Finite K] (a : ι → Fin τ.rank → Kˣ) :
    Nat.card (familyCentralizer τ K a ⊓ monomialSubgroup τ K : Subgroup (ModGL τ K)) =
      Nat.card (torusGroup τ K) * Nat.card (familyStabilizerSubgroup a) := by
  classical
  have hTB := triangular_borel_structure.{0, 0} τ K
  have hBC : borelGroup τ K ≤ adjointGroup τ K := (hTB.2.2.2.2.2.2.2.2.2.2.2 K).1
  have hTC : torusGroup τ K ≤ adjointGroup τ K := le_sup_left.trans hBC
  have hTN : torusGroup τ K ≤ monomialSubgroup τ K := le_sup_left
  have hmem : ∀ t ∈ torusGroup τ K, ∀ w ∈ familyStabilizer a,
      t * canonicalRep (coxeterSystem τ) K w ∈
        (familyCentralizer τ K a ⊓ monomialSubgroup τ K : Subgroup (ModGL τ K)) := by
    intro t ht w hw
    refine Subgroup.mem_inf.2 ⟨mem_familyCentralizer.2 ⟨mul_mem (hTC ht)
      (canonicalRep_mem_adjointGroup _ K w), fun i => ?_⟩,
      mul_mem (hTN ht) (canonicalRep_mem_monomialSubgroup' w)⟩
    have hdt := conj_rootDiagUnit_of_mem_torusGroup (a i) ht
    have hdn := (conj_canonicalRep_eq_iff (a i) w).2 (hw i)
    calc rootDiagUnit τ (a i) * (t * canonicalRep (coxeterSystem τ) K w) *
          (rootDiagUnit τ (a i))⁻¹ =
        (rootDiagUnit τ (a i) * t * (rootDiagUnit τ (a i))⁻¹) *
          (rootDiagUnit τ (a i) * canonicalRep (coxeterSystem τ) K w *
            (rootDiagUnit τ (a i))⁻¹) := by group
      _ = t * canonicalRep (coxeterSystem τ) K w := by rw [hdt, hdn]
  have e : (torusGroup τ K × familyStabilizerSubgroup a) ≃
      (familyCentralizer τ K a ⊓ monomialSubgroup τ K : Subgroup (ModGL τ K)) :=
    Equiv.ofBijective
      (fun p => ⟨(p.1 : ModGL τ K) * canonicalRep (coxeterSystem τ) K (p.2 : WeylGroup τ),
        hmem _ p.1.2 _ (mem_familyStabilizerSubgroup.1 p.2.2)⟩)
      ⟨fun p p' h => by
        have h' : (p.1 : ModGL τ K) * canonicalRep (coxeterSystem τ) K (p.2 : WeylGroup τ) =
            (p'.1 : ModGL τ K) * canonicalRep (coxeterSystem τ) K (p'.2 : WeylGroup τ) :=
          congrArg Subtype.val h
        obtain ⟨hww, hh, -, -⟩ := bruhat_factor_unique τ K p.2 p'.2 p.1 p'.1 1 1 1 1 p.1.2 p'.1.2
          (one_mem _) (one_mem _) (one_mem _) (one_mem _) (by simpa using h')
        exact Prod.ext (Subtype.ext hh) (Subtype.ext hww),
       fun g => by
        obtain ⟨hgC, hgN⟩ := Subgroup.mem_inf.1 g.2
        obtain ⟨hgC', hgfix'⟩ := mem_familyCentralizer.1 hgC
        obtain ⟨w, t, ht, hgt⟩ := exists_torus_mul_canonicalRep_of_mem_monomial hgN
        have hw : w ∈ familyStabilizer a := by
          intro i
          have h1 := hgfix' i
          rw [hgt] at h1
          have hdt := conj_rootDiagUnit_of_mem_torusGroup (a i) ht
          have h2 : rootDiagUnit τ (a i) * canonicalRep (coxeterSystem τ) K w *
              (rootDiagUnit τ (a i))⁻¹ = canonicalRep (coxeterSystem τ) K w := by
            have h3 : t * (rootDiagUnit τ (a i) * canonicalRep (coxeterSystem τ) K w *
                (rootDiagUnit τ (a i))⁻¹) = t * canonicalRep (coxeterSystem τ) K w := by
              calc t * (rootDiagUnit τ (a i) * canonicalRep (coxeterSystem τ) K w *
                    (rootDiagUnit τ (a i))⁻¹) =
                  (rootDiagUnit τ (a i) * t * (rootDiagUnit τ (a i))⁻¹) *
                    (rootDiagUnit τ (a i) * canonicalRep (coxeterSystem τ) K w *
                      (rootDiagUnit τ (a i))⁻¹) := by rw [hdt]
                _ = rootDiagUnit τ (a i) * (t * canonicalRep (coxeterSystem τ) K w) *
                    (rootDiagUnit τ (a i))⁻¹ := by group
                _ = t * canonicalRep (coxeterSystem τ) K w := h1
            exact mul_left_cancel h3
          exact (conj_canonicalRep_eq_iff (a i) w).1 h2
        exact ⟨(⟨t, ht⟩, ⟨w, mem_familyStabilizerSubgroup.2 hw⟩), Subtype.ext hgt.symm⟩⟩
  rw [← Nat.card_congr e, Nat.card_prod]

theorem card_familyCentralizer [Finite K] (a : ι → Fin τ.rank → Kˣ) :
    Nat.card (familyCentralizer τ K a) = Nat.card (torusGroup τ K) *
      (Nat.card K ^ (familyKernel a ∩ {α | IsRoot τ α ∧ 0 < height α}).ncard) *
      ∑ᶠ w : familyStabilizerSubgroup a,
        Nat.card K ^ (familyKernel a ∩ inversionSet (w : WeylGroup τ)).ncard := by
  classical
  have : Fintype (familyStabilizerSubgroup a) := Fintype.ofFinite _
  have hTB := triangular_borel_structure.{0, 0} τ K
  have hBC : borelGroup τ K ≤ adjointGroup τ K := (hTB.2.2.2.2.2.2.2.2.2.2.2 K).1
  have hTC : torusGroup τ K ≤ adjointGroup τ K := le_sup_left.trans hBC
  have hposfin : {β : Fin τ.rank → ℤ | IsRoot τ β ∧ 0 < height β}.Finite :=
    (finite_setOf_isRoot τ).subset fun β hβ => hβ.1
  have hcoll1 := fun {m : ℕ} (α : Fin m → Fin τ.rank → ℤ) (hα : Function.Injective α)
    (hr : Set.range α = {β : Fin τ.rank → ℤ | IsRoot τ β ∧ 0 < height β}) =>
    (positive_root_collection τ K).2 α hα hr
  have hcard1 := card_rootSpan_familyKernel_inter a hposfin (fun β hβ => hβ.1) hcoll1
  have hcard2 : ∀ w : WeylGroup τ, Nat.card (rootSpan τ K (familyKernel a ∩ inversionSet w)) =
      Nat.card K ^ (familyKernel a ∩ inversionSet w).ncard := fun w =>
    card_rootSpan_familyKernel_inter a (inversionSet_finite w) (fun β hβ => hβ.1)
      (fun {m} α hα hr => (bruhat_cell_factorization τ K).2.1 w α hα hr)
  have hfix : ∀ i, ∀ x ∈ torusGroup τ K, rootDiagUnit τ (a i) * x * (rootDiagUnit τ (a i))⁻¹ = x :=
    fun i x hx => conj_rootDiagUnit_of_mem_torusGroup (a i) hx
  have hmem : ∀ w ∈ familyStabilizer a, ∀ h ∈ torusGroup τ K,
      ∀ u ∈ rootSpan τ K (familyKernel a ∩ {α | IsRoot τ α ∧ 0 < height α}),
      ∀ v ∈ rootSpan τ K (familyKernel a ∩ inversionSet w),
        h * u * canonicalRep (coxeterSystem τ) K w * v ∈ familyCentralizer τ K a := by
    intro w hw h hh u hu v hv
    refine mem_familyCentralizer.2 ⟨mul_mem (mul_mem (mul_mem (hTC hh)
      (rootSpan_le_adjointGroup K _ hu)) (canonicalRep_mem_adjointGroup _ K w))
      (rootSpan_le_adjointGroup K _ hv), fun i => ?_⟩
    have hdu : rootDiagUnit τ (a i) * u * (rootDiagUnit τ (a i))⁻¹ = u :=
      conj_eq_iff_mem_centralizer.2 ((rootSpan_le_centralizer (a i)
        (S := familyKernel a ∩ {α | IsRoot τ α ∧ 0 < height α})
        (fun β hβ => ⟨hβ.1.1, hβ.1.2 i⟩)) hu)
    have hdv : rootDiagUnit τ (a i) * v * (rootDiagUnit τ (a i))⁻¹ = v :=
      conj_eq_iff_mem_centralizer.2 ((rootSpan_le_centralizer (a i)
        (S := familyKernel a ∩ inversionSet w) (fun β hβ => ⟨hβ.1.1, hβ.1.2 i⟩)) hv)
    have hdn := (conj_canonicalRep_eq_iff (a i) w).2 (hw i)
    calc rootDiagUnit τ (a i) * (h * u * canonicalRep (coxeterSystem τ) K w * v) *
          (rootDiagUnit τ (a i))⁻¹ =
        (rootDiagUnit τ (a i) * h * (rootDiagUnit τ (a i))⁻¹) *
          (rootDiagUnit τ (a i) * u * (rootDiagUnit τ (a i))⁻¹) *
          (rootDiagUnit τ (a i) * canonicalRep (coxeterSystem τ) K w *
            (rootDiagUnit τ (a i))⁻¹) *
          (rootDiagUnit τ (a i) * v * (rootDiagUnit τ (a i))⁻¹) := by group
      _ = h * u * canonicalRep (coxeterSystem τ) K w * v := by rw [hfix i h hh, hdu, hdn, hdv]
  have e : (Σ w : familyStabilizerSubgroup a, torusGroup τ K ×
      (rootSpan τ K (familyKernel a ∩ {α | IsRoot τ α ∧ 0 < height α})) ×
      (rootSpan τ K (familyKernel a ∩ inversionSet (w : WeylGroup τ)))) ≃
      familyCentralizer τ K a :=
    Equiv.ofBijective
      (fun p => ⟨(p.2.1 : ModGL τ K) * (p.2.2.1 : ModGL τ K) *
          canonicalRep (coxeterSystem τ) K (p.1 : WeylGroup τ) * (p.2.2.2 : ModGL τ K),
        hmem _ (mem_familyStabilizerSubgroup.1 p.1.2) _ p.2.1.2 _ p.2.2.1.2 _ p.2.2.2.2⟩)
      ⟨by
        rintro ⟨⟨w, hw⟩, h, u, v⟩ ⟨⟨w', hw'⟩, h', u', v'⟩ heq
        have hEq : (h : ModGL τ K) * u * canonicalRep (coxeterSystem τ) K w * v =
            (h' : ModGL τ K) * u' * canonicalRep (coxeterSystem τ) K w' * v' :=
          congrArg Subtype.val heq
        obtain ⟨hww, hh, hu, hv⟩ := bruhat_factor_unique τ K w w' _ _ _ _ _ _ h.2 h'.2
          (rootSpan_mono Set.inter_subset_right u.2) (rootSpan_mono Set.inter_subset_right u'.2)
          (rootSpan_mono Set.inter_subset_right v.2) (rootSpan_mono Set.inter_subset_right v'.2) hEq
        subst hww
        have e1 : h = h' := Subtype.ext hh
        have e2 : u = u' := Subtype.ext hu
        have e3 : v = v' := Subtype.ext hv
        subst e1 e2 e3
        rfl,
       fun g => by
        obtain ⟨w, hw, h, hh, u, hu, v, hv, hg⟩ := familyCentralizer_factors τ K a g g.2
        exact ⟨⟨⟨w, mem_familyStabilizerSubgroup.2 hw⟩, ⟨h, hh⟩, ⟨u, hu⟩, ⟨v, hv⟩⟩,
          Subtype.ext hg.symm⟩⟩
  rw [← Nat.card_congr e, Nat.card_sigma]
  simp only [Nat.card_prod, hcard1, hcard2]
  rw [finsum_eq_sum_of_fintype, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => by ring


theorem exists_conj_le_of_isPGroup_of_not_dvd_relIndex {Γ : Type*} [Group Γ] [Finite Γ] {r : ℕ}
    [hr : Fact r.Prime] {C N' A : Subgroup Γ} (hA : A ≤ C) (hAp : IsPGroup r A)
    (hI : ¬ r ∣ N'.relIndex C) : ∃ u ∈ C, ∀ x ∈ A, u * x * u⁻¹ ∈ N' := by
  classical
  set N := N'.subgroupOf C
  set A' : Subgroup C := A.subgroupOf C
  have hA'p : IsPGroup r A' := by
    rintro ⟨g, hg⟩
    obtain ⟨k, hk⟩ := hAp ⟨(g : Γ), hg⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun y : A => (y : Γ)) hk
    simpa using this
  have hcardQ : ¬ r ∣ Nat.card (C ⧸ N) := hI
  obtain ⟨Q, hQ⟩ := hA'p.nonempty_fixed_point_of_prime_not_dvd_card (C ⧸ N) hcardQ
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective Q
  refine ⟨(z : Γ)⁻¹, inv_mem z.2, fun x hx => ?_⟩
  have hxC : x ∈ C := hA hx
  set x' : C := ⟨x, hxC⟩
  have hx' : x' ∈ A' := hx
  have hfix := hQ ⟨x', hx'⟩
  change ((x' * z : C) : C ⧸ N) = (z : C ⧸ N) at hfix
  rw [QuotientGroup.eq] at hfix
  have h1 : (x' * z)⁻¹ * z ∈ N := hfix
  have h2 : z⁻¹ * x' * z ∈ N := by
    have := inv_mem h1
    simpa [mul_assoc] using this
  have h3 := Subgroup.mem_subgroupOf.1 h2
  simpa [mul_assoc] using h3

theorem not_dvd_relIndex_familyCentralizer [Finite K] (a : ι → Fin τ.rank → Kˣ) {r : ℕ}
    [hr : Fact r.Prime] (hqr : ¬ r ∣ Nat.card K) {M : ℕ} (hqM : Nat.card K ≡ 1 [MOD r ^ M])
    (hW : ¬ r ^ M ∣ Nat.card (WeylGroup τ)) :
    ¬ r ∣ (familyCentralizer τ K a ⊓ monomialSubgroup τ K).relIndex (familyCentralizer τ K a) := by
  classical
  have : Fintype (familyStabilizerSubgroup a) := Fintype.ofFinite _
  set q := Nat.card K with hqdef
  set C := familyCentralizer τ K a with hC
  set NC := C ⊓ monomialSubgroup τ K with hNC
  set Ws := Nat.card (familyStabilizerSubgroup a) with hWs
  set P := ∑ᶠ w : familyStabilizerSubgroup a,
    q ^ (familyKernel a ∩ inversionSet (w : WeylGroup τ)).ncard with hP
  set n₁ := (familyKernel a ∩ {α | IsRoot τ α ∧ 0 < height α}).ncard with hn₁
  set I := NC.relIndex C with hI
  have hle : NC ≤ C := inf_le_left
  have hH : 0 < Nat.card (torusGroup τ K) := Nat.card_pos
  have hrel : Ws * I = q ^ n₁ * P := by
    have h1 := Subgroup.card_mul_index (NC.subgroupOf C)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
      card_familyCentralizer_inf_monomial, card_familyCentralizer] at h1
    apply Nat.eq_of_mul_eq_mul_left hH
    have : Nat.card (torusGroup τ K) * Ws * I = Nat.card (torusGroup τ K) * q ^ n₁ * P := by
      rw [← h1]
      rfl
    calc Nat.card (torusGroup τ K) * (Ws * I) = Nat.card (torusGroup τ K) * Ws * I := by ring
      _ = Nat.card (torusGroup τ K) * q ^ n₁ * P := this
      _ = Nat.card (torusGroup τ K) * (q ^ n₁ * P) := by ring
  have hPW : P ≡ Ws [MOD r ^ M] := by
    rw [← ZMod.natCast_eq_natCast_iff, hP, finsum_eq_sum_of_fintype, Nat.cast_sum]
    have hq1 : (q : ZMod (r ^ M)) = 1 := by
      rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
      exact hqM
    simp only [Nat.cast_pow, hq1, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one, hWs, Nat.card_eq_fintype_card]
  have hW0 : Ws ≠ 0 := Nat.card_pos.ne'
  set e := Ws.factorization r with he
  have he1 : ¬ r ^ (e + 1) ∣ Ws := Nat.pow_succ_factorization_not_dvd hW0 hr.out
  have hWsW : ¬ r ^ M ∣ Ws := fun h =>
    hW (h.trans (Subgroup.card_subgroup_dvd_card (familyStabilizerSubgroup a)))
  have heM : e + 1 ≤ M := by
    by_contra h
    exact hWsW ((Nat.pow_dvd_pow r (by omega)).trans (Nat.ordProj_dvd Ws r))
  intro hrI
  obtain ⟨m, hm⟩ := hrI
  have hdvd : r ^ (e + 1) ∣ q ^ n₁ * P := by
    rw [← hrel, hm, pow_succ]
    exact mul_dvd_mul (Nat.ordProj_dvd Ws r) (Dvd.intro m rfl)
  have hcop : Nat.Coprime (r ^ (e + 1)) (q ^ n₁) :=
    Nat.Coprime.pow _ _ ((Nat.Prime.coprime_iff_not_dvd hr.out).2 hqr)
  have hPr : r ^ (e + 1) ∣ P := hcop.dvd_of_dvd_mul_left hdvd
  exact he1 ((hPW.dvd_iff (Nat.pow_dvd_pow r heM)).1 hPr)

theorem exists_conj_le_monomial_of_isPGroup_family [Finite K] (a : ι → Fin τ.rank → Kˣ) {r : ℕ}
    [hr : Fact r.Prime] (hqr : ¬ r ∣ Nat.card K) {M : ℕ} (hqM : Nat.card K ≡ 1 [MOD r ^ M])
    (hW : ¬ r ^ M ∣ Nat.card (WeylGroup τ)) {A : Subgroup (ModGL τ K)}
    (hA : A ≤ familyCentralizer τ K a) (hAp : IsPGroup r A) :
    ∃ u ∈ familyCentralizer τ K a, ∀ x ∈ A,
      u * x * u⁻¹ ∈ familyCentralizer τ K a ⊓ monomialSubgroup τ K := by
  have := finite_modGL (τ := τ) (K := K)
  exact exists_conj_le_of_isPGroup_of_not_dvd_relIndex hA hAp
    (not_dvd_relIndex_familyCentralizer a hqr hqM hW)

end Counting

end

end CFSG.HardMathSupport.Timmesfeld.Torality
