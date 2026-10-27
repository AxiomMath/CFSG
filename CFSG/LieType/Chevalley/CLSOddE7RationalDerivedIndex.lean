module

public import CFSG.LieType.Chevalley.LangFrobeniusFixedDerived

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem index_subgroupOf_le_two {G : Type*} [Group G] {H R : Subgroup G} (g : G)
    (h : ∀ r ∈ R, r ∈ H ∨ g * r ∈ H) : (H.subgroupOf R).index ≤ 2 := by
  by_cases hex : ∃ r ∈ R, r ∉ H
  · obtain ⟨r₀, hr₀, hr₀H⟩ := hex
    have hg₀ : g * r₀ ∈ H := (h r₀ hr₀).resolve_left hr₀H
    let f : Fin 2 → R ⧸ H.subgroupOf R := ![QuotientGroup.mk 1, QuotientGroup.mk ⟨r₀, hr₀⟩]
    have hf : Function.Surjective f := by
      intro x
      obtain ⟨⟨r, hr⟩, rfl⟩ := QuotientGroup.mk_surjective x
      rcases h r hr with hrH | hgr
      · refine ⟨0, ?_⟩
        change (QuotientGroup.mk 1 : R ⧸ H.subgroupOf R) = QuotientGroup.mk ⟨r, hr⟩
        rw [QuotientGroup.eq, inv_one, one_mul, Subgroup.mem_subgroupOf]
        exact hrH
      · refine ⟨1, ?_⟩
        change (QuotientGroup.mk ⟨r₀, hr₀⟩ : R ⧸ H.subgroupOf R) = QuotientGroup.mk ⟨r, hr⟩
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        have e : ((⟨r₀, hr₀⟩ : R)⁻¹ * ⟨r, hr⟩ : R) = (g * r₀)⁻¹ * (g * r) := by
          simp [mul_assoc]
        rw [e]
        exact mul_mem (inv_mem hg₀) hgr
    rw [Subgroup.index_eq_card]
    exact (Nat.card_le_card_of_surjective f hf).trans_eq (Nat.card_fin 2)
  · push Not at hex
    refine le_of_eq_of_le (Subgroup.index_eq_one.2 ?_) one_le_two
    exact eq_top_iff.2 fun x _ => Subgroup.mem_subgroupOf.2 (hex x x.2)

theorem baseChangeGL_rootDiagUnit
    {R S : Type} [Field R] [Field S] (f : R →+* S) {τ : Tag}
    (a : Fin τ.rank → Rˣ) :
    baseChangeGL f (rootDiagUnit τ a) =
      rootDiagUnit τ fun i => Units.map f.toMonoidHom (a i) := by
  refine Units.ext (end_ext_single fun b => ?_)
  rw [baseChangeGL_apply_single]
  change Finsupp.mapRange f f.map_zero (rootDiag a (Finsupp.single b 1)) =
    rootDiag (fun i => Units.map f.toMonoidHom (a i)) (Finsupp.single b 1)
  rcases b with i | α
  · rw [rootDiag_single_inl, rootDiag_single_inl, Finsupp.mapRange_single, map_one]
  · rw [rootDiag_single_inr, rootDiag_single_inr, Finsupp.smul_single_one,
      Finsupp.smul_single_one, Finsupp.mapRange_single]
    congr 1
    simp [map_prod, map_zpow₀]

theorem cartanChar_prod_zpow_eq_of_mul_eq {τ : Tag} {K : Type} [Field K]
    {B E : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} (hB : B * τ.cartan = E) (p : Fin τ.rank → Kˣ) :
    cartanChar (fun i => ∏ j, p j ^ B j i) = fun l => ∏ j, p j ^ E j l := by
  funext l
  calc ∏ i, (∏ j, p j ^ B j i) ^ τ.cartan i l
      = ∏ i, ∏ j, p j ^ (B j i * τ.cartan i l) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [← Finset.prod_zpow]
        exact Finset.prod_congr rfl fun j _ => (zpow_mul _ _ _).symm
    _ = ∏ j, ∏ i, p j ^ (B j i * τ.cartan i l) := Finset.prod_comm
    _ = ∏ j, p j ^ ((B * τ.cartan) j l) := by
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [Matrix.mul_apply, Finset.prod_zpow_eq_zpow_sum]
    _ = ∏ j, p j ^ E j l := by rw [hB]

@[expose] def e7Solve : Matrix (Fin Tag.E7.rank) (Fin Tag.E7.rank) ℤ :=
  !![2, 2, 3, 4, 3, 2, 1;
     4, 7, 8, 12, 9, 6, 3;
     3, 4, 6, 8, 6, 4, 2;
     4, 6, 8, 12, 9, 6, 3;
     1, 1, 2, 3, 3, 2, 1;
     2, 3, 4, 6, 5, 4, 2;
     -1, -2, -2, -3, -2, -1, 0]

@[expose] def e7Elim : Matrix (Fin Tag.E7.rank) (Fin Tag.E7.rank) ℤ :=
  !![1, 0, 0, 0, 0, 0, 0;
     0, 2, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0;
     0, -1, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 1, 0;
     0, -1, 0, 0, 0, 0, 1]

theorem e7Solve_mul_cartan : e7Solve * Tag.E7.cartan = e7Elim := by
  decide

theorem prod_update_zpow_e7Elim {G : Type*} [CommGroup G] (b : Fin 7 → G) (s : G)
    (hs : s ^ 2 = b 1 * b 4 * b 6) (l : Fin 7) :
    ∏ j : Fin 7, Function.update b 1 s j ^ e7Elim j l = b l := by
  fin_cases l <;> simp [Fin.prod_univ_succ, e7Elim, Function.update_apply]
  rw [hs]
  simp [mul_assoc, mul_left_comm, mul_comm]

theorem exists_cartanChar_E7_eq {K : Type} [Field K] (b : Fin Tag.E7.rank → Kˣ) (s : Kˣ)
    (hs : s ^ 2 = b ⟨1, by decide⟩ * b ⟨4, by decide⟩ * b ⟨6, by decide⟩) :
    ∃ t : Fin Tag.E7.rank → Kˣ, cartanChar t = b :=
  ⟨_, (cartanChar_prod_zpow_eq_of_mul_eq e7Solve_mul_cartan
    (Function.update b ⟨1, by decide⟩ s)).trans
      (funext fun l => prod_update_zpow_e7Elim (G := Kˣ) b s hs l)⟩

theorem exists_cartanChar_E7_or {K : Type} [Field K] [Finite K] (hK : ringChar K ≠ 2) :
    ∃ e : Fin Tag.E7.rank → Kˣ, ∀ b : Fin Tag.E7.rank → Kˣ,
      ∃ t : Fin Tag.E7.rank → Kˣ, cartanChar t = b ∨ cartanChar t = b * e := by
  classical
  have := Fintype.ofFinite K
  obtain ⟨ε, hε⟩ := FiniteField.exists_nonsquare hK
  have hε0 : ε ≠ 0 := fun h => hε (h ▸ ⟨0, (mul_zero 0).symm⟩)
  set i₁ : Fin Tag.E7.rank := ⟨1, by decide⟩
  set i₄ : Fin Tag.E7.rank := ⟨4, by decide⟩
  set i₆ : Fin Tag.E7.rank := ⟨6, by decide⟩
  set e : Fin Tag.E7.rank → Kˣ := Pi.mulSingle (M := fun _ => Kˣ) i₁ (Units.mk0 ε hε0)
  refine ⟨e, fun b => ?_⟩
  have hψ0 : ((b i₁ * b i₄ * b i₆ : Kˣ) : K) ≠ 0 := Units.ne_zero _
  have hroot : ∀ c : Kˣ, IsSquare (c : K) → ∃ s : Kˣ, s ^ 2 = c := by
    rintro c ⟨r, hr⟩
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact c.ne_zero (by rw [hr, mul_zero])
    exact ⟨Units.mk0 r hr0, Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, sq, hr])⟩
  by_cases hψ : IsSquare ((b i₁ * b i₄ * b i₆ : Kˣ) : K)
  · obtain ⟨s, hs⟩ := hroot _ hψ
    obtain ⟨t, ht⟩ := exists_cartanChar_E7_eq b s hs
    exact ⟨t, Or.inl ht⟩
  · have hsq : IsSquare ((b i₁ * b i₄ * b i₆ * Units.mk0 ε hε0 : Kˣ) : K) := by
      rw [Units.val_mul, Units.val_mk0,
        ← quadraticChar_one_iff_isSquare (mul_ne_zero hψ0 hε0), map_mul,
        quadraticChar_neg_one_iff_not_isSquare.2 hψ, quadraticChar_neg_one_iff_not_isSquare.2 hε]
      norm_num
    obtain ⟨s, hs⟩ := hroot _ hsq
    have h₁ : e i₁ = Units.mk0 ε hε0 := Pi.mulSingle_eq_same _ _
    have h₄ : e i₄ = 1 := Pi.mulSingle_eq_of_ne (by decide) _
    have h₆ : e i₆ = 1 := Pi.mulSingle_eq_of_ne (by decide) _
    obtain ⟨t, ht⟩ := exists_cartanChar_E7_eq (b * e) s (by
      change s ^ 2 = (b * e) i₁ * (b * e) i₄ * (b * e) i₆
      simp only [Pi.mul_apply, h₁, h₄, h₆, mul_one]
      rw [hs, mul_right_comm (b i₁ * b i₄), mul_right_comm (b i₁)])
    exact ⟨t, Or.inr ht⟩

theorem exists_rootDiagUnit_mul_of_frobenius_fixed
    (τ : Tag) {K L : Type} [Field K] [Finite K]
    [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ Nat.card K) {r : ModGL τ L} (hr : r ∈ adjointGroup τ L)
    (hrF : Units.map (entrywiseHom Fr) r = r) :
    ∃ a : Fin τ.rank → Kˣ, ∃ u ∈ (adjointGroup τ K).map (baseChangeGL (algebraMap K L)),
      r = baseChangeGL (algebraMap K L) (rootDiagUnit τ a) * u := by
  obtain ⟨S, hS⟩ := exists_finset_descent hr
  obtain ⟨E, hEf, hSE, hKE⟩ := exists_finite_subfield_of_finset (K := K) S
  obtain ⟨y, hy, rfl⟩ := hS E hSE
  obtain ⟨σE, hσE, hJ, hfix⟩ := exists_subfieldFrobenius_data (τ := τ) Fr hFr E hKE
  obtain ⟨h, hh, j, hj, rfl⟩ := mem_mul_of_mem_entrywiseFixedGroup (hfix y hy hrF)
  obtain ⟨hT, -, hF⟩ := hh
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hT
  have hσa : ∀ i, Units.map σE.toRingHom.toMonoidHom (a i) = a i := by
    have hF' : Units.map (entrywiseHom σE.toRingHom) (rootDiagUnit τ a) = rootDiagUnit τ a := hF
    have h0 : Units.map (entrywiseHom σE.toRingHom) (rootDiagUnit τ a) =
        rootDiagUnit τ (fun i => Units.map σE.toRingHom.toMonoidHom (a i)) :=
      Units.ext (entrywise_rootDiag σE.toRingHom a)
    exact congrFun (rootDiagUnit_injective (h0.symm.trans hF'))
  have hK : ∀ i, ∃ k : Kˣ, algebraMap K L k = ((a i : E) : L) := by
    intro i
    have hpow : ((a i : E) : L) ^ Nat.card K = ((a i : E) : L) := by
      rw [← hFr, ← hσE]
      exact congrArg (fun u : Eˣ => ((u : E) : L)) (hσa i)
    obtain ⟨k, hk⟩ := mem_range_algebraMap_of_pow_card_eq hpow
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [map_zero] at hk
      exact (a i).ne_zero (Subtype.ext hk.symm)
    exact ⟨Units.mk0 k hk0, hk⟩
  choose k hk using hK
  refine ⟨k, baseChangeGL E.subtype j, hJ ▸ Subgroup.mem_map_of_mem _ hj, ?_⟩
  rw [map_mul, baseChangeGL_rootDiagUnit, baseChangeGL_rootDiagUnit]
  congr 2
  funext i
  exact Units.ext (hk i).symm

theorem odd_E7_rational_derived_index_at_most_two
    (K : Type) [Field K] [Finite K]
    (hK : Odd (Nat.card K)) (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L]
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K) :
    Finite ↥(adjointGroup Tag.E7 L ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _)) ∧
    ⁅adjointGroup Tag.E7 L ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _),
        adjointGroup Tag.E7 L ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _)⁆ =
      (adjointGroup Tag.E7 K).map (baseChangeGL (algebraMap K L)) ∧
    (((adjointGroup Tag.E7 K).map (baseChangeGL (algebraMap K L))).subgroupOf
      (adjointGroup Tag.E7 L ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _))).index ≤
      2 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Algebra.IsAlgebraic K L := IsAlgClosure.isAlgebraic
  have hK2 : ringChar K ≠ 2 := by
    intro h2
    have h := (FiniteField.even_card_iff_char_two (F := K)).1 h2
    rw [Nat.card_eq_fintype_card, Nat.odd_iff] at hK
    omega
  obtain ⟨-, -, -, hder⟩ := exceptional_Lang_Frobenius_fixed_derived_root_group Tag.E7 K hK L Fr hFr
  set ι := baseChangeGL (τ := Tag.E7) (algebraMap K L)
  set H := (adjointGroup Tag.E7 K).map ι
  set R := adjointGroup Tag.E7 L ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _)
  have hdec : ∀ r ∈ R, ∃ a : Fin Tag.E7.rank → Kˣ, ∃ u ∈ H,
      r = ι (rootDiagUnit Tag.E7 a) * u :=
    fun r hr => exists_rootDiagUnit_mul_of_frobenius_fixed Tag.E7 Fr hFr hr.1 hr.2
  have hfin : Finite R := by
    have : Finite (ModGL Tag.E7 K) := finite_modGL
    have hle : R ≤ ι.range := by
      intro r hr
      obtain ⟨a, u, hu, rfl⟩ := hdec r hr
      exact mul_mem ⟨_, rfl⟩ (Subgroup.map_le_range _ _ hu)
    have : Finite ι.range := Finite.of_surjective _ ι.rangeRestrict_surjective
    exact Finite.of_injective _ (Subgroup.inclusion_injective hle)
  obtain ⟨e, he⟩ := exists_cartanChar_E7_or hK2
  have hχ : ∀ t : Fin Tag.E7.rank → Kˣ, ι (rootDiagUnit Tag.E7 (cartanChar t)) ∈ H := fun t => by
    rw [← list_prod_torusElt_eq_rootDiagUnit]
    refine Subgroup.mem_map_of_mem _ (Subgroup.list_prod_mem _ fun g hg => ?_)
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hg
    exact torusElt_mem_adjointGroup j _
  have hcos : ∀ r ∈ R, r ∈ H ∨ ι (rootDiagUnit Tag.E7 e) * r ∈ H := by
    intro r hr
    obtain ⟨a, u, hu, rfl⟩ := hdec r hr
    obtain ⟨t, ht | ht⟩ := he a
    · left
      rw [← ht]
      exact mul_mem (hχ t) hu
    · right
      rw [← mul_assoc, ← map_mul, ← rootDiagUnit_mul, mul_comm, ← ht]
      exact mul_mem (hχ t) hu
  exact ⟨hfin, hder, index_subgroupOf_le_two _ hcos⟩

end CFSG.LieType.Chevalley
