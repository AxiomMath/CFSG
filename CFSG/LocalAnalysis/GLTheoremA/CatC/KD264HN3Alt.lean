module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264HN3Tools
public import CFSG.Sporadic.HNSchreier.ThreeCent
public import CFSG.HardMathSupport.Dickson.I271.Support.EngineKL
public import CFSG.LocalAnalysis.GLTheoremA.S8.HNAlt12
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.Assembly
public import CFSG.Holt.H78.Sec4AltSylow
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264RowData
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264SevenSq
public import CFSG.LocalAnalysis.GLTheoremA.CatC.ThreeCycleElemAbelian

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Gen.HN3

open CFSG.Open Equiv CFSG.Sporadic.HNSchreier

@[expose] def blockA (i : Fin 4) : alternatingGroup (Fin 12) :=
  ⟨tri ⟨3 * i, by omega⟩ ⟨3 * i + 1, by omega⟩ ⟨3 * i + 2, by omega⟩,
    (isThreeCycle_tri (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
      (by simp [Fin.ext_iff])).mem_alternatingGroup⟩

theorem blockA_val (i : Fin 4) : ((blockA i : alternatingGroup (Fin 12)) : Perm (Fin 12)) =
    tri ⟨3 * i, by omega⟩ ⟨3 * i + 1, by omega⟩ ⟨3 * i + 2, by omega⟩ := rfl

theorem blockA_pow : ∀ i, blockA i ^ 3 = 1 := by
  intro i; apply Subtype.ext; rw [Subgroup.coe_pow, blockA_val]; fin_cases i <;> (unfold tri; decide)

theorem blockA_ne : ∀ i, blockA i ≠ 1 := by
  intro i h
  have := congrArg (fun x : alternatingGroup (Fin 12) => (x : Perm (Fin 12)) ⟨3 * i, by omega⟩) h
  simp only [blockA_val, Subgroup.coe_one, Perm.one_apply] at this
  revert this
  fin_cases i <;> (unfold tri; decide)

theorem blockA_comm : ∀ i j, blockA i * blockA j = blockA j * blockA i := by
  intro i j; apply Subtype.ext
  simp only [Subgroup.coe_mul, blockA_val]
  fin_cases i <;> fin_cases j <;> (unfold tri; decide)

theorem blockA_not_mem (j : Fin 4) :
    blockA j ∉ S8.CfgI.Triangular.lowerClosure blockA j.val := by
  intro h
  set p : Fin 12 := ⟨3 * j, by omega⟩
  have hle : S8.CfgI.Triangular.lowerClosure blockA j.val ≤
      (MulAction.stabilizer (Perm (Fin 12)) p).comap (alternatingGroup (Fin 12)).subtype := by
    rw [S8.CfgI.Triangular.lowerClosure, Subgroup.closure_le]
    rintro _ ⟨i, hi, rfl⟩
    simp only [Set.mem_setOf_eq] at hi
    rw [SetLike.mem_coe, Subgroup.mem_comap, MulAction.mem_stabilizer_iff, Subgroup.coe_subtype,
      Perm.smul_def, blockA_val]
    revert hi
    fin_cases i <;> fin_cases j <;> (simp only [p]; unfold tri; decide)
  have := hle h
  rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, Subgroup.coe_subtype, Perm.smul_def,
    blockA_val] at this
  revert this
  fin_cases j <;> (simp only [p]; unfold tri; decide)

theorem card_blocks : 3 ^ 4 ≤ Nat.card (Subgroup.closure (Set.range blockA)) :=
  card_closure_of_not_mem blockA_pow blockA_ne blockA_comm blockA_not_mem

theorem isElemAbelian_blocks : IsElemAbelian 3 (Subgroup.closure (Set.range blockA)) :=
  isElemAbelian_closure (by rintro _ ⟨i, rfl⟩; exact blockA_pow i)
    (by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩; exact blockA_comm i j)

@[expose] def altFix (Λ : Set (Fin 12)) : Subgroup (alternatingGroup (Fin 12)) :=
  (fixingSubgroup (Perm (Fin 12)) Λ).comap (alternatingGroup (Fin 12)).subtype

theorem mem_altFix {Λ : Set (Fin 12)} {τ : alternatingGroup (Fin 12)} :
    τ ∈ altFix Λ ↔ ∀ i ∈ Λ, (τ : Perm (Fin 12)) i = i := by
  rw [altFix, Subgroup.mem_comap, mem_fixingSubgroup_iff]
  exact ⟨fun h i hi => h i hi, fun h i hi => h i hi⟩

noncomputable def altFixEquiv (Λ : Set (Fin 12)) [DecidablePred (· ∈ Λᶜ)] :
    alternatingGroup ↥Λᶜ ≃* altFix Λ := by
  classical
  let f : alternatingGroup ↥Λᶜ →* Perm (Fin 12) :=
    (Perm.ofSubtype : Perm ↥Λᶜ →* Perm (Fin 12)).comp (alternatingGroup ↥Λᶜ).subtype
  have hf : Function.Injective f :=
    Perm.ofSubtype_injective.comp (alternatingGroup ↥Λᶜ).subtype_injective
  have hrange : f.range = alternatingGroup (Fin 12) ⊓ fixingSubgroup (Perm (Fin 12)) Λ := by
    rw [← CFSG.Holt.H78.map_ofSubtype_alternatingGroup_compl Λ, MonoidHom.range_comp,
      Subgroup.range_subtype]
  let e1 : alternatingGroup ↥Λᶜ ≃* f.range := MonoidHom.ofInjective hf
  have hmem : ∀ g : f.range, (g : Perm (Fin 12)) ∈
      alternatingGroup (Fin 12) ⊓ fixingSubgroup (Perm (Fin 12)) Λ := fun g => by
    rw [← hrange]; exact g.2
  have hmem' : ∀ t : altFix Λ, ((t : alternatingGroup (Fin 12)) : Perm (Fin 12)) ∈ f.range :=
    fun t => by
      rw [hrange]
      exact Subgroup.mem_inf.2 ⟨(t : alternatingGroup (Fin 12)).2, Subgroup.mem_comap.1 t.2⟩
  refine e1.trans
    { toFun := fun g => ⟨⟨g, (Subgroup.mem_inf.1 (hmem g)).1⟩,
        Subgroup.mem_comap.2 (Subgroup.mem_inf.1 (hmem g)).2⟩
      invFun := fun t => ⟨(t : alternatingGroup (Fin 12)), hmem' t⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }

theorem card_altFix {Λ : Set (Fin 12)} [DecidablePred (· ∈ Λᶜ)] (h6 : Nat.card ↥Λᶜ = 6) :
    Nat.card (altFix Λ) = 360 := by
  classical
  haveI : Nontrivial ↥Λᶜ := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  rw [← Nat.card_congr (altFixEquiv Λ).toEquiv, nat_card_alternatingGroup, h6]
  rfl

theorem isQuasisimple_altFix {Λ : Set (Fin 12)} [DecidablePred (· ∈ Λᶜ)]
    (h6 : Nat.card ↥Λᶜ = 6) : CFSG.Open.IsQuasisimple (altFix Λ) := by
  classical
  haveI hs : IsSimpleGroup (alternatingGroup ↥Λᶜ) := alternatingGroup.isSimpleGroup (by omega)
  haveI : IsSimpleGroup (altFix Λ) := @MulEquiv.isSimpleGroup _ _ _ _ hs (altFixEquiv Λ).symm
  have hnc : ∃ a b : altFix Λ, a * b ≠ b * a :=
    CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple
      (by rw [card_altFix h6]; norm_num)
  have hperf : commutator (altFix Λ) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator (altFix Λ)) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      apply hab
      have hc := Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [← commutator_def, h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
      exact hc
    · exact h
  exact Seven.isQuasisimple_of_simple hperf hnc

theorem tri012_apply0 : tri 0 1 2 (0 : Fin 12) = 1 := by unfold tri; decide
theorem tri012_apply1 : tri 0 1 2 (1 : Fin 12) = 2 := by unfold tri; decide
theorem tri012_sq_apply0 : (tri 0 1 2 ^ 2) (0 : Fin 12) = 2 := by unfold tri; decide

theorem support_tri012 : ∀ i : Fin 12, i ∈ (tri 0 1 2).support ↔ i.val < 3 := by
  unfold tri; decide

theorem exists_comp_of_elemAbelian {A : Subgroup (alternatingGroup (Fin 12))}
    (hA : IsElemAbelian 3 A) (hAC : A ≤ Subgroup.centralizer {tri012A})
    (hcard : 81 ≤ Nat.card A) :
    ∃ σ ∈ A, σ ≠ 1 ∧ σ ≠ tri012A ∧ σ ≠ tri012A ^ 2 ∧ ∃ K : Subgroup (alternatingGroup (Fin 12)),
      GLAPComponent 3 (Subgroup.centralizer {tri012A} ⊓ Subgroup.centralizer {σ}) K := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set t : Perm (Fin 12) := tri 0 1 2 with ht
  set B : Subgroup (Perm (Fin 12)) := A.map (alternatingGroup (Fin 12)).subtype with hB
  have hBmem : ∀ b ∈ B, ∃ a ∈ A, (a : Perm (Fin 12)) = b := by
    rintro _ ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩
  have hBt : ∀ b ∈ B, b * t = t * b := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := hBmem b hb
    have := Subgroup.mem_centralizer_singleton_iff.1 (hAC ha)
    exact congrArg Subtype.val this
  have hB3 : ∀ b ∈ B, b ^ 3 = 1 := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := hBmem b hb
    rw [← Subgroup.coe_pow, hA.2 a ha, Subgroup.coe_one]
  have hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    intro a ha b hb
    obtain ⟨a', ha', rfl⟩ := hBmem a ha
    obtain ⟨b', hb', rfl⟩ := hBmem b hb
    exact congrArg Subtype.val (congrArg Subtype.val (hA.1.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩))
  have hBcard : Nat.card B = Nat.card A :=
    Subgroup.card_map_of_injective (alternatingGroup (Fin 12)).subtype_injective
  set B0 : Subgroup (Perm (Fin 12)) := (MulAction.stabilizer B (0 : Fin 12)).map B.subtype
    with hB0
  have hB0le : B0 ≤ B := by rintro _ ⟨g, -, rfl⟩; exact g.2
  have horb : Nat.card (MulAction.orbit B (0 : Fin 12)) *
      Nat.card (MulAction.stabilizer B (0 : Fin 12)) = Nat.card B := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact MulAction.card_orbit_mul_card_stabilizer_eq_card_group B 0
  have horb3 : Nat.card (MulAction.orbit B (0 : Fin 12)) ≤ 3 := by
    have hsub : MulAction.orbit B (0 : Fin 12) ⊆ (t.support : Set (Fin 12)) := by
      rintro _ ⟨g, rfl⟩
      show (g : Perm (Fin 12)) 0 ∈ t.support
      exact mem_support_of_commute (hBt g g.2) ((support_tri012 0).2 (by decide))
    calc Nat.card (MulAction.orbit B (0 : Fin 12))
        ≤ Nat.card (t.support : Set (Fin 12)) := Nat.card_mono (Set.toFinite _) hsub
      _ = 3 := by rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]; unfold t tri; decide
  have hB0card : 27 ≤ Nat.card B0 := by
    rw [hB0, Subgroup.card_map_of_injective B.subtype_injective]
    haveI : Nonempty (MulAction.orbit B (0 : Fin 12)) := ⟨⟨0, MulAction.mem_orbit_self 0⟩⟩
    have hpos : 0 < Nat.card (MulAction.orbit B (0 : Fin 12)) := Nat.card_pos
    have : 81 ≤ Nat.card (MulAction.orbit B (0 : Fin 12)) *
        Nat.card (MulAction.stabilizer B (0 : Fin 12)) := by rw [horb, hBcard]; exact hcard
    nlinarith
  have hB0fix : ∀ b ∈ B0, ∀ i : Fin 12, i.val < 3 → b i = i := by
    rintro _ ⟨g, hg, rfl⟩ i hi
    have h0 : (g : Perm (Fin 12)) 0 = 0 := hg
    have hc := hBt g g.2
    have h1 : (g : Perm (Fin 12)) 1 = 1 := by
      rw [← tri012_apply0, ← ht, ← Perm.mul_apply, hc, Perm.mul_apply, h0, ht, tri012_apply0]
    have h2 : (g : Perm (Fin 12)) 2 = 2 := by
      rw [← tri012_apply1, ← ht, ← Perm.mul_apply, hc, Perm.mul_apply, h1, ht, tri012_apply1]
    have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases this with rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
  set S : Finset (Fin 12) := Finset.univ.filter fun i => 3 ≤ i.val with hS
  have hScard : S.card = 9 := by rw [hS]; decide
  obtain ⟨σ, hσB0, hσ3⟩ := ThreeCycle.exists_card_support_eq_three 3 B0 S (by norm_num)
    (fun b hb => hB3 b (hB0le hb)) (fun a ha b hb => hBc a (hB0le ha) b (hB0le hb))
    (fun b hb x hx => hB0fix b hb x (by simpa [hS] using hx)) (by rw [hScard])
    (by rw [show (3 : ℕ) ^ 3 = 27 by norm_num]; exact hB0card)
  obtain ⟨σA, hσA, hσAe⟩ := hBmem σ (hB0le hσB0)
  have hσfix := hB0fix σ hσB0
  have hσ1 : σA ≠ 1 := by
    intro h; rw [h, Subgroup.coe_one] at hσAe; rw [← hσAe] at hσ3; simp at hσ3
  have hσt : σA ≠ tri012A := by
    intro h
    have := hσfix 0 (by decide)
    rw [← hσAe, h, tri012A_val, tri012_apply0] at this
    exact absurd this (by decide)
  have hσt2 : σA ≠ tri012A ^ 2 := by
    intro h
    have := hσfix 0 (by decide)
    rw [← hσAe, h, Subgroup.coe_pow, tri012A_val, tri012_sq_apply0] at this
    exact absurd this (by decide)
  refine ⟨σA, hσA, hσ1, hσt, hσt2, ?_⟩
  set Λf : Finset (Fin 12) := Finset.univ.filter (fun i => i.val < 3) ∪ σ.support with hΛf
  have hdisj : Disjoint (Finset.univ.filter (fun i : Fin 12 => i.val < 3)) σ.support := by
    rw [Finset.disjoint_left]
    intro i hi hiσ
    rw [Finset.mem_filter] at hi
    exact (Perm.mem_support.1 hiσ) (hσfix i hi.2)
  have hΛcard : Λf.card = 6 := by
    rw [hΛf, Finset.card_union_of_disjoint hdisj, hσ3]
    rfl
  set Λ : Set (Fin 12) := (Λf : Set (Fin 12)) with hΛ
  have h6 : Nat.card ↥Λᶜ = 6 := by
    rw [hΛ, ← Finset.coe_compl, Nat.card_coe_set_eq, Set.ncard_coe_finset, Finset.card_compl,
      hΛcard]
    rfl
  have hdisjoint : ∀ (τ : Perm (Fin 12)) (π : Perm (Fin 12)),
      (∀ i ∈ Λ, τ i = i) → (∀ i ∉ Λ, π i = i) → τ * π = π * τ := by
    intro τ π hτ hπ
    have : τ.Disjoint π := fun i => by
      by_cases hi : i ∈ Λ
      · exact Or.inl (hτ i hi)
      · exact Or.inr (hπ i hi)
    exact this.commute.eq
  have htΛ : ∀ i ∉ Λ, t i = i := by
    intro i hi
    by_contra h
    apply hi
    simp only [hΛ, hΛf, Finset.coe_union, Finset.coe_filter, Set.mem_union, Set.mem_setOf_eq]
    exact Or.inl ⟨Finset.mem_univ _, (support_tri012 i).1 (Perm.mem_support.2 h)⟩
  have hσΛ : ∀ i ∉ Λ, σ i = i := by
    intro i hi
    by_contra h
    apply hi
    simp only [hΛ, hΛf, Finset.coe_union, Set.mem_union, Finset.mem_coe]
    exact Or.inr (Perm.mem_support.2 h)
  have hle : altFix Λ ≤ Subgroup.centralizer {tri012A} ⊓ Subgroup.centralizer {σA} := by
    intro τ hτ
    have hτΛ := mem_altFix.1 hτ
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_,
      Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    · apply Subtype.ext
      exact hdisjoint _ _ hτΛ htΛ
    · apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hσAe]
      exact hdisjoint _ _ hτΛ hσΛ
  have hnorm : ((altFix Λ).subgroupOf
      (Subgroup.centralizer {tri012A} ⊓ Subgroup.centralizer {σA})).Normal := by
    refine ⟨fun k hk g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.1 g.2
    have hgt : ((g : alternatingGroup (Fin 12)) : Perm (Fin 12))⁻¹ * t =
        t * ((g : alternatingGroup (Fin 12)) : Perm (Fin 12))⁻¹ := by
      have := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1
        (Subgroup.inv_mem _ hg1))
      simpa [tri012A_val] using this
    have hgσ : ((g : alternatingGroup (Fin 12)) : Perm (Fin 12))⁻¹ * σ =
        σ * ((g : alternatingGroup (Fin 12)) : Perm (Fin 12))⁻¹ := by
      have := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1
        (Subgroup.inv_mem _ hg2))
      simpa [← hσAe] using this
    have hpres : ∀ y ∈ Λ, ((g : alternatingGroup (Fin 12)) : Perm (Fin 12))⁻¹ y ∈ Λ := by
      intro y hy
      simp only [hΛ, hΛf, Finset.coe_union, Finset.coe_filter, Set.mem_union, Set.mem_setOf_eq,
        Finset.mem_coe] at hy ⊢
      rcases hy with ⟨-, hy⟩ | hy
      · left
        refine ⟨Finset.mem_univ _, (support_tri012 _).1 ?_⟩
        exact mem_support_of_commute hgt ((support_tri012 y).2 hy)
      · right
        exact mem_support_of_commute hgσ hy
    have hk' : ((k : alternatingGroup (Fin 12)) : Perm (Fin 12)) ∈
        fixingSubgroup (Perm (Fin 12)) Λ := Subgroup.mem_comap.1 hk
    have := conj_mem_fixing hpres hk'
    show ((g : alternatingGroup (Fin 12)) * (k : alternatingGroup (Fin 12)) *
      (g : alternatingGroup (Fin 12))⁻¹) ∈ altFix Λ
    rw [altFix, Subgroup.mem_comap]
    simpa using this
  exact ⟨altFix Λ, CFSG.HardMathSupport.Dickson.I271.glaPComponent_of_normal Nat.prime_three
    (isQuasisimple_altFix h6) (by rw [card_altFix h6]; norm_num) hle hnorm⟩

end CFSG.LocalAnalysis.GLTheoremA.KD264Gen.HN3
