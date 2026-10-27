module

public import CFSG.LocalAnalysis.RankThreeUC.IndexThree

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open Subgroup

abbrev WreathThree : Type := Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3)

section Generators

variable {D Q : Type*} [Group D] [Group Q]

private def wreathBase : (Q → D) →* D ≀ᵣ Q where
  toFun f := ⟨f, 1⟩
  map_one' := rfl
  map_mul' f g := by ext <;> simp [RegularWreathProduct.mul_def]

private lemma inl_mul_wreathBase_mul_inl_inv (q : Q) (f : Q → D) :
    RegularWreathProduct.inl q * wreathBase f * (RegularWreathProduct.inl q)⁻¹ =
      wreathBase (fun x => f (q⁻¹ * x)) := by
  ext <;> simp [wreathBase, RegularWreathProduct.mul_def, RegularWreathProduct.inl]

private lemma mk_eq_wreathBase_mul_inl (f : Q → D) (q : Q) :
    (⟨f, q⟩ : D ≀ᵣ Q) = wreathBase f * RegularWreathProduct.inl q := by
  ext <;> simp [wreathBase, RegularWreathProduct.mul_def, RegularWreathProduct.inl]

private lemma mulSingle_one_inv_mul [DecidableEq Q] (q : Q) (c : D) :
    (fun x => (Pi.mulSingle 1 c : Q → D) (q⁻¹ * x)) = Pi.mulSingle q c := by
  ext x
  by_cases h : x = q
  · subst h
    simp
  · simp [h, Ne.symm h, inv_mul_eq_one]

end Generators

theorem exists_generators_wreathThree :
    ∃ a b : WreathThree, a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ closure {a, b} = ⊤ := by
  set g : Multiplicative (ZMod 3) := Multiplicative.ofAdd 1
  have hg3 : g ^ 3 = 1 := by decide
  have hgen : ∀ q : Multiplicative (ZMod 3), ∃ k : ℕ, q = g ^ k := by
    intro q
    obtain ⟨k, hk⟩ : ∃ k : Fin 3, q = g ^ (k : ℕ) := by
      revert q
      decide
    exact ⟨k, hk⟩
  refine ⟨RegularWreathProduct.inl g, wreathBase (Pi.mulSingle 1 g), ?_, ?_, ?_⟩
  · rw [← map_pow, hg3, map_one]
  · rw [← map_pow, ← Pi.mulSingle_pow, hg3, Pi.mulSingle_one, map_one]
  · rw [eq_top_iff]
    intro w _
    set H := closure ({RegularWreathProduct.inl g, wreathBase (Pi.mulSingle 1 g)} :
      Set WreathThree)
    have ha : RegularWreathProduct.inl g ∈ H := subset_closure (by simp)
    have hb : wreathBase (Pi.mulSingle 1 g) ∈ H := subset_closure (by simp)
    have hinl : ∀ q, (RegularWreathProduct.inl q : WreathThree) ∈ H := fun q => by
      obtain ⟨k, rfl⟩ := hgen q
      rw [map_pow]
      exact pow_mem ha k
    have hsing : ∀ q c, wreathBase (Pi.mulSingle q c) ∈ H := fun q c => by
      obtain ⟨k, rfl⟩ := hgen c
      have h1 : wreathBase (Pi.mulSingle q g) ∈ H := by
        have := H.mul_mem (H.mul_mem (hinl q) hb) (H.inv_mem (hinl q))
        rwa [inl_mul_wreathBase_mul_inl_inv, mulSingle_one_inv_mul] at this
      rw [Pi.mulSingle_pow, map_pow]
      exact pow_mem h1 k
    have hbase : ∀ f, wreathBase f ∈ H := fun f => by
      have : f ∈ H.comap wreathBase := by
        rw [← Finset.univ_prod_mulSingle f]
        exact Subgroup.prod_mem _ fun x _ => hsing x (f x)
      exact this
    obtain ⟨f, q⟩ := w
    rw [mk_eq_wreathBase_mul_inl]
    exact H.mul_mem (hbase f) (hinl q)

theorem card_le_nine_of_surjective {A : Type*} [CommGroup A] (f : WreathThree →* A)
    (hf : Function.Surjective f) : (∀ a : A, a ^ 3 = 1) ∧ Nat.card A ≤ 9 := by
  obtain ⟨a, b, ha, hb, hab⟩ := exists_generators_wreathThree
  have hx : f a ^ 3 = 1 := by rw [← map_pow, ha, map_one]
  have hy : f b ^ 3 = 1 := by rw [← map_pow, hb, map_one]
  have hxinv : (f a)⁻¹ = f a ^ 2 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ']
    exact hx
  have hyinv : (f b)⁻¹ = f b ^ 2 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ']
    exact hy
  have hrange : ∀ z : A, ∃ i j : ℕ, z = f a ^ i * f b ^ j := by
    intro z
    obtain ⟨w, rfl⟩ := hf z
    have hw : w ∈ closure ({a, b} : Set WreathThree) := hab ▸ mem_top w
    induction hw using Subgroup.closure_induction with
    | mem u hu =>
      rcases hu with rfl | rfl
      · exact ⟨1, 0, by simp⟩
      · exact ⟨0, 1, by simp⟩
    | one => exact ⟨0, 0, by simp⟩
    | mul u v _ _ hu hv =>
      obtain ⟨i, j, hij⟩ := hu
      obtain ⟨k, l, hkl⟩ := hv
      refine ⟨i + k, j + l, ?_⟩
      rw [map_mul, hij, hkl, mul_mul_mul_comm, ← pow_add, ← pow_add]
    | inv u _ hu =>
      obtain ⟨i, j, hij⟩ := hu
      refine ⟨2 * i, 2 * j, ?_⟩
      rw [map_inv, hij, mul_inv, ← inv_pow, ← inv_pow, hxinv, hyinv, ← pow_mul, ← pow_mul]
  refine ⟨fun z => ?_, ?_⟩
  · obtain ⟨i, j, rfl⟩ := hrange z
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm i 3, mul_comm j 3, pow_mul, pow_mul, hx, hy]
    simp
  · have hsurj : Function.Surjective
        (fun p : Fin 3 × Fin 3 => f a ^ (p.1 : ℕ) * f b ^ (p.2 : ℕ)) := by
      intro z
      obtain ⟨i, j, rfl⟩ := hrange z
      refine ⟨(⟨i % 3, Nat.mod_lt _ (by norm_num)⟩, ⟨j % 3, Nat.mod_lt _ (by norm_num)⟩), ?_⟩
      simp only
      rw [← pow_eq_pow_mod i hx, ← pow_eq_pow_mod j hy]
    calc Nat.card A ≤ Nat.card (Fin 3 × Fin 3) := Nat.card_le_card_of_surjective _ hsurj
      _ = 9 := by simp

private lemma exists_abelian_normal {X : Type*} [Group X] [Group.IsSolvable X] [Nontrivial X] :
    ∃ A : Subgroup X, A.Normal ∧ A ≠ ⊥ ∧ ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
  classical
  have hex : ∃ n, derivedSeries X n = ⊥ := Group.IsSolvable.solvable
  obtain ⟨n, hn, hmin⟩ : ∃ n, derivedSeries X n = ⊥ ∧ ∀ k < n, derivedSeries X k ≠ ⊥ :=
    ⟨Nat.find hex, Nat.find_spec hex, fun k hk => Nat.find_min hex hk⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
    refine Nat.exists_eq_succ_of_ne_zero ?_
    rintro rfl
    exact top_ne_bot hn
  refine ⟨derivedSeries X m, derivedSeries_normal X m, hmin m (Nat.lt_succ_self m), ?_⟩
  intro x hx y hy
  have hxy : _ ∈ derivedSeries X (m + 1) := commutator_mem_commutator hx hy
  rw [hn, mem_bot] at hxy
  exact commutatorElement_eq_one_iff_mul_comm.mp hxy

private theorem exists_normal_index_three_of_wreath_aux :
    ∀ (n : ℕ) (X : Type) [Group X] [Finite X], Nat.card X = n → Odd (Nat.card X) →
      Group.IsSolvable X → ∀ S : Sylow 3 X, (S : Subgroup X) ≠ ⊥ →
      (∃ f : WreathThree →* (S : Subgroup X), Function.Surjective f) →
      ∃ N : Subgroup X, N.Normal ∧ N.index = 3 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X _ _ hn hodd hsolv S hS hf
  by_cases hab : ∀ x ∈ (S : Subgroup X), ∀ y ∈ (S : Subgroup X), x * y = y * x
  · obtain ⟨f, hf⟩ := hf
    let _ : CommGroup (S : Subgroup X) :=
      { (inferInstance : Group (S : Subgroup X)) with
        mul_comm := fun a b => Subtype.ext (hab a a.2 b b.2) }
    obtain ⟨h3, h9⟩ := card_le_nine_of_surjective f hf
    have hS3 : ∀ x ∈ (S : Subgroup X), x ^ 3 = 1 := fun x hx =>
      Subtype.ext_iff.mp (h3 ⟨x, hx⟩)
    have hcard : Nat.card (S : Subgroup X) = 3 ∨ Nat.card (S : Subgroup X) = 9 := by
      obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
      have h1 : 1 < Nat.card (S : Subgroup X) := (Subgroup.one_lt_card_iff_ne_bot _).mpr hS
      rw [hk] at h1 h9 ⊢
      have hk2 : k ≤ 2 := by
        by_contra h
        have : 3 ^ 3 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      interval_cases k <;> simp_all
    exact exists_normal_index_three_of_odd hodd S hS3 hab hcard
  · have := hsolv
    have : Nontrivial X := by
      obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hS
      exact ⟨a.1, 1, fun h => ha (Subtype.ext h)⟩
    obtain ⟨A, hA, hAbot, hAab⟩ := exists_abelian_normal (X := X)
    have hSA : ¬ (S : Subgroup X) ≤ A := fun h => hab fun x hx y hy => hAab x (h hx) y (h hy)
    have hsurj := QuotientGroup.mk'_surjective A
    have hS'ne : ((Sylow.mapSurjective hsurj S : Sylow 3 (X ⧸ A)) : Subgroup (X ⧸ A)) ≠ ⊥ := by
      rw [Sylow.coe_mapSurjective, Ne, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
      exact hSA
    have hf' : ∃ f : WreathThree →* ((Sylow.mapSurjective hsurj S : Sylow 3 (X ⧸ A)) :
        Subgroup (X ⧸ A)), Function.Surjective f := by
      obtain ⟨f, hf⟩ := hf
      exact ⟨((QuotientGroup.mk' A).subgroupMap (S : Subgroup X)).comp f,
        (MonoidHom.subgroupMap_surjective _ _).comp hf⟩
    have hlt : Nat.card (X ⧸ A) < n := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup A
      have h2 : 1 < Nat.card A := (Subgroup.one_lt_card_iff_ne_bot A).mpr hAbot
      have h3 : 0 < Nat.card (X ⧸ A) := Nat.card_pos
      rw [hn] at h1
      nlinarith
    have hodd' : Odd (Nat.card (X ⧸ A)) :=
      Odd.of_dvd_nat hodd (Subgroup.card_quotient_dvd_card A)
    obtain ⟨N', hN', hi⟩ := ih _ hlt (X ⧸ A) rfl hodd' inferInstance
      (Sylow.mapSurjective hsurj S) hS'ne hf'
    exact ⟨N'.comap (QuotientGroup.mk' A), hN'.comap _, by
      rw [Subgroup.index_comap_of_surjective _ hsurj, hi]⟩

theorem exists_normal_index_three_of_wreath (X : Type) [Group X] [Finite X]
    (hodd : Odd (Nat.card X)) (hsolv : Group.IsSolvable X) (S : Sylow 3 X)
    (hS : (S : Subgroup X) ≠ ⊥)
    (hf : ∃ f : WreathThree →* (S : Subgroup X), Function.Surjective f) :
    ∃ N : Subgroup X, N.Normal ∧ N.index = 3 :=
  exists_normal_index_three_of_wreath_aux _ X rfl hodd hsolv S hS hf

end CFSG.LocalAnalysis.RankThreeUC
