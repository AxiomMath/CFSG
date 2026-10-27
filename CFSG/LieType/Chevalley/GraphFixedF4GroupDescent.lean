module

public import CFSG.LieType.Chevalley.GraphFixedF4GroupRestriction
public import CFSG.LieType.Chevalley.CoordinateFieldFixedSubgroup

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LieType.Steinberg.Adjoint (BaseChange)

theorem baseChangeGL_torusElt
    {R S : Type} [Field R] [Field S] (f : R →+* S) {τ : Tag}
    (i : Fin τ.rank) (t : Rˣ) :
    baseChangeGL f (torusElt τ R i t) = torusElt τ S i (Units.map f.toMonoidHom t) := by
  refine Units.ext ((baseChange_baseChangeEnd f _).unique ?_)
  rw [torusElt, torusElt, Units.val_mul, Units.val_mul]
  have h := (BaseChange.weylElt (f := f) i t).mul (BaseChange.weylElt (f := f) i (-1))
  rwa [show Units.map f.toMonoidHom (-1) = -1 from Units.ext (by simp)] at h

section Frobenius

variable {k L : Type} [Field k] [Finite k] [Field L] [Algebra k L]

theorem mem_range_algebraMap_of_pow_card_eq {c : L} (hc : c ^ Nat.card k = c) :
    c ∈ Set.range (algebraMap k L) := by
  classical
  have : Fintype k := Fintype.ofFinite k
  rw [Nat.card_eq_fintype_card] at hc
  have hq1 : 1 < Fintype.card k := Fintype.one_lt_card
  have hP0 : (Polynomial.X ^ Fintype.card k - Polynomial.X : Polynomial L) ≠ 0 :=
    FiniteField.X_pow_card_sub_X_ne_zero L hq1
  have hroot : ∀ x : L, x ^ Fintype.card k = x →
      x ∈ (Polynomial.X ^ Fintype.card k - Polynomial.X : Polynomial L).roots.toFinset :=
    fun x hx => by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0, Polynomial.IsRoot.def,
        Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, hx, sub_self]
  have hS : Finset.univ.image (algebraMap k L) ⊆
      (Polynomial.X ^ Fintype.card k - Polynomial.X : Polynomial L).roots.toFinset := fun x hx => by
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hx
    exact hroot _ (by rw [← map_pow, FiniteField.pow_card])
  have hcard : (Polynomial.X ^ Fintype.card k - Polynomial.X : Polynomial L).roots.toFinset.card ≤
      (Finset.univ.image (algebraMap k L)).card := by
    rw [Finset.card_image_of_injective _ (algebraMap k L).injective, Finset.card_univ]
    exact (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans
      (FiniteField.X_pow_card_sub_X_natDegree_eq L hq1).le)
  have hc' := hroot c hc
  rw [← Finset.eq_of_subset_of_card_le hS hcard] at hc'
  obtain ⟨a, -, ha⟩ := Finset.mem_image.1 hc'
  exact ⟨a, ha⟩

theorem frobenius_comp_algebraMap (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card k) :
    Fr.comp (algebraMap k L) = algebraMap k L := by
  have : Fintype k := Fintype.ofFinite k
  ext a
  rw [RingHom.comp_apply, hFr, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]

theorem units_map_entrywiseHom_baseChangeGL_algebraMap
    (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ Nat.card k) {τ : Tag} (g : ModGL τ k) :
    Units.map (entrywiseHom Fr) (baseChangeGL (algebraMap k L) g) =
      baseChangeGL (algebraMap k L) g := by
  change baseChangeGL Fr (baseChangeGL (algebraMap k L) g) = _
  rw [baseChangeGL_baseChangeGL, frobenius_comp_algebraMap Fr hFr]

variable [IsAlgClosed L]

omit [Algebra k L] in
theorem frobenius_bijective (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card k) :
    Function.Bijective Fr :=
  ⟨Fr.injective, fun y => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq y (Nat.card_pos (α := k))
    exact ⟨z, by rw [hFr, hz]⟩⟩

theorem mem_map_adjointGroup_F4_of_frobenius_fixed
    (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ Nat.card k) {g : ModGL Tag.F4 L} (hg : g ∈ adjointGroup Tag.F4 L)
    (hfix : Units.map (entrywiseHom Fr) g = g) :
    g ∈ (adjointGroup Tag.F4 k).map (baseChangeGL (algebraMap k L)) := by
  set σ : L ≃+* L := RingEquiv.ofBijective Fr (frobenius_bijective Fr hFr)
  have hσ : σ.toRingHom = Fr := RingHom.ext fun _ => rfl
  have hσfix : ∀ c, σ c = c → c ∈ Set.range (algebraMap k L) := fun c hc =>
    mem_range_algebraMap_of_pow_card_eq (by rw [← hFr]; exact hc)
  have hg' : g ∈ entrywiseFixedGroup Tag.F4 σ := ⟨hg, by
    change Units.map (entrywiseHom σ.toRingHom) g = g
    rw [hσ]
    exact hfix⟩
  obtain ⟨h, hh, j, hj, rfl⟩ := mem_mul_of_mem_entrywiseFixedGroup hg'
  refine mul_mem ?_ ?_
  · obtain ⟨hhT, -, hhF⟩ := hh
    obtain ⟨t, ht⟩ := torusCoordHom_surjective (τ := Tag.F4) (R := L) ⟨h, hhT⟩
    have hval : h = (List.ofFn fun i => torusElt Tag.F4 L i (t i)).prod := by
      have := congrArg Subtype.val ht
      rw [coe_torusCoordHom] at this
      exact this.symm
    have hσt : torusCoordHom Tag.F4 L (fun i => Units.map σ.toRingHom.toMonoidHom (t i)) =
        torusCoordHom Tag.F4 L t := by
      refine Subtype.ext ?_
      rw [coe_torusCoordHom, coe_torusCoordHom]
      have h1 : Units.map (entrywiseHom σ.toRingHom) h = h := hhF
      rw [hval, map_list_prod, List.map_ofFn] at h1
      simpa only [Function.comp_def, entrywise_torusElt] using h1
    have ht' := torusCoordHom_injective_of_mul_eq_one cartan_mul_cartanInv_F4 hσt
    rw [hval]
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
    have hfi : σ (t i : L) = t i := congrArg Units.val (congrFun ht' i)
    obtain ⟨s, hs⟩ := hσfix _ hfi
    have hs0 : s ≠ 0 := fun h0 => (t i).ne_zero (by rw [← hs, h0, map_zero])
    refine ⟨torusElt Tag.F4 k i (Units.mk0 s hs0), torusElt_mem_adjointGroup i _, ?_⟩
    rw [baseChangeGL_torusElt]
    exact congrArg _ (Units.ext hs)
  · rw [fixedFieldImage_eq_closure] at hj
    refine (Subgroup.closure_le _).2 ?_ hj
    rintro _ ⟨i, c, hc, rfl | rfl⟩
    · obtain ⟨c', rfl⟩ := hσfix c hc
      exact ⟨xUnit Tag.F4 k i c', xUnit_mem_adjointGroup i c', baseChangeGL_xUnit _ i c'⟩
    · obtain ⟨c', rfl⟩ := hσfix c hc
      exact ⟨yUnit Tag.F4 k i c', yUnit_mem_adjointGroup i c', baseChangeGL_yUnit _ i c'⟩

theorem F4_frobenius_fixed_eq_map
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card k) :
    adjointGroup Tag.F4 L ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) =
      (adjointGroup Tag.F4 k).map (baseChangeGL (algebraMap k L)) := by
  refine le_antisymm (fun g hg => mem_map_adjointGroup_F4_of_frobenius_fixed Fr hFr hg.1 hg.2) ?_
  rintro _ ⟨g, hg, rfl⟩
  exact ⟨baseChangeGL_mem_adjointGroup _ hg,
    units_map_entrywiseHom_baseChangeGL_algebraMap Fr hFr g⟩

end Frobenius

section E6

variable {k L : Type} [Field k] [Finite k] [Field L] [Algebra k L] [IsAlgClosed L]

theorem two_eq_zero_of_ringChar {K : Type} [Field K] (hK : ringChar K = 2) : (2 : K) = 0 := by
  have : CharP K 2 := ringChar.of_eq hK
  exact_mod_cast CharP.cast_eq_zero K 2

theorem e6_frobenius_fixed_eq_map
    (hk : ringChar k = 2) (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ Nat.card k) :
    twistedFixedGroup TwistTag.E6 L (RingHom.id L) ⊓
        (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) =
      (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL (algebraMap k L)) := by
  have hk2 : (2 : k) = 0 := two_eq_zero_of_ringChar hk
  have hL2 : (2 : L) = 0 := by
    rw [← map_ofNat (algebraMap k L) 2, hk2, map_zero]
  refine le_antisymm (fun g hg => ?_) ?_
  · obtain ⟨hgΓ, hgF⟩ := hg
    have hfix : Units.map (entrywiseHom Fr) g = g := hgF
    have hΨ : Units.map (entrywiseHom Fr) (e6FixedToF4 L ⟨g, hgΓ⟩) = e6FixedToF4 L ⟨g, hgΓ⟩ := by
      have h := e6FixedToF4_baseChangeGL Fr ⟨g, hgΓ⟩
      have e : (⟨baseChangeGL Fr g, baseChangeGL_mem_twistedFixedGroup Fr hgΓ⟩ :
          twistedFixedGroup TwistTag.E6 L (RingHom.id L)) = ⟨g, hgΓ⟩ := Subtype.ext hfix
      rw [e] at h
      exact h.symm
    obtain ⟨f, hf, hfg⟩ := mem_map_adjointGroup_F4_of_frobenius_fixed Fr hFr
      (e6FixedToF4_mem_adjointGroup hL2 ⟨g, hgΓ⟩) hΨ
    obtain ⟨g', hg'⟩ := e6FixedToF4Group_surjective hk2 ⟨f, hf⟩
    have hg'f : e6FixedToF4 k g' = f := congrArg Subtype.val hg'
    refine ⟨g', g'.2, ?_⟩
    have h := e6FixedToF4_baseChangeGL (algebraMap k L) g'
    rw [hg'f, hfg] at h
    have hinj := e6FixedToF4Group_injective hL2
      (a₁ := ⟨_, baseChangeGL_mem_twistedFixedGroup (algebraMap k L) g'.2⟩) (a₂ := ⟨g, hgΓ⟩)
      (Subtype.ext h)
    exact congrArg Subtype.val hinj
  · rintro _ ⟨g, hg, rfl⟩
    exact ⟨baseChangeGL_mem_twistedFixedGroup _ hg,
      units_map_entrywiseHom_baseChangeGL_algebraMap Fr hFr g⟩

end E6

end CFSG.LieType.Chevalley
