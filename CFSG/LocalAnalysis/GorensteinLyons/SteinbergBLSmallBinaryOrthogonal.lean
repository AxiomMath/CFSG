module

public import CFSG.LinearAlgebra.BinaryReflectionNormalizer
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

public noncomputable section

namespace CFSG.LocalAnalysis.GorensteinLyons

namespace SmallBinaryOrthogonal

open Module TauCeti.QuadraticMap QuadraticMap CFSG.LinearAlgebra

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

theorem eq_one_of_ne_zero {a : ZMod 2} (ha : a ≠ 0) : a = 1 :=
  (zmod_two_cases a).resolve_left ha

theorem eq_of_add_eq_zero {x y : V} (h : x + y = 0) : x = y := by
  rw [eq_neg_of_add_eq_zero_left h, neg_eq_of_add_eq_zero_right (zmod2_vec_add_self y)]

theorem add_add_cancel (x y : V) : x + y + y = x := by
  rw [add_assoc, zmod2_vec_add_self, add_zero]

variable (q : QuadraticForm (ZMod 2) V)

theorem map_add_polar (x y : V) : q (x + y) = q x + q y + polar q x y := by
  rw [polar]
  ring

variable {q}

theorem eq_zero_of_polar (hb : (polarBilin q).Nondegenerate) {x : V}
    (h : ∀ y, polar q x y = 0) : x = 0 :=
  hb.1 x fun y => by rw [polarBilin_apply_apply]; exact h y

theorem exists_polar_eq_one (hb : (polarBilin q).Nondegenerate) {x : V} (hx : x ≠ 0) :
    ∃ y, polar q x y = 1 := by
  by_contra h
  push Not at h
  exact hx (eq_zero_of_polar hb fun y => (zmod_two_cases _).resolve_right (h y))

@[expose] def nonzeroPerm : (V ≃ₗ[ZMod 2] V) →* Equiv.Perm {v : V // v ≠ 0} where
  toFun g := g.toEquiv.subtypeEquiv fun v => by simp
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

theorem nonzeroPerm_injective : Function.Injective (nonzeroPerm (V := V)) := by
  intro g g' h
  refine LinearEquiv.ext fun v => ?_
  by_cases hv : v = 0
  · simp [hv]
  · exact congrArg (fun σ : Equiv.Perm {v : V // v ≠ 0} => (σ ⟨v, hv⟩ : V)) h

section Two

variable [FiniteDimensional (ZMod 2) V]

theorem natCard_nonzero : Nat.card {v : V // v ≠ 0} = 2 ^ finrank (ZMod 2) V - 1 := by
  classical
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have := Fintype.ofFinite V
  rw [Nat.card_eq_fintype_card]
  change Fintype.card {v : V | v ≠ 0} = _
  rw [Set.card_ne_eq, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]

theorem eq_of_finrank_two (hV : finrank (ZMod 2) V = 2) {s w : V} (hs : s ≠ 0)
    (hsw : polar q s w = 1) (v : V) : v = 0 ∨ v = s ∨ v = w ∨ v = s + w := by
  have hli : LinearIndependent (ZMod 2) ![s, w] := by
    refine LinearIndependent.pair_iff.2 fun a c h => ?_
    have hc : c = 0 := by
      have := congrArg (polar q s) h
      rw [polar_add_right, polar_smul_right, polar_smul_right, zmod2_polar_self, hsw,
        polar_zero_right] at this
      simpa using this
    subst hc
    rw [zero_smul, add_zero] at h
    exact ⟨(smul_eq_zero.1 h).resolve_right hs, rfl⟩
  have htop : Submodule.span (ZMod 2) (Set.range ![s, w]) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hli, Fintype.card_fin, hV]
  have hv : v ∈ Submodule.span (ZMod 2) (Set.range ![s, w]) := htop ▸ Submodule.mem_top
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).1 hv
  rw [Fin.sum_univ_two]
  rcases zmod_two_cases (c 0) with h0 | h0 <;> rcases zmod_two_cases (c 1) with h1 | h1 <;>
    simp [h0, h1]

theorem exists_two_singular (hb : (polarBilin q).Nondegenerate) (hV : finrank (ZMod 2) V = 2)
    {s : V} (hs : s ≠ 0) (hqs : q s = 0) :
    ∃ t : V, q t = 0 ∧ t ≠ s ∧ t ≠ 0 ∧ q (s + t) = 1 ∧
      ∀ v : V, v = 0 ∨ v = s ∨ v = t ∨ v = s + t := by
  obtain ⟨w, hw⟩ := exists_polar_eq_one hb hs
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [polar_zero_right] at hw
    exact zero_ne_one hw
  have hws : w ≠ s := by
    rintro rfl
    rw [zmod2_polar_self] at hw
    exact zero_ne_one hw
  have hsw0 : s + w ≠ 0 := fun h => hws (eq_of_add_eq_zero h).symm
  have hsws : s + w ≠ s := fun h => hw0 (by simpa using h)
  have hqsw : q (s + w) = q w + 1 := by rw [map_add_polar, hqs, hw, zero_add]
  have hall := eq_of_finrank_two hV hs hw
  rcases zmod_two_cases (q w) with hq | hq
  · refine ⟨w, hq, hws, hw0, by rw [hqsw, hq, zero_add], fun v => ?_⟩
    rcases hall v with h | h | h | h <;> simp [h]
  · refine ⟨s + w, by rw [hqsw, hq]; rfl, hsws, hsw0, ?_, fun v => ?_⟩
    · rw [← add_assoc, zmod2_vec_add_self, zero_add, hq]
    · rcases hall v with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr (by rw [h, ← add_assoc, zmod2_vec_add_self, zero_add])))
      · exact Or.inr (Or.inr (Or.inl h))

theorem two_dim_singular (hb : (polarBilin q).Nondegenerate) (hV : finrank (ZMod 2) V = 2)
    (hsing : ∃ v : V, v ≠ 0 ∧ q v = 0) :
    Nat.card {v : V // v ≠ 0 ∧ q v = 0} = 2 ∧ Nat.card (orthogonalGroup q) ≤ 2 := by
  obtain ⟨s, hs, hqs⟩ := hsing
  obtain ⟨t, hqt, hts, ht0, hqn, hall⟩ := exists_two_singular hb hV hs hqs
  have hset : {v : V | v ≠ 0 ∧ q v = 0} = {s, t} := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hv0, hqv⟩
      rcases hall v with h | h | h | h
      · exact absurd h hv0
      · exact Or.inl h
      · exact Or.inr h
      · rw [h, hqn] at hqv
        exact absurd hqv one_ne_zero
    · rintro (rfl | rfl)
      · exact ⟨hs, hqs⟩
      · exact ⟨ht0, hqt⟩
  have hcard : Nat.card ({s, t} : Set V) = 2 := by
    rw [Nat.card_coe_set_eq, Set.ncard_pair hts.symm]
  refine ⟨?_, ?_⟩
  · change Nat.card ({v : V | v ≠ 0 ∧ q v = 0} : Set V) = 2
    rw [hset, hcard]
  ·
    have hn : ∀ g ∈ orthogonalGroup q, g (s + t) = s + t := by
      intro g hg
      have hq : q (g (s + t)) = 1 := by rw [map_app_of_mem_orthogonalGroup hg, hqn]
      rcases hall (g (s + t)) with h | h | h | h
      · rw [h, map_zero] at hq
        exact absurd hq zero_ne_one
      · rw [h, hqs] at hq
        exact absurd hq zero_ne_one
      · rw [h, hqt] at hq
        exact absurd hq zero_ne_one
      · exact h
    have hmem : ∀ g ∈ orthogonalGroup q, g s ∈ ({s, t} : Set V) := by
      intro g hg
      have hq : q (g s) = 0 := by rw [map_app_of_mem_orthogonalGroup hg, hqs]
      have h0 : g s ≠ 0 := by simpa using hs
      rw [← hset]
      exact ⟨h0, hq⟩
    let φ : orthogonalGroup q → ({s, t} : Set V) := fun g =>
      ⟨(g : V ≃ₗ[ZMod 2] V) s, hmem _ g.2⟩
    have hφ : Function.Injective φ := by
      intro g g' h
      have hgs : (g : V ≃ₗ[ZMod 2] V) s = (g' : V ≃ₗ[ZMod 2] V) s := congrArg Subtype.val h
      have hgn := (hn _ g.2).trans (hn _ g'.2).symm
      have hgt : (g : V ≃ₗ[ZMod 2] V) t = (g' : V ≃ₗ[ZMod 2] V) t := by
        have e1 : (g : V ≃ₗ[ZMod 2] V) t =
            (g : V ≃ₗ[ZMod 2] V) (s + t) + (g : V ≃ₗ[ZMod 2] V) s := by
          rw [map_add, add_comm ((g : V ≃ₗ[ZMod 2] V) s), add_add_cancel]
        have e2 : (g' : V ≃ₗ[ZMod 2] V) t =
            (g' : V ≃ₗ[ZMod 2] V) (s + t) + (g' : V ≃ₗ[ZMod 2] V) s := by
          rw [map_add, add_comm ((g' : V ≃ₗ[ZMod 2] V) s), add_add_cancel]
        rw [e1, e2, hgn, hgs]
      apply Subtype.ext
      refine LinearEquiv.ext fun v => ?_
      rcases hall v with h | h | h | h <;> subst h
      · simp
      · exact hgs
      · exact hgt
      · exact hgn
    calc Nat.card (orthogonalGroup q) ≤ Nat.card ({s, t} : Set V) :=
          Nat.card_le_card_of_injective φ hφ
      _ = 2 := hcard

variable (q) in
theorem two_dim_embedding (hV : finrank (ZMod 2) V = 2) :
    Nat.card {v : V // v ≠ 0} = 3 ∧
      ∃ f : orthogonalGroup q →* Equiv.Perm (Fin 3), Function.Injective f := by
  have hcard : Nat.card {v : V // v ≠ 0} = 3 := by rw [natCard_nonzero, hV]; rfl
  have : Finite V := Module.finite_of_finite (ZMod 2)
  let e : {v : V // v ≠ 0} ≃ Fin 3 := (Finite.equivFin _).trans (finCongr hcard)
  exact ⟨hcard, e.permCongrHom.toMonoidHom.comp (nonzeroPerm.comp (orthogonalGroup q).subtype),
    e.permCongrHom.injective.comp
      (nonzeroPerm_injective.comp (orthogonalGroup q).subtype_injective)⟩

end Two

section Four

variable [FiniteDimensional (ZMod 2) V]

theorem exists_singular (hV : 3 ≤ finrank (ZMod 2) V) :
    ∃ s : V, s ≠ 0 ∧ q s = 0 := by
  by_contra hcon
  push Not at hcon
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  obtain ⟨u, hu⟩ := exists_ne (0 : V)
  have hK : 2 ≤ finrank (ZMod 2) (LinearMap.ker (polarBilin q u)) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (polarBilin q u)
    have h2 : finrank (ZMod 2) (LinearMap.range (polarBilin q u)) ≤ 1 :=
      (Submodule.finrank_le _).trans (finrank_self (ZMod 2)).le
    omega
  obtain ⟨v, hvK, hvu⟩ : ∃ v ∈ LinearMap.ker (polarBilin q u),
      v ∉ Submodule.span (ZMod 2) {u} := by
    by_contra h
    push Not at h
    have := Submodule.finrank_mono (show LinearMap.ker (polarBilin q u) ≤
      Submodule.span (ZMod 2) {u} from fun v hv => h v hv)
    rw [finrank_span_singleton hu] at this
    omega
  have hv0 : v ≠ 0 := fun h => hvu (h ▸ Submodule.zero_mem _)
  have huv : u + v ≠ 0 := fun h => hvu (by
    rw [← eq_of_add_eq_zero h]
    exact Submodule.mem_span_singleton_self u)
  have hpol : polar q u v = 0 := by
    have := LinearMap.mem_ker.1 hvK
    rwa [polarBilin_apply_apply] at this
  have h := hcon (u + v) huv
  rw [map_add_polar, hpol, eq_one_of_ne_zero (hcon u hu), eq_one_of_ne_zero (hcon v hv0)] at h
  exact h rfl

omit [FiniteDimensional (ZMod 2) V] in
theorem card_filter_polar_eq_one [Fintype V] [DecidableEq V] (hb : (polarBilin q).Nondegenerate)
    (hV : finrank (ZMod 2) V = 4) {s : V} (hs : s ≠ 0) :
    (Finset.univ.filter fun t : V => polar q s t = 1).card = 8 := by
  obtain ⟨w, hw⟩ := exists_polar_eq_one hb hs
  have hbij : (Finset.univ.filter fun t : V => polar q s t = 0).card =
      (Finset.univ.filter fun t : V => polar q s t = 1).card := by
    refine Finset.card_nbij' (· + w) (· + w) ?_ ?_ ?_ ?_
    · intro t ht
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ht ⊢
      rw [polar_add_right, ht, hw, zero_add]
    · intro t ht
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ht ⊢
      rw [polar_add_right, ht, hw]
      rfl
    · intro t _
      exact add_add_cancel t w
    · intro t _
      exact add_add_cancel t w
  have hsum := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun t : V => polar q s t = 0)
  have hneg : (Finset.univ.filter fun t : V => ¬ polar q s t = 0) =
      Finset.univ.filter fun t : V => polar q s t = 1 := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨eq_one_of_ne_zero, fun h => h ▸ one_ne_zero⟩
  rw [hneg, Finset.card_univ, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, hV] at hsum
  omega

theorem natCard_rSub (hb : (polarBilin q).Nondegenerate) (hV : finrank (ZMod 2) V = 4) {s : V}
    (hs : s ≠ 0) (hqs : q s = 0) : Nat.card {t : V // q t = 0 ∧ polar q s t = 1} = 4 := by
  classical
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have := Fintype.ofFinite V
  have h8 := card_filter_polar_eq_one hb hV hs
  set H := Finset.univ.filter fun t : V => polar q s t = 1 with hH
  have hbij : (H.filter fun t => q t = 0).card = (H.filter fun t => ¬ q t = 0).card := by
    refine Finset.card_nbij' (· + s) (· + s) ?_ ?_ ?_ ?_
    · intro t ht
      simp only [hH, Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_ofPred_eq] at ht ⊢
      refine ⟨by rw [polar_add_right, ht.1, zmod2_polar_self, add_zero], ?_⟩
      rw [map_add_polar, ht.2, hqs, polar_comm, ht.1]
      exact one_ne_zero
    · intro t ht
      simp only [hH, Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_ofPred_eq] at ht ⊢
      refine ⟨by rw [polar_add_right, ht.1, zmod2_polar_self, add_zero], ?_⟩
      rw [map_add_polar, eq_one_of_ne_zero ht.2, hqs, polar_comm, ht.1]
      rfl
    · intro t _
      exact add_add_cancel t s
    · intro t _
      exact add_add_cancel t s
  have hsum := Finset.card_filter_add_card_filter_not (s := H) (fun t : V => q t = 0)
  have hR : Nat.card {t : V // q t = 0 ∧ polar q s t = 1} = (H.filter fun t => q t = 0).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext t
    simp [hH, and_comm]
  omega

theorem two_dvd_natCard_singular (hb : (polarBilin q).Nondegenerate)
    (hV : finrank (ZMod 2) V = 4) : 2 ∣ Nat.card {t : V // q t = 0} := by
  classical
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have := Fintype.ofFinite V
  obtain ⟨s, hs, hqs⟩ := exists_singular (q := q) (by omega)
  set Z := Finset.univ.filter fun t : V => q t = 0 with hZ
  have hsum := Finset.card_filter_add_card_filter_not (s := Z) (fun t : V => polar q s t = 0)
  have hA : 2 ∣ (Z.filter fun t => polar q s t = 0).card := by
    let σ : Equiv.Perm {t : V // q t = 0 ∧ polar q s t = 0} :=
      { toFun := fun t => ⟨t + s, by
          rw [map_add_polar, t.2.1, hqs, polar_comm, t.2.2, add_zero, add_zero],
          by rw [polar_add_right, t.2.2, zmod2_polar_self, add_zero]⟩
        invFun := fun t => ⟨t + s, by
          rw [map_add_polar, t.2.1, hqs, polar_comm, t.2.2, add_zero, add_zero],
          by rw [polar_add_right, t.2.2, zmod2_polar_self, add_zero]⟩
        left_inv := fun t => Subtype.ext (add_add_cancel t.1 s)
        right_inv := fun t => Subtype.ext (add_add_cancel t.1 s) }
    have hσ : σ ^ 2 = 1 := by
      ext t
      exact add_add_cancel t.1 s
    have hsupp : σ.support = Finset.univ := by
      ext t
      simp only [Equiv.Perm.mem_support, Finset.mem_univ, iff_true, ne_eq]
      intro h
      have h' : (t : V) + s = t := congrArg Subtype.val h
      exact hs (by simpa using h')
    have h2 := Equiv.Perm.two_dvd_card_support hσ
    rw [hsupp, Finset.card_univ, Fintype.card_subtype] at h2
    convert h2 using 2
    ext t
    simp [hZ]
  have hR : (Z.filter fun t => ¬ polar q s t = 0).card = 4 := by
    have h4 := natCard_rSub hb hV hs hqs
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h4
    rw [← h4]
    congr 1
    ext t
    simp only [hZ, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => ⟨h.1, eq_one_of_ne_zero h.2⟩, fun h => ⟨h.1, h.2 ▸ one_ne_zero⟩⟩
  have hZcard : Nat.card {t : V // q t = 0} = Z.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, hZ]
  rw [hZcard]
  omega

variable (q) in
@[expose] def singularPerm : orthogonalGroup q →* Equiv.Perm {t : V // q t = 0} where
  toFun g := (g : V ≃ₗ[ZMod 2] V).toEquiv.subtypeEquiv fun t => by
    rw [LinearEquiv.coe_toEquiv, map_app_of_mem_orthogonalGroup g.2]
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

theorem exists_fixed_singular (hb : (polarBilin q).Nondegenerate) (hV : finrank (ZMod 2) V = 4)
    (P : Subgroup (orthogonalGroup q)) (hP : IsPGroup 2 P) :
    ∃ s : V, s ≠ 0 ∧ q s = 0 ∧ ∀ g ∈ P, (g : V ≃ₗ[ZMod 2] V) s = s := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  let _ : MulAction P {t : V // q t = 0} := MulAction.compHom _ ((singularPerm q).comp P.subtype)
  have hmod := hP.card_modEq_card_fixedPoints {t : V // q t = 0}
  have hfix : 2 ∣ Nat.card (MulAction.fixedPoints P {t : V // q t = 0}) :=
    Nat.modEq_zero_iff_dvd.1
      (hmod.symm.trans (Nat.modEq_zero_iff_dvd.2 (two_dvd_natCard_singular hb hV)))
  have h0 : (⟨0, map_zero q⟩ : {t : V // q t = 0}) ∈ MulAction.fixedPoints P {t : V // q t = 0} :=
    fun g => Subtype.ext (show ((g : orthogonalGroup q) : V ≃ₗ[ZMod 2] V) 0 = 0 from map_zero _)
  have hpos : 0 < Nat.card (MulAction.fixedPoints P {t : V // q t = 0}) :=
    Nat.card_pos_iff.2 ⟨⟨⟨_, h0⟩⟩, inferInstance⟩
  have hnt : Nontrivial (MulAction.fixedPoints P {t : V // q t = 0}) :=
    Finite.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨x, hx⟩ := exists_ne (⟨_, h0⟩ : MulAction.fixedPoints P {t : V // q t = 0})
  refine ⟨x.1.1, fun h => hx (Subtype.ext (Subtype.ext h)), x.1.2, fun g hg => ?_⟩
  exact congrArg Subtype.val (x.2 ⟨g, hg⟩)

variable (q) in
@[expose] def stabSingular (s : V) : Subgroup (orthogonalGroup q) where
  carrier := {g | (g : V ≃ₗ[ZMod 2] V) s = s}
  one_mem' := rfl
  mul_mem' := fun {g h} hg hh => by
    change (g : V ≃ₗ[ZMod 2] V) ((h : V ≃ₗ[ZMod 2] V) s) = s
    rw [show (h : V ≃ₗ[ZMod 2] V) s = s from hh, show (g : V ≃ₗ[ZMod 2] V) s = s from hg]
  inv_mem' := fun {g} hg => by
    have hg' : (g : V ≃ₗ[ZMod 2] V) s = s := hg
    change ((g⁻¹ : orthogonalGroup q) : V ≃ₗ[ZMod 2] V) s = s
    conv_lhs => rw [← hg']
    change ((g⁻¹ * g : orthogonalGroup q) : V ≃ₗ[ZMod 2] V) s = s
    rw [inv_mul_cancel]
    rfl

variable (q) in
@[expose] def rPerm (s : V) :
    stabSingular q s →* Equiv.Perm {t : V // q t = 0 ∧ polar q s t = 1} where
  toFun g := ((g : orthogonalGroup q) : V ≃ₗ[ZMod 2] V).toEquiv.subtypeEquiv fun t => by
    have hgs : ((g : orthogonalGroup q) : V ≃ₗ[ZMod 2] V) s = s := g.2
    have h := polar_map_of_mem_orthogonalGroup (g : orthogonalGroup q).2 s t
    rw [hgs] at h
    rw [LinearEquiv.coe_toEquiv, map_app_of_mem_orthogonalGroup (g : orthogonalGroup q).2, h]
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

omit [FiniteDimensional (ZMod 2) V] in
theorem span_insert_rSet (hb : (polarBilin q).Nondegenerate) {s : V} (hs : s ≠ 0)
    (hqs : q s = 0) :
    Submodule.span (ZMod 2) (insert s {t : V | q t = 0 ∧ polar q s t = 1}) = ⊤ := by
  obtain ⟨w, hw⟩ := exists_polar_eq_one hb hs
  have hsS : s ∈ Submodule.span (ZMod 2) (insert s {t : V | q t = 0 ∧ polar q s t = 1}) :=
    Submodule.subset_span (Set.mem_insert _ _)
  have h1 : ∀ u, polar q s u = 1 →
      u ∈ Submodule.span (ZMod 2) (insert s {t : V | q t = 0 ∧ polar q s t = 1}) := by
    intro u hu
    rcases zmod_two_cases (q u) with hq | hq
    · exact Submodule.subset_span (Set.mem_insert_of_mem _ ⟨hq, hu⟩)
    · have hmem : u + s ∈
          Submodule.span (ZMod 2) (insert s {t : V | q t = 0 ∧ polar q s t = 1}) := by
        refine Submodule.subset_span (Set.mem_insert_of_mem _ ⟨?_, ?_⟩)
        · calc q (u + s) = 1 + 0 + 1 := by rw [map_add_polar, hq, hqs, polar_comm, hu]
            _ = 0 := rfl
        · rw [polar_add_right, hu, zmod2_polar_self, add_zero]
      have := Submodule.add_mem _ hmem hsS
      rwa [add_add_cancel] at this
  refine eq_top_iff.2 fun u _ => ?_
  rcases zmod_two_cases (polar q s u) with h0 | h0
  · have := Submodule.add_mem _ (h1 (u + w) (by rw [polar_add_right, h0, hw, zero_add])) (h1 w hw)
    rwa [add_add_cancel] at this
  · exact h1 u h0

omit [FiniteDimensional (ZMod 2) V] in
theorem rPerm_injective (hb : (polarBilin q).Nondegenerate) {s : V} (hs : s ≠ 0)
    (hqs : q s = 0) : Function.Injective (rPerm q s) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hfix : ∀ t ∈ insert s {t : V | q t = 0 ∧ polar q s t = 1},
      ((g : orthogonalGroup q) : V ≃ₗ[ZMod 2] V) t = t := by
    rintro t (rfl | ht)
    · exact g.2
    · exact congrArg Subtype.val (Equiv.ext_iff.1 hg ⟨t, ht⟩)
  have hlin : (((g : orthogonalGroup q) : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) = LinearMap.id :=
    LinearMap.ext_on (span_insert_rSet hb hs hqs) fun t ht => hfix t ht
  exact Subtype.ext (Subtype.ext (LinearEquiv.ext fun v => LinearMap.congr_fun hlin v))

end Four

@[expose] def rot4 : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3

@[expose] def ref4 : Equiv.Perm (Fin 4) := Equiv.swap 0 2

@[expose] def d8PermFun : DihedralGroup 4 → Equiv.Perm (Fin 4)
  | .r i => rot4 ^ i.val
  | .sr i => rot4 ^ (-i).val * ref4

theorem d8PermFun_mul : ∀ x y : DihedralGroup 4,
    d8PermFun (x * y) = d8PermFun x * d8PermFun y := by
  decide +kernel

theorem d8PermFun_one : d8PermFun 1 = 1 := by decide +kernel

@[expose] def d8Perm : DihedralGroup 4 →* Equiv.Perm (Fin 4) where
  toFun := d8PermFun
  map_one' := d8PermFun_one
  map_mul' := d8PermFun_mul

theorem d8Perm_injective : Function.Injective d8Perm := by
  intro x y h
  revert x y
  decide +kernel

theorem factorization_twentyFour : (24 : ℕ).factorization 2 = 3 := by
  have hprod : (24 : ℕ) = 2 ^ 3 * 3 := by norm_num
  rw [hprod, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.factorization_pow_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬2 ∣ 3)]

theorem exists_dihedral_of_perm_four {G : Type*} [Group G] (hG : IsPGroup 2 G)
    (ψ : G →* Equiv.Perm (Fin 4)) (hψ : Function.Injective ψ) :
    ∃ f : G →* DihedralGroup 4, Function.Injective f := by
  obtain ⟨T, hT⟩ := (hG.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective).exists_le_sylow
  have hcard : Nat.card d8Perm.range = 2 ^ (Nat.card (Equiv.Perm (Fin 4))).factorization 2 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective d8Perm_injective).toEquiv, DihedralGroup.nat_card,
      Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin,
      show Nat.factorial 4 = 24 from rfl, factorization_twentyFour]
    rfl
  let H : Sylow 2 (Equiv.Perm (Fin 4)) := Sylow.ofCard d8Perm.range hcard
  let e : T ≃* H := Sylow.equiv T H
  let eD : d8Perm.range ≃* DihedralGroup 4 := (MonoidHom.ofInjective d8Perm_injective).symm
  exact ⟨eD.toMonoidHom.comp (e.toMonoidHom.comp ((Subgroup.inclusion hT).comp
      (MonoidHom.ofInjective hψ).toMonoidHom)),
    eD.injective.comp (e.injective.comp ((Subgroup.inclusion_injective hT).comp
      (MonoidHom.ofInjective hψ).injective))⟩

theorem dihedral_four_two_generated (K : Subgroup (DihedralGroup 4)) :
    ∃ x y : DihedralGroup 4, Subgroup.closure {x, y} = K := by
  obtain ⟨n, hn⟩ := (Subgroup.le_zpowers_iff (DihedralGroup.r 1)
    (K ⊓ Subgroup.zpowers (DihedralGroup.r 1))).1 inf_le_right
  set x : DihedralGroup 4 := DihedralGroup.r 1 ^ n with hxdef
  have hrot : ∀ i : ZMod 4, DihedralGroup.r i ∈ Subgroup.zpowers (DihedralGroup.r 1) := by
    intro i
    have := Subgroup.npow_mem_zpowers (DihedralGroup.r (1 : ZMod 4)) i.val
    rwa [DihedralGroup.r_one_pow, ZMod.natCast_zmod_val] at this
  have hxKR : x ∈ K ⊓ Subgroup.zpowers (DihedralGroup.r 1) := by
    rw [hn]
    exact Subgroup.mem_zpowers _
  have hrK : ∀ i, DihedralGroup.r i ∈ K → DihedralGroup.r i ∈ Subgroup.zpowers x := by
    intro i hi
    have : DihedralGroup.r i ∈ K ⊓ Subgroup.zpowers (DihedralGroup.r 1) := ⟨hi, hrot i⟩
    rwa [hn] at this
  by_cases hrefl : ∃ j, DihedralGroup.sr j ∈ K
  · obtain ⟨j, hj⟩ := hrefl
    refine ⟨x, DihedralGroup.sr j, le_antisymm ?_ ?_⟩
    · rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      exacts [hxKR.1, hj]
    · have hz : Subgroup.zpowers x ≤ Subgroup.closure {x, DihedralGroup.sr j} :=
        Subgroup.zpowers_le.2 (Subgroup.subset_closure (Set.mem_insert _ _))
      intro k hk
      cases k with
      | r i => exact hz (hrK i hk)
      | sr i =>
        have h1 : DihedralGroup.r (j - i) ∈ K := by
          have := K.mul_mem hk hj
          rwa [DihedralGroup.sr_mul_sr] at this
        have h2 : DihedralGroup.sr i = DihedralGroup.r (j - i) * DihedralGroup.sr j := by
          rw [DihedralGroup.r_mul_sr, sub_sub_cancel]
        rw [h2]
        exact Subgroup.mul_mem _ (hz (hrK _ h1))
          (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  · push Not at hrefl
    refine ⟨x, x, ?_⟩
    have hKR : K ⊓ Subgroup.zpowers (DihedralGroup.r 1) = K := inf_eq_left.2 fun k hk => by
      cases k with
      | r i => exact hrot i
      | sr i => exact absurd hk (hrefl i)
    rw [Set.pair_eq_singleton, ← Subgroup.zpowers_eq_closure, ← hKR, hn]

theorem two_generated_of_injective {G : Type*} [Group G] (f : G →* DihedralGroup 4)
    (hf : Function.Injective f) : ∃ a b : G, Subgroup.closure {a, b} = ⊤ := by
  obtain ⟨x, y, hxy⟩ := dihedral_four_two_generated f.range
  have hx : x ∈ f.range := hxy ▸ Subgroup.subset_closure (Set.mem_insert x {y})
  have hy : y ∈ f.range := hxy ▸ Subgroup.subset_closure (Set.mem_insert_of_mem x rfl)
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  refine ⟨a, b, Subgroup.map_injective hf ?_⟩
  rw [MonoidHom.map_closure, Set.image_pair, hxy, MonoidHom.range_eq_map]

theorem exists_dihedral_embedding [FiniteDimensional (ZMod 2) V]
    (hb : (polarBilin q).Nondegenerate) (hV : finrank (ZMod 2) V = 4)
    (P : Subgroup (orthogonalGroup q)) (hP : IsPGroup 2 P) :
    ∃ f : P →* DihedralGroup 4, Function.Injective f := by
  obtain ⟨s, hs, hqs, hfix⟩ := exists_fixed_singular hb hV P hP
  have hle : P ≤ stabSingular q s := fun g hg => hfix g hg
  have hcard := natCard_rSub hb hV hs hqs
  have : Finite V := Module.finite_of_finite (ZMod 2)
  let e : {t : V // q t = 0 ∧ polar q s t = 1} ≃ Fin 4 :=
    (Finite.equivFin _).trans (finCongr hcard)
  let ψ : P →* Equiv.Perm (Fin 4) :=
    e.permCongrHom.toMonoidHom.comp ((rPerm q s).comp (Subgroup.inclusion hle))
  have hψ : Function.Injective ψ :=
    e.permCongrHom.injective.comp
      ((rPerm_injective hb hs hqs).comp (Subgroup.inclusion_injective hle))
  exact exists_dihedral_of_perm_four hP ψ hψ

variable (q) in
@[expose] def pointwiseStab (W : Submodule (ZMod 2) V) : Subgroup (orthogonalGroup q) where
  carrier := {g | ∀ w ∈ W, (g : V ≃ₗ[ZMod 2] V) w = w}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {g h} hg hh w hw => by
    change (g : V ≃ₗ[ZMod 2] V) ((h : V ≃ₗ[ZMod 2] V) w) = w
    rw [hh w hw, hg w hw]
  inv_mem' := fun {g} hg w hw => by
    have hg' : (g : V ≃ₗ[ZMod 2] V) w = w := hg w hw
    change ((g⁻¹ : orthogonalGroup q) : V ≃ₗ[ZMod 2] V) w = w
    conv_lhs => rw [← hg']
    change ((g⁻¹ * g : orthogonalGroup q) : V ≃ₗ[ZMod 2] V) w = w
    rw [inv_mul_cancel]
    rfl

theorem sub_mem_orthogonal {W : Submodule (ZMod 2) V} {g : orthogonalGroup q}
    (hg : g ∈ pointwiseStab q W) (x : V) :
    (g : V ≃ₗ[ZMod 2] V) x - x ∈ LinearMap.BilinForm.orthogonal (polarBilin q) W := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro w hw
  have h := polar_map_of_mem_orthogonalGroup g.2 w x
  rw [show (g : V ≃ₗ[ZMod 2] V) w = w from hg w hw] at h
  rw [polarBilin_apply_apply, polar_sub_right, h, sub_self]

section Stab

variable [FiniteDimensional (ZMod 2) V]

theorem natCard_submodule (W : Submodule (ZMod 2) V) :
    Nat.card W = 2 ^ finrank (ZMod 2) W := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have := Fintype.ofFinite W
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]

theorem card_pointwiseStab_hyperplane (hb : (polarBilin q).Nondegenerate)
    (hV : finrank (ZMod 2) V = 4) (W : Submodule (ZMod 2) V) (hW : finrank (ZMod 2) W = 3) :
    Nat.card (pointwiseStab q W) ≤ 2 := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have hWtop : W ≠ ⊤ := fun h => by
    rw [h, finrank_top] at hW
    omega
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : V, x₀ ∉ W := by
    by_contra h
    push Not at h
    exact hWtop (eq_top_iff.2 fun x _ => h x)
  have hsup : W ⊔ Submodule.span (ZMod 2) {x₀} = ⊤ := by
    have hlt : W < W ⊔ Submodule.span (ZMod 2) {x₀} :=
      lt_of_le_of_ne le_sup_left fun h => hx₀ (h ▸ Submodule.mem_sup_right
        (Submodule.mem_span_singleton_self x₀))
    have h1 := Submodule.finrank_lt_finrank_of_lt hlt
    apply Submodule.eq_top_of_finrank_eq
    have h2 := Submodule.finrank_le (W ⊔ Submodule.span (ZMod 2) {x₀})
    omega
  let φ : pointwiseStab q W → LinearMap.BilinForm.orthogonal (polarBilin q) W := fun g =>
    ⟨((g : orthogonalGroup q) : V ≃ₗ[ZMod 2] V) x₀ - x₀, sub_mem_orthogonal g.2 x₀⟩
  have hφ : Function.Injective φ := by
    intro g g' h
    have hx : ((g : orthogonalGroup q) : V ≃ₗ[ZMod 2] V) x₀ =
        ((g' : orthogonalGroup q) : V ≃ₗ[ZMod 2] V) x₀ :=
      sub_left_injective (b := x₀) (congrArg Subtype.val h)
    have hlin : (((g : orthogonalGroup q) : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) =
        ((g' : orthogonalGroup q) : V ≃ₗ[ZMod 2] V) := by
      refine LinearMap.ext_on (s := (W : Set V) ∪ {x₀}) ?_ ?_
      · rw [Submodule.span_union, Submodule.span_eq, hsup]
      · rintro v (hv | rfl)
        · change ((g : orthogonalGroup q) : V ≃ₗ[ZMod 2] V) v =
            ((g' : orthogonalGroup q) : V ≃ₗ[ZMod 2] V) v
          rw [g.2 v hv, g'.2 v hv]
        · exact hx
    exact Subtype.ext (Subtype.ext (LinearEquiv.ext fun v => LinearMap.congr_fun hlin v))
  calc Nat.card (pointwiseStab q W) ≤ Nat.card (LinearMap.BilinForm.orthogonal (polarBilin q) W) :=
        Nat.card_le_card_of_injective φ hφ
    _ = 2 := by
      rw [natCard_submodule, LinearMap.BilinForm.finrank_orthogonal hb, hV, hW]
      rfl

theorem card_pointwiseStab_plane (hb : (polarBilin q).Nondegenerate)
    (hV : finrank (ZMod 2) V = 4) (W : Submodule (ZMod 2) V) (hW : finrank (ZMod 2) W = 2)
    (hq : ∀ w ∈ W, q w = 0) : Nat.card (pointwiseStab q W) ≤ 2 := by
  have hWpol : ∀ w ∈ W, ∀ w' ∈ W, polar q w w' = 0 := fun w hw w' hw' =>
    by rw [polar, hq w hw, hq w' hw', hq _ (W.add_mem hw hw'), sub_zero, sub_zero]
  have hWW : LinearMap.BilinForm.orthogonal (polarBilin q) W = W := by
    symm
    apply Submodule.eq_of_le_of_finrank_eq
    · intro w hw
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro w' hw'
      rw [polarBilin_apply_apply]
      exact hWpol w' hw' w hw
    · rw [LinearMap.BilinForm.finrank_orthogonal hb, hV, hW]
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl W
  have hCrank : finrank (ZMod 2) C = 2 := by
    have := Submodule.finrank_add_eq_of_isCompl hC
    omega
  let bC := Module.finBasisOfFinrankEq (ZMod 2) C hCrank
  set f₁ : V := (bC 0 : V) with hf₁
  set f₂ : V := (bC 1 : V) with hf₂
  have hdecomp : ∀ v : V, ∃ w ∈ W, ∃ a c : ZMod 2, v = w + a • f₁ + c • f₂ := by
    intro v
    have hv : v ∈ W ⊔ C := hC.sup_eq_top ▸ Submodule.mem_top
    obtain ⟨w, hw, y, hy, rfl⟩ := Submodule.mem_sup.1 hv
    refine ⟨w, hw, bC.repr ⟨y, hy⟩ 0, bC.repr ⟨y, hy⟩ 1, ?_⟩
    have hsum := bC.sum_repr ⟨y, hy⟩
    rw [Fin.sum_univ_two] at hsum
    have := congrArg Subtype.val hsum
    simp only [Submodule.coe_add, Submodule.coe_smul] at this
    rw [add_assoc]
    exact congrArg (w + ·) this.symm
  have hN : ∀ g ∈ pointwiseStab q W, ∀ x, (g : V ≃ₗ[ZMod 2] V) x - x ∈ W := fun g hg x =>
    hWW ▸ sub_mem_orthogonal hg x
  have hNx : ∀ g ∈ pointwiseStab q W, ∀ x, polar q x ((g : V ≃ₗ[ZMod 2] V) x - x) = 0 := by
    intro g hg x
    have h1 := map_add_polar q x ((g : V ≃ₗ[ZMod 2] V) x - x)
    rw [add_sub_cancel, map_app_of_mem_orthogonalGroup g.2, hq _ (hN g hg x), add_zero] at h1
    linear_combination -h1
  have hsymm : ∀ g ∈ pointwiseStab q W,
      polar q f₂ ((g : V ≃ₗ[ZMod 2] V) f₁ - f₁) = polar q f₁ ((g : V ≃ₗ[ZMod 2] V) f₂ - f₂) := by
    intro g hg
    have h := hNx g hg (f₁ + f₂)
    rw [map_add, show (g : V ≃ₗ[ZMod 2] V) f₁ + (g : V ≃ₗ[ZMod 2] V) f₂ - (f₁ + f₂) =
      ((g : V ≃ₗ[ZMod 2] V) f₁ - f₁) + ((g : V ≃ₗ[ZMod 2] V) f₂ - f₂) by abel,
      polar_add_left, polar_add_right, polar_add_right, hNx g hg f₁, hNx g hg f₂, zero_add,
      add_zero] at h
    exact (zmod2_eq_of_add_eq_zero h).symm
  have hdet : ∀ n ∈ W, polar q f₁ n = 0 → polar q f₂ n = 0 → n = 0 := by
    intro n hn h1 h2
    refine eq_zero_of_polar hb fun v => ?_
    obtain ⟨w, hw, a, c, rfl⟩ := hdecomp v
    rw [polar_comm, polar_add_left, polar_add_left, polar_smul_left, polar_smul_left, h1, h2,
      hWpol w hw n hn, smul_zero, smul_zero, add_zero, add_zero]
  let φ : pointwiseStab q W → ZMod 2 := fun g =>
    polar q f₁ (((g : orthogonalGroup q) : V ≃ₗ[ZMod 2] V) f₂ - f₂)
  have hφ : Function.Injective φ := by
    intro g g' h
    have h' : polar q f₁ (((g : orthogonalGroup q) : V ≃ₗ[ZMod 2] V) f₂ - f₂) =
        polar q f₁ (((g' : orthogonalGroup q) : V ≃ₗ[ZMod 2] V) f₂ - f₂) := h
    set G : V ≃ₗ[ZMod 2] V := ((g : orthogonalGroup q) : V ≃ₗ[ZMod 2] V) with hG
    set G' : V ≃ₗ[ZMod 2] V := ((g' : orthogonalGroup q) : V ≃ₗ[ZMod 2] V) with hG'
    have e1 : G f₁ = G' f₁ := by
      have hz := hdet ((G f₁ - f₁) - (G' f₁ - f₁)) (W.sub_mem (hN _ g.2 f₁) (hN _ g'.2 f₁))
        (by rw [polar_sub_right, hNx _ g.2 f₁, hNx _ g'.2 f₁, sub_self])
        (by rw [polar_sub_right, hsymm _ g.2, hsymm _ g'.2, h', sub_self])
      rw [sub_sub_sub_cancel_right, sub_eq_zero] at hz
      exact hz
    have e2 : G f₂ = G' f₂ := by
      have hz := hdet ((G f₂ - f₂) - (G' f₂ - f₂)) (W.sub_mem (hN _ g.2 f₂) (hN _ g'.2 f₂))
        (by rw [polar_sub_right, h', sub_self])
        (by rw [polar_sub_right, hNx _ g.2 f₂, hNx _ g'.2 f₂, sub_self])
      rw [sub_sub_sub_cancel_right, sub_eq_zero] at hz
      exact hz
    refine Subtype.ext (Subtype.ext (LinearEquiv.ext fun v => ?_))
    obtain ⟨w, hw, a, c, rfl⟩ := hdecomp v
    change G (w + a • f₁ + c • f₂) = G' (w + a • f₁ + c • f₂)
    rw [map_add, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul, e1, e2,
      g.2 w hw, g'.2 w hw]
  calc Nat.card (pointwiseStab q W) ≤ Nat.card (ZMod 2) := Nat.card_le_card_of_injective φ hφ
    _ = 2 := Nat.card_zmod 2

end Stab

end SmallBinaryOrthogonal

open SmallBinaryOrthogonal TauCeti.QuadraticMap Module in
theorem small_binary_orthogonal_two_subgroups_and_stabilizers {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] (q : QuadraticForm (ZMod 2) V)
    (hb : (QuadraticMap.polarBilin q).Nondegenerate)
    (_hV : finrank (ZMod 2) V = 2 ∨ finrank (ZMod 2) V = 4) :
    (finrank (ZMod 2) V = 2 →
      Nat.card {v : V // v ≠ 0} = 3 ∧
      (∃ f : orthogonalGroup q →* Equiv.Perm (Fin 3), Function.Injective f) ∧
      ((∃ v : V, v ≠ 0 ∧ q v = 0) →
        Nat.card {v : V // v ≠ 0 ∧ q v = 0} = 2 ∧ Nat.card (orthogonalGroup q) ≤ 2)) ∧
    (finrank (ZMod 2) V = 4 →
      (∀ P : Subgroup (orthogonalGroup q), IsPGroup 2 P →
        (∃ f : P →* DihedralGroup 4, Function.Injective f) ∧
        ∃ a b : P, Subgroup.closure {a, b} = ⊤) ∧
      (∀ W : Submodule (ZMod 2) V, finrank (ZMod 2) W = 3 →
        Nat.card (pointwiseStab q W) ≤ 2) ∧
      (∀ W : Submodule (ZMod 2) V, finrank (ZMod 2) W = 2 → (∀ w ∈ W, q w = 0) →
        Nat.card (pointwiseStab q W) ≤ 2)) := by
  refine ⟨fun hV => ?_, fun hV => ⟨fun P hP => ?_, fun W hW => card_pointwiseStab_hyperplane hb
    hV W hW, fun W hW hqW => card_pointwiseStab_plane hb hV W hW hqW⟩⟩
  · obtain ⟨h3, hf⟩ := two_dim_embedding q hV
    exact ⟨h3, hf, two_dim_singular hb hV⟩
  · obtain ⟨f, hf⟩ := exists_dihedral_embedding hb hV P hP
    exact ⟨⟨f, hf⟩, two_generated_of_injective f hf⟩

end CFSG.LocalAnalysis.GorensteinLyons
