module

public import CFSG.LieType.Steinberg.CentralExt.MinusculeCentrallyClosed
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.CentralExt.MinusculeClosed CFSG.LieType.CurtisTits

@[expose] def e6Node0 : Fin Tag.E6.rank := ⟨0, by decide⟩

@[expose] def e6Node2 : Fin Tag.E6.rank := ⟨2, by decide⟩

section Zeta

variable {F : Type} [Field F]

@[expose] noncomputable def zeta3Hom (ζ : Fˣ) (hζ : orderOf ζ = 3) : Multiplicative (ZMod 3) →* Fˣ where
  toFun a := ζ ^ (Multiplicative.toAdd a).val
  map_one' := by simp
  map_mul' a b := by
    rw [toAdd_mul, ZMod.val_add, ← pow_add]
    have h := pow_mod_orderOf ζ ((Multiplicative.toAdd a).val + (Multiplicative.toAdd b).val)
    rw [hζ] at h
    exact h

theorem zeta3Hom_apply (ζ : Fˣ) (hζ : orderOf ζ = 3) (a : Multiplicative (ZMod 3)) :
    zeta3Hom ζ hζ a = ζ ^ (Multiplicative.toAdd a).val := rfl

@[expose] noncomputable def zeta3Pi {n : ℕ} (ζ : Fˣ) (hζ : orderOf ζ = 3) :
    Multiplicative (Fin n → ZMod 3) →* (Fin n → Fˣ) where
  toFun x k := zeta3Hom ζ hζ (Multiplicative.ofAdd (Multiplicative.toAdd x k))
  map_one' := by
    ext k
    simp
  map_mul' x y := by
    ext k
    simp [map_mul]

theorem zeta3Pi_apply {n : ℕ} (ζ : Fˣ) (hζ : orderOf ζ = 3)
    (x : Multiplicative (Fin n → ZMod 3)) (k : Fin n) :
    zeta3Pi ζ hζ x k = ζ ^ (Multiplicative.toAdd x k).val := rfl

end Zeta

section Cartan

theorem card_cartan_kernel :
    (Finset.univ.filter (fun x : Fin Tag.E6.rank → ZMod 3 =>
      ∀ i : Fin Tag.E6.rank, (3 : ℤ) ∣
        ∑ j : Fin Tag.E6.rank, ((x j).val : ℤ) * Tag.E6.cartan j i)).card = 3 := by
  decide +kernel

end Cartan

section E6

variable {F : Type} [Field F] [Finite F]

theorem rootChar_simple_eq_one_of_isogeny_eq_one (u : Fin Tag.E6.rank → Fˣ)
    (h : e6Isogeny F (minTorus e6Data_valid F u) = 1) (i : Fin Tag.E6.rank) :
    ExceptionalCover.rootChar F (Pi.single i 1 : Fin Tag.E6.rank → ℤ) u = 1 := by
  have hconj := minTorus_conj_xm e6Data_valid F u (IsRoot.basis i) (1 : F)
  have h1 := congrArg (e6Isogeny F) hconj
  rw [map_mul, map_mul, h, one_mul, map_inv, h, inv_one, mul_one, e6Isogeny_xm_single,
    e6Isogeny_xm_single] at h1
  have h2 := eltElement_injective (simpleRoot Tag.E6 i) h1
  exact Units.ext (by simpa using h2.symm)

theorem rootChar_simple_zeta3Pi (ζ : Fˣ) (hζ : orderOf ζ = 3)
    (x : Multiplicative (Fin Tag.E6.rank → ZMod 3)) (i : Fin Tag.E6.rank) :
    ExceptionalCover.rootChar F (Pi.single i 1 : Fin Tag.E6.rank → ℤ) (zeta3Pi ζ hζ x) =
      ζ ^ (∑ k : Fin Tag.E6.rank, (((Multiplicative.toAdd x k).val : ℤ) * Tag.E6.cartan k i)) := by
  rw [ExceptionalCover.rootChar_apply, ← prod_zpow_eq_zpow_sum]
  refine Finset.prod_congr rfl fun k _ => ?_
  have hc : ExceptionalCover.cartanCoord (Pi.single i 1 : Fin Tag.E6.rank → ℤ) k =
      Tag.E6.cartan k i := by
    simp [ExceptionalCover.cartanCoord, Pi.single_apply]
  rw [hc, zeta3Pi_apply, ← zpow_natCast, ← zpow_mul]

theorem card_ker_torus_zeta_le (ζ : Fˣ) (hζ : orderOf ζ = 3) :
    Nat.card ((e6Isogeny F).comp ((minTorus e6Data_valid F).comp (zeta3Pi ζ hζ))).ker ≤ 3 := by
  classical
  set Θ := (e6Isogeny F).comp ((minTorus e6Data_valid F).comp (zeta3Pi ζ hζ)) with hΘ
  set S : Finset (Fin Tag.E6.rank → ZMod 3) :=
    Finset.univ.filter (fun x : Fin Tag.E6.rank → ZMod 3 =>
      ∀ i : Fin Tag.E6.rank, (3 : ℤ) ∣
        ∑ j : Fin Tag.E6.rank, ((x j).val : ℤ) * Tag.E6.cartan j i) with hS
  have hsub : ∀ x ∈ Θ.ker, Multiplicative.toAdd x ∈ S := by
    intro x hx
    rw [hS, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun i => ?_⟩
    have hx' : e6Isogeny F (minTorus e6Data_valid F (zeta3Pi ζ hζ x)) = 1 := hx
    have h1 := rootChar_simple_eq_one_of_isogeny_eq_one (F := F) (zeta3Pi ζ hζ x) hx' i
    rw [rootChar_simple_zeta3Pi] at h1
    have h2 := (orderOf_dvd_iff_zpow_eq_one (x := ζ)).2 h1
    rwa [hζ] at h2
  have hScard : Nat.card {y : Fin Tag.E6.rank → ZMod 3 // y ∈ S} = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    exact card_cartan_kernel
  let f : Θ.ker → {y : Fin Tag.E6.rank → ZMod 3 // y ∈ S} := fun x =>
    ⟨Multiplicative.toAdd (x : Multiplicative (Fin Tag.E6.rank → ZMod 3)), hsub x x.2⟩
  have hf : Function.Injective f := by
    intro a b h
    have h' : Multiplicative.toAdd (a : Multiplicative (Fin Tag.E6.rank → ZMod 3)) =
        Multiplicative.toAdd (b : Multiplicative (Fin Tag.E6.rank → ZMod 3)) :=
      congrArg (fun y : {y : Fin Tag.E6.rank → ZMod 3 // y ∈ S} => y.1) h
    exact Subtype.ext (Multiplicative.toAdd.injective h')
  exact (Nat.card_le_card_of_injective f hf).trans hScard.le

theorem le_normalizer_of_conj_mem {G : Type*} [Group G] {E X : Subgroup G}
    (h : ∀ e ∈ E, ∀ y ∈ X, e * y * e⁻¹ ∈ X) : E ≤ Subgroup.normalizer (X : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact fun hy => h g hg y hy
  · intro hy
    have := h g⁻¹ (E.inv_mem hg) _ hy
    simpa [mul_assoc] using this

theorem map_le_normalizer_map {G H : Type*} [Group G] [Group H] (f : G →* H) {E X : Subgroup G}
    (h : E ≤ Subgroup.normalizer (X : Set G)) :
    E.map f ≤ Subgroup.normalizer ((X.map f : Subgroup H) : Set H) := by
  rintro _ ⟨e, he, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro z
  have hc : ∀ e ∈ E, ∀ y ∈ X, e * y * e⁻¹ ∈ X := fun e he y hy =>
    (Subgroup.mem_normalizer_iff.1 (h he) y).1 hy
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨e * y * e⁻¹, hc e he y hy, by simp⟩
  · rintro ⟨y', hy', hz⟩
    refine ⟨e⁻¹ * y' * e, ?_, ?_⟩
    · simpa using hc e⁻¹ (E.inv_mem he) y' hy'
    · have : f y' = f e * z * (f e)⁻¹ := hz
      simp only [map_mul, map_inv, this]
      group

theorem card_multiplicative_pi_zmod_three :
    Nat.card (Multiplicative (Fin Tag.E6.rank → ZMod 3)) = 3 ^ 6 := by
  rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin Tag.E6.rank → ZMod 3) ≃ _)]
  rw [Nat.card_eq_fintype_card]
  simp [Fintype.card_fun, ZMod.card]
  rfl

theorem three_pow_five_le_card_image (ζ : Fˣ) (hζ : orderOf ζ = 3) :
    3 ^ 5 ≤ Nat.card (((minTorus e6Data_valid F).comp (zeta3Pi ζ hζ)).range.map (e6Isogeny F)) := by
  set τ := (minTorus e6Data_valid F).comp (zeta3Pi ζ hζ) with hτ
  have hmap : τ.range.map (e6Isogeny F) = ((e6Isogeny F).comp τ).range :=
    (MonoidHom.range_comp (e6Isogeny F) τ).symm
  rw [hmap]
  have hprod := Subgroup.card_ker_mul_card_range ((e6Isogeny F).comp τ)
  have hker := card_ker_torus_zeta_le (F := F) ζ hζ
  rw [card_multiplicative_pi_zmod_three] at hprod
  have hpos : 0 < Nat.card ((e6Isogeny F).comp τ).range := Nat.card_pos
  by_contra hlt
  push Not at hlt
  have : Nat.card ((e6Isogeny F).comp τ).ker * Nat.card ((e6Isogeny F).comp τ).range <
      3 ^ 6 := by
    calc Nat.card ((e6Isogeny F).comp τ).ker * Nat.card ((e6Isogeny F).comp τ).range
        ≤ 3 * Nat.card ((e6Isogeny F).comp τ).range := Nat.mul_le_mul_right _ hker
      _ < 3 * 3 ^ 5 := by omega
      _ = 3 ^ 6 := by norm_num
  omega

theorem isElemAbelian_range_of_pow_three {A G : Type*} [CommGroup A] [Group G] (f : A →* G)
    (h : ∀ a : A, a ^ 3 = 1) : IsElemAbelian 3 f.range := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ : (∃ x, f x = a.1) ∧ ∃ y, f y = b.1 := ⟨a.2, b.2⟩
    apply Subtype.ext
    show a.1 * b.1 = b.1 * a.1
    rw [← hx, ← hy, ← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨x, rfl⟩
    rw [← map_pow, h, map_one]

theorem pow_three_multiplicative_pi (n : ℕ) (a : Multiplicative (Fin n → ZMod 3)) : a ^ 3 = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  ext k
  simp only [Pi.smul_apply, Pi.zero_apply]
  generalize Multiplicative.toAdd a k = z
  revert z
  decide

theorem e6_even_witness (h2 : (2 : F) = 0) (ζ : Fˣ) (hζ : orderOf ζ = 3) :
    ∃ U : Subgroup (adjointGroup Tag.E6 F), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      (((minTorus e6Data_valid F).comp (zeta3Pi ζ hζ)).range).map (e6Isogeny F) ≤
        Subgroup.normalizer (U : Set (adjointGroup Tag.E6 F)) := by
  classical
  set X : Subgroup (e6Data_valid.minGroup F) :=
    e6Data_valid.rootGroup F (Pi.single e6Node0 1 : Fin Tag.E6.rank → ℤ) with hX
  have hXnorm : ((minTorus e6Data_valid F).comp (zeta3Pi ζ hζ)).range ≤
      Subgroup.normalizer (X : Set (e6Data_valid.minGroup F)) := by
    refine le_normalizer_of_conj_mem fun e he y hy => ?_
    obtain ⟨x, rfl⟩ := he
    obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup F).1 hy
    have := minTorus_conj_xm e6Data_valid F (zeta3Pi ζ hζ x) (IsRoot.basis e6Node0) c
    refine ?_
    show minTorus e6Data_valid F (zeta3Pi ζ hζ x) * _ * (minTorus e6Data_valid F (zeta3Pi ζ hζ x))⁻¹
      ∈ X
    rw [this]
    exact e6Data_valid.xm_mem_rootGroup F _ _
  refine ⟨X.map (e6Isogeny F), ?_, ?_, map_le_normalizer_map _ hXnorm⟩
  · intro hbot
    have hmem : e6Isogeny F (e6Data_valid.xm F (Pi.single e6Node0 1) 1) ∈ X.map (e6Isogeny F) :=
      ⟨_, e6Data_valid.xm_mem_rootGroup F _ _, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact e6Isogeny_xm_single_one_ne_one F e6Node0 hmem
  · have hX2 : IsPGroup 2 X := by
      intro g
      obtain ⟨c, hc⟩ := (e6Data_valid.mem_rootGroup F).1 g.2
      refine ⟨1, Subtype.ext ?_⟩
      show (g : e6Data_valid.minGroup F) ^ 2 = 1
      rw [← hc, pow_two, ← e6Data_valid.xm_add]
      have : c + c = 0 := by rw [← two_mul, h2, zero_mul]
      rw [this, e6Data_valid.xm_zero]
    exact hX2.map (e6Isogeny F)

@[expose] noncomputable def e6Inv0 : Fin Tag.E6.rank → Fˣ := Pi.mulSingle e6Node0 (-1)

theorem e6Inv0_sq : (e6Inv0 : Fin Tag.E6.rank → Fˣ) ^ 2 = (1 : Fin Tag.E6.rank → Fˣ) := by
  ext k
  by_cases hk : k = e6Node0
  · subst hk
    simp [e6Inv0]
  · simp [e6Inv0, Pi.mulSingle_eq_of_ne hk]

theorem e6Inv0_isogeny_ne_one (h2 : (2 : F) ≠ 0) :
    e6Isogeny F (minTorus e6Data_valid F e6Inv0) ≠ 1 := by
  intro h
  have h1 := rootChar_simple_eq_one_of_isogeny_eq_one (F := F) _ h e6Node2
  rw [e6Inv0, ExceptionalCover.rootChar_mulSingle] at h1
  have hc : ExceptionalCover.cartanCoord (Pi.single e6Node2 1 : Fin Tag.E6.rank → ℤ) e6Node0 =
      -1 := by
    simp [ExceptionalCover.cartanCoord, Pi.single_apply]
    decide +kernel
  rw [hc, zpow_neg_one, inv_neg_one] at h1
  have h3 : ((-1 : Fˣ) : F) = 1 := by rw [h1]; rfl
  apply h2
  have : ((-1 : Fˣ) : F) = -1 := by simp
  rw [this] at h3
  have h4 : (-1 : F) + 1 = 1 + 1 := by rw [h3]
  rw [neg_add_cancel] at h4
  rw [← one_add_one_eq_two]
  exact h4.symm

theorem e6_odd_witness (h2 : (2 : F) ≠ 0) (ζ : Fˣ) (hζ : orderOf ζ = 3) :
    ∃ U : Subgroup (adjointGroup Tag.E6 F), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      (((minTorus e6Data_valid F).comp (zeta3Pi ζ hζ)).range).map (e6Isogeny F) ≤
        Subgroup.normalizer (U : Set (adjointGroup Tag.E6 F)) := by
  classical
  set g₀ : e6Data_valid.minGroup F := minTorus e6Data_valid F e6Inv0 with hg₀
  have hg₀sq : g₀ ^ 2 = 1 := by rw [hg₀, ← map_pow, e6Inv0_sq, map_one]
  set X : Subgroup (e6Data_valid.minGroup F) := Subgroup.zpowers g₀ with hX
  have hXnorm : ((minTorus e6Data_valid F).comp (zeta3Pi ζ hζ)).range ≤
      Subgroup.normalizer (X : Set (e6Data_valid.minGroup F)) := by
    refine le_normalizer_of_conj_mem fun e he y hy => ?_
    obtain ⟨x, rfl⟩ := he
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have hcomm : Commute ((minTorus e6Data_valid F).comp (zeta3Pi ζ hζ) x) g₀ := by
      show Commute (minTorus e6Data_valid F (zeta3Pi ζ hζ x)) (minTorus e6Data_valid F e6Inv0)
      rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]
    have := (hcomm.zpow_right n).eq
    rw [this, mul_inv_cancel_right]
    exact Subgroup.mem_zpowers_iff.2 ⟨n, rfl⟩
  refine ⟨X.map (e6Isogeny F), ?_, ?_, map_le_normalizer_map _ hXnorm⟩
  · intro hbot
    have hmem : e6Isogeny F g₀ ∈ X.map (e6Isogeny F) :=
      ⟨_, Subgroup.mem_zpowers g₀, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact e6Inv0_isogeny_ne_one h2 hmem
  · have hX2 : IsPGroup 2 X := by
      intro g
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 g.2
      refine ⟨1, Subtype.ext ?_⟩
      show (g : e6Data_valid.minGroup F) ^ 2 = 1
      rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg₀sq, one_zpow]
    exact hX2.map (e6Isogeny F)

theorem e6_exists_torus_witness (h3 : 3 ∣ Nat.card F - 1) :
    ∃ (E : Subgroup (e6Data_valid.minGroup F)) (U : Subgroup (adjointGroup Tag.E6 F)),
      IsElemAbelian 3 E ∧ 3 ^ 5 ≤ Nat.card (E.map (e6Isogeny F)) ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
      E.map (e6Isogeny F) ≤ Subgroup.normalizer (U : Set (adjointGroup Tag.E6 F)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Fˣ, orderOf ζ = 3 := by
    have : 3 ∣ Nat.card Fˣ := by rw [Nat.card_units]; exact h3
    exact exists_prime_orderOf_dvd_card' 3 this
  refine ⟨((minTorus e6Data_valid F).comp (zeta3Pi ζ hζ)).range, ?_⟩
  have hEa : IsElemAbelian 3 ((minTorus e6Data_valid F).comp (zeta3Pi ζ hζ)).range :=
    isElemAbelian_range_of_pow_three _ (fun a => pow_three_multiplicative_pi _ a)
  by_cases h2 : (2 : F) = 0
  · obtain ⟨U, hU, hU2, hN⟩ := e6_even_witness h2 ζ hζ
    exact ⟨U, hEa, three_pow_five_le_card_image ζ hζ, hU, hU2, hN⟩
  · obtain ⟨U, hU, hU2, hN⟩ := e6_odd_witness h2 ζ hζ
    exact ⟨U, hEa, three_pow_five_le_card_image ζ hζ, hU, hU2, hN⟩

end E6

end CFSG.HardMathSupport.Dickson.Sec6.I1431
