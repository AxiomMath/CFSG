module

public import CFSG.LargeExtraspecial.S12Good

public section

namespace CFSG.LargeExtraspecial.S12Tri

open Subgroup

variable {G H : Type*} [Group G] [Group H]

@[expose] def TriGood (G : Type*) [Group G] (t : G) : Prop :=
  ¬ Group.IsSolvable (commutator G ⊓ centralizer {t} : Subgroup G) ∧
    S12NoNormalTwo (commutator G ⊓ centralizer {t})

@[expose] def TriResult (G : Type*) [Group G] (t : G) : Prop :=
  TriGood G t ∨ Nat.card (commutator G) = 60 ∨
    Nonempty (commutator G ≃* alternatingGroup (Fin 6))

theorem S12NoNormalTwo.map_mulEquiv (φ : G ≃* H) {A : Subgroup G} (hA : S12NoNormalTwo A) :
    S12NoNormalTwo (A.map φ.toMonoidHom) := by
  intro P hPA hP hAP
  have hP' : P.comap φ.toMonoidHom ≤ A := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := hPA hx
    rwa [← φ.injective hax]
  have hP2 : IsPGroup 2 (P.comap φ.toMonoidHom) :=
    hP.comap_of_injective φ.toMonoidHom φ.injective
  have hAN : A ≤ normalizer (P.comap φ.toMonoidHom : Set G) := by
    intro a ha
    rw [mem_normalizer_iff]
    intro x
    have h := mem_normalizer_iff.mp (hAP ⟨a, ha, rfl⟩) (φ x)
    simp only [mem_comap, MulEquiv.coe_toMonoidHom, map_mul, map_inv] at h ⊢
    exact h
  have hbot := hA _ hP' hP2 hAN
  rw [eq_bot_iff]
  intro y hy
  have hy' : φ.symm y ∈ P.comap φ.toMonoidHom := by
    simpa only [mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] using hy
  rw [hbot, mem_bot] at hy'
  rw [mem_bot, ← φ.apply_symm_apply y, hy', map_one]

theorem map_commutator_mulEquiv (φ : G ≃* H) :
    (commutator G).map φ.toMonoidHom = commutator H := by
  rw [commutator_def, commutator_def, map_commutator, map_top_of_surjective _ φ.surjective]

@[expose] noncomputable def commutatorEquiv (φ : G ≃* H) : commutator G ≃* commutator H :=
  ((commutator G).equivMapOfInjective φ.toMonoidHom φ.injective).trans
    (MulEquiv.subgroupCongr (map_commutator_mulEquiv φ))

theorem apply_mem_commutator_iff (φ : G ≃* H) {x : G} :
    φ x ∈ commutator H ↔ x ∈ commutator G := by
  rw [← map_commutator_mulEquiv φ]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rwa [← φ.injective hyx]
  · exact fun hx => ⟨x, hx, rfl⟩

theorem map_commutator_inf_centralizer (φ : G ≃* H) (t : G) :
    (commutator G ⊓ centralizer {t}).map φ.toMonoidHom = commutator H ⊓ centralizer {φ t} := by
  have hc : (commutator G).map φ.toMonoidHom = commutator H := by
    rw [commutator_def, commutator_def, map_commutator,
      map_top_of_surjective _ φ.surjective]
  ext y
  simp only [mem_map, mem_inf, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨x, ⟨hxG, hxt⟩, rfl⟩
    refine ⟨hc ▸ ⟨x, hxG, rfl⟩, ?_⟩
    rw [← map_mul, ← map_mul, hxt]
  · rintro ⟨hyH, hyt⟩
    rw [← hc] at hyH
    obtain ⟨x, hxG, rfl⟩ := hyH
    refine ⟨x, ⟨hxG, ?_⟩, rfl⟩
    apply φ.injective
    simpa only [MulEquiv.coe_toMonoidHom, map_mul] using hyt

theorem TriGood.of_mulEquiv (φ : G ≃* H) {t : G} (h : TriGood H (φ t)) : TriGood G t := by
  have hmap := map_commutator_inf_centralizer φ.symm (φ t)
  rw [MulEquiv.symm_apply_apply] at hmap
  refine ⟨fun hsol => h.1 ?_, hmap ▸ S12NoNormalTwo.map_mulEquiv φ.symm h.2⟩
  have e : (commutator G ⊓ centralizer {t} : Subgroup G) ≃*
      (commutator H ⊓ centralizer {φ t} : Subgroup H) :=
    ((commutator G ⊓ centralizer {t}).equivMapOfInjective φ.toMonoidHom φ.injective).trans
      (MulEquiv.subgroupCongr (map_commutator_inf_centralizer φ t))
  exact Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective

theorem triGood_of_normal {t : G} {N : Subgroup G} (hN : N ≤ commutator G ⊓ centralizer {t})
    (hNn : commutator G ⊓ centralizer {t} ≤ normalizer (N : Set G))
    (hC : ∀ c ∈ commutator G ⊓ centralizer {t}, (∀ n ∈ N, c * n = n * c) → c = 1)
    (hsol : ¬ Group.IsSolvable N) (h2 : ∀ P : Subgroup N, P.Normal → IsPGroup 2 P → P = ⊥) :
    TriGood G t := by
  refine ⟨fun hs => hsol (Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion hN) (Subgroup.inclusion_injective hN)), ?_⟩
  intro P hPC hP2 hCP
  have hPN : P.subgroupOf N = ⊥ := by
    refine h2 _ ⟨fun x hx n => ?_⟩ (hP2.comap_of_injective N.subtype N.subtype_injective)
    rw [mem_subgroupOf] at hx ⊢
    simpa only [coe_mul, coe_inv] using
      (mem_normalizer_iff.mp (hCP (hN n.2)) x).mp hx
  rw [eq_bot_iff]
  intro p hp
  rw [mem_bot]
  refine hC p (hPC hp) fun n hn => ?_
  have h1 : p * n * p⁻¹ * n⁻¹ ∈ P := by
    have : n * p⁻¹ * n⁻¹ ∈ P :=
      (mem_normalizer_iff.mp (hCP (hN hn)) p⁻¹).mp (P.inv_mem hp)
    simpa only [mul_assoc] using P.mul_mem hp this
  have h2' : p * n * p⁻¹ * n⁻¹ ∈ N :=
    N.mul_mem ((mem_normalizer_iff.mp (hNn (hPC hp)) n).mp hn) (N.inv_mem hn)
  have h3 : (⟨_, h2'⟩ : N) ∈ P.subgroupOf N := h1
  rw [hPN, mem_bot] at h3
  have h4 : p * n * p⁻¹ * n⁻¹ = 1 := congrArg Subtype.val h3
  calc p * n = p * n * p⁻¹ * n⁻¹ * (n * p) := by group
    _ = n * p := by rw [h4, one_mul]

theorem triGood_of_isSimpleGroup [Finite G] {t : G}
    (hs : IsSimpleGroup (commutator G ⊓ centralizer {t} : Subgroup G))
    (hna : ∃ a b : (commutator G ⊓ centralizer {t} : Subgroup G), a * b ≠ b * a) :
    TriGood G t := by
  set C₀ := (commutator G ⊓ centralizer {t} : Subgroup G)
  have hnsol : ¬ Group.IsSolvable C₀ := fun h => by
    obtain ⟨a, b, hab⟩ := hna
    exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr h a b)
  refine triGood_of_normal (N := C₀) le_rfl (fun c hc => ?_) (fun c hc hcN => ?_) hnsol ?_
  · rw [mem_normalizer_iff]
    intro x
    exact ⟨fun hx => C₀.mul_mem (C₀.mul_mem hc hx) (C₀.inv_mem hc), fun hx => by
      simpa [mul_assoc] using C₀.mul_mem (C₀.mul_mem (C₀.inv_mem hc) hx) hc⟩
  · have hz : (⟨c, hc⟩ : C₀) ∈ center C₀ := by
      rw [mem_center_iff]
      intro g
      exact Subtype.ext (hcN g g.2).symm
    have hZ : center C₀ = ⊥ := by
      rcases hs.eq_bot_or_eq_top_of_normal (center C₀) with h | h
      · exact h
      · exfalso
        obtain ⟨a, b, hab⟩ := hna
        exact hab (mem_center_iff.mp (h ▸ mem_top b) a)
    rw [hZ, mem_bot] at hz
    exact congrArg Subtype.val hz
  · intro P hPn hP2
    rcases hs.eq_bot_or_eq_top_of_normal P with h | h
    · exact h
    · exfalso
      apply hnsol
      have hC2 : IsPGroup 2 C₀ := fun g => by
        obtain ⟨k, hk⟩ := hP2 ⟨g, h ▸ mem_top g⟩
        exact ⟨k, congrArg Subtype.val hk⟩
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have := hC2.isNilpotent
      infer_instance

end CFSG.LargeExtraspecial.S12Tri
