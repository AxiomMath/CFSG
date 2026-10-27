module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.SylowCover

public section

namespace CFSG.EvenSporadicStandard.HNRecog.TwoHSData

open Subgroup

private lemma factorization_7920_eleven : (7920 : ℕ).factorization 11 = 1 := by
  have h : (7920 : ℕ) = 11 * 720 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_self Nat.prime_eleven,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

@[expose] def M11Order (n : ℕ) : Prop :=
  n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 8 ∨ n = 11

structure IsM11Like (X : Type*) [Group X] : Prop where
  card_eq : Nat.card X = 7920
  orderOf_mem : ∀ g : X, M11Order (orderOf g)
  exists_gen : ∃ y v : X, orderOf y = 11 ∧ orderOf v = 11 ∧ closure ({y, v} : Set X) = ⊤
  exists_involution : ∀ y : X, orderOf y = 11 →
    ∃ i : X, orderOf i = 2 ∧ closure ({y, i} : Set X) = ⊤
  nonabelian : ∃ x y : X, x * y ≠ y * x

theorem IsM11Like.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (h : IsM11Like X) :
    IsM11Like Y := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← h.card_eq]
    exact (Nat.card_congr e.toEquiv).symm
  · intro g
    have := h.orderOf_mem (e.symm g)
    rwa [MulEquiv.orderOf_eq e.symm g] at this
  · obtain ⟨y, v, hy, hv, hyv⟩ := h.exists_gen
    refine ⟨e y, e v, ?_, ?_, ?_⟩
    · rw [MulEquiv.orderOf_eq e y, hy]
    · rw [MulEquiv.orderOf_eq e v, hv]
    · have h1 : (closure ({y, v} : Set X)).map (e : X →* Y) = ⊤ := by
        rw [hyv, Subgroup.map_top_of_surjective _ e.surjective]
      rw [MonoidHom.map_closure, Set.image_pair] at h1
      simpa using h1
  · intro y' hy'
    have hy'' : orderOf (e.symm y') = 11 := by
      rwa [MulEquiv.orderOf_eq e.symm y']
    obtain ⟨i, hi2, hic⟩ := h.exists_involution (e.symm y') hy''
    refine ⟨e i, ?_, ?_⟩
    · rw [MulEquiv.orderOf_eq e i, hi2]
    · have h1 : (closure ({e.symm y', i} : Set X)).map (e : X →* Y) = ⊤ := by
        rw [hic, Subgroup.map_top_of_surjective _ e.surjective]
      rw [MonoidHom.map_closure, Set.image_pair] at h1
      simpa using h1
  · obtain ⟨x, y, hxy⟩ := h.nonabelian
    refine ⟨e x, e y, fun hcon => hxy ?_⟩
    apply e.injective
    rw [map_mul, map_mul]
    exact hcon

theorem IsM11Like.map_conj {G : Type*} [Group G] {M : Subgroup G} (h : IsM11Like ↥M) (g : G) :
    IsM11Like ↥(M.map (MulAut.conj g).toMonoidHom) :=
  h.of_mulEquiv
    (Subgroup.equivMapOfInjective M (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)

theorem isM11Like_of_data {X : Type*} [Group X] {y v i : X} (hcard : Nat.card X = 7920)
    (hord : ∀ g : X, M11Order (orderOf g)) (hy : orderOf y = 11) (hv : orderOf v = 11)
    (hyv : closure ({y, v} : Set X) = ⊤) (hi : orderOf i = 2)
    (hyi : closure ({y, i} : Set X) = ⊤) (hnc : y * v ≠ v * y) : IsM11Like X := by
  haveI : Finite X := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : Fact (Nat.Prime 11) := ⟨Nat.prime_eleven⟩
  refine ⟨hcard, hord, ⟨y, v, hy, hv, hyv⟩, ?_, ⟨y, v, hnc⟩⟩
  intro y' hy'
  have hS : Nat.card (zpowers y) = 11 ^ (Nat.card (⊤ : Subgroup X)).factorization 11 := by
    rw [Nat.card_zpowers, hy, Subgroup.card_top, hcard, factorization_7920_eleven, pow_one]
  obtain ⟨x, -, hxmem⟩ :=
    exists_conj_mem_of_orderOf_eq_prime (M := X) (p := 11) (R := ⊤) (S := zpowers y)
      le_top hS trivial hy'
  have hconjord : orderOf (x⁻¹ * y' * x) = 11 := by
    rw [show x⁻¹ * y' * x = (MulAut.conj x⁻¹) y' by simp [MulAut.conj_apply]]
    rw [MulEquiv.orderOf_eq (MulAut.conj x⁻¹) y', hy']
  have hy_zp : y ∈ zpowers (x⁻¹ * y' * x) := by
    haveI : Finite ↥(zpowers y) :=
      Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hy]; norm_num)
    have hle : zpowers (x⁻¹ * y' * x) ≤ zpowers y := Subgroup.zpowers_le.mpr hxmem
    have hcardeq : zpowers (x⁻¹ * y' * x) = zpowers y := by
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, hconjord, hy]
    rw [hcardeq]
    exact Subgroup.mem_zpowers y
  refine ⟨x * i * x⁻¹, ?_, ?_⟩
  · rw [show x * i * x⁻¹ = (MulAut.conj x) i by simp [MulAut.conj_apply]]
    rw [MulEquiv.orderOf_eq (MulAut.conj x) i, hi]
  · have hconj_closure : closure ({x * y * x⁻¹, x * i * x⁻¹} : Set X) = ⊤ := by
      have h1 : (closure ({y, i} : Set X)).map (MulAut.conj x).toMonoidHom = ⊤ := by
        rw [hyi, Subgroup.map_top_of_surjective (MulAut.conj x).toMonoidHom
          (MulAut.conj x).surjective]
      rw [MonoidHom.map_closure, Set.image_pair] at h1
      simpa [MulAut.conj_apply] using h1
    have hgen_le : closure ({x * y * x⁻¹, x * i * x⁻¹} : Set X) ≤
        closure ({y', x * i * x⁻¹} : Set X) := by
      apply (Subgroup.closure_le _).mpr
      intro p hp
      rcases Set.mem_insert_iff.mp hp with rfl | hp
      · have hmem : x * y * x⁻¹ ∈ zpowers y' := by
          obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy_zp
          rw [← hk]
          have hkey : x * (x⁻¹ * y' * x) ^ k * x⁻¹ = y' ^ k := by
            rw [← conj_zpow (i := k) (a := x) (b := x⁻¹ * y' * x)]
            congr 1
            group
          rw [hkey]
          exact Subgroup.zpow_mem_zpowers y' k
        exact (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))) hmem
      · rw [Set.mem_singleton_iff.mp hp]
        exact Subgroup.subset_closure (by simp)
    exact top_le_iff.mp (hconj_closure ▸ hgen_le)

theorem IsM11Like.le_of_order_eleven {G : Type*} [Group G] {M E : Subgroup G} (h : IsM11Like ↥M)
    (hE : ∀ t : G, orderOf t = 11 → t ∈ E) : M ≤ E := by
  obtain ⟨y, v, hy, hv, hyv⟩ := h.exists_gen
  set E' : Subgroup ↥M := E.comap M.subtype with hE'
  have hyE : y ∈ E' := by
    rw [hE', Subgroup.mem_comap]
    exact hE (y : G) (by rw [Subgroup.orderOf_coe, hy])
  have hvE : v ∈ E' := by
    rw [hE', Subgroup.mem_comap]
    exact hE (v : G) (by rw [Subgroup.orderOf_coe, hv])
  have htop : (⊤ : Subgroup ↥M) ≤ E' := by
    rw [← hyv]
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · rw [hx]; exact hyE
    · rw [hx]; exact hvE
  intro m hm
  have hmE' : (⟨m, hm⟩ : ↥M) ∈ E' := htop (Subgroup.mem_top _)
  rw [hE', Subgroup.mem_comap] at hmE'
  exact hmE'

end CFSG.EvenSporadicStandard.HNRecog.TwoHSData
