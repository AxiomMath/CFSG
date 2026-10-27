module

public import CFSG.GH74.KGroups.Generic4

public section

namespace CFSG.GH74.KGroups

theorem preimage_elementary {K J : Type*} [Group K] [Group J] (π : K →* J)
    (hπ : Function.Surjective π) (Z : Subgroup K) (hker : π.ker = Z)
    (hZc : ∀ z ∈ Z, ∀ g : K, g * z = z * g) (hZ2 : ∀ z ∈ Z, z ^ 2 = 1) (E : Subgroup J)
    (hE2 : ∀ x ∈ E, x ^ 2 = 1)
    (hconj : ∀ x ∈ E, x ≠ 1 → ∀ y ∈ E, y ≠ 1 → ∃ g : J, g * x * g⁻¹ = y)
    (e1 e2 e3 : J) (h1 : e1 ∈ E) (h2 : e2 ∈ E) (h3 : e3 ∈ E)
    (i1 : e1 ≠ 1) (i2 : e2 ≠ 1) (i3 : e3 ≠ 1) (i12 : e1 * e2 ≠ 1) (i13 : e1 * e3 ≠ 1)
    (i23 : e2 * e3 ≠ 1) (i123 : e1 * (e2 * e3) ≠ 1) :
    ∀ a ∈ E.comap π, a ^ 2 = 1 ∧ ∀ b ∈ E.comap π, a * b = b * a := by
  have hmemZ : ∀ x : K, x ∈ Z ↔ π x = 1 := fun x => by rw [← MonoidHom.mem_ker, hker]
  have hmem : ∀ x : K, x ∈ E.comap π ↔ π x ∈ E := fun x => Iff.rfl
  have hsq : ∀ a ∈ E.comap π, a ^ 2 ∈ Z := by
    intro a ha
    rw [hmemZ, map_pow]
    exact hE2 _ ((hmem a).1 ha)
  have hconjK : ∀ x ∈ E.comap π, x ∉ Z → ∀ y ∈ E.comap π, y ∉ Z →
      ∃ g : K, ∃ z ∈ Z, g * x * g⁻¹ = y * z := by
    intro x hx hxZ y hy hyZ
    obtain ⟨g, hg⟩ := hconj (π x) ((hmem x).1 hx) (fun h => hxZ ((hmemZ x).2 h)) (π y)
      ((hmem y).1 hy) (fun h => hyZ ((hmemZ y).2 h))
    obtain ⟨g', rfl⟩ := hπ g
    refine ⟨g', y⁻¹ * (g' * x * g'⁻¹), ?_, by group⟩
    rw [hmemZ, map_mul, map_inv, map_mul, map_mul, map_inv, hg, inv_mul_cancel]
  obtain ⟨a, rfl⟩ := hπ e1
  obtain ⟨b, rfl⟩ := hπ e2
  obtain ⟨d, rfl⟩ := hπ e3
  exact elementary_of_conj (E.comap π) Z hZc hZ2 hsq hconjK a b d h1 h2 h3
    (fun h => i1 ((hmemZ a).1 h)) (fun h => i2 ((hmemZ b).1 h)) (fun h => i3 ((hmemZ d).1 h))
    (fun h => i12 (by rw [← map_mul]; exact (hmemZ _).1 h))
    (fun h => i13 (by rw [← map_mul]; exact (hmemZ _).1 h))
    (fun h => i23 (by rw [← map_mul]; exact (hmemZ _).1 h))
    (fun h => i123 (by rw [← map_mul, ← map_mul]; exact (hmemZ _).1 h))

theorem preimage_elementary_model {K J G : Type*} [Group K] [Group J] [Group G] (π : K →* J)
    (hπ : Function.Surjective π) (Z : Subgroup K) (hker : π.ker = Z)
    (hZc : ∀ z ∈ Z, ∀ g : K, g * z = z * g) (hZ2 : ∀ z ∈ Z, z ^ 2 = 1)
    (P : Subgroup G) (e : J ≃* P) (E : Subgroup G) (hEP : E ≤ P)
    (hE2 : ∀ x ∈ E, x ^ 2 = 1) (e0 : G)
    (hconj : ∀ x ∈ E, x ≠ 1 → ∃ g ∈ P, g * e0 * g⁻¹ = x)
    (e1 e2 e3 : G) (h1 : e1 ∈ E) (h2 : e2 ∈ E) (h3 : e3 ∈ E)
    (i1 : e1 ≠ 1) (i2 : e2 ≠ 1) (i3 : e3 ≠ 1) (i12 : e1 * e2 ≠ 1) (i13 : e1 * e3 ≠ 1)
    (i23 : e2 * e3 ≠ 1) (i123 : e1 * (e2 * e3) ≠ 1) :
    ∀ a ∈ ((E.subgroupOf P).comap e.toMonoidHom).comap π, a ^ 2 = 1 ∧
      ∀ b ∈ ((E.subgroupOf P).comap e.toMonoidHom).comap π, a * b = b * a := by
  set E' : Subgroup J := (E.subgroupOf P).comap e.toMonoidHom with hE'
  have hmem : ∀ x : J, x ∈ E' ↔ ((e x : P) : G) ∈ E := fun x => Iff.rfl
  have lift : ∀ g : G, g ∈ E → ∃ x : J, x ∈ E' ∧ ((e x : P) : G) = g := fun g hg =>
    ⟨e.symm ⟨g, hEP hg⟩, (hmem _).2 (by simpa using hg), by simp⟩
  have hE2' : ∀ x ∈ E', x ^ 2 = 1 := by
    intro x hx
    apply e.injective
    apply Subtype.ext
    have := hE2 _ ((hmem x).1 hx)
    simpa using this
  have hne : ∀ x : J, ((e x : P) : G) ≠ 1 → x ≠ 1 := fun x hx hx1 => hx (by simp [hx1])
  have hconj' : ∀ x ∈ E', x ≠ 1 → ∀ y ∈ E', y ≠ 1 → ∃ g : J, g * x * g⁻¹ = y := by
    intro x hx hx1 y hy hy1
    have hx1' : ((e x : P) : G) ≠ 1 := fun h => hx1 (e.injective (Subtype.ext (by simpa using h)))
    have hy1' : ((e y : P) : G) ≠ 1 := fun h => hy1 (e.injective (Subtype.ext (by simpa using h)))
    obtain ⟨g1, hg1P, hg1⟩ := hconj _ ((hmem x).1 hx) hx1'
    obtain ⟨g2, hg2P, hg2⟩ := hconj _ ((hmem y).1 hy) hy1'
    refine ⟨e.symm ⟨g2 * g1⁻¹, P.mul_mem hg2P (P.inv_mem hg1P)⟩, ?_⟩
    apply e.injective
    apply Subtype.ext
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hg1, ← hg2]
    group
  obtain ⟨a, ha, ha'⟩ := lift e1 h1
  obtain ⟨b, hb, hb'⟩ := lift e2 h2
  obtain ⟨d, hd, hd'⟩ := lift e3 h3
  have key : ∀ x y : J, ((e x : P) : G) * ((e y : P) : G) = ((e (x * y) : P) : G) := by
    intro x y; simp
  exact preimage_elementary π hπ Z hker hZc hZ2 E' hE2' hconj' a b d ha hb hd
    (hne a (by rw [ha']; exact i1)) (hne b (by rw [hb']; exact i2)) (hne d (by rw [hd']; exact i3))
    (hne _ (by rw [← key, ha', hb']; exact i12)) (hne _ (by rw [← key, ha', hd']; exact i13))
    (hne _ (by rw [← key, hb', hd']; exact i23))
    (hne _ (by rw [← key, ha', ← key, hb', hd']; exact i123))

theorem exists_independent_triple {J : Type*} [Group J] (E : Subgroup J)
    (hE2 : ∀ x ∈ E, x ^ 2 = 1) (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hcard : 4 < Nat.card E) :
    ∃ e1 e2 e3 : J, e1 ∈ E ∧ e2 ∈ E ∧ e3 ∈ E ∧ e1 ≠ 1 ∧ e2 ≠ 1 ∧ e3 ≠ 1 ∧ e1 * e2 ≠ 1 ∧
      e1 * e3 ≠ 1 ∧ e2 * e3 ≠ 1 ∧ e1 * (e2 * e3) ≠ 1 := by
  have hinv : ∀ x ∈ E, x⁻¹ = x := fun x hx =>
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hE2 x hx)
  obtain ⟨e1, h1, h1L⟩ := exists_mem_notMem_list E [1] (by simp; omega)
  obtain ⟨e2, h2, h2L⟩ := exists_mem_notMem_list E [1, e1] (by simp; omega)
  obtain ⟨e3, h3, h3L⟩ := exists_mem_notMem_list E [1, e1, e2, e1 * e2] (by simp; omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h1L h2L h3L
  have n1 : e1 ≠ 1 := h1L
  have n2 : e2 ≠ 1 := h2L.1
  have n3 : e3 ≠ 1 := h3L.1
  refine ⟨e1, e2, e3, h1, h2, h3, n1, n2, n3, ?_, ?_, ?_, ?_⟩
  · intro h
    apply h2L.2
    have := eq_inv_of_mul_eq_one_right h
    rw [this, hinv e1 h1]
  · intro h
    apply h3L.2.1
    have := eq_inv_of_mul_eq_one_right h
    rw [this, hinv e1 h1]
  · intro h
    apply h3L.2.2.1
    have := eq_inv_of_mul_eq_one_right h
    rw [this, hinv e2 h2]
  · intro h
    apply h3L.2.2.2
    have h' : e2 * e3 = e1⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [hinv e1 h1] at h'
    have : e3 = e2⁻¹ * e1 := by rw [← h']; group
    rw [this, hinv e2 h2, hEc e2 h2 e1 h1]

open scoped commutatorElement in
theorem center_quotient_eq_bot {K : Type} [Group K] (hperf : commutator K = ⊤)
    (hsimple : IsSimpleGroup (K ⧸ Subgroup.center K)) :
    Subgroup.center (K ⧸ Subgroup.center K) = ⊥ := by
  rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center (K ⧸ Subgroup.center K)) with h | h
  · exact h
  · exfalso
    have hcomm : ∀ a b : K ⧸ Subgroup.center K, a * b = b * a := fun a b =>
      (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top a) b).symm
    have hle : commutator K ≤ Subgroup.center K := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      have : (QuotientGroup.mk ⁅a, b⁆ : K ⧸ Subgroup.center K) = 1 := by
        rw [commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
          QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv,
          hcomm (QuotientGroup.mk a) (QuotientGroup.mk b)]
        group
      exact (QuotientGroup.eq_one_iff _).1 this
    rw [hperf] at hle
    have hKtop : Subgroup.center K = ⊤ := top_le_iff.1 hle
    have : Subsingleton (K ⧸ Subgroup.center K) := by
      rw [hKtop]
      exact QuotientGroup.subsingleton_quotient_top
    obtain ⟨x, y, hxy⟩ := (hsimple.toNontrivial).exists_pair_ne
    exact hxy (Subsingleton.elim x y)

end CFSG.GH74.KGroups
