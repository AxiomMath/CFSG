module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergCCElementaryCoset

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup

variable {G : Type*} [Group G]

theorem mul_mul_self_eq_one_iff_mem_centralizer {E : Subgroup G} [IsElementaryAbelian 2 E]
    {t : G} (ht : t * t = 1) {e : G} (he : e ∈ E) :
    t * e * (t * e) = 1 ↔ e ∈ centralizer {t} := by
  have he2 : e * e = 1 := by
    have h := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E) e he
    rwa [pow_two] at h
  rw [mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h1 : t * e * t = e := by
      calc t * e * t = t * e * (t * e) * e := by
            rw [show t * e * (t * e) * e = t * e * t * (e * e) by group, he2, mul_one]
        _ = e := by rw [h, one_mul]
    calc e * t = t * e * t * t := by rw [h1]
      _ = t * e := by rw [mul_assoc (t * e) t t, ht, mul_one]
  · intro h
    calc t * e * (t * e) = t * (e * t) * e := by group
      _ = t * (t * e) * e := by rw [h]
      _ = (t * t) * (e * e) := by group
      _ = 1 := by rw [ht, he2, one_mul]

theorem elementary_quotient_involution_coset_conjugacy [Finite G] {V E : Subgroup G}
    (hEV : E ≤ V) [(E.subgroupOf V).Normal] [IsElementaryAbelian 2 E]
    [IsElementaryAbelian 2 (V ⧸ E.subgroupOf V)] {t : G} (ht : orderOf t = 2)
    (htV : t ∈ normalizer (V : Set G)) (htE : t ∈ normalizer (E : Set G)) (htV' : t ∉ V)
    (hC : {u | sectionRightConj htV htE u = u} =
      (closure (Set.range fun u => u⁻¹ * sectionRightConj htV htE u) :
        Set (V ⧸ E.subgroupOf V))) :
    {x | (∃ v ∈ V, x = t * v) ∧ orderOf x = 2} =
        {x | ∃ v ∈ V, ∃ d ∈ E ⊓ centralizer {t}, x = v⁻¹ * (t * d) * v} ∧
      Nat.card {x | (∃ v ∈ V, x = t * v) ∧ orderOf x = 2} =
        Nat.card {u | sectionRightConj htV htE u = u} *
          Nat.card (E ⊓ centralizer {t} : Subgroup G) ∧
      ∀ C : ConjClasses G, (∀ x ∈ C.carrier, orderOf x = 2) →
        C.carrier ∩ {x | ∃ v ∈ V, x = t * v} =
          {x | ∃ v ∈ V, ∃ y ∈ C.carrier ∩ {y | ∃ d ∈ E ⊓ centralizer {t}, y = t * d},
            x = v⁻¹ * y * v} := by
  classical
  set α := sectionRightConj htV htE with hα
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have hfix : {u | α u = u} = Set.range fun u : V ⧸ E.subgroupOf V => u⁻¹ * α u := by
    rw [hC, coe_closure_range_inv_mul_apply]
  have hsq_conj : ∀ {x : G} (y : G), x * x = 1 → y * x * y⁻¹ * (y * x * y⁻¹) = 1 := by
    intro x y hx
    calc y * x * y⁻¹ * (y * x * y⁻¹) = y * (x * x) * y⁻¹ := by group
      _ = 1 := by rw [hx]; group
  have hconj : ∀ v ∈ V, t * v * (t * v) = 1 →
      ∃ y ∈ V, ∃ d ∈ E ⊓ centralizer {t}, y * (t * v) * y⁻¹ = t * d := by
    intro v hv hsq
    obtain ⟨y, hy, e, he, hye⟩ :=
      exists_conj_mem_coset_of_mul_self_eq_one htV htE ht2 hfix hv hsq
    have hsqe : t * e * (t * e) = 1 := by
      rw [← hye]
      exact hsq_conj y hsq
    exact ⟨y, hy, e, mem_inf.mpr ⟨he, (mul_mul_self_eq_one_iff_mem_centralizer ht2 he).mp hsqe⟩,
      hye⟩
  have htd : ∀ d ∈ E ⊓ centralizer {t}, orderOf (t * d) = 2 := by
    intro d hd
    obtain ⟨hdE, hdC⟩ := mem_inf.mp hd
    apply orderOf_eq_prime
    · rw [pow_two]
      exact (mul_mul_self_eq_one_iff_mem_centralizer ht2 hdE).mpr hdC
    · intro h1
      apply htV'
      rw [eq_inv_of_mul_eq_one_left h1]
      exact V.inv_mem (hEV hdE)
  have hmemV : ∀ v ∈ V, ∀ d ∈ E, t⁻¹ * (v⁻¹ * (t * d) * v) ∈ V := by
    intro v hv d hd
    have h : t⁻¹ * (v⁻¹ * (t * d) * v) = t⁻¹ * v⁻¹ * t * d * v := by group
    rw [h]
    exact V.mul_mem (V.mul_mem (inv_mul_mul_mem_of_mem_normalizer htV (V.inv_mem hv)) (hEV hd)) hv
  have hconjmem : ∀ v ∈ V, ∀ d ∈ E, ∃ w ∈ V, v⁻¹ * (t * d) * v = t * w := fun v hv d hd =>
    ⟨_, hmemV v hv d hd, by group⟩
  have horder_conj : ∀ v x : G, orderOf (v⁻¹ * x * v) = orderOf x := by
    intro v x
    have h := MulEquiv.orderOf_eq (MulAut.conj v⁻¹) x
    rwa [MulAut.conj_apply, inv_inv] at h
  have hInv : {x | (∃ v ∈ V, x = t * v) ∧ orderOf x = 2} =
      {x | ∃ v ∈ V, ∃ d ∈ E ⊓ centralizer {t}, x = v⁻¹ * (t * d) * v} := by
    ext x
    constructor
    · rintro ⟨⟨v, hv, rfl⟩, hx⟩
      have hsq : t * v * (t * v) = 1 := by rw [← pow_two, ← hx, pow_orderOf_eq_one]
      obtain ⟨y, hy, d, hd, hyd⟩ := hconj v hv hsq
      exact ⟨y, hy, d, hd, by rw [← hyd]; group⟩
    · rintro ⟨v, hv, d, hd, rfl⟩
      exact ⟨hconjmem v hv d (mem_inf.mp hd).1, by rw [horder_conj, htd d hd]⟩
  refine ⟨hInv, ?_, ?_⟩
  ·
    set F : Set (V ⧸ E.subgroupOf V) := {u | α u = u} with hF
    set D : Subgroup G := E ⊓ centralizer {t} with hD
    set I : Set G := {x | (∃ v ∈ V, x = t * v) ∧ orderOf x = 2} with hI
    have hsel : ∀ u : F, ∃ y : V,
        (QuotientGroup.mk y : V ⧸ E.subgroupOf V)⁻¹ * α (QuotientGroup.mk y) = u := by
      intro u
      have hu : (u : V ⧸ E.subgroupOf V) ∈
          Set.range fun u : V ⧸ E.subgroupOf V => u⁻¹ * α u := by
        rw [← hfix]
        exact u.2
      obtain ⟨p, hp⟩ := hu
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective p
      exact ⟨y, hp⟩
    choose sel hsel using hsel
    have hmemI : ∀ (u : F) (d : D), ((sel u : G))⁻¹ * (t * d) * sel u ∈ I := by
      intro u d
      rw [hInv]
      exact ⟨sel u, (sel u).2, d, d.2, rfl⟩
    let Φ : F × D → I := fun p => ⟨((sel p.1 : G))⁻¹ * (t * p.2) * sel p.1, hmemI p.1 p.2⟩
    have hproj : ∀ (u : F) (d : D),
        (QuotientGroup.mk (⟨t⁻¹ * (((sel u : G))⁻¹ * (t * d) * sel u),
          hmemV _ (sel u).2 _ (mem_inf.mp d.2).1⟩ : V) : V ⧸ E.subgroupOf V) = u := by
      intro u d
      rw [mk_inv_mul_conj_coset_mul hEV htV htE (sel u) (mem_inf.mp d.2).1, ← hsel u]
      set w : V ⧸ E.subgroupOf V := QuotientGroup.mk (sel u)
      calc (α w)⁻¹ * w = (w⁻¹ * α w)⁻¹ := by rw [mul_inv_rev, inv_inv]
        _ = w⁻¹ * α w := inv_eq_of_mul_eq_one_right (mul_self_eq_one_of_isElementaryAbelian_two _)
    have hinj : Function.Injective Φ := by
      rintro ⟨u₁, d₁⟩ ⟨u₂, d₂⟩ h
      have h' : ((sel u₁ : G))⁻¹ * (t * d₁) * sel u₁ = ((sel u₂ : G))⁻¹ * (t * d₂) * sel u₂ :=
        congrArg Subtype.val h
      have hu : u₁ = u₂ := by
        apply Subtype.ext
        rw [← hproj u₁ d₁, ← hproj u₂ d₂]
        exact congrArg QuotientGroup.mk (Subtype.ext (congrArg (t⁻¹ * ·) h'))
      subst hu
      have hd : (d₁ : G) = d₂ := by
        have h2 := congrArg (fun z => (sel u₁ : G) * z * ((sel u₁ : G))⁻¹) h'
        simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] at h2
        exact mul_left_cancel h2
      exact Prod.ext rfl (Subtype.ext hd)
    have hsurj : Function.Surjective Φ := by
      rintro ⟨x, hx⟩
      obtain ⟨⟨v, hv, rfl⟩, hxo⟩ := hx
      have hsq : t * v * (t * v) = 1 := by rw [← pow_two, ← hxo, pow_orderOf_eq_one]
      let u : F := ⟨QuotientGroup.mk ⟨v, hv⟩,
        sectionRightConj_mk_eq_of_mul_self_eq_one htV htE ht2 hv hsq⟩
      obtain ⟨e, he, hye⟩ := conj_mem_coset_of_inv_mul_eq htV htE hv (sel u) (hsel u)
      have hsqe : t * e * (t * e) = 1 := by
        rw [← hye]
        exact hsq_conj _ hsq
      have hdD : e ∈ D :=
        mem_inf.mpr ⟨he, (mul_mul_self_eq_one_iff_mem_centralizer ht2 he).mp hsqe⟩
      refine ⟨(u, ⟨e, hdD⟩), Subtype.ext ?_⟩
      change ((sel u : G))⁻¹ * (t * e) * sel u = t * v
      rw [← hye]
      group
    rw [← Nat.card_eq_of_bijective Φ ⟨hinj, hsurj⟩, Nat.card_prod]
  ·
    have hCconj : ∀ C : ConjClasses G, ∀ x ∈ C.carrier, ∀ c : G, c⁻¹ * x * c ∈ C.carrier := by
      intro C x hx c
      rw [ConjClasses.mem_carrier_iff_mk_eq] at hx ⊢
      rw [← hx, ConjClasses.mk_eq_mk_iff_isConj]
      exact (isConj_iff.mpr ⟨c⁻¹, by rw [inv_inv]⟩).symm
    intro C hC2
    ext x
    constructor
    · rintro ⟨hxC, v, hv, rfl⟩
      have hsq : t * v * (t * v) = 1 := by rw [← pow_two, ← hC2 _ hxC, pow_orderOf_eq_one]
      obtain ⟨y, hy, d, hd, hyd⟩ := hconj v hv hsq
      have hyC : t * d ∈ C.carrier := by
        rw [← hyd]
        have h := hCconj C _ hxC y⁻¹
        rwa [inv_inv] at h
      exact ⟨y, hy, t * d, ⟨hyC, d, hd, rfl⟩, by rw [← hyd]; group⟩
    · rintro ⟨v, hv, y, ⟨hyC, d, hd, rfl⟩, rfl⟩
      exact ⟨hCconj C _ hyC v, hconjmem v hv d (mem_inf.mp hd).1⟩

end CFSG.LocalAnalysis.ComponentInitial
