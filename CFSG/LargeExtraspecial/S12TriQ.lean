module

public import CFSG.Fischer.Classification.Basic.Trichotomy

public section

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification
open scoped commutatorElement

@[expose] def fischerQ {X : Type*} [Group X] (E : Set X) : Subgroup X :=
  closure {x | ∃ d ∈ E, ∃ e ∈ E, d ≠ e ∧ d * e = e * d ∧ d * e = x}

section General

variable {X : Type*} [Group X] {E : Set X}

theorem mul_mem_fischerQ {d e : X} (hd : d ∈ E) (he : e ∈ E) (hne : d ≠ e)
    (hc : d * e = e * d) : d * e ∈ fischerQ E :=
  subset_closure ⟨d, hd, e, he, hne, hc, rfl⟩

theorem fischerQ_le_closure : fischerQ E ≤ closure E := by
  rw [fischerQ, closure_le]
  rintro _ ⟨d, hd, e, he, -, -, rfl⟩
  exact mul_mem (subset_closure hd) (subset_closure he)

theorem conj_mem_fischerQ {m : X} (hm : ∀ e ∈ E, m * e * m⁻¹ ∈ E) {y : X}
    (hy : y ∈ fischerQ E) : m * y * m⁻¹ ∈ fischerQ E := by
  have hle : (fischerQ E).map (MulAut.conj m).toMonoidHom ≤ fischerQ E := by
    rw [fischerQ, MonoidHom.map_closure, closure_le]
    rintro _ ⟨_, ⟨d, hd, e, he, hne, hc, rfl⟩, rfl⟩
    refine subset_closure ⟨m * d * m⁻¹, hm d hd, m * e * m⁻¹, hm e he, fun h => hne ?_, ?_, ?_⟩
    · simpa using h
    · calc m * d * m⁻¹ * (m * e * m⁻¹) = m * (d * e) * m⁻¹ := by group
        _ = m * (e * d) * m⁻¹ := by rw [hc]
        _ = m * e * m⁻¹ * (m * d * m⁻¹) := by group
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  exact hle ⟨y, hy, rfl⟩

theorem map_subtype_fischerQ {Y : Type*} [Group Y] {H : Subgroup Y} {E : Set Y} (hE : E ⊆ H) :
    (fischerQ (Subtype.val ⁻¹' E : Set H)).map H.subtype = fischerQ E := by
  rw [fischerQ, MonoidHom.map_closure, fischerQ]
  congr 1
  ext y
  constructor
  · rintro ⟨_, ⟨d, hd, e, he, hne, hc, rfl⟩, rfl⟩
    exact ⟨d, hd, e, he, fun h => hne (Subtype.ext h), congrArg Subtype.val hc, rfl⟩
  · rintro ⟨d, hd, e, he, hne, hc, rfl⟩
    refine ⟨⟨d, hE hd⟩ * ⟨e, hE he⟩, ⟨⟨d, hE hd⟩, hd, ⟨e, hE he⟩, he,
      fun h => hne (congrArg Subtype.val h), Subtype.ext hc, rfl⟩, rfl⟩

theorem isSolvable_of_pow_six {G : Type*} [Group G] [Finite G] (h : ∀ g : G, g ^ 6 = 1) :
    Group.IsSolvable G := by
  classical
  let := Fintype.ofFinite G
  have hsupp : (Nat.card G).factorization.support ⊆ {2, 3} := by
    intro p hp
    rw [Nat.support_factorization] at hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hdvd := Nat.dvd_of_mem_primeFactors hp
    have := Fact.mk hpp
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have h6 : p ∣ 6 := hg ▸ orderOf_dvd_of_pow_eq_one (h g)
    have hp6 : p ≤ 6 := Nat.le_of_dvd (by norm_num) h6
    have := hpp.two_le
    interval_cases p <;> first | (simp; done) | (norm_num at hpp; done) | norm_num at h6
  have hcard :
      Nat.card G = 2 ^ (Nat.card G).factorization 2 * 3 ^ (Nat.card G).factorization 3 := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self Nat.card_pos.ne']
    rw [Finsupp.prod_of_support_subset _ hsupp _ fun _ _ => pow_zero _]
    simp
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card]; exact hcard)

end General

section Pair

variable {X : Type} [Group X] {E : Set X}

theorem fischerQ_normal (hP : Pair X E) : (fischerQ E).Normal :=
  ⟨fun _ hy g => conj_mem_fischerQ (fun _ he => Pair.conj_mem hP he g) hy⟩

theorem fischerQ_ne_bot (hP : Pair X E) (hZ : center X = ⊥)
    (h3 : ∀ N : Subgroup X, N.Normal → IsPGroup 3 N → N = ⊥) : fischerQ E ≠ ⊥ := by
  obtain ⟨d, hd, e, he, hne, hc⟩ := Pair.exists_ne_commute_of_three hP hZ h3
  intro hbot
  have hmem := mul_mem_fischerQ hd he hne hc
  rw [hbot, mem_bot] at hmem
  have he' := eq_inv_of_mul_eq_one_right hmem
  rw [Pair.inv_eq hP hd] at he'
  exact hne he'.symm

theorem inv_mul_mem_of_minimal (hP : Pair X E) (hZ : center X = ⊥)
    (h2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥)
    (h3 : ∀ N : Subgroup X, N.Normal → IsPGroup 3 N → N = ⊥) {N : Subgroup X} (hNn : N.Normal)
    (hNbot : N ≠ ⊥) (hmin : ∀ K : Subgroup X, K.Normal → K ≤ N → K ≠ ⊥ → K = N) {a b : X}
    (ha : a ∈ E) (hb : b ∈ E) (hab : a * b = b * a) : a⁻¹ * b ∈ N := by
  have hNs := Pair.isSimpleGroup_of_minimal hP hZ h2 h3 hNn hNbot hmin
  have hNZ : ¬ N ≤ center X := fun h => hNbot (by rw [← le_bot_iff, ← hZ]; exact h)
  by_contra hne
  refine hNZ (Pair.normal_le_center_of_commute hP hNn hNs ha hb hab fun n hn => ?_)
  by_contra hc
  apply hne
  have hb' := Pair.conj_mem hP hb n
  have h1 := Pair.mul_conj_left_eq hP ha hb' hc
  have hπ : (QuotientGroup.mk (n * b * n⁻¹) : X ⧸ N) = QuotientGroup.mk b := by
    rw [QuotientGroup.eq]
    have := mul_mem hn (hNn.conj_mem _ (inv_mem hn) b⁻¹)
    convert this using 1
    group
  generalize n * b * n⁻¹ = b' at h1 hπ
  have key : (QuotientGroup.mk b : X ⧸ N) = QuotientGroup.mk a := by
    rw [← hπ]
    conv_lhs => rw [← h1]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hπ]
    have hab' : (QuotientGroup.mk a : X ⧸ N) * QuotientGroup.mk b =
        QuotientGroup.mk b * QuotientGroup.mk a := by
      rw [← QuotientGroup.mk_mul, hab, QuotientGroup.mk_mul]
    calc (QuotientGroup.mk a : X ⧸ N) * QuotientGroup.mk b * QuotientGroup.mk a *
          (QuotientGroup.mk a * QuotientGroup.mk b)⁻¹
        = QuotientGroup.mk a * (QuotientGroup.mk b * QuotientGroup.mk a) *
          (QuotientGroup.mk a * QuotientGroup.mk b)⁻¹ := by group
      _ = QuotientGroup.mk a := by rw [← hab']; group
  exact QuotientGroup.eq.1 key.symm

theorem fischerQ_le_of_minimal (hP : Pair X E) (hZ : center X = ⊥)
    (h2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥)
    (h3 : ∀ N : Subgroup X, N.Normal → IsPGroup 3 N → N = ⊥) {N : Subgroup X} (hNn : N.Normal)
    (hNbot : N ≠ ⊥) (hmin : ∀ K : Subgroup X, K.Normal → K ≤ N → K ≠ ⊥ → K = N) :
    fischerQ E ≤ N := by
  rw [fischerQ, closure_le]
  rintro _ ⟨d, hd, e, he, -, hc, rfl⟩
  have := inv_mul_mem_of_minimal hP hZ h2 h3 hNn hNbot hmin hd he hc
  rwa [Pair.inv_eq hP hd] at this

theorem fischerQ_minimal (hP : Pair X E) (hZ : center X = ⊥)
    (h2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥)
    (h3 : ∀ N : Subgroup X, N.Normal → IsPGroup 3 N → N = ⊥) :
    ∀ K : Subgroup X, K.Normal → K ≤ fischerQ E → K ≠ ⊥ → K = fischerQ E := by
  intro K hK hKQ hKbot
  have := Pair.finite hP
  obtain ⟨N, hNn, hNK, hNbot, hmin⟩ := CFSG.exists_minimal_normal_le K hK hKbot
  exact le_antisymm hKQ ((fischerQ_le_of_minimal hP hZ h2 h3 hNn hNbot hmin).trans hNK)

theorem eq_fischerQ_of_minimal (hP : Pair X E) (hZ : center X = ⊥)
    (h2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥)
    (h3 : ∀ N : Subgroup X, N.Normal → IsPGroup 3 N → N = ⊥) {N : Subgroup X} (hNn : N.Normal)
    (hNbot : N ≠ ⊥) (hmin : ∀ K : Subgroup X, K.Normal → K ≤ N → K ≠ ⊥ → K = N) :
    N = fischerQ E :=
  (hmin _ (fischerQ_normal hP) (fischerQ_le_of_minimal hP hZ h2 h3 hNn hNbot hmin)
    (fischerQ_ne_bot hP hZ h3)).symm

theorem isSimpleGroup_fischerQ (hP : Pair X E) (hZ : center X = ⊥)
    (h2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥)
    (h3 : ∀ N : Subgroup X, N.Normal → IsPGroup 3 N → N = ⊥) : IsSimpleGroup (fischerQ E) :=
  Pair.isSimpleGroup_of_minimal hP hZ h2 h3 (fischerQ_normal hP) (fischerQ_ne_bot hP hZ h3)
    (fischerQ_minimal hP hZ h2 h3)

theorem not_isSolvable_fischerQ (hP : Pair X E) (hZ : center X = ⊥)
    (h2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥)
    (h3 : ∀ N : Subgroup X, N.Normal → IsPGroup 3 N → N = ⊥) :
    ¬ Group.IsSolvable (fischerQ E) :=
  Pair.not_isSolvable_of_minimal hP hZ h2 h3 (fischerQ_normal hP) (fischerQ_ne_bot hP hZ h3)
    (fischerQ_minimal hP hZ h2 h3)

theorem fischerQ_le_commutator (hP : Pair X E) (hZ : center X = ⊥)
    (h2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥)
    (h3 : ∀ N : Subgroup X, N.Normal → IsPGroup 3 N → N = ⊥) :
    fischerQ E ≤ commutator X := by
  have hQs := isSimpleGroup_fischerQ hP hZ h2 h3
  have hQsol := not_isSolvable_fischerQ hP hZ h2 h3
  have hcN : commutator (fischerQ E) = ⊤ := by
    rcases hQs.eq_bot_or_eq_top_of_normal (commutator (fischerQ E)) with h | h
    · exfalso
      apply hQsol
      refine Group.isSolvable_of_comm fun a b => ?_
      have hc : ⁅a, b⁆ ∈ commutator (fischerQ E) := by
        rw [commutator_def]
        exact commutator_mem_commutator (mem_top a) (mem_top b)
      rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
      exact hc
    · exact h
  intro n hn
  have hmem : (⟨n, hn⟩ : fischerQ E) ∈ commutator (fischerQ E) := hcN ▸ mem_top _
  have h1 : n ∈ (commutator (fischerQ E)).map (fischerQ E).subtype := ⟨⟨n, hn⟩, hmem, rfl⟩
  rw [map_subtype_commutator] at h1
  exact commutator_mono le_top le_top h1

theorem commutator_le_fischerQ (hP : Pair X E)
    (hcos : ∀ d ∈ E, ∀ e ∈ E, d * e ∈ fischerQ E) : commutator X ≤ fischerQ E := by
  have := fischerQ_normal hP
  obtain ⟨e₀, he₀⟩ := Pair.nonempty hP
  have hall : ∀ e ∈ E, e₀⁻¹ * e ∈ fischerQ E := fun e he => by
    rw [Pair.inv_eq hP he₀]
    exact hcos e₀ he₀ e he
  rw [← Subgroup.Normal.quotient_commutative_iff_commutator_le]
  have hpow : ∀ g : X, (QuotientGroup.mk g : X ⧸ fischerQ E) ∈
      zpowers (QuotientGroup.mk e₀ : X ⧸ fischerQ E) := by
    intro g
    have hg : g ∈ closure E := (Pair.closure_eq hP).symm ▸ mem_top g
    induction hg using closure_induction with
    | mem x hx =>
      rw [(QuotientGroup.eq.2 (hall x hx)).symm]
      exact mem_zpowers _
    | one => exact one_mem _
    | mul x y _ _ hx hy => rw [QuotientGroup.mk_mul]; exact mul_mem hx hy
    | inv x _ hx => rw [QuotientGroup.mk_inv]; exact inv_mem hx
  refine ⟨⟨fun q₁ q₂ => ?_⟩⟩
  obtain ⟨g₁, rfl⟩ := QuotientGroup.mk_surjective q₁
  obtain ⟨g₂, rfl⟩ := QuotientGroup.mk_surjective q₂
  obtain ⟨k₁, hk₁⟩ := mem_zpowers_iff.1 (hpow g₁)
  obtain ⟨k₂, hk₂⟩ := mem_zpowers_iff.1 (hpow g₂)
  rw [← hk₁, ← hk₂, ← zpow_add, ← zpow_add, add_comm]

theorem commutator_eq_fischerQ_iff (hP : Pair X E) (hZ : center X = ⊥)
    (h2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥)
    (h3 : ∀ N : Subgroup X, N.Normal → IsPGroup 3 N → N = ⊥) :
    commutator X = fischerQ E ↔ ∀ d ∈ E, ∀ e ∈ E, d * e ∈ fischerQ E := by
  refine ⟨fun h d hd e he => ?_, fun hcos =>
    le_antisymm (commutator_le_fischerQ hP hcos) (fischerQ_le_commutator hP hZ h2 h3)⟩
  rw [← h]
  obtain ⟨g, rfl⟩ := isConj_iff.1 (Pair.isConj hP hd he)
  have e1 : d * (g * d * g⁻¹) = ⁅d, g⁆ := by
    rw [commutatorElement_def, Pair.inv_eq hP hd]
    group
  rw [e1, commutator_def]
  exact commutator_mem_commutator (mem_top d) (mem_top g)

theorem isSimpleGroup_commutator_iff (hP : Pair X E) (hZ : center X = ⊥)
    (h2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥)
    (h3 : ∀ N : Subgroup X, N.Normal → IsPGroup 3 N → N = ⊥) :
    IsSimpleGroup (commutator X) ↔ ∀ d ∈ E, ∀ e ∈ E, d * e ∈ fischerQ E := by
  rw [← commutator_eq_fischerQ_iff hP hZ h2 h3]
  refine ⟨fun hs => ?_, fun h => h ▸ isSimpleGroup_fischerQ hP hZ h2 h3⟩
  have hle := fischerQ_le_commutator hP hZ h2 h3
  have : ((fischerQ E).subgroupOf (commutator X)).Normal := (fischerQ_normal hP).subgroupOf _
  rcases hs.eq_bot_or_eq_top_of_normal ((fischerQ E).subgroupOf (commutator X)) with h | h
  · rw [subgroupOf_eq_bot] at h
    exact absurd (h.eq_bot_of_le hle) (fischerQ_ne_bot hP hZ h3)
  · exact le_antisymm (subgroupOf_eq_top.1 h) hle

end Pair

end CFSG.LargeExtraspecial
