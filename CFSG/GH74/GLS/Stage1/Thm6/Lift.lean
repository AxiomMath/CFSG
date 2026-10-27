module

public import Mathlib.GroupTheory.SchurZassenhaus

public section

namespace CFSG.GH74.GLS.Stage1.Thm6

open Subgroup

section Comap

variable {C : Type*} [Group C] (N : Subgroup C) [N.Normal] (Abar : Subgroup (C ⧸ N))

abbrev preimageSub : Subgroup C := Abar.comap (QuotientGroup.mk' N)

theorem le_preimageSub : N ≤ preimageSub N Abar := fun n hn => by
  show (QuotientGroup.mk' N) n ∈ Abar
  rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff n).mpr hn]
  exact Abar.one_mem

abbrev comapHom : ↥(preimageSub N Abar) →* ↥Abar := (QuotientGroup.mk' N).subgroupComap Abar

theorem comapHom_apply (m : ↥(preimageSub N Abar)) :
    ((comapHom N Abar m : ↥Abar) : C ⧸ N) = (m : C) := rfl

theorem comapHom_surjective : Function.Surjective (comapHom N Abar) := by
  intro a
  obtain ⟨c, hc⟩ := QuotientGroup.mk_surjective (a : C ⧸ N)
  refine ⟨⟨c, by show (QuotientGroup.mk' N) c ∈ Abar; rw [QuotientGroup.mk'_apply, hc]; exact a.2⟩, ?_⟩
  exact Subtype.ext (by rw [comapHom_apply]; exact hc)

theorem ker_comapHom : (comapHom N Abar).ker = N.subgroupOf (preimageSub N Abar) := by
  ext m
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← QuotientGroup.eq_one_iff]
  constructor
  · intro h
    have := congrArg Subtype.val h
    rwa [comapHom_apply] at this
  · intro h
    exact Subtype.ext (by rw [comapHom_apply]; exact h)

theorem card_preimageSub [Finite C] :
    Nat.card (preimageSub N Abar) = Nat.card N * Nat.card Abar := by
  have hNM := le_preimageSub N Abar
  have hindex : (N.subgroupOf (preimageSub N Abar)).index = Nat.card ↥Abar := by
    rw [← ker_comapHom, Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective _
      (comapHom_surjective N Abar), Subgroup.card_top]
  have h1 := Subgroup.card_mul_index (N.subgroupOf (preimageSub N Abar))
  rw [hindex, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv] at h1
  exact h1.symm

end Comap

section Lift

variable {C : Type*} [Group C] {p : ℕ} [Fact p.Prime]

theorem exists_lift_pSubgroup [Finite C] (N : Subgroup C) [N.Normal] (hN : ¬ p ∣ Nat.card N)
    (Abar : Subgroup (C ⧸ N)) (hA : IsPGroup p ↥Abar) :
    ∃ A : Subgroup C, IsPGroup p ↥A ∧ A.map (QuotientGroup.mk' N) = Abar ∧ A ⊓ N = ⊥ := by
  set π := QuotientGroup.mk' N with hπ
  set M : Subgroup C := preimageSub N Abar with hM
  have hNM : N ≤ M := le_preimageSub N Abar
  set N' : Subgroup ↥M := N.subgroupOf M with hN'
  have hN'n : N'.Normal := Subgroup.normal_subgroupOf
  set ϕ : ↥M →* ↥Abar := comapHom N Abar with hϕ
  have hindex : N'.index = Nat.card ↥Abar := by
    rw [hN', ← ker_comapHom, Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective _
      (comapHom_surjective N Abar), Subgroup.card_top]
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA
  have hcop : (Nat.card ↥N').Coprime N'.index := by
    rw [hindex, hk]
    have h1 : Nat.card ↥N' = Nat.card ↥N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv
    rw [h1]
    exact Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd (Fact.out)).mpr hN).symm
  obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hHp : IsPGroup p ↥H :=
    IsPGroup.of_card (n := k) (by rw [← hH.symm.index_eq_card, hindex, hk])
  refine ⟨H.map M.subtype, hHp.map M.subtype, ?_, ?_⟩
  · apply le_antisymm
    · rintro a ⟨c, ⟨h, _, rfl⟩, rfl⟩
      exact h.2
    · intro a ha
      obtain ⟨m, hm⟩ := comapHom_surjective N Abar ⟨a, ha⟩
      obtain ⟨⟨n, h⟩, hnh⟩ := hH.2 m
      have hn : ϕ (n : ↥M) = 1 := by
        rw [← MonoidHom.mem_ker, ker_comapHom]; exact n.2
      have h1 : ϕ (h : ↥M) = ⟨a, ha⟩ := by
        rw [← hm, ← hnh, map_mul, hn, one_mul]
      refine ⟨(h : ↥M), ⟨h, h.2, rfl⟩, ?_⟩
      have := congrArg Subtype.val h1
      rw [hϕ, comapHom_apply] at this
      exact this
  · rw [eq_bot_iff]
    rintro c ⟨⟨h, hhH, rfl⟩, hcN⟩
    have hhN : h ∈ N' := hcN
    have := Subgroup.disjoint_def.mp hH.disjoint hhN hhH
    rw [this]
    simp

end Lift

section Conj

variable {C : Type*} [Group C] (N : Subgroup C) [N.Normal]

theorem mem_smul_sylow' {X : Type*} [Group X] {p : ℕ} (P : Sylow p X) (g y : X) :
    y ∈ ((g • P : Sylow p X) : Subgroup X) ↔ g⁻¹ * y * g ∈ (P : Subgroup X) := by
  rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp [MulAut.smul_def]

omit [N.Normal] in
theorem eq_one_of_mem_of_sq_eq_one [Finite C] (hN : ¬ 2 ∣ Nat.card N) {a : C} (ha : a ∈ N)
    (ha2 : a * a = 1) : a = 1 := by
  have h1 : orderOf a ∣ Nat.card N := by
    have := orderOf_dvd_natCard (⟨a, ha⟩ : N)
    rwa [Subgroup.orderOf_mk] at this
  have h2 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using ha2)
  have h3 : orderOf a = 1 ∨ orderOf a = 2 := (Nat.dvd_prime Nat.prime_two).mp h2
  rcases h3 with h | h
  · exact orderOf_eq_one_iff.mp h
  · exact absurd (h ▸ h1) hN

theorem eq_or_eq_one_of_mem_zpowers_sq {a w : C} (ha : a * a = 1) (hw : w ∈ Subgroup.zpowers a) :
    w = 1 ∨ w = a := by
  obtain ⟨k, hk⟩ := hw
  have hk' : a ^ k = w := hk
  have ha2 : a ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ha
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left
    rw [← hk', zpow_mul, ha2, one_zpow]
  · right
    rw [← hk', zpow_add, zpow_mul, ha2, one_zpow, one_mul, zpow_one]

theorem exists_conj_of_conj_mk [Finite C] (hN : ¬ 2 ∣ Nat.card N) {a z : C} (ha : a * a = 1)
    (hz : z * z = 1) (hconj : IsConj (QuotientGroup.mk a : C ⧸ N) (QuotientGroup.mk z)) :
    ∃ c : C, c * a * c⁻¹ = z := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨cbar, hcbar⟩ := isConj_iff.mp hconj
  obtain ⟨c₀, rfl⟩ := QuotientGroup.mk_surjective cbar
  have hπa' : (QuotientGroup.mk (c₀ * a * c₀⁻¹) : C ⧸ N) = QuotientGroup.mk z := by
    rw [← hcbar]; simp
  by_cases hz1 : z = 1
  · subst hz1
    have h1 : (QuotientGroup.mk (c₀ * a * c₀⁻¹) : C ⧸ N) = 1 := by rw [hπa']; rfl
    have h2' : c₀ * a * c₀⁻¹ ∈ N := (QuotientGroup.eq_one_iff _).mp h1
    have hsq : (c₀ * a * c₀⁻¹) * (c₀ * a * c₀⁻¹) = 1 := by
      calc (c₀ * a * c₀⁻¹) * (c₀ * a * c₀⁻¹) = c₀ * (a * a) * c₀⁻¹ := by group
        _ = 1 := by rw [ha]; group
    have := eq_one_of_mem_of_sq_eq_one N hN h2' hsq
    refine ⟨1, ?_⟩
    have ha1 : a = 1 := by
      have : c₀ * a * c₀⁻¹ = 1 := this
      have h3 : a = c₀⁻¹ * (c₀ * a * c₀⁻¹) * c₀ := by group
      rw [h3, this]; group
    simp [ha1]
  · set a' := c₀ * a * c₀⁻¹ with ha'
    have hπz1 : (QuotientGroup.mk z : C ⧸ N) ≠ 1 := fun h =>
      hz1 (eq_one_of_mem_of_sq_eq_one N hN ((QuotientGroup.eq_one_iff z).mp h) hz)
    have hz2 : z ^ 2 = 1 := by simpa [pow_two] using hz
    have hsq' : a' * a' = 1 := by
      calc a' * a' = c₀ * (a * a) * c₀⁻¹ := by rw [ha']; group
        _ = 1 := by rw [ha]; group
    have ha'1 : a' ≠ 1 := fun h => hπz1 (by rw [← hπa', h]; rfl)
    set Abar : Subgroup (C ⧸ N) := Subgroup.zpowers (QuotientGroup.mk z : C ⧸ N) with hAbar
    have hAcard : Nat.card ↥Abar = 2 := by
      rw [hAbar, Nat.card_zpowers]
      exact orderOf_eq_prime (by rw [← QuotientGroup.mk_pow, hz2]; rfl) hπz1
    have hMcard : Nat.card (preimageSub N Abar) = Nat.card N * 2 := by
      rw [card_preimageSub, hAcard]
    have hzM : z ∈ preimageSub N Abar := Subgroup.mem_zpowers _
    have ha'M : a' ∈ preimageSub N Abar := by
      show (QuotientGroup.mk' N) a' ∈ Abar
      rw [QuotientGroup.mk'_apply, hπa']
      exact Subgroup.mem_zpowers _
    have hfac : (Nat.card (preimageSub N Abar)).factorization 2 = 1 := by
      have hNpos : Nat.card N ≠ 0 := Nat.card_pos.ne'
      rw [hMcard, Nat.factorization_mul hNpos (by norm_num)]
      simp [Nat.factorization_eq_zero_of_not_dvd hN, Nat.Prime.factorization_self Nat.prime_two]
    set M := preimageSub N Abar with hM
    have hzle : Subgroup.zpowers z ≤ M := (Subgroup.zpowers_le).mpr hzM
    have ha'le : Subgroup.zpowers a' ≤ M := (Subgroup.zpowers_le).mpr ha'M
    have hPz : Nat.card ↥((Subgroup.zpowers z).subgroupOf M) = 2 ^ (Nat.card M).factorization 2 := by
      rw [hfac, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzle).toEquiv, Nat.card_zpowers,
        orderOf_eq_prime hz2 hz1]
      norm_num
    have hPa : Nat.card ↥((Subgroup.zpowers a').subgroupOf M) = 2 ^ (Nat.card M).factorization 2 := by
      rw [hfac, Nat.card_congr (Subgroup.subgroupOfEquivOfLe ha'le).toEquiv, Nat.card_zpowers,
        orderOf_eq_prime (p := 2) (by simpa [pow_two] using hsq') ha'1]
      norm_num
    let SZ : Sylow 2 ↥M := Sylow.ofCard _ hPz
    let SA : Sylow 2 ↥M := Sylow.ofCard _ hPa
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥M) SA SZ
    have hz' : (⟨z, hzM⟩ : ↥M) ∈ (SZ : Subgroup ↥M) := Subgroup.mem_zpowers z
    rw [← hg, mem_smul_sylow'] at hz'
    have hw : (g : C)⁻¹ * z * (g : C) ∈ Subgroup.zpowers a' := hz'
    rcases eq_or_eq_one_of_mem_zpowers_sq hsq' hw with h1 | h1
    · exfalso
      apply hz1
      have : z = (g : C) * ((g : C)⁻¹ * z * (g : C)) * (g : C)⁻¹ := by group
      rw [this, h1]; group
    · refine ⟨(g : C) * c₀, ?_⟩
      calc (g : C) * c₀ * a * ((g : C) * c₀)⁻¹ = (g : C) * (c₀ * a * c₀⁻¹) * (g : C)⁻¹ := by group
        _ = (g : C) * ((g : C)⁻¹ * z * (g : C)) * (g : C)⁻¹ := by rw [← ha', ← h1]
        _ = z := by group

end Conj

section Frattini

variable {C : Type*} [Group C] (N : Subgroup C) [N.Normal]

omit [N.Normal] in
theorem inf_eq_bot_of_isPGroup_of_coprime [Finite C] {T : Subgroup C} (hT : IsPGroup 2 ↥T)
    (hN : ¬ 2 ∣ Nat.card N) : T ⊓ N = ⊥ := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [eq_bot_iff]
  rintro t ⟨htT, htN⟩
  obtain ⟨k, hk⟩ := hT ⟨t, htT⟩
  have h1 : orderOf t ∣ Nat.card N := by
    have := orderOf_dvd_natCard (⟨t, htN⟩ : N)
    rwa [Subgroup.orderOf_mk] at this
  have hd : orderOf t ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  have hj0 : j = 0 := by
    by_contra hj0
    exact hN ((dvd_pow_self 2 hj0).trans (hj ▸ h1))
  rw [hj0] at hj
  exact (Subgroup.mem_bot).mpr (orderOf_eq_one_iff.mp (by simpa using hj))

theorem exists_normalizing_lift [Finite C] (hN : ¬ 2 ∣ Nat.card N) {E : Subgroup C}
    (hE : IsPGroup 2 ↥E) (hEab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) {fbar : C ⧸ N}
    (hf : ∀ y : C ⧸ N, y ∈ E.map (QuotientGroup.mk' N) ↔
      fbar * y * fbar⁻¹ ∈ E.map (QuotientGroup.mk' N)) :
    ∃ n : C, (∀ y : C, y ∈ E ↔ n * y * n⁻¹ ∈ E) ∧
      ∀ e ∈ E, (QuotientGroup.mk (n * e * n⁻¹) : C ⧸ N) = fbar * QuotientGroup.mk e * fbar⁻¹ := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' N with hπ
  set Ebar : Subgroup (C ⧸ N) := E.map π with hEbar
  set L : Subgroup C := preimageSub N Ebar with hL
  obtain ⟨f₀, hf₀⟩ := QuotientGroup.mk_surjective fbar
  have hEN : E ⊓ N = ⊥ := inf_eq_bot_of_isPGroup_of_coprime N hE hN
  have hEbarcard : Nat.card ↥Ebar = Nat.card ↥E := by
    have hinj : Function.Injective (π.domRestrict E) := by
      intro a b hab
      apply Subtype.ext
      have : π a = π b := hab
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at this
      have hmem : (a : C)⁻¹ * b ∈ E ⊓ N := ⟨E.mul_mem (E.inv_mem a.2) b.2, this⟩
      rw [hEN, Subgroup.mem_bot] at hmem
      exact inv_mul_eq_one.mp hmem
    rw [hEbar, ← MonoidHom.domRestrict_range]
    exact Nat.card_range_of_injective hinj
  have hLcard : Nat.card ↥L = Nat.card ↥N * Nat.card ↥E := by
    rw [hL, card_preimageSub, hEbarcard]
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hE
  have hfacL : (Nat.card ↥L).factorization 2 = m := by
    rw [hLcard, hm, Nat.factorization_mul Nat.card_pos.ne' (pow_ne_zero _ (by norm_num))]
    simp [Nat.factorization_eq_zero_of_not_dvd hN, Nat.Prime.factorization_pow Nat.prime_two]
  have hEL : E ≤ L := fun e he => by
    show π e ∈ Ebar
    exact ⟨e, he, rfl⟩
  have hf₀L : ∀ y : C, y ∈ L ↔ f₀ * y * f₀⁻¹ ∈ L := by
    intro y
    show π y ∈ Ebar ↔ π (f₀ * y * f₀⁻¹) ∈ Ebar
    have : π (f₀ * y * f₀⁻¹) = fbar * π y * fbar⁻¹ := by
      rw [hπ, QuotientGroup.mk'_apply]; simp [← hf₀]
    rw [this]
    exact hf y
  set E' : Subgroup C := E.map (MulAut.conj f₀).toMonoidHom with hE'
  have hE'L : E' ≤ L := by
    rintro y ⟨e, he, rfl⟩
    exact (hf₀L _).mp (hEL he)
  have hE'card : Nat.card ↥E' = Nat.card ↥E :=
    Subgroup.card_map_of_injective (MulAut.conj f₀).injective
  have hSE : Nat.card ↥(E.subgroupOf L) = 2 ^ (Nat.card ↥L).factorization 2 := by
    rw [hfacL, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv, hm]
  have hSE' : Nat.card ↥(E'.subgroupOf L) = 2 ^ (Nat.card ↥L).factorization 2 := by
    rw [hfacL, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE'L).toEquiv, hE'card, hm]
  let SE : Sylow 2 ↥L := Sylow.ofCard _ hSE
  let SE' : Sylow 2 ↥L := Sylow.ofCard _ hSE'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥L) SE' SE
  have hgE : ∀ y : C, y ∈ E ↔ (g : C)⁻¹ * y * (g : C) ∈ E' := by
    intro y
    by_cases hy : y ∈ L
    · have := mem_smul_sylow' SE' g ⟨y, hy⟩
      rw [hg] at this
      exact this
    · constructor
      · intro h; exact absurd (hEL h) hy
      · intro h
        have h1 : (g : C)⁻¹ * y * (g : C) ∈ L := hE'L h
        have e : (g : C) * ((g : C)⁻¹ * y * (g : C)) * (g : C)⁻¹ = y := by group
        exact absurd (e ▸ L.mul_mem (L.mul_mem g.2 h1) (L.inv_mem g.2)) hy
  have hE'mem : ∀ z : C, z ∈ E' ↔ f₀⁻¹ * z * f₀ ∈ E := by
    intro z
    constructor
    · rintro ⟨e, he, rfl⟩
      have : f₀⁻¹ * (f₀ * e * f₀⁻¹) * f₀ = e := by group
      simpa [MulAut.conj_apply, this] using he
    · intro h
      refine ⟨f₀⁻¹ * z * f₀, h, ?_⟩
      show f₀ * (f₀⁻¹ * z * f₀) * f₀⁻¹ = z
      group
  refine ⟨(g : C) * f₀, fun y => ?_, fun e he => ?_⟩
  · have e1 : (g : C)⁻¹ * ((g : C) * f₀ * y * ((g : C) * f₀)⁻¹) * (g : C) = f₀ * y * f₀⁻¹ := by
      group
    rw [hgE ((g : C) * f₀ * y * ((g : C) * f₀)⁻¹), e1, hE'mem]
    have e2 : f₀⁻¹ * (f₀ * y * f₀⁻¹) * f₀ = y := by group
    rw [e2]
  · have hEbar_ab : ∀ a ∈ Ebar, ∀ b ∈ Ebar, a * b = b * a := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hEab a ha b hb]
    have hπe : π e ∈ Ebar := ⟨e, he, rfl⟩
    have hconj : fbar * π e * fbar⁻¹ ∈ Ebar := (hf (π e)).mp hπe
    have hg : π (g : C) ∈ Ebar := g.2
    have hcomm := hEbar_ab _ hg _ hconj
    have : (QuotientGroup.mk ((g : C) * f₀ * e * ((g : C) * f₀)⁻¹) : C ⧸ N) =
        π (g : C) * (fbar * π e * fbar⁻¹) * (π (g : C))⁻¹ := by
      rw [hπ, QuotientGroup.mk'_apply]
      simp [QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← hf₀, mul_assoc]
    rw [this, hcomm, mul_inv_cancel_right]
    rfl

end Frattini

section ThreePart

variable {C : Type*} [Group C]

theorem pow_mem_normalizer_aux {E : Subgroup C} {n : C} (hn : ∀ y : C, y ∈ E ↔ n * y * n⁻¹ ∈ E)
    (j : ℕ) : ∀ y : C, y ∈ E ↔ n ^ j * y * (n ^ j)⁻¹ ∈ E := by
  induction j with
  | zero => intro y; simp
  | succ j ih =>
    intro y
    have e : n ^ (j + 1) * y * (n ^ (j + 1))⁻¹ = n ^ j * (n * y * n⁻¹) * (n ^ j)⁻¹ := by
      rw [pow_succ]
      generalize n ^ j = w
      group
    rw [e, ← ih (n * y * n⁻¹)]
    exact hn y

theorem exists_threeElement_acting [Finite C] {E : Subgroup C} {n : C}
    (hn : ∀ y : C, y ∈ E ↔ n * y * n⁻¹ ∈ E) {c : ℕ} (hc : ∀ e ∈ E, n ^ (3 ^ c) * e = e * n ^ (3 ^ c)) :
    ∃ m : C, (∃ a : ℕ, m ^ (3 ^ a) = 1) ∧ (∀ y : C, y ∈ E ↔ m * y * m⁻¹ ∈ E) ∧
      ∀ e ∈ E, m * e * m⁻¹ = n * e * n⁻¹ := by
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos n).ne' 3 (by norm_num)
  set M := 3 ^ (a + c + 1) with hM
  have hM1 : 1 < M := Nat.one_lt_pow (by omega) (by norm_num)
  have hcop : Nat.Coprime b M :=
    Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hb).symm
  obtain ⟨r, -, hr⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hM1
  refine ⟨n ^ (b * r), ⟨a, ?_⟩, pow_mem_normalizer_aux hn _, fun e he => ?_⟩
  · calc (n ^ (b * r)) ^ (3 ^ a) = (n ^ (3 ^ a * b)) ^ r := by rw [← pow_mul, ← pow_mul]; ring_nf
      _ = 1 := by rw [← hab, pow_orderOf_eq_one, one_pow]
  ·
    obtain ⟨t, ht⟩ : ∃ t, b * r = 1 + M * t := ⟨b * r / M, by
      have := Nat.div_add_mod (b * r) M
      rw [hr] at this
      omega⟩
    have hcomm : ∀ j : ℕ, n ^ (M * j) * e = e * n ^ (M * j) := by
      intro j
      have h1 : Commute (n ^ (3 ^ c)) e := hc e he
      have : n ^ (M * j) = (n ^ (3 ^ c)) ^ (3 ^ (a + 1) * j) := by
        rw [← pow_mul, hM]; ring_nf
      rw [this]
      exact (h1.pow_left _).eq
    rw [ht, pow_add, pow_one]
    have h2 := hcomm t
    calc n * n ^ (M * t) * e * (n * n ^ (M * t))⁻¹ = n * (n ^ (M * t) * e * (n ^ (M * t))⁻¹) * n⁻¹ := by
          group
      _ = n * e * n⁻¹ := by rw [h2]; group

end ThreePart

end CFSG.GH74.GLS.Stage1.Thm6
