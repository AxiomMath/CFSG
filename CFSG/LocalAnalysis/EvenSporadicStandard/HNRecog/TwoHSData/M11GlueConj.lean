module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.M11Glue

public section

namespace CFSG.EvenSporadicStandard.HNRecog.TwoHSData

open Subgroup

private lemma factorization_7920_five : (7920 : ℕ).factorization 5 = 1 := by
  have h : (7920 : ℕ) = 5 * 1584 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_self Nat.prime_five,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

private lemma map_conj_map_conj {G : Type*} [Group G] (H : Subgroup G) (g h : G) :
    (H.map (MulAut.conj g).toMonoidHom).map (MulAut.conj h).toMonoidHom
      = H.map (MulAut.conj (h * g)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

private lemma map_conj_map_conj_inv {G : Type*} [Group G] (H : Subgroup G) (g : G) :
    (H.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = H := by
  rw [Subgroup.map_map]
  have hcomp : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id G := by
    ext x
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    group
  rw [hcomp, Subgroup.map_id]

theorem exists_conj_eq_of_isM11Like {G : Type*} [Group G] {E : Subgroup G} (hE : E.Normal)
    {a z b z₁ y₀ n₁ : G} {M₀ : Subgroup G} (hM₀ : IsM11Like ↥M₀) (hy₀ : orderOf y₀ = 11)
    (hy₀M : y₀ ∈ M₀) (hn₁ : n₁ * y₀ * n₁⁻¹ ∈ zpowers y₀)
    (hsyl : ∀ t : G, orderOf t = 11 → ∃ x : G, x⁻¹ * t * x ∈ zpowers y₀)
    (hodd : ∀ t : G, orderOf t = 11 → t ∈ E) (hb : b ∉ E) (hz₁ : z₁ ∉ E)
    (ha : ∀ g : G, a * g = g * a)
    (hcover : ∀ x : G, orderOf x = 2 → ∃ k : Fin 5, IsConj (![a, z, a * z, b, z₁] k) x)
    (hj : ∀ j : G, (IsConj z j ∨ IsConj (a * z) j) →
      j ∈ M₀ ∨ n₁ * j * n₁⁻¹ ∈ M₀ ∨
        ∃ w ∈ closure ({y₀, j} : Set G), ¬ M11Order (orderOf w))
    (M : Subgroup G) (hM : IsM11Like ↥M) :
    ∃ g : G, M = M₀.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨y, v, hy, hv, hyv⟩ := hM.exists_gen
  have hy₁ : orderOf (y : G) = 11 := by rw [Subgroup.orderOf_coe, hy]
  obtain ⟨x, hxmem⟩ := hsyl (y : G) hy₁
  let M₁ : Subgroup G := M.map (MulAut.conj x⁻¹).toMonoidHom
  have hM₁ : IsM11Like ↥M₁ := hM.map_conj x⁻¹
  have hMx : M = M₁.map (MulAut.conj x).toMonoidHom := by
    have h : M₁.map (MulAut.conj x).toMonoidHom = M := by
      change (M.map (MulAut.conj x⁻¹).toMonoidHom).map (MulAut.conj x).toMonoidHom = M
      simpa using map_conj_map_conj_inv M x⁻¹
    exact h.symm
  let t : G := x⁻¹ * (y : G) * x
  have ht_eq : t = (MulAut.conj x⁻¹) (y : G) := by simp [t, MulAut.conj_apply]
  have htmem : t ∈ zpowers y₀ := by
    rw [ht_eq]; simpa [MulAut.conj_apply] using hxmem
  have htM₁ : t ∈ M₁ := by
    refine Subgroup.mem_map.mpr ⟨(y : G), y.2, ?_⟩
    exact ht_eq.symm
  have htord : orderOf t = 11 := by
    rw [ht_eq, MulEquiv.orderOf_eq (MulAut.conj x⁻¹) (y : G), hy₁]
  have hy₀M₁ : y₀ ∈ M₁ := by
    haveI : Finite ↥(zpowers y₀) :=
      Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hy₀]; norm_num)
    have hle : zpowers t ≤ zpowers y₀ := Subgroup.zpowers_le.mpr htmem
    have hzp : zpowers t = zpowers y₀ := by
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, htord, hy₀]
    have hy₀zp : y₀ ∈ zpowers t := by rw [hzp]; exact Subgroup.mem_zpowers y₀
    exact (Subgroup.zpowers_le.mpr htM₁) hy₀zp
  have hy₂ : orderOf (⟨y₀, hy₀M₁⟩ : ↥M₁) = 11 := by
    rw [Subgroup.orderOf_mk, hy₀]
  obtain ⟨i, hi2, hicl⟩ := hM₁.exists_involution ⟨y₀, hy₀M₁⟩ hy₂
  let i₁ : G := (i : G)
  have hi₁ord : orderOf i₁ = 2 := by
    rw [show i₁ = (i : G) from rfl, Subgroup.orderOf_coe, hi2]
  have hi₁M₁ : i₁ ∈ M₁ := i.2
  have hclosureM₁ : closure ({y₀, i₁} : Set G) = M₁ := by
    have h1 : (closure ({⟨y₀, hy₀M₁⟩, i} : Set ↥M₁)).map M₁.subtype = M₁ := by
      rw [hicl, ← MonoidHom.range_eq_map M₁.subtype, Subgroup.range_subtype]
    rw [MonoidHom.map_closure, Set.image_pair] at h1
    simpa using h1
  have hi₁E : i₁ ∈ E := (hM₁.le_of_order_eleven (E := E) hodd) hi₁M₁
  have hji : IsConj z i₁ ∨ IsConj (a * z) i₁ := by
    obtain ⟨k, hk⟩ := hcover i₁ hi₁ord
    fin_cases k
    · exfalso
      have hk0 : IsConj a i₁ := by simpa using hk
      obtain ⟨c, hc⟩ := isConj_iff.mp hk0
      have hia : i₁ = a := by
        rw [← hc, (ha c).symm, mul_assoc, mul_inv_cancel, mul_one]
      have hcommGen : ∀ p ∈ ({y₀, i₁} : Set G), ∀ q ∈ ({y₀, i₁} : Set G), p * q = q * p := by
        intro p hp q hq
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
        rcases hp with hp | hp <;> rcases hq with hq | hq
        · rw [hp, hq]
        · rw [hp, hq, hia]; exact (ha y₀).symm
        · rw [hp, hq, hia]; exact ha y₀
        · rw [hp, hq]
      haveI : IsMulCommutative ↥M₁ := by
        rw [← hclosureM₁]
        exact Subgroup.isMulCommutative_closure (fun p hp q hq _ => hcommGen p hp q hq)
      obtain ⟨u, w, huw⟩ := hM₁.nonabelian
      exact huw (mul_comm' u w)
    · exact Or.inl (by simpa using hk)
    · exact Or.inr (by simpa using hk)
    · exfalso
      have hk3 : IsConj b i₁ := by simpa using hk
      obtain ⟨c, hc⟩ := isConj_iff.mp hk3
      have hbE : b ∈ E := by
        have hb' : b = c⁻¹ * i₁ * c := by rw [← hc]; group
        rw [hb']
        simpa using hE.conj_mem i₁ hi₁E c⁻¹
      exact hb hbE
    · exfalso
      have hk4 : IsConj z₁ i₁ := by simpa using hk
      obtain ⟨c, hc⟩ := isConj_iff.mp hk4
      have hz₁E : z₁ ∈ E := by
        have hz' : z₁ = c⁻¹ * i₁ * c := by rw [← hc]; group
        rw [hz']
        simpa using hE.conj_mem i₁ hi₁E c⁻¹
      exact hz₁ hz₁E
  rcases hj i₁ hji with hi₁M₀ | hni₁M₀ | ⟨w, hw, hword⟩
  · refine ⟨x, ?_⟩
    have hle : M₁ ≤ M₀ := by
      rw [← hclosureM₁]
      refine (Subgroup.closure_le _).mpr ?_
      intro p hp
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with hp | hp
      · rw [hp]; exact hy₀M
      · rw [hp]; exact hi₁M₀
    haveI : Finite ↥M₀ := Nat.finite_of_card_ne_zero (by rw [hM₀.card_eq]; norm_num)
    have hM₁_eq : M₁ = M₀ :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hM₀.card_eq, hM₁.card_eq])
    rw [hMx, hM₁_eq]
  · refine ⟨x * n₁⁻¹, ?_⟩
    let M₂ : Subgroup G := M₁.map (MulAut.conj n₁).toMonoidHom
    have hclosureM₂ : M₂ = closure ({n₁ * y₀ * n₁⁻¹, n₁ * i₁ * n₁⁻¹} : Set G) := by
      have hmap : (closure ({y₀, i₁} : Set G)).map (MulAut.conj n₁).toMonoidHom
          = closure ({n₁ * y₀ * n₁⁻¹, n₁ * i₁ * n₁⁻¹} : Set G) := by
        rw [MonoidHom.map_closure, Set.image_pair]
        simp [MulAut.conj_apply]
      change M₁.map (MulAut.conj n₁).toMonoidHom
        = closure ({n₁ * y₀ * n₁⁻¹, n₁ * i₁ * n₁⁻¹} : Set G)
      rw [← hclosureM₁]
      exact hmap
    have hle2 : M₂ ≤ M₀ := by
      rw [hclosureM₂]
      refine (Subgroup.closure_le _).mpr ?_
      intro p hp
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with hp | hp
      · rw [hp]; exact (Subgroup.zpowers_le.mpr hy₀M) hn₁
      · rw [hp]; exact hni₁M₀
    have hcardM₂ : Nat.card ↥M₂ = 7920 := by
      have h : Nat.card ↥M₁ = Nat.card ↥M₂ :=
        Nat.card_congr (Subgroup.equivMapOfInjective M₁ (MulAut.conj n₁).toMonoidHom
          (MulAut.conj n₁).injective).toEquiv
      rw [← h, hM₁.card_eq]
    haveI : Finite ↥M₀ := Nat.finite_of_card_ne_zero (by rw [hM₀.card_eq]; norm_num)
    have hM₂_eq : M₂ = M₀ :=
      Subgroup.eq_of_le_of_card_ge hle2 (by rw [hcardM₂, hM₀.card_eq])
    have hM₁_eq : M₁ = M₀.map (MulAut.conj n₁⁻¹).toMonoidHom := by
      have h : M₂.map (MulAut.conj n₁⁻¹).toMonoidHom = M₁ := by
        change (M₁.map (MulAut.conj n₁).toMonoidHom).map (MulAut.conj n₁⁻¹).toMonoidHom = M₁
        exact map_conj_map_conj_inv M₁ n₁
      rw [hM₂_eq] at h
      exact h.symm
    calc M = M₁.map (MulAut.conj x).toMonoidHom := hMx
      _ = (M₀.map (MulAut.conj n₁⁻¹).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
            rw [hM₁_eq]
      _ = M₀.map (MulAut.conj (x * n₁⁻¹)).toMonoidHom := map_conj_map_conj M₀ n₁⁻¹ x
  · exfalso
    have hwM₁ : w ∈ M₁ := hclosureM₁ ▸ hw
    have hord := hM₁.orderOf_mem (⟨w, hwM₁⟩ : ↥M₁)
    rw [Subgroup.orderOf_mk] at hord
    exact hword hord

theorem exists_conj_of_conj {G : Type*} [Group G] {M₀ M M' : Subgroup G}
    (h : ∃ g : G, M = M₀.map (MulAut.conj g).toMonoidHom)
    (h' : ∃ g : G, M' = M₀.map (MulAut.conj g).toMonoidHom) :
    ∃ g : G, M' = M.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨g', hg'⟩ := h'
  refine ⟨g' * g⁻¹, ?_⟩
  rw [hg', hg, map_conj_map_conj M₀ g (g' * g⁻¹),
    show (g' * g⁻¹) * g = g' from by group]

theorem isConj_of_orderOf_five {G : Type*} [Group G] [Finite G] {M₀ : Subgroup G}
    (hM₀ : IsM11Like ↥M₀) {ρ₀ : G} (hρ₀ : ρ₀ ∈ M₀) (hρ₀o : orderOf ρ₀ = 5)
    (hck : ∀ k : ℕ, 0 < k → k < 5 → ∃ c ∈ M₀, c * ρ₀ * c⁻¹ = ρ₀ ^ k) {ρ : G} (hρ : ρ ∈ M₀)
    (hρo : orderOf ρ = 5) : IsConj ρ₀ ρ := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hS : Nat.card (zpowers ρ₀) = 5 ^ (Nat.card M₀).factorization 5 := by
    rw [Nat.card_zpowers, hρ₀o, hM₀.card_eq, factorization_7920_five, pow_one]
  obtain ⟨x, -, hx⟩ :=
    exists_conj_mem_of_orderOf_eq_prime (M := G) (p := 5) (R := M₀) (S := zpowers ρ₀)
      (Subgroup.zpowers_le.mpr hρ₀) hS hρ hρo
  rw [mem_zpowers_iff_mem_range_orderOf] at hx
  obtain ⟨m, hmrange, hm⟩ := Finset.mem_image.mp hx
  rw [Finset.mem_range, hρ₀o] at hmrange
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with hm0 | hpos
    · exfalso
      have hρ1 : ρ = 1 := by
        have h1 : x⁻¹ * ρ * x = 1 := by rw [← hm, hm0, pow_zero]
        have := congrArg (fun z : G => x * z * x⁻¹) h1
        simpa [mul_assoc] using this
      rw [hρ1, orderOf_one] at hρo
      norm_num at hρo
    · exact hpos
  obtain ⟨c, -, hc⟩ := hck m hmpos hmrange
  refine isConj_iff.mpr ⟨x * c, ?_⟩
  have hρ_eq : ρ = x * ρ₀ ^ m * x⁻¹ := by
    rw [hm]; group
  rw [hρ_eq, ← hc]
  group

end CFSG.EvenSporadicStandard.HNRecog.TwoHSData
