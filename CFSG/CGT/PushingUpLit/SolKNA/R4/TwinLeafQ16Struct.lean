module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafBasic

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

variable {G : Type*} [Group G]

theorem Q16Pair.orderOf_eq {x y : G} (h : Q16Pair x y) : orderOf x = 8 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h4, h8, -, -⟩ := h
  have := orderOf_eq_prime_pow (p := 2) (n := 2) (x := x) (by simpa using h4) (by simpa using h8)
  simpa using this

theorem Q16Pair.mul_zpow {x y : G} (h : Q16Pair x y) (i : ℤ) : y * x ^ i = x ^ (-i) * y := by
  have h1 : y * x ^ i * y⁻¹ = x ^ (-i) := by
    rw [← conj_zpow, h.2.2.2, inv_zpow', zpow_neg]
  calc y * x ^ i = (y * x ^ i * y⁻¹) * y := by group
    _ = x ^ (-i) * y := by rw [h1]

theorem Q16Pair.mul_self_eq {x y : G} (h : Q16Pair x y) : y * y = x ^ (4 : ℤ) := by
  rw [← pow_two, h.2.2.1]
  norm_cast

theorem Q16Pair.mem_closure {x y : G} (h : Q16Pair x y) {g : G}
    (hg : g ∈ Subgroup.closure ({x, y} : Set G)) : ∃ i : ℤ, g = x ^ i ∨ g = y * x ^ i := by
  induction hg using Subgroup.closure_induction with
  | mem a ha =>
    rcases ha with rfl | ha
    · exact ⟨1, Or.inl (zpow_one _).symm⟩
    · rw [Set.mem_singleton_iff] at ha
      subst ha
      exact ⟨0, Or.inr (by simp)⟩
  | one => exact ⟨0, Or.inl (zpow_zero _).symm⟩
  | mul a b _ _ ha hb =>
    obtain ⟨i, rfl | rfl⟩ := ha <;> obtain ⟨j, rfl | rfl⟩ := hb
    · exact ⟨i + j, Or.inl (zpow_add _ _ _).symm⟩
    · refine ⟨-i + j, Or.inr ?_⟩
      have h1 : x ^ i * y = y * x ^ (-i) := by
        have := h.mul_zpow (-i)
        rw [neg_neg] at this
        exact this.symm
      calc x ^ i * (y * x ^ j) = (x ^ i * y) * x ^ j := by rw [mul_assoc]
        _ = y * (x ^ (-i) * x ^ j) := by rw [h1, mul_assoc]
        _ = y * x ^ (-i + j) := by rw [← zpow_add]
    · refine ⟨i + j, Or.inr ?_⟩
      rw [mul_assoc, ← zpow_add]
    · refine ⟨4 + (-i + j), Or.inl ?_⟩
      have h1 : x ^ i * y = y * x ^ (-i) := by
        have := h.mul_zpow (-i)
        rw [neg_neg] at this
        exact this.symm
      calc y * x ^ i * (y * x ^ j) = y * (x ^ i * y) * x ^ j := by group
        _ = y * (y * x ^ (-i)) * x ^ j := by rw [h1]
        _ = (y * y) * (x ^ (-i) * x ^ j) := by group
        _ = x ^ (4 : ℤ) * x ^ (-i + j) := by rw [h.mul_self_eq, ← zpow_add]
        _ = x ^ (4 + (-i + j)) := by rw [← zpow_add]
  | inv a _ ha =>
    obtain ⟨i, rfl | rfl⟩ := ha
    · exact ⟨-i, Or.inl (zpow_neg _ _).symm⟩
    · refine ⟨i - 4, Or.inr ?_⟩
      have hyinv : y⁻¹ = y * x ^ (-4 : ℤ) := by
        rw [inv_eq_iff_mul_eq_one, ← mul_assoc, h.mul_self_eq, ← zpow_add]
        simp
      calc (y * x ^ i)⁻¹ = x ^ (-i) * y⁻¹ := by rw [mul_inv_rev, zpow_neg]
        _ = x ^ (-i) * (y * x ^ (-4 : ℤ)) := by rw [hyinv]
        _ = (x ^ (-i) * y) * x ^ (-4 : ℤ) := by rw [mul_assoc]
        _ = (y * x ^ i) * x ^ (-4 : ℤ) := by
          rw [h.mul_zpow i]
        _ = y * x ^ (i - 4) := by rw [mul_assoc, ← zpow_add]; congr 1

theorem Q16Pair.not_mem_zpowers {x y : G} (h : Q16Pair x y) : y ∉ Subgroup.zpowers x := by
  intro hy
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  have h1 := h.2.2.2
  rw [(Commute.self_zpow x i).symm.eq, mul_inv_cancel_right] at h1
  have h2 : x ^ 2 = 1 := by
    rw [pow_two]
    exact mul_eq_one_iff_eq_inv.2 h1
  have h3 := orderOf_dvd_of_pow_eq_one h2
  rw [h.orderOf_eq] at h3
  omega

theorem Q16Pair.eq_of_central {x y : G} (h : Q16Pair x y) {g : G}
    (hg : g ∈ Subgroup.closure ({x, y} : Set G)) (hcx : g * x = x * g) (hcy : g * y = y * g) :
    g = 1 ∨ g = x ^ 4 := by
  have hx8 := h.orderOf_eq
  obtain ⟨i, rfl | rfl⟩ := h.mem_closure hg
  ·
    have h1 : x ^ i * y = x ^ (-i) * y := by rw [hcy, h.mul_zpow]
    have h2 : x ^ i = x ^ (-i) := mul_right_cancel h1
    have h3 : x ^ (i + i) = 1 := by
      have : x ^ i * x ^ i = x ^ (-i) * x ^ i := by rw [← h2]
      rw [zpow_add, this, ← zpow_add, neg_add_cancel, zpow_zero]
    have h4 : ((orderOf x : ℕ) : ℤ) ∣ i + i := orderOf_dvd_iff_zpow_eq_one.2 h3
    rw [hx8] at h4
    have h5 : x ^ (i % (orderOf x : ℤ)) = x ^ i := zpow_mod_orderOf x i
    rw [hx8] at h5
    have h6 : i % 8 = 0 ∨ i % 8 = 4 := by omega
    rcases h6 with h6 | h6
    · left
      rw [← h5]
      push_cast
      rw [h6, zpow_zero]
    · right
      rw [← h5]
      push_cast
      rw [h6]
      norm_cast
  ·
    exfalso
    have h1 : y * x ^ (i + 1) = y * x ^ (-1 + i) := by
      calc y * x ^ (i + 1) = y * x ^ i * x := by rw [zpow_add_one, mul_assoc]
        _ = x * (y * x ^ i) := hcx
        _ = (x * y) * x ^ i := by rw [mul_assoc]
        _ = (y * x ^ (-1 : ℤ)) * x ^ i := by
          have := h.mul_zpow (-1)
          rw [neg_neg, zpow_one] at this
          rw [← this]
        _ = y * x ^ (-1 + i) := by rw [mul_assoc, ← zpow_add]
    have h2 : x ^ (i + 1) = x ^ (-1 + i) := mul_left_cancel h1
    have h3 : x ^ (2 : ℤ) = 1 := by
      have h4 : x ^ (i + 1) * (x ^ (-1 + i))⁻¹ = 1 := by rw [h2, mul_inv_cancel]
      rw [← zpow_neg, ← zpow_add] at h4
      rw [← h4]
      congr 1
      ring
    have h4 : ((orderOf x : ℕ) : ℤ) ∣ 2 := orderOf_dvd_iff_zpow_eq_one.2 h3
    rw [hx8] at h4
    omega

theorem Q16Pair.card_closure_ge [Finite G] {x y : G} (h : Q16Pair x y) :
    16 ≤ Nat.card ↥(Subgroup.closure ({x, y} : Set G)) := by
  set R := Subgroup.closure ({x, y} : Set G) with hR
  have hxR : x ∈ R := Subgroup.subset_closure (Set.mem_insert _ _)
  have hyR : y ∈ R := Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hle : Subgroup.zpowers x ≤ R := Subgroup.zpowers_le.2 hxR
  have hdvd : Nat.card (Subgroup.zpowers x) ∣ Nat.card R := Subgroup.card_dvd_of_le hle
  rw [Nat.card_zpowers, h.orderOf_eq] at hdvd
  have hne : Nat.card R ≠ 8 := by
    intro h8
    have heq : Subgroup.zpowers x = R :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [h8, Nat.card_zpowers, h.orderOf_eq])
    rw [← heq] at hyR
    exact h.not_mem_zpowers hyR
  obtain ⟨k, hk⟩ := hdvd
  have hpos : 0 < Nat.card R := Nat.card_pos
  omega

end CFSG.CGT.PushingUpLit.SolKNA.R4

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf

variable {G : Type*} [Group G]

theorem Q16Q16.comm_closure {x y x' y' : G} (h : Q16Q16 x y x' y') :
    ∀ a ∈ Subgroup.closure ({x, y} : Set G), ∀ b ∈ Subgroup.closure ({x', y'} : Set G),
      a * b = b * a := by
  obtain ⟨-, -, -, hxx', hxy', hyx', hyy'⟩ := h
  set R₂ := Subgroup.closure ({x', y'} : Set G) with hR₂
  have hRx : R₂ ≤ Subgroup.centralizer ({x} : Set G) := by
    rw [hR₂, Subgroup.closure_le]
    rintro g (rfl | hg)
    · exact Subgroup.mem_centralizer_singleton_iff.2 hxx'.symm
    · rw [Set.mem_singleton_iff] at hg
      subst hg
      exact Subgroup.mem_centralizer_singleton_iff.2 hxy'.symm
  have hRy : R₂ ≤ Subgroup.centralizer ({y} : Set G) := by
    rw [hR₂, Subgroup.closure_le]
    rintro g (rfl | hg)
    · exact Subgroup.mem_centralizer_singleton_iff.2 hyx'.symm
    · rw [Set.mem_singleton_iff] at hg
      subst hg
      exact Subgroup.mem_centralizer_singleton_iff.2 hyy'.symm
  have hxC : x ∈ Subgroup.centralizer (R₂ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact Subgroup.mem_centralizer_singleton_iff.1 (hRx hb)
  have hyC : y ∈ Subgroup.centralizer (R₂ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact Subgroup.mem_centralizer_singleton_iff.1 (hRy hb)
  have hR₁ : Subgroup.closure ({x, y} : Set G) ≤ Subgroup.centralizer (R₂ : Set G) := by
    rw [Subgroup.closure_le]
    rintro g (rfl | hg)
    · exact hxC
    · rw [Set.mem_singleton_iff] at hg
      subst hg
      exact hyC
  intro a ha b hb
  exact (Subgroup.mem_centralizer_iff.1 (hR₁ ha) b hb).symm

theorem Q16Q16.card_ge [Finite G] {x y x' y' : G} (h : Q16Q16 x y x' y') :
    128 ≤ Nat.card ↥(Subgroup.closure ({x, y} : Set G) ⊔ Subgroup.closure ({x', y'} : Set G)) := by
  classical
  set R₁ := Subgroup.closure ({x, y} : Set G) with hR₁
  set R₂ := Subgroup.closure ({x', y'} : Set G) with hR₂
  have hcomm := h.comm_closure
  have hc : ∀ (a : ↥R₁) (b : ↥R₂), Commute (R₁.subtype a) (R₂.subtype b) :=
    fun a b => hcomm a a.2 b b.2
  have hrange : (MonoidHom.noncommCoprod R₁.subtype R₂.subtype hc).range = R₁ ⊔ R₂ := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  set μ : ↥R₁ × ↥R₂ →* G := MonoidHom.noncommCoprod R₁.subtype R₂.subtype hc with hμ
  have hker : Nat.card μ.ker ≤ 2 := by
    let f : ↥μ.ker → Bool := fun p => decide (((p.1.1 : ↥R₁) : G) = 1)
    have hx4 : x ^ 4 ≠ 1 := h.1.1
    have hinj : Function.Injective f := by
      intro p q hpq
      have hpa : ((p.1.1 : ↥R₁) : G) * ((p.1.2 : ↥R₂) : G) = 1 := p.2
      have hqa : ((q.1.1 : ↥R₁) : G) * ((q.1.2 : ↥R₂) : G) = 1 := q.2
      have hcen : ∀ r : ↥μ.ker, ((r.1.1 : ↥R₁) : G) = 1 ∨ ((r.1.1 : ↥R₁) : G) = x ^ 4 := by
        intro r
        have hra : ((r.1.1 : ↥R₁) : G) * ((r.1.2 : ↥R₂) : G) = 1 := r.2
        have hmemR₂ : ((r.1.1 : ↥R₁) : G) ∈ R₂ := by
          have : ((r.1.1 : ↥R₁) : G) = (((r.1.2 : ↥R₂) : G))⁻¹ := eq_inv_of_mul_eq_one_left hra
          rw [this]
          exact R₂.inv_mem r.1.2.2
        refine h.1.eq_of_central r.1.1.2 ?_ ?_
        · exact hcomm x (Subgroup.subset_closure (Set.mem_insert _ _)) _ hmemR₂ |>.symm
        · exact hcomm y (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
            _ hmemR₂ |>.symm
      have hval : ((p.1.1 : ↥R₁) : G) = ((q.1.1 : ↥R₁) : G) := by
        rcases hcen p with hp | hp <;> rcases hcen q with hq | hq
        · rw [hp, hq]
        · exfalso
          have : f p = true := decide_eq_true hp
          have h2 : f q = false := by
            simp only [f, decide_eq_false_iff_not]
            rw [hq]; exact hx4
          rw [hpq] at this
          rw [this] at h2
          exact absurd h2 (by simp)
        · exfalso
          have : f q = true := decide_eq_true hq
          have h2 : f p = false := by
            simp only [f, decide_eq_false_iff_not]
            rw [hp]; exact hx4
          rw [← hpq] at this
          rw [this] at h2
          exact absurd h2 (by simp)
        · rw [hp, hq]
      have hb : ((p.1.2 : ↥R₂) : G) = ((q.1.2 : ↥R₂) : G) := by
        have e1 : ((p.1.2 : ↥R₂) : G) = (((p.1.1 : ↥R₁) : G))⁻¹ := eq_inv_of_mul_eq_one_right hpa
        have e2 : ((q.1.2 : ↥R₂) : G) = (((q.1.1 : ↥R₁) : G))⁻¹ := eq_inv_of_mul_eq_one_right hqa
        rw [e1, e2, hval]
      apply Subtype.ext
      apply Prod.ext
      · exact Subtype.ext hval
      · exact Subtype.ext hb
    calc Nat.card μ.ker ≤ Nat.card Bool := Nat.card_le_card_of_injective f hinj
      _ = 2 := by simp
  have hprod : 256 ≤ Nat.card (↥R₁ × ↥R₂) := by
    rw [Nat.card_prod]
    exact Nat.mul_le_mul h.1.card_closure_ge h.2.1.card_closure_ge
  have hkr := Subgroup.card_ker_mul_card_range μ
  rw [hrange] at hkr
  have h2 : Nat.card μ.ker * Nat.card ↥(R₁ ⊔ R₂) ≤ 2 * Nat.card ↥(R₁ ⊔ R₂) :=
    Nat.mul_le_mul_right _ hker
  omega

@[expose] def Q16Q16.group (x y x' y' : G) : Subgroup G :=
  Subgroup.closure ({x, y} : Set G) ⊔ Subgroup.closure ({x', y'} : Set G)

theorem Q16Q16.mem_group_left {x y x' y' : G} {g : G} (hg : g ∈ Subgroup.closure ({x, y} : Set G)) :
    g ∈ Q16Q16.group x y x' y' := Subgroup.mem_sup_left hg

theorem Q16Q16.mem_group_right {x y x' y' : G} {g : G}
    (hg : g ∈ Subgroup.closure ({x', y'} : Set G)) : g ∈ Q16Q16.group x y x' y' :=
  Subgroup.mem_sup_right hg

theorem card_le_two_of_cyclic_exponent_two {P : Type*} [Group P] [Finite P] [IsCyclic P]
    (h : ∀ p : P, p ^ 2 = 1) : Nat.card P ≤ 2 := by
  classical
  haveI := Fintype.ofFinite P
  have h1 := IsCyclic.card_pow_eq_one_le (α := P) (n := 2) (by norm_num)
  have h2 : (Finset.univ.filter fun a : P => a ^ 2 = 1) = Finset.univ := by
    ext a
    simp [h a]
  rw [h2, Finset.card_univ, ← Nat.card_eq_fintype_card] at h1
  exact h1

theorem Q16Q16.image_sq_eq_one {x y x' y' : G} (h : Q16Q16 x y x' y') (N : Subgroup G) [N.Normal]
    (hcyc : IsCyclic ↥((Q16Q16.group x y x' y').map (QuotientGroup.mk' N))) :
    ∀ g ∈ Q16Q16.group x y x' y', (QuotientGroup.mk' N g) ^ 2 = 1 := by
  set ψ := QuotientGroup.mk' N with hψ
  set Q := Q16Q16.group x y x' y' with hQ
  have hcomm : ∀ a ∈ Q, ∀ b ∈ Q, ψ a * ψ b = ψ b * ψ a := by
    intro a ha b hb
    have := (IsCyclic.commGroup (α := ↥(Q.map ψ))).mul_comm
      ⟨ψ a, Subgroup.mem_map_of_mem _ ha⟩ ⟨ψ b, Subgroup.mem_map_of_mem _ hb⟩
    exact congrArg Subtype.val this
  have hpair : ∀ u v : G, Q16Pair u v → u ∈ Q → v ∈ Q → ψ u ^ 2 = 1 ∧ ψ v ^ 2 = 1 := by
    intro u v huv hu hv
    obtain ⟨h4, h8, hv2, huv'⟩ := huv
    have h1 : ψ u = (ψ u)⁻¹ := by
      have := congrArg ψ huv'
      rw [map_mul, map_mul, map_inv, hcomm v hv u hu, mul_assoc, mul_inv_cancel, mul_one] at this
      exact this
    refine ⟨?_, ?_⟩
    · rw [pow_two]
      exact mul_eq_one_iff_eq_inv.2 h1
    · have h2 : ψ u ^ 2 = 1 := by
        rw [pow_two]
        exact mul_eq_one_iff_eq_inv.2 h1
      calc ψ v ^ 2 = ψ (v ^ 2) := (map_pow ψ v 2).symm
        _ = ψ (u ^ 4) := by rw [hv2]
        _ = (ψ u ^ 2) ^ 2 := by rw [map_pow, ← pow_mul]
        _ = 1 := by rw [h2, one_pow]
  have hx : ψ x ^ 2 = 1 ∧ ψ y ^ 2 = 1 :=
    hpair x y h.1 (Q16Q16.mem_group_left (Subgroup.subset_closure (Set.mem_insert _ _)))
      (Q16Q16.mem_group_left (Subgroup.subset_closure
        (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
  have hx' : ψ x' ^ 2 = 1 ∧ ψ y' ^ 2 = 1 :=
    hpair x' y' h.2.1 (Q16Q16.mem_group_right (Subgroup.subset_closure (Set.mem_insert _ _)))
      (Q16Q16.mem_group_right (Subgroup.subset_closure
        (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
  have hmul : ∀ a ∈ Q, ∀ b ∈ Q, ψ a ^ 2 = 1 → ψ b ^ 2 = 1 → ψ (a * b) ^ 2 = 1 := by
    intro a ha b hb h1 h2
    rw [map_mul, Commute.mul_pow (hcomm a ha b hb), h1, h2, one_mul]
  have hQc : Q = Subgroup.closure (({x, y} : Set G) ∪ {x', y'}) :=
    (Subgroup.closure_union _ _).symm
  have key : ∀ g ∈ Subgroup.closure (({x, y} : Set G) ∪ {x', y'}), ψ g ^ 2 = 1 := by
    intro g hg'
    induction hg' using Subgroup.closure_induction with
    | mem a ha =>
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with (rfl | rfl) | (rfl | rfl)
      · exact hx.1
      · exact hx.2
      · exact hx'.1
      · exact hx'.2
    | one => simp
    | mul a b ha hb iha ihb =>
      exact hmul a (hQc ▸ ha) b (hQc ▸ hb) iha ihb
    | inv a ha iha =>
      rw [map_inv, inv_pow, iha, inv_one]
  intro g hg
  exact key g (hQc ▸ hg)

theorem Q16Q16.card_image_le_two [Finite G] {x y x' y' : G} (h : Q16Q16 x y x' y')
    (N : Subgroup G) [N.Normal]
    (hcyc : IsCyclic ↥((Q16Q16.group x y x' y').map (QuotientGroup.mk' N))) :
    Nat.card ↥((Q16Q16.group x y x' y').map (QuotientGroup.mk' N)) ≤ 2 := by
  haveI := hcyc
  haveI : Finite ↥((Q16Q16.group x y x' y').map (QuotientGroup.mk' N)) := inferInstance
  refine card_le_two_of_cyclic_exponent_two fun p => ?_
  obtain ⟨p, g, hg, rfl⟩ := p
  exact Subtype.ext (by simpa using h.image_sq_eq_one N hcyc g hg)

theorem Q16Q16.mul_mem_of_cyclic [Finite G] {x y x' y' : G} (h : Q16Q16 x y x' y')
    (N : Subgroup G) [N.Normal]
    (hcyc : IsCyclic ↥((Q16Q16.group x y x' y').map (QuotientGroup.mk' N))) :
    ∀ a ∈ Q16Q16.group x y x' y', ∀ b ∈ Q16Q16.group x y x' y', a ∉ N → b ∉ N → a * b ∈ N := by
  intro a ha b hb haN hbN
  have h2 := h.card_image_le_two N hcyc
  have hsa := h.image_sq_eq_one N hcyc a ha
  have hsb := h.image_sq_eq_one N hcyc b hb
  have ha1 : QuotientGroup.mk' N a ≠ 1 := fun h1 => haN ((QuotientGroup.eq_one_iff a).1 h1)
  have hb1 : QuotientGroup.mk' N b ≠ 1 := fun h1 => hbN ((QuotientGroup.eq_one_iff b).1 h1)
  let u : ↥((Q16Q16.group x y x' y').map (QuotientGroup.mk' N)) :=
    ⟨QuotientGroup.mk' N a, Subgroup.mem_map_of_mem _ ha⟩
  let v : ↥((Q16Q16.group x y x' y').map (QuotientGroup.mk' N)) :=
    ⟨QuotientGroup.mk' N b, Subgroup.mem_map_of_mem _ hb⟩
  have huv : QuotientGroup.mk' N a = QuotientGroup.mk' N b := by
    by_contra hne
    have hu1 : u ≠ 1 := fun h1 => ha1 (congrArg Subtype.val h1)
    have hv1 : v ≠ 1 := fun h1 => hb1 (congrArg Subtype.val h1)
    have huv' : u ≠ v := fun h1 => hne (congrArg Subtype.val h1)
    let f : Fin 3 → ↥((Q16Q16.group x y x' y').map (QuotientGroup.mk' N)) := ![1, u, v]
    have hf : Function.Injective f := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [f, eq_comm]
    have := Nat.card_le_card_of_injective f hf
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at this
    omega
  have h1 : QuotientGroup.mk' N (a * b) = 1 := by
    rw [map_mul, ← huv, ← pow_two]
    exact hsa
  exact (QuotientGroup.eq_one_iff (a * b)).1 h1

theorem Q16Q16.card_inf_ge [Finite G] {x y x' y' : G} (h : Q16Q16 x y x' y')
    (N : Subgroup G) [N.Normal]
    (hcyc : IsCyclic ↥((Q16Q16.group x y x' y').map (QuotientGroup.mk' N))) :
    64 ≤ Nat.card ↥(N ⊓ Q16Q16.group x y x' y') := by
  set Q := Q16Q16.group x y x' y' with hQ
  set f : ↥Q →* G ⧸ N := (QuotientGroup.mk' N).comp Q.subtype with hf
  have hker : f.ker = N.subgroupOf Q := by
    ext q
    simp [hf, MonoidHom.mem_ker, Subgroup.mem_subgroupOf, QuotientGroup.eq_one_iff]
  have hrange : f.range = Q.map (QuotientGroup.mk' N) := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  have hcard := Subgroup.card_ker_mul_card_range f
  rw [hker, hrange] at hcard
  have h2 := h.card_image_le_two N hcyc
  have h128 : 128 ≤ Nat.card ↥Q := h.card_ge
  have hinf : Nat.card ↥(N ⊓ Q) = Nat.card ↥(N.subgroupOf Q) := by
    rw [← Subgroup.subgroupOf_map_subtype N Q, Subgroup.card_map_of_injective Q.subtype_injective]
  rw [hinf]
  have h3 : Nat.card ↥(N.subgroupOf Q) * Nat.card ↥(Q.map (QuotientGroup.mk' N)) ≤
      Nat.card ↥(N.subgroupOf Q) * 2 := Nat.mul_le_mul_left _ h2
  omega

theorem orderOf_eq_eight_of_pow {g : G} (h4 : g ^ 4 ≠ 1) (h8 : g ^ 8 = 1) : orderOf g = 8 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := orderOf_eq_prime_pow (p := 2) (n := 2) (x := g) (by simpa using h4) (by simpa using h8)
  simpa using this

theorem Q16Q16.exists_orderOf_eight {x y x' y' : G} (h : Q16Q16 x y x' y') (N : Subgroup G)
    (hmul : ∀ a ∈ Q16Q16.group x y x' y', ∀ b ∈ Q16Q16.group x y x' y', a ∉ N → b ∉ N →
      a * b ∈ N) :
    ∃ g ∈ N, orderOf g = 8 := by
  obtain ⟨⟨hx4, hx8, hy2, hyx⟩, ⟨hx'4, hx'8, hy'2, hy'x'⟩, h44, hxx', hxy', hyx', hyy'⟩ := h
  have hq : Q16Q16 x y x' y' := ⟨⟨hx4, hx8, hy2, hyx⟩, ⟨hx'4, hx'8, hy'2, hy'x'⟩, h44, hxx', hxy',
    hyx', hyy'⟩
  have hxQ : x ∈ Q16Q16.group x y x' y' :=
    Q16Q16.mem_group_left (Subgroup.subset_closure (Set.mem_insert _ _))
  have hx'Q : x' ∈ Q16Q16.group x y x' y' :=
    Q16Q16.mem_group_right (Subgroup.subset_closure (Set.mem_insert _ _))
  have hy'Q : y' ∈ Q16Q16.group x y x' y' :=
    Q16Q16.mem_group_right (Subgroup.subset_closure
      (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  by_cases hxN : x ∈ N
  · exact ⟨x, hxN, orderOf_eq_eight_of_pow hx4 hx8⟩
  by_cases hy'N : y' ∈ N
  · by_cases hx'N : x' ∈ N
    · exact ⟨x', hx'N, orderOf_eq_eight_of_pow (by rw [← h44]; exact hx4) (by
        rw [show (8 : ℕ) = 4 * 2 by norm_num, pow_mul, ← h44, ← pow_mul]; exact hx8)⟩
    ·
      have hwN : y' * x' ∉ N := fun hw => hx'N (by
        have := N.mul_mem (N.inv_mem hy'N) hw
        simpa using this)
      have hwQ : y' * x' ∈ Q16Q16.group x y x' y' := (Q16Q16.group x y x' y').mul_mem hy'Q hx'Q
      have hg : x * (y' * x') ∈ N := hmul x hxQ (y' * x') hwQ hxN hwN
      have hyx2 : y' * x' = x'⁻¹ * y' := by
        have := congrArg (· * y') hy'x'
        simpa [mul_assoc] using this
      have hw2 : (y' * x') ^ 2 = x' ^ 4 := by
        have hy'' : y' * y' = x' ^ (4 : ℤ) := by rw [← pow_two, hy'2]; norm_cast
        calc (y' * x') ^ 2 = (y' * x') * (y' * x') := pow_two _
          _ = (x'⁻¹ * y') * (y' * x') := by rw [← hyx2]
          _ = x'⁻¹ * (y' * y') * x' := by group
          _ = x'⁻¹ * x' ^ (4 : ℤ) * x' := by rw [hy'']
          _ = x' ^ 4 := by group
      have hw4 : (y' * x') ^ 4 = 1 := by
        rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hw2, ← pow_mul]
        norm_num
        exact hx'8
      have hcomm : Commute x (y' * x') := (show Commute x y' from hxy').mul_right hxx'
      refine ⟨x * (y' * x'), hg, orderOf_eq_eight_of_pow ?_ ?_⟩
      · rw [hcomm.mul_pow, hw4, mul_one]
        exact hx4
      · rw [hcomm.mul_pow, show (8 : ℕ) = 4 * 2 by norm_num, pow_mul (y' * x'), hw4, one_pow,
          mul_one]
        exact hx8
  ·
    have hxyQ : x * y' ∈ Q16Q16.group x y x' y' := (Q16Q16.group x y x' y').mul_mem hxQ hy'Q
    have hg : x * y' ∈ N := hmul x hxQ y' hy'Q hxN hy'N
    have hy'4 : y' ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hy'2, ← pow_mul]
      exact hx'8
    have hcomm : Commute x y' := hxy'
    refine ⟨x * y', hg, orderOf_eq_eight_of_pow ?_ ?_⟩
    · rw [hcomm.mul_pow, hy'4, mul_one]
      exact hx4
    · rw [hcomm.mul_pow, show (8 : ℕ) = 4 * 2 by norm_num, pow_mul y', hy'4, one_pow, mul_one]
      exact hx8

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf
