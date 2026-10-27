module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup

theorem eq_one_of_conj_inv {G : Type*} [Group G] {c d y : G} (hc : y * c * y⁻¹ = c⁻¹)
    (hd : y * d * y⁻¹ = d⁻¹) (hy : y * (c * d) ^ 2 * y⁻¹ = (c * d) ^ 2)
    (hcu : c * (c * d) ^ 2 = (c * d) ^ 2 * c) (hodd : Odd (orderOf ((c * d) ^ 2))) :
    (c * d) ^ 2 = 1 := by
  have h1 : y * (c * d) ^ 2 * y⁻¹ = (c⁻¹ * d⁻¹) ^ 2 := by
    rw [← hc, ← hd]
    simp only [sq]
    group
  have h2 : (c⁻¹ * d⁻¹) ^ 2 = c⁻¹ * ((c * d) ^ 2)⁻¹ * c := by
    simp only [sq]
    group
  have hcom : Commute c ((c * d) ^ 2) := hcu
  have h3 : c⁻¹ * ((c * d) ^ 2)⁻¹ * c = ((c * d) ^ 2)⁻¹ := by
    rw [hcom.inv_inv.eq, inv_mul_cancel_right]
  have h4 : (c * d) ^ 2 = ((c * d) ^ 2)⁻¹ := by
    calc (c * d) ^ 2 = y * (c * d) ^ 2 * y⁻¹ := hy.symm
      _ = ((c * d) ^ 2)⁻¹ := by rw [h1, h2, h3]
  have h5 : ((c * d) ^ 2) ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 2 [h4]
    exact mul_inv_cancel _
  have h6 := orderOf_dvd_of_pow_eq_one h5
  have h7 : orderOf ((c * d) ^ 2) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h6 with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  exact orderOf_eq_one_iff.mp h7

theorem exists_fixed_of_card_eq_360 {α : Type*} [Fintype α] [DecidableEq α]
    (hα : Fintype.card α = 7) (H : Subgroup (Perm α)) [IsSimpleGroup ↥H]
    (hH : Nat.card H = 360) : ∃ p : α, ∀ h ∈ H, h p = p := by
  have hsize : ∀ x : α, (MulAction.orbit H x).ncard = 1 ∨ (MulAction.orbit H x).ncard = 6 := by
    intro x
    set S := MulAction.stabilizer H x
    have hk : S.index = (MulAction.orbit H x).ncard := MulAction.index_stabilizer H x
    have hdvd : S.index ∣ 360 := hH ▸ S.index_dvd_card
    have hle : (MulAction.orbit H x).ncard ≤ 7 := by
      rw [← hα, ← Nat.card_eq_fintype_card]
      exact Set.ncard_le_card _
    have hpos : 0 < S.index := Nat.pos_of_ne_zero (fun h => by simp [h] at hdvd)
    by_cases h1 : S.index = 1
    · left; rw [← hk, h1]
    by_cases h6 : S.index = 6
    · right; rw [← hk, h6]
    exfalso
    have hk7 : S.index ≠ 7 := fun h => by rw [h] at hdvd; norm_num at hdvd
    have hk5 : S.index ≤ 5 := by omega
    have hcore := S.normalCore_normal
    rcases hcore.eq_bot_or_eq_top with hb | ht
    · have h := S.index_normalCore_le_factorial_index
      rw [hb, index_bot, hH] at h
      have : Nat.factorial S.index ≤ Nat.factorial 5 := Nat.factorial_le hk5
      have : Nat.factorial 5 = 120 := by decide
      omega
    · have : S = ⊤ := top_le_iff.mp (ht ▸ S.normalCore_le)
      exact h1 (by rw [this, index_top])
  by_contra hno
  push Not at hno
  have hfix : ∀ x : α, (MulAction.orbit H x).ncard = 6 := by
    intro x
    rcases hsize x with h | h
    · exfalso
      obtain ⟨h₀, hh₀, hne⟩ := hno x
      have hx : x ∈ MulAction.orbit H x := MulAction.mem_orbit_self x
      have hy : (⟨h₀, hh₀⟩ : H) • x ∈ MulAction.orbit H x := MulAction.mem_orbit _ _
      obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp h
      rw [ha] at hx hy
      exact hne (hy.trans hx.symm)
    · exact h
  obtain ⟨x⟩ : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  have hlt : (MulAction.orbit H x).ncard < Nat.card α := by
    rw [hfix x, Nat.card_eq_fintype_card, hα]; norm_num
  obtain ⟨y, hy⟩ : ∃ y, y ∉ MulAction.orbit H x := by
    by_contra hall
    push Not at hall
    have : MulAction.orbit H x = Set.univ := Set.eq_univ_of_forall hall
    rw [this, Set.ncard_univ] at hlt
    exact lt_irrefl _ hlt
  have hdisj : Disjoint (MulAction.orbit H x) (MulAction.orbit H y) := by
    rw [Set.disjoint_left]
    intro z hzx hzy
    have e1 : MulAction.orbit H z = MulAction.orbit H x := MulAction.orbit_eq_iff.mpr hzx
    have e2 : MulAction.orbit H z = MulAction.orbit H y := MulAction.orbit_eq_iff.mpr hzy
    apply hy
    rw [← e1, e2]
    exact MulAction.mem_orbit_self y
  have hunion := Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)
  rw [hfix x, hfix y] at hunion
  have : (MulAction.orbit H x ∪ MulAction.orbit H y).ncard ≤ 7 := by
    rw [← hα, ← Nat.card_eq_fintype_card]
    exact Set.ncard_le_card _
  omega

theorem eq_zpow_mul_zpow_of_commute {α : Type*} [Fintype α] [DecidableEq α]
    {σ e₁ e₂ : Perm α} (h₁ : e₁.IsThreeCycle) (h₂ : e₂.IsThreeCycle)
    (hd : Disjoint e₁.support e₂.support)
    (hrest : ∀ x, x ∉ e₁.support → x ∉ e₂.support → σ x = x)
    (hc₁ : Commute σ e₁) (hc₂ : Commute σ e₂) : ∃ i j : ℤ, σ = e₁ ^ i * e₂ ^ j := by
  obtain ⟨hs₁, hm₁⟩ := (h₁.isCycle.commute_iff).mp hc₁
  obtain ⟨hs₂, hm₂⟩ := (h₂.isCycle.commute_iff).mp hc₂
  obtain ⟨i, hi⟩ := mem_zpowers_iff.mp hm₁
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hm₂
  have hσ₁ : ∀ x ∈ e₁.support, σ x = (e₁ ^ i) x := by
    intro x hx
    rw [hi, ofSubtype_apply_of_mem _ hx, subtypePerm_apply]
  have hσ₂ : ∀ x ∈ e₂.support, σ x = (e₂ ^ j) x := by
    intro x hx
    rw [hj, ofSubtype_apply_of_mem _ hx, subtypePerm_apply]
  refine ⟨i, j, Equiv.ext fun x => ?_⟩
  rw [Perm.mul_apply]
  by_cases hx₁ : x ∈ e₁.support
  · have hx₂ : x ∉ e₂.support := Finset.disjoint_left.mp hd hx₁
    rw [zpow_apply_eq_self_of_apply_eq_self (notMem_support.mp hx₂), hσ₁ x hx₁]
  · by_cases hx₂ : x ∈ e₂.support
    · have hy : (e₂ ^ j) x ∈ e₂.support := (zpow_apply_mem_support).mpr hx₂
      have hy₁ : (e₂ ^ j) x ∉ e₁.support := Finset.disjoint_right.mp hd hy
      rw [zpow_apply_eq_self_of_apply_eq_self (notMem_support.mp hy₁), hσ₂ x hx₂]
    · rw [zpow_apply_eq_self_of_apply_eq_self (notMem_support.mp hx₂),
        zpow_apply_eq_self_of_apply_eq_self (notMem_support.mp hx₁), hrest x hx₁ hx₂]

@[expose] def c5_234 : Perm (Fin 5) := swap 2 3 * swap 3 4

@[expose] def Good5 (ζ x : Perm (Fin 5)) : Prop :=
  x ^ 3 = 1 ∧ x ≠ 1 ∧ ζ * x * ζ⁻¹ = x⁻¹ ∧ (c5_234 * x) ^ 2 = 1 ∧ x ≠ c5_234⁻¹

instance (ζ x : Perm (Fin 5)) : Decidable (Good5 ζ x) := by unfold Good5; infer_instance

theorem sq_mul_eq_one_five_aux : ∀ ζ : Perm (Fin 5), ζ * c5_234 * ζ⁻¹ = c5_234⁻¹ →
    ∀ x : Perm (Fin 5), Good5 ζ x → ∀ x' : Perm (Fin 5), Good5 ζ x' → x' ≠ x → x' ≠ x⁻¹ →
      (x * x') ^ 2 = 1 := by
  decide +kernel

theorem isThreeCycle_of_pow_three_five {x : Perm (Fin 5)} (h3 : x ^ 3 = 1) (h1 : x ≠ 1) :
    x.IsThreeCycle := by
  have hord : orderOf x = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one h3) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) h1
    · exact h
  obtain ⟨k, hk⟩ := cycleType_prime_order (hord ▸ Nat.prime_three)
  rw [hord] at hk
  have hsum := sum_cycleType x
  have hle := Finset.card_le_univ x.support
  rw [hk, Multiset.sum_replicate, smul_eq_mul] at hsum
  simp only [Fintype.card_fin] at hle
  have hk0 : k = 0 := by omega
  rw [IsThreeCycle, hk, hk0]
  rfl

theorem sq_mul_eq_one_five {u ζ x x' : Perm (Fin 5)} (hu3 : u ^ 3 = 1) (hu1 : u ≠ 1)
    (hζu : ζ * u * ζ⁻¹ = u⁻¹)
    (hx : x ^ 3 = 1 ∧ x ≠ 1 ∧ ζ * x * ζ⁻¹ = x⁻¹ ∧ (u * x) ^ 2 = 1 ∧ x ≠ u⁻¹)
    (hx' : x' ^ 3 = 1 ∧ x' ≠ 1 ∧ ζ * x' * ζ⁻¹ = x'⁻¹ ∧ (u * x') ^ 2 = 1 ∧ x' ≠ u⁻¹)
    (h1 : x' ≠ x) (h2 : x' ≠ x⁻¹) : (x * x') ^ 2 = 1 := by
  have hc : c5_234.IsThreeCycle := card_support_eq_three_iff.mp (by decide)
  obtain ⟨τ, hτ⟩ : ∃ τ : Perm (Fin 5), τ * u * τ⁻¹ = c5_234 :=
    isConj_iff.mp (isConj_iff_cycleType_eq.mpr
      (Eq.trans (isThreeCycle_of_pow_three_five hu3 hu1) hc.symm))
  set f : MulAut (Perm (Fin 5)) := MulAut.conj τ with hfdef
  have hfu : f u = c5_234 := by rw [hfdef, MulAut.conj_apply, hτ]
  have tr : ∀ a : Perm (Fin 5),
      (a ^ 3 = 1 ∧ a ≠ 1 ∧ ζ * a * ζ⁻¹ = a⁻¹ ∧ (u * a) ^ 2 = 1 ∧ a ≠ u⁻¹) →
        Good5 (f ζ) (f a) := by
    rintro a ⟨e1, e2, e3, e4, e5⟩
    refine ⟨by rw [← map_pow, e1, map_one], fun h => e2 (f.injective (by rw [h, map_one])),
      by rw [← map_inv, ← map_mul, ← map_mul, e3, map_inv],
      by rw [← hfu, ← map_mul, ← map_pow, e4, map_one],
      fun h => e5 (f.injective (by rw [h, map_inv, hfu]))⟩
  have hζ' : f ζ * c5_234 * (f ζ)⁻¹ = c5_234⁻¹ := by
    rw [← hfu, ← map_inv, ← map_mul, ← map_mul, hζu, map_inv]
  have key := sq_mul_eq_one_five_aux (f ζ) hζ' (f x) (tr x hx) (f x') (tr x' hx')
    (fun h => h1 (f.injective h)) (fun h => h2 (f.injective (by rw [h, map_inv])))
  rw [← map_mul, ← map_pow] at key
  exact f.injective (by rw [key, map_one])

theorem exists_mem_normalizer_of_not_le {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P Y : Subgroup G} (hP : IsPGroup p P) (hYP : Y ≤ P) (hne : ¬ P ≤ Y) :
    ∃ a ∈ P, a ∈ normalizer (Y : Set G) ∧ a ∉ Y := by
  set I := Y.subgroupOf P with hI
  have hIlt : I < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hne fun x hx => ?_
    have : (⟨x, hx⟩ : P) ∈ I := by
      rw [htop]
      trivial
    exact mem_subgroupOf.mp this
  have : Group.IsNilpotent P := hP.isNilpotent
  have hlt := Group.normalizerCondition_of_isNilpotent (G := P) I hIlt
  obtain ⟨x, hxN, hxI⟩ := IsConcreteLE.exists_of_lt hlt
  have hxN' : (x : G) ∈ normalizer (Y : Set G) := by
    have : x ∈ (normalizer (Y : Set G)).subgroupOf P := by
      rw [subgroupOf_normalizer_eq hYP]
      exact hxN
    exact mem_subgroupOf.mp this
  exact ⟨x, x.2, hxN', fun hx => hxI (mem_subgroupOf.mpr hx)⟩

theorem exists_mem_ne_one_le_centralizer {G : Type*} [Group G] [Finite G] {V Q : Subgroup G}
    (hV : Nat.card V = 4) (hQ : IsPGroup 2 Q) (hQV : Q ≤ normalizer (V : Set G)) :
    ∃ s ∈ V, s ≠ 1 ∧ Q ≤ centralizer ({s} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : Q →* normalizer (V : Set G) := inclusion hQV
  let : MulAction Q V := MulAction.compHom V φ
  have hsmul : ∀ (q : Q) (v : V), ((q • v : V) : G) = (q : G) * v * (q : G)⁻¹ := fun q v => rfl
  have hmod := hQ.card_modEq_card_fixedPoints V
  rw [hV] at hmod
  have h1 : (1 : V) ∈ MulAction.fixedPoints Q V := fun q => by
    apply Subtype.ext
    rw [hsmul]
    simp
  have hge : 2 ≤ Nat.card (MulAction.fixedPoints Q V) := by
    have hpos : 0 < Nat.card (MulAction.fixedPoints Q V) :=
      Nat.card_pos_iff.mpr ⟨⟨⟨1, h1⟩⟩, inferInstance⟩
    have hev : Nat.card (MulAction.fixedPoints Q V) % 2 = 0 := by
      have := hmod.symm
      unfold Nat.ModEq at this
      omega
    omega
  obtain ⟨⟨s, hs⟩, hs1⟩ : ∃ s : MulAction.fixedPoints Q V, (s : V) ≠ 1 := by
    by_contra hall
    push Not at hall
    have : Nat.card (MulAction.fixedPoints Q V) ≤ 1 := by
      rw [Finite.card_le_one_iff_subsingleton]
      exact ⟨fun a b => Subtype.ext ((hall a).trans (hall b).symm)⟩
    omega
  refine ⟨s, s.2, fun h => hs1 (Subtype.ext h), fun q hq => ?_⟩
  have := congrArg Subtype.val (hs ⟨q, hq⟩)
  rw [hsmul] at this
  rw [mem_centralizer_singleton_iff]
  calc q * (s : G) = ((q : G) * s * q⁻¹) * q := by group
    _ = s * q := by rw [this]

end CFSG.ComponentClassification.RankTwoAlt
