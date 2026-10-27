module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneDegreeEight

public section

namespace CFSG.SeitzReduction.RankOne.DegreeEight

open Equiv

@[expose] def mobPerm (a b c d a' b' c' d' : ZMod 7)
    (h1 : ∀ x, mob a' b' c' d' (mob a b c d x) = x)
    (h2 : ∀ x, mob a b c d (mob a' b' c' d' x) = x) : Perm (Option (ZMod 7)) :=
  ⟨mob a b c d, mob a' b' c' d', h1, h2⟩

@[expose] def d8Rho : Perm (Option (ZMod 7)) := mobPerm 2 2 5 2 2 5 2 2 (by decide) (by decide)

@[expose] def d8RhoInv : Perm (Option (ZMod 7)) :=
  mobPerm 2 5 2 2 2 2 5 2 (by decide) (by decide)

@[expose] def d8Inv₁ : Perm (Option (ZMod 7)) := invol (mob 2 3 3 5) (by decide)

@[expose] def d8Inv₂ : Perm (Option (ZMod 7)) := invol (mob 2 4 4 5) (by decide)

@[expose] def d8Inv₃ : Perm (Option (ZMod 7)) := invol (mob 3 2 2 4) (by decide)

@[expose] def d8Inv₄ : Perm (Option (ZMod 7)) := invol (mob 3 5 5 4) (by decide)

@[expose] def d8Conj₁ : Perm (Option (ZMod 7)) := mobPerm 0 2 3 1 1 5 4 0 (by decide) (by decide)

@[expose] def d8Conj₂ : Perm (Option (ZMod 7)) := mobPerm 1 3 2 0 0 4 5 1 (by decide) (by decide)

@[expose] def d8Conj₃ : Perm (Option (ZMod 7)) := mobPerm 2 1 1 1 1 6 6 2 (by decide) (by decide)

@[expose] def d8Conj₄ : Perm (Option (ZMod 7)) := mobPerm 1 1 1 2 2 6 6 1 (by decide) (by decide)

@[expose] def d8List : List (Perm (Option (ZMod 7))) :=
  [1, tPro6, d8Rho, d8RhoInv, d8Inv₁, d8Inv₂, d8Inv₃, d8Inv₄]

@[expose] def d8Check : Bool :=
  d8List.all fun x => (d8List.all fun y => d8List.contains (x * y)) && d8List.contains x⁻¹

theorem d8Check_eq_true : d8Check = true := by decide +kernel

theorem d8List_mul_mem : ∀ x ∈ d8List, ∀ y ∈ d8List, x * y ∈ d8List := by
  have h := d8Check_eq_true
  simp only [d8Check, List.all_eq_true, Bool.and_eq_true, List.contains_iff_mem] at h
  exact fun x hx y hy => (h x hx).1 y hy

theorem d8List_inv_mem : ∀ x ∈ d8List, x⁻¹ ∈ d8List := by
  have h := d8Check_eq_true
  simp only [d8Check, List.all_eq_true, Bool.and_eq_true, List.contains_iff_mem] at h
  exact fun x hx => (h x hx).2

@[expose] def d8 : Subgroup (Perm (Option (ZMod 7))) where
  carrier := {x | x ∈ d8List}
  one_mem' := List.mem_cons_self
  mul_mem' hx hy := d8List_mul_mem _ hx _ hy
  inv_mem' hx := d8List_inv_mem _ hx

theorem mem_d8 {x : Perm (Option (ZMod 7))} : x ∈ d8 ↔ x ∈ d8List := Iff.rfl

theorem d8List_nodup : d8List.Nodup := by decide +kernel

theorem card_d8 : Nat.card d8 = 8 := by
  have h1 : (d8 : Set (Perm (Option (ZMod 7)))) = ↑d8List.toFinset := by
    ext x; simp [mem_d8]
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, h1, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup d8List_nodup]
  rfl

@[expose] def d8CasesCheck : Bool := d8List.all fun x => x * x == 1 || x == d8Rho || x == d8RhoInv

theorem d8CasesCheck_eq_true : d8CasesCheck = true := by decide +kernel

theorem d8_cases {x : Perm (Option (ZMod 7))} (hx : x ∈ d8) :
    x * x = 1 ∨ x = d8Rho ∨ x = d8RhoInv := by
  have h := d8CasesCheck_eq_true
  simp only [d8CasesCheck, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  rcases h x (mem_d8.mp hx) with (h1 | h1) | h1
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h1)

theorem d8RhoInv_eq : d8RhoInv = d8Rho⁻¹ := by decide +kernel

theorem d8Rho_ne_one : d8Rho ≠ 1 := by decide +kernel

theorem d8Rho_mem_d8 : d8Rho ∈ d8 := mem_d8.mpr (by simp [d8List])

@[expose] def d8CommCheck : Bool := d8List.all fun x => x * tPro6 == tPro6 * x

theorem d8CommCheck_eq_true : d8CommCheck = true := by decide +kernel

theorem d8_commute_tPro6 {x : Perm (Option (ZMod 7))} (hx : x ∈ d8) :
    x * tPro6 = tPro6 * x := by
  have h := d8CommCheck_eq_true
  simp only [d8CommCheck, List.all_eq_true, beq_iff_eq] at h
  exact h x (mem_d8.mp hx)

@[expose] def d8ConjList : List (Perm (Option (ZMod 7))) := [1, d8Conj₁, d8Conj₂, d8Conj₃, d8Conj₄]

@[expose] def d8ConjCheck : Bool :=
  d8List.all fun x => !(x * x == 1) || x == 1 || d8ConjList.any fun c => c * tPro6 * c⁻¹ == x

theorem d8ConjCheck_eq_true : d8ConjCheck = true := by decide +kernel

theorem d8_involution_conj {x : Perm (Option (ZMod 7))} (hx : x ∈ d8) (hxx : x * x = 1)
    (hx1 : x ≠ 1) : ∃ c ∈ d8ConjList, c * tPro6 * c⁻¹ = x := by
  have h := d8ConjCheck_eq_true
  simp only [d8ConjCheck, List.all_eq_true, List.any_eq_true, Bool.or_eq_true, beq_iff_eq,
    Bool.not_eq_true', beq_eq_false_iff_ne] at h
  rcases h x (mem_d8.mp hx) with (h1 | h1) | h1
  · exact absurd hxx h1
  · exact absurd h1 hx1
  · exact h1

theorem d8Rho_mem_natPSL : d8Rho ∈ natPSL := mem_natPSL_of_mob 2 2 5 2 (by decide) (fun _ => rfl)

theorem d8RhoInv_mem_natPSL : d8RhoInv ∈ natPSL :=
  mem_natPSL_of_mob 2 5 2 2 (by decide) (fun _ => rfl)

theorem d8Inv₁_mem_natPSL : d8Inv₁ ∈ natPSL :=
  mem_natPSL_of_mob 2 3 3 5 (by decide) (fun _ => rfl)

theorem d8Inv₂_mem_natPSL : d8Inv₂ ∈ natPSL :=
  mem_natPSL_of_mob 2 4 4 5 (by decide) (fun _ => rfl)

theorem d8Inv₃_mem_natPSL : d8Inv₃ ∈ natPSL :=
  mem_natPSL_of_mob 3 2 2 4 (by decide) (fun _ => rfl)

theorem d8Inv₄_mem_natPSL : d8Inv₄ ∈ natPSL :=
  mem_natPSL_of_mob 3 5 5 4 (by decide) (fun _ => rfl)

theorem d8Conj₁_mem_natPSL : d8Conj₁ ∈ natPSL :=
  mem_natPSL_of_mob 0 2 3 1 (by decide) (fun _ => rfl)

theorem d8Conj₂_mem_natPSL : d8Conj₂ ∈ natPSL :=
  mem_natPSL_of_mob 1 3 2 0 (by decide) (fun _ => rfl)

theorem d8Conj₃_mem_natPSL : d8Conj₃ ∈ natPSL :=
  mem_natPSL_of_mob 2 1 1 1 (by decide) (fun _ => rfl)

theorem d8Conj₄_mem_natPSL : d8Conj₄ ∈ natPSL :=
  mem_natPSL_of_mob 1 1 1 2 (by decide) (fun _ => rfl)

theorem d8_le_natPSL : d8 ≤ natPSL := by
  intro x hx
  simp only [mem_d8, d8List, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact one_mem _
  · exact tPro6_mem_natPSL
  · exact d8Rho_mem_natPSL
  · exact d8RhoInv_mem_natPSL
  · exact d8Inv₁_mem_natPSL
  · exact d8Inv₂_mem_natPSL
  · exact d8Inv₃_mem_natPSL
  · exact d8Inv₄_mem_natPSL

theorem mem_natPSL_of_mem_d8ConjList {c : Perm (Option (ZMod 7))} (hc : c ∈ d8ConjList) :
    c ∈ natPSL := by
  simp only [d8ConjList, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · exact one_mem _
  · exact d8Conj₁_mem_natPSL
  · exact d8Conj₂_mem_natPSL
  · exact d8Conj₃_mem_natPSL
  · exact d8Conj₄_mem_natPSL

theorem exists_centralizing_of_mem_d8 {x : Perm (Option (ZMod 7))} (hx : x ∈ d8)
    (hxx : x * x = 1) :
    ∃ P : Subgroup (Perm (Option (ZMod 7))), P ≤ natPSL ∧ Nat.card P = 8 ∧
      ∀ y ∈ P, y * x = x * y := by
  by_cases hx1 : x = 1
  · subst hx1
    exact ⟨d8, d8_le_natPSL, card_d8, fun y _ => by rw [mul_one, one_mul]⟩
  obtain ⟨c, hc, hcx⟩ := d8_involution_conj hx hxx hx1
  have hcN : c ∈ natPSL := mem_natPSL_of_mem_d8ConjList hc
  refine ⟨d8.map (MulAut.conj c).toMonoidHom, ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact mul_mem (mul_mem hcN (d8_le_natPSL hy)) (inv_mem hcN)
  · rw [Subgroup.card_map_of_injective (MulAut.conj c).injective, card_d8]
  · rintro _ ⟨y, hy, rfl⟩
    have h1 := d8_commute_tPro6 hy
    rw [← hcx]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc c * y * c⁻¹ * (c * tPro6 * c⁻¹) = c * (y * tPro6) * c⁻¹ := by group
      _ = c * (tPro6 * y) * c⁻¹ := by rw [h1]
      _ = c * tPro6 * c⁻¹ * (c * y * c⁻¹) := by group

theorem natPSL_exists_apply_none (z : Option (ZMod 7)) : ∃ σ ∈ natPSL, σ none = z := by
  cases z with
  | none => exact ⟨1, one_mem _, rfl⟩
  | some k =>
    have h1 : ∀ k : ZMod 7, ∀ x, mob 0 1 6 k (mob k 6 1 0 x) = x := by decide
    have h2 : ∀ k : ZMod 7, ∀ x, mob k 6 1 0 (mob 0 1 6 k x) = x := by decide
    have h3 : ∀ k : ZMod 7, k * 0 - 6 * 1 = 1 := by decide
    have h4 : ∀ k : ZMod 7, mob k 6 1 0 none = some k := by decide
    exact ⟨⟨mob k 6 1 0, mob 0 1 6 k, h1 k, h2 k⟩,
      mem_natPSL_of_mob k 6 1 0 (h3 k) (fun _ => rfl), h4 k⟩

instance natPSL_isPretransitive : MulAction.IsPretransitive natPSL (Option (ZMod 7)) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨σ, hσ, hσx⟩ := natPSL_exists_apply_none x
  obtain ⟨τ, hτ, hτy⟩ := natPSL_exists_apply_none y
  refine ⟨⟨τ * σ⁻¹, mul_mem hτ (inv_mem hσ)⟩, ?_⟩
  change (τ * σ⁻¹) x = y
  rw [Perm.mul_apply, ← hσx, ← Perm.mul_apply σ⁻¹ σ, inv_mul_cancel, Perm.one_apply, hτy]

theorem card_stabilizer_natPSL (z : Option (ZMod 7)) :
    Nat.card (MulAction.stabilizer natPSL z) = 21 := by
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer natPSL z)
  rw [MulAction.index_stabilizer_of_transitive, card_natPSL] at h1
  have h8 : Nat.card (Option (ZMod 7)) = 8 := by rw [Nat.card_eq_fintype_card]; rfl
  rw [h8] at h1
  omega

theorem eq_one_of_mem_natPSL_of_fix' {σ : Perm (Option (ZMod 7))} (hσ : σ ∈ natPSL)
    {z : Option (ZMod 7)} (hz : σ z = z) {k : ℕ} (hk : σ ^ 2 ^ k = 1) : σ = 1 := by
  have hst : (⟨σ, hσ⟩ : natPSL) ∈ MulAction.stabilizer natPSL z := hz
  have h21 : orderOf (⟨σ, hσ⟩ : natPSL) ∣ 21 := by
    rw [← card_stabilizer_natPSL z]
    exact Subgroup.orderOf_dvd_natCard _ hst
  have h2k : orderOf (⟨σ, hσ⟩ : natPSL) ∣ 2 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    exact Subtype.ext (by simpa using hk)
  have hcop : Nat.Coprime 21 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  have h1 : orderOf (⟨σ, hσ⟩ : natPSL) = 1 :=
    Nat.dvd_one.mp (Nat.Coprime.gcd_eq_one hcop ▸ Nat.dvd_gcd h21 h2k)
  simpa using congrArg Subtype.val (orderOf_eq_one_iff.mp h1)

theorem eq_one_of_mem_natPSL_of_fix {σ : Perm (Option (ZMod 7))} (hσ : σ ∈ natPSL)
    {z : Option (ZMod 7)} (hz : σ z = z) (h4 : σ ^ 4 = 1) : σ = 1 :=
  eq_one_of_mem_natPSL_of_fix' hσ hz (k := 2) h4

theorem pow_four_of_mem_d8 {x : Perm (Option (ZMod 7))} (hx : x ∈ d8) : x ^ 4 = 1 := by
  rcases d8_cases hx with h | rfl | rfl
  · have h2 : x ^ 2 = 1 := by rw [sq]; exact h
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h2, one_pow]
  · decide +kernel
  · decide +kernel

theorem eq_d8_of_isPGroup {K : Subgroup (Perm (Option (ZMod 7)))} (hK : IsPGroup 2 K)
    (hKN : K ≤ natPSL) (hdK : d8 ≤ K) : K = d8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hK
  have hdvd : Nat.card K ∣ 168 := card_natPSL ▸ Subgroup.card_dvd_of_le hKN
  have hm3 : m ≤ 3 := by
    by_contra hm4
    push Not at hm4
    have h16 : 16 ∣ Nat.card K := hm ▸ (pow_dvd_pow 2 hm4 : 2 ^ 4 ∣ 2 ^ m)
    have := dvd_trans h16 hdvd
    norm_num at this
  have hle : Nat.card K ≤ Nat.card d8 := by
    rw [hm, card_d8]
    calc 2 ^ m ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hm3
      _ = 8 := rfl
  exact (Subgroup.eq_of_le_of_card_ge hdK hle).symm

theorem mem_d8_of_normalizes {g : Perm (Option (ZMod 7))} (hg : g ∈ natPSL)
    (h2 : ∃ k : ℕ, g ^ 2 ^ k = 1) (hn : g ∈ Subgroup.normalizer (d8 : Set _)) : g ∈ d8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz : IsPGroup 2 (Subgroup.zpowers g) := by
    obtain ⟨k, hk⟩ := h2
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hd : IsPGroup 2 d8 := IsPGroup.of_card (n := 3) (by rw [card_d8]; rfl)
  have hK := IsPGroup.to_sup_of_normal_right' hz hd (Subgroup.zpowers_le.mpr hn)
  have hKN : Subgroup.zpowers g ⊔ d8 ≤ natPSL := sup_le (Subgroup.zpowers_le.mpr hg) d8_le_natPSL
  rw [← eq_d8_of_isPGroup hK hKN le_sup_right]
  exact Subgroup.mem_sup_left (Subgroup.mem_zpowers g)

@[expose] def d8DblCheck : Bool :=
  d8List.all fun x => !(d8List.contains (dbl⁻¹ * x * dbl)) || x == 1

theorem d8DblCheck_eq_true : d8DblCheck = true := by decide +kernel

theorem eq_one_of_mem_d8_of_mem_conj {x : Perm (Option (ZMod 7))} (hx : x ∈ d8)
    (hx' : dbl⁻¹ * x * dbl ∈ d8) : x = 1 := by
  have h := d8DblCheck_eq_true
  simp only [d8DblCheck, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  rcases h x (mem_d8.mp hx) with h1 | h1
  · exfalso
    have h2 : d8List.contains (dbl⁻¹ * x * dbl) = true := List.contains_iff_mem.mpr hx'
    rw [h2] at h1
    exact absurd h1 (by decide)
  · exact h1

@[expose] noncomputable def d8Sylow : Sylow 2 natPSL :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  IsPGroup.toSylow (P := d8.subgroupOf natPSL)
    (IsPGroup.of_card (n := 3) (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe d8_le_natPSL).toEquiv, card_d8]; rfl))
    (by
      have h1 := Subgroup.card_mul_index (d8.subgroupOf natPSL)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe d8_le_natPSL).toEquiv, card_d8,
        card_natPSL] at h1
      have h21 : (d8.subgroupOf natPSL).index = 21 := by omega
      rw [h21]; decide)

theorem coe_d8Sylow : ((d8Sylow : Subgroup natPSL)) = d8.subgroupOf natPSL := rfl

theorem eq_bot_of_normal_of_fixedPointFree {E : Subgroup (Perm (Option (ZMod 7)))}
    (hEN : E ≤ natPSL) (hEn : ∀ g ∈ natPSL, ∀ e ∈ E, g * e * g⁻¹ ∈ E)
    (hfree : ∀ e ∈ E, ∀ z, e z = z → e = 1) : E = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E' : Subgroup natPSL := E.subgroupOf natPSL with hE'
  have hE'n : E'.Normal := ⟨fun x hx g => by
    rw [hE', Subgroup.mem_subgroupOf] at hx ⊢
    exact hEn g g.2 x hx⟩
  set K : Subgroup natPSL := MulAction.stabilizer natPSL (none : Option (ZMod 7)) with hK
  have hKcard : Nat.card K = 21 := card_stabilizer_natPSL none
  have hinf : E' ⊓ K = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxE, hxK⟩
    rw [Subgroup.mem_bot]
    exact Subtype.ext (hfree _ (Subgroup.mem_subgroupOf.mp hxE) none hxK)
  have h1 := Subgroup.relIndex_mul_card (H := E') (K := E' ⊔ K)
  rw [Subgroup.relIndex_sup_left, inf_eq_left.mpr le_sup_left] at h1
  have h2 := Subgroup.relIndex_mul_card (H := E') (K := K)
  rw [hinf, Subgroup.card_bot, mul_one, hKcard] at h2
  rw [h2] at h1
  have hdvd : Nat.card (E' ⊔ K : Subgroup natPSL) ∣ 168 :=
    card_natPSL ▸ Subgroup.card_subgroup_dvd_card _
  have hE8 : Nat.card E' ∣ 8 := by
    rw [← h1] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 21) (by simpa using hdvd)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (show Nat.card E' ∣ 2 ^ 3 from hE8)
  have hE2 : IsPGroup 2 E' := IsPGroup.of_card hj
  have h1 := hE2.le_sylow_of_normal d8Sylow
  set g0 : natPSL := ⟨dbl, dbl_mem_natPSL⟩
  have h2 := hE2.le_sylow_of_normal (g0 • d8Sylow)
  rw [eq_bot_iff]
  intro x hx
  have hxE' : (⟨x, hEN hx⟩ : natPSL) ∈ E' := Subgroup.mem_subgroupOf.mpr hx
  have hx1 := h1 hxE'
  have hx2 := h2 hxE'
  rw [coe_d8Sylow, Subgroup.mem_subgroupOf] at hx1
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, coe_d8Sylow] at hx2
  obtain ⟨y, hy, hyx⟩ := hx2
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hy
  have hyx1 :
      (g0 : Perm (Option (ZMod 7))) * (y : Perm (Option (ZMod 7))) * (g0 : Perm _)⁻¹ = x := by
    simpa [MulAut.conj_apply] using congrArg Subtype.val hyx
  have hyx' : (y : Perm (Option (ZMod 7))) = dbl⁻¹ * x * dbl := by
    rw [← hyx1]
    change (y : Perm (Option (ZMod 7))) = dbl⁻¹ * (dbl * (y : Perm _) * dbl⁻¹) * dbl
    group
  rw [Subgroup.mem_bot]
  exact eq_one_of_mem_d8_of_mem_conj hx1 (hyx' ▸ hy)

end CFSG.SeitzReduction.RankOne.DegreeEight
