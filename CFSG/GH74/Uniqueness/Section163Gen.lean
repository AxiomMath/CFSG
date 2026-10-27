module

public import CFSG.GH74.Uniqueness.Section161
public import CFSG.GH74.Uniqueness.Section16Conf

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

section FourGroup

variable {X : Type*} [Group X]

@[expose] def fourSub (a b : X) (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    Subgroup X where
  carrier := {1, a, b, a * b}
  mul_mem' := by
    have h1 : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
    have h2 : b * a = a * b := hab.symm
    have h3 : b * (a * b) = a := by rw [← mul_assoc, ← hab, mul_assoc, hb, mul_one]
    have h4 : a * b * a = b := by rw [hab, mul_assoc, ha, mul_one]
    have h5 : a * b * b = a := by rw [mul_assoc, hb, mul_one]
    have h6 : a * b * (a * b) = 1 := by rw [← mul_assoc, h4, hb]
    rintro x y hx hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      simp [ha, hb, h1, h2, h3, h4, h5, h6]
  one_mem' := Set.mem_insert _ _
  inv_mem' := by
    have h6 : (a * b)⁻¹ = a * b := by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hb, hab]
    rintro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl | rfl | rfl
    · simp
    · simp [inv_eq_of_mul_eq_one_right ha]
    · simp [inv_eq_of_mul_eq_one_right hb]
    · simp [h6]

theorem mem_fourSub {a b : X} {ha : a * a = 1} {hb : b * b = 1} {hab : a * b = b * a} {x : X} :
    x ∈ fourSub a b ha hb hab ↔ x = 1 ∨ x = a ∨ x = b ∨ x = a * b := Iff.rfl

theorem card_fourSub [Finite X] {a b : X} {ha : a * a = 1} {hb : b * b = 1}
    {hab : a * b = b * a} (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) :
    Nat.card (fourSub a b ha hb hab) = 4 := by
  classical
  have hab1 : a * b ≠ 1 := fun h => hne (by
    have := congrArg (a * ·) h
    simp only [← mul_assoc, ha, one_mul, mul_one] at this
    exact this.symm)
  have haab : a ≠ a * b := fun h => hb1 (by
    have := congrArg (a⁻¹ * ·) h
    simpa using this.symm)
  have hbab : b ≠ a * b := fun h => ha1 (by
    have h' : b * 1 = a * b := by rw [mul_one]; exact h
    rw [hab] at h'
    exact (mul_left_cancel h').symm)
  have e : Nat.card ↥(fourSub a b ha hb hab) = Nat.card (({1, a, b, a * b} : Set X)) := rfl
  rw [e, Nat.card_coe_set_eq, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
    Set.ncard_pair hbab]
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hne, haab⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨Ne.symm ha1, Ne.symm hb1, Ne.symm hab1⟩

theorem mul_self_of_mem_fourSub {a b : X} {ha : a * a = 1} {hb : b * b = 1}
    {hab : a * b = b * a} : ∀ w ∈ fourSub a b ha hb hab, w * w = 1 := by
  intro w hw
  rcases hw with rfl | rfl | rfl | rfl
  · simp
  · exact ha
  · exact hb
  · rw [← mul_assoc, hab, mul_assoc b a a, ha, mul_one, hb]

theorem fourSub_le {a b : X} {ha : a * a = 1} {hb : b * b = 1} {hab : a * b = b * a}
    {H : Subgroup X} (haH : a ∈ H) (hbH : b ∈ H) : fourSub a b ha hb hab ≤ H := by
  intro w hw
  rcases hw with rfl | rfl | rfl | rfl
  · exact H.one_mem
  · exact haH
  · exact hbH
  · exact H.mul_mem haH hbH

end FourGroup

section Generation

variable {X : Type*} [Group X] [Finite X]

theorem le_of_inf_centralizer_le_of_four {N W K : Subgroup X} (hN : Odd (Nat.card N))
    (hW4 : Nat.card W = 4) (hW2 : ∀ w ∈ W, w * w = 1) (hWN : W ≤ normalizer (N : Set X))
    (hK : ∀ w ∈ W, w ≠ 1 → centralizer ({w} : Set X) ⊓ N ≤ K) : N ≤ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : MulDistribMulAction ↥W ↥N := MulDistribMulAction.compHom ↥N (Subgroup.inclusion hWN)
  have hsmul : ∀ (a : ↥W) (y : ↥N), ((a • y : ↥N) : X) = a * y * (a : X)⁻¹ := fun _ _ => rfl
  have hWinv : ∀ a : ↥W, a⁻¹ = a := fun a => inv_eq_of_mul_eq_one_right (Subtype.ext (hW2 a a.2))
  have : CFSG.IsElementaryAbelian 2 ↥W :=
    { toIsMulCommutative := ⟨⟨fun a b => by
        calc a * b = (a * b)⁻¹ := (hWinv _).symm
          _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
          _ = b * a := by rw [hWinv, hWinv]⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a => by
        rw [sq]
        exact Subtype.ext (hW2 a a.2) }
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (p := 2) (A := ↥W) (H := ↥N)
    (by rw [hW4]; norm_num) (fun h => (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr h))
  have hmap := congrArg (Subgroup.map N.subtype) hgen
  simp only [Subgroup.map_iSup, map_fixedPointSubgroup_conj hsmul, map_subtype_top] at hmap
  rw [← hmap]
  exact iSup₂_le fun a ha => hK a a.2 (fun h => ha (Subtype.ext h))

omit [Finite X] in
theorem IsZStarIn.exists_mul_centralizer {A : Subgroup X} {z : X} (hz : z * z = 1)
    (h : IsZStarIn A z) :
    ∃ N : Subgroup X, N ≤ A ∧ A ≤ normalizer (N : Set X) ∧ Odd (Nat.card N) ∧
      ∀ a ∈ A, ∃ k ∈ N, ∃ c ∈ A ⊓ centralizer ({z} : Set X), a = k * c := by
  obtain ⟨-, N, hNA, hNn, hNodd, hN⟩ := h
  refine ⟨N, hNA, (Subgroup.normal_subgroupOf_iff_le_normalizer hNA).mp hNn, hNodd,
    fun a ha => ?_⟩
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  set n₀ := a * z * a⁻¹ * z⁻¹ with hn₀
  have hn₀N : n₀ ∈ N := hN a ha
  have hzz : z⁻¹ * z⁻¹ = 1 := by rw [← mul_inv_rev, hz, inv_one]
  have hinv : z * n₀ * z⁻¹ = n₀⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    calc z * n₀ * z⁻¹ * n₀ = z * a * z * a⁻¹ * (z⁻¹ * z⁻¹) * a * z * a⁻¹ * z⁻¹ := by
          rw [hn₀]; group
      _ = z * a * (z * z) * a⁻¹ * z⁻¹ := by rw [hzz]; group
      _ = 1 := by rw [hz]; group
  have hodd : Odd (orderOf n₀) := by
    have h1 := orderOf_dvd_natCard (⟨n₀, hn₀N⟩ : N)
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat hNodd h1
  obtain ⟨j, hj⟩ := Bender.exists_sq_eq_of_odd_orderOf hodd
  set k := n₀ ^ j with hk
  have hkN : k ∈ N := N.pow_mem hn₀N j
  have hzk : z * k⁻¹ * z⁻¹ = k := by
    have h1 : z * k * z⁻¹ = k⁻¹ := by rw [hk, ← conj_pow, hinv, inv_pow]
    calc z * k⁻¹ * z⁻¹ = (z * k * z⁻¹)⁻¹ := by group
      _ = k := by rw [h1, inv_inv]
  have hconj : k * z * k⁻¹ = a * z * a⁻¹ := by
    calc k * z * k⁻¹ = k * (z * k⁻¹ * z⁻¹) * z := by group
      _ = k * k * z := by rw [hzk]
      _ = n₀ * z := by rw [hk, hj]
      _ = a * z * a⁻¹ := by rw [hn₀]; group
  refine ⟨k, hkN, k⁻¹ * a, Subgroup.mem_inf.mpr ⟨A.mul_mem (A.inv_mem (hNA hkN)) ha, ?_⟩,
    by group⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc k⁻¹ * a * z = k⁻¹ * (a * z * a⁻¹) * a := by group
    _ = k⁻¹ * (k * z * k⁻¹) * a := by rw [hconj]
    _ = z * (k⁻¹ * a) := by group

theorem exists_mem_normalizer_not_mem_of_ne {p : ℕ} [Fact p.Prime] {V S : Subgroup X}
    (hS : IsPGroup p S) (hVS : V ≤ S) (hne : V ≠ S) :
    ∃ s ∈ S, s ∈ normalizer (V : Set X) ∧ s ∉ V := by
  have : Group.IsNilpotent S := hS.isNilpotent
  have hlt : V.subgroupOf S < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hne
    apply le_antisymm hVS
    intro x hx
    have : (⟨x, hx⟩ : S) ∈ V.subgroupOf S := htop ▸ Subgroup.mem_top _
    exact this
  have hnorm := Group.normalizerCondition_of_isNilpotent (G := S) _ hlt
  obtain ⟨s, hsN, hsV⟩ := IsConcreteLE.exists_of_lt hnorm
  refine ⟨s, s.2, ?_, hsV⟩
  rw [Subgroup.mem_normalizer_iff]
  intro v
  constructor
  · intro hv
    exact (Subgroup.mem_normalizer_iff.mp hsN ⟨v, hVS hv⟩).mp hv
  · intro hv
    have hvS : v ∈ S := by
      have := S.mul_mem (S.mul_mem (S.inv_mem s.2) (hVS hv)) s.2
      simpa [mul_assoc] using this
    exact (Subgroup.mem_normalizer_iff.mp hsN ⟨v, hvS⟩).mpr hv

theorem exists_conjugate_le_of_isSylowOf {p : ℕ} [Fact p.Prime] {P K E : Subgroup X}
    (hP : ABGLocalTools.IsSylowOf p P K) (hEK : E ≤ K) (hE : IsPGroup p E) :
    ∃ g ∈ K, conjugate E g ≤ P := by
  obtain ⟨Q₀, rfl⟩ := hP
  have hE' : IsPGroup p (E.subgroupOf K) := hE.comap_subtype
  obtain ⟨Q, hQ⟩ := hE'.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K Q Q₀
  refine ⟨(k : X)⁻¹, K.inv_mem k.2, fun y hy => ?_⟩
  rw [mem_conjugate_iff, inv_inv] at hy
  have hmem : (k : X)⁻¹ * y * k ∈ (Q : Subgroup K).map K.subtype :=
    ⟨⟨_, hEK hy⟩, hQ (Subgroup.mem_subgroupOf.mpr hy), rfl⟩
  have h2 := mem_map_smul Q k hmem
  rw [hk] at h2
  convert h2 using 1
  group

theorem exists_commute_ne_of_four {P V : Subgroup X} (hP : IsPGroup 2 P) {u : X} (huP : u ∈ P)
    (hu2 : orderOf u = 2) (hVP : V ≤ P) (hV4 : Nat.card V = 4) (hV2 : ∀ v ∈ V, v * v = 1) :
    ∃ v ∈ P, v * v = 1 ∧ v ≠ 1 ∧ v ≠ u ∧ u * v = v * u := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu1 : u ≠ 1 := fun h => by rw [h, orderOf_one] at hu2; omega
  have huu : u * u = 1 := by rw [← sq, ← hu2, pow_orderOf_eq_one]
  have hnt : Nontrivial ↥P := ⟨⟨⟨u, huP⟩, 1, fun h => hu1 (congrArg Subtype.val h)⟩⟩
  have hZnt : Nontrivial (center ↥P) := hP.center_nontrivial
  have h2 : 2 ∣ Nat.card (center ↥P) := by
    obtain ⟨k, hk⟩ := (hP.to_subgroup (center ↥P)).exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact (Finite.one_lt_card_iff_nontrivial.mpr hZnt).ne' hk
    rw [hk]
    exact dvd_pow_self 2 hk0
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 2 h2
  set v₀ : X := ((c : ↥P) : X) with hv₀
  have hv₀P : v₀ ∈ P := (c : ↥P).2
  have hv₀2 : orderOf v₀ = 2 := by
    rw [hv₀, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hc]
  have hv₀v₀ : v₀ * v₀ = 1 := by rw [← sq, ← hv₀2, pow_orderOf_eq_one]
  have hv₀1 : v₀ ≠ 1 := fun h => by rw [h, orderOf_one] at hv₀2; omega
  have hv₀c : ∀ y ∈ P, y * v₀ = v₀ * y := fun y hy =>
    congrArg Subtype.val ((Subgroup.mem_center_iff.mp c.2) ⟨y, hy⟩)
  by_cases hne : v₀ = u
  ·
    obtain ⟨v, hvV, hv1, hvu⟩ : ∃ v ∈ V, v ≠ 1 ∧ v ≠ u := by
      by_contra hcon
      push Not at hcon
      have hsub : (V : Set X) ⊆ ({1, u} : Set X) := fun v hv => by
        by_cases hv1 : v = 1
        · exact Or.inl hv1
        · exact Or.inr (hcon v hv hv1)
      have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [← Nat.card_coe_set_eq, show Nat.card (V : Set X) = Nat.card V from rfl, hV4] at hle
      have := Set.ncard_insert_le (1 : X) ({u} : Set X)
      rw [Set.ncard_singleton] at this
      omega
    refine ⟨v, hVP hvV, hV2 v hvV, hv1, hvu, ?_⟩
    rw [← hne]
    exact (hv₀c v (hVP hvV)).symm
  · exact ⟨v₀, hv₀P, hv₀v₀, hv₀1, hne, hv₀c u huP⟩

end Generation

section Sylow31

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem IsProductDisconnected.isSylowOf_of_mem (h : IsProductDisconnected Z M)
    {H T : Subgroup X} (hT : ABGLocalTools.IsSylowOf 2 T (H ⊓ M)) {z : X} (hz : z ∈ Z)
    (hzT : z ∈ T) : ABGLocalTools.IsSylowOf 2 T H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ H := hT.le.trans inf_le_left
  have hzM : z ∈ M := (Subgroup.mem_inf.mp (hT.le hzT)).2
  obtain ⟨S, hS, hTS⟩ := exists_isSylowOf_ge_of_le hTH hT.isPGroup
  by_cases heq : T = S
  · rw [heq]
    exact hS
  exfalso
  obtain ⟨s, hsS, hsN, hsT⟩ := exists_mem_normalizer_not_mem_of_ne hS.isPGroup hTS heq
  have hsH : s ∈ H := hS.le hsS
  have hsM : s ∈ M := by
    apply h.mem_of_conj_mem hz hzM
    have hsinv : s⁻¹ ∈ normalizer (T : Set X) := (normalizer (T : Set X)).inv_mem hsN
    have h1 := (Subgroup.mem_normalizer_iff.mp hsinv z).mp hzT
    rw [inv_inv] at h1
    exact (Subgroup.mem_inf.mp (hT.le h1)).2
  have hle : T ⊔ zpowers s ≤ H ⊓ M :=
    sup_le hT.le (zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hsH, hsM⟩))
  have hp : IsPGroup 2 (T ⊔ zpowers s : Subgroup X) :=
    hS.isPGroup.to_le (sup_le hTS (zpowers_le.mpr hsS))
  have heq' := hT.eq_of_le le_sup_left hle hp
  exact hsT (heq' ▸ mem_sup_right (mem_zpowers s))

end Sylow31

end CFSG.GH74.Uniqueness
