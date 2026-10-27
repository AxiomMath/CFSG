module

public import CFSG.GroupTheory.FourGroupOddOrderIdentity

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

variable {G : Type*} [Group G]

private def kleinFourOfCommutingInvolutions (a b : G) (ha : a * a = 1) (hb : b * b = 1)
    (hab : Commute a b) : Subgroup G where
  carrier := {a * b, a, b, 1}
  one_mem' := by simp
  mul_mem' := by
    have hba : b * a = a * b := hab.eq.symm
    have ha_ab : a * (a * b) = b := by
      rw [← mul_assoc, ha, one_mul]
    have hb_ab : b * (a * b) = a := by
      rw [← mul_assoc, hba, mul_assoc, hb, mul_one]
    have hab_a : (a * b) * a = b := by
      rw [mul_assoc, hba, ha_ab]
    have hab_b : (a * b) * b = a := by
      rw [mul_assoc, hb, mul_one]
    have hab_sq : (a * b) * (a * b) = 1 := by
      rw [← mul_assoc, hab_a, hb]
    intro x y hx hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
    rcases hx with (rfl | rfl | rfl | rfl) <;>
      rcases hy with (rfl | rfl | rfl | rfl) <;>
      simp [ha, hb, hba, ha_ab, hb_ab, hab_a, hab_b, hab_sq]
  inv_mem' := by
    have ha_inv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
    have hb_inv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
    have hab_sq : (a * b) * (a * b) = 1 := by
      calc
        (a * b) * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hab.eq.symm]
        _ = 1 := by rw [← mul_assoc, ha, one_mul, hb]
    have hab_inv : (a * b)⁻¹ = a * b :=
      inv_eq_of_mul_eq_one_right hab_sq
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with (rfl | rfl | rfl | rfl) <;>
      simp [ha_inv, hb_inv, hab_inv]

private theorem isKleinFour_kleinFourOfCommutingInvolutions (a b : G) (ha : a * a = 1)
    (hb : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (habne : a ≠ b) (hab : Commute a b) :
    IsKleinFour (kleinFourOfCommutingInvolutions a b ha hb hab) := by
  let V := kleinFourOfCommutingInvolutions a b ha hb hab
  have hoa : orderOf a = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using ha) ha1
  have hob : orderOf b = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using hb) hb1
  have habnot : a * b ∉ ({a, b, 1} : Set G) :=
    mul_notMem_of_orderOf_eq_two hoa hob habne
  constructor
  · change Nat.card V = 4
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
    change ({a * b, a, b, 1} : Set G).ncard = 4
    simp [habnot, ha1, hb1, habne]
  · apply Nat.dvd_antisymm
    · apply Monoid.exponent_dvd_of_forall_pow_eq_one
      intro x
      rcases x with ⟨x, hx⟩
      apply Subtype.ext
      change x ^ 2 = 1
      change x ∈ ({a * b, a, b, 1} : Set G) at hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with (rfl | rfl | rfl | rfl)
      · calc
          (a * b) ^ 2 = a * (b * a) * b := by rw [pow_two]; group
          _ = a * (a * b) * b := by rw [hab.eq.symm]
          _ = 1 := by rw [← mul_assoc, ha, one_mul, hb]
      · simpa [pow_two] using ha
      · simpa [pow_two] using hb
      · simp
    · have haV : a ∈ V := by
        change a ∈ ({a * b, a, b, 1} : Set G)
        simp
      have hordV : orderOf (⟨a, haV⟩ : V) = 2 := by
        simpa [Subgroup.orderOf_mk] using hoa
      simpa [hordV] using
        (Monoid.order_dvd_exponent (⟨a, haV⟩ : V))

@[reducible]
private def conjActOfLeNormalizer (T K : Subgroup G)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) : MulDistribMulAction T K where
  smul t k := ⟨(t : G) * (k : G) * (t : G)⁻¹,
    (Subgroup.mem_normalizer_iff.mp (hTK t.2) (k : G)).1 k.2⟩
  one_smul k := Subtype.ext (by change (1 : G) * (k : G) * (1 : G)⁻¹ = (k : G); group)
  mul_smul s t k := Subtype.ext (by
    change (((s * t : T) : G)) * (k : G) * (((s * t : T) : G))⁻¹ =
      (s : G) * ((t : G) * (k : G) * (t : G)⁻¹) * (s : G)⁻¹
    simp only [Subgroup.coe_mul]
    group)
  smul_mul t k l := Subtype.ext (by
    change (t : G) * (((k : K) * (l : K) : K) : G) * (t : G)⁻¹ =
      ((t : G) * (k : G) * (t : G)⁻¹) * ((t : G) * (l : G) * (t : G)⁻¹)
    simp only [Subgroup.coe_mul]
    group)
  smul_one t := Subtype.ext (by change (t : G) * (1 : G) * (t : G)⁻¹ = (1 : G); group)

private theorem centralizer_singleton_one : Subgroup.centralizer ({1} : Set G) = ⊤ := by
  rw [Subgroup.centralizer_eq_top_iff_subset]
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact Subgroup.mem_center_iff.mpr (fun y => by simp)

private theorem centralizer_pair_one_left (b : G) :
    Subgroup.centralizer ({1, b} : Set G) = Subgroup.centralizer ({b} : Set G) := by
  apply le_antisymm
  · exact Subgroup.centralizer_le (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact Or.inr rfl)
  · intro g hg
    rw [Subgroup.mem_centralizer_iff] at hg ⊢
    rintro x (hx | hx)
    · rw [hx]; simp
    · rw [hx]; exact hg b rfl

private theorem centralizer_pair_one_right (a : G) :
    Subgroup.centralizer ({a, 1} : Set G) = Subgroup.centralizer ({a} : Set G) := by
  apply le_antisymm
  · exact Subgroup.centralizer_le (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact Or.inl rfl)
  · intro g hg
    rw [Subgroup.mem_centralizer_iff] at hg ⊢
    rintro x (hx | hx)
    · rw [hx]; exact hg a rfl
    · rw [hx]; simp

theorem card_mul_sq_eq_prod_of_klein {N : Subgroup G} [Finite N] (hodd : ¬ 2 ∣ Nat.card ↥N)
    {a u : G} (ha : a * a = 1) (hu : u * u = 1) (hau : a * u = u * a)
    (hNa : ∀ x ∈ N, a * x * a⁻¹ ∈ N) (hNu : ∀ x ∈ N, u * x * u⁻¹ ∈ N) :
    Nat.card ↥N * Nat.card ↥(N ⊓ Subgroup.centralizer ({a, u} : Set G)) ^ 2 =
      Nat.card ↥(N ⊓ Subgroup.centralizer ({a} : Set G)) *
        Nat.card ↥(N ⊓ Subgroup.centralizer ({u} : Set G)) *
        Nat.card ↥(N ⊓ Subgroup.centralizer ({a * u} : Set G)) := by
  classical
  have hNodd : Odd (Nat.card N) :=
    Nat.not_even_iff_odd.mp (by simpa [even_iff_two_dvd] using hodd)
  by_cases ha1 : a = 1
  · rw [ha1]
    rw [centralizer_pair_one_left u, centralizer_singleton_one, inf_top_eq,
      show (1 : G) * u = u by simp]
    ring
  by_cases hu1 : u = 1
  · rw [hu1]
    rw [centralizer_pair_one_right a, centralizer_singleton_one, inf_top_eq,
      show a * (1 : G) = a by simp]
    ring
  by_cases hne : a = u
  · rw [hne]
    have hc : Subgroup.centralizer ({u, u} : Set G) = Subgroup.centralizer ({u} : Set G) := by
      have hsu : ({u, u} : Set G) = ({u} : Set G) := by ext x; simp
      rw [hsu]
    rw [hc, show u * u = (1 : G) by exact hu, centralizer_singleton_one, inf_top_eq]
    ring
  have hcu : Commute a u := (commute_iff_eq a u).mpr hau
  let V : Subgroup G := Subgroup.closure ({a, u} : Set G)
  have haV : a ∈ V := Subgroup.subset_closure (by simp)
  have huV : u ∈ V := Subgroup.subset_closure (by simp)
  have haN : a ∈ Subgroup.normalizer (N : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hNa h, fun hh => ?_⟩
    have h2 : a * (a * h * a⁻¹) * a⁻¹ ∈ N := hNa _ hh
    have h1a : a * a = 1 := ha
    have hinv : a⁻¹ * a⁻¹ = 1 := by rw [← mul_inv_rev, ha, inv_one]
    have heq : a * (a * h * a⁻¹) * a⁻¹ = h := by
      calc a * (a * h * a⁻¹) * a⁻¹ = (a * a) * h * (a⁻¹ * a⁻¹) := by group
        _ = 1 * h * 1 := by rw [h1a, hinv]
        _ = h := by group
    rwa [heq] at h2
  have huN : u ∈ Subgroup.normalizer (N : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hNu h, fun hh => ?_⟩
    have h2 : u * (u * h * u⁻¹) * u⁻¹ ∈ N := hNu _ hh
    have h1u : u * u = 1 := hu
    have hinv : u⁻¹ * u⁻¹ = 1 := by rw [← mul_inv_rev, hu, inv_one]
    have heq : u * (u * h * u⁻¹) * u⁻¹ = h := by
      calc u * (u * h * u⁻¹) * u⁻¹ = (u * u) * h * (u⁻¹ * u⁻¹) := by group
        _ = 1 * h * 1 := by rw [h1u, hinv]
        _ = h := by group
    rwa [heq] at h2
  have hVN : V ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.closure_le _).mpr (by
      rintro x (hx | hx)
      · rw [hx]; exact haN
      · rw [hx]; exact huN)
  have hVK : IsKleinFour V := by
    have hVeq : V = kleinFourOfCommutingInvolutions a u ha hu hcu := by
      apply le_antisymm
      · refine (Subgroup.closure_le _).mpr ?_
        rintro x (hx | hx)
        · rw [hx]
          change a ∈ ({a * u, a, u, 1} : Set G)
          simp
        · rw [hx]
          change u ∈ ({a * u, a, u, 1} : Set G)
          simp
      · intro x hx
        change x ∈ ({a * u, a, u, 1} : Set G) at hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with hx | hx | hx | hx
        · rw [hx]
          exact V.mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
        · rw [hx]; exact Subgroup.subset_closure (by simp)
        · rw [hx]; exact Subgroup.subset_closure (by simp)
        · rw [hx]; exact V.one_mem
    rw [hVeq]
    exact isKleinFour_kleinFourOfCommutingInvolutions a u ha hu ha1 hu1 hne hcu
  haveI : IsKleinFour V := hVK
  haveI : Finite V := Nat.finite_of_card_ne_zero (by rw [hVK.card_four]; norm_num)
  haveI : Fintype V := Fintype.ofFinite V
  letI : MulDistribMulAction V N := conjActOfLeNormalizer V N hVN
  have hsmul : ∀ (v : V) (n : N),
      (((v • n : N) : G)) = (v : G) * (n : G) * (v : G)⁻¹ := by
    intro v n
    rfl
  have hfixV : fixedPointSubgroup V N =
      (N ⊓ Subgroup.centralizer ({a, u} : Set G)).subgroupOf N := by
    ext n
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
      FixedPoints.mem_subgroup]
    constructor
    · intro hn
      refine ⟨n.2, fun x hx => ?_⟩
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx
      · rw [hx]
        have h := congrArg Subtype.val (hn ⟨a, haV⟩)
        rw [hsmul] at h
        calc a * (n : G) = (a * (n : G) * a⁻¹) * a := by group
          _ = (n : G) * a := by rw [h]
      · rw [hx]
        have h := congrArg Subtype.val (hn ⟨u, huV⟩)
        rw [hsmul] at h
        calc u * (n : G) = (u * (n : G) * u⁻¹) * u := by group
          _ = (n : G) * u := by rw [h]
    · rintro ⟨-, hcomm⟩
      intro v
      apply Subtype.ext
      rw [hsmul]
      have hcent : (n : G) ∈ Subgroup.centralizer (V : Set G) := by
        rw [show (V : Set G) = (Subgroup.closure ({a, u} : Set G) : Set G) from rfl,
          Subgroup.centralizer_closure]
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with hx | hx
        · rw [hx]; exact hcomm a (by simp)
        · rw [hx]; exact hcomm u (by simp)
      calc (v : G) * (n : G) * (v : G)⁻¹ = ((n : G) * (v : G)) * (v : G)⁻¹ := by
            rw [Subgroup.mem_centralizer_iff.mp hcent v v.2]
        _ = (n : G) := by group
  have hcardFixV : Nat.card (fixedPointSubgroup V N) =
      Nat.card ↥(N ⊓ Subgroup.centralizer ({a, u} : Set G)) := by
    calc Nat.card (fixedPointSubgroup V N)
        = Nat.card ((N ⊓ Subgroup.centralizer ({a, u} : Set G)).subgroupOf N) := by rw [hfixV]
      _ = Nat.card ↥(N ⊓ Subgroup.centralizer ({a, u} : Set G)) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hmain : Nat.card N * Nat.card (fixedPointSubgroup V N) ^ 2 =
      ∏ t ∈ Finset.univ.erase (1 : V),
        Nat.card (fixedPointSubgroup (Subgroup.zpowers t) N) :=
    (CFSG.GroupTheory.odd_group_four_group_centralizer_order_identity
      (A := V) (X := N) hNodd).1
  have key : ∀ y : V, Nat.card (fixedPointSubgroup (Subgroup.zpowers y) N) =
      Nat.card ↥(N ⊓ Subgroup.centralizer ({(y : G)} : Set G)) := by
    intro y
    have hfix : fixedPointSubgroup (Subgroup.zpowers y) N =
        (N ⊓ Subgroup.centralizer ({(y : G)} : Set G)).subgroupOf N := by
      ext n
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
        CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff]
      constructor
      · intro hn
        refine ⟨n.2, fun x hx => ?_⟩
        rw [Set.mem_singleton_iff] at hx
        rw [hx]
        have h := congrArg Subtype.val hn
        rw [hsmul] at h
        calc (y : G) * (n : G) = ((y : G) * (n : G) * (y : G)⁻¹) * (y : G) := by group
          _ = (n : G) * (y : G) := by rw [h]
      · rintro ⟨-, hcomm⟩
        apply Subtype.ext
        rw [hsmul]
        calc (y : G) * (n : G) * (y : G)⁻¹ = ((n : G) * (y : G)) * (y : G)⁻¹ := by
              rw [hcomm (y : G) (by simp)]
          _ = (n : G) := by group
    calc Nat.card (fixedPointSubgroup (Subgroup.zpowers y) N)
        = Nat.card ((N ⊓ Subgroup.centralizer ({(y : G)} : Set G)).subgroupOf N) := by
          rw [hfix]
      _ = Nat.card ↥(N ⊓ Subgroup.centralizer ({(y : G)} : Set G)) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  set ta : V := ⟨a, haV⟩ with hta_def
  set tu : V := ⟨u, huV⟩ with htu_def
  have hta : ta ≠ 1 := fun h => ha1 (by
    have h' : (⟨a, haV⟩ : V) = 1 := by rw [← hta_def]; exact h
    exact congrArg Subtype.val h')
  have htu : tu ≠ 1 := fun h => hu1 (by
    have h' : (⟨u, huV⟩ : V) = 1 := by rw [← htu_def]; exact h
    exact congrArg Subtype.val h')
  have htat : ta ≠ tu := fun h => hne (by
    have h' : (⟨a, haV⟩ : V) = ⟨u, huV⟩ := by rw [← hta_def, ← htu_def]; exact h
    exact congrArg Subtype.val h')
  have htu_inv : tu⁻¹ = tu := inv_eq_of_mul_eq_one_right (IsKleinFour.mul_self tu)
  have htau_ne1 : ta * tu ≠ 1 := by
    intro h
    have h' : ta = tu⁻¹ := mul_eq_one_iff_eq_inv.mp h
    exact htat (by rw [h', htu_inv])
  have hata : ta * tu ≠ ta := fun h =>
    htu (mul_left_cancel (by rw [mul_one]; exact h))
  have hatu : ta * tu ≠ tu := fun h =>
    hta (mul_right_cancel (by rw [one_mul]; exact h))
  have herase : Finset.univ.erase (1 : V) = {ta * tu, ta, tu} := by
    rw [← IsKleinFour.eq_finset_univ hta htu htat]
    ext x
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx1, hx | hx | hx | hx⟩
      · exact Or.inl hx
      · exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inr hx)
      · exact absurd hx hx1
    · rintro (hx | hx | hx)
      · rw [hx]; exact ⟨htau_ne1, Or.inl rfl⟩
      · rw [hx]; exact ⟨hta, Or.inr (Or.inl rfl)⟩
      · rw [hx]; exact ⟨htu, Or.inr (Or.inr (Or.inl rfl))⟩
  have hcoetau : ((ta * tu : V) : G) = a * u := by rw [hta_def, htu_def]; rfl
  have hcoea : ((ta : V) : G) = a := by rw [hta_def]
  have hcoeu : ((tu : V) : G) = u := by rw [htu_def]
  have h1 := hmain
  rw [herase, Finset.prod_insert (by simp [hata, hatu]),
    Finset.prod_insert (by simp [htat]), Finset.prod_singleton] at h1
  rw [key (ta * tu), key ta, key tu, hcoetau, hcoea, hcoeu] at h1
  rw [← hcardFixV, h1]
  ring

end CFSG.EvenSporadicStandard.HNRecog.Section3
