module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Goldschmidt.Steps.G3bPSL2

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup

variable {G : Type} [Group G]

section Four

variable {V : Subgroup G}

theorem mul_self_of_isKleinFour (hV : IsKleinFour V) {v : G} (hv : v ∈ V) : v * v = 1 :=
  congrArg Subtype.val (@IsKleinFour.mul_self V _ hV ⟨v, hv⟩)

theorem commute_of_isKleinFour (hV : IsKleinFour V) {u v : G} (hu : u ∈ V) (hv : v ∈ V) :
    u * v = v * u :=
  congrArg Subtype.val (isMulCommutative_iff.mp (@IsKleinFour.isMulCommutative V _ hV)
    ⟨u, hu⟩ ⟨v, hv⟩)

theorem isPGroup_of_isKleinFour (hV : IsKleinFour V) : IsPGroup 2 V :=
  IsPGroup.of_card (n := 2) (by rw [@IsKleinFour.card_four V _ hV]; norm_num)

theorem orderOf_eq_two_of_isKleinFour (hV : IsKleinFour V) {v : G} (hv : v ∈ V) (hv1 : v ≠ 1) :
    orderOf v = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact mul_self_of_isKleinFour hV hv) hv1

theorem exists_mem_ne_of_isKleinFour (hV : IsKleinFour V) (u : G) :
    ∃ v ∈ V, v ≠ 1 ∧ v ≠ u := by
  by_contra h
  push Not at h
  have hsub : (V : Set G) ⊆ {1, u} := fun v hv => by
    by_cases hv1 : v = 1
    · exact Or.inl hv1
    · exact Or.inr (h v hv hv1)
  have h1 : Nat.card V ≤ 2 := by
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
    calc (V : Set G).ncard ≤ ({1, u} : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 2 := (Set.ncard_insert_le _ _).trans (by simp)
  rw [@IsKleinFour.card_four V _ hV] at h1
  omega

theorem mem_or_le_sup_of_isKleinFour (hV : IsKleinFour V) {v u : G} (hv : v ∈ V) (hv1 : v ≠ 1)
    (hu : u ∈ V) : u ∈ zpowers v ∨ V ≤ zpowers v ⊔ zpowers u := by
  by_cases h1 : u = 1
  · left
    rw [h1]
    exact one_mem _
  by_cases h2 : u = v
  · left
    rw [h2]
    exact mem_zpowers v
  right
  intro w hw
  by_cases hw1 : w = 1
  · rw [hw1]
    exact one_mem _
  by_cases hwv : w = v
  · rw [hwv]
    exact mem_sup_left (mem_zpowers v)
  by_cases hwu : w = u
  · rw [hwu]
    exact mem_sup_right (mem_zpowers u)
  have h := @IsKleinFour.eq_mul_of_ne_all V _ hV ⟨v, hv⟩ ⟨u, hu⟩ ⟨w, hw⟩
    (fun e => hv1 (congrArg Subtype.val e)) (fun e => h1 (congrArg Subtype.val e))
    (fun e => h2 (congrArg Subtype.val e).symm) (fun e => hw1 (congrArg Subtype.val e))
    (fun e => hwv (congrArg Subtype.val e)) (fun e => hwu (congrArg Subtype.val e))
  have hw' : w = v * u := congrArg Subtype.val h
  rw [hw']
  exact mul_mem (mem_sup_left (mem_zpowers v)) (mem_sup_right (mem_zpowers u))

end Four

theorem eq_one_or_eq_of_mem_zpowers {a x : G} (ha : orderOf a = 2) (hx : x ∈ zpowers a) :
    x = 1 ∨ x = a := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  rw [← zpow_mod_orderOf, ha]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    simp [h]
  · right
    simp [h]

theorem isKleinFour_sup {a b : G} (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : a ≠ b)
    (hc : a * b = b * a) : IsKleinFour (zpowers a ⊔ zpowers b : Subgroup G) := by
  have hnorm : zpowers b ≤ normalizer ((zpowers a : Subgroup G) : Set G) := by
    rw [zpowers_le]
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun w hw => by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
      exact (Commute.zpow_left hc k).eq)
  have hdisj : Disjoint (zpowers a) (zpowers b) := by
    rw [disjoint_iff, eq_bot_iff]
    intro x hx
    rw [mem_bot]
    rcases eq_one_or_eq_of_mem_zpowers ha hx.1 with h | h
    · exact h
    rcases eq_one_or_eq_of_mem_zpowers hb hx.2 with h' | h'
    · exact h'
    exact absurd (h.symm.trans h') hab
  have hcard : Nat.card (zpowers a ⊔ zpowers b : Subgroup G) = 4 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnorm hdisj,
      Nat.card_zpowers, Nat.card_zpowers, ha, hb]
  have hsq : ∀ x ∈ (zpowers a ⊔ zpowers b : Subgroup G), x * x = 1 := by
    intro x hx
    have hx' : x ∈ ((zpowers b ⊔ zpowers a : Subgroup G) : Set G) := by rwa [sup_comm]
    rw [coe_mul_of_left_le_normalizer_right _ _ hnorm] at hx'
    obtain ⟨y, hy, z, hz, rfl⟩ := hx'
    have hyz : y * z = z * y := by
      rcases eq_one_or_eq_of_mem_zpowers hb hy with rfl | rfl <;>
        rcases eq_one_or_eq_of_mem_zpowers ha hz with rfl | rfl <;> simp [hc]
    have hy2 : y * y = 1 := by
      rcases eq_one_or_eq_of_mem_zpowers hb hy with rfl | rfl
      · simp
      · rw [← pow_two, ← hb, pow_orderOf_eq_one]
    have hz2 : z * z = 1 := by
      rcases eq_one_or_eq_of_mem_zpowers ha hz with rfl | rfl
      · simp
      · rw [← pow_two, ← ha, pow_orderOf_eq_one]
    calc y * z * (y * z) = y * (z * y) * z := by group
      _ = y * y * (z * z) := by rw [← hyz]; group
      _ = 1 := by rw [hy2, hz2, one_mul]
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ha
    exact absurd ha (by norm_num)
  have : Nontrivial (zpowers a ⊔ zpowers b : Subgroup G) :=
    ⟨⟨⟨a, mem_sup_left (mem_zpowers a)⟩, 1, fun h => ha1 (congrArg Subtype.val h)⟩⟩
  refine ⟨hcard, (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr fun g hg => ?_⟩
  apply orderOf_eq_prime _ hg
  rw [pow_two]
  exact Subtype.ext (hsq g g.2)

structure FourPair (S₁ S₂ V₁ V₂ : Subgroup G) : Prop where
  le_left : V₁ ≤ S₁
  le_right : V₂ ≤ S₂
  four_left : IsKleinFour V₁
  four_right : IsKleinFour V₂
  comm : V₁ ≤ centralizer (V₂ : Set G)
  disj : V₁ ⊓ V₂ = ⊥

namespace FourPair

variable {S₁ S₂ V₁ V₂ : Subgroup G}

theorem of_le (hc : S₁ ≤ centralizer (S₂ : Set G)) (hd : S₁ ⊓ S₂ = ⊥) (h₁ : V₁ ≤ S₁)
    (h₂ : V₂ ≤ S₂) (hV₁ : IsKleinFour V₁) (hV₂ : IsKleinFour V₂) : FourPair S₁ S₂ V₁ V₂ :=
  ⟨h₁, h₂, hV₁, hV₂, h₁.trans (hc.trans (centralizer_le (SetLike.coe_subset_coe.mpr h₂))),
    le_bot_iff.mp (hd ▸ inf_le_inf h₁ h₂)⟩

variable (hp : FourPair S₁ S₂ V₁ V₂)
include hp

theorem symm : FourPair S₂ S₁ V₂ V₁ :=
  ⟨hp.le_right, hp.le_left, hp.four_right, hp.four_left, le_centralizer_iff.mp hp.comm,
    by rw [inf_comm]; exact hp.disj⟩

theorem commute {u v : G} (hu : u ∈ V₁) (hv : v ∈ V₂) : u * v = v * u :=
  (mem_centralizer_iff.mp (hp.comm hu) v hv).symm

theorem exists_mul {t : G} (ht : t ∈ V₁ ⊔ V₂) : ∃ u₁ ∈ V₁, ∃ u₂ ∈ V₂, t = u₁ * u₂ := by
  have hn : V₁ ≤ normalizer (V₂ : Set G) := hp.comm.trans (centralizer_le_normalizer _)
  have h : t ∈ ((V₁ ⊔ V₂ : Subgroup G) : Set G) := ht
  rw [coe_mul_of_left_le_normalizer_right _ _ hn] at h
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := h
  exact ⟨u₁, hu₁, u₂, hu₂, rfl⟩

theorem le_centralizer_left : V₁ ⊔ V₂ ≤ centralizer (V₁ : Set G) :=
  sup_le (fun _ hu => mem_centralizer_iff.mpr fun _ hv =>
      commute_of_isKleinFour hp.four_left hv hu)
    (le_centralizer_iff.mp hp.comm)

theorem le_centralizer_right : V₁ ⊔ V₂ ≤ centralizer (V₂ : Set G) :=
  sup_le hp.comm
    (fun _ hu => mem_centralizer_iff.mpr fun _ hv => commute_of_isKleinFour hp.four_right hv hu)

theorem le_centralizer_sup : V₁ ⊔ V₂ ≤ centralizer ((V₁ ⊔ V₂ : Subgroup G) : Set G) :=
  sup_le (le_centralizer_iff.mp hp.le_centralizer_left)
    (le_centralizer_iff.mp hp.le_centralizer_right)

theorem commute_mem {s t : G} (hs : s ∈ V₁ ⊔ V₂) (ht : t ∈ V₁ ⊔ V₂) : s * t = t * s :=
  (mem_centralizer_iff.mp (hp.le_centralizer_sup ht) s hs)

theorem le_centralizer_of_mem {t : G} (ht : t ∈ V₁ ⊔ V₂) :
    V₁ ⊔ V₂ ≤ centralizer ({t} : Set G) := fun _ hs =>
  mem_centralizer_singleton_iff.mpr (hp.commute_mem hs ht)

theorem mul_self_mem {t : G} (ht : t ∈ V₁ ⊔ V₂) : t * t = 1 := by
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := hp.exists_mul ht
  have h1 := mul_self_of_isKleinFour hp.four_left hu₁
  have h2 := mul_self_of_isKleinFour hp.four_right hu₂
  have hc := hp.commute hu₁ hu₂
  calc u₁ * u₂ * (u₁ * u₂) = u₁ * (u₂ * u₁) * u₂ := by group
    _ = u₁ * u₁ * (u₂ * u₂) := by rw [← hc]; group
    _ = 1 := by rw [h1, h2, one_mul]

theorem orderOf_eq_two {t : G} (ht : t ∈ V₁ ⊔ V₂) (ht1 : t ≠ 1) : orderOf t = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact hp.mul_self_mem ht) ht1

theorem isPGroup_left : IsPGroup 2 V₁ := isPGroup_of_isKleinFour hp.four_left

theorem isPGroup_right : IsPGroup 2 V₂ := isPGroup_of_isKleinFour hp.four_right

theorem card_sup : Nat.card (V₁ ⊔ V₂ : Subgroup G) = 16 := by
  have hn : V₂ ≤ normalizer (V₁ : Set G) :=
    (le_centralizer_iff.mp hp.comm).trans (centralizer_le_normalizer _)
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hn
    (disjoint_iff.mpr hp.disj), @IsKleinFour.card_four V₁ _ hp.four_left,
    @IsKleinFour.card_four V₂ _ hp.four_right]

theorem isElemAbelian : IsElemAbelian 2 (V₁ ⊔ V₂ : Subgroup G) :=
  ⟨isMulCommutative_iff.mpr fun a b => Subtype.ext (hp.commute_mem a.2 b.2),
    fun x hx => by rw [pow_two]; exact hp.mul_self_mem hx⟩

end FourPair

end CFSG.Goldschmidt75
