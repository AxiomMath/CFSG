module

public import CFSG.GH74.GLS.C3.Layer1.Th2P43fRules
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.GH74.GLS.Th2.P43f

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1.Bk
  CFSG.GH74.GLS.C3.Layer1.Back CFSG.GH74.GLS.Th2 Equiv Equiv.Perm
  CFSG.LieType.SteinbergBR.SmallAlt

variable {G : Type} [Group G] {x : G} {K T S : Subgroup G} {a z : G} {psi : G → Perm (Fin 7)}

theorem sides_excl (g : Perm (Fin 7)) :
    ¬ ((g = a7P 2 ∨ g = a7P 3) ∧ (g = a7P 6 ∨ g = a7P 7)) := by
  rintro ⟨h1, h2⟩
  rcases h1 with rfl | rfl <;> rcases h2 with h | h <;> exact absurd h (by decide)

namespace Frame

variable (F : Frame x K T S a z psi)

include F

theorem S_le_normalizer_T : ∀ s ∈ S, s ∈ normalizer (T : Set G) := by
  intro s hs
  rcases F.S_cases s hs with h | h
  · exact Subgroup.le_normalizer h
  · have e : s = a * (a⁻¹ * s) := by group
    rw [e]
    exact Subgroup.mul_mem _ F.core.a_mem_norm (Subgroup.le_normalizer h)

theorem psi_inv {g : G} (hg : g ∈ centralizer ({x} : Set G)) : psi g⁻¹ = (psi g)⁻¹ := by
  have := F.psi_mul g hg g⁻¹ ((centralizer ({x} : Set G)).inv_mem hg)
  rw [mul_inv_cancel, F.psi_one] at this
  exact eq_inv_of_mul_eq_one_right this.symm

theorem psi_inj [Finite G] {u v : G} (hu : u ∈ T ⊓ K) (hv : v ∈ T ⊓ K) (h : psi u = psi v) :
    u = v := by
  have hvi : v⁻¹ ∈ T ⊓ K := Subgroup.inv_mem _ hv
  by_contra hne
  have hne' : u * v⁻¹ ≠ 1 := fun h1 => hne (mul_inv_eq_one.1 h1)
  refine F.psi_P_ne_one (Subgroup.mul_mem _ hu hvi) hne' ?_
  rw [F.psi_mul u (F.P_le_C hu) v⁻¹ (F.P_le_C hvi), F.psi_inv (F.P_le_C hv), h, mul_inv_cancel]

theorem z_mem_four [Finite G] {V : Subgroup G} (hV : IsFourSub (T ⊓ K) V) : z ∈ V := by
  by_contra hz
  obtain ⟨hVP, hVel, hV4⟩ := hV
  have hcomm : ∀ u ∈ V, ∀ w ∈ zpowers z, u * w = w * u := by
    intro u hu w hw
    rcases mem_zpowers_of_sq F.z_sq hw with rfl | rfl
    · simp
    · exact F.z_central u (hVP hu)
  have hdisj : V ⊓ zpowers z = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rcases mem_zpowers_of_sq F.z_sq hy.2 with rfl | rfl
    · exact one_mem _
    · exact absurd hy.1 hz
  have hel := isElementaryAbelian_sup_of_commute hVel (isElementaryAbelian_zpowers_of_sq F.z_sq) hcomm
  have hcard : Nat.card ↥(V ⊔ zpowers z) = 8 := by
    rw [card_sup_of_commute_of_disjoint hcomm hdisj, hV4, Nat.card_zpowers,
      orderOf_eq_prime (by rw [sq]; exact F.z_sq) F.z_ne]
  have hle : V ⊔ zpowers z ≤ T ⊓ K := sup_le hVP (zpowers_le.2 F.z_mem)
  have := F.core.P_d8.card_le_four hle hel
  omega

theorem exists_nc [Finite G] {V : Subgroup G} (hV : IsFourSub (T ⊓ K) V) :
    ∃ y ∈ V, y ≠ 1 ∧ y ≠ z := by
  by_contra hcon
  push Not at hcon
  have hle : V ≤ zpowers z := by
    intro y hy
    by_cases h1 : y = 1
    · rw [h1]; exact one_mem _
    · rw [hcon y hy h1]; exact mem_zpowers z
  have h1 := Subgroup.card_le_of_le hle
  rw [hV.2.2, Nat.card_zpowers, orderOf_eq_prime (by rw [sq]; exact F.z_sq) F.z_ne] at h1
  omega

theorem four_eq [Finite G] {V : Subgroup G} (hV : IsFourSub (T ⊓ K) V) {y : G} (hy : y ∈ V)
    (hy1 : y ≠ 1) (hyz : y ≠ z) : ∀ t ∈ V, t = 1 ∨ t = z ∨ t = y ∨ t = z * y := by
  obtain ⟨hcomm, hsq⟩ := forall_of_isElementaryAbelian hV.2.1
  have hzV := F.z_mem_four hV
  have hyy : y * y = 1 := hsq y hy
  have hc : ∀ u ∈ zpowers z, ∀ w ∈ zpowers y, u * w = w * u := by
    intro u hu w hw
    rcases mem_zpowers_of_sq F.z_sq hu with rfl | rfl
    · simp
    · rcases mem_zpowers_of_sq hyy hw with rfl | rfl
      · simp
      · exact hcomm _ hzV _ hy
  have hdisj : zpowers z ⊓ zpowers y = ⊥ := by
    rw [eq_bot_iff]
    intro t ht
    rcases mem_zpowers_of_sq F.z_sq ht.1 with rfl | rfl
    · exact one_mem _
    · rcases mem_zpowers_of_sq hyy ht.2 with h1 | h1
      · exact absurd h1 F.z_ne
      · exact absurd h1.symm hyz
  have hcard : Nat.card ↥(zpowers z ⊔ zpowers y) = 4 := by
    rw [card_sup_of_commute_of_disjoint hc hdisj, Nat.card_zpowers, Nat.card_zpowers,
      orderOf_eq_prime (by rw [sq]; exact F.z_sq) F.z_ne,
      orderOf_eq_prime (by rw [sq]; exact hyy) hy1]
  have hle : zpowers z ⊔ zpowers y ≤ V := sup_le (zpowers_le.2 hzV) (zpowers_le.2 hy)
  have heq : zpowers z ⊔ zpowers y = V :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hV.2.2])
  intro t ht
  rw [← heq] at ht
  obtain ⟨p, hp, q, hq, rfl⟩ :=
    CFSG.GH74.GLS.C3.Layer1.Bk.mem_sup_of_commute hc ht
  rcases mem_zpowers_of_sq F.z_sq hp with rfl | rfl <;> rcases mem_zpowers_of_sq hyy hq with rfl | rfl <;>
    simp

theorem four_eq_of_nc [Finite G] {V V' : Subgroup G} (hV : IsFourSub (T ⊓ K) V)
    (hV' : IsFourSub (T ⊓ K) V') {y y' : G} (hy : y ∈ V) (hy1 : y ≠ 1) (hyz : y ≠ z)
    (hy' : y' ∈ V') (hy'1 : y' ≠ 1) (hy'z : y' ≠ z) (h : y' = y ∨ y' = z * y) : V' = V := by
  have hzV := F.z_mem_four hV
  have hzV' := F.z_mem_four hV'
  have h1 : y' ∈ V := by
    rcases h with rfl | rfl
    · exact hy
    · exact Subgroup.mul_mem _ hzV hy
  have h2 : y ∈ V' := by
    rcases h with rfl | rfl
    · exact hy'
    · have : y = z * (z * y) := by
        calc y = (z * z) * y := by rw [F.z_sq, one_mul]
          _ = z * (z * y) := by group
      rw [this]
      exact Subgroup.mul_mem _ hzV' hy'
  apply le_antisymm
  · intro t ht
    rcases F.four_eq hV' hy' hy'1 hy'z t ht with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact hzV
    · exact h1
    · exact Subgroup.mul_mem _ hzV h1
  · intro t ht
    rcases F.four_eq hV hy hy1 hyz t ht with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact hzV'
    · exact h2
    · exact Subgroup.mul_mem _ hzV' h2

theorem psi_zmul {y : G} (hy : y ∈ T ⊓ K) [Finite G] : psi (z * y) = a7P 1 * psi y := by
  rw [F.psi_mul z (F.P_le_C F.z_mem) y (F.P_le_C hy), F.psi_z]

theorem nc_side [Finite G] {y : G} (hy : y ∈ T ⊓ K) (hy2 : y * y = 1) (hy1 : y ≠ 1) (hyz : y ≠ z) :
    (psi y = a7P 2 ∨ psi y = a7P 3) ∨ (psi y = a7P 6 ∨ psi y = a7P 7) := by
  obtain ⟨i, hi⟩ := F.psi_P y hy
  have hsq : a7P i * a7P i = 1 := by rw [← hi]; exact F.psi_P_sq hy hy2
  rcases a7P_invol_idx i hsq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd (by rw [hi]; rfl) (F.psi_P_ne_one hy hy1)
  · exact absurd (F.psi_inj hy F.z_mem (by rw [hi, F.psi_z])) hyz
  · exact Or.inl (Or.inl hi)
  · exact Or.inl (Or.inr hi)
  · exact Or.inr (Or.inl hi)
  · exact Or.inr (Or.inr hi)

theorem same_side [Finite G] {y y' : G} (hy : y ∈ T ⊓ K) (hy' : y' ∈ T ⊓ K)
    (h : ((psi y = a7P 2 ∨ psi y = a7P 3) ∧ (psi y' = a7P 2 ∨ psi y' = a7P 3)) ∨
      ((psi y = a7P 6 ∨ psi y = a7P 7) ∧ (psi y' = a7P 6 ∨ psi y' = a7P 7))) :
    y' = y ∨ y' = z * y := by
  obtain ⟨h23, h32, h67, h76⟩ := a7P_pair
  have hzy : z * y ∈ T ⊓ K := Subgroup.mul_mem _ F.z_mem hy
  have hzy' := F.psi_zmul hy
  have key : ∀ g g' : Perm (Fin 7), psi y = g → psi y' = g' → (g' = g ∨ g' = a7P 1 * g) →
      y' = y ∨ y' = z * y := by
    intro g g' hg hg' hgg
    rcases hgg with h1 | h1
    · left
      exact F.psi_inj hy' hy (by rw [hg, hg', h1])
    · right
      exact F.psi_inj hy' hzy (by rw [hzy', hg, hg', h1])
  rcases h with ⟨h1 | h1, h2 | h2⟩ | ⟨h1 | h1, h2 | h2⟩
  · exact key _ _ h1 h2 (Or.inl rfl)
  · exact key _ _ h1 h2 (Or.inr h23.symm)
  · exact key _ _ h1 h2 (Or.inr h32.symm)
  · exact key _ _ h1 h2 (Or.inl rfl)
  · exact key _ _ h1 h2 (Or.inl rfl)
  · exact key _ _ h1 h2 (Or.inr h67.symm)
  · exact key _ _ h1 h2 (Or.inr h76.symm)
  · exact key _ _ h1 h2 (Or.inl rfl)

theorem klein_sides [Finite G] {V V' : Subgroup G} (hV : IsFourSub (T ⊓ K) V)
    (hV' : IsFourSub (T ⊓ K) V') (hne : V ≠ V') {y y' : G} (hy : y ∈ V) (hy1 : y ≠ 1)
    (hyz : y ≠ z) (hy' : y' ∈ V') (hy'1 : y' ≠ 1) (hy'z : y' ≠ z) :
    ((psi y = a7P 2 ∨ psi y = a7P 3) ∧ (psi y' = a7P 6 ∨ psi y' = a7P 7)) ∨
      ((psi y = a7P 6 ∨ psi y = a7P 7) ∧ (psi y' = a7P 2 ∨ psi y' = a7P 3)) := by
  have hyP : y ∈ T ⊓ K := hV.1 hy
  have hy'P : y' ∈ T ⊓ K := hV'.1 hy'
  have hy2 : y * y = 1 := (forall_of_isElementaryAbelian hV.2.1).2 y hy
  have hy'2 : y' * y' = 1 := (forall_of_isElementaryAbelian hV'.2.1).2 y' hy'
  have hnot : ¬ (((psi y = a7P 2 ∨ psi y = a7P 3) ∧ (psi y' = a7P 2 ∨ psi y' = a7P 3)) ∨
      ((psi y = a7P 6 ∨ psi y = a7P 7) ∧ (psi y' = a7P 6 ∨ psi y' = a7P 7))) := fun hs =>
    hne (F.four_eq_of_nc hV hV' hy hy1 hyz hy' hy'1 hy'z (F.same_side hyP hy'P hs)).symm
  have h1 := F.nc_side hyP hy2 hy1 hyz
  have h2 := F.nc_side hy'P hy'2 hy'1 hy'z
  rcases h1 with r | t <;> rcases h2 with r' | t'
  · exact absurd (Or.inl ⟨r, r'⟩) hnot
  · exact Or.inl ⟨r, t'⟩
  · exact Or.inr ⟨t, r'⟩
  · exact absurd (Or.inr ⟨t, t'⟩) hnot

theorem klein_unique_other [Finite G] {V V₁ V₂ : Subgroup G} (hV : IsFourSub (T ⊓ K) V)
    (hV₁ : IsFourSub (T ⊓ K) V₁) (hV₂ : IsFourSub (T ⊓ K) V₂) (h1 : V ≠ V₁) (h2 : V₂ ≠ V₁) :
    V = V₂ := by
  by_contra hne
  obtain ⟨y, hy, hy1, hyz⟩ := F.exists_nc hV
  obtain ⟨y₁, hy₁, hy₁1, hy₁z⟩ := F.exists_nc hV₁
  obtain ⟨y₂, hy₂, hy₂1, hy₂z⟩ := F.exists_nc hV₂
  have s1 := F.klein_sides hV hV₁ h1 hy hy1 hyz hy₁ hy₁1 hy₁z
  have s2 := F.klein_sides hV₂ hV₁ h2 hy₂ hy₂1 hy₂z hy₁ hy₁1 hy₁z
  have s3 := F.klein_sides hV hV₂ hne hy hy1 hyz hy₂ hy₂1 hy₂z
  rcases s1 with ⟨a1, b1⟩ | ⟨a1, b1⟩ <;> rcases s2 with ⟨a2, b2⟩ | ⟨a2, b2⟩ <;>
    rcases s3 with ⟨a3, b3⟩ | ⟨a3, b3⟩
  · exact sides_excl (psi y₂) ⟨a2, b3⟩
  · exact sides_excl (psi y) ⟨a1, a3⟩
  · exact sides_excl (psi y₁) ⟨b2, b1⟩
  · exact sides_excl (psi y₁) ⟨b2, b1⟩
  · exact sides_excl (psi y₁) ⟨b1, b2⟩
  · exact sides_excl (psi y₁) ⟨b1, b2⟩
  · exact sides_excl (psi y) ⟨a3, a1⟩
  · exact sides_excl (psi y₂) ⟨b3, a2⟩

end Frame

end CFSG.GH74.GLS.Th2.P43f
