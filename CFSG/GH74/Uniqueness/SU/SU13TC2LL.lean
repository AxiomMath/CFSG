module

public import CFSG.GH74.Uniqueness.SU.SU13Data9
public import CFSG.GH74.Uniqueness.SU.SU13TB1Main
public import CFSG.GH74.Uniqueness.SU.SU13TB2Ord

public section

namespace CFSG.GH74.Uniqueness.SU.SU13

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU13.TB

variable {G : Type} [Group G]

@[expose] noncomputable def kfour {z : G} (hz : orderOf z = 2) (e : Elts G z) : Subgroup G :=
  CFSG.GorensteinWalter.kleinFourOfCommutingInvolutions e.t z
    (by rw [← pow_two]; exact sq_eq_one_of_orderOf_eq_two e.t_ord)
    (by rw [← pow_two]; exact sq_eq_one_of_orderOf_eq_two hz) e.t_comm

section KF

variable {z : G}

theorem kfour_mem (hz : orderOf z = 2) (e : Elts G z) {x : G} (hx : x ∈ kfour hz e) :
    x = e.t * z ∨ x = e.t ∨ x = z ∨ x = 1 := by
  have : x ∈ ({e.t * z, e.t, z, 1} : Set G) := hx
  simpa using this

theorem t_mem_kfour (hz : orderOf z = 2) (e : Elts G z) : e.t ∈ kfour hz e := by
  show e.t ∈ ({e.t * z, e.t, z, 1} : Set G)
  simp

theorem z_mem_kfour (hz : orderOf z = 2) (e : Elts G z) : z ∈ kfour hz e := by
  show z ∈ ({e.t * z, e.t, z, 1} : Set G)
  simp

theorem isKleinFour_kfour (hz : orderOf z = 2) (e : Elts G z) : IsKleinFour (kfour hz e) := by
  have hz1 : z ≠ 1 := by
    intro h; rw [h, orderOf_one] at hz; exact absurd hz (by norm_num)
  have ht1 : e.t ≠ 1 := by
    intro h; have := e.t_ord; rw [h, orderOf_one] at this; exact absurd this (by norm_num)
  exact CFSG.GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions e.t z
    (by rw [← pow_two]; exact sq_eq_one_of_orderOf_eq_two e.t_ord)
    (by rw [← pow_two]; exact sq_eq_one_of_orderOf_eq_two hz) ht1 hz1 e.t_ne e.t_comm

end KF

theorem mem_normalizer_of_forall {N C : Subgroup G} (hNC : ∀ c ∈ C, ∀ n ∈ N, c * n * c⁻¹ ∈ N) {k : G}
    (hk : k ∈ C) : k ∈ normalizer (N : Set G) := by
  rw [mem_normalizer_iff]
  intro h
  refine ⟨fun hh => hNC k hk h hh, fun hh => ?_⟩
  have := hNC k⁻¹ (C.inv_mem hk) _ hh
  simpa [mul_assoc] using this

variable [Finite G] {z : G}

theorem lattice_card (hz : orderOf z = 2) (e : Elts G z) (l : Lem232 z e) {E : Subgroup G}
    (hm : MPart9 z e E) {N : Subgroup G} (hNY : N ≤ oc (centralizer ({e.s₂} : Set G)))
    (hNC : ∀ c ∈ centralizer ({e.s₂} : Set G), ∀ n ∈ N, c * n * c⁻¹ ∈ N) :
    Nat.card N * Nat.card (N ⊓ zpowers e.s₂ : Subgroup G) ^ 2 =
      Nat.card (N ⊓ centralizer ({z} : Set G) : Subgroup G) ^ 3 := by
  set C : Subgroup G := centralizer ({e.s₂} : Set G) with hC
  set M : Subgroup G := C ⊓ centralizer ({z} : Set G) with hM
  have hz1 : z ≠ 1 := by
    intro h; rw [h, orderOf_one] at hz; exact absurd hz (by norm_num)
  have ht1 : e.t ≠ 1 := by
    intro h; have := e.t_ord; rw [h, orderOf_one] at this; exact absurd this (by norm_num)
  have hzC : z ∈ C := mem_centralizer_singleton_iff.mpr e.s₂_comm.symm
  have htC : e.t ∈ C := mem_centralizer_singleton_iff.mpr e.t_s₂
  have : IsKleinFour (kfour hz e) := isKleinFour_kfour hz e
  have hTmem : ∀ x ∈ kfour hz e, x = e.t * z ∨ x = e.t ∨ x = z ∨ x = 1 :=
    fun x hx => kfour_mem hz e hx
  have hTC : kfour hz e ≤ C := by
    intro x hx
    rcases hTmem x hx with rfl | rfl | rfl | rfl
    · exact C.mul_mem htC hzC
    · exact htC
    · exact hzC
    · exact C.one_mem
  have hNodd : Odd (Nat.card N) :=
    Odd.of_dvd_nat (odd_card_oc C) (Subgroup.card_dvd_of_le hNY)
  have hTn : kfour hz e ≤ normalizer (N : Set G) := fun x hx => mem_normalizer_of_forall hNC (hTC hx)
  have hBW := CFSG.ABGLocalTools.card_mul_card_centralizer_four_sq (T := kfour hz e) (K := N) hNodd hTn
    (a := e.t) (b := z) (t_mem_kfour hz e) (z_mem_kfour hz e) ht1 hz1 e.t_ne
  have hNt : Nat.card (N ⊓ centralizer ({e.t} : Set G) : Subgroup G) =
      Nat.card (N ⊓ centralizer ({z} : Set G) : Subgroup G) := by
    obtain ⟨k, hk, hkz⟩ := l.k₁
    have := card_inf_centralizer_conj (mem_normalizer_of_forall hNC (mem_centralizer_singleton_iff.mpr hk)) z
    rw [hkz] at this
    exact this
  have hNtz : Nat.card (N ⊓ centralizer ({e.t * z} : Set G) : Subgroup G) =
      Nat.card (N ⊓ centralizer ({z} : Set G) : Subgroup G) := by
    obtain ⟨k, hk, hkz⟩ := l.k₂
    have := card_inf_centralizer_conj (mem_normalizer_of_forall hNC (mem_centralizer_singleton_iff.mpr hk)) z
    rw [hkz] at this
    exact this
  have hNT : N ⊓ centralizer ((kfour hz e : Subgroup G) : Set G) = N ⊓ zpowers e.s₂ := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxN, hxT⟩ := mem_inf.mp hx
      have hxz : x * z = z * x := (mem_centralizer_iff.mp hxT z (z_mem_kfour hz e)).symm
      have hxt : e.t * x = x * e.t := mem_centralizer_iff.mp hxT e.t (t_mem_kfour hz e)
      have hxY : x ∈ oc C := hNY hxN
      have hxM : x ∈ oc C ⊓ centralizer ({z} : Set G) :=
        mem_inf.mpr ⟨hxY, mem_centralizer_singleton_iff.mpr hxz⟩
      have hxE : x ∈ E := by
        have h1 : oc C ⊓ centralizer ({z} : Set G) ≤ oc M := by
          refine le_oc_of_normal_odd (X := M) (N := oc C ⊓ centralizer ({z} : Set G)) ?_ ?_ ?_
          · intro y hy
            obtain ⟨hy1, hy2⟩ := mem_inf.mp hy
            exact mem_inf.mpr ⟨oc_le _ hy1, hy2⟩
          · intro g hg n hn
            obtain ⟨hn1, hn2⟩ := mem_inf.mp hn
            obtain ⟨hgC, hgz⟩ := mem_inf.mp hg
            refine mem_inf.mpr ⟨conj_mem_oc hgC hn1, ?_⟩
            rw [mem_centralizer_singleton_iff] at hn2 hgz ⊢
            have hgi : g⁻¹ * z = z * g⁻¹ := (Commute.inv_left (show Commute g z from hgz)).eq
            calc g * n * g⁻¹ * z = g * n * (g⁻¹ * z) := by group
              _ = g * n * (z * g⁻¹) := by rw [hgi]
              _ = g * (n * z) * g⁻¹ := by group
              _ = g * (z * n) * g⁻¹ := by rw [hn2]
              _ = (g * z) * n * g⁻¹ := by group
              _ = (z * g) * n * g⁻¹ := by rw [hgz]
              _ = z * (g * n * g⁻¹) := by group
          · exact Odd.of_dvd_nat (odd_card_oc C)
              (Subgroup.card_dvd_of_le inf_le_left)
        rw [← hm.oc_eq]
        exact h1 hxM
      exact mem_inf.mpr ⟨hxN, hm.cent_t x hxE hxt⟩
    · intro x hx
      obtain ⟨hxN, hxs⟩ := mem_inf.mp hx
      refine mem_inf.mpr ⟨hxN, mem_centralizer_iff.mpr fun y hy => ?_⟩
      obtain ⟨k, rfl⟩ := hxs
      have hcy : Commute y e.s₂ := by
        rcases hTmem y hy with rfl | rfl | rfl | rfl
        · exact Commute.mul_left e.t_s₂ e.s₂_comm.symm
        · exact e.t_s₂
        · exact e.s₂_comm.symm
        · exact Commute.one_left _
      exact hcy.zpow_right k
  rw [hNT, hNt, hNtz] at hBW
  rw [hBW]; ring

end CFSG.GH74.Uniqueness.SU.SU13
