module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Basic
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CanonicalLocalObstruction

public section

namespace CFSG.QuasithinUnique.Cl1

open Equiv Equiv.Perm CFSG.RankThreeCoreUniqueness.Helpers CFSG.QuasithinUnique
open scoped commutatorElement

section Perms

@[expose] def others (a b : Fin 8) : List (Fin 8) :=
  (List.finRange 8).filter fun x => x ≠ a ∧ x ≠ b

@[expose] def pt (a b : Fin 8) (i : ℕ) : Fin 8 := (others a b).getD i 0

@[expose] def tau6 (a b : Fin 8) : Perm (Fin 8) :=
  swap a b * swap (pt a b 0) (pt a b 1) * (swap (pt a b 2) (pt a b 3) * swap (pt a b 3) (pt a b 4))

@[expose] def kap2 (a b : Fin 8) : Perm (Fin 8) :=
  swap (pt a b 3) (pt a b 4) * swap (pt a b 4) (pt a b 5)

@[expose] def kap3 (a b : Fin 8) : Perm (Fin 8) :=
  swap (pt a b 0) (pt a b 2) * swap (pt a b 2) (pt a b 3)

theorem tau6_sign : ∀ a b : Fin 8, a ≠ b → sign (tau6 a b) = 1 := by decide

theorem tau6_comm : ∀ a b : Fin 8, a ≠ b → tau6 a b * swap a b = swap a b * tau6 a b := by decide

theorem tau6_pow : ∀ a b : Fin 8, a ≠ b → tau6 a b ^ 6 = 1 := by decide

theorem kap2_sign : ∀ a b : Fin 8, a ≠ b → sign (kap2 a b) = 1 := by decide

theorem kap2_fix : ∀ a b : Fin 8, a ≠ b → kap2 a b a = a ∧ kap2 a b b = b := by decide

theorem kap2_nc :
    ∀ a b : Fin 8, a ≠ b → tau6 a b ^ 2 * kap2 a b ≠ kap2 a b * tau6 a b ^ 2 := by decide

theorem kap3_sign : ∀ a b : Fin 8, a ≠ b → sign (kap3 a b) = 1 := by decide

theorem kap3_fix : ∀ a b : Fin 8, a ≠ b → kap3 a b a = a ∧ kap3 a b b = b := by decide

theorem kap3_nc :
    ∀ a b : Fin 8, a ≠ b → tau6 a b ^ 3 * kap3 a b ≠ kap3 a b * tau6 a b ^ 3 := by decide

theorem card_sdiff_pair : ∀ a b : Fin 8, a ≠ b → (Finset.univ \ {a, b} : Finset (Fin 8)).card = 6 := by
  decide

end Perms

section Centralizer

variable {G : Type} [Group G] {Ki : Subgroup G} {t : G} {φ : ↥Ki ≃* ↥(alternatingGroup (Fin 8))}
  {a b : Fin 8}

theorem mem_centralizer_iff (hind : InducesAut t Ki φ (MulAut.conjNormal (Equiv.swap a b)))
    (y : ↥Ki) :
    (y : G) ∈ Subgroup.centralizer ({t} : Set G) ↔
      (φ y : Perm (Fin 8)) * swap a b = swap a b * (φ y : Perm (Fin 8)) := by
  obtain ⟨hN, hφ⟩ := hind
  have hy' : t⁻¹ * (y : G) * t ∈ Ki := by
    have := (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (Ki : Set G)).inv_mem hN) y).mp y.2
    simpa using this
  have key := hφ y ⟨t⁻¹ * (y : G) * t, hy'⟩ rfl
  have hcoe : ((φ ⟨t⁻¹ * (y : G) * t, hy'⟩ : ↥(alternatingGroup (Fin 8))) : Perm (Fin 8)) =
      swap a b * (φ y : Perm (Fin 8)) * (swap a b)⁻¹ := by
    rw [key]
    simp
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hyt
    have h1 : (⟨t⁻¹ * (y : G) * t, hy'⟩ : ↥Ki) = y := by
      apply Subtype.ext
      show t⁻¹ * (y : G) * t = y
      calc t⁻¹ * (y : G) * t = t⁻¹ * ((y : G) * t) := by group
        _ = t⁻¹ * (t * y) := by rw [hyt]
        _ = y := by group
    rw [h1] at hcoe
    have h2 : (φ y : Perm (Fin 8)) = swap a b * (φ y : Perm (Fin 8)) * (swap a b)⁻¹ := hcoe
    calc (φ y : Perm (Fin 8)) * swap a b
        = (swap a b * (φ y : Perm (Fin 8)) * (swap a b)⁻¹) * swap a b := by rw [← h2]
      _ = swap a b * (φ y : Perm (Fin 8)) := by group
  · intro hc
    have h2 : swap a b * (φ y : Perm (Fin 8)) * (swap a b)⁻¹ = (φ y : Perm (Fin 8)) := by
      calc swap a b * (φ y : Perm (Fin 8)) * (swap a b)⁻¹
          = ((φ y : Perm (Fin 8)) * swap a b) * (swap a b)⁻¹ := by rw [hc]
        _ = (φ y : Perm (Fin 8)) := by group
    have h3 : φ ⟨t⁻¹ * (y : G) * t, hy'⟩ = φ y := by
      apply Subtype.ext
      rw [hcoe, h2]
    have h4 : (⟨t⁻¹ * (y : G) * t, hy'⟩ : ↥Ki) = y := φ.injective h3
    have h5 : t⁻¹ * (y : G) * t = y := congrArg Subtype.val h4
    calc (y : G) * t = t * (t⁻¹ * (y : G) * t) := by group
      _ = t * y := by rw [h5]

theorem commute_swap_of_fix (w : Perm (Fin 8)) (hwa : w a = a) (hwb : w b = b) :
    w * swap a b = swap a b * w := by
  ext x
  simp only [Perm.mul_apply]
  by_cases hxa : x = a
  · subst hxa
    rw [swap_apply_left, hwa, swap_apply_left, hwb]
  · by_cases hxb : x = b
    · subst hxb
      rw [swap_apply_right, hwb, swap_apply_right, hwa]
    · rw [swap_apply_of_ne_of_ne hxa hxb]
      have hwx : w x ≠ a := fun h => hxa (w.injective (h.trans hwa.symm))
      have hwx' : w x ≠ b := fun h => hxb (w.injective (h.trans hwb.symm))
      rw [swap_apply_of_ne_of_ne hwx hwx']

end Centralizer

section Perfect

theorem isPerfect_of_simple {Y : Type*} [Group Y] [IsSimpleGroup Y]
    (hnc : ¬ IsMulCommutative Y) : Group.IsPerfect Y := by
  rw [Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Y) with h | h
  · exfalso
    apply hnc
    refine ⟨⟨fun x y => ?_⟩⟩
    have h1 : ⁅x, y⁆ ∈ commutator Y := Subgroup.commutator_mem_commutator (Subgroup.mem_top x)
      (Subgroup.mem_top y)
    rw [h, Subgroup.mem_bot] at h1
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1)
  · exact h

end Perfect

section Witness

variable {G : Type} [Group G] {Ki : Subgroup G}

theorem not_comm_aux (φ : ↥Ki ≃* ↥(alternatingGroup (Fin 8))) (u v : ↥(alternatingGroup (Fin 8)))
    (n : ℕ) (hnc : (u : Perm (Fin 8)) ^ n * (v : Perm (Fin 8)) ≠
      (v : Perm (Fin 8)) * (u : Perm (Fin 8)) ^ n) :
    ((φ.symm u : ↥Ki) : G) ^ n * ((φ.symm v : ↥Ki) : G) * (((φ.symm u : ↥Ki) : G) ^ n)⁻¹ ≠
      ((φ.symm v : ↥Ki) : G) := by
  intro h
  have h1 : (φ.symm u) ^ n * φ.symm v * ((φ.symm u) ^ n)⁻¹ = φ.symm v :=
    Subtype.ext (by simpa using h)
  have h2 : u ^ n * v * (u ^ n)⁻¹ = v := by
    have := congrArg φ h1
    simpa [map_mul, map_pow, map_inv] using this
  apply hnc
  have h3 : ((u ^ n * v * (u ^ n)⁻¹ : ↥(alternatingGroup (Fin 8))) : Perm (Fin 8)) =
      (v : Perm (Fin 8)) := congrArg Subtype.val h2
  have h4 : (u : Perm (Fin 8)) ^ n * (v : Perm (Fin 8)) * ((u : Perm (Fin 8)) ^ n)⁻¹ =
      (v : Perm (Fin 8)) := by simpa using h3
  calc (u : Perm (Fin 8)) ^ n * (v : Perm (Fin 8))
      = ((u : Perm (Fin 8)) ^ n * (v : Perm (Fin 8)) * ((u : Perm (Fin 8)) ^ n)⁻¹) *
        (u : Perm (Fin 8)) ^ n := by group
    _ = (v : Perm (Fin 8)) * (u : Perm (Fin 8)) ^ n := by rw [h4]

end Witness

section Main

variable {G : Type} [Group G]

theorem a8_transposition_facts {Ki : Subgroup G} {t : G}
    (φ : ↥Ki ≃* ↥(alternatingGroup (Fin 8))) {a b : Fin 8} (hab : a ≠ b)
    (hind : InducesAut t Ki φ (MulAut.conjNormal (Equiv.swap a b))) :
    ∃ x : G, x ∈ Ki ⊓ Subgroup.centralizer ({t} : Set G) ∧ x ^ 6 = 1 ∧
      (∃ k ∈ perfectResidualOf (Ki ⊓ Subgroup.centralizer ({t} : Set G)),
        x ^ 2 * k * (x ^ 2)⁻¹ ≠ k) ∧
      (∃ k ∈ perfectResidualOf (Ki ⊓ Subgroup.centralizer ({t} : Set G)),
        x ^ 3 * k * (x ^ 3)⁻¹ ≠ k) ∧
      360 ∣ Nat.card ↥(perfectResidualOf (Ki ⊓ Subgroup.centralizer ({t} : Set G))) ∧
      Nat.card ↥(perfectResidualOf (Ki ⊓ Subgroup.centralizer ({t} : Set G))) ∣ 20160 := by
  set X : Subgroup G := Ki ⊓ Subgroup.centralizer ({t} : Set G) with hX
  set s : Finset (Fin 8) := Finset.univ \ {a, b} with hs
  have hscard : Nat.card ↥s = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    exact card_sdiff_pair a b hab
  have hnt : Nontrivial ↥s := Finite.one_lt_card_iff_nontrivial.mp (by rw [hscard]; norm_num)
  let ψ : ↥(alternatingGroup ↥s) →* G :=
    Ki.subtype.comp (φ.symm.toMonoidHom.comp (alternatingGroup.ofSubtype s))
  have hψinj : Function.Injective ψ := by
    intro u v huv
    have h1 : φ.symm (alternatingGroup.ofSubtype s u) = φ.symm (alternatingGroup.ofSubtype s v) :=
      Subtype.ext huv
    exact alternatingGroup.ofSubtype_injective (φ.symm.injective h1)
  have hsimple : IsSimpleGroup ↥(alternatingGroup ↥s) :=
    alternatingGroup.isSimpleGroup (by rw [hscard]; norm_num)
  have hnc : ¬ IsMulCommutative ↥(alternatingGroup ↥s) := by
    rw [alternatingGroup.isMulCommutative_iff_card_le_three, hscard]
    norm_num
  have : Group.IsPerfect ↥(alternatingGroup ↥s) := isPerfect_of_simple hnc
  have hperf : Group.IsPerfect ↥ψ.range := Group.IsPerfect.range ψ
  have hfixX : ∀ w : ↥(alternatingGroup (Fin 8)), (w : Perm (Fin 8)) a = a →
      (w : Perm (Fin 8)) b = b → ((φ.symm w : ↥Ki) : G) ∈ X := by
    intro w hwa hwb
    refine Subgroup.mem_inf.mpr ⟨(φ.symm w).2, ?_⟩
    rw [mem_centralizer_iff hind (φ.symm w), MulEquiv.apply_symm_apply]
    exact commute_swap_of_fix _ hwa hwb
  have hrange : ∀ w : ↥(alternatingGroup (Fin 8)), (w : Perm (Fin 8)) a = a →
      (w : Perm (Fin 8)) b = b → ((φ.symm w : ↥Ki) : G) ∈ ψ.range := by
    intro w hwa hwb
    have hsupp : (w : Perm (Fin 8)).support ⊆ s := by
      intro x hx
      rw [Equiv.Perm.mem_support] at hx
      rw [hs, Finset.mem_sdiff]
      refine ⟨Finset.mem_univ x, ?_⟩
      intro hxab
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxab
      rcases hxab with rfl | rfl
      · exact hx hwa
      · exact hx hwb
    obtain ⟨u, hu⟩ := (alternatingGroup.mem_range_ofSubtype_iff s w).mpr hsupp
    exact ⟨u, by simp only [ψ, MonoidHom.comp_apply, hu]; rfl⟩
  have hYX : ψ.range ≤ X := by
    rintro _ ⟨u, rfl⟩
    refine hfixX _ ?_ ?_
    ·
      have h := (alternatingGroup.mem_range_ofSubtype_iff s _).mp ⟨u, rfl⟩
      by_contra hne
      have := h (Equiv.Perm.mem_support.mpr hne)
      rw [hs, Finset.mem_sdiff] at this
      exact this.2 (by simp)
    · have h := (alternatingGroup.mem_range_ofSubtype_iff s _).mp ⟨u, rfl⟩
      by_contra hne
      have := h (Equiv.Perm.mem_support.mpr hne)
      rw [hs, Finset.mem_sdiff] at this
      exact this.2 (by simp)
  have hYK : ψ.range ≤ perfectResidualOf X :=
    perfect_subgroup_le_perfectResidualOf _ _ hperf hYX
  have hsgn6 : tau6 a b ∈ alternatingGroup (Fin 8) :=
    Equiv.Perm.mem_alternatingGroup.mpr (tau6_sign a b hab)
  have hk2s : kap2 a b ∈ alternatingGroup (Fin 8) :=
    Equiv.Perm.mem_alternatingGroup.mpr (kap2_sign a b hab)
  have hk3s : kap3 a b ∈ alternatingGroup (Fin 8) :=
    Equiv.Perm.mem_alternatingGroup.mpr (kap3_sign a b hab)
  let w6 : ↥(alternatingGroup (Fin 8)) := ⟨tau6 a b, hsgn6⟩
  let k2 : ↥(alternatingGroup (Fin 8)) := ⟨kap2 a b, hk2s⟩
  let k3 : ↥(alternatingGroup (Fin 8)) := ⟨kap3 a b, hk3s⟩
  refine ⟨((φ.symm w6 : ↥Ki) : G), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine Subgroup.mem_inf.mpr ⟨(φ.symm w6).2, ?_⟩
    rw [mem_centralizer_iff hind, MulEquiv.apply_symm_apply]
    exact tau6_comm a b hab
  · have h6 : (φ.symm w6) ^ 6 = 1 := by
      apply φ.injective
      rw [map_pow, MulEquiv.apply_symm_apply, map_one]
      apply Subtype.ext
      simpa [w6] using tau6_pow a b hab
    simpa using congrArg Subtype.val h6
  · exact ⟨((φ.symm k2 : ↥Ki) : G),
      hYK (hrange k2 (kap2_fix a b hab).1 (kap2_fix a b hab).2),
      not_comm_aux φ w6 k2 2 (kap2_nc a b hab)⟩
  · exact ⟨((φ.symm k3 : ↥Ki) : G),
      hYK (hrange k3 (kap3_fix a b hab).1 (kap3_fix a b hab).2),
      not_comm_aux φ w6 k3 3 (kap3_nc a b hab)⟩
  · have h1 : Nat.card ↥ψ.range = 360 := by
      rw [← Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv, nat_card_alternatingGroup, hscard]
      norm_num [Nat.factorial]
    rw [← h1]
    exact Subgroup.card_dvd_of_le hYK
  · have hle : perfectResidualOf X ≤ Ki := (Subgroup.map_subtype_le _).trans inf_le_left
    have h2 : Nat.card ↥Ki = 20160 := by
      rw [Nat.card_congr φ.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      norm_num [Nat.factorial]
    rw [← h2]
    exact Subgroup.card_dvd_of_le hle

end Main

end CFSG.QuasithinUnique.Cl1
