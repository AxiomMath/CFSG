module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GConj

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem l34g_pair_unique [Finite G] {H I I' L : Subgroup G} {u : G} (hu : orderOf u = 2)
    (huH : u ∈ normalizer (H : Set G)) (hI : IsComponentIn I H) (hI' : IsComponentIn I' H)
    (hL : IsQuasisimple ↥L) (hLI : L ≤ I ⊔ CFSG.conjugate I u)
    (hLI' : L ≤ I' ⊔ CFSG.conjugate I' u) : I' = I ∨ I' = CFSG.conjugate I u := by
  by_contra h
  rw [not_or] at h
  obtain ⟨hI'I, hI'J⟩ := h
  have hJ : IsComponentIn (CFSG.conjugate I u) H :=
    l34g_isComponentIn_conjugate_of_mem_normalizer hI huH
  have hJ' : IsComponentIn (CFSG.conjugate I' u) H :=
    l34g_isComponentIn_conjugate_of_mem_normalizer hI' huH
  have hJ'u : CFSG.conjugate (CFSG.conjugate I' u) u = I' :=
    l34g_conjugate_conjugate_self I' hu
  have hJu : CFSG.conjugate (CFSG.conjugate I u) u = I :=
    l34g_conjugate_conjugate_self I hu
  have hJ'I : CFSG.conjugate I' u ≠ I := by
    intro heq
    exact hI'J (by rw [← hJ'u, heq])
  have hJ'J : CFSG.conjugate I' u ≠ CFSG.conjugate I u := by
    intro heq
    exact hI'I (by rw [← hJ'u, heq, hJu])
  have hcommL : ∀ a b : ↥L, a * b = b * a := by
    intro a b
    apply Subtype.ext
    have hcent : I' ⊔ CFSG.conjugate I' u ≤
        Subgroup.centralizer ((I ⊔ CFSG.conjugate I u : Subgroup G) : Set G) := by
      apply sup_le
      · intro y hy
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have hIcent : I ≤ Subgroup.centralizer ({y} : Set G) := by
          intro z hz
          rw [Subgroup.mem_centralizer_iff]
          intro t ht
          rw [Set.mem_singleton_iff] at ht
          subst t
          exact (hI.commute_of_ne hI' (Ne.symm hI'I) z hz y hy).symm
        have hJcent : CFSG.conjugate I u ≤ Subgroup.centralizer ({y} : Set G) := by
          intro z hz
          rw [Subgroup.mem_centralizer_iff]
          intro t ht
          rw [Set.mem_singleton_iff] at ht
          subst t
          exact hI'.commute_of_ne hJ hI'J y hy z hz
        exact (Subgroup.mem_centralizer_iff.1 (sup_le hIcent hJcent hx)
          y (Set.mem_singleton _)).symm
      · intro y hy
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have hIcent : I ≤ Subgroup.centralizer ({y} : Set G) := by
          intro z hz
          rw [Subgroup.mem_centralizer_iff]
          intro t ht
          rw [Set.mem_singleton_iff] at ht
          subst t
          exact hJ'.commute_of_ne hI hJ'I y hy z hz
        have hJcent : CFSG.conjugate I u ≤ Subgroup.centralizer ({y} : Set G) := by
          intro z hz
          rw [Subgroup.mem_centralizer_iff]
          intro t ht
          rw [Set.mem_singleton_iff] at ht
          subst t
          exact hJ'.commute_of_ne hJ hJ'J y hy z hz
        exact (Subgroup.mem_centralizer_iff.1 (sup_le hIcent hJcent hx)
          y (Set.mem_singleton _)).symm
    have ha : (a : G) ∈ I' ⊔ CFSG.conjugate I' u := hLI' a.2
    have hb : (b : G) ∈ I ⊔ CFSG.conjugate I u := hLI b.2
    exact (Subgroup.mem_centralizer_iff.1 (hcent ha) (b : G) hb).symm
  obtain ⟨-, -, p, q, hpq⟩ := hL
  obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective p
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective q
  exact hpq (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcommL p q])

theorem l34g_conj_fixed_of_sqrt [Finite G] {H I L : Subgroup G} {u w : G} (hu : orderOf u = 2)
    (hww : w * w = u) (hw : w ∈ normalizer (H : Set G)) (hI : IsComponentIn I H)
    (hL : IsQuasisimple ↥L) (hLw : ∀ l ∈ L, w * l = l * w)
    (hLI : L ≤ I ⊔ CFSG.conjugate I u) : CFSG.conjugate I u = I := by
  have hwu : u * w = w * u := by rw [← hww]; group
  have huH : u ∈ normalizer (H : Set G) := by
    rw [← hww]
    exact mul_mem hw hw
  have hLc : L ≤ Subgroup.centralizer ({w} : Set G) := by
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hLw l hl
  have hLmap : L.map (MulAut.conj w⁻¹).toMonoidHom = L :=
    conjugate_eq_self_of_le_centralizer hLc
  have hLI' : L ≤ CFSG.conjugate I w ⊔ CFSG.conjugate (CFSG.conjugate I w) u := by
    have hmap : L.map (MulAut.conj w⁻¹).toMonoidHom ≤
        (I ⊔ CFSG.conjugate I u).map (MulAut.conj w⁻¹).toMonoidHom :=
      Subgroup.map_mono (f := (MulAut.conj w⁻¹).toMonoidHom) hLI
    rw [hLmap, Subgroup.map_sup] at hmap
    have hJw : (CFSG.conjugate I u).map (MulAut.conj w⁻¹).toMonoidHom =
        CFSG.conjugate (CFSG.conjugate I w) u := by
      change CFSG.conjugate (CFSG.conjugate I u) w =
        CFSG.conjugate (CFSG.conjugate I w) u
      rw [l34g_conjugate_conjugate I u w, l34g_conjugate_conjugate I w u, hwu]
    rw [hJw] at hmap
    exact hmap
  have hI' : IsComponentIn (CFSG.conjugate I w) H :=
    l34g_isComponentIn_conjugate_of_mem_normalizer hI hw
  have hstep : CFSG.conjugate I u = CFSG.conjugate (CFSG.conjugate I w) w := by
    rw [← hww, ← l34g_conjugate_conjugate]
  rcases l34g_pair_unique hu huH hI hI' hL hLI hLI' with h | h
  · rw [hstep, h]
    exact h
  · calc CFSG.conjugate I u
        = CFSG.conjugate (CFSG.conjugate I w) w := hstep
      _ = CFSG.conjugate (CFSG.conjugate I u) w := by rw [h]
      _ = CFSG.conjugate I (u * w) := l34g_conjugate_conjugate I u w
      _ = CFSG.conjugate I (w * u) := by rw [hwu]
      _ = CFSG.conjugate (CFSG.conjugate I w) u := (l34g_conjugate_conjugate I w u).symm
      _ = CFSG.conjugate (CFSG.conjugate I u) u := by rw [h]
      _ = I := l34g_conjugate_conjugate_self I hu

end CFSG.OddStandard.SmallF3.Omega
