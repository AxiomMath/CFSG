module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Tactic.Group

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

@[expose] noncomputable def sec8t84d5_iotaHom {G : Type} [Group G] (t : G) (T Y1 Y2 : Subgroup G)
    (hsw1 : ∀ a ∈ T ⊓ Y1, t * a * t⁻¹ ∈ T ⊓ Y2)
    (hcomm : ∀ a ∈ T ⊓ Y1, ∀ b ∈ T ⊓ Y2, a * b = b * a) :
    ↥(T ⊓ Y1) →* G where
  toFun s := (s : G) * (t * (s : G) * t⁻¹)
  map_one' := by simp
  map_mul' s s' := by
    have h2 : t * ((s : G) * (s' : G)) * t⁻¹ =
        (t * (s : G) * t⁻¹) * (t * (s' : G) * t⁻¹) := by group
    have h3 : (s : G) * (s' : G) * ((t * (s : G) * t⁻¹) * (t * (s' : G) * t⁻¹)) =
        (s : G) * ((s' : G) * (t * (s : G) * t⁻¹)) * (t * (s' : G) * t⁻¹) := by group
    have hc : (s' : G) * (t * (s : G) * t⁻¹) = (t * (s : G) * t⁻¹) * (s' : G) :=
      hcomm (s' : G) s'.2 (t * (s : G) * t⁻¹) (hsw1 (s : G) s.2)
    show (s : G) * (s' : G) * (t * ((s : G) * (s' : G)) * t⁻¹) =
      (s : G) * (t * (s : G) * t⁻¹) * ((s' : G) * (t * (s' : G) * t⁻¹))
    rw [h2, h3, hc]
    group

lemma sec8t84d5_iotaHom_injective {G : Type} [Group G] {t : G} {T Y1 Y2 : Subgroup G}
    (hsw1 : ∀ a ∈ T ⊓ Y1, t * a * t⁻¹ ∈ T ⊓ Y2)
    (hcomm : ∀ a ∈ T ⊓ Y1, ∀ b ∈ T ⊓ Y2, a * b = b * a)
    (hinf : (T ⊓ Y1) ⊓ (T ⊓ Y2) = ⊥) :
    Function.Injective (sec8t84d5_iotaHom t T Y1 Y2 hsw1 hcomm) := by
  refine (MonoidHom.ker_eq_bot_iff (sec8t84d5_iotaHom t T Y1 Y2 hsw1 hcomm)).mp ?_
  rw [eq_bot_iff]
  intro s hs
  rw [Subgroup.mem_bot]
  have h1 : (s : G) * (t * (s : G) * t⁻¹) = 1 := by
    have h := MonoidHom.mem_ker.mp hs
    change (s : G) * (t * (s : G) * t⁻¹) = 1 at h
    exact h
  have h2 : (s : G) = (t * (s : G) * t⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left h1
  have hm : (s : G) ∈ (T ⊓ Y1) ⊓ (T ⊓ Y2) :=
    ⟨s.2, by rw [h2]; exact (T ⊓ Y2).inv_mem (hsw1 (s : G) s.2)⟩
  rw [hinf, Subgroup.mem_bot] at hm
  exact Subtype.ext hm

lemma sec8t84d5_normalizer_conj_of_involution {G : Type} [Group G] {H : Subgroup G} {t : G}
    (ht : t * t = 1) (hle : H.map (MulAut.conj t) ≤ H) :
    t ∈ Subgroup.normalizer H := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply le_antisymm hle
  intro h hh
  refine Subgroup.mem_map.mpr
    ⟨MulAut.conj t h, hle (Subgroup.mem_map.mpr ⟨h, hh, rfl⟩), ?_⟩
  change MulAut.conj t (MulAut.conj t h) = h
  rw [MulAut.conj_apply, MulAut.conj_apply]
  change t * (t * h * t⁻¹) * t⁻¹ = h
  rw [show t * (t * h * t⁻¹) * t⁻¹ = (t * t) * h * (t * t)⁻¹ by group, ht]
  simp

lemma sec8t84d5_range_iotaHom_le_T0 {G : Type} [Group G] {t : G} {T Y1 Y2 : Subgroup G}
    (hsw1 : ∀ a ∈ T ⊓ Y1, t * a * t⁻¹ ∈ T ⊓ Y2)
    (hcomm : ∀ a ∈ T ⊓ Y1, ∀ b ∈ T ⊓ Y2, a * b = b * a) :
    (sec8t84d5_iotaHom t T Y1 Y2 hsw1 hcomm).range ≤ T ⊓ (Y1 ⊔ Y2) := by
  rintro d ⟨s, rfl⟩
  exact ⟨mul_mem s.2.1 (hsw1 (s : G) s.2).1,
    Subgroup.mul_mem_sup s.2.2 (hsw1 (s : G) s.2).2⟩

lemma sec8t84d5_range_iotaHom_le_centralizer {G : Type} [Group G] {t : G} {T Y1 Y2 : Subgroup G}
    (ht : t * t = 1)
    (hsw1 : ∀ a ∈ T ⊓ Y1, t * a * t⁻¹ ∈ T ⊓ Y2)
    (hcomm : ∀ a ∈ T ⊓ Y1, ∀ b ∈ T ⊓ Y2, a * b = b * a) :
    (sec8t84d5_iotaHom t T Y1 Y2 hsw1 hcomm).range ≤ Subgroup.centralizer ({t} : Set G) := by
  rintro d ⟨s, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  rw [hh]
  have hc : (s : G) * (t * (s : G) * t⁻¹) = (t * (s : G) * t⁻¹) * (s : G) :=
    hcomm (s : G) s.2 (t * (s : G) * t⁻¹) (hsw1 (s : G) s.2)
  have hY : t * (t * (s : G) * t⁻¹) * t⁻¹ = (s : G) := by
    rw [show t * (t * (s : G) * t⁻¹) * t⁻¹ = (t * t) * (s : G) * (t * t)⁻¹ by group, ht]
    simp
  have hconj : t * ((s : G) * (t * (s : G) * t⁻¹)) * t⁻¹ =
      (s : G) * (t * (s : G) * t⁻¹) := by
    calc t * ((s : G) * (t * (s : G) * t⁻¹)) * t⁻¹
        = (t * (s : G) * t⁻¹) * (t * (t * (s : G) * t⁻¹) * t⁻¹) := by group
      _ = (t * (s : G) * t⁻¹) * (s : G) := by rw [hY]
      _ = (s : G) * (t * (s : G) * t⁻¹) := hc.symm
  calc t * ((s : G) * (t * (s : G) * t⁻¹))
      = t * ((s : G) * (t * (s : G) * t⁻¹)) * (t⁻¹ * t) := by rw [inv_mul_cancel, mul_one]
    _ = (t * ((s : G) * (t * (s : G) * t⁻¹)) * t⁻¹) * t := by group
    _ = ((s : G) * (t * (s : G) * t⁻¹)) * t := by rw [hconj]

lemma sec8t84d5_mem_range_iotaHom_of_mem_T0_centralizer {G : Type} [Group G] {t : G}
    {T Y1 Y2 : Subgroup G}
    (hsw1 : ∀ a ∈ T ⊓ Y1, t * a * t⁻¹ ∈ T ⊓ Y2)
    (hsw2 : ∀ a ∈ T ⊓ Y2, t * a * t⁻¹ ∈ T ⊓ Y1)
    (hcomm : ∀ a ∈ T ⊓ Y1, ∀ b ∈ T ⊓ Y2, a * b = b * a)
    (hinf : (T ⊓ Y1) ⊓ (T ⊓ Y2) = ⊥)
    (hT0eq : T ⊓ (Y1 ⊔ Y2) = (T ⊓ Y1) ⊔ (T ⊓ Y2))
    {a : G} (ha : a ∈ T ⊓ (Y1 ⊔ Y2)) (hac : t * a = a * t) :
    a ∈ (sec8t84d5_iotaHom t T Y1 Y2 hsw1 hcomm).range := by
  have hS1_cent : T ⊓ Y1 ≤ Subgroup.centralizer ((T ⊓ Y2 : Subgroup G) : Set G) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (hcomm s hs b hb).symm
  have hS1_norm : T ⊓ Y1 ≤ Subgroup.normalizer ((T ⊓ Y2 : Subgroup G) : Set G) :=
    hS1_cent.trans (Subgroup.centralizer_le_normalizer ((T ⊓ Y2 : Subgroup G) : Set G))
  rw [hT0eq] at ha
  have ha' : a ∈ (↑((T ⊓ Y1) ⊔ (T ⊓ Y2)) : Set G) := ha
  rw [Subgroup.coe_mul_of_left_le_normalizer_right (T ⊓ Y1) (T ⊓ Y2) hS1_norm] at ha'
  obtain ⟨s1, hs1, s2, hs2, hprod⟩ := Set.mem_mul.mp ha'
  rw [← hprod] at hac ⊢
  have hconj : t * (s1 * s2) * t⁻¹ = s1 * s2 := by rw [hac]; group
  have hvu : (t * s2 * t⁻¹) * (t * s1 * t⁻¹) = s1 * s2 := by
    rw [hcomm (t * s2 * t⁻¹) (hsw2 s2 hs2) (t * s1 * t⁻¹) (hsw1 s1 hs1)]
    rw [show (t * s1 * t⁻¹) * (t * s2 * t⁻¹) = t * (s1 * s2) * t⁻¹ by group, hconj]
  have heq : s1⁻¹ * (t * s2 * t⁻¹) = s2 * (t * s1 * t⁻¹)⁻¹ := by
    have h := congrArg (fun x => s1⁻¹ * x * (t * s1 * t⁻¹)⁻¹) hvu
    rw [show s1⁻¹ * ((t * s2 * t⁻¹) * (t * s1 * t⁻¹)) * (t * s1 * t⁻¹)⁻¹
          = s1⁻¹ * (t * s2 * t⁻¹) by group] at h
    rw [show s1⁻¹ * (s1 * s2) * (t * s1 * t⁻¹)⁻¹
          = s2 * (t * s1 * t⁻¹)⁻¹ by group] at h
    exact h
  have hmem1 : s1⁻¹ * (t * s2 * t⁻¹) ∈ T ⊓ Y1 :=
    mul_mem ((T ⊓ Y1).inv_mem hs1) (hsw2 s2 hs2)
  have hmem2 : s2 * (t * s1 * t⁻¹)⁻¹ ∈ T ⊓ Y2 :=
    mul_mem hs2 ((T ⊓ Y2).inv_mem (hsw1 s1 hs1))
  have hbot : s1⁻¹ * (t * s2 * t⁻¹) = 1 := by
    have hmem : s1⁻¹ * (t * s2 * t⁻¹) ∈ (T ⊓ Y1) ⊓ (T ⊓ Y2) :=
      ⟨hmem1, by rw [heq]; exact hmem2⟩
    rwa [hinf, Subgroup.mem_bot] at hmem
  have hs2eq : s2 = t * s1 * t⁻¹ := by
    have h2 : s2 * (t * s1 * t⁻¹)⁻¹ = 1 := by rw [← heq]; exact hbot
    exact mul_inv_eq_one.mp h2
  refine ⟨⟨s1, hs1⟩, ?_⟩
  show (s1 : G) * (t * s1 * t⁻¹) = s1 * s2
  rw [hs2eq]

lemma sec8t84d5_centralizer_eq_range_iota_sup_zpowers {G : Type} [Group G] {t : G}
    {T Y1 Y2 : Subgroup G}
    (ht : t * t = 1)
    (hsw1 : ∀ a ∈ T ⊓ Y1, t * a * t⁻¹ ∈ T ⊓ Y2)
    (hsw2 : ∀ a ∈ T ⊓ Y2, t * a * t⁻¹ ∈ T ⊓ Y1)
    (hcomm : ∀ a ∈ T ⊓ Y1, ∀ b ∈ T ⊓ Y2, a * b = b * a)
    (hinf : (T ⊓ Y1) ⊓ (T ⊓ Y2) = ⊥)
    (hT0eq : T ⊓ (Y1 ⊔ Y2) = (T ⊓ Y1) ⊔ (T ⊓ Y2))
    (hTeq : T = Subgroup.zpowers t ⊔ (T ⊓ (Y1 ⊔ Y2)))
    (htT : t ∈ T) :
    T ⊓ Subgroup.centralizer ({t} : Set G) =
      (sec8t84d5_iotaHom t T Y1 Y2 hsw1 hcomm).range ⊔ Subgroup.zpowers t := by
  have hZC : Subgroup.zpowers t ≤ Subgroup.centralizer ({t} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr (fun h hh => by
      rw [Set.mem_singleton_iff] at hh; simp [hh]))
  have hmap1 : (T ⊓ Y1).map (MulAut.conj t) ≤ T ⊓ Y2 := by
    rintro x ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply] using hsw1 y hy
  have hmap2 : (T ⊓ Y2).map (MulAut.conj t) ≤ T ⊓ Y1 := by
    rintro x ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply] using hsw2 y hy
  have hT0map : (T ⊓ (Y1 ⊔ Y2)).map (MulAut.conj t) ≤ T ⊓ (Y1 ⊔ Y2) := by
    rw [hT0eq, Subgroup.map_sup]
    exact sup_le (hmap1.trans le_sup_right) (hmap2.trans le_sup_left)
  have hZ_norm : Subgroup.zpowers t ≤
      Subgroup.normalizer ((T ⊓ (Y1 ⊔ Y2) : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr (sec8t84d5_normalizer_conj_of_involution ht hT0map)
  apply le_antisymm
  · rintro x ⟨hxT, hxC⟩
    have hx : x ∈ Subgroup.zpowers t ⊔ (T ⊓ (Y1 ⊔ Y2)) := hTeq ▸ hxT
    have hx' : x ∈ (↑(Subgroup.zpowers t ⊔ (T ⊓ (Y1 ⊔ Y2))) : Set G) := hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers t) (T ⊓ (Y1 ⊔ Y2))
      hZ_norm] at hx'
    obtain ⟨z0, hz0, a, ha, hxza⟩ := Set.mem_mul.mp hx'
    have hz0c : z0 ∈ Subgroup.centralizer ({t} : Set G) := hZC hz0
    have haz0 : a = z0⁻¹ * x := by rw [← hxza]; group
    have haC : a ∈ Subgroup.centralizer ({t} : Set G) := by
      rw [haz0]
      exact mul_mem ((Subgroup.centralizer ({t} : Set G)).inv_mem hz0c) hxC
    have hcomm_a : t * a = a * t :=
      Subgroup.mem_centralizer_iff.mp haC t (Set.mem_singleton t)
    have haD : a ∈ (sec8t84d5_iotaHom t T Y1 Y2 hsw1 hcomm).range :=
      sec8t84d5_mem_range_iotaHom_of_mem_T0_centralizer hsw1 hsw2 hcomm hinf hT0eq ha hcomm_a
    have hza : z0 * a ∈ Subgroup.zpowers t ⊔ (sec8t84d5_iotaHom t T Y1 Y2 hsw1 hcomm).range :=
      Subgroup.mul_mem_sup hz0 haD
    rw [← hxza]
    rwa [sup_comm] at hza
  · refine sup_le ?_ ?_
    · exact le_inf ((sec8t84d5_range_iotaHom_le_T0 hsw1 hcomm).trans inf_le_left)
        (sec8t84d5_range_iotaHom_le_centralizer ht hsw1 hcomm)
    · exact le_inf (Subgroup.zpowers_le.mpr htT) hZC

end CFSG.OddStandard.SmallF3.Omega
