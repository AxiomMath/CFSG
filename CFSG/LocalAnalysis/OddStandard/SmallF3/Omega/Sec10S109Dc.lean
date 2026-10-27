module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Notation

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem isPGroup_zpowers_of_sq {x : G} (hx : x * x = 1) : IsPGroup 2 ↥(zpowers x) := by
  rw [isPGroup_iff_pow_pow_eq_one]
  rintro ⟨y, hy⟩
  refine ⟨1, ?_⟩
  have h1 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hx)
  have h2 : orderOf y ∣ 2 := (orderOf_dvd_of_mem_zpowers hy).trans h1
  apply Subtype.ext
  have : y ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp h2
  simpa using this

private theorem zpowers_le_normalizer_of_commute {a b : G} (h : a * b = b * a) :
    zpowers a ≤ normalizer ((zpowers b : Subgroup G) : Set G) := by
  refine Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ ?_)
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact ((show Commute a b from h).zpow_right i).eq.symm

private theorem isPGroup_two_tz {t z : G} (ht2 : t * t = 1) (hz2 : z * z = 1)
    (htz : t * z = z * t) : IsPGroup 2 ↥(zpowers t ⊔ zpowers z) :=
  IsPGroup.to_sup_of_normal_left' (isPGroup_zpowers_of_sq ht2) (isPGroup_zpowers_of_sq hz2)
    (zpowers_le_normalizer_of_commute htz.symm)

theorem sec10D_mem_normalizer_tz {t z c : G} (hcz : c * z * c⁻¹ = z)
    (hct : c * t * c⁻¹ ∈ zpowers t ⊔ zpowers z) (hct' : c⁻¹ * t * c ∈ zpowers t ⊔ zpowers z) :
    c ∈ normalizer ((zpowers t ⊔ zpowers z : Subgroup G) : Set G) := by
  have key : ∀ d : G, d * z * d⁻¹ = z → d * t * d⁻¹ ∈ zpowers t ⊔ zpowers z →
      ∀ x ∈ zpowers t ⊔ zpowers z, d * x * d⁻¹ ∈ zpowers t ⊔ zpowers z := by
    intro d hdz hdt x hx
    have hmap : (zpowers t ⊔ zpowers z).map (MulAut.conj d).toMonoidHom ≤
        zpowers t ⊔ zpowers z := by
      rw [Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨y, hy, rfl⟩
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        have : (MulAut.conj d).toMonoidHom (t ^ i) = (d * t * d⁻¹) ^ i := by
          simp [map_zpow, MulAut.conj_apply]
        rw [this]
        exact Subgroup.zpow_mem _ hdt i
      · rintro _ ⟨y, hy, rfl⟩
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        have : (MulAut.conj d).toMonoidHom (z ^ i) = (d * z * d⁻¹) ^ i := by
          simp [map_zpow, MulAut.conj_apply]
        rw [this, hdz]
        exact Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers z i)
    exact hmap (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  have hcz' : c⁻¹ * z * c⁻¹⁻¹ = z := by
    calc c⁻¹ * z * c⁻¹⁻¹ = c⁻¹ * z * c := by group
      _ = c⁻¹ * (c * z * c⁻¹) * c := by rw [hcz]
      _ = z := by group
  rw [Subgroup.mem_set_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact key c hcz hct x hx
  · intro hx
    have h := key c⁻¹ hcz' (by simpa using hct') (c * x * c⁻¹) hx
    have e : c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x := by group
    rwa [e] at h

theorem sec10D_isolated_mod [Finite G] {T : Subgroup G} {t z : G}
    (hT : IsSylow2Of T (centralizer ({z} : Set G))) (htT : t ∈ T) (hzT : z ∈ T)
    (hsc : IsStrClosedModZ t z T) (ht2 : t * t = 1) (hz2 : z * z = 1) (htz : t * z = z * t) :
    ∀ h ∈ centralizer ({z} : Set G),
      (h * t * h⁻¹) * t * (h * t * h⁻¹)⁻¹ * t⁻¹ ∈ zpowers z →
        h * t * h⁻¹ = t ∨ h * t * h⁻¹ = t * z := by
  intro h hh hcomm
  have hhz : Commute h z := Subgroup.mem_centralizer_singleton_iff.mp hh
  have htzc : Commute t z := htz
  have hzH : z ∈ centralizer ({z} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have htH : t ∈ centralizer ({z} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr htz
  obtain ⟨u, hu⟩ : ∃ u : G, u = h * t * h⁻¹ := ⟨_, rfl⟩
  rw [← hu] at hcomm ⊢
  have huu : u * u = 1 := by
    calc u * u = h * (t * t) * h⁻¹ := by rw [hu]; group
      _ = 1 := by rw [ht2]; group
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  have huzc : Commute u z := by
    rw [hu]
    exact (hhz.mul_left htzc).mul_left hhz.inv_left
  have huz : u * z * u⁻¹ = z := by
    calc u * z * u⁻¹ = z * u * u⁻¹ := by rw [huzc.eq]
      _ = z := by group
  have huH : u ∈ centralizer ({z} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr huzc.eq
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcomm
  have hutu : u * t * u⁻¹ ∈ zpowers t ⊔ zpowers z := by
    have e : u * t * u⁻¹ = z ^ k * t := by rw [hk]; group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers z k))
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
  have hutu' : u⁻¹ * t * u ∈ zpowers t ⊔ zpowers z := by
    have h := hutu
    rw [huinv] at h ⊢
    exact h
  have huN : u ∈ normalizer ((zpowers t ⊔ zpowers z : Subgroup G) : Set G) :=
    sec10D_mem_normalizer_tz huz hutu hutu'
  have hD2 : IsPGroup 2 ↥((zpowers t ⊔ zpowers z) ⊔ zpowers u) :=
    IsPGroup.to_sup_of_normal_left' (isPGroup_two_tz ht2 hz2 htz) (isPGroup_zpowers_of_sq huu)
      (Subgroup.zpowers_le.mpr huN)
  have hDH : (zpowers t ⊔ zpowers z) ⊔ zpowers u ≤ centralizer ({z} : Set G) :=
    sup_le (sup_le (Subgroup.zpowers_le.mpr htH) (Subgroup.zpowers_le.mpr hzH))
      (Subgroup.zpowers_le.mpr huH)
  obtain ⟨Q, hQ, hDQ⟩ := exists_isSylow2Of_ge hD2 hDH
  obtain ⟨a, ha, hconj⟩ := hT.exists_conj_mem hQ
  have htQ : t ∈ Q :=
    hDQ (Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers t)))
  have huQ : u ∈ Q := hDQ (Subgroup.mem_sup_right (Subgroup.mem_zpowers u))
  have hat : a⁻¹ * t * a ∈ T := (hconj t).mp htQ
  have hau : a⁻¹ * u * a ∈ T := (hconj u).mp huQ
  have h1 : a⁻¹ * t * a = t ∨ a⁻¹ * t * a = t * z := hsc a ha (Subgroup.mem_sup_left hat)
  have h2 : a⁻¹ * u * a = t ∨ a⁻¹ * u * a = t * z := by
    have hha : h⁻¹ * a ∈ centralizer ({z} : Set G) := mul_mem (inv_mem hh) ha
    have e : (h⁻¹ * a)⁻¹ * t * (h⁻¹ * a) = a⁻¹ * u * a := by rw [hu]; group
    rw [← e]
    apply hsc _ hha
    rw [e]
    exact Subgroup.mem_sup_left hau
  have haz : a * z * a⁻¹ = z := by
    have h := Subgroup.mem_centralizer_singleton_iff.mp ha
    calc a * z * a⁻¹ = z * a * a⁻¹ := by rw [h]
      _ = z := by group
  have hu_eq : u = a * (a⁻¹ * u * a) * a⁻¹ := by group
  have ht_eq : t = a * (a⁻¹ * t * a) * a⁻¹ := by group
  have hat' : a * t * a⁻¹ = t ∨ a * t * a⁻¹ = t * z := by
    rcases h1 with h1 | h1
    · left
      rw [h1] at ht_eq
      exact ht_eq.symm
    · right
      rw [h1] at ht_eq
      have e : a * (t * z) * a⁻¹ = (a * t * a⁻¹) * (a * z * a⁻¹) := by group
      rw [e, haz] at ht_eq
      calc a * t * a⁻¹ = a * t * a⁻¹ * z * z := by rw [mul_assoc _ z z, hz2, mul_one]
        _ = t * z := by rw [← ht_eq]
  rcases h2 with h2 | h2
  · rw [h2] at hu_eq
    rw [hu_eq]
    exact hat'
  · rw [h2] at hu_eq
    have e : a * (t * z) * a⁻¹ = (a * t * a⁻¹) * (a * z * a⁻¹) := by group
    rw [e, haz] at hu_eq
    rw [hu_eq]
    rcases hat' with h | h
    · right
      rw [h]
    · left
      rw [h, mul_assoc, hz2, mul_one]

end CFSG.OddStandard.SmallF3.Omega
