module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109Dc
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10K0Aux

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec10D_eq_one_or_of_mem_zpowers {x a : G} (hx : x * x = 1) (ha : a ∈ zpowers x) :
    a = 1 ∨ a = x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  have hx2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hx
  obtain ⟨n, hn | hn⟩ := Int.even_or_odd' k
  · left
    rw [hn, zpow_mul, hx2, one_zpow]
  · right
    rw [hn, zpow_add, zpow_mul, hx2, one_zpow, one_mul, zpow_one]

private theorem zpowers_comm_of_commute {t z : G} (htz : t * z = z * t) :
    ∀ a ∈ zpowers t, ∀ b ∈ zpowers z, a * b = b * a := by
  intro a ha b hb
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  exact (Commute.zpow_zpow (show Commute t z from htz) m n).eq

theorem sec10D_mem_hatCent {t z c : G} (hc : c ∈ centralizer ({z} : Set G))
    (hct : c * t * c⁻¹ = t ∨ c * t * c⁻¹ = t * z) : c ∈ hatCent t z := by
  have hczc : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hc
  have hcz : c * z * c⁻¹ = z := by rw [hczc, mul_assoc, mul_inv_cancel, mul_one]
  have hcz' : c⁻¹ * z * c = z := by
    calc c⁻¹ * z * c = c⁻¹ * (c * z * c⁻¹) * c := by rw [hcz]
      _ = z := by group
  have htmem : t ∈ zpowers t ⊔ zpowers z := Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  have hzmem : z ∈ zpowers t ⊔ zpowers z := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have hmem1 : c * t * c⁻¹ ∈ zpowers t ⊔ zpowers z := by
    rcases hct with h | h
    · rw [h]
      exact htmem
    · rw [h]
      exact Subgroup.mul_mem _ htmem hzmem
  have hmem2 : c⁻¹ * t * c ∈ zpowers t ⊔ zpowers z := by
    rcases hct with h | h
    · have e : c⁻¹ * t * c = t := by
        calc c⁻¹ * t * c = c⁻¹ * (c * t * c⁻¹) * c := by rw [h]
          _ = t := by group
      rw [e]
      exact htmem
    · have e1 : t = (c⁻¹ * t * c) * z := by
        calc t = c⁻¹ * (c * t * c⁻¹) * c := by group
          _ = c⁻¹ * (t * z) * c := by rw [h]
          _ = (c⁻¹ * t * c) * (c⁻¹ * z * c) := by group
          _ = (c⁻¹ * t * c) * z := by rw [hcz']
      rw [eq_mul_inv_of_mul_eq e1.symm]
      exact Subgroup.mul_mem _ htmem (Subgroup.inv_mem _ hzmem)
  exact Subgroup.mem_inf.mpr ⟨hc, sec10D_mem_normalizer_tz hcz hmem1 hmem2⟩

theorem sec10D_hatCent_conj {t z : G} (ht2 : t * t = 1) (hz2 : z * z = 1) (htz : t * z = z * t)
    (ht1 : t ≠ 1) (hne : t ≠ z) {p : G} (hp : p ∈ hatCent t z) :
    p * t * p⁻¹ = t ∨ p * t * p⁻¹ = t * z := by
  obtain ⟨hpc, hpn⟩ := Subgroup.mem_inf.mp hp
  have hpz : p * z * p⁻¹ = z := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hpc, mul_assoc, mul_inv_cancel, mul_one]
  have hmem : p * t * p⁻¹ ∈ zpowers t ⊔ zpowers z :=
    ((Subgroup.mem_set_normalizer_iff.mp hpn) t).mp (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
  obtain ⟨a, ha, b, hb, hab⟩ :=
    exists_mul_of_mem_sup_of_commute (zpowers_comm_of_commute htz) hmem
  rcases sec10D_eq_one_or_of_mem_zpowers ht2 ha with ha' | ha' <;>
    rcases sec10D_eq_one_or_of_mem_zpowers hz2 hb with hb' | hb' <;> rw [ha', hb'] at hab
  · exact absurd (conj_eq_one_iff.mp (by rw [hab, one_mul])) ht1
  · refine absurd ?_ hne
    exact mul_left_cancel (mul_right_cancel (by rw [hab, one_mul, hpz]))
  · left
    rw [hab, mul_one]
  · right
    exact hab

theorem sec10D_K0_le (t z : G) :
    secK0 t z ≤ centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G) := by
  unfold secK0 oTwoRes
  rw [Subgroup.closure_le]
  intro x hx
  exact hx.1

theorem sec10D_K0_le_hatCent (t z : G) : secK0 t z ≤ hatCent t z := by
  intro x hx
  obtain ⟨hxt, hxz⟩ := Subgroup.mem_inf.mp (sec10D_K0_le t z hx)
  refine sec10D_mem_hatCent hxz (Or.inl ?_)
  have h : x * t = t * x := (Subgroup.mem_centralizer_singleton_iff.mp hxt)
  rw [h, mul_assoc, mul_inv_cancel, mul_one]

theorem sec10D_hatCent_normalizes {t z : G} (ht2 : t * t = 1) (hz2 : z * z = 1)
    (htz : t * z = z * t) (ht1 : t ≠ 1) (hne : t ≠ z) {c : G} (hc : c ∈ hatCent t z) :
    ∀ x ∈ oTwoRes (centralizer ({z, t} : Set G)),
      c * x * c⁻¹ ∈ oTwoRes (centralizer ({z, t} : Set G)) := by
  have hcz : c ∈ centralizer ({z} : Set G) := (Subgroup.mem_inf.mp hc).1
  have hczc : Commute c z := Subgroup.mem_centralizer_singleton_iff.mp hcz
  have hct' : c⁻¹ * t * c = t ∨ c⁻¹ * t * c = t * z := by
    simpa only [inv_inv] using sec10D_hatCent_conj ht2 hz2 htz ht1 hne (inv_mem hc)
  intro x hx
  unfold oTwoRes at hx ⊢
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
      have hyz : z * y = y * z := Subgroup.mem_centralizer_iff.mp hy.1 z (by simp)
      have hyt : t * y = y * t := Subgroup.mem_centralizer_iff.mp hy.1 t (by simp)
      have hyw : y * (c⁻¹ * t * c) = (c⁻¹ * t * c) * y := by
        rcases hct' with h | h
        · rw [h]
          exact hyt.symm
        · rw [h]
          calc y * (t * z) = (y * t) * z := by rw [mul_assoc]
            _ = (t * y) * z := by rw [hyt]
            _ = t * (y * z) := by rw [mul_assoc]
            _ = t * (z * y) := by rw [hyz]
            _ = (t * z) * y := by rw [mul_assoc]
      refine Subgroup.subset_closure ⟨?_, ?_⟩
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rcases Set.mem_insert_iff.mp hh with h1 | h1
        · rw [h1]
          have hycz : Commute y z := hyz.symm
          exact ((hczc.mul_left hycz).mul_left hczc.inv_left).symm.eq
        · rw [Set.mem_singleton_iff.mp h1]
          calc t * (c * y * c⁻¹) = c * ((c⁻¹ * t * c) * y) * c⁻¹ := by group
            _ = c * (y * (c⁻¹ * t * c)) * c⁻¹ := by rw [hyw]
            _ = (c * y * c⁻¹) * t := by group
      · have hconj : orderOf (c * y * c⁻¹) = orderOf y := by
          rw [← MulAut.conj_apply c y]
          exact (MulAut.conj c).orderOf_eq y
        rw [hconj]
        exact hy.2
  | one => simpa using Subgroup.one_mem (Subgroup.closure _)
  | mul y w _ _ ihy ihw => simpa only [conj_mul] using Subgroup.mul_mem _ ihy ihw
  | inv y _ ihy => simpa only [conj_inv] using Subgroup.inv_mem _ ihy

end CFSG.OddStandard.SmallF3.Omega
