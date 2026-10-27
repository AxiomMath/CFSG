module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117Act
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117Fix

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

private theorem sec11_conj_mem_zpowers {a z u : G} (haz : a * z = z * a)
    (hu : u ∈ zpowers z) : a * u * a⁻¹ ∈ zpowers z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  rw [← conj_zpow]
  have h : a * z * a⁻¹ = z := by rw [haz]; group
  rw [h]
  exact Subgroup.zpow_mem_zpowers z k

private theorem sec11_conj_mem_zpowers_iff {a z u : G} (haz : a * z = z * a) :
    a * u * a⁻¹ ∈ zpowers z ↔ u ∈ zpowers z := by
  refine ⟨fun h => ?_, fun h => sec11_conj_mem_zpowers haz h⟩
  have hazi : a⁻¹ * z = z * a⁻¹ := (show Commute a z from haz).inv_left
  have h' : a⁻¹ * (a * u * a⁻¹) * a ∈ zpowers z := by
    simpa using sec11_conj_mem_zpowers hazi h
  have heq : a⁻¹ * (a * u * a⁻¹) * a = u := by group
  rwa [heq] at h'

private theorem sec11_conj_inv_self {g q : G} (hg : g * g = 1) :
    g * (g * q * g⁻¹) * g⁻¹ = q := by
  have hgi : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  rw [hgi]
  have h2 : g * (g * q * g) * g = (g * g) * q * (g * g) := by group
  rw [h2, hg]
  group

private theorem sec11_conj_prod_mid {a b c : G} (hab : a * b = b * a) (hac : a * c = c * a) :
    (a * b)⁻¹ * (b * c * b⁻¹) * (a * b) = c := by
  have hX : Commute a (b * (c * b⁻¹)) :=
    (show Commute a b from hab).mul_right
      ((show Commute a c from hac).mul_right (show Commute a b from hab).inv_right)
  have hcancel : a⁻¹ * (b * (c * b⁻¹)) * a = b * (c * b⁻¹) := by
    simpa only [inv_inv] using hX.inv_left.mul_inv_cancel
  calc (a * b)⁻¹ * (b * c * b⁻¹) * (a * b)
      = b⁻¹ * (a⁻¹ * (b * (c * b⁻¹)) * a) * b := by group
    _ = b⁻¹ * (b * (c * b⁻¹)) * b := by rw [hcancel]
    _ = c := by group

theorem sec11_ax_W_abs [Finite G] {z a x : G} {T C Q1 Q2 : Subgroup G}
    (h1 : Sec11Q8 G z Q1) (h2 : Sec11Q8 G z Q2) (hT : IsPGroup 2 T)
    (hzT : z ∈ T) (hzc : ∀ g ∈ T, g * z = z * g) (hQ1T : Q1 ≤ T) (hQ2T : Q2 ≤ T)
    (hQ : ∀ p ∈ Q1, ∀ q ∈ Q2, p * q = q * p) (haT : a ∈ T) (hxT : x ∈ T)
    (ha2 : a * a = 1) (hx2 : x * x = 1)
    (ha12 : ∀ q ∈ Q1, a * q * a⁻¹ ∈ Q2) (ha21 : ∀ q ∈ Q2, a * q * a⁻¹ ∈ Q1)
    (hx1 : ∀ q ∈ Q1, x * q * x⁻¹ ∈ Q1) (hx2' : ∀ q ∈ Q2, x * q * x⁻¹ ∈ Q2)
    (hnt1 : ∃ y ∈ Q1, x * y * x⁻¹ * y⁻¹ ∉ zpowers z)
    (hnt2 : ∃ y ∈ Q2, x * y * x⁻¹ * y⁻¹ ∉ zpowers z)
    (hC : ∀ g ∈ T, (∀ q ∈ Q1 ⊔ Q2, g * q = q * g) → g ∈ C) :
    a * x * a⁻¹ * x⁻¹ ∈ C ⊔ (Q1 ⊔ Q2) := by
  classical
  have ha : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hx : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have haz : a * z = z * a := hzc a haT
  have hxz : x * z = z * x := hzc x hxT
  set y : G := a * x * a⁻¹ with hy
  have hyi : y⁻¹ = a * x⁻¹ * a⁻¹ := by rw [hy]; group
  have hyT : y ∈ T := by
    rw [hy]
    exact T.mul_mem (T.mul_mem haT hxT) (T.inv_mem haT)
  have hyz : y * z = z * y := by
    have hz : Commute y z := by
      rw [hy]
      exact ((show Commute a z from haz).mul_left (show Commute x z from hxz)).mul_left
        (show Commute a⁻¹ z from (show Commute a z from haz).inv_left)
    exact hz.eq
  have hyNorm1 : ∀ q ∈ Q1, y * q * y⁻¹ ∈ Q1 := by
    intro q hq
    have hA : y * q * y⁻¹ = a * (x * (a * q * a⁻¹) * x⁻¹) * a⁻¹ := by
      rw [hy, hyi, ha]; group
    rw [hA]
    exact ha21 _ (hx2' _ (ha12 q hq))
  have hyNorm2 : ∀ q ∈ Q2, y * q * y⁻¹ ∈ Q2 := by
    intro q hq
    have hA : y * q * y⁻¹ = a * (x * (a * q * a⁻¹) * x⁻¹) * a⁻¹ := by
      rw [hy, hyi, ha]; group
    rw [hA]
    exact ha12 _ (hx1 _ (ha21 q hq))
  have hy2 : y * y = 1 := by
    rw [hy]
    calc (a * x * a⁻¹) * (a * x * a⁻¹) = a * (x * x) * a⁻¹ := by group
      _ = a * 1 * a⁻¹ := by rw [hx2]
      _ = 1 := by group
  have hyNT1 : ∃ q ∈ Q1, y * q * y⁻¹ * q⁻¹ ∉ zpowers z := by
    obtain ⟨q', hq'Q, hq'nt⟩ := hnt2
    refine ⟨a * q' * a⁻¹, ha21 q' hq'Q, ?_⟩
    have hB : y * (a * q' * a⁻¹) * y⁻¹ * (a * q' * a⁻¹)⁻¹
        = a * (x * q' * x⁻¹ * q'⁻¹) * a⁻¹ := by
      rw [hy, hyi]; group
    rw [hB]
    intro hconj
    exact hq'nt ((sec11_conj_mem_zpowers_iff haz).mp hconj)
  have hyNT2 : ∃ q ∈ Q2, y * q * y⁻¹ * q⁻¹ ∉ zpowers z := by
    obtain ⟨q', hq'Q, hq'nt⟩ := hnt1
    refine ⟨a * q' * a⁻¹, ha12 q' hq'Q, ?_⟩
    have hB : y * (a * q' * a⁻¹) * y⁻¹ * (a * q' * a⁻¹)⁻¹
        = a * (x * q' * x⁻¹ * q'⁻¹) * a⁻¹ := by
      rw [hy, hyi]; group
    rw [hB]
    intro hconj
    exact hq'nt ((sec11_conj_mem_zpowers_iff haz).mp hconj)
  have hxN1 : x ∈ Subgroup.normalizer (Q1 : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro q
    exact ⟨hx1 q, fun hq => by
      have h2 : x * (x * q * x⁻¹) * x⁻¹ ∈ Q1 := hx1 (x * q * x⁻¹) hq
      rwa [sec11_conj_inv_self hx2] at h2⟩
  have hxN2 : x ∈ Subgroup.normalizer (Q2 : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro q
    exact ⟨hx2' q, fun hq => by
      have h2 : x * (x * q * x⁻¹) * x⁻¹ ∈ Q2 := hx2' (x * q * x⁻¹) hq
      rwa [sec11_conj_inv_self hx2] at h2⟩
  have hyN1 : y ∈ Subgroup.normalizer (Q1 : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro q
    exact ⟨hyNorm1 q, fun hq => by
      have h2 : y * (y * q * y⁻¹) * y⁻¹ ∈ Q1 := hyNorm1 (y * q * y⁻¹) hq
      rwa [sec11_conj_inv_self hy2] at h2⟩
  have hyN2 : y ∈ Subgroup.normalizer (Q2 : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro q
    exact ⟨hyNorm2 q, fun hq => by
      have h2 : y * (y * q * y⁻¹) * y⁻¹ ∈ Q2 := hyNorm2 (y * q * y⁻¹) hq
      rwa [sec11_conj_inv_self hy2] at h2⟩
  let T1 : Subgroup G := T ⊓ Subgroup.normalizer (Q1 : Set G)
  let T2 : Subgroup G := T ⊓ Subgroup.normalizer (Q2 : Set G)
  have hzT1 : z ∈ T1 := ⟨hzT, Subgroup.le_normalizer h1.z_mem⟩
  have hzT2 : z ∈ T2 := ⟨hzT, Subgroup.le_normalizer h2.z_mem⟩
  have hxT1 : x ∈ T1 := ⟨hxT, hxN1⟩
  have hxT2 : x ∈ T2 := ⟨hxT, hxN2⟩
  have hyT1 : y ∈ T1 := ⟨hyT, hyN1⟩
  have hyT2 : y ∈ T2 := ⟨hyT, hyN2⟩
  have hQ1T1 : Q1 ≤ T1 := fun q hq => ⟨hQ1T hq, Subgroup.le_normalizer hq⟩
  have hQ2T2 : Q2 ≤ T2 := fun q hq => ⟨hQ2T hq, Subgroup.le_normalizer hq⟩
  have hT1 : IsPGroup 2 T1 := hT.to_le inf_le_left
  have hT2 : IsPGroup 2 T2 := hT.to_le inf_le_left
  obtain ⟨p1, hp1Q1, hp1z, hp1fix⟩ :=
    sec11_exists_fixed_class hT1 hzT1 (fun g hg => hzc g hg.1) hQ1T1
      (fun g hg q hq => ((Subgroup.mem_normalizer_iff.mp hg.2) q).mp hq)
      (Sec11Q8.exists_not_mem h1)
  obtain ⟨p2, hp2Q2, hp2z, hp2fix⟩ :=
    sec11_exists_fixed_class hT2 hzT2 (fun g hg => hzc g hg.1) hQ2T2
      (fun g hg q hq => ((Subgroup.mem_normalizer_iff.mp hg.2) q).mp hq)
      (Sec11Q8.exists_not_mem h2)
  have hyxNorm1 : ∀ q ∈ Q1, (y * x) * q * (y * x)⁻¹ ∈ Q1 := by
    intro q hq
    rw [show (y * x) * q * (y * x)⁻¹ = y * (x * q * x⁻¹) * y⁻¹ by group]
    exact hyNorm1 _ (hx1 q hq)
  have hyxNorm2 : ∀ q ∈ Q2, (y * x) * q * (y * x)⁻¹ ∈ Q2 := by
    intro q hq
    rw [show (y * x) * q * (y * x)⁻¹ = y * (x * q * x⁻¹) * y⁻¹ by group]
    exact hyNorm2 _ (hx2' q hq)
  have hY1 : ∀ q ∈ Q1, (y * x) * q * (y * x)⁻¹ * q⁻¹ ∈ zpowers z :=
    sec11_act_mul h1 hp1Q1 hp1z hyNorm1 hx1 hyz hxz
      (hp1fix y hyT1) (hp1fix x hxT1) hyNT1 hnt1
  have hY2 : ∀ q ∈ Q2, (y * x) * q * (y * x)⁻¹ * q⁻¹ ∈ zpowers z :=
    sec11_act_mul h2 hp2Q2 hp2z hyNorm2 hx2' hyz hxz
      (hp2fix y hyT2) (hp2fix x hxT2) hyNT2 hnt2
  obtain ⟨k1, hk1Q1, hk1eq⟩ := Sec11Q8.inner_of_trivial h1 hyxNorm1 hY1
  obtain ⟨k2, hk2Q2, hk2eq⟩ := Sec11Q8.inner_of_trivial h2 hyxNorm2 hY2
  set w : G := (k1 * k2)⁻¹ * (y * x) with hw
  have hwT : w ∈ T := by
    rw [hw]
    exact T.mul_mem (T.inv_mem (T.mul_mem (hQ1T hk1Q1) (hQ2T hk2Q2)))
      (T.mul_mem hyT hxT)
  have hwQ1 : ∀ q ∈ Q1, w * q = q * w := by
    intro q hq
    have hconj : w * q * w⁻¹ = q := by
      calc w * q * w⁻¹
          = (k1 * k2)⁻¹ * ((y * x) * q * (y * x)⁻¹) * (k1 * k2) := by rw [hw]; group
        _ = (k1 * k2)⁻¹ * (k1 * q * k1⁻¹) * (k1 * k2) := by rw [hk1eq q hq]
        _ = k2⁻¹ * q * k2 := by group
        _ = q := by
              have hcomm : q * k2 = k2 * q := hQ q hq k2 hk2Q2
              calc k2⁻¹ * q * k2 = k2⁻¹ * (q * k2) := by group
                _ = k2⁻¹ * (k2 * q) := by rw [hcomm]
                _ = q := by group
    calc w * q = (w * q * w⁻¹) * w := by group
      _ = q * w := by rw [hconj]
  have hwQ2 : ∀ q ∈ Q2, w * q = q * w := by
    intro q hq
    have h12 : k1 * k2 = k2 * k1 := hQ k1 hk1Q1 k2 hk2Q2
    have h1q : k1 * q = q * k1 := hQ k1 hk1Q1 q hq
    have hconj : w * q * w⁻¹ = q := by
      calc w * q * w⁻¹
          = (k1 * k2)⁻¹ * ((y * x) * q * (y * x)⁻¹) * (k1 * k2) := by rw [hw]; group
        _ = (k1 * k2)⁻¹ * (k2 * q * k2⁻¹) * (k1 * k2) := by rw [hk2eq q hq]
        _ = q := sec11_conj_prod_mid h12 h1q
    calc w * q = (w * q * w⁻¹) * w := by group
      _ = q * w := by rw [hconj]
  have hwCent : ∀ q ∈ Q1 ⊔ Q2, w * q = q * w := by
    have hle1 : Q1 ≤ Subgroup.centralizer ({w} : Set G) :=
      fun q hq => Subgroup.mem_centralizer_singleton_iff.mpr (hwQ1 q hq).symm
    have hle2 : Q2 ≤ Subgroup.centralizer ({w} : Set G) :=
      fun q hq => Subgroup.mem_centralizer_singleton_iff.mpr (hwQ2 q hq).symm
    have hsup : Q1 ⊔ Q2 ≤ Subgroup.centralizer ({w} : Set G) := sup_le hle1 hle2
    intro q hq
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hsup hq)).symm
  have hwC : w ∈ C := hC w hwT hwCent
  have hyx_eq : y * x = (k1 * k2) * w := by
    rw [hw]
    group
  rw [hx, hyx_eq]
  exact Subgroup.mul_mem (C ⊔ (Q1 ⊔ Q2))
    (Subgroup.mem_sup_right (Subgroup.mul_mem_sup hk1Q1 hk2Q2)) (Subgroup.mem_sup_left hwC)

end CFSG.OddStandard.SmallF3.Omega
