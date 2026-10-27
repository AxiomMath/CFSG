module

public import CFSG.CGT.PushingUpLit.CGT6E.Emb55OB
public import CFSG.CGT.PushingUpLit.CGT6E.Emb55Act
public import CFSG.CGT.PushingUpLit.CGT6E.Emb55GL

public section

namespace CFSG.CGT.PushingUpLit.CGT6E

open CFSG.Quasithin CFSG.CGT.PushingUpLit.CGT6
open scoped commutatorElement

theorem zpow_conj_of_comm {G : Type*} [Group G] {x y z : G} (hxy : x * y * x⁻¹ = z * y)
    (hzx : x * z = z * x) (n : ℤ) : x ^ n * y * x ^ (-n) = z ^ n * y := by
  have hc : ∀ m : ℤ, Commute x (z ^ m) := fun m =>
    Commute.zpow_right (show Commute x z from hzx) m
  have hzxn : ∀ m : ℤ, x * z ^ m * x⁻¹ = z ^ m := fun m => by
    rw [(hc m).eq]; group
  have hzxn' : ∀ m : ℤ, x⁻¹ * z ^ m * x = z ^ m := fun m => by
    have := (hc m).inv_left.eq
    rw [this]; group
  have h1 : x⁻¹ * z * x = z := by simpa using hzxn' 1
  have h2 : y = z * (x⁻¹ * y * x) := by
    calc y = x⁻¹ * (x * y * x⁻¹) * x := by group
      _ = x⁻¹ * (z * y) * x := by rw [hxy]
      _ = (x⁻¹ * z * x) * (x⁻¹ * y * x) := by group
      _ = z * (x⁻¹ * y * x) := by rw [h1]
  have hy : x⁻¹ * y * x = z⁻¹ * y := by
    calc x⁻¹ * y * x = z⁻¹ * (z * (x⁻¹ * y * x)) := by group
      _ = z⁻¹ * y := by rw [← h2]
  induction n using Int.induction_on with
  | zero => simp
  | succ i ih =>
    calc x ^ ((i : ℤ) + 1) * y * x ^ (-((i : ℤ) + 1))
        = x * (x ^ (i : ℤ) * y * x ^ (-(i : ℤ))) * x⁻¹ := by group
      _ = x * (z ^ (i : ℤ) * y) * x⁻¹ := by rw [ih]
      _ = (x * z ^ (i : ℤ) * x⁻¹) * (x * y * x⁻¹) := by group
      _ = z ^ (i : ℤ) * (z * y) := by rw [hzxn, hxy]
      _ = z ^ ((i : ℤ) + 1) * y := by group
  | pred i ih =>
    calc x ^ (-(i : ℤ) - 1) * y * x ^ (-(-(i : ℤ) - 1))
        = x⁻¹ * (x ^ (-(i : ℤ)) * y * x ^ (-(-(i : ℤ)))) * x := by group
      _ = x⁻¹ * (z ^ (-(i : ℤ)) * y) * x := by rw [ih]
      _ = (x⁻¹ * z ^ (-(i : ℤ)) * x) * (x⁻¹ * y * x) := by group
      _ = z ^ (-(i : ℤ)) * (z⁻¹ * y) := by rw [hzxn', hy]
      _ = z ^ (-(i : ℤ) - 1) * y := by group

variable {V : Type} [CommGroup V] [Finite V] {G T Y H Q D : Subgroup (MulAut V)} {y a : MulAut V}

namespace Cfg55

variable (k : Cfg55 V G T Y H Q D y a)
include k

theorem Q_le_D : Q ≤ D := by
  rw [k.Q_eq, Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact k.aD
  · exact k.cD

omit [Finite V] in
theorem hnc : a * ⁅a, y⁆ ≠ ⁅a, y⁆ * a := fun h =>
  k.d01 (commutatorElement_eq_one_iff_mul_comm.mpr h)

theorem card_Q : Nat.card ↥Q = 27 := by
  have h27 := ge_27_of_noncomm k.data.Q3 k.aQ k.cQ k.hnc
  have := k.card_Q_le
  omega

theorem extra27 : Extra27 Q where
  card := k.card_Q
  exp := fun x hx => k.D3 x (k.Q_le_D hx)
  cl := fun x hx z hz w hw => (k.Dcl x (k.Q_le_D hx) z hz).2 w (k.Q_le_D hw)
  nc := ⟨a, k.aQ, ⁅a, y⁆, k.cQ, k.hnc⟩

theorem kernel {g : MulAut V} (hg : g ∈ H)
    (hker : ∀ x ∈ Q, ∃ z ∈ Q, (∀ q ∈ Q, z * q = q * z) ∧ g * x * g⁻¹ = x * z) : g ∈ Q := by
  set c : MulAut V := ⁅a, y⁆ with hc
  set d0 : MulAut V := ⁅a, c⁆ with hd0
  have hz : ∀ z ∈ Q, (∀ q ∈ Q, z * q = q * z) → z ∈ Subgroup.zpowers d0 := fun z hzQ hzc =>
    k.extra27.mem_zpowers_commutator k.aQ k.cQ k.hnc hzQ hzc
  obtain ⟨z₁, hz₁Q, hz₁c, hz₁⟩ := hker a k.aQ
  obtain ⟨z₂, hz₂Q, hz₂c, hz₂⟩ := hker c k.cQ
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hz z₁ hz₁Q hz₁c)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hz z₂ hz₂Q hz₂c)
  have haH : a ∈ H := k.data.QH k.aQ
  have hcH : c ∈ H := k.data.QH k.cQ
  have hd0a : a * d0 = d0 * a := k.d0H a haH
  have hd0c : c * d0 = d0 * c := k.d0H c hcH
  have hd0def : d0 = a * c * a⁻¹ * c⁻¹ := by rw [hd0, commutatorElement_def]
  have hac : a * c * a⁻¹ = d0 * c := by rw [hd0def]; group
  have hca : c * a * c⁻¹ = d0⁻¹ * a := by rw [hd0def]; group
  have hcd : c * d0⁻¹ = d0⁻¹ * c := (Commute.inv_right (show Commute c d0 from hd0c)).eq
  have hA : ∀ n : ℤ, a ^ n * c * a ^ (-n) = d0 ^ n * c := zpow_conj_of_comm hac hd0a
  have hC : ∀ m : ℤ, c ^ m * a * c ^ (-m) = (d0⁻¹) ^ m * a := zpow_conj_of_comm hca hcd
  have hAd : Commute a d0 := hd0a
  set r₀ : MulAut V := a ^ j * c ^ (-i) with hr₀
  have hr₀Q : r₀ ∈ Q := Q.mul_mem (Q.zpow_mem k.aQ j) (Q.zpow_mem k.cQ (-i))
  have hr₀a : r₀ * a * r₀⁻¹ = g * a * g⁻¹ := by
    have h1 := hC (-i)
    rw [neg_neg] at h1
    have h2 : r₀ * a * r₀⁻¹ = a ^ j * (c ^ (-i) * a * c ^ i) * a ^ (-j) := by rw [hr₀]; group
    have h3 : (d0⁻¹) ^ (-i) = d0 ^ i := by simp
    have h4 : a ^ j * (d0 ^ i * a) * a ^ (-j) = d0 ^ i * a := by
      have : a ^ j * d0 ^ i = d0 ^ i * a ^ j := (Commute.zpow_zpow hAd j i).eq
      calc a ^ j * (d0 ^ i * a) * a ^ (-j) = (a ^ j * d0 ^ i) * a * a ^ (-j) := by group
        _ = (d0 ^ i * a ^ j) * a * a ^ (-j) := by rw [this]
        _ = d0 ^ i * a := by group
    rw [h2, h1, h3, h4, hz₁, ← hi]
    exact (Commute.zpow_right hAd i).eq.symm
  have hr₀c : r₀ * c * r₀⁻¹ = g * c * g⁻¹ := by
    have h2 : r₀ * c * r₀⁻¹ = a ^ j * c * a ^ (-j) := by rw [hr₀]; group
    have hcc : Commute c d0 := hd0c
    rw [h2, hA j, hz₂, ← hj]
    exact (Commute.zpow_right hcc j).eq.symm
  set k0 : MulAut V := r₀⁻¹ * g with hk0
  have hk0a : k0 * a = a * k0 := by
    have : k0 * a * k0⁻¹ = a := by
      calc k0 * a * k0⁻¹ = r₀⁻¹ * (g * a * g⁻¹) * r₀ := by rw [hk0]; group
        _ = r₀⁻¹ * (r₀ * a * r₀⁻¹) * r₀ := by rw [hr₀a]
        _ = a := by group
    calc k0 * a = (k0 * a * k0⁻¹) * k0 := by group
      _ = a * k0 := by rw [this]
  have hk0c : k0 * c = c * k0 := by
    have : k0 * c * k0⁻¹ = c := by
      calc k0 * c * k0⁻¹ = r₀⁻¹ * (g * c * g⁻¹) * r₀ := by rw [hk0]; group
        _ = r₀⁻¹ * (r₀ * c * r₀⁻¹) * r₀ := by rw [hr₀c]
        _ = c := by group
    calc k0 * c = (k0 * c * k0⁻¹) * k0 := by group
      _ = c * k0 := by rw [this]
  have hQle : Q ≤ Subgroup.centralizer ({k0} : Set (MulAut V)) := by
    rw [k.Q_eq, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
      rw [Set.mem_singleton_iff] at hh
      rw [hh]; exact hk0a
    · refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
      rw [Set.mem_singleton_iff] at hh
      rw [hh]; exact hk0c
  have hk0H : k0 ∈ H := H.mul_mem (H.inv_mem (k.data.QH hr₀Q)) hg
  have hk0Q : k0 ∈ Q := k.data.Qcent k0 hk0H fun q hq =>
    Subgroup.mem_centralizer_iff.mp (hQle hq) k0 (Set.mem_singleton _)
  have : g = r₀ * k0 := by rw [hk0]; group
  rw [this]
  exact Q.mul_mem hr₀Q hk0Q

theorem mem_normalizer_T {t : MulAut V} (ht : t ∈ T) :
    t ∈ Subgroup.normalizer (Q : Set (MulAut V)) := by
  have hle : conjSub t Q ≤ Q := by
    refine k.data.Qmax (conjSub t Q) ?_ ?_ ?_
    · intro x hx
      obtain ⟨q, hq, rfl⟩ := mem_conjSub.mp hx
      exact (k.data.tN t ht q).mp (k.data.QH hq)
    · intro h hh n hn
      obtain ⟨q, hq, rfl⟩ := mem_conjSub.mp hn
      have hh' : t⁻¹ * h * t ∈ H := by
        simpa using (k.data.tN t⁻¹ (T.inv_mem ht) h).mp hh
      have := k.data.Qnorm _ hh' q hq
      refine mem_conjSub.mpr ⟨_, this, ?_⟩
      group
    · exact k.data.Q3.map (MulAut.conj t).toMonoidHom
  have heq : conjSub t Q = Q := Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSub])
  refine Subgroup.mem_normalizer_iff.mpr fun q =>
    ⟨fun hq => hle (conj_mem_conjSub hq), fun hq => ?_⟩
  have h1 : t * q * t⁻¹ ∈ conjSub t Q := by rw [heq]; exact hq
  obtain ⟨q', hq', hqq⟩ := mem_conjSub.mp h1
  have : q' = q := by simpa using hqq
  exact this ▸ hq'

theorem comm_mem {t h : MulAut V} (ht : t ∈ T) (hh : h ∈ H) : t * h * t⁻¹ * h⁻¹ ∈ Q := by
  obtain ⟨ψ, hψ⟩ := k.extra27.exists_psi
  have htN := k.mem_normalizer_T ht
  have hhN := k.data.mem_normalizer_Q hh
  have hyH : y ∈ H := k.data.yH k.hy
  have hyN := k.data.mem_normalizer_Q hyH
  have hu1 : ψ ⟨y, hyN⟩ ≠ 1 := fun e => k.hyQ (k.kernel hyH ((hψ ⟨y, hyN⟩).mp e))
  have hu3 : ψ ⟨y, hyN⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨y, hyN⟩ : Subgroup.normalizer (Q : Set (MulAut V))) ^ 3 = 1 :=
      Subtype.ext (by simpa using k.data.sec.pow_three k.hy)
    rw [this, map_one]
  have hty : t * y = y * t := Subgroup.mem_centralizer_iff.mp (k.data.sec.yle k.hy).2 t ht
  have hτu : ψ ⟨t, htN⟩ * ψ ⟨y, hyN⟩ = ψ ⟨y, hyN⟩ * ψ ⟨t, htN⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg ψ (Subtype.ext hty)
  obtain ⟨m, hm⟩ := k.data.sec.tTwo ⟨t, ht⟩
  have htm : t ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hτm : ψ ⟨t, htN⟩ ^ 2 ^ m = 1 := by
    rw [← map_pow]
    have : (⟨t, htN⟩ : Subgroup.normalizer (Q : Set (MulAut V))) ^ 2 ^ m = 1 :=
      Subtype.ext (by simpa using htm)
    rw [this, map_one]
  have hτ := gl23_two_element_central _ _ hu3 hu1 hτu (gl23_pow_sixteen hτm)
  have hcent : ∀ ρ : GL (Fin 2) (ZMod 3), ψ ⟨t, htN⟩ * ρ = ρ * ψ ⟨t, htN⟩ := by
    intro ρ
    rcases hτ with e | e <;> rw [e] <;> simp
  have hgH : t * h * t⁻¹ * h⁻¹ ∈ H :=
    H.mul_mem ((k.data.tN t ht h).mp hh) (H.inv_mem hh)
  set G0 : Subgroup.normalizer (Q : Set (MulAut V)) :=
    ⟨t, htN⟩ * ⟨h, hhN⟩ * ⟨t, htN⟩⁻¹ * ⟨h, hhN⟩⁻¹ with hG0
  have hG01 : ψ G0 = 1 := by
    rw [hG0, map_mul, map_mul, map_mul, map_inv, map_inv, hcent (ψ ⟨h, hhN⟩)]
    group
  have hker := (hψ G0).mp hG01
  exact k.kernel hgH (by simpa [hG0] using hker)

end Cfg55

end CFSG.CGT.PushingUpLit.CGT6E
