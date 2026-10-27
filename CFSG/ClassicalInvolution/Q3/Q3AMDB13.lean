module

public import CFSG.ClassicalInvolution.Q3.Q3AMDB10
public import CFSG.ClassicalInvolution.Q3.Q3AMDB01

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3CP
open scoped commutatorElement

section Elementary

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_sq_eq_one_of_mem_odd {N : Subgroup G} (hN : Odd (Nat.card N)) {x : G}
    (hx : x ∈ N) (hx2 : x * x = 1) : x = 1 := by
  by_cases hx1 : x = 1
  · exact hx1
  · exact eq_one_of_isPGroup_of_mem_odd hN hx (isPGroup_zpowers_of_mul_self_eq_one hx2 hx1)

theorem eq_of_commute_of_mul_mem_odd {N : Subgroup G} (hN : Odd (Nat.card N)) {a b : G}
    (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) (h : a * b ∈ N) : a = b := by
  have h2 : (a * b) * (a * b) = 1 := by
    calc (a * b) * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha, hb, one_mul]
  have h1 := eq_one_of_sq_eq_one_of_mem_odd hN h h2
  have h3 : a = b⁻¹ := mul_eq_one_iff_eq_inv.mp h1
  rw [h3, inv_eq_of_mul_eq_one_right hb]

theorem exists_pow_eq_conj_of_odd {N : Subgroup G} (hN : Odd (Nat.card N)) {l x : G}
    (hl : l * l = 1) (hlN : ∀ n ∈ N, l * n * l⁻¹ ∈ N) (hx : x ∈ N) :
    ∃ (k : ℕ) (y : G), y ∈ N ∧ Odd k ∧ (x⁻¹ * l) ^ k = y * l * y⁻¹ := by
  have hl' : l⁻¹ = l := inv_eq_of_mul_eq_one_right hl
  have hgg : (x⁻¹ * l) * (x⁻¹ * l) ∈ N := by
    have h1 := hlN x⁻¹ (N.inv_mem hx)
    have e : (x⁻¹ * l) * (x⁻¹ * l) = x⁻¹ * (l * x⁻¹ * l⁻¹) := by
      rw [hl']
      group
    rw [e]
    exact N.mul_mem (N.inv_mem hx) h1
  have hodd : Odd (orderOf ((x⁻¹ * l) * (x⁻¹ * l))) :=
    hN.of_dvd_nat (Subgroup.orderOf_dvd_natCard N hgg)
  obtain ⟨j, hj⟩ := hodd
  refine ⟨orderOf ((x⁻¹ * l) * (x⁻¹ * l)), ?_⟩
  set g := x⁻¹ * l with hg
  have hgk : g ^ (orderOf (g * g)) = g * (g * g) ^ j := by
    rw [hj, pow_succ', pow_mul, pow_two]
  have hkk : (g ^ (orderOf (g * g))) * (g ^ (orderOf (g * g))) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, pow_two, pow_orderOf_eq_one]
  have hmem : l⁻¹ * g ^ (orderOf (g * g)) ∈ N := by
    rw [hgk, hg, hl']
    have h2 : l * x⁻¹ * l ∈ N := by
      have := hlN x⁻¹ (N.inv_mem hx)
      rwa [hl'] at this
    have e : l * (x⁻¹ * l * (x⁻¹ * l * (x⁻¹ * l)) ^ j) = (l * x⁻¹ * l) * ((x⁻¹ * l) * (x⁻¹ * l)) ^ j
      := by group
    rw [e]
    exact N.mul_mem h2 (N.pow_mem hgg j)
  obtain ⟨y, hy, hyl⟩ := exists_conj_of_inv_mul_mem_odd hN hl hkk hmem
  exact ⟨y, hy, ⟨j, hj⟩, hyl⟩

theorem conj_pow_odd {g t u : G} (hgt : g * t * g⁻¹ = u) (hgu : (g * g) * u = u * (g * g))
    {k : ℕ} (hk : Odd k) : g ^ k * t * (g ^ k)⁻¹ = u := by
  obtain ⟨j, rfl⟩ := hk
  have hc : Commute ((g * g) ^ j) u := (Commute.pow_left hgu j)
  have e : g ^ (2 * j + 1) * t * (g ^ (2 * j + 1))⁻¹ =
      (g * g) ^ j * (g * t * g⁻¹) * ((g * g) ^ j)⁻¹ := by
    rw [pow_succ, pow_mul, pow_two]
    group
  rw [e, hgt]
  have := hc.eq
  rw [mul_inv_eq_iff_eq_mul]
  exact this

end Elementary

section Normalize


variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
  {K J K' : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem PspSetting.conj_mem_oddCore_nbrLayer (hset : PspSetting Ω K J S R T W z t K') {c : G}
    (hc : c ∈ Subgroup.centralizer ({z} : Set G)) {n : G}
    (hn : n ∈ oddCoreOf (nbrLayer Ω K z)) : c * n * c⁻¹ ∈ oddCoreOf (nbrLayer Ω K z) := by
  have hΩ : HypOmegaMod Ω := hset.bad.std.stand.hyp
  have hNC : Subgroup.normalizer (K : Set G) = Subgroup.centralizer ({z} : Set G) :=
    hset.bad.normalizer_eq_centralizer
  have hCM : ∀ g ∈ Subgroup.centralizer ({z} : Set G), conjSub g K = K := fun g hg =>
    mem_normalizer_iff_conjSub_eq.mp (by rw [hNC]; exact hg)
  refine conj_mem_oddCoreOf_of_mem_normalizer (fun y hy => conj_mem_nbrLayer hΩ hCM hc hy)
    (fun y hy => ?_) hn
  have := conj_mem_nbrLayer hΩ hCM (Subgroup.inv_mem _ hc) hy
  rwa [inv_inv] at this

theorem oddCore_nbrLayer_comm {n : G} (hn : n ∈ oddCoreOf (nbrLayer Ω K z)) : n * z = z * n :=
  Subgroup.mem_centralizer_singleton_iff.mp
    (nbrLayer_le_centralizer Ω K z (oddCoreOf_le_self _ hn))

theorem PspSetting.t_mem_centralizer (hset : PspSetting Ω K J S R T W z t K') :
    t ∈ Subgroup.centralizer ({z} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.mpr hset.mul_comm_zt.symm

theorem PspSetting.mul_mem_centralizer (hset : PspSetting Ω K J S R T W z t K') :
    z * t ∈ Subgroup.centralizer ({z} : Set G) := by
  refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
  rw [mul_assoc, ← hset.mul_comm_zt]

theorem PspSetting.nbr_involution_mem_coset (hset : PspSetting Ω K J S R T W z t K')
    (hD : PspNbhdDouble Ω K z) {N : Subgroup G} (hN : N ∈ omegaNbr Ω K) {w : G}
    (hw : IsUniqueInvolution N w) :
    ∃ n ∈ oddCoreOf (nbrLayer Ω K z), w = n * t ∨ w = n * (z * t) := by
  obtain ⟨x, hx, h | h⟩ := hset.nbr_involution_conj hD hN hw
  · refine ⟨x * (t * x⁻¹ * t⁻¹), (oddCoreOf _).mul_mem hx
      (hset.conj_mem_oddCore_nbrLayer hset.t_mem_centralizer ((oddCoreOf _).inv_mem hx)),
      Or.inl ?_⟩
    rw [h]
    group
  · refine ⟨x * ((z * t) * x⁻¹ * (z * t)⁻¹), (oddCoreOf _).mul_mem hx
      (hset.conj_mem_oddCore_nbrLayer hset.mul_mem_centralizer ((oddCoreOf _).inv_mem hx)),
      Or.inr ?_⟩
    rw [h]
    group

theorem PspSetting.mul_eq_z_of_mixed (hset : PspSetting Ω K J S R T W z t K') {n₁ n₂ a b : G}
    (hn₁ : n₁ ∈ oddCoreOf (nbrLayer Ω K z)) (hn₂ : n₂ ∈ oddCoreOf (nbrLayer Ω K z))
    (ha : a = n₁ * t) (hb : b = n₂ * (z * t)) (ha2 : a * a = 1) (hb2 : b * b = 1)
    (hab : a * b = b * a) (haz : a * z = z * a) (hbz : b * z = z * b) : a * b = z := by
  have hstd := hset.bad.std
  have hodd := oddCoreOf_odd_natCard (nbrLayer Ω K z)
  have hzt := hset.mul_comm_zt
  have ht2 : t * t = 1 := hstd.ht.sq
  have hz2 : z * z = 1 := hstd.hz.sq
  have htzt : t * z * t = z := by rw [← hzt, mul_assoc, ht2, mul_one]
  have hab2 : (a * b) * (a * b) = 1 := by
    calc (a * b) * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha2, hb2, one_mul]
  have hcomm : z * (a * b) = (a * b) * z := by
    calc z * (a * b) = (z * a) * b := by group
      _ = (a * z) * b := by rw [haz]
      _ = a * (z * b) := by group
      _ = a * (b * z) := by rw [hbz]
      _ = (a * b) * z := by group
  have e : a * b = (n₁ * (t * n₂ * t⁻¹)) * z := by
    calc a * b = (n₁ * t) * (n₂ * (z * t)) := by rw [ha, hb]
      _ = n₁ * (t * n₂ * t⁻¹) * (t * z * t) := by group
      _ = n₁ * (t * n₂ * t⁻¹) * z := by rw [htzt]
  have hmem : z * (a * b) ∈ oddCoreOf (nbrLayer Ω K z) := by
    have h1 : n₁ * (t * n₂ * t⁻¹) ∈ oddCoreOf (nbrLayer Ω K z) :=
      (oddCoreOf _).mul_mem hn₁ (hset.conj_mem_oddCore_nbrLayer hset.t_mem_centralizer hn₂)
    have h2 := hset.conj_mem_oddCore_nbrLayer
      (Subgroup.mem_centralizer_singleton_iff.mpr rfl : z ∈ Subgroup.centralizer ({z} : Set G)) h1
    have hz' : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
    have e2 : z * (a * b) = z * (n₁ * (t * n₂ * t⁻¹)) * z⁻¹ := by
      rw [e, hz']
      group
    rw [e2]
    exact h2
  exact (eq_of_commute_of_mul_mem_odd hodd hz2 hab2 hcomm hmem).symm

theorem PspSetting.pair_of_nbr_involutions (hset : PspSetting Ω K J S R T W z t K')
    (hD : PspNbhdDouble Ω K z) {N₁ N₂ : Subgroup G} (h1 : N₁ ∈ omegaNbr Ω K)
    (h2 : N₂ ∈ omegaNbr Ω K) {a b : G} (ha : IsUniqueInvolution N₁ a)
    (hb : IsUniqueInvolution N₂ b) (hab : a * b = b * a) : a = b ∨ a * b = z := by
  have hstd := hset.bad.std
  have hΩ : HypOmegaMod Ω := hstd.stand.hyp
  have hodd := oddCoreOf_odd_natCard (nbrLayer Ω K z)
  have hzt := hset.mul_comm_zt
  have ht2 : t * t = 1 := hstd.ht.sq
  have hz2 : z * z = 1 := hstd.hz.sq
  have hut2 : (z * t) * (z * t) = 1 := by
    calc (z * t) * (z * t) = z * (t * z) * t := by group
      _ = z * (z * t) * t := by rw [hzt]
      _ = (z * z) * (t * t) := by group
      _ = 1 := by rw [hz2, ht2, one_mul]
  have haz : a * z = z * a := (Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hstd.hz h1 ha).symm
  have hbz : b * z = z * b := (Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hstd.hz h2 hb).symm
  obtain ⟨n₁, hn₁, ha'⟩ := hset.nbr_involution_mem_coset hD h1 ha
  obtain ⟨n₂, hn₂, hb'⟩ := hset.nbr_involution_mem_coset hD h2 hb
  rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb'
  · left
    refine eq_of_commute_of_mul_mem_odd hodd ha.sq hb.sq hab ?_
    have e : a * b = n₁ * (t * n₂ * t⁻¹) := by
      rw [ha', hb']
      calc n₁ * t * (n₂ * t) = n₁ * (t * n₂ * t⁻¹) * (t * t) := by group
        _ = n₁ * (t * n₂ * t⁻¹) := by rw [ht2, mul_one]
    rw [e]
    exact (oddCoreOf _).mul_mem hn₁ (hset.conj_mem_oddCore_nbrLayer hset.t_mem_centralizer hn₂)
  · exact Or.inr (hset.mul_eq_z_of_mixed hn₁ hn₂ ha' hb' ha.sq hb.sq hab haz hbz)
  · right
    have := hset.mul_eq_z_of_mixed hn₂ hn₁ hb' ha' hb.sq ha.sq hab.symm hbz haz
    rw [hab]
    exact this
  · left
    refine eq_of_commute_of_mul_mem_odd hodd ha.sq hb.sq hab ?_
    have e : a * b = n₁ * ((z * t) * n₂ * (z * t)⁻¹) := by
      rw [ha', hb']
      calc n₁ * (z * t) * (n₂ * (z * t)) =
          n₁ * ((z * t) * n₂ * (z * t)⁻¹) * ((z * t) * (z * t)) := by group
        _ = n₁ * ((z * t) * n₂ * (z * t)⁻¹) := by rw [hut2, mul_one]
    rw [e]
    exact (oddCoreOf _).mul_mem hn₁
      (hset.conj_mem_oddCore_nbrLayer hset.mul_mem_centralizer hn₂)

theorem PspSetting.exists_normalized_partner (hset : PspSetting Ω K J S R T W z t K')
    (hD : PspNbhdDouble Ω K z) {L : Subgroup G} (hL : L ∈ Ω) {l : G}
    (hl : IsUniqueInvolution L l) (hlz : l ≠ z) (hcomm : l * z = z * l) :
    ∃ (L' : Subgroup G) (e : G), L' ∈ Ω ∧ IsUniqueInvolution L' e ∧ e ≠ z ∧ e * z = z * e ∧
      ((¬ ∃ P : Subgroup G, IsSylow2In P L ∧ P ≤ Subgroup.centralizer ({z} : Set G)) →
        ¬ ∃ P : Subgroup G, IsSylow2In P L' ∧ P ≤ Subgroup.centralizer ({z} : Set G)) ∧
      (e * t = t * e ∨ e * t * e⁻¹ = z * t) := by
  have hstd := hset.bad.std
  have hΩ : HypOmegaMod Ω := hstd.stand.hyp
  have hNC : Subgroup.normalizer (K : Set G) = Subgroup.centralizer ({z} : Set G) :=
    hset.bad.normalizer_eq_centralizer
  have hz2 : z * z = 1 := hstd.hz.sq
  have hlC : l ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm
  have hCM : ∀ g ∈ Subgroup.centralizer ({z} : Set G), conjSub g K = K := fun g hg =>
    mem_normalizer_iff_conjSub_eq.mp (by rw [hNC]; exact hg)
  have hodd := oddCoreOf_odd_natCard (nbrLayer Ω K z)
  have hJl : conjSub l J ∈ omegaNbr Ω K :=
    conjSub_mem_omegaNbr_of_conjSub_eq hΩ (hCM l hlC) hstd.hJ
  have hwl : IsUniqueInvolution (conjSub l J) (l * t * l⁻¹) := hstd.ht.conj l
  obtain ⟨x, hx, hcase⟩ := hset.nbr_involution_conj hD hJl hwl
  have hxC : x ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (oddCore_nbrLayer_comm hx)
  have hgC : x⁻¹ * l ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hxC) hlC
  obtain ⟨k, y, hy, hk, hkey⟩ := exists_pow_eq_conj_of_odd hodd hl.sq
    (fun n hn => hset.conj_mem_oddCore_nbrLayer hlC hn) hx
  have hyz : y * z = z * y := oddCore_nbrLayer_comm hy
  have hyzc : y * z * y⁻¹ = z := by
    rw [mul_inv_eq_iff_eq_mul]
    exact hyz
  refine ⟨conjSub y L, y * l * y⁻¹, hΩ.conjInvariant y L hL, hl.conj y, ?_, ?_, ?_, ?_⟩
  · intro h
    apply hlz
    calc l = y⁻¹ * (y * l * y⁻¹) * y := by group
      _ = y⁻¹ * z * y := by rw [h]
      _ = z := by
        calc y⁻¹ * z * y = y⁻¹ * (z * y) := by group
          _ = y⁻¹ * (y * z) := by rw [← hyz]
          _ = z := inv_mul_cancel_left y z
  · have := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.pow_mem _ hgC k)
    rw [hkey] at this
    exact this
  · rintro hno ⟨P, hP, hPC⟩
    apply hno
    refine ⟨conjSub y⁻¹ P, ?_, ?_⟩
    · have := IsSylow2In.conj hP y⁻¹
      rwa [conjSub_inv_conjSub] at this
    · intro w hw
      rw [mem_conjSub_iff, inv_inv] at hw
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hPC hw)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have e1 : w * z = y⁻¹ * ((y * w * y⁻¹) * z) * y := by
        calc w * z = y⁻¹ * ((y * w * y⁻¹) * (y * z * y⁻¹)) * y := by group
          _ = y⁻¹ * ((y * w * y⁻¹) * z) * y := by rw [hyzc]
      have e2 : z * w = y⁻¹ * (z * (y * w * y⁻¹)) * y := by
        calc z * w = y⁻¹ * ((y * z * y⁻¹) * (y * w * y⁻¹)) * y := by group
          _ = y⁻¹ * (z * (y * w * y⁻¹)) * y := by rw [hyzc]
      rw [e1, e2, h1]
  · rcases hcase with h | h
    · left
      have hgt : (x⁻¹ * l) * t * (x⁻¹ * l)⁻¹ = t := by
        calc (x⁻¹ * l) * t * (x⁻¹ * l)⁻¹ = x⁻¹ * (l * t * l⁻¹) * x := by group
          _ = x⁻¹ * (x * t * x⁻¹) * x := by rw [h]
          _ = t := by group
      have hcg : (x⁻¹ * l) * t = t * (x⁻¹ * l) := mul_inv_eq_iff_eq_mul.mp hgt
      have hgu : ((x⁻¹ * l) * (x⁻¹ * l)) * t = t * ((x⁻¹ * l) * (x⁻¹ * l)) := by
        calc ((x⁻¹ * l) * (x⁻¹ * l)) * t = (x⁻¹ * l) * ((x⁻¹ * l) * t) := by group
          _ = (x⁻¹ * l) * (t * (x⁻¹ * l)) := by rw [hcg]
          _ = ((x⁻¹ * l) * t) * (x⁻¹ * l) := by group
          _ = (t * (x⁻¹ * l)) * (x⁻¹ * l) := by rw [hcg]
          _ = t * ((x⁻¹ * l) * (x⁻¹ * l)) := by group
      have := conj_pow_odd hgt hgu hk
      rw [hkey] at this
      exact mul_inv_eq_iff_eq_mul.mp this
    · right
      have hgz : (x⁻¹ * l) * z = z * (x⁻¹ * l) := Subgroup.mem_centralizer_singleton_iff.mp hgC
      have hgt : (x⁻¹ * l) * t * (x⁻¹ * l)⁻¹ = z * t := by
        calc (x⁻¹ * l) * t * (x⁻¹ * l)⁻¹ = x⁻¹ * (l * t * l⁻¹) * x := by group
          _ = x⁻¹ * (x * (z * t) * x⁻¹) * x := by rw [h]
          _ = z * t := by group
      have hg1 : (x⁻¹ * l) * t = (z * t) * (x⁻¹ * l) := mul_inv_eq_iff_eq_mul.mp hgt
      have hg2t : ((x⁻¹ * l) * (x⁻¹ * l)) * t = t * ((x⁻¹ * l) * (x⁻¹ * l)) := by
        calc ((x⁻¹ * l) * (x⁻¹ * l)) * t = (x⁻¹ * l) * ((x⁻¹ * l) * t) := by group
          _ = (x⁻¹ * l) * ((z * t) * (x⁻¹ * l)) := by rw [hg1]
          _ = ((x⁻¹ * l) * z) * t * (x⁻¹ * l) := by group
          _ = (z * (x⁻¹ * l)) * t * (x⁻¹ * l) := by rw [hgz]
          _ = z * ((x⁻¹ * l) * t) * (x⁻¹ * l) := by group
          _ = z * ((z * t) * (x⁻¹ * l)) * (x⁻¹ * l) := by rw [hg1]
          _ = (z * z) * t * ((x⁻¹ * l) * (x⁻¹ * l)) := by group
          _ = t * ((x⁻¹ * l) * (x⁻¹ * l)) := by rw [hz2, one_mul]
      have hgu : ((x⁻¹ * l) * (x⁻¹ * l)) * (z * t) = (z * t) * ((x⁻¹ * l) * (x⁻¹ * l)) := by
        have hg2z : ((x⁻¹ * l) * (x⁻¹ * l)) * z = z * ((x⁻¹ * l) * (x⁻¹ * l)) := by
          calc ((x⁻¹ * l) * (x⁻¹ * l)) * z = (x⁻¹ * l) * ((x⁻¹ * l) * z) := by group
            _ = (x⁻¹ * l) * (z * (x⁻¹ * l)) := by rw [hgz]
            _ = ((x⁻¹ * l) * z) * (x⁻¹ * l) := by group
            _ = (z * (x⁻¹ * l)) * (x⁻¹ * l) := by rw [hgz]
            _ = z * ((x⁻¹ * l) * (x⁻¹ * l)) := by group
        calc ((x⁻¹ * l) * (x⁻¹ * l)) * (z * t) = (((x⁻¹ * l) * (x⁻¹ * l)) * z) * t := by group
          _ = (z * ((x⁻¹ * l) * (x⁻¹ * l))) * t := by rw [hg2z]
          _ = z * (((x⁻¹ * l) * (x⁻¹ * l)) * t) := by group
          _ = z * (t * ((x⁻¹ * l) * (x⁻¹ * l))) := by rw [hg2t]
          _ = (z * t) * ((x⁻¹ * l) * (x⁻¹ * l)) := by group
      have := conj_pow_odd hgt hgu hk
      rw [hkey] at this
      exact this

theorem PspSetting.mul_eq_of_mem_omegaNbr_vertex (hset : PspSetting Ω K J S R T W z t K')
    (hD : PspNbhdDouble Ω K z) {M : Subgroup G} (hM : M ∈ Ω) (hMK : M ∈ omegaNbr Ω K) {m : G}
    (hm : IsUniqueInvolution M m) {L : Subgroup G} (hLM : L ∈ omegaNbr Ω M) {e : G}
    (he : IsUniqueInvolution L e) (hez : e ≠ z) (hcomm : e * z = z * e) : e * z = m := by
  have hstd := hset.bad.std
  have hΩ : HypOmegaMod Ω := hstd.stand.hyp
  obtain ⟨g, hg⟩ := hstd.stand.trans M hM
  have hmg : m = g * z * g⁻¹ := hm.eq (by rw [← hg]; exact hstd.hz.conj g)
  have hKM : K ∈ omegaNbr Ω M :=
    Q3CL.T3.omegaNbr_symm AschTight.Sec6Gen.l6_2Gen hΩ hstd.stand.mem hM hMK
  have hL₁ : conjSub g⁻¹ L ∈ omegaNbr Ω K := by
    have := omegaNbr_conj hΩ.conjInvariant hLM g⁻¹
    rwa [← hg, conjSub_inv_conjSub] at this
  have hK₁ : conjSub g⁻¹ K ∈ omegaNbr Ω K := by
    have := omegaNbr_conj hΩ.conjInvariant hKM g⁻¹
    rwa [← hg, conjSub_inv_conjSub] at this
  have he₁ : IsUniqueInvolution (conjSub g⁻¹ L) (g⁻¹ * e * g) := by
    simpa using he.conj g⁻¹
  have hz₁ : IsUniqueInvolution (conjSub g⁻¹ K) (g⁻¹ * z * g) := by
    simpa using hstd.hz.conj g⁻¹
  have hc₁ : (g⁻¹ * e * g) * (g⁻¹ * z * g) = (g⁻¹ * z * g) * (g⁻¹ * e * g) := by
    calc (g⁻¹ * e * g) * (g⁻¹ * z * g) = g⁻¹ * (e * z) * g := by group
      _ = g⁻¹ * (z * e) * g := by rw [hcomm]
      _ = (g⁻¹ * z * g) * (g⁻¹ * e * g) := by group
  rcases hset.pair_of_nbr_involutions hD hL₁ hK₁ he₁ hz₁ hc₁ with h | h
  · exfalso
    apply hez
    calc e = g * (g⁻¹ * e * g) * g⁻¹ := by group
      _ = g * (g⁻¹ * z * g) * g⁻¹ := by rw [h]
      _ = z := by group
  · rw [hmg]
    calc e * z = g * ((g⁻¹ * e * g) * (g⁻¹ * z * g)) * g⁻¹ := by group
      _ = g * z * g⁻¹ := by rw [h]

theorem PspSetting.not_mem_omegaNbr_J (hset : PspSetting Ω K J S R T W z t K')
    (hD : PspNbhdDouble Ω K z) {L : Subgroup G} (hL : L ∈ Ω) {e : G}
    (he : IsUniqueInvolution L e) (hez : e ≠ z) (hcomm : e * z = z * e)
    (hLK : L ∉ omegaNbr Ω K) : L ∉ omegaNbr Ω J := by
  intro hLJ
  have hstd := hset.bad.std
  have hzt := hset.mul_comm_zt
  have h1 := hset.mul_eq_of_mem_omegaNbr_vertex hD hstd.hJ.1 hstd.hJ hstd.ht hLJ he hez hcomm
  have hez' : e = z * t := by
    rw [eq_mul_inv_of_mul_eq h1, inv_eq_of_mul_eq_one_right hstd.hz.sq, ← hzt]
  have hLK' : L = K' :=
    hset.noTwins_all hset.nbrK.1 L ⟨hL, z * t, hset.uniq_mul, hez' ▸ he⟩
  exact hLK (hLK' ▸ hset.nbrK)

theorem PspSetting.not_mem_omegaNbr_K' (hset : PspSetting Ω K J S R T W z t K')
    (hD : PspNbhdDouble Ω K z) {L : Subgroup G} (hL : L ∈ Ω) {e : G}
    (he : IsUniqueInvolution L e) (hez : e ≠ z) (hcomm : e * z = z * e)
    (hLK : L ∉ omegaNbr Ω K) : L ∉ omegaNbr Ω K' := by
  intro hLK'
  have hstd := hset.bad.std
  have hzt := hset.mul_comm_zt
  have hz2 : z * z = 1 := hstd.hz.sq
  have h1 := hset.mul_eq_of_mem_omegaNbr_vertex hD hset.nbrK.1 hset.nbrK hset.uniq_mul hLK' he hez
    hcomm
  have hez' : e = t := by
    rw [eq_mul_inv_of_mul_eq h1, inv_eq_of_mul_eq_one_right hz2]
    calc z * t * z = z * (t * z) := by group
      _ = z * (z * t) := by rw [hzt]
      _ = (z * z) * t := by group
      _ = t := by rw [hz2, one_mul]
  have hLJ : L = J := hset.noTwins_all hstd.hJ.1 L ⟨hL, t, hstd.ht, hez' ▸ he⟩
  exact hLK (hLJ ▸ hstd.hJ)

end Normalize

end CFSG.ClassicalInvolution.Q3.Q3AM
