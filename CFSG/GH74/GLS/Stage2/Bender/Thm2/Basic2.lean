module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Basic
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Defs
public import CFSG.GH74.GLS.Stage2.Local.Bar
public import CFSG.GH74.GLS.Stage2.Local.Basic

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

section Comm

variable {G : Type} [Group G]

theorem map_conj_eq_of_mem_normalizer {A : Subgroup G} {g : G} (hg : g ∈ normalizer (A : Set G)) :
    A.map (MulAut.conj g).toMonoidHom = A := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg a).mp ha
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, by simp [mul_assoc]⟩
    have h := (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * x * g)).mpr
    apply h
    simpa [mul_assoc] using hx

theorem mem_normalizer_commutator {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  have h1 := Subgroup.map_commutator A B (MulAut.conj g).toMonoidHom
  rw [map_conj_eq_of_mem_normalizer hA, map_conj_eq_of_mem_normalizer hB] at h1
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h1]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h1] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := (MulAut.conj g).injective hyx
    rw [← this]
    exact hy

theorem commutator_le_of_normalizes {H K : Subgroup G} (h : K ≤ normalizer (H : Set G)) : ⁅H, K⁆ ≤ H := by
  rw [Subgroup.commutator_le]
  intro h₁ hh₁ h₂ hh₂
  have : h₂ * h₁⁻¹ * h₂⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp (h hh₂) h₁⁻¹).mp (inv_mem hh₁)
  have h3 : ⁅h₁, h₂⁆ = h₁ * (h₂ * h₁⁻¹ * h₂⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [h3]
  exact mul_mem hh₁ this

theorem eq_one_or_eq_of_mem_zpowers {z w : G} (hz : z * z = 1) (hw : w ∈ zpowers z) : w = 1 ∨ w = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have h2 : z ^ (2 : ℕ) = 1 := by simpa [pow_two] using hz
  have hd : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2'
  · left
    have : z = 1 := orderOf_eq_one_iff.mp h1
    rw [this, one_zpow]
  · rw [← zpow_mod_orderOf, h2']
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      simp [h]
    · right
      simp [h]

theorem comm_comm_eq_of_odd {A : Subgroup G} {z : G} (hz : z * z = 1) (hn : z ∈ normalizer (A : Set G))
    (hodd : ∀ a ∈ A, Odd (orderOf a)) : ⁅⁅A, zpowers z⁆, zpowers z⁆ = ⁅A, zpowers z⁆ := by
  have hzB : z ∈ normalizer ((⁅A, zpowers z⁆ : Subgroup G) : Set G) :=
    mem_normalizer_commutator hn (by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (mem_zpowers z) hx) (inv_mem (mem_zpowers z))
      · intro hx
        have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (inv_mem (mem_zpowers z)) hx) (mem_zpowers z)
        simpa [mul_assoc] using this)
  apply le_antisymm
  · exact commutator_le_of_normalizes (Subgroup.zpowers_le.mpr hzB)
  · rw [Subgroup.commutator_le]
    intro a ha w hw
    rcases eq_one_or_eq_of_mem_zpowers hz hw with rfl | rfl
    · simp
    · set b : G := ⁅a, w⁆ with hb
      have hbB : b ∈ ⁅A, zpowers w⁆ := Subgroup.commutator_mem_commutator ha (mem_zpowers w)
      have hzinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hz
      have hbA : b ∈ A := by
        have h1 : w * a⁻¹ * w⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hn a⁻¹).mp (inv_mem ha)
        have h2 : b = a * (w * a⁻¹ * w⁻¹) := by
          simp only [hb, commutatorElement_def]
          group
        rw [h2]
        exact mul_mem ha h1
      have hww : w⁻¹ * w⁻¹ = 1 := by
        rw [← mul_inv_rev, hz, inv_one]
      have hzb : w * b * w⁻¹ = b⁻¹ := by
        calc w * b * w⁻¹ = w * a * w * a⁻¹ * (w⁻¹ * w⁻¹) := by
              simp only [hb, commutatorElement_def]
              group
          _ = w * a * w * a⁻¹ := by rw [hww, mul_one]
          _ = w * a * w⁻¹ * a⁻¹ := by rw [hzinv]
          _ = b⁻¹ := by
              simp only [hb, commutatorElement_def]
              group
      have hbb : ⁅b, w⁆ = b * b := by
        have : ⁅b, w⁆ = b * (w * b * w⁻¹)⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [this, hzb, inv_inv]
      obtain ⟨m, hm⟩ := hodd b hbA
      have hbm : b = (b * b) ^ (m + 1) := by
        have h1 : b ^ (2 * m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one b
        calc b = b ^ (2 * m + 1) * b := by rw [h1, one_mul]
          _ = (b * b) ^ (m + 1) := by rw [← pow_succ, ← pow_two, ← pow_mul]; ring_nf
      have hc : ⁅b, w⁆ ∈ ⁅⁅A, zpowers w⁆, zpowers w⁆ := Subgroup.commutator_mem_commutator hbB (mem_zpowers w)
      rw [hbb] at hc
      have : (b * b) ^ (m + 1) ∈ ⁅⁅A, zpowers w⁆, zpowers w⁆ := pow_mem hc (m + 1)
      rw [← hbm] at this
      exact this

theorem mem_normalizer_inf {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp hA x).mp h1, (Subgroup.mem_normalizer_iff.mp hB x).mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp hA x).mpr h1, (Subgroup.mem_normalizer_iff.mp hB x).mpr h2⟩

theorem mem_normalizer_zpowers_of_comm {z c : G} (hc : c * z = z * c) : c ∈ normalizer ((zpowers z : Subgroup G) : Set G) := by
  have h1 : ∀ k : ℤ, c * z ^ k * c⁻¹ = z ^ k := by
    intro k
    have : Commute c (z ^ k) := (Commute.zpow_right (show Commute c z from hc) k)
    rw [this.eq, mul_inv_cancel_right]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [h1 k]
    exact mem_zpowers_iff.mpr ⟨k, rfl⟩
  · intro hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hx' : x = z ^ k := by
      calc x = c⁻¹ * (c * x * c⁻¹) * c := by group
        _ = c⁻¹ * z ^ k * c := by rw [← hk]
        _ = c⁻¹ * (c * z ^ k * c⁻¹) * c := by rw [h1 k]
        _ = z ^ k := by group
    rw [hx']
    exact mem_zpowers_iff.mpr ⟨k, rfl⟩

theorem cen_le_centralizer_zpowers (z : G) : centralizer ({z} : Set G) ≤ centralizer ((zpowers z : Subgroup G) : Set G) := by
  intro x hx
  have hxz : Commute x z := Subgroup.mem_centralizer_singleton_iff.mp hx
  refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  exact (hxz.zpow_right k).symm.eq

theorem centralizer_zpowers_le (z : G) : centralizer ((zpowers z : Subgroup G) : Set G) ≤ centralizer ({z} : Set G) :=
  Subgroup.centralizer_le (fun x hx => by rw [Set.mem_singleton_iff.mp hx]; exact mem_zpowers z)

theorem odd_orderOf_of_pgroup {p : ℕ} (hp : p.Prime) (hodd : Odd p) {A : Subgroup G} (hA : IsPGroup p ↥A) :
    ∀ a ∈ A, Odd (orderOf a) := by
  have : Fact p.Prime := ⟨hp⟩
  intro a ha
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hA) ⟨a, ha⟩
  rw [Subgroup.orderOf_mk] at hk
  rw [hk]
  exact hodd.pow

end Comm

section Char

variable {G : Type} [Group G]

theorem conj_mem_of_characteristic {P Q : Subgroup G} (hQP : Q ≤ P)
    (hQ : Subgroup.Characteristic (Q.subgroupOf P)) {m : G} (hm : m ∈ normalizer (P : Set G)) {x : G}
    (hx : x ∈ Q) : m * x * m⁻¹ ∈ Q := by
  have hmap := map_conj_eq_of_mem_normalizer hm
  let φ : ↥P ≃* ↥P := (MulEquiv.subgroupMap (MulAut.conj m) P).trans (MulEquiv.subgroupCongr hmap)
  have h1 := hQ.fixed φ
  have hxP : (⟨x, hQP hx⟩ : ↥P) ∈ Q.subgroupOf P := hx
  have hmem : (⟨x, hQP hx⟩ : ↥P) ∈ (Q.subgroupOf P).comap φ.toMonoidHom := by
    rw [h1]
    exact hxP
  rw [Subgroup.mem_comap] at hmem
  exact hmem

theorem mem_normalizer_of_characteristic {P Q : Subgroup G} (hQP : Q ≤ P)
    (hQ : Subgroup.Characteristic (Q.subgroupOf P)) {m : G} (hm : m ∈ normalizer (P : Set G)) :
    m ∈ normalizer (Q : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact fun hx => conj_mem_of_characteristic hQP hQ hm hx
  · intro hx
    have := conj_mem_of_characteristic hQP hQ (inv_mem hm) hx
    simpa [mul_assoc] using this

end Char

section Access

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ}

theorem Ctx9.coatom (h : Ctx9 G z k S M p) : IsCoatom M := h.mem.1

theorem Ctx9.cen_le (h : Ctx9 G z k S M p) : Cen z ≤ M := h.mem.2

theorem Ctx9.z_mem (h : Ctx9 G z k S M p) : z ∈ M := h.cen_le (mem_Cen_self z)

theorem Ctx9.orderOf_z (h : Ctx9 G z k S M p) : orderOf z = 2 := h.ctx.orderOf_z

theorem Ctx9.z_mul_z (h : Ctx9 G z k S M p) : z * z = 1 := by
  have := pow_orderOf_eq_one z
  rw [h.orderOf_z] at this
  simpa [pow_two] using this

theorem Ctx9.S_le_M (h : Ctx9 G z k S M p) : S ≤ M := h.ctx.S_le_Cen.trans h.cen_le

theorem Ctx9.odd_p (h : Ctx9 G z k S M p) : Odd p := h.prime.eq_two_or_odd'.resolve_left h.odd

theorem Ctx9.P_pgroup (_h : Ctx9 G z k S M p) : IsPGroup p ↥(Op p M) := op_isPGroup M

theorem Ctx9.simple (h : Ctx9 G z k S M p) : IsSimpleGroup G := h.ctx.std.kps.1

variable {Q T U : Subgroup G} {t g : G}

theorem Ctx10.Q_le_P (h : Ctx10 G z k S M p Q T U t g) : Q ≤ Op p M := h.Q_mem.1

theorem Ctx10.Q_pgroup (h : Ctx10 G z k S M p Q T U t g) : IsPGroup p ↥Q :=
  h.ctx9.P_pgroup.to_le h.Q_le_P

theorem Ctx10.M_le_normalizer_Q (h : Ctx10 G z k S M p Q T U t g) : M ≤ normalizer (Q : Set G) :=
  fun _ hm => mem_normalizer_of_characteristic h.Q_le_P h.Q_mem.2.1 (le_normalizer_Op' p M hm)

theorem Ctx10.not_Q_le_Cen (h : Ctx10 G z k S M p Q T U t g) : ¬ Q ≤ Cen z := h.Q_mem.2.2.2.2.2

theorem Ctx10.T_le_S (h : Ctx10 G z k S M p Q T U t g) : T ≤ S := by
  by_cases h1 : TypeOneCase G k
  · exact ((h.choice.T_one h1).1).le
  · rw [(h.choice.T_two h1).1]
    exact inf_le_left

theorem Ctx10.T_le_Cen (h : Ctx10 G z k S M p Q T U t g) : T ≤ Cen z := h.T_le_S.trans h.ctx9.ctx.S_le_Cen

theorem Ctx10.T_le_M (h : Ctx10 G z k S M p Q T U t g) : T ≤ M := h.T_le_Cen.trans h.ctx9.cen_le

theorem Ctx10.z_mem_U (h : Ctx10 G z k S M p Q T U t g) : z ∈ U := by
  rw [h.choice.U_gen]
  exact Subgroup.mem_sup_left (mem_zpowers z)

theorem Ctx10.z_mem_T (h : Ctx10 G z k S M p Q T U t g) : z ∈ T := by
  by_cases h1 : TypeOneCase G k
  · rw [(h.choice.T_one h1).1]
    exact h.ctx9.ctx.z_mem
  · rw [(h.choice.T_two h1).1]
    refine ⟨h.ctx9.ctx.z_mem, ?_⟩
    have := h.choice.U_four.1
    refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
    have hc := IsMulCommutative.is_comm.comm (⟨u, hu⟩ : ↥U) ⟨z, h.z_mem_U⟩
    exact congrArg Subtype.val hc

theorem Ctx10.g_not_mem (h : Ctx10 G z k S M p Q T U t g) : g ∉ M := fun hg =>
  h.choice.t_out g hg h.choice.t_conj.symm

end Access

end CFSG.GH74.GLS.Stage2.Bender.Thm2
