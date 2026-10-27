module

public import CFSG.CGT.PushingUpLit.T2KSW.Defs
public import CFSG.Sporadic.Mathieu.M24

public section

namespace CFSG.CGT.PushingUpLit.C2L

open CFSG CFSG.CGT.PushingUpLit.T2K CFSG.CGT.PushingUpLit.T2KSW
open scoped commutatorElement

theorem false_of_classLETwo_of_dihedral {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) (hc : ClassLETwo T) {s t : G}
    (hs : s ^ 2 = 1) (ht : t ^ 2 = 1) (h8 : (s * t) ^ 8 = 1) (h4 : (s * t) ^ 4 ≠ 1) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hss : s * s = 1 := by rw [← pow_two]; exact hs
  have htt : t * t = 1 := by rw [← pow_two]; exact ht
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  obtain ⟨r, hr⟩ : ∃ r : G, r = s * t := ⟨_, rfl⟩
  rw [← hr] at h8 h4
  have hrs : s * r * s⁻¹ = r⁻¹ := by
    rw [hr, mul_inv_rev, hsi, hti, ← mul_assoc, hss, one_mul]
  have hrs' : s * r⁻¹ * s⁻¹ = r := by
    rw [show s * r⁻¹ * s⁻¹ = (s * r * s⁻¹)⁻¹ by group, hrs, inv_inv]
  have c1 : ⁅r, s⁆ = r ^ 2 := by
    calc ⁅r, s⁆ = r * (s * r⁻¹ * s⁻¹) := by simp only [commutatorElement_def]; group
      _ = r ^ 2 := by rw [hrs', ← pow_two]
  have c2 : ⁅r ^ 2, s⁆ = r ^ 4 := by
    have h2 : s * (r ^ 2)⁻¹ * s⁻¹ = r ^ 2 := by
      calc s * (r ^ 2)⁻¹ * s⁻¹ = (s * r⁻¹ * s⁻¹) * (s * r⁻¹ * s⁻¹) := by group
        _ = r ^ 2 := by rw [hrs', ← pow_two]
    calc ⁅r ^ 2, s⁆ = r ^ 2 * (s * (r ^ 2)⁻¹ * s⁻¹) := by
          simp only [commutatorElement_def]; group
      _ = r ^ 4 := by rw [h2]; group
  have hcomm : ⁅⁅r, s⁆, s⁆ = r ^ 4 := by rw [c1, c2]
  have hA : IsPGroup 2 (Subgroup.zpowers r) := by
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
      (show orderOf r ∣ 2 ^ 3 from orderOf_dvd_of_pow_eq_one (by simpa using h8))
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hi])
  have hB : IsPGroup 2 (Subgroup.zpowers s) := by
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
      (show orderOf s ∣ 2 ^ 1 from orderOf_dvd_of_pow_eq_one (by simpa using hs))
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hi])
  have key : ∀ y ∈ Subgroup.zpowers r, s * y * s⁻¹ ∈ Subgroup.zpowers r := by
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have : s * r ^ k * s⁻¹ = (r ^ k)⁻¹ := by
      have h := map_zpow (MulAut.conj s) r k
      simp only [MulAut.conj_apply] at h
      rw [h, hrs, inv_zpow', zpow_neg]
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.zpow_mem_zpowers r k)
  have hBA : Subgroup.zpowers s ≤ Subgroup.normalizer (Subgroup.zpowers r : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨key y, fun h => ?_⟩
    have h' := key _ h
    have e : s * (s * y * s⁻¹) * s⁻¹ = y := by
      rw [hsi]
      calc s * (s * y * s) * s = (s * s) * y * (s * s) := by group
        _ = y := by rw [hss]; group
    rwa [e] at h'
  have hP : IsPGroup 2 (Subgroup.zpowers r ⊔ Subgroup.zpowers s : Subgroup G) :=
    hA.to_sup_of_normal_left' hB hBA
  obtain ⟨m, -, hm⟩ := T2K.exists_conj_le_of_isPGroup hT hP le_top
  have hmem : ∀ x ∈ (Subgroup.zpowers r ⊔ Subgroup.zpowers s : Subgroup G), m * x * m⁻¹ ∈ T :=
    fun x hx => hm ⟨x, hx, by simp [MulAut.conj_apply]⟩
  have hr' := hmem r (Subgroup.mem_sup_left (Subgroup.mem_zpowers r))
  have hs' := hmem s (Subgroup.mem_sup_right (Subgroup.mem_zpowers s))
  have h1 := hc _ hr' _ hs' _ hs'
  have h2 : ⁅⁅m * r * m⁻¹, m * s * m⁻¹⁆, m * s * m⁻¹⁆ = m * r ^ 4 * m⁻¹ := by
    have h := map_commutatorElement (MulAut.conj m) ⁅r, s⁆ s
    rw [map_commutatorElement (MulAut.conj m) r s, hcomm] at h
    simp only [MulAut.conj_apply] at h
    exact h.symm
  rw [h2] at h1
  apply h4
  have := congrArg (fun z => m⁻¹ * z * m) h1
  simpa [mul_assoc] using this

section M24

open CFSG.Blueprint CFSG.Sporadic.Mathieu

private def m24w : NativeSporadic.M24 :=
  m24a * m24b⁻¹ * m24a * m24b * m24a * m24b⁻¹ * m24a * m24b * m24a * m24b⁻¹ * m24a * m24b *
    m24a * m24b⁻¹

private def m24t : NativeSporadic.M24 := m24w ^ 2

private theorem m24a_sq : m24a ^ 2 = 1 := by decide +kernel

private theorem m24t_sq : m24t ^ 2 = 1 := by
  have h : m24w ^ 4 = 1 := by decide +kernel
  rw [m24t, ← pow_mul]
  exact h

private def m24rTab : Fin 24 → Fin 24 :=
  ![0, 6, 23, 3, 18, 17, 10, 14, 7, 12, 8, 13, 2, 15, 5, 20, 4, 1, 9, 16, 11, 22, 21, 19]

private theorem m24r_apply (x : Fin 24) :
    ((m24a * m24t : NativeSporadic.M24) : Equiv.Perm (Fin 24)) x = m24rTab x := by
  revert x
  decide +kernel

private theorem m24r_pow (k : ℕ) (x : Fin 24) :
    (((m24a * m24t) ^ k : NativeSporadic.M24) : Equiv.Perm (Fin 24)) x = m24rTab^[k] x := by
  rw [Subgroup.coe_pow, Equiv.Perm.coe_pow]
  have h : ⇑((m24a * m24t : NativeSporadic.M24) : Equiv.Perm (Fin 24)) = m24rTab :=
    funext m24r_apply
  rw [h]

private theorem m24r_pow_eight : (m24a * m24t) ^ 8 = 1 := by
  refine Subtype.ext (Equiv.ext fun x => ?_)
  rw [m24r_pow]
  show m24rTab^[8] x = x
  revert x
  decide +kernel

private theorem m24r_pow_four : (m24a * m24t) ^ 4 ≠ 1 := by
  intro h
  have h1 : m24rTab^[4] 1 = 1 := by
    have := congrArg (fun g : NativeSporadic.M24 => (g : Equiv.Perm (Fin 24)) 1) h
    rw [m24r_pow] at this
    exact this
  revert h1
  decide +kernel

theorem not_classLETwo_of_mulEquiv_m24 {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) (e : G ≃* NativeSporadic.M24) :
    ¬ ClassLETwo T := by
  intro hc
  refine false_of_classLETwo_of_dihedral hT hc (s := e.symm m24a) (t := e.symm m24t) ?_ ?_ ?_ ?_
  · rw [← map_pow, m24a_sq, map_one]
  · rw [← map_pow, m24t_sq, map_one]
  · rw [← map_mul, ← map_pow, m24r_pow_eight, map_one]
  · intro h
    apply m24r_pow_four
    have h' : e.symm ((m24a * m24t) ^ 4) = 1 := by
      rw [map_pow, map_mul]
      exact h
    exact e.symm.injective (by rw [h', map_one])

end M24

end CFSG.CGT.PushingUpLit.C2L
