module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

namespace T7T

variable {G : Type} [Group G] [Finite G]

@[expose] def conjAut (A : Subgroup G) (t : G) (ht2 : t * t = 1)
    (htA : ∀ a ∈ A, t * a * t⁻¹ ∈ A) : ↥A ≃* ↥A where
  toFun a := ⟨t * a * t⁻¹, htA a a.2⟩
  invFun a := ⟨t * a * t⁻¹, htA a a.2⟩
  left_inv a := by
    apply Subtype.ext
    have h : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    simp only [h]
    calc t * (t * (a : G) * t) * t = (t * t) * a * (t * t) := by group
      _ = a := by rw [ht2]; group
  right_inv a := by
    apply Subtype.ext
    have h : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    simp only [h]
    calc t * (t * (a : G) * t) * t = (t * t) * a * (t * t) := by group
      _ = a := by rw [ht2]; group
  map_mul' a b := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    group


theorem exists_conj_eq_mul_of_isPGroup {A : Subgroup G} (hA : IsPGroup 2 A) {z t : G}
    (hzA : z ∈ A) (hz2 : z * z = 1) (hz1 : z ≠ 1) (hzc : ∀ a ∈ A, z * a = a * z)
    (ht2 : t * t = 1) (htA : ∀ a ∈ A, t * a * t⁻¹ ∈ A) (htz : t * z * t⁻¹ = z)
    (hfix : ∀ a ∈ A, t * a * t⁻¹ = a → a = 1 ∨ a = z)
    (hbig : ∃ a ∈ A, a ≠ 1 ∧ a ≠ z) :
    ∃ a ∈ A, a ≠ 1 ∧ a ≠ z ∧ t * a * t⁻¹ = a * z := by
  classical
  set z' : ↥A := ⟨z, hzA⟩ with hz'
  have hz'cen : z' ∈ Subgroup.center ↥A := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hzc g g.2).symm
  let N : Subgroup ↥A := Subgroup.zpowers z'
  have hNc : N ≤ Subgroup.center ↥A := (Subgroup.zpowers_le).mpr hz'cen
  have hNn : N.Normal := Subgroup.normal_of_le_center hNc
  let ψ := conjAut A t ht2 htA
  have hψz : ψ z' = z' := by
    apply Subtype.ext
    exact htz
  have hψN : N.map ψ.toMonoidHom = N := by
    show (Subgroup.zpowers z').map ψ.toMonoidHom = Subgroup.zpowers z'
    rw [MonoidHom.map_zpowers]
    show Subgroup.zpowers (ψ z') = _
    rw [hψz]
  let σe : ↥A ⧸ N ≃* ↥A ⧸ N := QuotientGroup.congr N N ψ hψN
  let σ : Equiv.Perm (↥A ⧸ N) := σe.toEquiv
  have hσmk : ∀ a : ↥A, σ (a : ↥A ⧸ N) = ((ψ a : ↥A) : ↥A ⧸ N) := fun a =>
    QuotientGroup.congr_mk N N ψ hψN a
  have hσ2 : σ ^ 2 ^ 1 = 1 := by
    ext q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    simp only [pow_one, Equiv.Perm.coe_mul, Function.comp_apply, Equiv.Perm.coe_one, id_eq,
      pow_two]
    rw [hσmk, hσmk]
    congr 1
    apply Subtype.ext
    exact (conjAut A t ht2 htA).left_inv a |> congrArg Subtype.val
  have hσ1 : σ 1 = 1 := map_one σe
  let _ : Fintype (↥A ⧸ N) := Fintype.ofFinite _
  have hordz : orderOf z' = 2 := by
    apply orderOf_eq_prime
    · rw [pow_two]
      exact Subtype.ext hz2
    · intro h
      apply hz1
      exact congrArg Subtype.val h
  have hNcard : Nat.card N = 2 := by
    show Nat.card (Subgroup.zpowers z') = 2
    rw [Nat.card_zpowers, hordz]
  obtain ⟨m, hm⟩ := hA.exists_card_eq
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  rw [hNcard, hm] at hmul
  have hdvd : 2 ∣ Fintype.card (↥A ⧸ N) := by
    by_contra hnd
    rw [← Nat.card_eq_fintype_card] at hnd
    have hQ : Nat.card (↥A ⧸ N) ∣ 2 ^ m := Dvd.intro _ hmul.symm
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hQ
    have hj0 : j = 0 := by
      by_contra hj0
      exact hnd (hj ▸ dvd_pow_self 2 hj0)
    rw [hj0] at hj
    simp only [pow_zero] at hj
    have hsub : Subsingleton (↥A ⧸ N) := (Nat.card_eq_one_iff_unique.mp hj).1
    obtain ⟨a, haA, ha1, haz⟩ := hbig
    have h1 : (⟨a, haA⟩ : ↥A) ∈ N := by
      rw [← QuotientGroup.eq_one_iff]
      exact Subsingleton.elim _ _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
    have hk0 := zpow_mod_orderOf z' k
    rw [hordz] at hk0
    have hk' : z' ^ (k % 2) = z' ^ k := by simpa using hk0
    rcases Int.emod_two_eq_zero_or_one k with h0 | h0
    · rw [h0] at hk'
      simp at hk'
      apply ha1
      have := congrArg Subtype.val (hk.symm.trans hk'.symm)
      simpa using this
    · rw [h0] at hk'
      simp at hk'
      apply haz
      have := congrArg Subtype.val (hk.symm.trans hk'.symm)
      simpa using this
  obtain ⟨b, hb, hb1⟩ := Equiv.Perm.exists_fixed_point_of_prime' (p := 2) (n := 1) hdvd hσ2 hσ1
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective b
  rw [hσmk] at hb
  have hanN : a ∉ N := by
    intro h
    exact hb1 ((QuotientGroup.eq_one_iff a).mpr h)
  have hqa := QuotientGroup.eq.mp hb
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hqa
  have hk0 := zpow_mod_orderOf z' k
  rw [hordz] at hk0
  have hk' : z' ^ (k % 2) = z' ^ k := by simpa using hk0
  have ha1 : (a : G) ≠ 1 := by
    intro h
    apply hanN
    have : a = 1 := Subtype.ext h
    rw [this]; exact N.one_mem
  have haz : (a : G) ≠ z := by
    intro h
    apply hanN
    have : a = z' := Subtype.ext h
    rw [this]; exact Subgroup.mem_zpowers z'
  refine ⟨a, a.2, ha1, haz, ?_⟩
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  rcases Int.emod_two_eq_zero_or_one k with h0 | h0
  · exfalso
    rw [h0] at hk'
    have h1 : z' ^ k = 1 := by simpa using hk'.symm
    have hψa : ψ a = a := inv_mul_eq_one.mp (hk.symm.trans h1)
    rcases hfix a a.2 (congrArg Subtype.val hψa) with h | h
    · exact ha1 h
    · exact haz h
  · rw [h0] at hk'
    have h2 : (ψ a)⁻¹ * a = z' := by rw [← hk]; simpa using hk'.symm
    have h3 : a = ψ a * z' := by rw [← h2]; group
    have h4 : (a : G) = (t * a * t⁻¹) * z := congrArg Subtype.val h3
    calc t * (a : G) * t⁻¹ = ((t * a * t⁻¹) * z) * z⁻¹ := by group
      _ = a * z⁻¹ := by rw [← h4]
      _ = a * z := by rw [hzinv]

end T7T

end CFSG.ClassicalInvolution.Asc77
