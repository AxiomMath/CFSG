module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.Schreier
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

open scoped commutatorElement

namespace CFSG.GroupTheory

theorem commutatorElement_mul_center_left {G : Type*} [Group G] {x y z : G}
    (hz : z ∈ Subgroup.center G) : ⁅x * z, y⁆ = ⁅x, y⁆ := by
  have hzy : z * y * z⁻¹ = y := by
    rw [show z * y = y * z from ((Subgroup.mem_center_iff.mp hz) y).symm, mul_assoc,
      mul_inv_cancel, mul_one]
  rw [commutatorElement_def, commutatorElement_def]
  rw [show (x * z) * y * (x * z)⁻¹ * y⁻¹ = x * (z * y * z⁻¹) * x⁻¹ * y⁻¹ by group, hzy]

theorem commutatorElement_mul_center_right {G : Type*} [Group G] {x y w : G}
    (hw : w ∈ Subgroup.center G) : ⁅x, y * w⁆ = ⁅x, y⁆ := by
  have hxw : w * x⁻¹ * w⁻¹ = x⁻¹ := by
    rw [show w * x⁻¹ = x⁻¹ * w from ((Subgroup.mem_center_iff.mp hw) x⁻¹).symm, mul_assoc,
      mul_inv_cancel, mul_one]
  rw [commutatorElement_def, commutatorElement_def]
  rw [show x * (y * w) * x⁻¹ * (y * w)⁻¹ = x * y * (w * x⁻¹ * w⁻¹) * y⁻¹ by group, hxw]

theorem commutatorElement_mul_center {G : Type*} [Group G] {x y z w : G}
    (hz : z ∈ Subgroup.center G) (hw : w ∈ Subgroup.center G) :
    ⁅x * z, y * w⁆ = ⁅x, y⁆ := by
  rw [commutatorElement_mul_center_left hz, commutatorElement_mul_center_right hw]

theorem finite_commutatorSet_of_finite_quotient_center
    {G : Type*} [Group G] (h : Finite (G ⧸ Subgroup.center G)) :
    Finite ↑(commutatorSet G) := by
  let f : (G ⧸ Subgroup.center G) × (G ⧸ Subgroup.center G) → ↑(commutatorSet G) :=
    fun p => ⟨⁅(p.1).out, (p.2).out⁆, ⟨(p.1).out, (p.2).out, rfl⟩⟩
  refine Finite.of_surjective f ?_
  rintro ⟨c, hc⟩
  rw [commutatorSet_def] at hc
  rcases hc with ⟨x, y, rfl⟩
  refine ⟨((↑x : G ⧸ Subgroup.center G), (↑y : G ⧸ Subgroup.center G)), ?_⟩
  apply Subtype.ext
  have hxZ : (↑x : G ⧸ Subgroup.center G).out⁻¹ * x ∈ Subgroup.center G := by
    have hout : (↑((↑x : G ⧸ Subgroup.center G).out) : G ⧸ Subgroup.center G) =
        (↑x : G ⧸ Subgroup.center G) := Quotient.out_eq _
    exact QuotientGroup.eq.mp hout
  have hyZ : (↑y : G ⧸ Subgroup.center G).out⁻¹ * y ∈ Subgroup.center G := by
    have hout : (↑((↑y : G ⧸ Subgroup.center G).out) : G ⧸ Subgroup.center G) =
        (↑y : G ⧸ Subgroup.center G) := Quotient.out_eq _
    exact QuotientGroup.eq.mp hout
  have hcx := commutatorElement_mul_center
    (x := (↑x : G ⧸ Subgroup.center G).out) (y := (↑y : G ⧸ Subgroup.center G).out)
    (z := (↑x : G ⧸ Subgroup.center G).out⁻¹ * x)
    (w := (↑y : G ⧸ Subgroup.center G).out⁻¹ * y) hxZ hyZ
  rw [mul_inv_cancel_left, mul_inv_cancel_left] at hcx
  exact hcx.symm

theorem finite_of_perfect_of_finite_quotient_center {G : Type*} [Group G]
    (hG : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤) [Finite (G ⧸ Subgroup.center G)] : Finite G := by
  have hset : Finite ↑(commutatorSet G) :=
    finite_commutatorSet_of_finite_quotient_center (G := G) inferInstance
  haveI : Finite ↑(commutatorSet G) := hset
  haveI : Finite ↑(commutator G) := inferInstance
  have hcomm : commutator G = ⊤ := by
    rw [commutator_def]
    exact hG
  exact Finite.of_surjective (fun x : commutator G => (x : G))
    fun y => ⟨⟨y, by rw [hcomm]; exact Subgroup.mem_top y⟩, rfl⟩

theorem not_dvd_card_center_of_perfect {G : Type*} [Group G] [Finite G]
    (hG : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤) {p : ℕ} [Fact p.Prime]
    (hp : ¬ p ^ 2 ∣ Nat.card (G ⧸ Subgroup.center G)) :
    ¬ p ∣ Nat.card (Subgroup.center G) := by
  intro hpZ
  have hpp : p.Prime := Fact.out
  have hG' : commutator G = ⊤ := by
    rw [commutator_def]
    exact hG
  obtain ⟨P⟩ : Nonempty (Sylow p G) := inferInstance
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp P.isPGroup'
  let f0 : P.toSubgroup →* G ⧸ Subgroup.center G :=
    (QuotientGroup.mk' (Subgroup.center G)).comp P.toSubgroup.subtype
  have hRdvd : Nat.card f0.range ∣ p ^ n := by
    rw [← hn, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange f0).toEquiv]
    exact Subgroup.card_quotient_dvd_card _
  obtain ⟨m, hm_le, hm_eq⟩ := (Nat.dvd_prime_pow hpp).1 hRdvd
  have hRZ : Nat.card f0.range ∣ Nat.card (G ⧸ Subgroup.center G) :=
    Subgroup.card_subgroup_dvd_card _
  have hm1 : m ≤ 1 := by
    by_contra hcon
    have h2 : p ^ 2 ∣ Nat.card f0.range := by
      rw [hm_eq]
      exact pow_dvd_pow p (by omega)
    exact hp (dvd_trans h2 hRZ)
  have hcyc : IsCyclic f0.range := by
    rcases (show m = 0 ∨ m = 1 by omega) with rfl | rfl
    · rw [pow_zero] at hm_eq
      have hsub : Subsingleton f0.range := (Nat.card_eq_one_iff_unique.mp hm_eq).1
      exact isCyclic_of_subsingleton
    · rw [pow_one] at hm_eq
      exact isCyclic_of_prime_card hm_eq
  have hker : f0.rangeRestrict.ker ≤ Subgroup.center P.toSubgroup := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 := congrArg Subtype.val hx
    have h2 : ((x : G) : G ⧸ Subgroup.center G) = 1 := h1
    have hxZ : (x : G) ∈ Subgroup.center G := (QuotientGroup.eq_one_iff _).mp h2
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp hxZ (g : G)
  have hPmc : IsMulCommutative P.toSubgroup :=
    MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center f0.rangeRestrict hker
  have hPab : ∀ a b : P.toSubgroup, a * b = b * a := fun a b => hPmc.is_comm.comm a b
  let _ : CommGroup P.toSubgroup :=
    { (inferInstance : Group P.toSubgroup) with mul_comm := hPab }
  have hVG : ∀ g : G, MonoidHom.transfer (MonoidHom.id P.toSubgroup) g = 1 := by
    have hle : commutator G ≤ (MonoidHom.transfer (MonoidHom.id P.toSubgroup)).ker := by
      unfold commutator
      apply Subgroup.commutator_le.mpr
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm _ _
    intro g
    have hg : g ∈ commutator G := by
      rw [hG']
      exact Subgroup.mem_top g
    exact (MonoidHom.mem_ker).mp (hle hg)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hpZ
  have hzZ : (z : G) ∈ Subgroup.center G := z.2
  have hord : orderOf (z : G) = p := (Subgroup.orderOf_coe z).trans hz
  have key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * (z : G) ^ k * g₀ ∈ P.toSubgroup →
      g₀⁻¹ * (z : G) ^ k * g₀ = (z : G) ^ k := by
    intro k g₀ _
    have hk : (z : G) ^ k ∈ Subgroup.center G := pow_mem hzZ k
    rw [Subgroup.mem_center_iff.mp hk g₀⁻¹]
    simp
  have hV := hVG (z : G)
  rw [MonoidHom.transfer_eq_pow (MonoidHom.id P.toSubgroup) (z : G) key] at hV
  have h2 : (z : G) ^ P.toSubgroup.index = 1 := congrArg Subtype.val hV
  have hdvd : orderOf (z : G) ∣ P.toSubgroup.index := orderOf_dvd_of_pow_eq_one h2
  rw [hord] at hdvd
  exact Sylow.not_dvd_index P hdvd

theorem exists_pow_five_eq_one_conj_sq_of_quotient_center_alternating_eight
    {J : Type*} [Group J] (hJ : ⁅(⊤ : Subgroup J), (⊤ : Subgroup J)⁆ = ⊤)
    (e : J ⧸ Subgroup.center J ≃* alternatingGroup (Fin 8)) :
    ∃ v g : J, v ^ 5 = 1 ∧ v ∉ Subgroup.center J ∧ g * v * g⁻¹ = v ^ 2 := by
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  haveI hfinQuot : Finite (J ⧸ Subgroup.center J) :=
    Finite.of_equiv (alternatingGroup (Fin 8)) e.symm
  haveI hfinJ : Finite J := finite_of_perfect_of_finite_quotient_center hJ
  have hcardA : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hcardQ : Nat.card (J ⧸ Subgroup.center J) = 20160 := by
    rw [Nat.card_congr e.toEquiv, hcardA]
  have h5Z : ¬ 5 ∣ Nat.card (Subgroup.center J) := by
    refine not_dvd_card_center_of_perfect hJ (p := 5) ?_
    rw [hcardQ]
    norm_num
  let c : alternatingGroup (Fin 8) :=
    ⟨List.formPerm [0, 1, 2, 3, 4], Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩
  let a : alternatingGroup (Fin 8) :=
    ⟨List.formPerm [1, 2, 4, 3] * List.formPerm [5, 6],
      Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩
  have hc5 : c ^ 5 = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    decide
  have hcne : c ≠ 1 := by
    intro hc1
    have h1 : (List.formPerm [0, 1, 2, 3, 4] : Equiv.Perm (Fin 8)) = 1 := by
      simpa [c] using congrArg Subtype.val hc1
    exact (by decide : (List.formPerm [0, 1, 2, 3, 4] : Equiv.Perm (Fin 8)) ≠ 1) h1
  have hac : a * c * a⁻¹ = c ^ 2 := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
    decide

  let q : J →* J ⧸ Subgroup.center J := QuotientGroup.mk' (Subgroup.center J)
  let e' : J →* alternatingGroup (Fin 8) := e.toMonoidHom.comp q
  have hker : MonoidHom.ker e' = Subgroup.center J := by
    ext z
    rw [MonoidHom.mem_ker]
    constructor
    · intro hz
      have hq : q z = 1 := e.injective (by
        rw [map_one]
        simpa [e'] using hz)
      have hzk : z ∈ (QuotientGroup.mk' (Subgroup.center J)).ker := MonoidHom.mem_ker.mpr hq
      rwa [QuotientGroup.ker_mk'] at hzk
    · intro hz
      have hq : q z = 1 := by
        have hzk : z ∈ (QuotientGroup.mk' (Subgroup.center J)).ker := by
          rwa [QuotientGroup.ker_mk']
        exact MonoidHom.mem_ker.mp hzk
      simp [e', hq]
  have he' : Function.Surjective e' := by
    intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Subgroup.center J) (e.symm y)
    exact ⟨x, by
      show e (q x) = y
      rw [hx]
      exact MulEquiv.apply_symm_apply e y⟩
  obtain ⟨v₀, hv₀⟩ := he' c
  set N : ℕ := Nat.card (Subgroup.center J) with hN
  have hconj_pow : ∀ n : ℕ, a * c ^ n * a⁻¹ = (a * c * a⁻¹) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, pow_succ]
      rw [show a * (c ^ n * c) * a⁻¹ = (a * c ^ n * a⁻¹) * (a * c * a⁻¹) by group, ih]
  have hacN : a * c ^ N * a⁻¹ = (c ^ N) ^ 2 := by
    rw [hconj_pow N, hac, ← pow_mul, ← pow_mul, Nat.mul_comm 2 N]
  let v : J := v₀ ^ N
  have hv0z : v₀ ^ 5 ∈ Subgroup.center J := by
    rw [← hker, MonoidHom.mem_ker, map_pow, hv₀, hc5]
  have hcenter_pow : ∀ z ∈ Subgroup.center J, z ^ N = 1 := by
    intro z hz
    have hdvd : orderOf z ∣ N := by
      have h := Subgroup.orderOf_dvd_natCard (Subgroup.center J) hz
      rwa [← hN] at h
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hv5 : v ^ 5 = 1 := by
    show (v₀ ^ N) ^ 5 = 1
    rw [← pow_mul, mul_comm N 5, pow_mul]
    exact hcenter_pow (v₀ ^ 5) hv0z
  have hv : e' v = c ^ N := by
    show e' (v₀ ^ N) = c ^ N
    rw [map_pow, hv₀]
  have hvne : e' v ≠ 1 := by
    rw [hv]
    intro h
    have h5N : 5 ∣ N := by
      have hord : orderOf c = 5 := orderOf_eq_prime hc5 hcne
      have hdvd : orderOf c ∣ N := orderOf_dvd_of_pow_eq_one h
      rwa [hord] at hdvd
    exact h5Z h5N
  have hvZ : v ∉ Subgroup.center J := by
    intro hvZ
    have hmem : v ∈ MonoidHom.ker e' := by
      rw [hker]
      exact hvZ
    exact hvne (MonoidHom.mem_ker.mp hmem)
  obtain ⟨g, hg⟩ := he' a
  let z : J := g * v * g⁻¹ * (v ^ 2)⁻¹
  have hz_center : z ∈ Subgroup.center J := by
    have h1 : e' z = 1 := by
      simp only [z, map_mul, map_inv, map_pow]
      rw [hg, hv, hacN, mul_inv_cancel]
    rwa [← hker, MonoidHom.mem_ker]
  have hzN : z ^ N = 1 := hcenter_pow z hz_center
  have hgv : g * v * g⁻¹ = z * v ^ 2 := by
    show g * v * g⁻¹ = (g * v * g⁻¹ * (v ^ 2)⁻¹) * v ^ 2
    group
  have hz5 : z ^ 5 = 1 := by
    have hpow5 : (g * v * g⁻¹) ^ 5 = 1 := by
      rw [← MulAut.conj_apply g v, ← map_pow, hv5, map_one]
    have hzv : Commute z (v ^ 2) := ((Subgroup.mem_center_iff.mp hz_center) (v ^ 2)).symm
    have h1 : (z * v ^ 2) ^ 5 = 1 := by
      rw [← hgv]
      exact hpow5
    rw [hzv.mul_pow] at h1
    rw [show (v ^ 2) ^ 5 = 1 by
      rw [← pow_mul, show 2 * 5 = 5 * 2 by norm_num, pow_mul, hv5, one_pow]] at h1
    simpa using h1
  have hz1 : z = 1 := by
    have hdvd5 : orderOf z ∣ 5 := orderOf_dvd_of_pow_eq_one hz5
    have hdvdN : orderOf z ∣ N := orderOf_dvd_of_pow_eq_one hzN
    have hgcd : orderOf z ∣ Nat.gcd 5 N := Nat.dvd_gcd hdvd5 hdvdN
    have h5N : ¬ 5 ∣ N := fun h => h5Z h
    have hgcd1 : Nat.gcd 5 N = 1 :=
      (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 5)).mpr h5N
    rw [hgcd1] at hgcd
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hgcd)
  have hconj : g * v * g⁻¹ = v ^ 2 := by
    rw [hgv, hz1, one_mul]
  exact ⟨v, g, hv5, hvZ, hconj⟩

end CFSG.GroupTheory

end
