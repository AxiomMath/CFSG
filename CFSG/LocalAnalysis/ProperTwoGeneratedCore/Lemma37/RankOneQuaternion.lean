module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankOneBender
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.BorelHold

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly CFSG.Semidihedral.CentralQuotients

theorem card_center_dihedralGroup_le_two {n : ℕ} [NeZero n] (hn : Even n) (hn2 : n ≠ 2) :
    Nat.card (Subgroup.center (DihedralGroup n)) ≤ 2 := by
  rw [DihedralGroup.center_eq_closure_of_even_ne_two hn hn2, Nat.card_zpowers]
  refine Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one ?_)
  obtain ⟨k, hk⟩ := hn
  rw [pow_two, DihedralGroup.r_mul_r, ← Nat.cast_add, show n / 2 + n / 2 = n by omega,
    ZMod.natCast_self, ← DihedralGroup.one_def]

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {H : Subgroup G} {z : G}
  {J : Subgroup (EscapingQuotient z)}

namespace RankOneSetting

variable (h : RankOneSetting G S H z J)
include h

theorem mem_center_iff_mem_nativeQuaternionZ (T : Sylow 2 J) {m : ℕ} (hm : 2 ≤ m)
    (e : (T : Subgroup J) ≃* QuaternionGroup m) (x : (T : Subgroup J)) :
    (x : J) ∈ Subgroup.center J ↔ e x ∈ nativeQuaternionZ m := by
  constructor
  · intro hx
    have hxT : x ∈ Subgroup.center (T : Subgroup J) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_center_iff.mp hx g)
    have hc : e x ∈ Subgroup.center (QuaternionGroup m) := by
      rw [Subgroup.mem_center_iff] at hxT ⊢
      intro g
      obtain ⟨g', rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul, hxT g']
    rcases ((CFSG.GroupTheory.quaternion_centralizers hm).2.2.1 (e x)).mp hc with h0 | h1
    · rw [h0, ← QuaternionGroup.one_def]
      exact Subgroup.one_mem _
    · rw [h1]
      exact Subgroup.mem_zpowers _
  · intro hx
    have hsq : (QuaternionGroup.a (m : ZMod (2 * m)) : QuaternionGroup m) ^ 2 = 1 := by
      rw [pow_two, QuaternionGroup.a_mul_a, ← Nat.cast_add, ← two_mul, ZMod.natCast_self,
        ← QuaternionGroup.one_def]
    have hx2 : x ^ 2 = 1 := by
      apply e.injective
      rw [map_pow, map_one, ← orderOf_dvd_iff_pow_eq_one]
      exact (orderOf_dvd_of_mem_zpowers hx).trans (orderOf_dvd_of_pow_eq_one hsq)
    by_cases hx1 : x = 1
    · rw [hx1]
      exact Subgroup.one_mem _
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hord : orderOf (((x : J) : EscapingQuotient z)) = 2 := by
        rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
        exact orderOf_eq_prime hx2 hx1
      have hxt : ((x : J) : EscapingQuotient z) = escapingBar z := h.unique _ (x : J).2 hord
      convert h.bar_mem_center using 1
      exact Subtype.ext hxt

theorem sylow_quotient_mulEquiv (T : Sylow 2 J) {r : ℕ} (hr : 3 ≤ r)
    (e : (T : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2))) :
    Nonempty (((T.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center J)) :
      Subgroup (J ⧸ Subgroup.center J))) ≃* DihedralGroup (2 ^ (r - 2))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm : 2 ≤ 2 ^ (r - 2) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (r - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : NeZero (2 ^ (r - 2)) := ⟨by positivity⟩
  refine ⟨?_⟩
  let ψ : (T : Subgroup J) →* J ⧸ Subgroup.center J :=
    (QuotientGroup.mk' (Subgroup.center J)).comp (T : Subgroup J).subtype
  let χ : (T : Subgroup J) →* DihedralGroup (2 ^ (r - 2)) :=
    (quaternionToDihedral (2 ^ (r - 2))).comp e.toMonoidHom
  have hχ : Function.Surjective χ :=
    (quaternionToDihedral_surjective (2 ^ (r - 2))).comp e.surjective
  have hker : ψ.ker = χ.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    change (QuotientGroup.mk' (Subgroup.center J)) (x : J) = 1 ↔
      quaternionToDihedral (2 ^ (r - 2)) (e x) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← MonoidHom.mem_ker,
      quaternionToDihedral_ker]
    exact h.mem_center_iff_mem_nativeQuaternionZ T hm e x
  have hrange : ψ.range = ((T.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center J)) :
      Subgroup (J ⧸ Subgroup.center J))) := by
    rw [Sylow.coe_mapSurjective, MonoidHom.range_comp, Subgroup.range_subtype]
  exact (MulEquiv.subgroupCongr hrange).symm.trans
    ((QuotientGroup.quotientKerEquivRange ψ).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans
        (QuotientGroup.quotientKerEquivOfSurjective χ hχ)))

theorem sylow_mulEquiv_quaternion_two
    (T : Sylow 2 J) :
    Nonempty ((T : Subgroup J) ≃* QuaternionGroup 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, hr, ⟨e⟩⟩ := h.sylow_quaternion h.component T
  obtain ⟨d⟩ := h.sylow_quotient_mulEquiv T hr e
  set Q := T.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center J)) with hQ
  have hBF := CFSG.ProperTwoGeneratedCore.TheoremC.benderBorelFactsHold _ h.isBenderGroup Q
  have hcard := hBF.center_card
  have : NeZero (2 ^ (r - 2)) := ⟨by positivity⟩
  by_cases hr3 : r = 3
  · subst hr3
    exact ⟨e⟩
  exfalso
  have heven : Even (2 ^ (r - 2)) := (Nat.even_pow' (by omega)).mpr even_two
  have hne : 2 ^ (r - 2) ≠ 2 := by
    intro h2
    have h3 : r - 2 = 1 := Nat.pow_right_injective (le_refl 2) (show 2 ^ (r - 2) = 2 ^ 1 by
      rw [h2, pow_one])
    omega
  have hle := card_center_dihedralGroup_le_two heven hne
  let f : {w : J ⧸ Subgroup.center J //
      CFSG.ProperTwoGeneratedCore.TheoremC.InCenterOf (Q : Subgroup _) w} →
      Subgroup.center (DihedralGroup (2 ^ (r - 2))) := fun w =>
    ⟨d ⟨w.1, w.2.1⟩, by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨g', rfl⟩ := d.surjective g
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (w.2.2 g' g'.2).eq⟩
  have hf : Function.Injective f := by
    intro w w' hww'
    have := d.injective (congrArg Subtype.val hww')
    exact Subtype.ext
      (congrArg (fun x : (Q : Subgroup (J ⧸ Subgroup.center J)) => (x : J ⧸ Subgroup.center J))
        this)
  have := Nat.card_le_card_of_injective f hf
  omega

theorem pow_four_eq_one
    {a : EscapingQuotient z} (haS : a ∈ escapingSylowImage S z)
    (haJ : a ∈ J) : a ^ 4 = 1 := by
  obtain ⟨P, hP⟩ := h.exists_sylow_inf h.component
  obtain ⟨e⟩ := h.sylow_mulEquiv_quaternion_two P
  have haP : a ∈ (P : Subgroup J).map J.subtype := hP ▸ ⟨haS, haJ⟩
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp haP
  have hexp : (e ⟨b, hb⟩) ^ 4 = 1 := by
    have h4 := Monoid.pow_exponent_eq_one (e ⟨b, hb⟩)
    rwa [QuaternionGroup.exponent] at h4
  have hb4 : (⟨b, hb⟩ : (P : Subgroup J)) ^ 4 = 1 := by
    apply e.injective
    rw [map_pow, map_one, hexp]
  have := congrArg (fun x : (P : Subgroup J) => ((x : J) : EscapingQuotient z)) hb4
  simpa using this

end RankOneSetting

end CFSG.ProperTwoGeneratedCore.Lemma37
