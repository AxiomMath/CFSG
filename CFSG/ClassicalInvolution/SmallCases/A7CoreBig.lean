module

public import CFSG.ClassicalInvolution.Asc77.AscFusionS13
public import CFSG.ClassicalInvolution.SmallCases.A7CoreTrivial
public import CFSG.ClassicalInvolution.SmallCases.A7CoreTwin

public section

namespace CFSG.ClassicalInvolution.A7Core

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Hat2A7
  CFSG.ClassicalInvolution.Hat2A7R CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

variable {F : Type} [Group F] [Finite F]

theorem sq_eq_one_of_mem_twin_inter {K K' : Subgroup F} {z : F} (hK : IsClassical2A7 ⊤ K z)
    (hK' : IsClassical2A7 ⊤ K' z) (hne : K ≠ K') {k : F} (hkK : k ∈ K) (hkK' : k ∈ K')
    (hk2 : IsPGroup 2 (Subgroup.zpowers k)) : k * k = 1 := by
  by_contra h
  exact hne (eq_of_mem_of_mem hK hK' hkK hkK' hk2 (AscFusion.four_le_orderOf_of_sq_ne_one hk2 h))

theorem exists_two_sq_elements {K V : Subgroup F} {z : F} (hK : IsClassical2A7 ⊤ K z)
    (hV : IsSylow2In V K) :
    ∃ a₁ ∈ V, ∃ a₂ ∈ V, a₁ * a₁ = z ∧ a₂ * a₂ = z ∧ (a₁ * a₂) * (a₁ * a₂) ≠ 1 := by
  have hKz : IsUniqueInvolution K z := isUniqueInvolution hK
  obtain ⟨k₁, hk₁, ⟨eQ⟩⟩ := isQuatSub_of_isSylow2In hK hV
  have : NeZero (2 ^ k₁) := ⟨by positivity⟩
  have hn2 : 2 ≤ 2 ^ k₁ := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k₁ := Nat.pow_le_pow_right (by norm_num) hk₁
  have hsq : ∀ i : ZMod (2 * 2 ^ k₁), ((eQ.symm (QuaternionGroup.xa i) : ↥V) : F) *
      ((eQ.symm (QuaternionGroup.xa i) : ↥V) : F) = z := by
    intro i
    set x : ↥V := eQ.symm (QuaternionGroup.xa i) with hx
    have hx4 : orderOf x = 4 := by
      rw [hx, MulEquiv.orderOf_eq]
      exact QuaternionGroup.orderOf_xa i
    set a : F := (x : F) with ha
    have ha4 : orderOf a = 4 := by rw [ha, Subgroup.orderOf_coe]; exact hx4
    have haK : a ∈ K := hV.1 x.2
    have h1 : (a * a) * (a * a) = 1 := by
      have : a ^ 4 = 1 := by rw [← ha4]; exact pow_orderOf_eq_one a
      calc (a * a) * (a * a) = a ^ 4 := by simp [pow_succ, mul_assoc]
        _ = 1 := this
    rcases hKz.unique (a * a) (K.mul_mem haK haK) h1 with h | h
    · exfalso
      have : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
      rw [ha4] at this
      omega
    · exact h
  refine ⟨((eQ.symm (QuaternionGroup.xa 0) : ↥V) : F), (eQ.symm (QuaternionGroup.xa 0)).2,
    ((eQ.symm (QuaternionGroup.xa 1) : ↥V) : F), (eQ.symm (QuaternionGroup.xa 1)).2,
    hsq 0, hsq 1, ?_⟩
  intro h
  apply AscFusion.quaternion_pair_prod_sq_ne_one (n := 2 ^ k₁) hn2
  have h' : (eQ.symm (QuaternionGroup.xa 0) * eQ.symm (QuaternionGroup.xa 1)) *
      (eQ.symm (QuaternionGroup.xa 0) * eQ.symm (QuaternionGroup.xa 1)) = 1 := Subtype.ext h
  have := congrArg eQ h'
  simpa [map_mul] using this

theorem eq_one_or_eq_of_twin_conj {K : Subgroup F} {z : F} (hK : IsClassical2A7 ⊤ K z)
    {J : Subgroup F} {t : F} (hJ : IsClassical2A7 ⊤ J t) (hne : t ≠ z) {v : F} (hvJ : v ∈ J)
    (hvz : v * z = z * v) {R : Subgroup F} (hR2 : IsPGroup 2 R) (hvR : v ∈ R)
    (hKK' : conjSub v⁻¹ K ≠ K) {x y : F} (hxt : x * t = t * x) (hy : v * y = x * v * x⁻¹)
    (hyR : y ∈ R) (hyK : y ∈ K) : y = 1 ∨ y = z := by
  classical
  have hKz : IsUniqueInvolution K z := isUniqueInvolution hK
  have hJt : IsUniqueInvolution J t := isUniqueInvolution hJ
  have hy2 : IsPGroup 2 (Subgroup.zpowers y) := hR2.to_le (Subgroup.zpowers_le.mpr hyR)
  by_cases hxJ : x ∈ Subgroup.normalizer (J : Set F)
  · left
    have hvJ' : x * v * x⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp hxJ v).mp hvJ
    have hyJ : y ∈ J := by
      have : y = v⁻¹ * (v * y) := by group
      rw [this, hy]
      exact J.mul_mem (J.inv_mem hvJ) hvJ'
    exact AscFusion.eq_one_of_mem_inf_of_isPGroup hJt hKz hne hyJ hyK hy2
  · have hJ₂t : IsClassical2A7 ⊤ (conjSub x J) t := classical_conjSub_of_commute hJ hxt
    have hJne : conjSub x J ≠ J := fun h => hxJ (AscHypOmega.mem_normalizer_of_conjSub_eq h)
    obtain ⟨-, -, hcomm⟩ := twin_facts hJ₂t hJ hJne
    have hw : x * v * x⁻¹ ∈ conjSub x J := conj_mem_conjSub hvJ
    have hcw : ⁅x * v * x⁻¹, v⁆ ∈ oddCoreOf (conjSub x J) ⊓ oddCoreOf J :=
      hcomm (Subgroup.commutator_mem_commutator hw hvJ)
    have hc3 : ⁅y, v⁆ = v⁻¹ * ⁅x * v * x⁻¹, v⁆ * v⁻¹⁻¹ := by
      rw [← hy]
      simp only [commutatorElement_def]
      group
    have hc3o : ⁅y, v⁆ ∈ oddCoreOf J := by
      rw [hc3]
      exact mem_normalizer_oddCoreOf_of_mem_normalizer
        ((Subgroup.normalizer (J : Set F)).inv_mem (Subgroup.le_normalizer hvJ)) hcw.2
    have hc3R : ⁅y, v⁆ ∈ R := by
      rw [commutatorElement_def]
      exact R.mul_mem (R.mul_mem (R.mul_mem hyR hvR) (R.inv_mem hyR)) (R.inv_mem hvR)
    have hc31 : ⁅y, v⁆ = 1 :=
      eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard J) hc3o
        (hR2.to_le (Subgroup.zpowers_le.mpr hc3R))
    have hyv : y * v = v * y := commutatorElement_eq_one_iff_mul_comm.mp hc31
    have hyK' : y ∈ conjSub v⁻¹ K := by
      have := conj_mem_conjSub (n := v⁻¹) hyK
      have e : v⁻¹ * y * v⁻¹⁻¹ = y := by
        calc v⁻¹ * y * v⁻¹⁻¹ = v⁻¹ * (y * v) := by group
          _ = v⁻¹ * (v * y) := by rw [hyv]
          _ = y := by group
      rwa [e] at this
    have hK' : IsClassical2A7 ⊤ (conjSub v⁻¹ K) z :=
      classical_conjSub_of_commute hK (inv_comm_of_comm hvz)
    exact hKz.unique y hyK (sq_eq_one_of_mem_twin_inter hK hK' hKK'.symm hyK hyK' hy2)

theorem not_forall_comm_of_twin {K : Subgroup F} {z : F} (hK : IsClassical2A7 ⊤ K z)
    {J : Subgroup F} {t : F} (hJ : IsClassical2A7 ⊤ J t) (htz : z * t = t * z)
    (htK : t ∈ Subgroup.normalizer (K : Set F)) {v : F} (hvJ : v ∈ J) (hvz : v * z = z * v)
    (hvK : conjSub v⁻¹ K ≠ K) {R : Subgroup F} (hR2 : IsPGroup 2 R) (htR : t ∈ R)
    (hRK : IsSylow2In (R ⊓ K) K)
    (hcomm : ∀ q ∈ R ⊓ K, ∀ q' ∈ R ⊓ conjSub v⁻¹ K, q * q' = q' * q)
    (hconj : ∀ q ∈ R ⊓ K, v⁻¹ * q * v ∈ R ⊓ conjSub v⁻¹ K) :
    ¬ ∀ k ∈ K, ⁅t, k⁆ ∈ oddCoreOf K := by
  classical
  intro htriv
  have hKz : IsUniqueInvolution K z := isUniqueInvolution hK
  have hJt : IsUniqueInvolution J t := isUniqueInvolution hJ
  have hz2 : z * z = 1 := hKz.sq
  have ht2 : t * t = 1 := hJt.sq
  have hK' : IsClassical2A7 ⊤ (conjSub v⁻¹ K) z :=
    classical_conjSub_of_commute hK (inv_comm_of_comm hvz)
  have hvz' : v⁻¹ * z * v = z := conj_eq_of_comm hvz
  have htQ : ∀ q ∈ R ⊓ K, t * q = q * t := by
    intro q hq'
    have h1 : ⁅t, q⁆ ∈ oddCoreOf K := htriv q hq'.2
    have h2 : ⁅t, q⁆ ∈ R := by
      rw [commutatorElement_def]
      exact R.mul_mem (R.mul_mem (R.mul_mem htR hq'.1) (R.inv_mem htR)) (R.inv_mem hq'.1)
    have h3 : IsPGroup 2 (Subgroup.zpowers ⁅t, q⁆) := hR2.to_le (Subgroup.zpowers_le.mpr h2)
    exact commutatorElement_eq_one_iff_mul_comm.mp
      (eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K) h1 h3)
  obtain ⟨a₁, ha₁, a₂, ha₂, ha₁2, ha₂2, hprod⟩ := exists_two_sq_elements hK hRK
  have key : ∀ a ∈ R ⊓ K, a * a = z → v⁻¹ * a * v = a * t := by
    intro a ha ha2
    have haK : a ∈ K := ha.2
    have ha2' : IsPGroup 2 (Subgroup.zpowers a) := AscFusion.isPGroup_zpowers_of_sq_eq hz2 ha2
    have hat : a * t = t * a := (htQ a ha).symm
    have haJ : a ∈ Subgroup.normalizer (J : Set F) :=
      mem_normalizer_of_trivial_action hJ hK htz htK htriv haK ha2' hat
    have ha'mem : v⁻¹ * a * v ∈ R ⊓ conjSub v⁻¹ K := hconj a ha
    have hcom : a * (v⁻¹ * a * v) = (v⁻¹ * a * v) * a := hcomm a ha _ ha'mem
    have hcom' : (v⁻¹ * a * v) * a⁻¹ = a⁻¹ * (v⁻¹ * a * v) := by
      calc (v⁻¹ * a * v) * a⁻¹ = a⁻¹ * (a * (v⁻¹ * a * v)) * a⁻¹ := by group
        _ = a⁻¹ * ((v⁻¹ * a * v) * a) * a⁻¹ := by rw [hcom]
        _ = a⁻¹ * (v⁻¹ * a * v) := by group
    have hd : a⁻¹ * (v⁻¹ * a * v) ∈ J := by
      have h1 : a⁻¹ * v⁻¹ * a⁻¹⁻¹ ∈ J :=
        (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (J : Set F)).inv_mem haJ) v⁻¹).mp
          (J.inv_mem hvJ)
      have e : a⁻¹ * (v⁻¹ * a * v) = (a⁻¹ * v⁻¹ * a⁻¹⁻¹) * v := by group
      rw [e]
      exact J.mul_mem h1 hvJ
    have ha'2 : (v⁻¹ * a * v) * (v⁻¹ * a * v) = z := by
      calc (v⁻¹ * a * v) * (v⁻¹ * a * v) = v⁻¹ * (a * a) * v := by group
        _ = v⁻¹ * z * v := by rw [ha2]
        _ = z := hvz'
    have hdd : (a⁻¹ * (v⁻¹ * a * v)) * (a⁻¹ * (v⁻¹ * a * v)) = 1 := by
      calc (a⁻¹ * (v⁻¹ * a * v)) * (a⁻¹ * (v⁻¹ * a * v))
          = a⁻¹ * ((v⁻¹ * a * v) * a⁻¹) * (v⁻¹ * a * v) := by group
        _ = a⁻¹ * (a⁻¹ * (v⁻¹ * a * v)) * (v⁻¹ * a * v) := by rw [hcom']
        _ = (a * a)⁻¹ * ((v⁻¹ * a * v) * (v⁻¹ * a * v)) := by group
        _ = 1 := by rw [ha2, ha'2]; exact inv_mul_cancel z
    rcases hJt.unique _ hd hdd with h1 | h1
    · exfalso
      have haa' : v⁻¹ * a * v = a := (inv_mul_eq_one.mp h1).symm
      have haK' : a ∈ conjSub v⁻¹ K := haa' ▸ ha'mem.2
      have ha4 : orderOf a = 4 := AscFusion.orderOf_eq_four_of_sq_eq hz2 hKz.ne_one ha2
      exact hvK (eq_of_mem_of_mem hK hK' haK haK' ha2' (by omega)).symm
    · calc v⁻¹ * a * v = a * (a⁻¹ * (v⁻¹ * a * v)) := by group
        _ = a * t := by rw [h1]
  have h₁ := key a₁ ha₁ ha₁2
  have h₂ := key a₂ ha₂ ha₂2
  have hprodmem : a₁ * a₂ ∈ R ⊓ K := (R ⊓ K).mul_mem ha₁ ha₂
  have hfix : v⁻¹ * (a₁ * a₂) * v = a₁ * a₂ := by
    calc v⁻¹ * (a₁ * a₂) * v = (v⁻¹ * a₁ * v) * (v⁻¹ * a₂ * v) := by group
      _ = (a₁ * t) * (a₂ * t) := by rw [h₁, h₂]
      _ = a₁ * (t * a₂) * t := by group
      _ = a₁ * (a₂ * t) * t := by rw [htQ a₂ ha₂]
      _ = a₁ * a₂ * (t * t) := by group
      _ = a₁ * a₂ := by rw [ht2, mul_one]
  have hmemK' : a₁ * a₂ ∈ conjSub v⁻¹ K := by
    have := (hconj _ hprodmem).2
    rwa [hfix] at this
  have hpg : IsPGroup 2 (Subgroup.zpowers (a₁ * a₂)) :=
    hR2.to_le (Subgroup.zpowers_le.mpr hprodmem.1)
  exact hprod (sq_eq_one_of_mem_twin_inter hK hK' hvK.symm hprodmem.2 hmemK' hpg)

end CFSG.ClassicalInvolution.A7Core
