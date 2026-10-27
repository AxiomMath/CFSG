module

public import CFSG.ClassicalInvolution.Asc77.AscFusionS7
public import CFSG.ClassicalInvolution.Asc77.AscFusionS4
public import CFSG.ClassicalInvolution.Asc77.AscFusionR12
public import CFSG.ClassicalInvolution.Asc77.AscFusionR2

public section

namespace CFSG.ClassicalInvolution.Asc77.AscFusion

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscHypOmega
  CFSG.ComponentClassification
open scoped commutatorElement MatrixGroups Pointwise

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem four_le_orderOf_of_sq_ne_one {k : G} (hk2 : IsPGroup 2 (Subgroup.zpowers k))
    (h : k * k ≠ 1) : 4 ≤ orderOf k := by
  obtain ⟨s, hs⟩ := hk2.exists_card_eq
  rw [Nat.card_zpowers] at hs
  by_contra hlt
  have hs1 : s ≤ 1 := by
    by_contra hs1
    have h4 : 2 ^ 2 ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hdvd : orderOf k ∣ 2 := by
    rw [hs]
    exact (pow_dvd_pow 2 hs1 : 2 ^ s ∣ 2 ^ 1)
  exact h (by rw [← pow_two]; exact orderOf_dvd_iff_pow_eq_one.mp hdvd)

theorem eq_one_of_mem_inf_of_isPGroup {J K : Subgroup G} {t z y : G}
    (hJ : IsUniqueInvolution J t) (hK : IsUniqueInvolution K z) (hne : t ≠ z)
    (hyJ : y ∈ J) (hyK : y ∈ K) (hy2 : IsPGroup 2 (Subgroup.zpowers y)) : y = 1 := by
  by_contra hy1
  have hord : orderOf y ≠ 1 := fun h => hy1 (orderOf_eq_one_iff.mp h)
  obtain ⟨s, hs⟩ := hy2.exists_card_eq
  rw [Nat.card_zpowers] at hs
  have hs1 : 1 ≤ s := by
    by_contra h0
    have : s = 0 := by omega
    rw [this] at hs
    exact hord (by simpa using hs)
  set w : G := y ^ (2 ^ (s - 1)) with hw
  have hwJ : w ∈ J := J.pow_mem hyJ _
  have hwK : w ∈ K := K.pow_mem hyK _
  have hww : w * w = 1 := by
    rw [hw, ← pow_add, ← two_mul, ← pow_succ', Nat.sub_add_cancel hs1, ← hs]
    exact pow_orderOf_eq_one y
  have hw1 : w ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hs] at this
    have h2 : 2 ^ s ≤ 2 ^ (s - 1) := Nat.le_of_dvd (by positivity) this
    have h3 : 2 ^ (s - 1) < 2 ^ s := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have h1 := (hJ.unique w hwJ hww).resolve_left hw1
  have h2 := (hK.unique w hwK hww).resolve_left hw1
  exact hne (h1.symm.trans h2)

theorem sq_eq_one_of_mem_twin_inter (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K₀ : Subgroup G} {z₀ : G}
    (h₀ : IsClassicalMember p f K₀ z₀) {K K' : Subgroup G}
    (hK : K ∈ CoreAssembly.conjClass K₀) (hK' : K' ∈ CoreAssembly.conjClass K₀) (hne : K ≠ K')
    {k : G} (hkK : k ∈ K) (hkK' : k ∈ K') (hk2 : IsPGroup 2 (Subgroup.zpowers k)) :
    k * k = 1 := by
  by_contra h
  exact hne (eq_of_mem_of_mem hp2 hq h₀ hK hK' hkK hkK' hk2 (four_le_orderOf_of_sq_ne_one hk2 h))

omit [Finite G] in
theorem twin_conj_identity {v κ : G} (hc : κ * (v⁻¹ * κ * v) = (v⁻¹ * κ * v) * κ) :
    κ * (v⁻¹ * κ * v) * v * (κ * (v⁻¹ * κ * v))⁻¹ = v⁻¹ * κ * (v * v) * κ⁻¹ := by
  calc κ * (v⁻¹ * κ * v) * v * (κ * (v⁻¹ * κ * v))⁻¹
      = (κ * (v⁻¹ * κ * v)) * v * (v⁻¹ * κ⁻¹ * v) * κ⁻¹ := by group
    _ = ((v⁻¹ * κ * v) * κ) * v * (v⁻¹ * κ⁻¹ * v) * κ⁻¹ := by rw [hc]
    _ = v⁻¹ * κ * (v * v) * κ⁻¹ := by group

section Quat

open QuaternionGroup in
theorem quaternion_pair_prod_sq_ne_one {n : ℕ} [NeZero n] (hn : 2 ≤ n) :
    (xa (0 : ZMod (2 * n)) * xa 1) * (xa 0 * xa 1) ≠ 1 := by
  rw [xa_mul_xa, a_mul_a]
  intro h
  have h1 : ((n : ZMod (2 * n)) + 1 - 0) + ((n : ZMod (2 * n)) + 1 - 0) = 0 :=
    QuaternionGroup.a.inj (h.trans one_def)
  rcases zmod_double_eq_zero h1 with h2 | h2
  · have h3 : (((n + 1 : ℕ)) : ZMod (2 * n)) = 0 := by
      push_cast
      simpa using h2
    have h4 := (ZMod.natCast_eq_zero_iff _ _).mp h3
    have h5 := Nat.le_of_dvd (by omega) h4
    omega
  · have h3 : ((1 : ℕ) : ZMod (2 * n)) = 0 := by
      have : (n : ZMod (2 * n)) + 1 - 0 = n := h2
      push_cast
      linear_combination this
    have h4 := (ZMod.natCast_eq_zero_iff _ _).mp h3
    have h5 := Nat.le_of_dvd (by norm_num) h4
    omega

end Quat

theorem exists_two_sq_elements (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K V : Subgroup G} {z : G}
    (hK : IsClassicalMember p f K z) (hV : IsSylow2In V K) :
    ∃ a₁ ∈ V, ∃ a₂ ∈ V, a₁ * a₁ = z ∧ a₂ * a₂ = z ∧ (a₁ * a₂) * (a₁ * a₂) ≠ 1 := by
  have hKz : IsUniqueInvolution K z :=
    ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hK
  have hQuat : IsQuatSub V := isQuatSub_of_isSylow2In hp2 hK hV
  obtain ⟨k₁, hk₁, ⟨eQ⟩⟩ := id hQuat
  have : NeZero (2 ^ k₁) := ⟨by positivity⟩
  have hn2 : 2 ≤ 2 ^ k₁ := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k₁ := Nat.pow_le_pow_right (by norm_num) hk₁
  have hsq : ∀ i : ZMod (2 * 2 ^ k₁), ((eQ.symm (QuaternionGroup.xa i) : ↥V) : G) *
      ((eQ.symm (QuaternionGroup.xa i) : ↥V) : G) = z := by
    intro i
    set x : ↥V := eQ.symm (QuaternionGroup.xa i) with hx
    have hx4 : orderOf x = 4 := by
      rw [hx, MulEquiv.orderOf_eq]
      exact QuaternionGroup.orderOf_xa i
    set a : G := (x : G) with ha
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
  refine ⟨((eQ.symm (QuaternionGroup.xa 0) : ↥V) : G), (eQ.symm (QuaternionGroup.xa 0)).2,
    ((eQ.symm (QuaternionGroup.xa 1) : ↥V) : G), (eQ.symm (QuaternionGroup.xa 1)).2,
    hsq 0, hsq 1, ?_⟩
  intro h
  apply quaternion_pair_prod_sq_ne_one (n := 2 ^ k₁) hn2
  have h' : (eQ.symm (QuaternionGroup.xa 0) * eQ.symm (QuaternionGroup.xa 1)) *
      (eQ.symm (QuaternionGroup.xa 0) * eQ.symm (QuaternionGroup.xa 1)) = 1 := Subtype.ext h
  have := congrArg eQ h'
  simpa [map_mul] using this


theorem eq_one_or_eq_of_twin_conj (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G} {z : G}
    (hKm : IsClassicalMember p f K z) {J : Subgroup G} {t : G}
    (hJ : J ∈ CoreAssembly.conjClass K) (hJt : IsUniqueInvolution J t) (hne : t ≠ z)
    {v : G} (hvJ : v ∈ J) {R : Subgroup G} (hR2 : IsPGroup 2 R) (hvR : v ∈ R)
    (hK' : conjSub v⁻¹ K ∈ CoreAssembly.conjClass K) (hKK' : conjSub v⁻¹ K ≠ K)
    {x y : G} (hxt : x * t = t * x) (hy : v * y = x * v * x⁻¹) (hyR : y ∈ R) (hyK : y ∈ K) :
    y = 1 ∨ y = z := by
  classical
  have hKz : IsUniqueInvolution K z :=
    ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hKm
  have hKc : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hy2 : IsPGroup 2 (Subgroup.zpowers y) := hR2.to_le (Subgroup.zpowers_le.mpr hyR)
  by_cases hxJ : x ∈ Subgroup.normalizer (J : Set G)
  · left
    have hvJ' : x * v * x⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp hxJ v).mp hvJ
    have hyJ : y ∈ J := by
      have : y = v⁻¹ * (v * y) := by group
      rw [this, hy]
      exact J.mul_mem (J.inv_mem hvJ) hvJ'
    exact eq_one_of_mem_inf_of_isPGroup hJt hKz hne hyJ hyK hy2
  · have hJ₂ : conjSub x J ∈ CoreAssembly.conjClass K := conjSub_mem_conjClass hJ x
    have hJ₂t : IsUniqueInvolution (conjSub x J) t := by
      have := hJt.conj x
      have e : x * t * x⁻¹ = t := by
        rw [mul_inv_eq_iff_eq_mul]
        exact hxt
      rwa [e] at this
    have hJne : conjSub x J ≠ J := fun h => hxJ (AscHypOmega.mem_normalizer_of_conjSub_eq h)
    obtain ⟨-, -, hcomm⟩ := twin_facts_general hq hp2 hKm hJ₂ hJ hJ₂t hJt hJne
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
        ((Subgroup.normalizer (J : Set G)).inv_mem (Subgroup.le_normalizer hvJ)) hcw.2
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
    exact hKz.unique y hyK (sq_eq_one_of_mem_twin_inter hp2 hq hKm hKc hK' hKK'.symm hyK hyK' hy2)


theorem not_forall_comm_of_twin (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G} {z : G}
    (hKm : IsClassicalMember p f K z) {J : Subgroup G} {t : G}
    (hJ : J ∈ CoreAssembly.conjClass K) (hJt : IsUniqueInvolution J t)
    (htz : z * t = t * z) (htK : t ∈ Subgroup.normalizer (K : Set G))
    {v : G} (hvJ : v ∈ J) (hvz : v * z = z * v)
    (hK' : conjSub v⁻¹ K ∈ CoreAssembly.conjClass K) (hvK : conjSub v⁻¹ K ≠ K)
    {R : Subgroup G} (hR2 : IsPGroup 2 R) (htR : t ∈ R) (hRK : IsSylow2In (R ⊓ K) K)
    (hcomm : ∀ q ∈ R ⊓ K, ∀ q' ∈ R ⊓ conjSub v⁻¹ K, q * q' = q' * q)
    (hconj : ∀ q ∈ R ⊓ K, v⁻¹ * q * v ∈ R ⊓ conjSub v⁻¹ K) :
    ¬ ∀ k ∈ K, ⁅t, k⁆ ∈ oddCoreOf K := by
  classical
  intro htriv
  have hKz : IsUniqueInvolution K z :=
    ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hKm
  have hKc : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hz2 : z * z = 1 := hKz.sq
  have ht2 : t * t = 1 := hJt.sq
  have hJm : IsClassicalMember p f J t := isClassicalMember_of_mem_conjClass hp2 hq hKm hJ hJt
  have hKJ : K ∈ CoreAssembly.conjClass J := conjClass_symm hJ
  have hvz' : v⁻¹ * z * v = z := by
    calc v⁻¹ * z * v = v⁻¹ * (z * v) := by rw [mul_assoc]
      _ = v⁻¹ * (v * z) := by rw [hvz]
      _ = z := by group
  have htQ : ∀ q ∈ R ⊓ K, t * q = q * t := by
    intro q hq'
    have h1 : ⁅t, q⁆ ∈ oddCoreOf K := htriv q hq'.2
    have h2 : ⁅t, q⁆ ∈ R := by
      rw [commutatorElement_def]
      exact R.mul_mem (R.mul_mem (R.mul_mem htR hq'.1) (R.inv_mem htR)) (R.inv_mem hq'.1)
    have h3 : IsPGroup 2 (Subgroup.zpowers ⁅t, q⁆) := hR2.to_le (Subgroup.zpowers_le.mpr h2)
    exact commutatorElement_eq_one_iff_mul_comm.mp
      (eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K) h1 h3)
  obtain ⟨a₁, ha₁, a₂, ha₂, ha₁2, ha₂2, hprod⟩ := exists_two_sq_elements hp2 hq hKm hRK
  have key : ∀ a ∈ R ⊓ K, a * a = z → v⁻¹ * a * v = a * t := by
    intro a ha ha2
    have haK : a ∈ K := ha.2
    have ha2' : IsPGroup 2 (Subgroup.zpowers a) := isPGroup_zpowers_of_sq_eq hz2 ha2
    have hat : a * t = t * a := (htQ a ha).symm
    have haJ : a ∈ Subgroup.normalizer (J : Set G) :=
      mem_normalizer_of_trivial_action hp2 hq hJm hKJ hKz htz htK htriv haK ha2' hat
    have ha'mem : v⁻¹ * a * v ∈ R ⊓ conjSub v⁻¹ K := hconj a ha
    have hcom : a * (v⁻¹ * a * v) = (v⁻¹ * a * v) * a := hcomm a ha _ ha'mem
    have hcom' : (v⁻¹ * a * v) * a⁻¹ = a⁻¹ * (v⁻¹ * a * v) := by
      calc (v⁻¹ * a * v) * a⁻¹ = a⁻¹ * (a * (v⁻¹ * a * v)) * a⁻¹ := by group
        _ = a⁻¹ * ((v⁻¹ * a * v) * a) * a⁻¹ := by rw [hcom]
        _ = a⁻¹ * (v⁻¹ * a * v) := by group
    have hd : a⁻¹ * (v⁻¹ * a * v) ∈ J := by
      have h1 : a⁻¹ * v⁻¹ * a⁻¹⁻¹ ∈ J :=
        (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (J : Set G)).inv_mem haJ) v⁻¹).mp
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
      have ha4 : orderOf a = 4 := orderOf_eq_four_of_sq_eq hz2 hKz.ne_one ha2
      exact hvK (eq_of_mem_of_mem hp2 hq hKm hKc hK' haK haK' ha2' (by omega)).symm
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
  exact hprod (sq_eq_one_of_mem_twin_inter hp2 hq hKm hKc hK' hvK.symm hprodmem.2 hmemK' hpg)


theorem big_order_contradiction (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G} {z : G}
    (hKm : IsClassicalMember p f K z) {J : Subgroup G} {t : G}
    (hJ : J ∈ CoreAssembly.conjClass K) (hJt : IsUniqueInvolution J t) (hne : t ≠ z)
    (htK : t ∈ Subgroup.normalizer (K : Set G)) {v : G} (hvJ : v ∈ J)
    (hv2 : IsPGroup 2 (Subgroup.zpowers v)) (h8 : 8 ≤ orderOf v) (hvz : v * z = z * v)
    (hvK2 : v * v ∈ Subgroup.normalizer (K : Set G))
    (hv : v ∉ Subgroup.normalizer (K : Set G)) : False := by
  classical
  have hKz : IsUniqueInvolution K z :=
    ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hKm
  have hKc : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hz2 : z * z = 1 := hKz.sq
  have ht2 : t * t = 1 := hJt.sq
  have hvK : conjSub v⁻¹ K ≠ K := fun h => by
    have := (Subgroup.normalizer (K : Set G)).inv_mem
      (AscHypOmega.mem_normalizer_of_conjSub_eq h)
    exact hv (by simpa using this)
  have hK'mem : conjSub v⁻¹ K ∈ CoreAssembly.conjClass K := conjSub_mem_conjClass hKc v⁻¹
  have hvz' : v⁻¹ * z * v = z := by
    calc v⁻¹ * z * v = v⁻¹ * (z * v) := by rw [mul_assoc]
      _ = v⁻¹ * (v * z) := by rw [hvz]
      _ = z := by group
  have htz : z * t = t * z := by
    have h := hKz.conj_eq (conjSub_eq_of_mem_normalizer htK)
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  have hvt : v * t = t * v := (hJt.commute_of_mem hvJ).symm
  have hn2 : IsPGroup 2 (Subgroup.zpowers (v * v)) :=
    hv2.to_le (Subgroup.zpowers_le.mpr
      ((Subgroup.zpowers v).mul_mem (Subgroup.mem_zpowers v) (Subgroup.mem_zpowers v)))
  have hnn1 : (v * v) * (v * v) ≠ 1 := by
    intro h
    have h4 : v ^ 4 = 1 := by
      calc v ^ 4 = (v * v) * (v * v) := by simp [pow_succ, mul_assoc]
        _ = 1 := h
    have := orderOf_le_of_pow_eq_one (by norm_num) h4
    omega
  have h4n : 4 ≤ orderOf (v * v) := four_le_orderOf_of_sq_ne_one hn2 hnn1
  have htn : t ∈ Subgroup.zpowers ((v * v) * (v * v)) :=
    mem_zpowers_sq_of_isUniqueInvolution hJt (J.mul_mem hvJ hvJ) hn2 h4n
  obtain ⟨R, hR2, hvR, -, hRK, -, hcomm, hconj⟩ :=
    exists_twin_sylow hp2 hq hKm hKc hKz hv2 hvz hvK hvK2
  have htR : t ∈ R :=
    Subgroup.zpowers_le.mpr (R.mul_mem (R.mul_mem hvR hvR) (R.mul_mem hvR hvR)) htn
  have hnt := not_forall_comm_of_twin hp2 hq hKm hJ hJt htz htK hvJ hvz hK'mem hvK hR2 htR hRK
    hcomm hconj
  obtain ⟨κ, hκ, hκ2, hκt⟩ := exists_inverted_involution_member hp2 hKm hq hR2 hRK htR ht2 htK hnt
  have hκ'mem : v⁻¹ * κ * v ∈ R ⊓ conjSub v⁻¹ K := hconj κ hκ
  have hcomκ : κ * (v⁻¹ * κ * v) = (v⁻¹ * κ * v) * κ := hcomm κ hκ _ hκ'mem
  have hκ'2 : (v⁻¹ * κ * v) * (v⁻¹ * κ * v) = z := by
    calc (v⁻¹ * κ * v) * (v⁻¹ * κ * v) = v⁻¹ * (κ * κ) * v := by group
      _ = v⁻¹ * z * v := by rw [hκ2]
      _ = z := hvz'
  have hxx : (κ * (v⁻¹ * κ * v)) * (κ * (v⁻¹ * κ * v)) = 1 := by
    calc (κ * (v⁻¹ * κ * v)) * (κ * (v⁻¹ * κ * v))
        = κ * ((v⁻¹ * κ * v) * κ) * (v⁻¹ * κ * v) := by group
      _ = κ * (κ * (v⁻¹ * κ * v)) * (v⁻¹ * κ * v) := by rw [hcomκ]
      _ = (κ * κ) * ((v⁻¹ * κ * v) * (v⁻¹ * κ * v)) := by group
      _ = 1 := by rw [hκ2, hκ'2, hz2]
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have htκ : t * κ * t⁻¹ = κ⁻¹ := by
    have : t * κ * t⁻¹ = t⁻¹ * κ * t := by rw [hti]
    rw [this]
    exact hκt
  have htvt : t * v * t⁻¹ = v := by
    rw [mul_inv_eq_iff_eq_mul]
    exact hvt.symm
  have htvt' : t * v⁻¹ * t⁻¹ = v⁻¹ := by
    calc t * v⁻¹ * t⁻¹ = (t * v * t⁻¹)⁻¹ := by group
      _ = v⁻¹ := by rw [htvt]
  have htκ' : t * (v⁻¹ * κ * v) * t⁻¹ = (v⁻¹ * κ * v)⁻¹ := by
    calc t * (v⁻¹ * κ * v) * t⁻¹ = (t * v⁻¹ * t⁻¹) * (t * κ * t⁻¹) * (t * v * t⁻¹) := by group
      _ = v⁻¹ * κ⁻¹ * v := by rw [htvt', htκ, htvt]
      _ = (v⁻¹ * κ * v)⁻¹ := by group
  have hxt : (κ * (v⁻¹ * κ * v)) * t = t * (κ * (v⁻¹ * κ * v)) := by
    have h1 : t * (κ * (v⁻¹ * κ * v)) * t⁻¹ = κ * (v⁻¹ * κ * v) := by
      calc t * (κ * (v⁻¹ * κ * v)) * t⁻¹
          = (t * κ * t⁻¹) * (t * (v⁻¹ * κ * v) * t⁻¹) := by group
        _ = κ⁻¹ * (v⁻¹ * κ * v)⁻¹ := by rw [htκ, htκ']
        _ = ((v⁻¹ * κ * v) * κ)⁻¹ := by group
        _ = (κ * (v⁻¹ * κ * v))⁻¹ := by rw [hcomκ]
        _ = κ * (v⁻¹ * κ * v) := inv_eq_of_mul_eq_one_right hxx
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  have hy : v * ((v * v)⁻¹ * κ * (v * v) * κ⁻¹) =
      (κ * (v⁻¹ * κ * v)) * v * (κ * (v⁻¹ * κ * v))⁻¹ := by
    rw [twin_conj_identity hcomκ]
    group
  have hyR : (v * v)⁻¹ * κ * (v * v) * κ⁻¹ ∈ R :=
    R.mul_mem (R.mul_mem (R.mul_mem (R.inv_mem (R.mul_mem hvR hvR)) hκ.1)
      (R.mul_mem hvR hvR)) (R.inv_mem hκ.1)
  have hyK : (v * v)⁻¹ * κ * (v * v) * κ⁻¹ ∈ K := by
    refine K.mul_mem ?_ (K.inv_mem hκ.2)
    exact (mem_conj_iff_of_mem_normalizer hvK2 κ).mpr hκ.2
  have hyc := eq_one_or_eq_of_twin_conj hp2 hq hKm hJ hJt hne hvJ hR2 hvR hK'mem hvK hxt hy hyR hyK
  have hκz : z * κ = κ⁻¹ := by
    have h4 : (κ * κ) * (κ * κ) = 1 := by rw [hκ2, hz2]
    calc z * κ = κ⁻¹ * ((κ * κ) * (κ * κ)) := by rw [← hκ2]; group
      _ = κ⁻¹ := by rw [h4, mul_one]
  have hinvconj : ∀ m : G, m⁻¹ * κ⁻¹ * m = (m⁻¹ * κ * m)⁻¹ := fun m => by group
  have hmκ : ((v * v) * (v * v))⁻¹ * κ * ((v * v) * (v * v)) = κ := by
    rcases hyc with h1 | h1
    · have h2 : (v * v)⁻¹ * κ * (v * v) = κ := mul_inv_eq_one.mp h1
      calc ((v * v) * (v * v))⁻¹ * κ * ((v * v) * (v * v))
          = (v * v)⁻¹ * ((v * v)⁻¹ * κ * (v * v)) * (v * v) := by group
        _ = κ := by rw [h2, h2]
    · have h2 : (v * v)⁻¹ * κ * (v * v) = κ⁻¹ := by
        have h3 : (v * v)⁻¹ * κ * (v * v) = z * κ := by
          calc (v * v)⁻¹ * κ * (v * v) = ((v * v)⁻¹ * κ * (v * v) * κ⁻¹) * κ := by group
            _ = z * κ := by rw [h1]
        rw [h3, hκz]
      calc ((v * v) * (v * v))⁻¹ * κ * ((v * v) * (v * v))
          = (v * v)⁻¹ * ((v * v)⁻¹ * κ * (v * v)) * (v * v) := by group
        _ = (v * v)⁻¹ * κ⁻¹ * (v * v) := by rw [h2]
        _ = ((v * v)⁻¹ * κ * (v * v))⁻¹ := hinvconj (v * v)
        _ = κ := by rw [h2, inv_inv]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp htn
  have hκm : κ * ((v * v) * (v * v)) = ((v * v) * (v * v)) * κ := by
    calc κ * ((v * v) * (v * v))
        = ((v * v) * (v * v)) * (((v * v) * (v * v))⁻¹ * κ * ((v * v) * (v * v))) := by group
      _ = ((v * v) * (v * v)) * κ := by rw [hmκ]
  have hκt' : κ * t = t * κ := by
    rw [← hk]
    exact (Commute.zpow_right (show Commute κ ((v * v) * (v * v)) from hκm) k).eq
  have h1 : t⁻¹ * κ * t = κ := by
    calc t⁻¹ * κ * t = t⁻¹ * (κ * t) := by group
      _ = t⁻¹ * (t * κ) := by rw [hκt']
      _ = κ := by group
  have h2 : κ = κ⁻¹ := h1.symm.trans hκt
  have h3 : κ * κ = 1 := by
    calc κ * κ = κ * κ⁻¹ := by rw [← h2]
      _ = 1 := mul_inv_cancel κ
  exact hKz.ne_one (hκ2.symm.trans h3)

end CFSG.ClassicalInvolution.Asc77.AscFusion
