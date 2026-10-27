module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Lattice57
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Fixed57
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.XStruct

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.TwoFi22
open scoped commutatorElement

variable {G : Type} [Group G]

theorem exists_mem_normalizer_not_mem [Finite G] {P R : Subgroup G} (hP : IsPGroup 2 P)
    (hlt : R < P) : ∃ u ∈ P, u ∈ normalizer (R : Set G) ∧ u ∉ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent ↥P := hP.isNilpotent
  have hne : R.subgroupOf P < ⊤ := by
    refine lt_top_iff_ne_top.2 (fun h => hlt.not_ge ?_)
    exact Subgroup.subgroupOf_eq_top.1 h
  have hlt' := Group.normalizerCondition_of_isNilpotent _ hne
  obtain ⟨y, hyN, hyH⟩ := IsConcreteLE.exists_of_lt hlt'
  have hRP : R ≤ P := hlt.le
  refine ⟨(y : G), y.2, ?_, fun h => hyH (mem_subgroupOf.2 h)⟩
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have := (mem_normalizer_iff.1 hyN ⟨h, hRP hh⟩).1 (mem_subgroupOf.2 hh)
    exact mem_subgroupOf.1 this
  · intro hh
    have hhP : h ∈ P := by
      have h1 : (y : G)⁻¹ * ((y : G) * h * (y : G)⁻¹) * (y : G) ∈ P :=
        mul_mem (mul_mem (inv_mem y.2) (hRP hh)) y.2
      have e : (y : G)⁻¹ * ((y : G) * h * (y : G)⁻¹) * (y : G) = h := by group
      rwa [e] at h1
    have := (mem_normalizer_iff.1 hyN ⟨h, hhP⟩).2 (mem_subgroupOf.2 hh)
    exact mem_subgroupOf.1 this

theorem commutator_mem_zpowers_of_extraspecial [Finite G] {R : Subgroup G}
    (hext : CFSG.IsExtraspecialPGroup 2 ↥R) {z : G} (hzR : z ∈ R) (hz2 : orderOf z = 2)
    (hzc : ∀ r ∈ R, r * z = z * r) : ∀ a ∈ R, ∀ b ∈ R, ⁅a, b⁆ ∈ zpowers z := by
  intro a ha b hb
  obtain ⟨-, hcom, -, hcard⟩ := hext
  have hzRc : (⟨z, hzR⟩ : ↥R) ∈ center ↥R := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (hzc g g.2)
  have hord : orderOf (⟨z, hzR⟩ : ↥R) = 2 := (Subgroup.orderOf_mk z hzR).trans hz2
  have hcen : zpowers (⟨z, hzR⟩ : ↥R) = center ↥R := by
    refine Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hzRc) ?_
    rw [Nat.card_zpowers, hord, hcard]
  have hmem : ⁅(⟨a, ha⟩ : ↥R), (⟨b, hb⟩ : ↥R)⁆ ∈ center ↥R := by
    rw [← hcom]
    exact Subgroup.commutator_mem_commutator (mem_top _) (mem_top _)
  rw [← hcen] at hmem
  obtain ⟨n, hn⟩ := mem_zpowers_iff.1 hmem
  have := congrArg Subtype.val hn
  simp only [Subgroup.coe_zpow] at this
  exact mem_zpowers_iff.2 ⟨n, this⟩

theorem mem_normPair_of_conj_t [Finite G] {z t u : G} (hz : u * z = z * u)
    (ht : u * t * u⁻¹ = t ∨ u * t * u⁻¹ = t * z) : u ∈ normPair z t := by
  rcases ht with h | h
  · apply centPair_le_normPair
    rw [mem_centPair_iff]
    refine ⟨hz.symm, ?_⟩
    calc t * u = (u * t * u⁻¹) * u := by rw [h]
      _ = u * t := by group
  · exact mem_normPair_of_swap hz h

section Main

variable [Finite G] {t z : G}

theorem Level55.lattice57 (d : Level55 G t z) (h54 : IsTwoConstrained (centZ z)) {x : G}
    (hxz : x * z = z * x) (hxt : x * t * x⁻¹ = t * z)
    (hxN : x ∈ normalizer ((O2In (centPair z t) : Subgroup G) : Set G))
    (hxK : ∀ k ∈ centPair z t, x * k * x⁻¹ * k⁻¹ ∈ O2In (centPair z t))
    (hx2 : x ^ 2 ∈ O2In (centPair z t)) (hxn : x ∉ O2In (centPair z t))
    (hext : CFSG.IsExtraspecialPGroup 2 ↥(Rsub z t)) :
    Lattice57 G (centPair z t) (O2In (centPair z t)) (Rsub z t) z t := by
  have hRY : Rsub z t = O2In (centPair z t) ⊔ zpowers x :=
    d.O2In_normPair_eq h54 hxz hxt hxN hxK hx2 hxn
  have hzz := d.z_mul_self
  have hYz : ∀ y ∈ O2In (centPair z t), y * z = z * y := fun y hy =>
    (mem_centPair_iff.1 (O2In_le _ hy)).1.symm
  have hYt : ∀ y ∈ O2In (centPair z t), y * t = t * y := fun y hy =>
    (mem_centPair_iff.1 (O2In_le _ hy)).2.symm
  have hRcases : ∀ a ∈ Rsub z t, a ∈ O2In (centPair z t) ∨
      ∃ y ∈ O2In (centPair z t), a = y * x := by
    intro a ha
    rw [hRY] at ha
    rcases mem_or_exists_mul_of_mem_sup_zpowers hxN hx2 ha with h | ⟨r, hr, rfl⟩
    · exact Or.inl h
    · exact Or.inr ⟨r, hr, rfl⟩
  have hzcen : ∀ r ∈ Rsub z t, r * z = z * r := by
    intro r hr
    rcases hRcases r hr with h | ⟨y, hy, rfl⟩
    · exact hYz r h
    · calc y * x * z = y * (x * z) := by rw [mul_assoc]
        _ = y * (z * x) := by rw [hxz]
        _ = (y * z) * x := by rw [mul_assoc]
        _ = (z * y) * x := by rw [hYz y hy]
        _ = z * (y * x) := by rw [mul_assoc]
  have hYR : O2In (centPair z t) ≤ Rsub z t := by
    rw [hRY]; exact le_sup_left
  have hzY : z ∈ O2In (centPair z t) := d.pair_le_O2K (z_mem_pair z t)
  have htY : t ∈ O2In (centPair z t) := d.pair_le_O2K (t_mem_pair z t)
  exact
    { z_ord := d.z_ord
      t_ord := d.t_ord
      zt_comm := d.zt_comm
      z_mem := hzY
      t_mem := htY
      Y_le_R := hYR
      Y_le_K := O2In_le _
      t_mem_K := mem_centPair_iff.2 ⟨d.zt_comm, rfl⟩
      K_z := fun k hk => (mem_centPair_iff.1 hk).1.symm
      K_t := fun k hk => (mem_centPair_iff.1 hk).2.symm
      K_Y := fun k hk y hy => (normal_subgroupOf_O2In (centPair z t)).conj_mem
        ⟨y, O2In_le _ hy⟩ (mem_subgroupOf.2 hy) ⟨k, hk⟩
      z_central := hzcen
      R_comm := commutator_mem_zpowers_of_extraspecial hext (hYR hzY) d.z_ord hzcen
      index := by
        intro a ha b hb haY hbY
        rcases hRcases a ha with h | ⟨y₁, hy₁, rfl⟩
        · exact absurd h haY
        rcases hRcases b hb with h | ⟨y₂, hy₂, rfl⟩
        · exact absurd h hbY
        have e : (y₁ * x)⁻¹ * (y₂ * x) = x⁻¹ * (y₁⁻¹ * y₂) * x := by group
        rw [e]
        have := (mem_normalizer_iff.1 (inv_mem hxN) _).1 (mul_mem (inv_mem hy₁) hy₂)
        simpa using this
      swap := by
        intro a ha haY
        rcases hRcases a ha with h | ⟨y, hy, rfl⟩
        · exact absurd h haY
        have hy1 : y * (t * z) = (t * z) * y := by
          calc y * (t * z) = (y * t) * z := by rw [mul_assoc]
            _ = (t * y) * z := by rw [hYt y hy]
            _ = t * (y * z) := by rw [mul_assoc]
            _ = t * (z * y) := by rw [hYz y hy]
            _ = (t * z) * y := by rw [mul_assoc]
        calc y * x * t * (y * x)⁻¹ = y * (x * t * x⁻¹) * y⁻¹ := by group
          _ = y * (t * z) * y⁻¹ := by rw [hxt]
          _ = (t * z) * y * y⁻¹ := by rw [hy1]
          _ = t * z := by group
      irred := d.irred
      nonsplit := by
        intro A₁ hA₁Y hA₁K hzA₁ hcos
        have hle : ⁅d.R0, centPair z t⁆ ≤ A₁ := by
          rw [Subgroup.commutator_le]
          intro r hr k hk
          have hrY : r ∈ O2In (centPair z t) := d.R0_le_O2K hr
          have hkt : k * t * k⁻¹ = t := by
            have := (mem_centPair_iff.1 hk).2
            calc k * t * k⁻¹ = (t * k) * k⁻¹ := by rw [this]
              _ = t := by group
          rcases hcos r hrY with hrA | hrtA
          · have h1 := hA₁K k hk r⁻¹ (inv_mem hrA)
            have e : ⁅r, k⁆ = r * (k * r⁻¹ * k⁻¹) := by
              simp only [commutatorElement_def]; group
            rw [e]
            exact mul_mem hrA h1
          · have h1 := hA₁K k hk _ hrtA
            have e1 : k * (r * t) * k⁻¹ = (k * r * k⁻¹) * t := by
              calc k * (r * t) * k⁻¹ = (k * r * k⁻¹) * (k * t * k⁻¹) := by group
                _ = (k * r * k⁻¹) * t := by rw [hkt]
            have e : ⁅r, k⁆ = (r * t) * (k * (r * t) * k⁻¹)⁻¹ := by
              rw [e1]
              simp only [commutatorElement_def]; group
            rw [e]
            exact mul_mem hrtA (inv_mem h1)
        exact hle d.t_mem_comm }

theorem Level55.psub_le_rsub (d : Level55 G t z) (h54 : IsTwoConstrained (centZ z))
    (hext : CFSG.IsExtraspecialPGroup 2 ↥(Rsub z t)) (hcard : Nat.card (Rsub z t) = 2 ^ 25)
    (hle : Rsub z t ≤ Psub z) (hY : O2In (centPair z t) ≤ Psub z) : Psub z ≤ Rsub z t := by
  by_contra hPR
  have hRP : Rsub z t < Psub z := lt_of_le_of_ne hle (fun h => hPR (h ▸ le_rfl))
  have hcardY : Nat.card (O2In (centPair z t)) = 2 ^ 24 := by
    rw [d.O2K, card_sup_zpowers_of_orderOf_eq_two d.t_ord d.t_not_mem
      (fun r hr => d.R0_comm_t hr), d.R0_card]
    norm_num
  have hlt : O2In (centPair z t) < Psub z := by
    refine lt_of_le_of_ne hY (fun hEq => ?_)
    have h1 : Nat.card (Rsub z t) ≤ Nat.card (O2In (centPair z t)) :=
      Subgroup.card_le_of_le (by rw [hEq]; exact hle)
    rw [hcard, hcardY] at h1
    norm_num at h1
  obtain ⟨x, hxP, hxn, hxz, hxt, hxN, hxK, hx2⟩ := d.exists_x_of_lt hlt
  have hNC : normPair z t ≤ centZ z := d.normPair_le_centZ h54 hxz hxt
  have hLat := d.lattice57 h54 hxz hxt hxN hxK hx2 hxn hext
  obtain ⟨u₀, hu₀P, hu₀N, hu₀R⟩ := exists_mem_normalizer_not_mem (isPGroup_O2In (centZ z)) hRP
  set U : Subgroup G := Psub z ⊓ normalizer (Rsub z t : Set G) with hUdef
  have hUP : IsPGroup 2 U := (isPGroup_O2In (centZ z)).to_le inf_le_left
  have hRU : Rsub z t ≤ U := le_inf hle le_normalizer
  have hUR : ∀ u ∈ U, ∀ r ∈ Rsub z t, u * r * u⁻¹ ∈ Rsub z t := fun u hu r hr =>
    (mem_normalizer_iff.1 (mem_inf.1 hu).2 r).1 hr
  have hUz : ∀ u ∈ U, u * z = z * u := fun u hu =>
    mem_centralizer_singleton_iff.1 (O2In_le _ (mem_inf.1 hu).1)
  have hzR : z ∈ Rsub z t := hLat.Y_le_R hLat.z_mem
  have htR : t ∈ Rsub z t := hLat.Y_le_R hLat.t_mem
  have htz : t ∉ zpowers z := by
    intro ht
    rcases eq_one_or_eq_of_mem_zpowers_two d.z_ord ht with h | h
    · have := d.t_ord
      rw [h, orderOf_one] at this
      omega
    · exact d.z_ne_t h.symm
  have hKN : ∀ k ∈ centPair z t, k ∈ normalizer (Rsub z t : Set G) := fun k hk =>
    mem_normalizer_O2In (centPair_le_normPair z t hk)
  have hKU : ∀ k ∈ centPair z t, ∀ u ∈ U, k * u * k⁻¹ ∈ U := by
    intro k hk u hu
    refine mem_inf.2 ⟨?_, mul_mem (mul_mem (hKN k hk) (mem_inf.1 hu).2) (inv_mem (hKN k hk))⟩
    exact (normal_subgroupOf_O2In (centZ z)).conj_mem ⟨u, O2In_le _ (mem_inf.1 hu).1⟩
      (mem_subgroupOf.2 (mem_inf.1 hu).1) ⟨k, centPair_le_centZ z t hk⟩
  obtain ⟨a, haR, haz, ha⟩ := exists_mem_commutator_mem_zpowers hUP hRU hUR hUz
    ⟨t, htR, htz⟩
  have hzW : ∀ r ∈ Rsub z t, r * z * r⁻¹ ∈ zpowers z := fun r hr => by
    rw [mul_inv_eq_iff_eq_mul.2 (hLat.z_central r hr)]
    exact mem_zpowers z
  let A : Subgroup G :=
    { carrier := {r | r ∈ Rsub z t ∧ ∀ u ∈ U, ⁅u, r⁆ ∈ zpowers z}
      one_mem' := ⟨one_mem _, fun u _ => by rw [commutatorElement_one_right]; exact one_mem _⟩
      mul_mem' := by
        rintro r r' ⟨hr, hrU⟩ ⟨hr', hr'U⟩
        refine ⟨mul_mem hr hr', fun u hu => ?_⟩
        have e : ⁅u, r * r'⁆ = ⁅u, r⁆ * (r * ⁅u, r'⁆ * r⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact mul_mem (hrU u hu) (conj_mem_zpowers_of_conj_mem (hzW r hr) _ (hr'U u hu))
      inv_mem' := by
        rintro r ⟨hr, hrU⟩
        refine ⟨inv_mem hr, fun u hu => ?_⟩
        have e : ⁅u, r⁻¹⁆ = r⁻¹ * ⁅u, r⁆⁻¹ * r⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact conj_mem_zpowers_of_conj_mem (hzW r⁻¹ (inv_mem hr)) _ (inv_mem (hrU u hu)) }
  have hAR : A ≤ Rsub z t := fun r hr => hr.1
  have hzA : z ∈ A := ⟨hzR, fun u hu => by
    rw [commutatorElement_eq_one_iff_mul_comm.2 (hUz u hu)]
    exact one_mem _⟩
  have hAK : ∀ k ∈ centPair z t, ∀ r ∈ A, k * r * k⁻¹ ∈ A := by
    intro k hk r hr
    refine ⟨(mem_normalizer_iff.1 (hKN k hk) r).1 hr.1, fun u hu => ?_⟩
    have e : ⁅u, k * r * k⁻¹⁆ = k * ⁅k⁻¹ * u * k, r⁆ * k⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    have hu' : k⁻¹ * u * k ∈ U := by
      have := hKU k⁻¹ (inv_mem hk) u hu
      rwa [inv_inv] at this
    exact hLat.conj_zpowers_z hk _ (hr.2 _ hu')
  have htA : t ∈ A := hLat.mem_of_invariant hAR hzA hAK ⟨a, ⟨haR, ha⟩, haz⟩
  have hUN : U ≤ normPair z t := by
    intro u hu
    have hut : ⁅u, t⁆ ∈ zpowers z := htA.2 u hu
    refine mem_normPair_of_conj_t (hUz u hu) ?_
    rcases eq_one_or_eq_of_mem_zpowers_two d.z_ord hut with h | h
    · left
      exact mul_inv_eq_one.1 h
    · right
      have h' : u * t * u⁻¹ * t⁻¹ = z := h
      calc u * t * u⁻¹ = (u * t * u⁻¹ * t⁻¹) * t := by group
        _ = z * t := by rw [h']
        _ = t * z := d.zt_comm
  have hUnorm : (U.subgroupOf (normPair z t)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    have hgP : (g : G) ∈ normalizer (Psub z : Set G) := mem_normalizer_O2In (hNC g.2)
    have hgR : (g : G) ∈ normalizer (Rsub z t : Set G) := mem_normalizer_O2In g.2
    refine mem_inf.2 ⟨?_, mul_mem (mul_mem hgR (mem_inf.1 hn).2) (inv_mem hgR)⟩
    exact (mem_normalizer_iff.1 hgP n).1 (mem_inf.1 hn).1
  have hUle : U ≤ O2In (normPair z t) := le_O2In hUN hUnorm hUP
  exact hu₀R (hUle (mem_inf.2 ⟨hu₀P, hu₀N⟩))

end Main

section Certified

theorem ds81Lemma57Direct :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t z : G),
      Setting G L t → CentralPair G L t z → IsTwoConstrained (centZ z) → Conclusion55 G L t z →
        Psub z ≤ Rsub z t := by
  intro G _ _ L t z hS hc h54 h55
  obtain ⟨d⟩ := hS.exists_level55 hc h55.centralizer_eq
  exact d.psub_le_rsub h54 h55.extraspecial h55.card h55.le_P h55.o2K_le

end Certified

end CFSG.EvenSporadicStandard.TwoB
