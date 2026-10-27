module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714Stmt
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorReduction

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG
open scoped commutatorElement

section Layer

variable {C : Type} [Group C]

theorem exists_component_not_ker {A : Type*} [Group A] (π : ↥(layer C) →* A) (h : ∃ x, π x ≠ 1) :
    ∃ B : Subgroup C, IsComponent B ∧ ¬ (B.subgroupOf (layer C) ≤ π.ker) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hx⟩ := h
  have key : ∀ y : C, y ∈ layer C → ∃ hy : y ∈ layer C, π ⟨y, hy⟩ = 1 := by
    intro y hy
    have hy' : y ∈ ⨆ K : {K : Subgroup C // IsComponent K}, K.1 := by
      rw [layer, sSup_eq_iSup'] at hy
      exact hy
    refine Subgroup.iSup_induction (fun K : {K : Subgroup C // IsComponent K} => K.1)
      (C := fun y => ∃ hy : y ∈ layer C, π ⟨y, hy⟩ = 1) hy' ?_ ?_ ?_
    · intro K y hyK
      have hKE : K.1 ≤ layer C := le_sSup K.2
      have hyE : y ∈ layer C := hKE hyK
      refine ⟨hyE, ?_⟩
      have h1 : (⟨y, hyE⟩ : ↥(layer C)) ∈ K.1.subgroupOf (layer C) := hyK
      exact MonoidHom.mem_ker.mp (hcon K.1 K.2 h1)
    · exact ⟨(layer C).one_mem, map_one π⟩
    · rintro a b ⟨ha, ha1⟩ ⟨hb, hb1⟩
      refine ⟨(layer C).mul_mem ha hb, ?_⟩
      have : (⟨a * b, (layer C).mul_mem ha hb⟩ : ↥(layer C)) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
      rw [this, map_mul, ha1, hb1, mul_one]
  obtain ⟨hy, h1⟩ := key x.1 x.2
  exact hx (by simpa using h1)

theorem map_eq_top_of_component {A : Type*} [Group A] [IsSimpleGroup A] (π : ↥(layer C) →* A)
    (hπ : Function.Surjective π) {B : Subgroup C} (hB : IsComponent B)
    (hn : ¬ (B.subgroupOf (layer C) ≤ π.ker)) : (B.subgroupOf (layer C)).map π = ⊤ := by
  have hBE : B ≤ layer C := le_sSup hB
  have hsub : (B.subgroupOf (layer C)).IsSubnormal := (LocalCores.component_overgroup hB hBE).2
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup inferInstance
    (Subgroup.IsSubnormal.map hπ hsub) with h | h
  · exact absurd ((Subgroup.map_eq_bot_iff _).mp h) hn
  · exact h

variable [Finite C]

theorem component_eq_of_map_eq_top {A : Type*} [Group A] (hA : ∃ a b : A, a * b ≠ b * a)
    (π : ↥(layer C) →* A) {B B' : Subgroup C} (hB : IsComponent B) (hB' : IsComponent B')
    (h : (B.subgroupOf (layer C)).map π = ⊤) (h' : (B'.subgroupOf (layer C)).map π = ⊤) :
    B = B' := by
  rcases LocalCores.distinct_components_commute hB hB' with h1 | h1
  · exact h1
  · exfalso
    obtain ⟨a, b, hab⟩ := hA
    have ha : a ∈ (B.subgroupOf (layer C)).map π := by rw [h]; trivial
    have hb : b ∈ (B'.subgroupOf (layer C)).map π := by rw [h']; trivial
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    apply hab
    have hxC : (x : C) ∈ B := hx
    have hyC : (y : C) ∈ B' := hy
    have hc : ⁅(x : C), (y : C)⁆ = 1 := by
      have := Subgroup.commutator_mem_commutator hxC hyC
      rw [h1] at this
      exact this
    have key : ∀ u v : C, ⁅u, v⁆ = 1 → u * v = v * u := by
      intro u v huv
      rw [commutatorElement_def] at huv
      calc u * v = (u * v * u⁻¹ * v⁻¹) * (v * u) := by group
        _ = v * u := by rw [huv, one_mul]
    have : (x : C) * y = y * x := key _ _ hc
    have h3 : x * y = y * x := Subtype.ext this
    rw [← map_mul, ← map_mul, h3]

omit [Finite C] in
theorem map_conj_eq_top {E : Subgroup C} [E.Normal] {A : Type*} [Group A] (O : Subgroup ↥E) [O.Normal]
    (hO : O.Characteristic) (φ : ↥E ⧸ O ≃* A) {B : Subgroup C}
    (hB : (B.subgroupOf E).map (φ.toMonoidHom.comp (QuotientGroup.mk' O)) = ⊤) (c : C) :
    ((B.map (MulAut.conj c).toMonoidHom).subgroupOf E).map
      (φ.toMonoidHom.comp (QuotientGroup.mk' O)) = ⊤ := by
  classical
  let γ : ↥E ≃* ↥E := MulAut.conjNormal c
  have hγO : O.map γ.toMonoidHom = O := Subgroup.characteristic_iff_map_eq.mp hO γ
  have hle : O ≤ O.comap γ.toMonoidHom := Subgroup.map_le_iff_le_comap.mp hγO.le
  let Γ : ↥E ⧸ O →* ↥E ⧸ O := QuotientGroup.map O O γ.toMonoidHom hle
  have hsurj : (B.subgroupOf E).map (QuotientGroup.mk' O) = ⊤ := by
    have h1 : ((B.subgroupOf E).map (QuotientGroup.mk' O)).map φ.toMonoidHom = ⊤ := by
      rw [Subgroup.map_map]
      exact hB
    have h2 : ((⊤ : Subgroup (↥E ⧸ O))).map φ.toMonoidHom = ⊤ :=
      Subgroup.map_top_of_surjective _ φ.surjective
    exact Subgroup.map_injective φ.injective (h1.trans h2.symm)
  rw [eq_top_iff]
  intro a _
  obtain ⟨y1, hy1⟩ := QuotientGroup.mk_surjective (φ.symm a)
  obtain ⟨b, hb, hbq⟩ : ∃ b ∈ B.subgroupOf E, QuotientGroup.mk' O b = QuotientGroup.mk (γ.symm y1) := by
    have : QuotientGroup.mk' O (γ.symm y1) ∈ (B.subgroupOf E).map (QuotientGroup.mk' O) := by
      rw [hsurj]
      trivial
    exact this
  refine ⟨γ b, ?_, ?_⟩
  · show ((γ b : ↥E) : C) ∈ B.map (MulAut.conj c).toMonoidHom
    refine ⟨(b : C), hb, ?_⟩
    simp [γ, MulAut.conjNormal_apply]
  · show φ (QuotientGroup.mk' O (γ b)) = a
    have h1 : QuotientGroup.mk' O (γ b) = Γ (QuotientGroup.mk' O b) := by
      simp [Γ, QuotientGroup.map_mk]
    rw [h1, hbq]
    have h2 : Γ (QuotientGroup.mk (γ.symm y1)) = QuotientGroup.mk y1 := by
      simp [Γ, QuotientGroup.map_mk]
    rw [h2, hy1]
    simp

theorem exists_alt7_component
    (h : Nonempty (↥(layer C) ⧸ pPrimeCore 2 ↥(layer C) ≃* alternatingGroup (Fin 7))) :
    ∃ B : Subgroup C, IsComponent B ∧ B.Normal ∧
      Nonempty (↥B ⧸ center ↥B ≃* alternatingGroup (Fin 7)) ∧ Odd (Nat.card ↥(center ↥B)) := by
  classical
  obtain ⟨φ⟩ := h
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by norm_num)
  have hnonab : ∃ a b : alternatingGroup (Fin 7), a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hnc : ¬ IsMulCommutative (alternatingGroup (Fin 7)) := by
      rw [alternatingGroup.isMulCommutative_iff_card_le_three]
      simp
    exact hnc ⟨⟨fun a b => hcon a b⟩⟩
  have hch : (layer C).Characteristic := LocalCores.layer_characteristic
  have hEn : (layer C).Normal := inferInstance
  have hOn : (pPrimeCore 2 ↥(layer C)).Normal := pPrimeCore_normal
  have hOchar : (pPrimeCore 2 ↥(layer C)).Characteristic := pPrimeCore_characteristic
  let q : ↥(layer C) →* ↥(layer C) ⧸ pPrimeCore 2 ↥(layer C) := QuotientGroup.mk' _
  let π : ↥(layer C) →* alternatingGroup (Fin 7) := φ.toMonoidHom.comp q
  have hπ : Function.Surjective π := φ.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨a, ha⟩ : ∃ a : alternatingGroup (Fin 7), a ≠ 1 := by
    obtain ⟨a, b, hab⟩ := hnonab
    by_cases h1 : a = 1
    · exact ⟨b, fun hb => hab (by rw [h1, hb])⟩
    · exact ⟨a, h1⟩
  obtain ⟨x, hx⟩ := hπ a
  obtain ⟨B, hB, hBn⟩ := exists_component_not_ker π ⟨x, by rw [hx]; exact ha⟩
  have htop := map_eq_top_of_component π hπ hB hBn
  have hBE : B ≤ layer C := le_sSup hB
  let ι : ↥B →* ↥(layer C) := Subgroup.inclusion hBE
  let σ : ↥B →* alternatingGroup (Fin 7) := π.comp ι
  have hσ : Function.Surjective σ := by
    intro a
    have : a ∈ (B.subgroupOf (layer C)).map π := by rw [htop]; trivial
    obtain ⟨y, hy, hya⟩ := this
    exact ⟨⟨y, hy⟩, hya⟩
  have hker : σ.ker ≤ center ↥B := by
    rcases LocalCores.quasisimple_normal_subgroups hB.1 σ.normal_ker with h1 | h1
    · exfalso
      obtain ⟨a, b, hab⟩ := hnonab
      obtain ⟨a', rfl⟩ := hσ a
      obtain ⟨b', rfl⟩ := hσ b
      apply hab
      have h2 : σ a' = 1 := MonoidHom.mem_ker.mp (by rw [h1]; trivial)
      have h3 : σ b' = 1 := MonoidHom.mem_ker.mp (by rw [h1]; trivial)
      rw [h2, h3]
    · exact h1
  have hcenA : center (alternatingGroup (Fin 7)) = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (center (alternatingGroup (Fin 7))) with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨a, b, hab⟩ := hnonab
      apply hab
      have : a ∈ center (alternatingGroup (Fin 7)) := by rw [h1]; trivial
      exact (Subgroup.mem_center_iff.mp this b).symm
  have hcen : center ↥B ≤ σ.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    have : σ z ∈ center (alternatingGroup (Fin 7)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨b, rfl⟩ := hσ g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz b]
    rw [hcenA] at this
    exact this
  have hEq : center ↥B = σ.ker := le_antisymm hcen hker
  refine ⟨B, hB, ?_, ?_, ?_⟩
  · refine ⟨fun n hn g => ?_⟩
    have hBc : IsComponent (B.map (MulAut.conj g).toMonoidHom) :=
      LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hB
    have hconj := map_conj_eq_top (pPrimeCore 2 ↥(layer C)) hOchar φ (B := B) htop g
    have heq := component_eq_of_map_eq_top hnonab π hB hBc htop hconj
    have hmem : g * n * g⁻¹ ∈ B.map (MulAut.conj g).toMonoidHom :=
      ⟨n, hn, by simp [MulAut.conj_apply]⟩
    rw [← heq] at hmem
    exact hmem
  · exact ⟨(QuotientGroup.quotientMulEquivOfEq hEq).trans
      (QuotientGroup.quotientKerEquivOfSurjective σ hσ)⟩
  · have hsub : σ.ker.map ι ≤ pPrimeCore 2 ↥(layer C) := by
      rintro _ ⟨z, hz, rfl⟩
      have h1 : π (ι z) = 1 := hz
      have h2 : φ (q (ι z)) = 1 := h1
      have h3 : q (ι z) = 1 := φ.injective (by rw [h2, map_one])
      have h4 : ι z ∈ (QuotientGroup.mk' (pPrimeCore 2 ↥(layer C))).ker := h3
      rwa [QuotientGroup.ker_mk'] at h4
    have hdvd : Nat.card σ.ker ∣ Nat.card (pPrimeCore 2 ↥(layer C)) := by
      have := Subgroup.card_dvd_of_le hsub
      rwa [Subgroup.card_map_of_injective (Subgroup.inclusion_injective hBE)] at this
    have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥(layer C))) := pPrimeCore_coprime_card
    rw [hEq]
    exact Nat.coprime_two_left.mp (Nat.Coprime.coprime_dvd_right hdvd hcop)

end Layer

end CFSG.GH74.GLS.IVK.Proofs2

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.GH74.GLS.IVK.Proofs2 CFSG.ComponentClassification.ExcSelector

theorem card_alt7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem Ivk714Hyp.two_five_two_zero_dvd {K : Type} [Group K] [Finite K] {z : MulAut K}
    (h : Ivk714Hyp K z) : 2520 ∣ Nat.card ↥(fixedSubgroup K z) := by
  obtain ⟨φ⟩ := h
  have h1 : Nat.card (↥(layer ↥(fixedSubgroup K z)) ⧸ pPrimeCore 2 ↥(layer ↥(fixedSubgroup K z))) =
      2520 := by
    rw [Nat.card_congr φ.toEquiv]
    exact card_alt7
  have h2 := Subgroup.card_quotient_dvd_card (pPrimeCore 2 ↥(layer ↥(fixedSubgroup K z)))
  have h3 := Subgroup.card_subgroup_dvd_card (layer ↥(fixedSubgroup K z))
  rw [h1] at h2
  exact h2.trans h3

theorem Ivk714Hyp.exists_component {K : Type} [Group K] [Finite K] {z : MulAut K}
    (h : Ivk714Hyp K z) :
    ∃ B : Subgroup K, CFSG.Assembly.IsComponentOf B (fixedSubgroup K z) ∧
      (B.subgroupOf (fixedSubgroup K z)).Normal ∧
      Nonempty (↥B ⧸ center ↥B ≃* alternatingGroup (Fin 7)) ∧ Odd (Nat.card ↥(center ↥B)) := by
  obtain ⟨B, hB, hBn, ⟨hq⟩, hodd⟩ := exists_alt7_component (C := ↥(fixedSubgroup K z)) h
  have hsub : (B.map (fixedSubgroup K z).subtype).subgroupOf (fixedSubgroup K z) = B :=
    Subgroup.comap_map_eq_self_of_injective (fixedSubgroup K z).subtype_injective B
  have hle : B.map (fixedSubgroup K z).subtype ≤ fixedSubgroup K z := by
    rintro _ ⟨b, -, rfl⟩
    exact b.2
  let e : ↥B ≃* ↥(B.map (fixedSubgroup K z).subtype) :=
    B.equivMapOfInjective (fixedSubgroup K z).subtype (fixedSubgroup K z).subtype_injective
  refine ⟨B.map (fixedSubgroup K z).subtype, ?_, ?_, ?_, ?_⟩
  · rw [LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hle, hsub]
    exact hB
  · rw [hsub]
    exact hBn
  · exact ⟨(centralQuotientCongr e).symm.trans hq⟩
  · have hc : (center ↥B).map e.toMonoidHom = center ↥(B.map (fixedSubgroup K z).subtype) :=
      Subgroup.map_center_eq e
    rw [← hc, Subgroup.card_map_of_injective e.injective]
    exact hodd

theorem Ivk714Hyp.false_of_noSmallComponent {K : Type} [Group K] [Finite K]
    (hNS : NoSmallComponent K) {z : MulAut K} (hz : orderOf z = 2) (h : Ivk714Hyp K z) : False := by
  obtain ⟨B, hB, hBn, ⟨hq⟩, hodd⟩ := h.exists_component
  have hz2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hz
    omega
  exact hNS z hz2 hz1 B hB hBn (Or.inr (Or.inl ⟨⟨hq⟩, hodd⟩))

end CFSG.GH74.GLS.IVK
