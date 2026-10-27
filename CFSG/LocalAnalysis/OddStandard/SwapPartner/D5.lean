module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.LemmaGElt
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.WpGTypes

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern

variable {G : Type} [Group G] {z : G} {ι : Perm (Fin 10) →* G} {g : G}

private theorem centData_ne_one (hC : CentData z ι) : z ≠ 1 := by
  intro h
  have h2 : orderOf z = 1 := by rw [h, orderOf_one]
  rw [hC.order] at h2
  exact absurd h2 (by norm_num)

private theorem Egrp_le_Dgrp (hC : CentData z ι) (hg : GElt z ι g) :
    Egrp z ι ≤ Dgrp z g := by
  apply sup_le
  · apply Subgroup.zpowers_le.2
    exact Subgroup.subset_closure (by simp)
  · apply Subgroup.zpowers_le.2
    rw [← hg.conj_z]
    exact (Dgrp z g).mul_mem ((Dgrp z g).mul_mem (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))) ((Dgrp z g).inv_mem (Subgroup.subset_closure (by simp)))

private theorem eq_z_or_eq_x1_of_mem_Egrp_of_isConj (hC : CentData z ι)
    (hP2 : ¬ IsConj z (z * ι τ₀)) {w : G} (hw : w ∈ Egrp z ι) (hc : IsConj z w) :
    w = z ∨ w = ι τ₀ := by
  obtain ⟨i, j, rfl⟩ := (mem_Egrp_iff hC).1 hw
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_mul, mul_one] at hc
  · exact absurd (isConj_one_left.mp hc) (centData_ne_one hC)
  · right
    simp
  · left
    simp
  · exact absurd hc hP2

private theorem g_not_mem_Egrp (hC : CentData z ι) (hg : GElt z ι g) :
    g ∉ Egrp z ι := by
  intro hgE
  have hcE : Egrp z ι ≤ centralizer ({z} : Set G) := by
    apply sup_le
    · exact Subgroup.zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl)
    · exact Subgroup.zpowers_le.2 (mem_centralizer_singleton_iff.2 (hC.comm τ₀).symm)
  have hgz : g * z = z * g := mem_centralizer_singleton_iff.1 (hcE hgE)
  have hxz : ι τ₀ = z := by
    rw [← hg.conj_z]
    calc g * z * g⁻¹ = z * g * g⁻¹ := by rw [hgz]
      _ = z := by group
  exact hC.ne_z τ₀ hxz

private theorem isConj_g_of_isConj_z_mul (hC : CentData z ι) (hg : GElt z ι g)
    (hg1 : g * g = 1) {e : G} (he : e ∈ Egrp z ι) (hc : IsConj z (g * e)) :
    IsConj z g := by
  obtain ⟨i, j, rfl⟩ := (mem_Egrp_iff hC).1 he
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_mul, mul_one] at hc
  · simpa using hc
  · exfalso
    have h2 : (g * ι τ₀) * (g * ι τ₀) = 1 := mul_self_of_isConj hC hc
    have hcomp : (g * ι τ₀) * (g * ι τ₀) = z * ι τ₀ := by
      calc (g * ι τ₀) * (g * ι τ₀) = (g * ι τ₀ * g⁻¹) * (g * g) * ι τ₀ := by group
        _ = z * (g * g) * ι τ₀ := by rw [hg.conj_x₁]
        _ = z * ι τ₀ := by rw [hg1, mul_one]
    rw [hcomp] at h2
    exact x₂_ne_one hC h2
  · exfalso
    have h2 : (g * z) * (g * z) = 1 := mul_self_of_isConj hC hc
    have hcomp : (g * z) * (g * z) = z * ι τ₀ := by
      calc (g * z) * (g * z) = (g * z * g⁻¹) * (g * g) * z := by group
        _ = ι τ₀ * (g * g) * z := by rw [hg.conj_z]
        _ = z * ι τ₀ := by rw [hg1, mul_one, ← hC.comm τ₀]
    rw [hcomp] at h2
    exact x₂_ne_one hC h2
  · have heq : g * (z * ι τ₀) = z * g * z := by
      calc g * (z * ι τ₀) = (z * ι τ₀) * g := hg.comm_x₂ hC
        _ = z * (ι τ₀ * g) := by group
        _ = z * ((g * z * g⁻¹) * g) := by rw [← hg.conj_z]
        _ = z * g * z := by group
    have hziz : z⁻¹ = z := inv_eq_of_mul_eq_one_right hC.mul_self
    have hgj : IsConj g (z * g * z) := isConj_iff.2 ⟨z, by rw [hziz]⟩
    exact (heq ▸ hc).trans hgj.symm

theorem mem_Dgrp_iff (hC : CentData z ι) (hg : GElt z ι g) {c : G} :
    c ∈ Dgrp z g ↔ ∃ e ∈ Egrp z ι, c = e ∨ c = g * e := by
  let P : G → Prop := fun c => ∃ e ∈ Egrp z ι, c = e ∨ c = g * e
  have hgN : ∀ h : G, h ∈ Egrp z ι ↔ g * h * g⁻¹ ∈ Egrp z ι :=
    Subgroup.mem_normalizer_iff.1 (GElt.mem_normalizer_Egrp hC hg)
  have hgNi : ∀ h : G, h ∈ Egrp z ι ↔ g⁻¹ * h * g ∈ Egrp z ι :=
    Subgroup.mem_normalizer_iff''.1 (GElt.mem_normalizer_Egrp hC hg)
  have hg2 : g * g ∈ Egrp z ι := by
    rcases hg.sq with h | h
    · rw [h]; exact (mem_Egrp_iff hC).2 ⟨0, 0, by simp⟩
    · rw [h]; exact (mem_Egrp_iff hC).2 ⟨1, 1, by simp⟩
  constructor
  · intro hc
    exact Subgroup.closure_induction (k := ({z, g} : Set G)) (x := c)
      (p := fun w _ => P w)
      (by
        intro y hy
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with hy | hy
        · rw [hy]
          exact ⟨z, (mem_Egrp_iff hC).2 ⟨1, 0, by simp⟩, Or.inl rfl⟩
        · rw [hy]
          exact ⟨1, (mem_Egrp_iff hC).2 ⟨0, 0, by simp⟩, Or.inr (by rw [mul_one])⟩)
      ⟨1, (mem_Egrp_iff hC).2 ⟨0, 0, by simp⟩, Or.inl rfl⟩
      (by
        intro x y hx hy ihx ihy
        rcases ihx with ⟨e1, he1, h1 | h1⟩ <;> rcases ihy with ⟨e2, he2, h2 | h2⟩
        · exact ⟨e1 * e2, mul_mem he1 he2, Or.inl (by rw [h1, h2])⟩
        · refine ⟨(g⁻¹ * e1 * g) * e2, mul_mem ((hgNi e1).1 he1) he2, Or.inr ?_⟩
          rw [h1, h2]; group
        · exact ⟨e1 * e2, mul_mem he1 he2, Or.inr (by rw [h1, h2]; group)⟩
        · refine ⟨(g * e1 * g⁻¹) * (g * g) * e2,
            mul_mem (mul_mem ((hgN e1).1 he1) hg2) he2, Or.inl ?_⟩
          rw [h1, h2]; group)
      (by
        intro x hx ihx
        rcases ihx with ⟨e1, he1, h1 | h1⟩
        · exact ⟨e1⁻¹, inv_mem he1, Or.inl (by rw [h1])⟩
        · refine ⟨(g⁻¹ * e1⁻¹ * g) * (g * g)⁻¹,
            mul_mem ((hgNi e1⁻¹).1 (inv_mem he1)) (inv_mem hg2), Or.inr ?_⟩
          rw [h1]; group)
      hc
  · rintro ⟨e, he, h | h⟩
    · rw [h]; exact Egrp_le_Dgrp hC hg he
    · rw [h]
      exact (Dgrp z g).mul_mem (Subgroup.subset_closure (by simp)) (Egrp_le_Dgrp hC hg he)

theorem card_Dgrp (hC : CentData z ι) (hg : GElt z ι g) : Nat.card (Dgrp z g) = 8 := by
  haveI : Finite (Egrp z ι) :=
    (Nat.card_pos_iff.1 (by rw [card_Egrp hC]; norm_num)).2
  let f : Egrp z ι ⊕ Egrp z ι → Dgrp z g := fun s =>
    match s with
    | Sum.inl e => ⟨(e : G), (mem_Dgrp_iff hC hg).2 ⟨(e : G), e.2, Or.inl rfl⟩⟩
    | Sum.inr e => ⟨g * (e : G), (mem_Dgrp_iff hC hg).2 ⟨(e : G), e.2, Or.inr rfl⟩⟩
  have hinj : Function.Injective f := by
    intro a b hab
    match a, b with
    | Sum.inl e1, Sum.inl e2 =>
        have h : (e1 : G) = e2 := congrArg (fun d : Dgrp z g => (d : G)) hab
        exact congrArg Sum.inl (Subtype.ext h)
    | Sum.inl e1, Sum.inr e2 =>
        exfalso
        have h : (e1 : G) = g * e2 := congrArg (fun d : Dgrp z g => (d : G)) hab
        apply g_not_mem_Egrp hC hg
        have hgE : g = (e1 : G) * (e2 : G)⁻¹ := by rw [h]; group
        rw [hgE]
        exact (Egrp z ι).mul_mem e1.2 ((Egrp z ι).inv_mem e2.2)
    | Sum.inr e1, Sum.inl e2 =>
        exfalso
        have h : g * e1 = (e2 : G) := congrArg (fun d : Dgrp z g => (d : G)) hab
        apply g_not_mem_Egrp hC hg
        have hgE : g = (e2 : G) * (e1 : G)⁻¹ := by rw [← h]; group
        rw [hgE]
        exact (Egrp z ι).mul_mem e2.2 ((Egrp z ι).inv_mem e1.2)
    | Sum.inr e1, Sum.inr e2 =>
        have h : g * e1 = g * e2 := congrArg (fun d : Dgrp z g => (d : G)) hab
        have h' : (e1 : G) = e2 := mul_left_cancel h
        exact congrArg Sum.inr (Subtype.ext h')
  have hsurj : Function.Surjective f := by
    intro d
    obtain ⟨e, he, h | h⟩ := (mem_Dgrp_iff hC hg).1 d.2
    · exact ⟨Sum.inl ⟨e, he⟩, Subtype.ext h.symm⟩
    · exact ⟨Sum.inr ⟨e, he⟩, Subtype.ext h.symm⟩
  have hcard : Nat.card (Dgrp z g) = Nat.card (Egrp z ι ⊕ Egrp z ι) :=
    Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩).symm
  simp [hcard, Nat.card_sum, card_Egrp hC]

theorem isPGroup_Dgrp (hC : CentData z ι) (hg : GElt z ι g) : IsPGroup 2 (Dgrp z g) :=
  IsPGroup.of_card (n := 3) (by rw [card_Dgrp hC hg]; norm_num)

theorem Dgrp_le_Yhat (hC : CentData z ι) (hg : GElt z ι g) :
    Dgrp z g ≤ centralizer (Agrp ι : Set G) ⊓ centralizer ({z * ι τ₀} : Set G) := by
  apply (Subgroup.closure_le (centralizer (Agrp ι : Set G) ⊓
    centralizer ({z * ι τ₀} : Set G))).2
  intro x hx
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with hx | hx
  · rw [hx]
    exact ⟨Egrp_le_centralizer_Agrp hC (Subgroup.mem_sup_left (Subgroup.mem_zpowers z)),
      z_mem_centralizer_x₂ hC⟩
  · rw [hx]
    exact ⟨hg.mem_centralizer_Agrp, mem_centralizer_singleton_iff.2 (hg.comm_x₂ hC)⟩

theorem normalizer_Dgrp_inf_le (hC : CentData z ι) (hP2 : ¬ IsConj z (z * ι τ₀))
    (hg : GElt z ι g) (hg1 : g * g = 1) (hgz : ¬ IsConj z g) :
    normalizer ((Dgrp z g : Subgroup G) : Set G) ⊓ centralizer (Agrp ι : Set G) ≤ Dgrp z g := by
  intro c hc
  obtain ⟨hcN, hcA⟩ := hc
  have hzD : z ∈ Dgrp z g := Subgroup.subset_closure (by simp)
  have hczD : c * z * c⁻¹ ∈ Dgrp z g := (Subgroup.mem_normalizer_iff.1 hcN z).1 hzD
  have hconj : IsConj z (c * z * c⁻¹) := isConj_iff.2 ⟨c, rfl⟩
  obtain ⟨e, he, hcase | hcase⟩ := (mem_Dgrp_iff hC hg).1 hczD
  · rw [hcase] at hconj
    rcases eq_z_or_eq_x1_of_mem_Egrp_of_isConj hC hP2 he hconj with hez | hex1
    · rw [hez] at hcase
      have hcz : c * z = z * c := by
        calc c * z = (c * z * c⁻¹) * c := by group
          _ = z * c := by rw [hcase]
      have hcE : c ∈ Egrp z ι := by
        rw [← centralizer_Agrp_inf_centralizer_z hC]
        exact ⟨hcA, mem_centralizer_singleton_iff.2 hcz⟩
      exact Egrp_le_Dgrp hC hg hcE
    · rw [hex1] at hcase
      have hx1g : g⁻¹ * ι τ₀ * g = z := by
        rw [← hg.conj_z]; group
      have hcomm_gc : (g⁻¹ * c) * z = z * (g⁻¹ * c) := by
        have hconjz : (g⁻¹ * c) * z * (g⁻¹ * c)⁻¹ = z := by
          calc (g⁻¹ * c) * z * (g⁻¹ * c)⁻¹ = g⁻¹ * (c * z * c⁻¹) * g := by group
            _ = g⁻¹ * (ι τ₀) * g := by rw [hcase]
            _ = z := hx1g
        calc (g⁻¹ * c) * z = ((g⁻¹ * c) * z * (g⁻¹ * c)⁻¹) * (g⁻¹ * c) := by group
          _ = z * (g⁻¹ * c) := by rw [hconjz]
      have hginv : g⁻¹ * c ∈ Egrp z ι := by
        rw [← centralizer_Agrp_inf_centralizer_z hC]
        exact ⟨(centralizer (Agrp ι : Set G)).mul_mem
            ((centralizer (Agrp ι : Set G)).inv_mem hg.mem_centralizer_Agrp) hcA,
          mem_centralizer_singleton_iff.2 hcomm_gc⟩
      exact (mem_Dgrp_iff hC hg).2 ⟨g⁻¹ * c, hginv, Or.inr (by group)⟩
  · rw [hcase] at hconj
    exact absurd (isConj_g_of_isConj_z_mul hC hg hg1 he hconj) hgz

theorem Dgrp_eq_of_isPGroup [Finite G] (hC : CentData z ι) (hP2 : ¬ IsConj z (z * ι τ₀))
    (hg : GElt z ι g) (hg1 : g * g = 1) (hgz : ¬ IsConj z g) {P : Subgroup G} (hP : IsPGroup 2 P)
    (hPR : P ≤ centralizer (Agrp ι : Set G)) (hDP : Dgrp z g ≤ P) : P = Dgrp z g := by
  by_contra hne
  have hDne : (Dgrp z g).subgroupOf P ≠ ⊤ := by
    intro htop
    exact hne (le_antisymm (Subgroup.subgroupOf_eq_top.1 htop) hDP)
  haveI : Group.IsNilpotent ↥P := IsPGroup.isNilpotent hP
  have hnc : NormalizerCondition ↥P := normalizerCondition_of_isNilpotent
  have hlt : (Dgrp z g).subgroupOf P < normalizer ((Dgrp z g).subgroupOf P) :=
    hnc _ (lt_top_iff_ne_top.2 hDne)
  obtain ⟨-, x, hxN, hxD⟩ := SetLike.lt_iff_le_and_exists.1 hlt
  have hxNG : (x : G) ∈ normalizer ((Dgrp z g : Subgroup G) : Set G) := by
    have h2 : x ∈ (normalizer ((Dgrp z g : Subgroup G) : Set G)).subgroupOf P := by
      rw [Subgroup.subgroupOf_normalizer_eq hDP]
      exact hxN
    exact Subgroup.mem_subgroupOf.1 h2
  have hxPR : (x : G) ∈ centralizer (Agrp ι : Set G) := hPR x.2
  have hxnot : (x : G) ∉ Dgrp z g := fun hxd => hxD (Subgroup.mem_subgroupOf.2 hxd)
  exact hxnot (normalizer_Dgrp_inf_le hC hP2 hg hg1 hgz ⟨hxNG, hxPR⟩)

private theorem not_two_dvd_relIndex_of_le [Finite G] (hC : CentData z ι)
    (hP2 : ¬ IsConj z (z * ι τ₀)) (hg : GElt z ι g) (hg1 : g * g = 1)
    (hgz : ¬ IsConj z g) {K : Subgroup G} (hDK : Dgrp z g ≤ K)
    (hKR : K ≤ centralizer (Agrp ι : Set G)) : ¬ 2 ∣ (Dgrp z g).relIndex K := by
  have hD'pg : IsPGroup 2 ((Dgrp z g).subgroupOf K) := by
    rw [← Subgroup.comap_subtype]
    exact (isPGroup_Dgrp hC hg).comap_subtype
  obtain ⟨P, hD'P⟩ := IsPGroup.exists_le_sylow hD'pg
  have hPmap_pg : IsPGroup 2 (P.map K.subtype) := P.2.map K.subtype
  have hPmap_le : P.map K.subtype ≤ centralizer (Agrp ι : Set G) := by
    rintro _ ⟨p, -, rfl⟩
    exact hKR p.2
  have hDPmap : Dgrp z g ≤ P.map K.subtype := by
    intro d hd
    exact ⟨⟨d, hDK hd⟩, hD'P (Subgroup.mem_subgroupOf.2 hd), rfl⟩
  have heq : P.map K.subtype = Dgrp z g :=
    Dgrp_eq_of_isPGroup hC hP2 hg hg1 hgz hPmap_pg hPmap_le hDPmap
  have hD'eq : (Dgrp z g).subgroupOf K = (P : Subgroup ↥K) := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hDK]
    exact heq.symm
  haveI : (P : Subgroup ↥K).FiniteIndex := inferInstance
  have hndvd : ¬ 2 ∣ (P : Subgroup ↥K).index := P.not_dvd_index
  rw [← hD'eq] at hndvd
  exact hndvd

theorem not_two_dvd_relIndex_Dgrp_Yhat [Finite G] (hC : CentData z ι)
    (hP2 : ¬ IsConj z (z * ι τ₀)) (hg : GElt z ι g) (hg1 : g * g = 1) (hgz : ¬ IsConj z g) :
    ¬ 2 ∣ (Dgrp z g).relIndex
      (centralizer (Agrp ι : Set G) ⊓ centralizer ({z * ι τ₀} : Set G)) :=
  not_two_dvd_relIndex_of_le hC hP2 hg hg1 hgz (Dgrp_le_Yhat hC hg) inf_le_left

theorem card_le_eight_of_isPGroup [Finite G] (hC : CentData z ι)
    (hP2 : ¬ IsConj z (z * ι τ₀)) (hg : GElt z ι g) (hg1 : g * g = 1) (hgz : ¬ IsConj z g)
    {Q : Subgroup G} (hQ : IsPGroup 2 Q) (hQA : Q ≤ centralizer (Agrp ι : Set G))
    (hQx : Q ≤ centralizer ({z * ι τ₀} : Set G)) : Nat.card Q ≤ 8 := by
  let Y : Subgroup G :=
    centralizer (Agrp ι : Set G) ⊓ centralizer ({z * ι τ₀} : Set G)
  have hDY : Dgrp z g ≤ Y := Dgrp_le_Yhat hC hg
  have hQY : Q ≤ Y := le_inf hQA hQx
  have hcardQ : Nat.card (Q.subgroupOf Y) = Nat.card Q := by
    rw [← Subgroup.card_subtype Y (Q.subgroupOf Y), Subgroup.map_subgroupOf_eq_of_le hQY]
  have hdvd : Nat.card Q ∣ Nat.card Y := by
    rw [← hcardQ]
    exact Subgroup.card_subgroup_dvd_card (Q.subgroupOf Y)
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hQ
  have hcardY : Nat.card Y = (Dgrp z g).relIndex Y * 8 := by
    rw [← Subgroup.relIndex_mul_card (H := Dgrp z g) (K := Y), inf_eq_left.2 hDY,
      card_Dgrp hC hg]
  have hodd : ¬ 2 ∣ (Dgrp z g).relIndex Y :=
    not_two_dvd_relIndex_Dgrp_Yhat hC hP2 hg hg1 hgz
  have hcop : Nat.Coprime 2 ((Dgrp z g).relIndex Y) :=
    Nat.prime_two.coprime_iff_not_dvd.2 hodd
  have hdvd8 : 2 ^ n ∣ 8 := by
    have h2 : 2 ^ n ∣ Nat.card Y := by rw [← hn]; exact hdvd
    rw [hcardY] at h2
    have hcop' : Nat.Coprime (2 ^ n) ((Dgrp z g).relIndex Y) := by
      cases n with
      | zero => simp
      | succ n => rw [Nat.coprime_pow_left_iff (Nat.succ_pos n)]; exact hcop
    exact (hcop'.dvd_mul_left).1 h2
  rw [hn]
  exact Nat.le_of_dvd (by norm_num) hdvd8

end CFSG.OddStandard.AltStdSec.SwapPartner
