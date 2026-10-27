module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.SetTheory.Cardinal.Finite
import CFSG.FeitThompson.Foundations.SolvableHallConjugacy
import CFSG.FeitThompson.Foundations.ProductSubgroupsCardinality

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Pointwise Subgroup

variable {X : Type*} [Group X]

private theorem mem_conj_smul_iff' {g x : X} {U : Subgroup X} :
    x ∈ (MulAut.conj g • U : Subgroup X) ↔ g⁻¹ * x * g ∈ U := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp [MulAut.smul_def, mul_assoc]

theorem le_normalizer_inf_of_normal (D J : Subgroup X) [D.Normal] :
    J ≤ normalizer ((D ⊓ J : Subgroup X) : Set X) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => Subgroup.mem_inf.2 ⟨‹D.Normal›.conj_mem h (Subgroup.mem_inf.1 hh).1 g,
    J.mul_mem (J.mul_mem hg (Subgroup.mem_inf.1 hh).2) (J.inv_mem hg)⟩, fun hh => ?_⟩
  obtain ⟨hhD, hhJ⟩ := Subgroup.mem_inf.1 hh
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · have h1 : h = g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ := by group
    rw [h1]
    exact ‹D.Normal›.conj_mem _ hhD g⁻¹
  · have h1 : h = g⁻¹ * (g * h * g⁻¹) * g := by group
    rw [h1]
    exact J.mul_mem (J.mul_mem (J.inv_mem hg) hhJ) hg

theorem inf_sup_eq_of_normal_of_le (D : Subgroup X) [D.Normal] {J U : Subgroup X} (hUJ : U ≤ J) :
    J ⊓ (D ⊔ U) = D ⊓ J ⊔ U := by
  refine le_antisymm ?_ (le_inf (sup_le inf_le_right hUJ) (sup_le_sup_right inf_le_left U))
  intro x hx
  obtain ⟨hxJ, hxDU⟩ := Subgroup.mem_inf.1 hx
  rw [← SetLike.mem_coe, Subgroup.normal_mul D U] at hxDU
  obtain ⟨d, hd, u, hu, rfl⟩ := hxDU
  have hdJ : d ∈ J := by
    have h : d * u * u⁻¹ ∈ J := J.mul_mem hxJ (J.inv_mem (hUJ hu))
    simpa using h
  exact Subgroup.mul_mem_sup (Subgroup.mem_inf.2 ⟨hd, hdJ⟩) hu

theorem mem_centralizer_of_mem_normalizer_of_mem_normal {D U : Subgroup X} [hD : D.Normal]
    (hDU : D ⊓ U = ⊥) {x : X} (hxD : x ∈ D) (hxN : x ∈ normalizer (U : Set X)) :
    x ∈ centralizer (U : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hu' : x⁻¹ * u * x ∈ U := (Subgroup.mem_normalizer_iff''.1 hxN u).1 hu
  have hzU : u⁻¹ * (x⁻¹ * u * x) ∈ U := U.mul_mem (U.inv_mem hu) hu'
  have hzD : u⁻¹ * (x⁻¹ * u * x) ∈ D := by
    have h1 : u⁻¹ * x⁻¹ * u⁻¹⁻¹ ∈ D := hD.conj_mem x⁻¹ (D.inv_mem hxD) u⁻¹
    have h2 : u⁻¹ * (x⁻¹ * u * x) = u⁻¹ * x⁻¹ * u⁻¹⁻¹ * x := by group
    rw [h2]
    exact D.mul_mem h1 hxD
  have hone : u⁻¹ * (x⁻¹ * u * x) = 1 := by
    have h := hDU ▸ Subgroup.mem_inf.2 ⟨hzD, hzU⟩
    simpa using h
  have h2 : x⁻¹ * u * x = u := (inv_mul_eq_one.1 hone).symm
  calc u * x = x * (x⁻¹ * u * x) := by group
    _ = x * u := by rw [h2]

private theorem exists_mem_conj_smul_eq_of_coprime [Finite X] [Group.IsSolvable X]
    {V U W : Subgroup X} {m : ℕ} (hUV : U ≤ V) (hWV : W ≤ V)
    (hU : Nat.card ↥V = Nat.card U * m) (hW : Nat.card ↥V = Nat.card W * m)
    (hcop : Nat.Coprime (Nat.card U) m) :
    ∃ t ∈ V, MulAut.conj t • W = U := by
  set π : Set ℕ := ((Nat.card U).primeFactors : Set ℕ) with hπ
  have hm : m ≠ 0 := by
    rintro rfl
    simp only [mul_zero] at hU
    exact Nat.card_pos.ne' hU
  have hUW : Nat.card U = Nat.card W :=
    Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hm) (hU.symm.trans hW)
  have hcardU : Nat.card (U.subgroupOf V) = Nat.card U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUV).toEquiv
  have hcardW : Nat.card (W.subgroupOf V) = Nat.card W :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWV).toEquiv
  have hidxU : (U.subgroupOf V).index = m := by
    have h := Subgroup.card_mul_index (U.subgroupOf V)
    rw [hcardU, hU] at h
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h
  have hidxW : (W.subgroupOf V).index = m := by
    have h := Subgroup.card_mul_index (W.subgroupOf V)
    rw [hcardW, hW] at h
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h
  have hpiU : IsPiNumber π (Nat.card U) := isPiNumber_iff.2 fun p hp => by simpa [hπ] using hp
  have hpim : IsPiNumber πᶜ m := isPiNumber_compl_iff.2 fun p hp => by
    simp only [hπ, Finset.mem_coe]
    exact fun hp' => Finset.disjoint_left.1 hcop.disjoint_primeFactors hp' hp
  have hU' : IsHallSubgroup π (U.subgroupOf V) :=
    ⟨by rw [hcardU]; exact hpiU, by rw [hidxU]; exact hpim⟩
  have hW' : IsHallSubgroup π (W.subgroupOf V) :=
    ⟨by rw [hcardW, ← hUW]; exact hpiU, by rw [hidxW]; exact hpim⟩
  obtain ⟨g, hg⟩ := exists_forall_mem_iff_conj_mem_of_isHallSubgroup hW' hU'
  refine ⟨(g : X), g.2, ?_⟩
  ext x
  rw [mem_conj_smul_iff']
  constructor
  · intro hx
    have hxV : x ∈ V := by
      have h : (g : X) * ((g : X)⁻¹ * x * (g : X)) * (g : X)⁻¹ ∈ V :=
        V.mul_mem (V.mul_mem g.2 (hWV hx)) (V.inv_mem g.2)
      simpa [mul_assoc] using h
    have := (hg ⟨x, hxV⟩).2 (by simpa [Subgroup.mem_subgroupOf] using hx)
    simpa [Subgroup.mem_subgroupOf] using this
  · intro hx
    have := (hg ⟨x, hUV hx⟩).1 (by simpa [Subgroup.mem_subgroupOf] using hx)
    simpa [Subgroup.mem_subgroupOf] using this

variable [Finite X] [Group.IsSolvable X] {D J U : Subgroup X}

theorem exists_mem_mul_eq_of_mem_normalizer [D.Normal] (hDJ : D ⊔ J = ⊤) (hUJ : U ≤ J)
    (hcop : Nat.Coprime (Nat.card D) (Nat.card U)) {n : X} (hn : n ∈ normalizer (U : Set X)) :
    ∃ e ∈ D ⊓ centralizer (U : Set X), ∃ y ∈ J ⊓ normalizer (U : Set X), n = e * y := by
  set E : Subgroup X := D ⊓ J with hE
  have hUnormE : U ≤ normalizer (E : Set X) := hUJ.trans (le_normalizer_inf_of_normal D J)
  have hcopUE : Nat.Coprime (Nat.card U) (Nat.card E) :=
    hcop.symm.coprime_dvd_right (Subgroup.card_dvd_of_le (hE ▸ inf_le_left))
  have hEU : U ⊓ E = ⊥ := disjoint_iff.1 (Subgroup.disjoint_of_coprime_natCard hcopUE)
  have hDUbot : D ⊓ U = ⊥ := disjoint_iff.1 (Subgroup.disjoint_of_coprime_natCard hcop)
  set V : Subgroup X := U ⊔ E with hV
  have hcoeV : ((V : Subgroup X) : Set X) = (U : Set X) * (E : Set X) :=
    hV ▸ Subgroup.coe_mul_of_left_le_normalizer_right U E hUnormE
  have hcardV : Nat.card ↥V = Nat.card U * Nat.card E := by
    have h := natCard_mul_mul_natCard_inf U E
    rw [hEU] at h
    simp only [Subgroup.card_bot, mul_one] at h
    rw [← h, ← hcoeV]
    rfl
  have hnDJ : n ∈ (D : Set X) * (J : Set X) := by
    rw [← Subgroup.normal_mul D J, hDJ]; simp
  obtain ⟨d, hdD, j, hjJ, rfl⟩ := hnDJ
  set W : Subgroup X := MulAut.conj d⁻¹ • U with hW
  have hmemW : ∀ x : X, x ∈ W ↔ d * x * d⁻¹ ∈ U := fun x => by
    rw [hW, mem_conj_smul_iff']; simp
  have hWJ : W ≤ J := by
    intro x hx
    have h1 : (d * j)⁻¹ * (d * x * d⁻¹) * (d * j) ∈ U :=
      (Subgroup.mem_normalizer_iff''.1 hn _).1 ((hmemW x).1 hx)
    have h2 : (d * j)⁻¹ * (d * x * d⁻¹) * (d * j) = j⁻¹ * x * j := by group
    rw [h2] at h1
    have h3 : j * (j⁻¹ * x * j) * j⁻¹ ∈ J := J.mul_mem (J.mul_mem hjJ (hUJ h1)) (J.inv_mem hjJ)
    simpa [mul_assoc] using h3
  have hWDU : W ≤ D ⊔ U := by
    intro x hx
    have hxU : d * x * d⁻¹ ∈ U := (hmemW x).1 hx
    have hdxd : d⁻¹ * (d * x * d⁻¹ * d * (d * x * d⁻¹)⁻¹) ∈ D :=
      D.mul_mem (D.inv_mem hdD) (‹D.Normal›.conj_mem d hdD _)
    have hxeq : x = d⁻¹ * (d * x * d⁻¹ * d * (d * x * d⁻¹)⁻¹) * (d * x * d⁻¹) := by group
    rw [hxeq]
    exact Subgroup.mul_mem_sup hdxd hxU
  have hWV : W ≤ V := by
    rw [hV, hE, sup_comm U (D ⊓ J), ← inf_sup_eq_of_normal_of_le D hUJ]
    exact le_inf hWJ hWDU
  have hcardW : Nat.card ↥V = Nat.card W * Nat.card E := by
    rw [hcardV, hW, natCard_conj_smul]
  obtain ⟨t, htV, hconj⟩ :=
    exists_mem_conj_smul_eq_of_coprime (hV ▸ le_sup_left) hWV hcardV hcardW hcopUE
  have hdt : d * t⁻¹ ∈ normalizer (U : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have s1 : h ∈ U ↔ t⁻¹ * h * t ∈ W := by rw [← hconj, mem_conj_smul_iff']
    have s2 : d * (t⁻¹ * h * t) * d⁻¹ = d * t⁻¹ * h * (d * t⁻¹)⁻¹ := by group
    rw [s1, hmemW _, s2]
  have hsEU : t⁻¹ ∈ (E : Set X) * (U : Set X) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left E U hUnormE, sup_comm E U, ← hV]
    exact V.inv_mem htV
  obtain ⟨c, hc, u₀, hu₀, hcu⟩ := hsEU
  obtain ⟨hcD, hcJ⟩ := Subgroup.mem_inf.1 (hE ▸ hc)
  have hdcN : d * c ∈ normalizer (U : Set X) := by
    have h1 : d * c = d * t⁻¹ * u₀⁻¹ := by rw [← hcu]; group
    rw [h1]
    exact (normalizer (U : Set X)).mul_mem hdt
      ((normalizer (U : Set X)).inv_mem (Subgroup.le_normalizer hu₀))
  refine ⟨d * c, Subgroup.mem_inf.2 ⟨D.mul_mem hdD hcD,
      mem_centralizer_of_mem_normalizer_of_mem_normal hDUbot (D.mul_mem hdD hcD) hdcN⟩,
    c⁻¹ * j, Subgroup.mem_inf.2 ⟨J.mul_mem (J.inv_mem hcJ) hjJ, ?_⟩, by group⟩
  have h2 : c⁻¹ * j = (d * c)⁻¹ * (d * j) := by group
  rw [h2]
  exact (normalizer (U : Set X)).mul_mem ((normalizer (U : Set X)).inv_mem hdcN) hn

theorem coe_normalizer_eq_inf_centralizer_mul_inf_normalizer [D.Normal] (hDJ : D ⊔ J = ⊤)
    (hUJ : U ≤ J) (hcop : Nat.Coprime (Nat.card D) (Nat.card U)) :
    (normalizer (U : Set X) : Set X)
      = ((D ⊓ centralizer (U : Set X) : Subgroup X) : Set X)
        * ((J ⊓ normalizer (U : Set X) : Subgroup X) : Set X) := by
  apply Set.Subset.antisymm
  · intro n hn
    obtain ⟨e, he, y, hy, rfl⟩ := exists_mem_mul_eq_of_mem_normalizer hDJ hUJ hcop hn
    exact Set.mul_mem_mul he hy
  · rintro n ⟨e, he, y, hy, rfl⟩
    exact (normalizer (U : Set X)).mul_mem
      (Subgroup.centralizer_le_normalizer _ (Subgroup.mem_inf.1 he).2)
      (Subgroup.mem_inf.1 hy).2

theorem normalizer_eq_inf_centralizer_sup_inf_normalizer [D.Normal] (hDJ : D ⊔ J = ⊤)
    (hUJ : U ≤ J) (hcop : Nat.Coprime (Nat.card D) (Nat.card U)) :
    normalizer (U : Set X) = D ⊓ centralizer (U : Set X) ⊔ J ⊓ normalizer (U : Set X) := by
  refine le_antisymm (fun n hn => ?_) (sup_le
    (inf_le_right.trans (Subgroup.centralizer_le_normalizer _)) inf_le_right)
  obtain ⟨e, he, y, hy, rfl⟩ := exists_mem_mul_eq_of_mem_normalizer hDJ hUJ hcop hn
  exact Subgroup.mul_mem_sup he hy

end CFSG.FeitThompson

