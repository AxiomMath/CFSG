module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FCent
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec79BA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4S47Act

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B : Subgroup G}
  {φ : (Fin 7 → ZMod 2) → G}

private theorem sec4F_normalizer_le_normalizer_centralizer (X : Subgroup G) :
    normalizer (X : Set G) ≤ normalizer (centralizer (X : Set G) : Set G) := by
  intro x hx
  have hx' : ∀ y, y ∈ X ↔ x * y * x⁻¹ ∈ X := Subgroup.mem_normalizer_iff.mp hx
  have hx'' : ∀ y, y ∈ X → x⁻¹ * y * x ∈ X := by
    intro y hy
    rw [hx']
    simpa [mul_assoc] using hy
  rw [Subgroup.mem_normalizer_iff]
  intro c
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hc y hy
    have h1 := hc (x⁻¹ * y * x) (hx'' y hy)
    calc y * (x * c * x⁻¹) = x * ((x⁻¹ * y * x) * c) * x⁻¹ := by group
      _ = x * (c * (x⁻¹ * y * x)) * x⁻¹ := by rw [h1]
      _ = x * c * x⁻¹ * y := by group
  · intro hc y hy
    have h1 := hc (x * y * x⁻¹) ((hx' y).mp hy)
    have h2 : (x * y * x⁻¹) * (x * c * x⁻¹) = x * (y * c) * x⁻¹ := by group
    have h3 : (x * c * x⁻¹) * (x * y * x⁻¹) = x * (c * y) * x⁻¹ := by group
    rw [h2, h3] at h1
    have h4 := congrArg (fun z => x⁻¹ * z * x) h1
    simpa [mul_assoc] using h4

private theorem Sec4FSetup.A_le_centralizer (h : Sec4FSetup t L S z A B φ) :
    A ≤ centralizer (A : Set G) := by
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact h.A_comm hb ha

theorem Sec4FSetup.isSylow2Of_cent (h : Sec4FSetup t L S z A B φ) :
    IsSylow2Of A (centralizer (A : Set G)) := by
  have hAC : A ≤ centralizer (A : Set G) := h.A_le_centralizer
  have hA2 : IsPGroup 2 A := by
    intro a
    refine ⟨1, ?_⟩
    rw [show (2 : ℕ) ^ 1 = 2 by norm_num, pow_two]
    exact Subtype.ext (h.A_sq a.2)
  refine ⟨hAC, hA2, ?_⟩
  have hA2sub : IsPGroup 2 (A.subgroupOf (centralizer (A : Set G))) :=
    hA2.of_equiv (Subgroup.subgroupOfEquivOfLe hAC).symm
  obtain ⟨P, hAP⟩ := IsPGroup.exists_le_sylow hA2sub
  have hQsyl : IsSylow2Of ((P : Subgroup ↥(centralizer (A : Set G))).map
      (centralizer (A : Set G)).subtype) (centralizer (A : Set G)) :=
    isSylow2Of_map_sylow P
  have hAQ : A ≤ (P : Subgroup ↥(centralizer (A : Set G))).map
      (centralizer (A : Set G)).subtype := by
    intro a ha
    have hx : (⟨a, hAC ha⟩ : ↥(centralizer (A : Set G))) ∈
        A.subgroupOf (centralizer (A : Set G)) :=
      (Subgroup.mem_subgroupOf (H := A) (K := centralizer (A : Set G))
        (h := ⟨a, hAC ha⟩)).mpr ha
    exact Subgroup.mem_map_of_mem (centralizer (A : Set G)).subtype (hAP hx)
  have hQA : (P : Subgroup ↥(centralizer (A : Set G))).map
      (centralizer (A : Set G)).subtype ≤ A := by
    intro q hq
    have hqC : q ∈ centralizer (A : Set G) := hQsyl.1 hq
    obtain ⟨n, hn⟩ := hQsyl.2.1 ⟨q, hq⟩
    exact h.cent_two_elt hqC ⟨n, by simpa using congrArg Subtype.val hn⟩
  have hQAeq : (P : Subgroup ↥(centralizer (A : Set G))).map
      (centralizer (A : Set G)).subtype = A := le_antisymm hQA hAQ
  have hindex : A.relIndex (centralizer (A : Set G)) =
      ((P : Subgroup ↥(centralizer (A : Set G))).map
        (centralizer (A : Set G)).subtype).relIndex (centralizer (A : Set G)) := by
    rw [hQAeq]
  rw [hindex]
  exact hQsyl.2.2

theorem Sec4FSetup.sup_oddCore (h : Sec4FSetup t L S z A B φ) :
    A ⊔ oddCoreIn (centralizer (A : Set G)) = centralizer (A : Set G) := by
  refine sup_oddCoreIn_of_central_sylow h.isSylow2Of_cent ?_
  intro k hk a ha
  exact Subgroup.mem_centralizer_iff.mp hk a ha

theorem Sec4FSetup.conj_mem_oddCore (h : Sec4FSetup t L S z A B φ) {m o : G}
    (hm : m ∈ normalizer (A : Set G)) (ho : o ∈ oddCoreIn (centralizer (A : Set G))) :
    m * o * m⁻¹ ∈ oddCoreIn (centralizer (A : Set G)) :=
  conj_mem_oddCoreIn (sec4F_normalizer_le_normalizer_centralizer A hm) ho

theorem Sec4FSetup.BO_le_cent (h : Sec4FSetup t L S z A B φ) :
    B ⊔ oddCoreIn (centralizer (A : Set G)) ≤ centralizer (A : Set G) :=
  sup_le (h.B_le_A.trans h.A_le_centralizer) (oddCoreIn_normal (centralizer (A : Set G))).1

theorem Sec4FSetup.cent_cases (h : Sec4FSetup t L S z A B φ) {c : G}
    (hc : c ∈ centralizer (A : Set G)) :
    c ∈ B ⊔ oddCoreIn (centralizer (A : Set G)) ∨
      c * t ∈ B ⊔ oddCoreIn (centralizer (A : Set G)) := by
  have hcO : c ∈ A ⊔ oddCoreIn (centralizer (A : Set G)) := by
    rw [h.sup_oddCore]
    exact hc
  have hcomm : ∀ a ∈ A, ∀ o ∈ oddCoreIn (centralizer (A : Set G)), a * o = o * a :=
    fun a ha o ho =>
      Subgroup.mem_centralizer_iff.mp ((oddCoreIn_normal (centralizer (A : Set G))).1 ho) a ha
  obtain ⟨a, ha, o, ho, hco⟩ := sec4F_mem_sup_comm hcomm hcO
  have hot : t * o = o * t :=
    Subgroup.mem_centralizer_iff.mp ((oddCoreIn_normal (centralizer (A : Set G))).1 ho)
      t h.t_mem_A
  obtain ⟨b, hb, hba⟩ := h.mem_A_cases ha
  rcases hba with rfl | rfl
  · left
    rw [hco]
    exact Subgroup.mul_mem_sup hb ho
  · right
    rw [hco]
    have heq : (b * t) * o * t = b * o := by
      calc (b * t) * o * t = b * (t * o) * t := by group
        _ = b * (o * t) * t := by rw [hot]
        _ = b * o * (t * t) := by group
        _ = b * o := by rw [h.t_sq, mul_one]
    rw [heq]
    exact Subgroup.mul_mem_sup hb ho

theorem Sec4FSetup.t_not_mem_BO (h : Sec4FSetup t L S z A B φ) :
    t ∉ B ⊔ oddCoreIn (centralizer (A : Set G)) := by
  intro ht
  have hcomm : ∀ a ∈ B, ∀ o ∈ oddCoreIn (centralizer (A : Set G)), a * o = o * a :=
    fun a ha o ho =>
      Subgroup.mem_centralizer_iff.mp ((oddCoreIn_normal (centralizer (A : Set G))).1 ho) a
        (h.B_le_A ha)
  obtain ⟨b, hb, o, ho, hbo⟩ := sec4F_mem_sup_comm hcomm ht
  have hoA : o ∈ A := by
    have h1 : o = b⁻¹ * t := by rw [hbo]; group
    rw [h1]
    exact A.mul_mem (A.inv_mem (h.B_le_A hb)) h.t_mem_A
  have ho2 : o * o = 1 := h.A_sq hoA
  have hodd : Odd (orderOf o) := odd_orderOf_of_mem_oddCoreIn ho
  have hdvd : orderOf o ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one, pow_two]
    exact ho2
  have h1 : orderOf o = 1 :=
    Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.mpr hodd) hdvd dvd_rfl
  have ho1 : o = 1 := orderOf_eq_one_iff.mp h1
  have htb : t = b := by rw [hbo, ho1, mul_one]
  have htL : t ∈ L := by
    rw [htb]
    exact h.B_le_L hb
  exact sec4_t_not_mem h.ctx.toSec4Setting htL

theorem Sec4FSetup.conj_mem_BO (h : Sec4FSetup t L S z A B φ) {m x : G}
    (hm : m ∈ normalizer (A : Set G)) (hx : x ∈ B ⊔ oddCoreIn (centralizer (A : Set G))) :
    m * x * m⁻¹ ∈ B ⊔ oddCoreIn (centralizer (A : Set G)) := by
  have hcomm : ∀ a ∈ B, ∀ o ∈ oddCoreIn (centralizer (A : Set G)), a * o = o * a :=
    fun a ha o ho =>
      Subgroup.mem_centralizer_iff.mp ((oddCoreIn_normal (centralizer (A : Set G))).1 ho) a
        (h.B_le_A ha)
  obtain ⟨b, hb, o, ho, hbo⟩ := sec4F_mem_sup_comm hcomm hx
  have hmb : m * b * m⁻¹ ∈ B := h.conj_mem_B hm hb
  have hmo : m * o * m⁻¹ ∈ oddCoreIn (centralizer (A : Set G)) :=
    h.conj_mem_oddCore hm ho
  have heq : m * x * m⁻¹ = (m * b * m⁻¹) * (m * o * m⁻¹) := by
    rw [hbo]
    group
  rw [heq]
  exact Subgroup.mul_mem_sup hmb hmo

end CFSG.OddStandard.SmallF3.Omega
