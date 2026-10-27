module

public import CFSG.GroupTheory.CommutingProductFixedSubgroup
public import Mathlib.Data.Finset.Erase
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Defs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open scoped commutatorElement

variable {Ω : Type*} [Group Ω]

theorem i224_conj_mem_centralizer {A : Subgroup Ω} {h z : Ω} (hh : h ∈ Subgroup.normalizer (A : Set Ω))
    (hz : z ∈ Subgroup.centralizer (A : Set Ω)) : h * z * h⁻¹ ∈ Subgroup.centralizer (A : Set Ω) := by
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  have h1 : h⁻¹ * t * h ∈ A := by
    have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (A : Set Ω)).inv_mem hh) t).1 ht
    simpa using this
  have h2 := Subgroup.mem_centralizer_iff.1 hz _ h1
  calc t * (h * z * h⁻¹) = h * ((h⁻¹ * t * h) * z) * h⁻¹ := by group
    _ = h * (z * (h⁻¹ * t * h)) * h⁻¹ := by rw [h2]
    _ = h * z * h⁻¹ * t := by group

theorem i224_comm_mem_centralizer_left {A : Subgroup Ω} {g h : Ω}
    (hg : g ∈ Subgroup.centralizer (A : Set Ω)) (hh : h ∈ Subgroup.normalizer (A : Set Ω)) :
    g * h * g⁻¹ * h⁻¹ ∈ Subgroup.centralizer (A : Set Ω) := by
  have := (Subgroup.centralizer (A : Set Ω)).mul_mem hg
    (i224_conj_mem_centralizer hh ((Subgroup.centralizer (A : Set Ω)).inv_mem hg))
  simpa [mul_assoc] using this

theorem i224_comm_mem_centralizer_right {A : Subgroup Ω} {g h : Ω}
    (hg : g ∈ Subgroup.normalizer (A : Set Ω)) (hh : h ∈ Subgroup.centralizer (A : Set Ω)) :
    g * h * g⁻¹ * h⁻¹ ∈ Subgroup.centralizer (A : Set Ω) :=
  (Subgroup.centralizer (A : Set Ω)).mul_mem (i224_conj_mem_centralizer hg hh)
    ((Subgroup.centralizer (A : Set Ω)).inv_mem hh)

@[expose] def i224Adm (H W Q : Subgroup Ω) : Subgroup Ω where
  carrier := {x | x ∈ H ∧ ∃ q ∈ W ⊓ Q, x⁻¹ * q ∈ Subgroup.centralizer (H : Set Ω)}
  mul_mem' := by
    rintro x y ⟨hxL, qx, hqx, hqxi⟩ ⟨hyL, qy, hqy, hqyi⟩
    refine ⟨H.mul_mem hxL hyL, qx * qy, (W ⊓ Q).mul_mem hqx hqy, ?_⟩
    have h2 := Subgroup.mem_centralizer_iff.1 hqxi y⁻¹ (H.inv_mem hyL)
    have : (x * y)⁻¹ * (qx * qy) = (x⁻¹ * qx) * (y⁻¹ * qy) := by
      calc (x * y)⁻¹ * (qx * qy) = y⁻¹ * (x⁻¹ * qx) * qy := by group
        _ = (x⁻¹ * qx) * y⁻¹ * qy := by rw [h2]
        _ = (x⁻¹ * qx) * (y⁻¹ * qy) := by group
    rw [this]
    exact (Subgroup.centralizer (H : Set Ω)).mul_mem hqxi hqyi
  one_mem' := ⟨H.one_mem, 1, (W ⊓ Q).one_mem, by simp⟩
  inv_mem' := by
    rintro x ⟨hxL, qx, hqx, hqxi⟩
    refine ⟨H.inv_mem hxL, qx⁻¹, (W ⊓ Q).inv_mem hqx, ?_⟩
    have hz := (Subgroup.centralizer (H : Set Ω)).inv_mem hqxi
    have h2 := Subgroup.mem_centralizer_iff.1 hz x hxL
    have : (x⁻¹)⁻¹ * qx⁻¹ = (x⁻¹ * qx)⁻¹ := by
      have e1 : (x⁻¹ * qx)⁻¹ = qx⁻¹ * x := by group
      rw [e1]
      rw [e1] at h2
      calc (x⁻¹)⁻¹ * qx⁻¹ = x * (qx⁻¹ * x) * x⁻¹ := by group
        _ = (qx⁻¹ * x) * x * x⁻¹ := by rw [h2]
        _ = qx⁻¹ * x := by group
    rw [this]
    exact hz

theorem mem_i224Adm {H W Q : Subgroup Ω} {x : Ω} :
    x ∈ i224Adm H W Q ↔ x ∈ H ∧ ∃ q ∈ W ⊓ Q, x⁻¹ * q ∈ Subgroup.centralizer (H : Set Ω) := Iff.rfl

theorem i224_iso {J : Type*} [Fintype J] [DecidableEq J] (L : J → Subgroup Ω)
    (hcomm : ∀ i c, i ≠ c → ∀ x ∈ L i, ∀ y ∈ L c, x * y = y * x)
    (hperf : ∀ i, ⁅L i, L i⁆ = L i) (W : Subgroup Ω) (hWM : W ≤ ⨆ i, L i)
    (hH0 : ∀ i, L i ≤ i224Adm (L i) W ⊤)
    (hH1 : ∀ i c, i ≠ c → L i ≤ i224Adm (L i) W (Subgroup.centralizer (L c : Set Ω))) :
    ∀ i, L i ≤ W := by
  classical
  have hnorm : ∀ c, (⨆ i, L i) ≤ Subgroup.normalizer (L c : Set Ω) := by
    intro c
    refine iSup_le fun d => ?_
    by_cases hdc : d = c
    · subst hdc
      exact Subgroup.le_normalizer
    · refine le_trans ?_ (Subgroup.centralizer_le_normalizer (L c : Set Ω))
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (hcomm d c hdc x hx y hy).symm
  have hcommutator : ∀ {H : Subgroup Ω} {U : Subgroup Ω}, ⁅H, H⁆ = H →
      (∀ x₁ ∈ H, ∀ x₂ ∈ H, ⁅x₁, x₂⁆ ∈ U) → H ≤ U := by
    intro H U hH hU
    rw [← hH, Subgroup.commutator_def, Subgroup.closure_le]
    rintro _ ⟨x₁, hx₁, x₂, hx₂, rfl⟩
    exact hU x₁ hx₁ x₂ hx₂
  intro i
  have hcc : ∀ a ∈ L i, ∀ b ∈ Subgroup.centralizer (L i : Set Ω), a * b = b * a :=
    fun a ha b hb => (Subgroup.mem_centralizer_iff.1 hb a ha)
  have hcomm_id : ∀ x₁ ∈ L i, ∀ x₂ ∈ L i, ∀ q₁ q₂ : Ω,
      x₁⁻¹ * q₁ ∈ Subgroup.centralizer (L i : Set Ω) →
      x₂⁻¹ * q₂ ∈ Subgroup.centralizer (L i : Set Ω) →
      ⁅q₁, q₂⁆ = ⁅x₁, x₂⁆ * ⁅x₁⁻¹ * q₁, x₂⁻¹ * q₂⁆ := by
    intro x₁ hx₁ x₂ hx₂ q₁ q₂ hq₁i hq₂i
    have h3 := CFSG.GroupTheory.commutatorElement_mul_of_commute
      (A := L i) (B := Subgroup.centralizer (L i : Set Ω)) hcc hx₁ hx₂ hq₁i hq₂i
    have hq₁' : q₁ = x₁ * (x₁⁻¹ * q₁) := by group
    have hq₂' : q₂ = x₂ * (x₂⁻¹ * q₂) := by group
    rw [← h3, ← hq₁', ← hq₂']
  have key : ∀ S : Finset J, i ∉ S →
      L i ≤ i224Adm (L i) W (⨅ d ∈ S, Subgroup.centralizer (L d : Set Ω)) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      simpa using hH0 i
    | insert c S hcS ih =>
      intro hiS
      have hic : i ≠ c := fun h => hiS (h ▸ Finset.mem_insert_self _ _)
      have hiS' : i ∉ S := fun h => hiS (Finset.mem_insert_of_mem h)
      refine hcommutator (hperf i) ?_
      intro x₁ hx₁ x₂ hx₂
      obtain ⟨-, q₁, hq₁, hq₁i⟩ := ih hiS' hx₁
      obtain ⟨-, q₂, hq₂, hq₂i⟩ := hH1 i c hic hx₂
      have hWq₁ : q₁ ∈ ⨆ i, L i := hWM hq₁.1
      have hWq₂ : q₂ ∈ ⨆ i, L i := hWM hq₂.1
      have hq₁C : ∀ d ∈ S, q₁ ∈ Subgroup.centralizer (L d : Set Ω) := fun d hd =>
        Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hq₁.2 d) hd
      refine ⟨?_, ⁅q₁, q₂⁆, ?_, ?_⟩
      · rw [commutatorElement_def]
        exact (L i).mul_mem ((L i).mul_mem ((L i).mul_mem hx₁ hx₂) ((L i).inv_mem hx₁))
          ((L i).inv_mem hx₂)
      · refine ⟨?_, ?_⟩
        · rw [commutatorElement_def]
          exact W.mul_mem (W.mul_mem (W.mul_mem hq₁.1 hq₂.1) (W.inv_mem hq₁.1)) (W.inv_mem hq₂.1)
        · refine Subgroup.mem_iInf.2 fun d => Subgroup.mem_iInf.2 fun hd => ?_
          rcases Finset.mem_insert.1 hd with rfl | hdS
          · exact i224_comm_mem_centralizer_right (hnorm d hWq₁) hq₂.2
          · exact i224_comm_mem_centralizer_left (hq₁C d hdS) (hnorm d hWq₂)
      · have h5 := hcomm_id x₁ hx₁ x₂ hx₂ q₁ q₂ hq₁i hq₂i
        rw [h5, inv_mul_cancel_left, commutatorElement_def]
        exact (Subgroup.centralizer (L i : Set Ω)).mul_mem
          ((Subgroup.centralizer (L i : Set Ω)).mul_mem
            ((Subgroup.centralizer (L i : Set Ω)).mul_mem hq₁i hq₂i)
            ((Subgroup.centralizer (L i : Set Ω)).inv_mem hq₁i))
          ((Subgroup.centralizer (L i : Set Ω)).inv_mem hq₂i)
  refine hcommutator (hperf i) ?_
  intro x₁ hx₁ x₂ hx₂
  have hiS : i ∉ Finset.univ.erase i := by simp
  obtain ⟨-, q₁, hq₁, hq₁i⟩ := key _ hiS hx₁
  obtain ⟨-, q₂, hq₂, hq₂i⟩ := key _ hiS hx₂
  have hqC : ∀ q ∈ (⨅ d ∈ Finset.univ.erase i, Subgroup.centralizer (L d : Set Ω)),
      ∀ d, d ≠ i → q ∈ Subgroup.centralizer (L d : Set Ω) := by
    intro q hq d hd
    exact Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hq d) (by simp [hd])
  have hr : ∀ (x q : Ω), x ∈ L i → (∀ d, d ≠ i → q ∈ Subgroup.centralizer (L d : Set Ω)) →
      x⁻¹ * q ∈ Subgroup.centralizer (L i : Set Ω) →
      ∀ d, ∀ t ∈ L d, t * (x⁻¹ * q) = (x⁻¹ * q) * t := by
    intro x q hx hqC hqi d t ht
    by_cases hd : d = i
    · subst hd
      exact Subgroup.mem_centralizer_iff.1 hqi t ht
    · have h1 := hcomm d i hd t ht x⁻¹ ((L i).inv_mem hx)
      have h2 := Subgroup.mem_centralizer_iff.1 (hqC d hd) t ht
      calc t * (x⁻¹ * q) = (t * x⁻¹) * q := by group
        _ = (x⁻¹ * t) * q := by rw [h1]
        _ = x⁻¹ * (t * q) := by group
        _ = x⁻¹ * (q * t) := by rw [h2]
        _ = (x⁻¹ * q) * t := by group
  have hr₁ := hr x₁ q₁ hx₁ (hqC q₁ hq₁.2) hq₁i
  have hr₂mem : x₂⁻¹ * q₂ ∈ ⨆ i, L i :=
    (⨆ i, L i).mul_mem ((⨆ i, L i).inv_mem (le_iSup L i hx₂)) (hWM hq₂.1)
  have hcr : ∀ d, L d ≤ Subgroup.centralizer ({x₁⁻¹ * q₁} : Set Ω) := by
    intro d t ht
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hr₁ d t ht
  have hr₂Z : x₂⁻¹ * q₂ ∈ Subgroup.centralizer ({x₁⁻¹ * q₁} : Set Ω) :=
    (iSup_le hcr) hr₂mem
  have hrr : ⁅x₁⁻¹ * q₁, x₂⁻¹ * q₂⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_commute]
    exact (Subgroup.mem_centralizer_singleton_iff.1 hr₂Z).symm
  have h4 : ⁅q₁, q₂⁆ = ⁅x₁, x₂⁆ := by
    rw [hcomm_id x₁ hx₁ x₂ hx₂ q₁ q₂ hq₁i hq₂i, hrr, mul_one]
  rw [← h4, commutatorElement_def]
  exact W.mul_mem (W.mul_mem (W.mul_mem hq₁.1 hq₂.1) (W.inv_mem hq₁.1)) (W.inv_mem hq₂.1)

end CFSG.HardMathSupport.Solomon.Coordinator
