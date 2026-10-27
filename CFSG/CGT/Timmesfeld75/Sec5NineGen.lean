module

public import CFSG.CGT.Timmesfeld75.O2Lift

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

variable {Y : Type*} [Group Y] {E : Subgroup Y}

theorem eq_one_of_conj_eq_mul_center (hE : IsWC E) (hEZ : E ⊓ Subgroup.center Y = ⊥)
    {e b z g : Y} (he : e ∈ E) (hb : b ∈ E) (hb1 : b ≠ 1) (hz : z ∈ Subgroup.center Y)
    (h : g * e * g⁻¹ = b * z) : z = 1 := by
  have hu : g * e * g⁻¹ ∈ conjSubgroup g E :=
    mem_conjSubgroup.2 (by simpa [mul_assoc] using he)
  have hle : conjSubgroup g E ≤ Subgroup.centralizer ({b} : Set Y) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hc : x * (b * z) = (b * z) * x := by
      rw [← h]
      exact elemAbelian_mul_comm (isElemAbelian_conjSubgroup hE.1 g) hx hu
    have hzx : x * z = z * x := Subgroup.mem_center_iff.1 hz x
    have hxb : x * b * z = b * x * z := by
      calc x * b * z = x * (b * z) := by rw [mul_assoc]
        _ = (b * z) * x := hc
        _ = b * (z * x) := by rw [mul_assoc]
        _ = b * (x * z) := by rw [hzx]
        _ = b * x * z := by rw [mul_assoc]
    exact mul_right_cancel hxb
  have hconj : conjSubgroup g E = E := (hE.2 b hb hb1).2 g hle
  have hbz : b * z ∈ E := by
    rw [← h]
    rw [hconj] at hu
    exact hu
  have hzE : z ∈ E := by
    have := E.mul_mem (E.inv_mem hb) hbz
    simpa using this
  have hz' : z ∈ E ⊓ Subgroup.center Y := ⟨hzE, hz⟩
  rw [hEZ, Subgroup.mem_bot] at hz'
  exact hz'

theorem inf_center_eq_bot_of_not_comm (hE : IsWC E)
    (hcl : Subgroup.normalClosure (E : Set Y) = ⊤) (hnc : ∃ a b : Y, a * b ≠ b * a) :
    E ⊓ Subgroup.center Y = ⊥ := by
  by_contra hne
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hzE : z ∈ E := hz.1
  have hzZ : z ∈ Subgroup.center Y := hz.2
  have hEn : ∀ g : Y, conjSubgroup g E = E := by
    intro g
    refine (hE.2 z hzE hz1').2 g fun x _ => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_center_iff.1 hzZ x
  have hnorm : E.Normal := ⟨fun n hn g => by
    have : g * n * g⁻¹ ∈ conjSubgroup g E :=
      mem_conjSubgroup.2 (by simpa [mul_assoc] using hn)
    rwa [hEn g] at this⟩
  have hle : Subgroup.normalClosure (E : Set Y) ≤ E :=
    Subgroup.normalClosure_le_normal fun x hx => hx
  rw [hcl] at hle
  obtain ⟨a, b, hab⟩ := hnc
  exact hab (elemAbelian_mul_comm hE.1 (hle (Subgroup.mem_top a)) (hle (Subgroup.mem_top b)))

theorem commutator_eq_top_of_wc (hE : IsWC E) (hEZ : E ⊓ Subgroup.center Y = ⊥)
    (hcl : Subgroup.normalClosure (E : Set Y) = ⊤) (h4 : 4 ≤ Nat.card E)
    (htr : ∀ a ∈ E, a ≠ 1 → ∀ b ∈ E, b ≠ 1 →
      ∃ g z : Y, z ∈ Subgroup.center Y ∧ g * a * g⁻¹ = b * z) :
    commutator Y = ⊤ := by
  by_contra hne
  obtain ⟨e₀, he₀, he₀D⟩ : ∃ e ∈ E, e ∉ commutator Y := by
    by_contra h
    push Not at h
    apply hne
    rw [eq_top_iff, ← hcl]
    exact Subgroup.normalClosure_le_normal h
  have he₀1 : e₀ ≠ 1 := fun h => he₀D (h ▸ (commutator Y).one_mem)
  have hall : ∀ b ∈ E, b ≠ 1 → b * e₀⁻¹ ∈ commutator Y := by
    intro b hb hb1
    obtain ⟨g, z, hz, hgz⟩ := htr e₀ he₀ he₀1 b hb hb1
    have hz1 : z = 1 := eq_one_of_conj_eq_mul_center hE hEZ he₀ hb hb1 hz hgz
    rw [hz1, mul_one] at hgz
    have : b * e₀⁻¹ = ⁅g, e₀⁆ := by
      rw [← hgz]
      simp only [commutatorElement_def]
    rw [this]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top e₀)
  obtain ⟨b₁, hb₁, b₂, hb₂, hb₁1, hb₂1, hb₁₂⟩ := exists_mul_ne_one_of_four_le_card hE.1 h4
  have hx₁ := hall b₁ hb₁ hb₁1
  have hx₂ := hall b₂ hb₂ hb₂1
  have hx₃ := hall (b₁ * b₂) (E.mul_mem hb₁ hb₂) hb₁₂
  apply he₀D
  have e : e₀ = (b₁ * e₀⁻¹)⁻¹ * ((b₁ * b₂) * e₀⁻¹) * (b₂ * e₀⁻¹)⁻¹ := by group
  rw [e]
  exact (commutator Y).mul_mem ((commutator Y).mul_mem ((commutator Y).inv_mem hx₁) hx₃)
    ((commutator Y).inv_mem hx₂)

theorem card_map_eq_of_inf_ker_eq_bot {K : Type*} [Group K] (f : Y →* K)
    (h : E ⊓ f.ker = ⊥) : Nat.card (E.map f) = Nat.card E := by
  refine (Nat.card_congr (Equiv.ofBijective
    (fun e : E => (⟨f e, Subgroup.mem_map_of_mem f e.2⟩ : E.map f)) ⟨?_, ?_⟩)).symm
  · intro a b hab
    have h1 : f a = f b := congrArg Subtype.val hab
    have h2 : (a : Y)⁻¹ * b ∈ E ⊓ f.ker :=
      ⟨E.mul_mem (E.inv_mem a.2) b.2, MonoidHom.mem_ker.2 (by
        rw [map_mul, map_inv, h1, inv_mul_cancel])⟩
    rw [h, Subgroup.mem_bot] at h2
    exact Subtype.ext (inv_mul_eq_one.1 h2)
  · rintro ⟨y, hy⟩
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hy
    exact ⟨⟨e, he⟩, rfl⟩

end CFSG.CGT.Timmesfeld75
