module

public import CFSG.ClassicalInvolution.Asc77.AscE187P1c

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

omit [Finite G] in
theorem centralizer_conj_le {a h : G} (hH : h ∈ H) (haH : Subgroup.centralizer ({a} : Set G) ≤ H) :
    Subgroup.centralizer ({h⁻¹ * a * h} : Set G) ≤ H := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff] at hx
  have hmem : h * x * h⁻¹ ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc h * x * h⁻¹ * a = h * (x * (h⁻¹ * a * h)) * h⁻¹ := by group
      _ = h * ((h⁻¹ * a * h) * x) * h⁻¹ := by rw [hx]
      _ = a * (h * x * h⁻¹) := by group
  have := haH hmem
  have e : x = h⁻¹ * (h * x * h⁻¹) * h := by group
  rw [e]
  exact H.mul_mem (H.mul_mem (H.inv_mem hH) this) hH

theorem E187C.part1_of (hSH : (S : Subgroup G) ≤ H)
    (hcore : ∀ {a g t : G}, a * a = 1 → Subgroup.centralizer ({a} : Set G) ≤ H → g ∉ H →
      t = g * a * g⁻¹ → t ∈ (S : Subgroup G) →
      (∀ x ∈ (S : Subgroup G), t * x = x * t → x ∈ conjSub g (S : Subgroup G)) → False)
    {a g : G} (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (haH : Subgroup.centralizer ({a} : Set G) ≤ H) (hgt : g * a * g⁻¹ ∈ H) :
    ∃ h' ∈ H, h' * a * h'⁻¹ = g * a * g⁻¹ := by
  by_contra hno
  push Not at hno
  have hgH : g ∉ H := fun hg => hno g hg rfl
  have ha2' : orderOf (g * a * g⁻¹) = 2 := by
    rw [orderOf_conj_mul_inv_eq]
    exact orderOf_eq_two_of_sq ha1 ha2
  have hv : IsPGroup 2 (Subgroup.zpowers (g * a * g⁻¹)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha2']; norm_num)
  obtain ⟨h₁, hh₁H, hh₁⟩ := exists_conj_mem_of_sylow_le hSH hgt hv
  set g₁ := h₁⁻¹ * g with hg₁
  set t := h₁⁻¹ * (g * a * g⁻¹) * h₁ with ht
  have hat₁ : t = g₁ * a * g₁⁻¹ := by rw [ht, hg₁]; group
  have hg₁H : g₁ ∉ H := by
    intro hh
    apply hgH
    have : g = h₁ * g₁ := by rw [hg₁]; group
    rw [this]
    exact H.mul_mem hh₁H hh
  have hUp : IsPGroup 2 ↥((S : Subgroup G) ⊓ Subgroup.centralizer ({t} : Set G)) :=
    S.isPGroup'.to_le inf_le_left
  have hUH : (S : Subgroup G) ⊓ Subgroup.centralizer ({t} : Set G) ≤ conjSub g₁ H := by
    intro x hx
    have hxt := Subgroup.mem_centralizer_singleton_iff.mp hx.2
    rw [mem_conjSub_iff]
    apply haH
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e1 : g₁⁻¹ * (t * x) * g₁ = a * (g₁⁻¹ * x * g₁) := by rw [hat₁]; group
    have e2 : g₁⁻¹ * (x * t) * g₁ = (g₁⁻¹ * x * g₁) * a := by rw [hat₁]; group
    rw [← e2, ← e1, hxt]
  have hS₁H : ((conjSylow g₁ S : Sylow 2 G) : Subgroup G) ≤ conjSub g₁ H := by
    rw [coe_conjSylow]
    exact conjSub_mono hSH
  obtain ⟨h', hh'H, hUh'⟩ := exists_conj_sylow_ge hS₁H hUp hUH
  rw [coe_conjSylow] at hUh'
  obtain ⟨h₂, hh₂H, rfl⟩ : ∃ h₂ ∈ H, h' = g₁ * h₂ * g₁⁻¹ := by
    refine ⟨g₁⁻¹ * h' * g₁, ?_, by group⟩
    rwa [mem_conjSub_iff] at hh'H
  have hconj : conjSub (g₁ * h₂ * g₁⁻¹) (conjSub g₁ (S : Subgroup G)) =
      conjSub (g₁ * h₂) (S : Subgroup G) := by
    rw [← conjSub_mul]
    congr 1
    group
  rw [hconj] at hUh'
  have ha₂ : (h₂⁻¹ * a * h₂) * (h₂⁻¹ * a * h₂) = 1 := by
    calc (h₂⁻¹ * a * h₂) * (h₂⁻¹ * a * h₂) = h₂⁻¹ * (a * a) * h₂ := by group
      _ = 1 := by rw [ha2]; group
  have hg₂H : g₁ * h₂ ∉ H := by
    intro hh
    apply hg₁H
    have : g₁ = (g₁ * h₂) * h₂⁻¹ := by group
    rw [this]
    exact H.mul_mem hh (H.inv_mem hh₂H)
  have hat₂ : t = (g₁ * h₂) * (h₂⁻¹ * a * h₂) * (g₁ * h₂)⁻¹ := by rw [hat₁]; group
  have htS : t ∈ (S : Subgroup G) := hh₁
  exact hcore ha₂ (centralizer_conj_le hh₂H haH) hg₂H hat₂ htS
    (fun x hxS hxt => hUh' ⟨hxS, Subgroup.mem_centralizer_singleton_iff.mpr hxt.symm⟩)


theorem MinCex.part1 (h : E187Hyps p f) (h4 : E187E4C p f)
    (c : MinCex p f Ω K S R W H) {z : G} (hz : IsUniqueInvolution K z) (hzW : z ∈ W)
    (hP : ∀ x : G, x * z * x⁻¹ ∈ H → x ∈ H) {a g : G} (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (haH : Subgroup.centralizer ({a} : Set G) ≤ H) (hgt : g * a * g⁻¹ ∈ H) :
    ∃ h' ∈ H, h' * a * h'⁻¹ = g * a * g⁻¹ := by
  have hp : p ≠ 2 := c.stand.odd
  have hq : 5 ≤ p ^ f := c.stand.five
  have hΩ : HypOmegaMod p f Ω := c.stand.hyp
  have hA : EtaAbelian Ω := h.etaAbelian hp hq hΩ
  exact E187C.part1_of (c.sylow_le hA)
    (fun ha2 haH hgH hat htS hCS => c.part1_core h h4 hz hzW hP ha2 haH hgH hat htS hCS) ha2 ha1
    haH hgt

end CFSG.ClassicalInvolution.Asc77
