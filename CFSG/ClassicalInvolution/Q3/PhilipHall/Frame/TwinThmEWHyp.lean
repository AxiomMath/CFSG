module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPrintedDefs
public import CFSG.ClassicalInvolution.Asc77.AscE187Conj

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

namespace TwinDisc

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem CentralizersPrinted.conj (hΩ : ConjInvariant Ω) {K W H : Subgroup G}
    (h : CentralizersPrinted Ω K W H) (g : G) :
    CentralizersPrinted Ω (conjSub g K) (conjSub g W) (conjSub g H) := by
  intro J hJ a haJ haW ha1 ha2
  have hJ' : conjSub g⁻¹ J ∈ KPerp Ω K := by
    have := KPerp_conj hΩ hJ g⁻¹
    rwa [conjSub_inv_conjSub] at this
  have haJ' : g⁻¹ * a * g ∈ K ⊔ conjSub g⁻¹ J := by
    have := conj_mem_conjSub (n := g⁻¹) haJ
    rwa [conjSub_sup, inv_inv, conjSub_inv_conjSub] at this
  have haW' : g⁻¹ * a * g ∈ W := by
    have := conj_mem_conjSub (n := g⁻¹) haW
    rwa [inv_inv, conjSub_inv_conjSub] at this
  have ha1' : g⁻¹ * a * g ≠ 1 := by
    intro h1
    apply ha1
    have : a = g * (g⁻¹ * a * g) * g⁻¹ := by group
    rw [this, h1]
    group
  have ha2' : (g⁻¹ * a * g) * (g⁻¹ * a * g) = 1 := by
    calc (g⁻¹ * a * g) * (g⁻¹ * a * g) = g⁻¹ * (a * a) * g := by group
      _ = 1 := by rw [ha2]; group
  have hc := h _ hJ' _ haJ' haW' ha1' ha2'
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff] at hx
  have hx' : g⁻¹ * x * g ∈ Subgroup.centralizer ({g⁻¹ * a * g} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g⁻¹ * x * g * (g⁻¹ * a * g) = g⁻¹ * (x * a) * g := by group
      _ = g⁻¹ * (a * x) * g := by rw [hx]
      _ = g⁻¹ * a * g * (g⁻¹ * x * g) := by group
  have := hc hx'
  rw [mem_conjSub_iff]
  exact this

end TwinDisc

namespace TwinThmEW

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem conjSub_inf' (g : G) (A B : Subgroup G) :
    conjSub g (A ⊓ B) = conjSub g A ⊓ conjSub g B := by
  ext x
  simp only [mem_conjSub_iff, Subgroup.mem_inf]

@[expose] def CentAll (Ω : Set (Subgroup G)) (W H : Subgroup G) : Prop :=
  ∀ M ∈ Ω, M ⊓ W ∈ USet Ω → TwinDisc.CentralizersPrinted Ω M W H

@[expose] def CentPairs (Ω : Set (Subgroup G)) (S W H : Subgroup G) : Prop :=
  ∀ M ∈ Ω, M ⊓ W ∈ USet Ω → ∀ J ∈ KPerp Ω M, ∀ R₁ R₂ : Subgroup G, R₁ ∈ RSet Ω → R₁ ≤ M → R₁ ≤ S →
    R₂ ∈ RSet Ω → R₂ ≤ J → R₂ ≤ S → (Commutes R₁ R₂ ∨ R₂ = R₁) → ∀ a ∈ R₁ ⊔ R₂, a ∈ W → a ≠ 1 →
      a * a = 1 → Subgroup.centralizer ({a} : Set G) ≤ H

theorem CentAll.toPairs {W H : Subgroup G} (h : CentAll Ω W H) (S : Subgroup G) :
    CentPairs Ω S W H :=
  fun M hM hMW J hJ _ _ _ hR₁M _ _ hR₂J _ _ a haR haW ha1 ha2 =>
    h M hM hMW J hJ a (sup_le_sup hR₁M hR₂J haR) haW ha1 ha2

structure EHypAll (Ω : Set (Subgroup G)) (K S W H : Subgroup G) : Prop where
  trans : ∀ J ∈ dstarComp Ω K, ∃ h ∈ H, conjSub h K = J
  cent : CentPairs Ω S W H

theorem CentPairs.conj (hΩ : ConjInvariant Ω) {S W H : Subgroup G} (h : CentPairs Ω S W H) (g : G) :
    CentPairs Ω (conjSub g S) (conjSub g W) (conjSub g H) := by
  intro M hM hMW J hJ R₁ R₂ hR₁ hR₁M hR₁S hR₂ hR₂J hR₂S hcomm a haR haW ha1 ha2
  have hM' : conjSub g⁻¹ M ∈ Ω := hΩ g⁻¹ M hM
  have hMW' : conjSub g⁻¹ M ⊓ W ∈ USet Ω := by
    have := USet.conj hΩ hMW g⁻¹
    rwa [conjSub_inf', conjSub_inv_conjSub] at this
  have hJ' : conjSub g⁻¹ J ∈ KPerp Ω (conjSub g⁻¹ M) := KPerp_conj hΩ hJ g⁻¹
  have hS' : ∀ {R : Subgroup G}, R ≤ conjSub g S → conjSub g⁻¹ R ≤ S := fun {R} hR => by
    have := conjSub_mono (n := g⁻¹) hR
    rwa [conjSub_inv_conjSub] at this
  have hcomm' : Commutes (conjSub g⁻¹ R₁) (conjSub g⁻¹ R₂) ∨ conjSub g⁻¹ R₂ = conjSub g⁻¹ R₁ := by
    rcases hcomm with h1 | h1
    · exact Or.inl (h1.conjSub g⁻¹)
    · exact Or.inr (by rw [h1])
  have haR' : g⁻¹ * a * g ∈ conjSub g⁻¹ R₁ ⊔ conjSub g⁻¹ R₂ := by
    have := conj_mem_conjSub (n := g⁻¹) haR
    rwa [conjSub_sup, inv_inv] at this
  have haW' : g⁻¹ * a * g ∈ W := by
    have := conj_mem_conjSub (n := g⁻¹) haW
    rwa [inv_inv, conjSub_inv_conjSub] at this
  have ha1' : g⁻¹ * a * g ≠ 1 := by
    intro h1
    apply ha1
    have : a = g * (g⁻¹ * a * g) * g⁻¹ := by group
    rw [this, h1]
    group
  have ha2' : (g⁻¹ * a * g) * (g⁻¹ * a * g) = 1 := by
    calc (g⁻¹ * a * g) * (g⁻¹ * a * g) = g⁻¹ * (a * a) * g := by group
      _ = 1 := by rw [ha2]; group
  have hc := h _ hM' hMW' _ hJ' _ _ (RSet.conj hΩ hR₁ g⁻¹) (conjSub_mono hR₁M) (hS' hR₁S)
    (RSet.conj hΩ hR₂ g⁻¹) (conjSub_mono hR₂J) (hS' hR₂S) hcomm' _ haR' haW' ha1' ha2'
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff] at hx
  have hx' : g⁻¹ * x * g ∈ Subgroup.centralizer ({g⁻¹ * a * g} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g⁻¹ * x * g * (g⁻¹ * a * g) = g⁻¹ * (x * a) * g := by group
      _ = g⁻¹ * (a * x) * g := by rw [hx]
      _ = g⁻¹ * a * g * (g⁻¹ * x * g) := by group
  have := hc hx'
  rw [mem_conjSub_iff]
  exact this

theorem CentPairs.conj_of_mem (hΩ : ConjInvariant Ω) {S W H : Subgroup G} (h : CentPairs Ω S W H)
    {x : G} (hx : x ∈ H) : CentPairs Ω (conjSub x S) (conjSub x W) H := by
  have := h.conj hΩ x
  rwa [conjSub_eq_self_of_mem hx] at this

theorem EHypAll.conj (hΩ : ConjInvariant Ω) {K S W H : Subgroup G} (h : EHypAll Ω K S W H) (g : G) :
    EHypAll Ω (conjSub g K) (conjSub g S) (conjSub g W) (conjSub g H) where
  trans := by
    intro J hJ
    have hJ' : conjSub g⁻¹ J ∈ dstarComp Ω K := by
      have := dstarComp_conj hΩ hJ g⁻¹
      rwa [conjSub_inv_conjSub] at this
    obtain ⟨h₀, hh₀, hh₀K⟩ := h.trans _ hJ'
    refine ⟨g * h₀ * g⁻¹, conj_mem_conjSub hh₀, ?_⟩
    rw [show g * h₀ * g⁻¹ = g * (h₀ * g⁻¹) by group, conjSub_mul, conjSub_mul,
      conjSub_inv_conjSub, hh₀K, conjSub_conjSub_inv]
  cent := h.cent.conj hΩ g

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
