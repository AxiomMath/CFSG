module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpE4Zc
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpE4Gen
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpQ8

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section

variable {G : Type} [Group G] {z : G} {k : Kind}
variable {A : Type} [Group A] [Finite A] {a : A} {p : ℕ} {X : Subgroup A}

omit [Finite A] in
theorem mem_normalizer_of_normal {R : Subgroup A} (hR : R.Normal) (g : A) :
    g ∈ normalizer (R : Set A) := by
  rw [Subgroup.mem_normalizer_iff]
  intro r
  constructor
  · intro hr
    exact hR.conj_mem r hr g
  · intro hr
    have := hR.conj_mem _ hr g⁻¹
    simpa [mul_assoc] using this

theorem SubData.R_comm (F : E4Hyp G z k) {c : E4Ctx G z A a p X} {J : Subgroup A} (d : SubData c J)
    (h : Sl2Cl p (secZ a X J) (secX a X J) (secJ a X J)) : ⁅pCore 2 A, X⁆ = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨c.A4.prime⟩
  by_contra hWne
  have hRn : (pCore 2 A).Normal := pCore_normal
  have hR2 : IsPGroup 2 ↥(pCore 2 A) := pCore_isPGroup
  have hRJ : pCore 2 A ≤ centralizer (J : Set A) := pCore_le_centralizer_comp d.comp 2
  set R := pCore 2 A with hR
  set W := ⁅R, X⁆ with hWdef
  have hWR : W ≤ R := by
    rw [hWdef, Subgroup.commutator_le]
    intro r hr x _
    have : ⁅r, x⁆ = r * (x * r⁻¹ * x⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact mul_mem hr (hRn.conj_mem _ (inv_mem hr) x)
  have hW2 : IsPGroup 2 ↥W := hR2.to_le hWR
  have hXR : X ≤ normalizer (R : Set A) := fun x _ => mem_normalizer_of_normal hRn x
  have hXW : X ≤ normalizer (W : Set A) := fun x hx =>
    CoreA.mem_normalizer_commutator (mem_normalizer_of_normal hRn x) (le_normalizer hx)
  have haW : a ∈ normalizer (W : Set A) :=
    CoreA.mem_normalizer_commutator (mem_normalizer_of_normal hRn a) c.a_mem_normalizer
  have hsetup : Setup412 p W X a :=
    { prime := c.A4.prime, odd := c.A4.odd, W2 := hW2, Xp := c.A4.pgroup, XW := hXW, zW := haW,
      z2 := c.z2, zX := c.a_mem_normalizer, comm := c.A4.comm, Cz := fun w _ hw => c.inv w hw }
  have hcop : Nat.Coprime (Nat.card ↥X) (Nat.card ↥R) := by
    obtain ⟨n, hn⟩ := c.A4.pgroup.exists_card_eq
    obtain ⟨m, hm⟩ := hR2.exists_card_eq
    rw [hn, hm]
    exact Nat.Coprime.pow n m ((Nat.coprime_primes c.A4.prime Nat.prime_two).2 c.A4.odd)
  have hWW : ⁅W, X⁆ = W := CoreA.commutator_commutator_eq_of_coprime hXR hcop
  have hcore : Core412 W X a := core412_of_setup hsetup hWW hWne
  obtain ⟨y₁, hy₁, hy₁sq, hy₁4, hy₁c, hy₁z⟩ := d.exists_y h
  obtain ⟨F₀, hF₀, hFin, hodd, h3, ⟨eK⟩, -⟩ := Sl2Cl.model c.A4.prime c.A4.odd h
  obtain ⟨eS⟩ := secJ_equiv d.hyp
  have hcen : center (Hat J) ≠ ⊥ := center_ne_bot_of_sl2 hodd (eS.symm.trans eK)
  have hsC : y₁ * y₁ ∈ centralizer (J : Set A) := by
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    exact (hy₁c j hj).symm
  have huniq : ∀ g : A, g * g = 1 → g ≠ 1 → g ∈ centralizer (J : Set A) → g = y₁ * y₁ := by
    intro g hg2 hg1 hgC
    refine F.uinv A a c.sec J d.comp hcen g (y₁ * y₁) hg2 hy₁4 hg1 hy₁sq hgC hsC ?_
    have := Subgroup.mem_centralizer_iff.mp hgC (y₁ * y₁) (J.mul_mem hy₁ hy₁)
    exact this.symm
  have hZ : ∀ g ∈ W ⊓ centralizer (W : Set A), g = 1 ∨ g = y₁ * y₁ := by
    intro g hg
    by_cases hg1 : g = 1
    · exact Or.inl hg1
    · exact Or.inr (huniq g (hcore.Z_exp2 g hg) hg1 (hRJ (hWR hg.1)))
  have hWnt : Nontrivial ↥W := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    exact hWne
  have hcenW : Nontrivial (center ↥W) := hW2.center_nontrivial
  obtain ⟨⟨g, hgc⟩, hg1⟩ := exists_ne (1 : center ↥W)
  have hgZ : (g : A) ∈ W ⊓ centralizer (W : Set A) := by
    refine ⟨g.2, ?_⟩
    show (g : A) ∈ centralizer (W : Set A)
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have := Subgroup.mem_center_iff.mp hgc ⟨w, hw⟩
    exact congrArg Subtype.val this
  have hgne : (g : A) ≠ 1 := fun h1 => hg1 (Subtype.ext (Subtype.ext h1))
  have hsZ : y₁ * y₁ ∈ W ⊓ centralizer (W : Set A) := by
    rcases hZ _ hgZ with h1 | h1
    · exact absurd h1 hgne
    · rw [← h1]; exact hgZ
  obtain ⟨-, y₂, hy₂W, hy₂sq, hy₂z⟩ := q8_data hsetup hWW hWne hy₁sq hsZ hZ
  exact d.zcontra h hy₁ hy₁sq hy₁4 hy₁z (hRJ (hWR hy₂W)) hy₂sq hy₂z

end

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
