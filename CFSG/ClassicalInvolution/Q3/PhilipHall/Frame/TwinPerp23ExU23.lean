module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf3Members
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf4Conn
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23Pf3Main

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement



section U23

open CFSG.ClassicalInvolution.Balance

theorem oddCore_centralizes_twoElt_gen {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {K K' : Subgroup G} {t : G} (hΩ : HypOmegaGen Ω) (hK : K ∈ Ω) (hK'Ω : K' ∈ Ω) (hne : K' ≠ K)
    (hz : IsUniqueInvolution K t) (hzK' : IsUniqueInvolution K' t)
    (hcard8 : ∀ P : Subgroup G, IsSylow2In P K → Nat.card ↥P = 8)
    (hxy : ∀ R₁ R₂ : Subgroup G, IsSylow2In R₁ K → IsSylow2In R₂ K' → Commutes R₁ R₂ →
      ∀ x ∈ R₁, ∀ y ∈ R₂, orderOf x = 4 → orderOf y = 4 →
        ∀ g ∈ oddCoreOf (Subgroup.centralizer ({t} : Set G)), g * (x * y) = (x * y) * g)
    {a : G} (ha : a ∈ K) (ha2 : IsPGroup 2 (Subgroup.zpowers a)) :
    ∀ g ∈ oddCoreOf (Subgroup.centralizer ({t} : Set G)), g * a = a * g := by
  intro g hg
  obtain ⟨R₁, hR₁, hzle⟩ := IsSylow2In.exists_ge ha2 (Subgroup.zpowers_le.mpr ha)
  have haR : a ∈ R₁ := hzle (Subgroup.mem_zpowers a)
  have hR₁N : R₁ ≤ Subgroup.normalizer (K' : Set G) :=
    hR₁.1.trans (Sec6Gen.le_normalizer_of_twin hΩ hK hK'Ω hne.symm hz hzK')
  obtain ⟨R₂, hR₂, hfix₂⟩ := exists_sylow_normalized hR₁.2.1 hR₁N
  have hR₁R₂ : R₁ ≤ Subgroup.normalizer (R₂ : Set G) := fun r hr =>
    mem_normalizer_iff_conjSub_eq.mpr (hfix₂ r hr)
  have hP : IsPGroup 2 ↥(R₁ ⊔ R₂) := hR₁.2.1.to_sup_of_normal_right' hR₂.2.1 hR₁R₂
  have c12 : Commutes R₁ R₂ :=
    Sec6Gen.commutes_of_twin_of_isPGroup hΩ hK hK'Ω hne.symm hz hzK' hR₁.1 hR₂.1 hP
  obtain ⟨y, hyR, hy4⟩ := A7T22.exists_orderOf_eq_four_of_isSylow2In hΩ hK'Ω hR₂
  obtain ⟨k, -, ⟨e⟩⟩ := Sec6Gen.isQuatSub_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hK hR₁)
  have : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
  have hcardR := hcard8 R₁ hR₁
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card] at hcardR
  have hn : 2 * 2 ^ k = 4 := by omega
  obtain ⟨p, q, hp, hq, hpq⟩ := TwinPerpV3.q8_exists_diff hn (e ⟨a, haR⟩)
  set x : G := ((e.symm p : R₁) : G) with hxdef
  set x' : G := ((e.symm q : R₁) : G) with hx'def
  have hxR : x ∈ R₁ := (e.symm p).2
  have hx'R : x' ∈ R₁ := (e.symm q).2
  have hx4 : orderOf x = 4 := by rw [hxdef, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]; exact hp
  have hx'4 : orderOf x' = 4 := by rw [hx'def, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]; exact hq
  have hxx' : x⁻¹ * x' = a := by
    have h1 : (e.symm p)⁻¹ * e.symm q = ⟨a, haR⟩ := by
      rw [← map_inv, ← map_mul, hpq]; simp
    have := congrArg (fun r : R₁ => (r : G)) h1
    simpa [hxdef, hx'def] using this
  have g1 := hxy R₁ R₂ hR₁ hR₂ c12 x hxR y hyR hx4 hy4 g hg
  have g2 := hxy R₁ R₂ hR₁ hR₂ c12 x' hx'R y hyR hx'4 hy4 g hg
  have hcom : Commute g (x * y)⁻¹ := (show Commute g (x * y) from g1).inv_right
  have hc3 : Commute g ((x * y)⁻¹ * (x' * y)) := hcom.mul_right (show Commute g (x' * y) from g2)
  have hay : a * y = y * a := c12 a haR y hyR
  have e2 : (x * y)⁻¹ * (x' * y) = a := by
    have : (x * y)⁻¹ * (x' * y) = y⁻¹ * (x⁻¹ * x') * y := by group
    rw [this, hxx']
    calc y⁻¹ * a * y = y⁻¹ * (a * y) := by group
      _ = y⁻¹ * (y * a) := by rw [hay]
      _ = a := by group
  rw [e2] at hc3
  exact hc3.eq

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem p23_oddCore_comm_xy (hP : TL4.TightBelowRPlus 3 n) (hc : P23Cfg n Y R S t K' W u e g)
    (hno : SecNoExit R e) (hα : alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥) :
    ∀ R₁ R₂ : Subgroup Y, IsSylow2In R₁ (tightCore R) → IsSylow2In R₂ K' → Commutes R₁ R₂ →
      ∀ x ∈ R₁, ∀ y ∈ R₂, orderOf x = 4 → orderOf y = 4 →
        ∀ q ∈ oddCoreOf (Subgroup.centralizer ({t} : Set Y)), q * (x * y) = (x * y) * q := by
  intro R₁ R₂ hR₁ hR₂ hcm x hx y hy ox oy q hq
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hK : tightCore R ∈ twinSet (Om R) (tightCore R) := mem_twinSet_self
    (CoreAssembly.mem_conjClass_self _) hz
  obtain ⟨c, hct, hcu⟩ := p23FuseN hP Y R S t K' W u e g hc hno _ hK _ hc.std.hK' hc.std.hne R₁ R₂
    hR₁ hR₂ hcm x hx y hy ox oy
  have hcinv : c⁻¹ ∈ Subgroup.centralizer ({t} : Set Y) := Subgroup.inv_mem _ hct
  have hq' : c⁻¹ * q * c ∈ oddCoreOf (Subgroup.centralizer ({t} : Set Y)) := by
    have := conj_mem_oddCoreIn hcinv hq
    have h' : c⁻¹ * q * c ∈ Balance.oddCoreIn (Subgroup.centralizer ({t} : Set Y)) := by
      simpa using this
    exact h'
  have h1 : (c⁻¹ * q * c) * u = u * (c⁻¹ * q * c) :=
    TwinDisc.oddCore_comm_of_alpha hα (Subgroup.subset_closure (by simp)) hz.ne_one
      (Subgroup.subset_closure (by simp)) hq'
  rw [← hcu]
  calc q * (c * u * c⁻¹) = c * ((c⁻¹ * q * c) * u) * c⁻¹ := by group
    _ = c * (u * (c⁻¹ * q * c)) * c⁻¹ := by rw [h1]
    _ = (c * u * c⁻¹) * q := by group

end U23

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
