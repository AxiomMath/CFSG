module

public import CFSG.ClassicalInvolution.Q3.Q3PPEdgeThird
public import CFSG.ClassicalInvolution.Q3.Q3NMM11
public import CFSG.ClassicalInvolution.Q3.Q3NMSl23
public import CFSG.ClassicalInvolution.Q3.Q3PPFundFix

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3PP

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution.Q3.Q3OF CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3NM

theorem fixedOddFree_of_kind_sl23 {c : CompData} (hc : c = CompData.sl23) :
    FixedOddFree (c.G ⧸ Subgroup.center c.G) := by
  subst hc
  exact fixedOddFree_sl23

theorem fixedOddFree_of_kind_m11 {c : CompData} (hc : c = CompData.m11) :
    FixedOddFree (c.G ⧸ Subgroup.center c.G) := by
  subst hc
  exact fixedOddFree_m11_quotient

section Edge

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}
  {K₁ K₂ : Subgroup G} {z₁ z₂ : G} {ι : Type}

namespace EdgeData

theorem oddCoreIn_layer_fixed_le_of_conj [Finite ι] (hR : RouteD3Setup K z)
    (h : EdgeData K K₁ K₂ z₁ z₂) (hN : EdgeThirdFree K K₁ K₂ z₁ z₂)
    (hXN : NonClassicalAt (conjClass3 K) (z₁ * z₂)) (h1 : TwinFreeAt (conjClass3 K) K₁ z₁)
    (h2 : TwinFreeAt (conjClass3 K) K₂ z₂)
    (D : LieSystemData3 ι (locQuot (conjClass3 K) z₁) (locFamily (conjClass3 K) z₁)) {i₂ : ι}
    (hi₂ : locImg (conjClass3 K) z₁ K₂ ≤ (D.hom i₂).range)
    (hk : FixedOddFree ((D.kind i₂).G ⧸ Subgroup.center (D.kind i₂).G) ∨
      FixedOddFreeFund (D.kind i₂))
    {g : G} (hne : g * z₁ * g⁻¹ ≠ z₁)
    (hKb : K₁ ≤ Subgroup.centralizer ({g * z₁ * g⁻¹} : Set G))
    (hzb : z₂ * (g * z₁ * g⁻¹) = (g * z₁ * g⁻¹) * z₂) :
    oddCoreIn (centralizingLayer (conjClass3 K) {g * z₁ * g⁻¹} ⊓
        Subgroup.centralizer ({z₁ * z₂} : Set G)) ≤
      oddCoreIn (centralizingLayer (conjClass3 K) {g * z₁ * g⁻¹}) := by
  have hΩ := hR.inClass
  have hex := hR.setup.1
  have hR₁ : RouteD3Setup K₁ z₁ := Q3TC.RouteD3Setup.of_mem_conjClass3 hR h.mem₁ h.cls₁
  have hcl : conjClass3 K₁ = conjClass3 K := Q3TC.conjClass3_eq_of_mem h.mem₁
  have hP1 : LocalOddCentral (conjClass3 K) {z₁} := hcl ▸ hR₁.setup.2
  have hO3 : LocalOddThreeFree3 (conjClass3 K) z₁ :=
    hcl ▸ Q3W.oddThreeFreeInput_proved G K₁ z₁ hR₁
  have hK₁z : K₁ ∈ centralizingMembers (conjClass3 K) {z₁} :=
    ⟨h.mem₁, isSubnormal_le h.cls₁.subnormal⟩
  have hK₂z : K₂ ∈ centralizingMembers (conjClass3 K) {z₁} := ⟨h.mem₂, h.le_centralizer₁⟩
  obtain ⟨i₁, i₂', -, hi₁, hi₂', hA1, hcover, -⟩ :=
    h.layer_z₁_two_components_of_third hR hN hXN h1 h2 D
  have hii : i₂ = i₂' := eq_of_locImg_le_range3 hΩ hex hP1 hO3 D hK₂z hi₂ hi₂'
  subst hii
  have hK₁b : K₁ ∈ centralizingMembers (conjClass3 K) {g * z₁ * g⁻¹} := ⟨h.mem₁, hKb⟩
  rw [centralizingMembers_conj hΩ.conjInvariant g z₁] at hK₁b
  obtain ⟨K', hK'm, hK'eq⟩ := hK₁b
  obtain ⟨j, hj⟩ := exists_range_of_mem3 D (mem_locFamily_iff.mpr ⟨K', hK'm, rfl⟩)
  have hjeq : j = i₂ := by
    rcases hcover j with hji | hji
    · exfalso
      subst hji
      have hKK : K₁ = K' :=
        eq_of_mem_compMembers_a13 hΩ hex hP1 hO3 hA1 ⟨hK₁z, hi₁⟩ ⟨hK'm, hj⟩
      have hc : conjSub g K₁ = K₁ := by
        conv_lhs => rw [hKK]
        exact hK'eq
      have hcls : IsClassicalMember3 K₁ (g * z₁ * g⁻¹) := by
        have := h.cls₁.conj g
        rwa [hc] at this
      exact hne (involution_unique3 h.cls₁ hcls).symm
    · exact hji
  have hK'c : K' ∈ compMembers3 (conjClass3 K) z₁ D i₂ := ⟨hK'm, hjeq ▸ hj⟩
  obtain ⟨R, -, hRf, hRK⟩ := exists_corr_left3 hΩ hex hP1 hO3 D hK'c
  have hxb : (z₁ * z₂) * (g * z₁ * g⁻¹) = (g * z₁ * g⁻¹) * (z₁ * z₂) := by
    have hz1 : z₁ * (g * z₁ * g⁻¹) = (g * z₁ * g⁻¹) * z₁ :=
      Subgroup.mem_centralizer_singleton_iff.mp (hKb h.cls₁.mem)
    calc z₁ * z₂ * (g * z₁ * g⁻¹) = z₁ * (z₂ * (g * z₁ * g⁻¹)) := mul_assoc _ _ _
      _ = z₁ * ((g * z₁ * g⁻¹) * z₂) := by rw [hzb]
      _ = (z₁ * (g * z₁ * g⁻¹)) * z₂ := (mul_assoc _ _ _).symm
      _ = ((g * z₁ * g⁻¹) * z₁) * z₂ := by rw [hz1]
      _ = (g * z₁ * g⁻¹) * (z₁ * z₂) := mul_assoc _ _ _
  have hab : g⁻¹ * (z₁ * z₂) * g ∈ Subgroup.centralizer ({z₁} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g⁻¹ * (z₁ * z₂) * g * z₁ = g⁻¹ * ((z₁ * z₂) * (g * z₁ * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z₁ * g⁻¹) * (z₁ * z₂)) * g := by rw [hxb]
      _ = z₁ * (g⁻¹ * (z₁ * z₂) * g) := by group
  have ha2 : orderOf (g⁻¹ * (z₁ * z₂) * g) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) (z₁ * z₂)
    rw [h.orderOf_prod] at this
    simpa [MulAut.conj_apply] using this
  have hK'a : K' ≤ Subgroup.centralizer ({g⁻¹ * (z₁ * z₂) * g} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hy' : g * y * g⁻¹ ∈ K₁ := by
      rw [← hK'eq]
      exact conj_mem_conjSub hy
    have hc := Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer_prod₁ hy')
    calc y * (g⁻¹ * (z₁ * z₂) * g) = g⁻¹ * ((g * y * g⁻¹) * (z₁ * z₂)) * g := by group
      _ = g⁻¹ * ((z₁ * z₂) * (g * y * g⁻¹)) * g := by rw [hc]
      _ = g⁻¹ * (z₁ * z₂) * g * y := by group
  have hO' := oddCoreIn_layer_fixed_le_of_components hΩ.conjInvariant ModelFacts.modelClauseZero
    m11Facts hab ha2 D fun i => by
      rcases hcover i with hi | hi
      · subst hi
        exact Or.inl (fixedOddFree_of_kind_sl23 hA1)
      · subst hi
        rcases hk with hk | hk
        · exact Or.inl hk
        · exact Or.inr ⟨hk, R, hRf, K', hK'm, hK'a, hRK⟩
  have hlay : centralizingLayer (conjClass3 K) {g * z₁ * g⁻¹} =
      conjSub g (centralizingLayer (conjClass3 K) {z₁}) :=
    centralizingLayer_conj hΩ.conjInvariant g z₁
  have hcen : Subgroup.centralizer ({z₁ * z₂} : Set G) =
      conjSub g (Subgroup.centralizer ({g⁻¹ * (z₁ * z₂) * g} : Set G)) := by
    ext y
    rw [mem_conjSub_iff, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hy
      calc g⁻¹ * y * g * (g⁻¹ * (z₁ * z₂) * g) = g⁻¹ * (y * (z₁ * z₂)) * g := by group
        _ = g⁻¹ * ((z₁ * z₂) * y) * g := by rw [hy]
        _ = g⁻¹ * (z₁ * z₂) * g * (g⁻¹ * y * g) := by group
    · intro hy
      calc y * (z₁ * z₂) = g * ((g⁻¹ * y * g) * (g⁻¹ * (z₁ * z₂) * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * (z₁ * z₂) * g) * (g⁻¹ * y * g)) * g⁻¹ := by rw [hy]
        _ = (z₁ * z₂) * y := by group
  have hinf : conjSub g (centralizingLayer (conjClass3 K) {z₁} ⊓
        Subgroup.centralizer ({g⁻¹ * (z₁ * z₂) * g} : Set G)) =
      conjSub g (centralizingLayer (conjClass3 K) {z₁}) ⊓
        conjSub g (Subgroup.centralizer ({g⁻¹ * (z₁ * z₂) * g} : Set G)) := by
    ext y
    simp only [mem_conjSub_iff, Subgroup.mem_inf]
  rw [hlay, hcen, ← hinf, oddCoreIn_conjSub_eq, oddCoreIn_conjSub_eq]
  exact conjSub_mono hO'

theorem involutionOddCore_prod_eq_bot_of_third [Finite ι] (hOA : OddAutLayerRigidHyp)
    (hR : RouteD3Setup K z) (hnab : ∃ a b : G, a * b ≠ b * a) (h : EdgeData K K₁ K₂ z₁ z₂)
    (hN : EdgeThirdFree K K₁ K₂ z₁ z₂) (hXN : NonClassicalAt (conjClass3 K) (z₁ * z₂))
    (h1 : TwinFreeAt (conjClass3 K) K₁ z₁) (h2 : TwinFreeAt (conjClass3 K) K₂ z₂)
    (D : LieSystemData3 ι (locQuot (conjClass3 K) z₁) (locFamily (conjClass3 K) z₁)) {i₂ : ι}
    (hi₂ : locImg (conjClass3 K) z₁ K₂ ≤ (D.hom i₂).range)
    (hk : FixedOddFree ((D.kind i₂).G ⧸ Subgroup.center (D.kind i₂).G) ∨
      FixedOddFreeFund (D.kind i₂))
    (hKl : KleinAt K K₁ z₂) : involutionOddCore (z₁ * z₂) = ⊥ := by
  obtain ⟨M₁, M₂, w₁, hM₁, hM₂, c₁, c₂, hK₁, hcomm, hne⟩ := hKl
  have hcl : conjClass3 K₁ = conjClass3 K := Q3TC.conjClass3_eq_of_mem h.mem₁
  obtain ⟨g₁, hg₁⟩ : M₁ ∈ conjClass3 K₁ := hcl ▸ hM₁
  obtain ⟨g₂, hg₂⟩ : M₂ ∈ conjClass3 K₁ := hcl ▸ hM₂
  have hg₁' : conjSub g₁ K₁ = M₁ := hg₁
  have hg₂' : conjSub g₂ K₁ = M₂ := hg₂
  have hw₁ : w₁ = g₁ * z₁ * g₁⁻¹ := by
    have := h.cls₁.conj g₁
    rw [hg₁'] at this
    exact involution_unique3 c₁ this
  have hw₂ : z₂ * w₁ = g₂ * z₁ * g₂⁻¹ := by
    have := h.cls₁.conj g₂
    rw [hg₂'] at this
    exact involution_unique3 c₂ this
  have hxx : z₁ * z₂ = z₂ * z₁ := h.mul_comm₁₂
  have hne₁ : g₁ * z₁ * g₁⁻¹ ≠ z₁ := by
    intro heq
    have hw : w₁ = z₁ := hw₁.trans heq
    apply hXN M₂ hM₂ (z₂ * w₁) c₂
    rw [hw]
    exact hxx.symm
  have hne₂ : g₂ * z₁ * g₂⁻¹ ≠ z₁ := by
    intro heq
    have h3 : z₂ * w₁ = z₁ := hw₂.trans heq
    apply hXN M₁ hM₁ w₁ c₁
    calc w₁ = z₂ * (z₂ * w₁) := by rw [← mul_assoc, h.sq₂, one_mul]
      _ = z₂ * z₁ := by rw [h3]
      _ = z₁ * z₂ := hxx.symm
  have hK₁₂ : K₁ ≤ Subgroup.centralizer ({z₂ * w₁} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have a1 : y * z₂ = z₂ * y :=
      Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer₂ hy)
    have a2 : y * w₁ = w₁ * y := Subgroup.mem_centralizer_singleton_iff.mp (hK₁ hy)
    calc y * (z₂ * w₁) = (y * z₂) * w₁ := (mul_assoc _ _ _).symm
      _ = z₂ * (y * w₁) := by rw [a1, mul_assoc]
      _ = z₂ * (w₁ * y) := by rw [a2]
      _ = (z₂ * w₁) * y := (mul_assoc _ _ _).symm
  have hz₂₂ : z₂ * (z₂ * w₁) = (z₂ * w₁) * z₂ := by
    calc z₂ * (z₂ * w₁) = (z₂ * z₂) * w₁ := (mul_assoc _ _ _).symm
      _ = w₁ * (z₂ * z₂) := by rw [h.sq₂, one_mul, mul_one]
      _ = (w₁ * z₂) * z₂ := (mul_assoc _ _ _).symm
      _ = (z₂ * w₁) * z₂ := by rw [hcomm]
  have hO₁ := h.oddCoreIn_layer_fixed_le_of_conj hR hN hXN h1 h2 D hi₂ hk (g := g₁) hne₁
    (by rw [← hw₁]; exact hK₁) (by rw [← hw₁]; exact hcomm.symm)
  rw [← hw₁] at hO₁
  have hO₂ := h.oddCoreIn_layer_fixed_le_of_conj hR hN hXN h1 h2 D hi₂ hk (g := g₂) hne₂
    (by rw [← hw₂]; exact hK₁₂) (by rw [← hw₂]; exact hz₂₂)
  rw [← hw₂] at hO₂
  exact h.involutionOddCore_prod_eq_bot_of_klein hOA hR hnab hM₁ hM₂ c₁ c₂ hK₁ hcomm hne hO₁ hO₂

theorem oddCoreIn_layer_prod_eq_bot_of_third [Finite ι] (hOA : OddAutLayerRigidHyp)
    (hR : RouteD3Setup K z) (hnab : ∃ a b : G, a * b ≠ b * a) (h : EdgeData K K₁ K₂ z₁ z₂)
    (hN : EdgeThirdFree K K₁ K₂ z₁ z₂) (hXN : NonClassicalAt (conjClass3 K) (z₁ * z₂))
    (h1 : TwinFreeAt (conjClass3 K) K₁ z₁) (h2 : TwinFreeAt (conjClass3 K) K₂ z₂)
    (D : LieSystemData3 ι (locQuot (conjClass3 K) z₁) (locFamily (conjClass3 K) z₁)) {i₂ : ι}
    (hi₂ : locImg (conjClass3 K) z₁ K₂ ≤ (D.hom i₂).range)
    (hk : FixedOddFree ((D.kind i₂).G ⧸ Subgroup.center (D.kind i₂).G) ∨
      FixedOddFreeFund (D.kind i₂))
    (hKl : KleinAt K K₁ z₂) :
    oddCoreIn (centralizingLayer (conjClass3 K) {z₁ * z₂}) = ⊥ := by
  have h2' := oddCoreIn_centralizingLayer_le hR.inClass.conjInvariant (z₁ * z₂)
  rw [h.involutionOddCore_prod_eq_bot_of_third hOA hR hnab hN hXN h1 h2 D hi₂ hk hKl] at h2'
  exact le_bot_iff.mp h2'

end EdgeData

end Edge

end CFSG.ClassicalInvolution.Q3.Q3PP
