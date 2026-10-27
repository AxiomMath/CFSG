module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmQ3LBase
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmQ3LG2Sh
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmPair
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3G2Core
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5G2D4

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TA3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)


set_option linter.unusedSectionVars false

namespace Q3L

theorem card_outer_le_two_g23
    {X : Type} [Group X]
    (hm : LieModel X .G2 0 3 1) : Nat.card (Outer X) ≤ 2 := by
  obtain ⟨⟨-, hf1, -⟩, hm'⟩ :=
    Q5G2D4.chevalleyExceptionalModel_of_lieModel hm (by decide) (by decide) (by decide)
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hm'
  have : CharP K ReeTag.G2.prime :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_three
      hf1 hK
  obtain ⟨-, -, ⟨Θ, -, hsurj, hker⟩, -⟩ := G2_three_exact_automorphism_normal_form hf1 K hK
  have hinner : inner (CFSG.Blueprint.Chevalley.adjointGroup ReeTag.G2.tag K) = Θ.ker :=
    hker.symm
  let e₂ : Outer (CFSG.Blueprint.Chevalley.adjointGroup ReeTag.G2.tag K) ≃*
      Multiplicative (ZMod (2 * 1)) :=
    (QuotientGroup.quotientMulEquivOfEq hinner).trans
      (QuotientGroup.quotientKerEquivOfSurjective Θ hsurj)
  rw [Nat.card_congr (((equivalence e).trans e₂).toEquiv.trans Multiplicative.toAdd),
    Nat.card_zmod]

theorem mul_inv_mem_of_card_outer_le_two {Y : Type} [Group Y] [Finite Y] {N : Subgroup Y}
    [N.Normal] (hC : Subgroup.centralizer (N : Set Y) = ⊥) (h2 : Nat.card (Outer N) ≤ 2)
    {y y' : Y} (hy : y ∉ N) (hy' : y' ∉ N) : y * y'⁻¹ ∈ N := by
  classical
  rw [← outerHom_eq_one_iff hC]
  by_contra hne
  have h1 : outerHom N y ≠ 1 := fun h => hy ((outerHom_eq_one_iff hC).mp h)
  have h1' : outerHom N y' ≠ 1 := fun h => hy' ((outerHom_eq_one_iff hC).mp h)
  have hne' : outerHom N y ≠ outerHom N y' := fun heq => hne (by
    rw [map_mul, map_inv, heq, mul_inv_cancel])
  have : Finite (MulAut N) := Nobq.finite_mulAut_of_finite N
  have : Fintype (Outer N) := Fintype.ofFinite _
  have hcard : ({1, outerHom N y, outerHom N y'} : Finset (Outer N)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [h1.symm, h1'.symm]), Finset.card_pair hne']
  have h3 : 3 ≤ Nat.card (Outer N) := by
    rw [Nat.card_eq_fintype_card, ← hcard]
    exact Finset.card_le_univ _
  omega


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem exists_u1_sylow (h : PerpHypS n Y R S t) {N : Subgroup Y} [N.Normal]
    (hC : Subgroup.centralizer (N : Set Y) = ⊥) (hO : Nobq.OutTwoCyclic ↥N) :
    t ∈ N ∧ ∃ s ∈ (S : Subgroup R).map R.subtype, s ∈ N ∧ orderOf s = 4 := by
  obtain ⟨htN, s, hsK, hsN, hs4⟩ := exists_u1_of_outTwoCyclic h hC hO
  have hs2 : IsPGroup 2 (Subgroup.zpowers s) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hs4]; norm_num)
  obtain ⟨y, hyK, hy⟩ := Asc77.exists_conj_of_isSylow2In h.core.datum.sylow_core hs2
    (Subgroup.zpowers_le.mpr hsK)
  have hs' : y⁻¹ * s * y ∈ (S : Subgroup R).map R.subtype :=
    mem_conjSub_iff.mp (hy (Subgroup.mem_zpowers s))
  refine ⟨htN, y⁻¹ * s * y, hs', ?_, ?_⟩
  · have := (inferInstance : N.Normal).conj_mem s hsN y⁻¹
    rwa [inv_inv] at this
  · have := MulEquiv.orderOf_eq (MulAut.conj y⁻¹) s
    rw [MulAut.conj_apply, inv_inv] at this
    rw [this, hs4]

theorem core_le_of_sylow_le (h : PerpHypS n Y R S t) {N : Subgroup Y} [N.Normal]
    (hS : (S : Subgroup R).map R.subtype ≤ N) : tightCore R ≤ N := by
  refine (Subgroup.closure_le N).mpr ?_
  rintro x ⟨hxR, hx2⟩
  have hxK : x ∈ tightCore R := Subgroup.subset_closure ⟨hxR, hx2⟩
  obtain ⟨y, -, hy⟩ := Asc77.exists_conj_of_isSylow2In h.core.datum.sylow_core hx2
    (Subgroup.zpowers_le.mpr hxK)
  have h1 : y⁻¹ * x * y ∈ N := hS (mem_conjSub_iff.mp (hy (Subgroup.mem_zpowers x)))
  have := (inferInstance : N.Normal).conj_mem _ h1 y
  rwa [show y * (y⁻¹ * x * y) * y⁻¹ = x by group] at this

theorem eq_top_of_core_le (h : PerpHypS n Y R S t) {N : Subgroup Y} [N.Normal]
    (hK : tightCore R ≤ N) : N = ⊤ := by
  have hgen : (⨆ g : Y, conjSub g (tightCore R)) = ⊤ := h.core.gen
  rw [eq_top_iff, ← hgen]
  refine iSup_le fun g x hx => ?_
  have hx' := hK (mem_conjSub_iff.mp hx)
  have := (inferInstance : N.Normal).conj_mem _ hx' g
  rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at this

theorem false_of_cross (h : PerpHypS n Y R S t) {N : Subgroup Y} [N.Normal]
    (hOut : ∀ y y' : Y, y ∉ N → y' ∉ N → y * y'⁻¹ ∈ N) {A B : Subgroup Y}
    (hAN : ∀ c ∈ N ⊓ Subgroup.centralizer ({t} : Set Y), ∀ a ∈ A, c * a * c⁻¹ ∈ A)
    (hAB : ∀ x ∈ A, x ∈ B → x = 1 ∨ x = t) {g : Y}
    (hgc : g ∈ Subgroup.centralizer ({t} : Set Y)) {s : Y}
    (hsS : s ∈ (S : Subgroup R).map R.subtype) (hs4 : orderOf s = 4) (hsA : s ∈ A)
    (hs'B : g * s * g⁻¹ ∈ B) : False := by
  have hs'4 : orderOf (g * s * g⁻¹) = 4 := by
    have := MulEquiv.orderOf_eq (MulAut.conj g) s
    rw [MulAut.conj_apply] at this
    rw [this, hs4]
  have key : g * s * g⁻¹ ∈ A → False := fun hA => by
    rcases hAB _ hA hs'B with h1 | h1
    · rw [h1, orderOf_one] at hs'4
      exact absurd hs'4 (by norm_num)
    · rw [h1, h.core.datum.order] at hs'4
      exact absurd hs'4 (by norm_num)
  have hS0C : ∀ w ∈ (S : Subgroup R).map R.subtype, w ∈ Subgroup.centralizer ({t} : Set Y) :=
    fun w hw => h.core.datum.cent (tightCore_le R (h.core.datum.sylow_core.1 hw))
  by_cases hgN : g ∈ N
  · exact key (hAN g (Subgroup.mem_inf.mpr ⟨hgN, hgc⟩) s hsA)
  by_cases hS0 : (S : Subgroup R).map R.subtype ≤ N
  · apply hgN
    rw [eq_top_of_core_le h (core_le_of_sylow_le h hS0)]
    exact Subgroup.mem_top g
  obtain ⟨w, hwS, hwN⟩ := SetLike.not_le_iff_exists.mp hS0
  obtain ⟨e⟩ := h.core.q8
  let e₀ : ↥((S : Subgroup R).map R.subtype) ≃* QuaternionGroup 2 :=
    ((S : Subgroup R).equivMapOfInjective R.subtype R.subtype_injective).symm.trans e
  have hx4 : orderOf (⟨s, hsS⟩ : ↥((S : Subgroup R).map R.subtype)) = 4 := by
    rw [Subgroup.orderOf_mk]; exact hs4
  have hws : w * s * w⁻¹ ∈ A := by
    rcases q8_conj e₀ hx4 ⟨w, hwS⟩ with h1 | h1
    · have h2 : w * s * w⁻¹ = s := congrArg Subtype.val h1
      rw [h2]; exact hsA
    · have h2 : w * s * w⁻¹ = s⁻¹ := congrArg Subtype.val h1
      rw [h2]; exact inv_mem hsA
  have hc : g * w⁻¹ ∈ N ⊓ Subgroup.centralizer ({t} : Set Y) :=
    Subgroup.mem_inf.mpr ⟨hOut g w hgN hwN, mul_mem hgc (inv_mem (hS0C w hwS))⟩
  have := hAN _ hc _ hws
  rw [show g * w⁻¹ * (w * s * w⁻¹) * (g * w⁻¹)⁻¹ = g * s * g⁻¹ by group] at this
  exact key this

end Q3L


theorem leaf_g23 {n : ℕ} : TwinLeafS n fun F _ => LieModel F .G2 0 3 1 :=
  TwinLeafS.of_no fun Y _ _ R S t h _ hm => by
    haveI := h.core.simple
    haveI hTn : (genFittingFStar Y).Normal := genFittingFStar_normal Y
    have hC : Subgroup.centralizer ((genFittingFStar Y : Subgroup Y) : Set Y) = ⊥ :=
      Nobq.centralizer_genFittingFStar_eq_bot h.core.nonab
    obtain ⟨htN, s, hsS, hsN, hs4⟩ := Q3L.exists_u1_sylow h hC
      (outTwoCyclic_G2 (by decide)
        (Q5G2D4.chevalleyExceptionalModel_of_lieModel hm (by decide) (by decide) (by decide)))
    have hsK : s ∈ tightCore R := h.core.datum.sylow_core.1 hsS
    have hOut : ∀ y y' : Y, y ∉ genFittingFStar Y → y' ∉ genFittingFStar Y →
        y * y'⁻¹ ∈ genFittingFStar Y := fun y y' hy hy' =>
      Q3L.mul_inv_mem_of_card_outer_le_two hC (Q3L.card_outer_le_two_g23 hm) hy hy'
    have ht : orderOf (⟨t, htN⟩ : genFittingFStar Y) = 2 := by
      rw [Subgroup.orderOf_mk]; exact h.core.datum.order
    obtain ⟨F, _, _, Sh, hcard, hz⟩ :=
      GH74.GLS.IVK.GHInv.exists_shape_G2 Nat.prime_three (by decide) hm _ ht
    have hF : Nat.card F = 3 := by rw [hcard, pow_one]
    have h3 : (3 : F) = 0 := LieType.HighestRoot.three_eq_zero hF
    have h2 : (2 : F) ≠ 0 := two_ne_zero_of_three h3
    have hzt : ((Sh.z : genFittingFStar Y) : Y) = t := by rw [hz]
    set P := Q3Sh.toCentShape htN Sh hzt h3 h2 with hP
    have hsq : ∀ c ∈ genFittingFStar Y ⊓ Subgroup.centralizer ({t} : Set Y), c * c = t →
        c ∈ P.A ∨ c ∈ P.B := by
      intro c hc hcc
      obtain ⟨x, rfl⟩ := Q3Sh.exists_ι htN hc
      have hxx : x * x = Sh.z := by
        apply Q3Sh.ι_injective htN
        rw [map_mul, hcc]
        exact hzt.symm
      rcases Q3L.mem_or_of_mul_self Sh h2 h2 hxx with hx | hx
      · exact Or.inl ⟨x, hx, rfl⟩
      · exact Or.inr ⟨x, hx, rfl⟩
    obtain ⟨g, hgc, hne, -, -⟩ := exists_twin h
    have hsC : s ∈ Subgroup.centralizer ({t} : Set Y) := h.core.datum.cent (tightCore_le R hsK)
    have hsD : s ∈ genFittingFStar Y ⊓ Subgroup.centralizer ({t} : Set Y) :=
      Subgroup.mem_inf.mpr ⟨hsN, hsC⟩
    have hs'D : g * s * g⁻¹ ∈ genFittingFStar Y ⊓ Subgroup.centralizer ({t} : Set Y) :=
      Subgroup.mem_inf.mpr ⟨hTn.conj_mem s hsN g,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hgc hsC) (Subgroup.inv_mem _ hgc)⟩
    have hss : s * s = t := by
      have hz0 := uniqueInv_core h
      obtain ⟨h4, h2'⟩ := Q3L.pow_four_of_orderOf hs4
      refine (hz0.unique _ (mul_mem hsK hsK) ?_).resolve_left ?_
      · have e4 : (s * s) * (s * s) = s ^ 4 := by
          simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        rw [e4]
        exact h4
      · exact fun h1 => h2' (by rw [sq]; exact h1)
    have hs's : (g * s * g⁻¹) * (g * s * g⁻¹) = t := by
      have hgt : g * t * g⁻¹ = t := by
        rw [Subgroup.mem_centralizer_singleton_iff] at hgc
        rw [hgc]; group
      rw [show (g * s * g⁻¹) * (g * s * g⁻¹) = g * (s * s) * g⁻¹ by group, hss, hgt]
    rcases hsq s hsD hss with hsA | hsB <;> rcases hsq _ hs'D hs's with hs'A | hs'B
    · exact Q3L.false_of_twin_hom h (θ := P.A.subtype) Subtype.val_injective
        (Q3L.sl3_q8 hF P.eA) hgc hne hsK hs4 ⟨⟨s, hsA⟩, rfl⟩ ⟨⟨_, hs'A⟩, rfl⟩
    · exact Q3L.false_of_cross h hOut P.normal_A P.inter hgc hsS hs4 hsA hs'B
    · exact Q3L.false_of_cross h hOut (A := P.B) (B := P.A) P.normal_B
        (fun x hxB hxA => P.inter x hxA hxB) hgc hsS hs4 hsB hs'A
    · exact Q3L.false_of_twin_hom h (θ := P.B.subtype) Subtype.val_injective
        (Q3L.sl3_q8 hF P.eB) hgc hne hsK hs4 ⟨⟨s, hsB⟩, rfl⟩ ⟨⟨_, hs'B⟩, rfl⟩

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small
