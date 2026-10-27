module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76PclsTwo
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44RankTwoX
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylMain
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Hq4O82
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Assembly

public section

namespace CFSG.ComponentClassification.Sol76T13.R12.Pcls

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Multiplier
  CFSG.LieType.Steinberg.CentralExt CFSG.LieType.Chevalley.C2E6Std
  CFSG.RankThree.PartTwo.Sec4.Census

variable {Q : Type} [Group Q] [Finite Q]

theorem three_le_pRank_of_noncentral_involution {x u v : Q} (hx : orderOf x = 2)
    (hxZ : x ∉ center Q) (hu : orderOf u = 2) (hv : orderOf v = 2) (huv : u ≠ v)
    (huZ : u ∈ center Q) (hvZ : v ∈ center Q) : 3 ≤ CFSG.pRank 2 Q := by
  have hsq : ∀ {w : Q}, orderOf w = 2 → w * w = 1 := fun hw => by
    rw [← pow_two, ← hw, pow_orderOf_eq_one]
  have hne : ∀ {w : Q}, orderOf w = 2 → w ≠ 1 := fun hw h => by
    rw [h, orderOf_one] at hw; omega
  have hxu : x * u = u * x := mem_center_iff.mp huZ x
  have hxv : x * v = v * x := mem_center_iff.mp hvZ x
  have huv' : u * v = v * u := mem_center_iff.mp hvZ u
  refine three_le_pRank_of_involutions (hsq hx) (hsq hu) (hsq hv) hxu hxv huv' ?_
  intro a b d h
  have hval : ∀ w : ZMod 2, w = 0 ∨ w = 1 := by decide
  have huvZ : ∀ b d : ZMod 2, u ^ b.val * v ^ d.val ∈ center Q := fun b d =>
    mul_mem (pow_mem huZ _) (pow_mem hvZ _)
  rcases hval a with rfl | rfl
  · rcases hval b with rfl | rfl <;> rcases hval d with rfl | rfl
    · exact ⟨rfl, rfl, rfl⟩
    · simp at h; exact absurd h (hne hv)
    · simp at h; exact absurd h (hne hu)
    · simp only [ZMod.val_zero, ZMod.val_one, pow_zero, pow_one, one_mul] at h
      have h1 := eq_inv_of_mul_eq_one_left h
      rw [inv_eq_of_mul_eq_one_right (hsq hv)] at h1
      exact absurd h1 huv
  · exfalso
    apply hxZ
    have h' : x = (u ^ b.val * v ^ d.val)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← mul_assoc]
      simpa using h
    rw [h']
    exact inv_mem (huvZ b d)

theorem three_le_pRank_of_relRootGroup
    (hO : pPrimeCore 2 Q = ⊥) (e : Q ⧸ center Q ≃* stdGroup)
    {r : Fin CFSG.Blueprint.Chevalley.Tag.F4.rank → ℤ} (hr : CFSG.Blueprint.Chevalley.IsRoot .F4 r)
    (h4 : Nat.card (RelativeRoots.relRootGroup r) = 4) {z : Q} (hzZ : z ∈ center Q)
    (hz2 : orderOf z = 2) : 3 ≤ CFSG.pRank 2 Q := by
  set η := e.toMonoidHom.comp (QuotientGroup.mk' (center Q)) with hηdef
  have hη : Function.Surjective η := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : η.ker = center Q := ker_quotientMap e
  have h2 : IsPGroup 2 η.ker := hker ▸ isPGroup_center_of_pPrimeCore_eq_bot hO
  obtain ⟨F, hFmap, hFker, hFsup⟩ :=
    TwistedE6LeviCover.exists_split_relRootGroup η hη hker.le h2 hr
  obtain ⟨hWc, hW2⟩ := RelativeRoots.relRootGroup_elementary hr
  have hFtriv : ∀ f ∈ F, η f = 1 → f = 1 := fun f hf h1 => by
    have hmem : f ∈ F ⊓ η.ker := ⟨hf, h1⟩
    rw [hFker] at hmem
    exact hmem
  have hFW : ∀ f ∈ F, η f ∈ (RelativeRoots.relRootGroup r).comap stdGroup.subtype :=
    fun f hf => hFmap ▸ ⟨f, hf, rfl⟩
  have hFc : ∀ f ∈ F, ∀ f' ∈ F, f * f' = f' * f := fun f hf f' hf' => by
    have hc : η (f * f' * (f' * f)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, mul_inv_eq_one]
      exact Subtype.ext (hWc _ (Subgroup.mem_comap.mp (hFW f hf)) _
        (Subgroup.mem_comap.mp (hFW f' hf')))
    have := hFtriv _ (mul_mem (mul_mem hf hf') (inv_mem (mul_mem hf' hf))) hc
    exact mul_inv_eq_one.mp this
  have hF2 : ∀ f ∈ F, f * f = 1 := fun f hf =>
    hFtriv _ (mul_mem hf hf) (by
      rw [map_mul]; exact Subtype.ext (hW2 _ (Subgroup.mem_comap.mp (hFW f hf))))
  have hlift : ∀ y : Q, η y ∈ (RelativeRoots.relRootGroup r).comap stdGroup.subtype →
      ∃ f ∈ F, ∃ c ∈ η.ker, f * c = y := fun y hy => by
    have hy' : y ∈ ((RelativeRoots.relRootGroup r).comap stdGroup.subtype).comap η := hy
    rw [hFsup] at hy'
    exact Subgroup.mem_sup_of_normal_right.mp hy'
  refine three_le_pRank_of_lifts hη hker (W := (RelativeRoots.relRootGroup r).comap
    stdGroup.subtype) ?_ (fun y y' hy hy' => ?_) (fun y hy => ?_) hzZ hz2
  · rw [LieType.Chevalley.TwistedE6FieldTwoCover.card_relG, h4]
  · obtain ⟨f, hf, c, hc, rfl⟩ := hlift y hy
    obtain ⟨f', hf', c', hc', rfl⟩ := hlift y' hy'
    have hcZ := mem_center_iff.mp (hker.le hc)
    have hc'Z := mem_center_iff.mp (hker.le hc')
    have hff' : Commute f f' := hFc f hf f' hf'
    exact ((hff'.mul_right (hc'Z f : Commute f c')).mul_left
      ((show Commute c f' from (hcZ f').symm).mul_right (hc'Z c : Commute c c'))).eq
  · obtain ⟨f, hf, c, hc, rfl⟩ := hlift y hy
    refine ⟨c, hc, ?_⟩
    have hcf : Commute f c := mem_center_iff.mp (hker.le hc) f
    rw [hcf.mul_pow, pow_two f, hF2 f hf, one_mul]

theorem three_le_pRank_of_twistedE6Two
    (hO : pPrimeCore 2 Q = ⊥) (hL : LieModel (Q ⧸ center Q) .twistedE6 0 2 1) {z : Q}
    (hzZ : z ∈ center Q) (hz2 : orderOf z = 2) : 3 ≤ CFSG.pRank 2 Q := by
  obtain ⟨e⟩ := (EvenSmallLie.TwoE6.lieModel_twistedE6_two_iff _).1 hL
  have hr := CFSG.Blueprint.Chevalley.isRoot_single CFSG.Blueprint.Chevalley.Tag.F4
    ⟨2, by decide⟩
  refine three_le_pRank_of_relRootGroup hO e hr ?_ hzZ hz2
  have hfe : LieType.Chevalley.f4Euclid
      (Pi.single (⟨2, by decide⟩ : Fin CFSG.Blueprint.Chevalley.Tag.F4.rank) 1) =
        ![0, 0, 0, 1] := by
    unfold LieType.Chevalley.f4Euclid
    rw [Finset.sum_eq_single ⟨2, by decide⟩ (fun b _ hb => by rw [Pi.single_eq_of_ne hb]; simp)
      (by simp)]
    simp only [Pi.single_eq_same, Int.cast_one, one_smul]
    rfl
  rw [RelativeRoots.card_relRootGroup hr, hfe, ite_eq_right_iff.mpr]
  intro h
  simp [dotProduct, Fin.sum_univ_four] at h

theorem three_le_pRank_of_O82
    (hQ : IsQuasisimple Q)
    (hL : LieModel (Q ⧸ center Q) .POmegaPlus 4 2 1)
    (hrow : GriessAll.GriessRow (Q ⧸ center Q) .POmegaPlus 4 2 1) {z : Q} (hzZ : z ∈ center Q)
    (hz2 : orderOf z = 2) : 3 ≤ CFSG.pRank 2 Q := by
  have hdvd := card_center_dvd_of_griessRow hQ hrow
  have hval : (genericOrders .POmegaPlus 4 2 1).1 * (genericOrders .POmegaPlus 4 2 1).2 *
      ((exceptionalOrders .POmegaPlus 4 2 1).1 * (exceptionalOrders .POmegaPlus 4 2 1).2) = 4 := by
    have hg : genericOrders .POmegaPlus 4 2 1 = (1, 1) := by
      simp only [genericOrders, show Even (2 ^ 1) from ⟨1, rfl⟩, ↓reduceIte]
    rw [hg]
    decide
  rw [hval] at hdvd
  have hz1 : z ≠ 1 := by rintro rfl; rw [orderOf_one] at hz2; omega
  have : Nontrivial (center Q) := ⟨⟨⟨z, hzZ⟩, 1, fun h => hz1 (congrArg Subtype.val h)⟩⟩
  have h2le : 2 ≤ Nat.card (center Q) := Finite.one_lt_card
  have hcases : Nat.card (center Q) = 2 ∨ Nat.card (center Q) = 4 := by
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : Nat.card (center Q)
    · exact Or.inl rfl
    · exact absurd hdvd (by norm_num)
    · exact Or.inr rfl
  rcases hcases with hZ2 | hZ4
  ·
    obtain ⟨θ, -⟩ := EvenSmallLie.OmegaEight.Weyl.exists_mulEquiv_wPlus Q
      hQ.1.commutator_eq_top hZ2 hL
    have hP := EvenSmallLie.OmegaEight.Weyl.weylPackage
    set A : Subgroup ↥EvenSmallLie.OmegaEight.Weyl.wPlus :=
      EvenSmallLie.OmegaEight.Weyl.eSub.subgroupOf EvenSmallLie.OmegaEight.Weyl.wPlus
    have hA2 : ∀ a ∈ A, a ^ 2 = 1 := fun a ha => Subtype.ext (by
      rw [Subgroup.coe_pow, pow_two]
      exact hP.abelian.sq_eSub _ ha)
    have hA : CFSG.IsElementaryAbelian 2 A :=
      { toIsMulCommutative :=
          ⟨⟨fun a b => Subtype.ext (DoubleCoverLift.mul_comm_of_sq_eq_one hA2 a.2 b.2)⟩⟩
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
          Subtype.ext (hA2 a a.2) }
    have hcard : Nat.card A = 2 ^ 7 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP.coords.eSub_le).toEquiv]
      exact hP.abelian.card_eSub
    set A' : Subgroup Q := A.map θ.symm.toMonoidHom
    have hA'2 : ∀ a ∈ A', a ^ 2 = 1 := by
      rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hA2 a ha, map_one]
    have hA' : CFSG.IsElementaryAbelian 2 A' :=
      { toIsMulCommutative :=
          ⟨⟨fun a b => Subtype.ext (DoubleCoverLift.mul_comm_of_sq_eq_one hA'2 a.2 b.2)⟩⟩
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
          Subtype.ext (hA'2 a a.2) }
    have hcard' : Nat.card A' = 2 ^ 7 := by
      rw [Subgroup.card_map_of_injective θ.symm.injective, hcard]
    exact TransitiveLift.le_pRank_of_card hA' (k := 3) (by rw [hcard']; norm_num)
  ·
    obtain ⟨θ, hθ⟩ := RankTwoClassical.ExcO8E.exists_mulEquiv_eFib
      (RankTwoClassical.ExcO8E.isPerfect_eFib' Hq4.censusChecks_e480) hQ.1
      hZ4 hL
    have hmem : ∀ a b : Bool, θ.symm (RankTwoClassical.ExcO8E.zElt a b) ∈ center Q := by
      intro a b
      have h := RankTwoClassical.ExcO8E.zElt_mem_ker a b
      rw [← hθ] at h
      obtain ⟨y, hy, hyθ⟩ := h
      rw [← hyθ]
      simpa using hy
    have hzP : EvenSmallLie.OmegaEight.Weyl.zPlus * EvenSmallLie.OmegaEight.Weyl.zPlus = 1 :=
      Subtype.ext EvenSmallLie.OmegaEight.Weyl.zPerm_mul_self
    have hz00 : RankTwoClassical.ExcO8E.zElt false false = 1 := by
      apply Subtype.ext; apply Prod.ext <;> simp [RankTwoClassical.ExcO8E.zElt]
    have hord : ∀ a b : Bool, (a, b) ≠ (false, false) →
        orderOf (θ.symm (RankTwoClassical.ExcO8E.zElt a b)) = 2 := by
      intro a b hab
      rw [MulEquiv.orderOf_eq]
      refine orderOf_eq_prime ?_ ?_
      · apply Subtype.ext; apply Prod.ext <;> cases a <;> cases b <;>
          simp [RankTwoClassical.ExcO8E.zElt, pow_two, hzP]
      · intro h
        exact hab (RankTwoClassical.ExcO8E.zElt_injective (a₁ := (a, b)) (a₂ := (false, false))
          (h.trans hz00.symm))
    have hne : θ.symm (RankTwoClassical.ExcO8E.zElt true false) ≠
        θ.symm (RankTwoClassical.ExcO8E.zElt false true) := fun h => by
      have := RankTwoClassical.ExcO8E.zElt_injective (a₁ := (true, false)) (a₂ := (false, true))
        (θ.symm.injective h)
      simp at this
    obtain ⟨⟨x, hx, hxZ⟩, -⟩ := Hq4.centralFour_O82 hQ hL (hord true false (by decide))
      (hord false true (by decide)) hne (hmem true false) (hmem false true)
    exact three_le_pRank_of_noncentral_involution hx hxZ (hord true false (by decide))
      (hord false true (by decide)) hne (hmem true false) (hmem false true)

end CFSG.ComponentClassification.Sol76T13.R12.Pcls
