module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.UnitaryKernelsRootCenter
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.PointKernelRootProductRoot

public section

namespace CFSG.ProperTwoGeneratedCore.UnitaryKernels

open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.ProperTwoGeneratedCore.RootCenter
open CFSG.ProperTwoGeneratedCore.RankOnePair

universe u

variable {G : Type u} [Group G]

structure UnitaryKernelRootData (H : Subgroup G) (z w : G) (U R : Subgroup G) (q : ℕ) :
    Prop where
  le : R ≤ localInvolutionPointHull z w ⊓ H
  pow_two : ∀ y ∈ R, ∃ k : ℕ, y ^ 2 ^ k = 1
  two_mem : ∀ y ∈ localInvolutionPointHull z w, y ∈ H → (∃ k : ℕ, y ^ 2 ^ k = 1) → y ∈ R
  card : Nat.card R = q ^ 3
  mem_center : ∀ x, x ∈ U ↔ x ∈ R ∧ ∀ y ∈ R, x * y = y * x
  sq_mem : ∀ x ∈ R, x ^ 2 ∈ U
  inv_mem : ∀ x ∈ R, x ^ 2 = 1 → x ∈ U
  inter_centralizer : ∀ x ∈ U,
    x ∈ Subgroup.centralizer (localInvolutionPointHull z w : Set G) → x = 1
  aut : ∀ x : Subgroup.centralizer ({w} : Set G), (x : G) ∈ H →
    (∀ y ∈ U, (x : G) * y = y * x) → (x : G) ^ 2 ∈ U →
    (∃ r : Subgroup.centralizer ({w} : Set G), (r : G) ∈ R ∧
      originalCentralizerHullQuotientConjugation z w x =
        originalCentralizerHullQuotientConjugation z w r) ∨
      originalCentralizerHullQuotientConjugation z w x ^ 2 = 1
  fix : ∀ Y : Subgroup G, U ≤ Y → (∃ a ∈ R, ∀ b ∈ R, b ∈ Y ∨ a⁻¹ * b ∈ Y) →
    ∀ x : Subgroup.centralizer ({w} : Set G), (x : G) ∈ H →
      (∀ y ∈ U, (x : G) * y = y * x) → (∀ y ∈ R, y ∈ Y → (x : G) * y = y * x) →
      ∃ y : Subgroup.centralizer ({w} : Set G), (y : G) ∈ U ∧
        originalCentralizerHullQuotientConjugation z w x =
          originalCentralizerHullQuotientConjugation z w y
  solvable : ∃ A : Subgroup (MulAut (hullQuotient (localInvolutionPointHull z w))),
    Group.IsSolvable A ∧ ∀ x : Subgroup.centralizer ({w} : Set G), (x : G) ∈ H →
      (∀ y ∈ U, (x : G) * y = y * x) → originalCentralizerHullQuotientConjugation z w x ∈ A

variable [Finite G]

theorem unitaryKernelRootData_of_borel {H : Subgroup G} {z w : G} {U : Subgroup G} {q : ℕ}
    (hcentral : CFSG.oddCore (localInvolutionPointHull z w) ≤
      Subgroup.center (localInvolutionPointHull z w))
    (hodd : Odd (Nat.card (CFSG.oddCore (localInvolutionPointHull z w))))
    (hborel : IsBorelSubgroup ((H.subgroupOf (localInvolutionPointHull z w)).map
      (QuotientGroup.mk' (CFSG.oddCore (localInvolutionPointHull z w)))))
    (horbit : Odd (Nat.card (numeratorRightOrbit H (localInvolutionPointHull z w)
      (rightCosetMk H 1))))
    (hUL : U ≤ localInvolutionPointHull z w)
    (hUset : (U : Set G) = {1} ∪ {x : G | x ∈ localInvolutionPointHull z w ∧
      x ∈ H ⊓ Subgroup.centralizer ({w} : Set G) ∧ orderOf x = 2})
    (hroot : ∀ S : Sylow 2 (hullQuotient (localInvolutionPointHull z w)),
      Nat.card (S : Subgroup (hullQuotient (localInvolutionPointHull z w))) = q ^ 3 ∧
        UnitaryRootCenterData (S : Subgroup (hullQuotient (localInvolutionPointHull z w)))
          ((CFSG.omega₁ (G := (S : Subgroup (hullQuotient (localInvolutionPointHull z w))))
            (p := 2)).map
            (S : Subgroup (hullQuotient (localInvolutionPointHull z w))).subtype))
    (R : Sylow 2 ↥(localInvolutionPointHull z w ⊓ H)) :
    UnitaryKernelRootData H z w U
      ((R : Subgroup _).map (localInvolutionPointHull z w ⊓ H).subtype) q := by
  obtain ⟨htwo, hinj, Q, hQ, hQcard⟩ := hull_point_sylow_root hcentral hodd hborel horbit R
  obtain ⟨hcardQ, hRC⟩ := hroot Q
  have hRgLH : (R : Subgroup _).map (localInvolutionPointHull z w ⊓ H).subtype ≤
      localInvolutionPointHull z w ⊓ H := Subgroup.map_subtype_le _
  have hRgpow : ∀ y ∈ (R : Subgroup _).map (localInvolutionPointHull z w ⊓ H).subtype,
      ∃ k : ℕ, y ^ 2 ^ k = 1 := fun y hy => pow_two_pow_of_mem_sylow_map R hy
  have hRgcard : Nat.card ((R : Subgroup _).map (localInvolutionPointHull z w ⊓ H).subtype) =
      Nat.card R := Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
  rw [← hRgcard] at hQcard
  generalize (R : Subgroup _).map (localInvolutionPointHull z w ⊓ H).subtype = Rg at *
  have hLM : localInvolutionPointHull z w ≤ Subgroup.centralizer ({w} : Set G) :=
    localInvolutionPointHull_le_centralizer z w
  have hUmem : ∀ x ∈ U, x ^ 2 = 1 ∧ x ∈ H := by
    intro x hx
    rw [← SetLike.mem_coe, hUset] at hx
    rcases hx with hx | ⟨-, ⟨hxH, -⟩, hx2⟩
    · rw [Set.mem_singleton_iff.mp hx]
      exact ⟨one_pow 2, H.one_mem⟩
    · exact ⟨by rw [← hx2]; exact pow_orderOf_eq_one x, hxH⟩
  have hURg : U ≤ Rg := fun x hx =>
    htwo x (hUL hx) (hUmem x hx).2 ⟨1, by rw [pow_one]; exact (hUmem x hx).1⟩
  have hΩ : (CFSG.omega₁ (G := (Q : Subgroup (hullQuotient (localInvolutionPointHull z w))))
      (p := 2)).map (Q : Subgroup (hullQuotient (localInvolutionPointHull z w))).subtype =
      hullImage (localInvolutionPointHull z w) U := by
    rw [CFSG.ShultStronglyClosedTI.SuzukiLayerKernel.map_omega₁_subtype]
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro g ⟨hgQ, hg2⟩
      rw [hQ] at hgQ
      obtain ⟨x, hx, rfl⟩ := hgQ
      have hxRg : (x : G) ∈ Rg := Subgroup.mem_subgroupOf.mp hx
      have hx2 : x ^ 2 = 1 := hinj (x ^ 2) 1 (Rg.pow_mem hxRg 2) Rg.one_mem
        (by rw [map_pow, hg2, map_one])
      have hxU : (x : G) ∈ U := by
        by_cases h1 : (x : G) = 1
        · rw [h1]
          exact U.one_mem
        · rw [← SetLike.mem_coe, hUset]
          exact Or.inr ⟨x.2, ⟨(hRgLH hxRg).2, hLM x.2⟩,
            orderOf_eq_prime (congrArg Subtype.val hx2) h1⟩
      exact mk_mem_hullImage _ hxU
    · rintro _ ⟨x, hx, rfl⟩
      have hxU : (x : G) ∈ U := Subgroup.mem_subgroupOf.mp hx
      refine Subgroup.subset_closure ⟨?_, ?_⟩
      · rw [hQ]
        exact mk_mem_hullImage _ (hURg hxU)
      · rw [← map_pow, show x ^ 2 = 1 from Subtype.ext (hUmem _ hxU).1, map_one]
  rw [hΩ, hQ] at hRC
  have hmapx : ∀ x : Subgroup.centralizer ({w} : Set G), (x : G) ∈ H →
      (hullImage (localInvolutionPointHull z w) Rg).map
          (originalCentralizerHullQuotientConjugation z w x).toMonoidHom =
        hullImage (localInvolutionPointHull z w) Rg := by
    intro x hxH
    refine quotConj_map_hullImage z w x (hRgLH.trans inf_le_left) (fun y hy => ?_)
      (fun y hy => ?_)
    · obtain ⟨k, hk⟩ := hRgpow y hy
      exact htwo _ (centralizer_conj_mem_hull z w x.2 (hRgLH hy).1)
        (H.mul_mem (H.mul_mem hxH (hRgLH hy).2) (H.inv_mem hxH))
        ⟨k, conj_pow_two_pow_eq_one hk⟩
    · obtain ⟨k, hk⟩ := hRgpow y hy
      have hconj := centralizer_conj_mem_hull z w (Subgroup.inv_mem _ x.2) (hRgLH hy).1
      have hpow := conj_pow_two_pow_eq_one (a := (x : G)⁻¹) hk
      rw [inv_inv] at hconj hpow
      exact htwo _ hconj (H.mul_mem (H.mul_mem (H.inv_mem hxH) (hRgLH hy).2) hxH) ⟨k, hpow⟩
  have hmemA : ∀ x : Subgroup.centralizer ({w} : Set G), (x : G) ∈ H →
      (∀ y ∈ U, (x : G) * y = y * x) →
      originalCentralizerHullQuotientConjugation z w x ∈
        rootCenterAut (hullImage (localInvolutionPointHull z w) Rg)
          (hullImage (localInvolutionPointHull z w) U) := fun x hxH hxU =>
    mem_rootCenterAut.mpr ⟨hmapx x hxH, quotConj_apply_hullImage z w x hxU⟩
  refine ⟨hRgLH, hRgpow, htwo, hQcard.symm.trans hcardQ, fun x => ⟨fun hxU => ?_, fun hx => ?_⟩,
    fun x hxRg => ?_, fun x hxRg hx2 => ?_, fun x hxU hxC => ?_, fun x hxH hxU hx2 => ?_,
    fun Y hUY ⟨a, haR, hab⟩ x hxH hxU hxY => ?_, ⟨_, hRC.solvable, hmemA⟩⟩
  · refine ⟨hURg hxU, fun y hy => ?_⟩
    have hc := ((hRC.mem_iff _).mp (mk_mem_hullImage (localInvolutionPointHull z w)
      (y := ⟨x, hUL hxU⟩) hxU)).2 _
      (mk_mem_hullImage (localInvolutionPointHull z w) (y := ⟨y, (hRgLH hy).1⟩) hy)
    rw [← map_mul, ← map_mul] at hc
    exact congrArg Subtype.val
      (hinj _ _ (Rg.mul_mem (hURg hxU) hy) (Rg.mul_mem hy (hURg hxU)) hc)
  · obtain ⟨hxRg, hxc⟩ := hx
    have hcen : ∀ a ∈ hullImage (localInvolutionPointHull z w) Rg,
        QuotientGroup.mk' _ ⟨x, (hRgLH hxRg).1⟩ * a =
          a * QuotientGroup.mk' _ ⟨x, (hRgLH hxRg).1⟩ := by
      rintro _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hxc y (Subgroup.mem_subgroupOf.mp hy))
    obtain ⟨y, hy, hyx⟩ := (hRC.mem_iff _).mpr ⟨mk_mem_hullImage _ hxRg, hcen⟩
    have hyx' : (y : G) = x := congrArg Subtype.val
      (hinj y ⟨x, (hRgLH hxRg).1⟩ (hURg (Subgroup.mem_subgroupOf.mp hy)) hxRg hyx)
    rw [← hyx']
    exact Subgroup.mem_subgroupOf.mp hy
  · have hxL := (hRgLH hxRg).1
    obtain ⟨y, hy, hyx⟩ := hRC.sq_mem _ (mk_mem_hullImage _ (y := ⟨x, hxL⟩) hxRg)
    rw [← map_pow] at hyx
    have hyx' : (y : G) = x ^ 2 := congrArg Subtype.val
      (hinj y (⟨x, hxL⟩ ^ 2) (hURg (Subgroup.mem_subgroupOf.mp hy)) (Rg.pow_mem hxRg 2) hyx)
    rw [← hyx']
    exact Subgroup.mem_subgroupOf.mp hy
  · by_cases h1 : x = 1
    · rw [h1]
      exact U.one_mem
    · rw [← SetLike.mem_coe, hUset]
      exact Or.inr ⟨(hRgLH hxRg).1, ⟨(hRgLH hxRg).2, hLM (hRgLH hxRg).1⟩,
        orderOf_eq_prime hx2 h1⟩
  · have hxL := hUL hxU
    have hconj : MulAut.conj (QuotientGroup.mk' (CFSG.oddCore (localInvolutionPointHull z w))
        ⟨x, hxL⟩) = MulAut.conj 1 := by
      rw [map_one]
      apply MulEquiv.ext
      intro a
      induction a using QuotientGroup.induction_on with
      | H l =>
        rw [MulAut.conj_apply, MulAut.one_apply]
        change QuotientGroup.mk' (CFSG.oddCore (localInvolutionPointHull z w)) ⟨x, hxL⟩ *
          QuotientGroup.mk' _ l *
          (QuotientGroup.mk' (CFSG.oddCore (localInvolutionPointHull z w)) ⟨x, hxL⟩)⁻¹ =
          QuotientGroup.mk' _ l
        rw [← map_inv, ← map_mul, ← map_mul]
        congr 1
        apply Subtype.ext
        change x * l * x⁻¹ = l
        rw [← Subgroup.mem_centralizer_iff.mp hxC l l.2, mul_inv_cancel_right]
    have h1 := hRC.injOn_conj (mk_mem_hullImage _ (y := ⟨x, hxL⟩) (hURg hxU)) (one_mem _) hconj
    exact congrArg Subtype.val (hinj ⟨x, hxL⟩ 1 (hURg hxU) Rg.one_mem (by rw [h1, map_one]))
  · have hx2L : ((x ^ 2 : Subgroup.centralizer ({w} : Set G)) : G) ∈
        localInvolutionPointHull z w := hUL hx2
    have hγ2 : originalCentralizerHullQuotientConjugation z w x ^ 2 ∈
        (hullImage (localInvolutionPointHull z w) U).map MulAut.conj := by
      rw [← map_pow, quotConj_of_mem_hull z w (x ^ 2) hx2L]
      exact Subgroup.mem_map_of_mem _ (mk_mem_hullImage _ (y := ⟨_, hx2L⟩) hx2)
    rcases hRC.aut_sq _ (hmemA x hxH hxU) hγ2 with hR | h1
    · obtain ⟨_, ⟨r, hr, rfl⟩, hγ⟩ := hR
      refine Or.inl ⟨⟨r, hLM r.2⟩, Subgroup.mem_subgroupOf.mp hr, ?_⟩
      rw [quotConj_of_mem_hull z w ⟨r, hLM r.2⟩ r.2]
      exact hγ.symm
    · exact Or.inr h1
  · have hU₀ : hullImage (localInvolutionPointHull z w) U ≤
        hullImage (localInvolutionPointHull z w) (Rg ⊓ Y) := hullImage_mono _ (le_inf hURg hUY)
    have h₀R : hullImage (localInvolutionPointHull z w) (Rg ⊓ Y) ≤
        hullImage (localInvolutionPointHull z w) Rg := hullImage_mono _ inf_le_left
    have hidx : (hullImage (localInvolutionPointHull z w) (Rg ⊓ Y)).relIndex
        (hullImage (localInvolutionPointHull z w) Rg) ≤ 2 := by
      refine relIndex_le_two_of_forall (a := QuotientGroup.mk' _ ⟨a, (hRgLH haR).1⟩)
        (mk_mem_hullImage _ haR) ?_
      rintro _ ⟨b, hb, rfl⟩
      have hbRg := Subgroup.mem_subgroupOf.mp hb
      rcases hab b hbRg with hbY | hbY
      · exact Or.inl (mk_mem_hullImage _ ⟨hbRg, hbY⟩)
      · right
        rw [← map_inv, ← map_mul]
        exact mk_mem_hullImage _ (y := (⟨a, (hRgLH haR).1⟩ : localInvolutionPointHull z w)⁻¹ * b)
          ⟨Rg.mul_mem (Rg.inv_mem haR) hbRg, hbY⟩
    have hfix₀ := quotConj_apply_hullImage z w x (Y := Rg ⊓ Y) (fun y hy => hxY y hy.1 hy.2)
    obtain ⟨_, ⟨y, hy, rfl⟩, hγ⟩ := (Set.ext_iff.mp (hRC.fix_eq _ hU₀ h₀R hidx) _).mp
      ⟨hmemA x hxH hxU, hfix₀⟩
    refine ⟨⟨y, hLM y.2⟩, Subgroup.mem_subgroupOf.mp hy, ?_⟩
    rw [quotConj_of_mem_hull z w ⟨y, hLM y.2⟩ y.2]
    exact hγ.symm

end CFSG.ProperTwoGeneratedCore.UnitaryKernels
