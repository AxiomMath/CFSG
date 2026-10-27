module

public import CFSG.RankThree.PartOne.KLAY.F4
public import CFSG.LieType.Ree.LargeReeInvolutionFusionCoords

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.ReeSec8

open Subgroup
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.LieType.Ree.LargeReeCover (f4i pairedTorusHom pairedTorusHom_apply torusPair)

open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootChar rootDiagUnit
  root_diagonal_conjugation)

open CFSG.RankThree.Chevalley (simpleRootSL2_injective_of_charTwo)

open CFSG.RankThree.PartOne.KLAY (f4S03 isRoot_of_mem_f4S03 neg_mem_f4S03 rhoM coe_rhoM f4Phi
  reeGamma_inf_rootSpan_eq f4_kernel_sub rootChar_eq_torusWeight torusExp_combo coord_f4S03
  commute_rhoM exists_of_mem_rootSpan_f4S03 simpleRootSL2_mem_rootSpan_f4S03
  finiteReeAut_rhoM_zero finiteReeAut_rhoM_three rootSpan_le_centralizer_of_char_one
  rootChar_single)

open scoped Pointwise

section Weyl

variable {K : Type} [Field K] [CharP K F4.prime]

theorem canonicalRep_fixedOrbit_mul_self
    (j : Fin F4.fixedOrbitCount) :
    canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j) *
      canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j) = 1 := by
  have : CharP K 2 := ‹CharP K F4.prime›
  have h := CFSG.SectionRank.LargeRee.nrep_mul_charTwo K (F4.fixedOrbitElement j)
    (F4.fixedOrbitElement j)
  rw [fixedOrbitElement_mul_self, nrep_one] at h
  exact (congrArg Subtype.val h).symm

end Weyl

section Torus

variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]

theorem weylOne_conj_torusOne
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (u : Kˣ) :
    canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨0, by decide⟩) *
        pairedTorusHom a (f4i 0) (f4i 3) u *
          (canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨0, by decide⟩))⁻¹ =
      (pairedTorusHom a (f4i 0) (f4i 3) u)⁻¹ := by
  have h := congrArg Subtype.val (CFSG.SectionRank.LargeRee.torus_reflections (a := a) hK u).1
  have hn : (nrep F4.tag K (F4.blockElt (CFSG.SectionRank.LargeRee.fi 0)) : ModGL F4.tag K) =
      canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨0, by decide⟩) := by
    change canonicalRep (coxeterSystem F4.tag) K _ = _
    rw [blockElt_eq]
    rfl
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hn] at h
  rw [← rankOneTorusPair_left, LargeReeCover.torusPair_eq_reeTorus]
  simp only [CFSG.SectionRank.LargeRee.reeTorus_one, mul_one]
  exact h

theorem weylTwo_conj_torusTwo
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (v : Kˣ) :
    canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨1, by decide⟩) *
        pairedTorusHom a (f4i 1) (f4i 2) v *
          (canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨1, by decide⟩))⁻¹ =
      (pairedTorusHom a (f4i 1) (f4i 2) v)⁻¹ := by
  have h := congrArg Subtype.val (CFSG.SectionRank.LargeRee.torus_reflections (a := a) hK v).2.2.1
  have hn : (nrep F4.tag K (F4.blockElt (CFSG.SectionRank.LargeRee.fi 1)) : ModGL F4.tag K) =
      canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨1, by decide⟩) := by
    change canonicalRep (coxeterSystem F4.tag) K _ = _
    rw [blockElt_eq]
    rfl
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hn] at h
  rw [← rankOneTorusPair_right, LargeReeCover.torusPair_eq_reeTorus]
  simp only [CFSG.SectionRank.LargeRee.reeTorus_one, one_mul]
  exact h

theorem gConj_torusOne
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (s : Kˣ) :
    (weylTwo K * weylOne K * weylTwo K) * pairedTorusHom a (f4i 0) (f4i 3) s *
        (weylTwo K * weylOne K * weylTwo K)⁻¹ =
      torusPair a (s ^ (1 + 2 * ((2 ^ a : ℕ) : ℤ)), s ^ (2 + 4 * ((2 ^ a : ℕ) : ℤ))) := by
  have h1 := canonicalRep_conj_torusOne (a := a) hK
  have h2 := canonicalRep_conj_torusTwo (a := a) hK
  have h3 := weylOne_conj_torusOne (a := a) hK
  have h4 := weylTwo_conj_torusTwo (a := a) hK
  set θ : ℤ := ((2 ^ a : ℕ) : ℤ) with hθ
  rw [weylOne, weylTwo]
  set n₁ := canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨0, by decide⟩)
  set n₂ := canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨1, by decide⟩)
  set T₁ := pairedTorusHom (K := K) a (f4i 0) (f4i 3) with hT₁
  set T₂ := pairedTorusHom (K := K) a (f4i 1) (f4i 2) with hT₂
  have hpair : ∀ u v : Kˣ, torusPair (K := K) a (u, v) = T₁ u * T₂ v := fun _ _ => rfl
  have hq : s ^ (4 * θ + 4 * θ ^ 2) = s ^ (2 + 4 * θ) := by
    refine units_zpow_congr hK s 2 ?_
    rw [hθ]
    push_cast
    ring
  calc (n₂ * n₁ * n₂) * T₁ s * (n₂ * n₁ * n₂)⁻¹ =
        n₂ * (n₁ * (n₂ * T₁ s * n₂⁻¹) * n₁⁻¹) * n₂⁻¹ := by group
    _ = n₂ * ((n₁ * T₁ s * n₁⁻¹) * (n₁ * T₂ (s ^ (2 + 2 * θ)) * n₁⁻¹)) * n₂⁻¹ := by
        rw [h1]
        group
    _ = (n₂ * T₁ s * n₂⁻¹)⁻¹ * (n₂ * T₂ (s ^ (2 + 2 * θ)) * n₂⁻¹) *
          (n₂ * T₁ (s ^ (2 + 2 * θ)) * n₂⁻¹) := by
        rw [h3, h2]
        group
    _ = torusPair a ((s, s ^ (2 + 2 * θ))⁻¹ * (1, s ^ (2 + 2 * θ))⁻¹ *
          (s ^ (2 + 2 * θ), (s ^ (2 + 2 * θ)) ^ (2 + 2 * θ))) := by
        rw [h1, h4, h1, map_mul, map_mul, map_inv, map_inv, hpair, hpair, hpair, map_one,
          one_mul]
    _ = torusPair a (s ^ (1 + 2 * θ), s ^ (2 + 4 * θ)) := by
        rw [← hq]
        congr 1
        refine Prod.ext ?_ ?_
        · simp only [Prod.fst_mul, Prod.fst_inv, inv_one, mul_one]
          group
        · simp only [Prod.snd_mul, Prod.snd_inv]
          group

end Torus

section Descent

theorem SL2_eq_one_of_mem_center {K : Type} [Field K] [CharP K 2] {A : SL2 K}
    (hA : A ∈ center (SL2 K)) : A = 1 := by
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  simp only [Fintype.card_fin] at hr
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hr1 : (r - 1) ^ 2 = 0 := by linear_combination hr + (1 - r) * h2
  have hr' : r = 1 := sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hr1)
  apply Subtype.ext
  rw [← hrA, hr', map_one, Matrix.SpecialLinearGroup.coe_one]

theorem rootChar_neg_eq {K : Type} [Field K] (l : Fin F4.tag.rank → Kˣ)
    (v : Fin F4.tag.rank → ℤ) : rootChar l (-v) = (rootChar l v)⁻¹ := by
  simp only [rootChar, Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib]

theorem rootSpan_le_centralizer_of_eq_one {K : Type} [Field K]
    {l : Fin F4.tag.rank → Kˣ} (h0 : l (f4i 0) = 1) (h3 : l (f4i 3) = 1) :
    rootSpan F4.tag K f4S03 ≤ centralizer {rootDiagUnit F4.tag l} := by
  refine rootSpan_le_centralizer_of_char_one fun α hα => ⟨isRoot_of_mem_f4S03 hα, ?_⟩
  rcases hα with rfl | rfl | rfl | rfl
  · exact (rootChar_single l _).trans h0
  · rw [rootChar_neg_eq, rootChar_single]
    exact inv_eq_one.2 h0
  · exact (rootChar_single l _).trans h3
  · rw [rootChar_neg_eq, rootChar_single]
    exact inv_eq_one.2 h3

variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]

theorem exists_torus_mul_of_mem
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {y : ModGL F4.tag K} (hy : y ∈ F4.reeGamma K a)
    (hyTM : y ∈ (torusGroup F4.tag K : Set (ModGL F4.tag K)) *
      (rootSpan F4.tag K f4S03 : Set (ModGL F4.tag K))) :
    ∃ h ∈ F4.reeGamma K a ⊓ torusGroup F4.tag K,
      h⁻¹ * y ∈ F4.reeGamma K a ⊓ rootSpan F4.tag K f4S03 := by
  have h0 : (Pi.single (f4i 0) 1 : Fin F4.tag.rank → ℤ) ∈ f4S03 := Or.inl rfl
  have h3 : (Pi.single (f4i 3) 1 : Fin F4.tag.rank → ℤ) ∈ f4S03 := Or.inr (Or.inr (Or.inl rfl))
  obtain ⟨t, ht, m, hm, hytm⟩ := hyTM
  replace hytm : t * m = y := hytm
  subst hytm
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  have hsq : ∀ u : Kˣ, ∃ v : Kˣ, v ^ 2 = u := fun u => ⟨u ^ 2 ^ (2 * a), by
    have h1 : 2 ^ (2 * a) * 2 = Nat.card K - 1 + 1 := by
      rw [hK, Nat.sub_add_cancel Nat.one_le_two_pow, pow_succ]
    rw [← pow_mul, h1, pow_succ, CFSG.SectionRank.LargeRee.units_pow_card_sub_one, one_mul]⟩
  obtain ⟨c₀, hc₀⟩ := hsq (l (f4i 0))
  obtain ⟨c₃, hc₃⟩ := hsq (l (f4i 3))
  obtain ⟨d, hd⟩ : ∃ d, torusElt F4.tag K (f4i 0) c₀ * torusElt F4.tag K (f4i 3) c₃ = d :=
    ⟨_, rfl⟩
  have hdT : d ∈ torusGroup F4.tag K := by
    rw [← hd]
    exact mul_mem (torusElt_mem_torusGroup _ _) (torusElt_mem_torusGroup _ _)
  have hdM : d ∈ rootSpan F4.tag K f4S03 := by
    rw [← hd, ← simpleRootSL2_HSL, ← simpleRootSL2_HSL]
    exact mul_mem (simpleRootSL2_mem_rootSpan_f4S03 h0 _) (simpleRootSL2_mem_rootSpan_f4S03 h3 _)
  obtain ⟨l', hl'⟩ : ∃ l' : Fin F4.tag.rank → Kˣ, l * ((fun j => c₀ ^ F4.tag.cartan (f4i 0) j) *
      (fun j => c₃ ^ F4.tag.cartan (f4i 3) j))⁻¹ = l' := ⟨_, rfl⟩
  have ht'eq : rootDiagUnit F4.tag l * d⁻¹ = rootDiagUnit F4.tag l' := by
    rw [← hd, ← hl', torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, ← rootDiagUnit_mul,
      rootDiagUnit_inv, ← rootDiagUnit_mul]
  have e00 : F4.tag.cartan (f4i 0) (f4i 0) = 2 := by decide
  have e30 : F4.tag.cartan (f4i 3) (f4i 0) = 0 := by decide
  have e03 : F4.tag.cartan (f4i 0) (f4i 3) = 0 := by decide
  have e33 : F4.tag.cartan (f4i 3) (f4i 3) = 2 := by decide
  have hl'0 : l' (f4i 0) = 1 := by
    rw [← hl']
    simp only [Pi.mul_apply, Pi.inv_apply, e00, e30, zpow_zero, mul_one, ← hc₀]
    rw [zpow_two, sq, mul_inv_cancel]
  have hl'3 : l' (f4i 3) = 1 := by
    rw [← hl']
    simp only [Pi.mul_apply, Pi.inv_apply, e03, e33, zpow_zero, one_mul, ← hc₃]
    rw [zpow_two, sq, mul_inv_cancel]
  have hcent := rootSpan_le_centralizer_of_eq_one (K := K) hl'0 hl'3
  obtain ⟨t', ht'⟩ : ∃ t', rootDiagUnit F4.tag l' = t' := ⟨_, rfl⟩
  rw [ht'] at hcent ht'eq
  have ht'T : t' ∈ torusGroup F4.tag K := by
    rw [← ht'eq]
    exact mul_mem ht (inv_mem hdT)
  obtain ⟨m', hm'⟩ : ∃ m', d * m = m' := ⟨_, rfl⟩
  have hm'M : m' ∈ rootSpan F4.tag K f4S03 := by
    rw [← hm']
    exact mul_mem hdM hm
  have hy' : rootDiagUnit F4.tag l * m = t' * m' := by
    rw [← ht'eq, ← hm']
    group
  rw [hy'] at hy ⊢
  obtain ⟨hyA, hyF⟩ := mem_reeGamma.1 hy
  have ht'A : t' ∈ adjointGroup F4.tag K := torusGroup_le_adjointGroup F4 K ht'T
  have hm'A : m' ∈ adjointGroup F4.tag K := by
    have h := mul_mem (inv_mem ht'A) hyA
    rwa [inv_mul_cancel_left] at h
  obtain ⟨l'', hl''⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup
    (finiteReeAut_mem_torusGroup (a := a) ht'T ht'A)
  have hxM : ∀ i, Pi.single i 1 ∈ f4S03 → xUnit F4.tag K i 1 ∈ rootSpan F4.tag K f4S03 :=
    fun i hi => by
      rw [← simpleRootSL2_uSL]
      exact simpleRootSL2_mem_rootSpan_f4S03 hi _
  have hchar : ∀ i j, F4.perm i = j → Pi.single i 1 ∈ f4S03 → l'' j = 1 := by
    intro i j hij hi
    have hc : (⟨t', ht'A⟩ : adjointGroup F4.tag K) * xElement i 1 = xElement i 1 * ⟨t', ht'A⟩ :=
      Subtype.ext (mem_centralizer_singleton_iff.1 (hcent (hxM i hi))).symm
    have hc' := congrArg Subtype.val (congrArg (F4.finiteReeAut K a) hc)
    rw [map_mul, map_mul, finiteReeAut_xElement, one_pow, hij] at hc'
    change ((F4.finiteReeAut K a ⟨t', ht'A⟩ : adjointGroup F4.tag K) : ModGL F4.tag K) *
        xUnit F4.tag K j 1 = xUnit F4.tag K j 1 *
          ((F4.finiteReeAut K a ⟨t', ht'A⟩ : adjointGroup F4.tag K) : ModGL F4.tag K) at hc'
    rw [hl''] at hc'
    have h2 := (root_diagonal_conjugation F4.tag K l'').1 j 1
    rw [hc', mul_inv_cancel_right, mul_one] at h2
    have h3 : (1 : K) = (l'' j : K) := pinnedX_injective F4.tag K (Pi.single j 1)
      (by rw [pinnedX_single, pinnedX_single]; exact h2)
    exact Units.ext h3.symm
  have hl''0 : l'' (f4i 0) = 1 := hchar (f4i 3) (f4i 0) (by decide) h3
  have hl''3 : l'' (f4i 3) = 1 := hchar (f4i 0) (f4i 3) (by decide) h0
  have hFcent := rootSpan_le_centralizer_of_eq_one (K := K) hl''0 hl''3
  rw [← hl''] at hFcent
  have hFm' : ((F4.finiteReeAut K a ⟨m', hm'A⟩ : adjointGroup F4.tag K) : ModGL F4.tag K) ∈
      rootSpan F4.tag K f4S03 := by
    obtain ⟨A, B, hAB⟩ := exists_of_mem_rootSpan_f4S03 hm'M
    have e : (⟨m', hm'A⟩ : adjointGroup F4.tag K) = rhoM K largeReeI1 A * rhoM K largeReeI4 B :=
      Subtype.ext hAB
    rw [e, map_mul, finiteReeAut_rhoM_zero, finiteReeAut_rhoM_three, Subgroup.coe_mul, coe_rhoM,
      coe_rhoM]
    exact mul_mem (simpleRootSL2_mem_rootSpan_f4S03 h3 _) (simpleRootSL2_mem_rootSpan_f4S03 h0 _)
  have hFy : F4.finiteReeAut K a ⟨t', ht'A⟩ * F4.finiteReeAut K a ⟨m', hm'A⟩ =
      ⟨t', ht'A⟩ * ⟨m', hm'A⟩ := by
    rw [← map_mul]
    exact hyF
  obtain ⟨x, hx⟩ : ∃ x : ModGL F4.tag K, x =
      t'⁻¹ * ((F4.finiteReeAut K a ⟨t', ht'A⟩ : adjointGroup F4.tag K) : ModGL F4.tag K) :=
    ⟨_, rfl⟩
  have hx' : x =
      m' * ((F4.finiteReeAut K a ⟨m', hm'A⟩ : adjointGroup F4.tag K) : ModGL F4.tag K)⁻¹ := by
    have hFy' := congrArg Subtype.val hFy
    simp only [Subgroup.coe_mul] at hFy'
    rw [hx]
    calc t'⁻¹ * ((F4.finiteReeAut K a ⟨t', ht'A⟩ : adjointGroup F4.tag K) : ModGL F4.tag K) =
        t'⁻¹ * (((F4.finiteReeAut K a ⟨t', ht'A⟩ : adjointGroup F4.tag K) : ModGL F4.tag K) *
          ((F4.finiteReeAut K a ⟨m', hm'A⟩ : adjointGroup F4.tag K) : ModGL F4.tag K)) *
            ((F4.finiteReeAut K a ⟨m', hm'A⟩ : adjointGroup F4.tag K) : ModGL F4.tag K)⁻¹ := by
          group
      _ = m' * ((F4.finiteReeAut K a ⟨m', hm'A⟩ : adjointGroup F4.tag K) : ModGL F4.tag K)⁻¹ := by
        rw [hFy']
        group
  have hxM' : x ∈ rootSpan F4.tag K f4S03 := by
    rw [hx']
    exact mul_mem hm'M (inv_mem hFm')
  have hxC : ∀ z ∈ rootSpan F4.tag K f4S03, x * z = z * x := by
    intro z hz
    have h1 : Commute z t' := mem_centralizer_singleton_iff.1 (hcent hz)
    have h2 : Commute z ((F4.finiteReeAut K a ⟨t', ht'A⟩ : adjointGroup F4.tag K) :
      ModGL F4.tag K) := mem_centralizer_singleton_iff.1 (hFcent hz)
    rw [hx]
    exact (h1.inv_right.mul_right h2).symm.eq
  have hx1 : x = 1 := by
    have : CharP K 2 := ‹CharP K F4.prime›
    obtain ⟨A, B, hAB⟩ := exists_of_mem_rootSpan_f4S03 hxM'
    have hcomm := fun (X : SL2 K) (Y : SL2 K) =>
      congrArg Subtype.val (commute_rhoM (K := K) X Y).eq
    simp only [Subgroup.coe_mul, coe_rhoM] at hcomm
    have hA : A ∈ center (SL2 K) := by
      refine Subgroup.mem_center_iff.2 fun X => ?_
      have h := hxC _ (simpleRootSL2_mem_rootSpan_f4S03 (i := largeReeI1) h0 X)
      rw [hAB] at h
      apply simpleRootSL2_injective_of_charTwo largeReeI1
      rw [map_mul, map_mul]
      have h' : simpleRootSL2 F4.tag K largeReeI1 A * simpleRootSL2 F4.tag K largeReeI1 X *
          simpleRootSL2 F4.tag K largeReeI4 B = simpleRootSL2 F4.tag K largeReeI1 X *
            simpleRootSL2 F4.tag K largeReeI1 A * simpleRootSL2 F4.tag K largeReeI4 B := by
        calc _ = simpleRootSL2 F4.tag K largeReeI1 A * (simpleRootSL2 F4.tag K largeReeI1 X *
              simpleRootSL2 F4.tag K largeReeI4 B) := by group
          _ = simpleRootSL2 F4.tag K largeReeI1 A * simpleRootSL2 F4.tag K largeReeI4 B *
              simpleRootSL2 F4.tag K largeReeI1 X := by rw [hcomm X B]; group
          _ = _ := by rw [h]; group
      exact (mul_right_cancel h').symm
    have hB : B ∈ center (SL2 K) := by
      refine Subgroup.mem_center_iff.2 fun X => ?_
      have h := hxC _ (simpleRootSL2_mem_rootSpan_f4S03 (i := largeReeI4) h3 X)
      rw [hAB] at h
      apply simpleRootSL2_injective_of_charTwo largeReeI4
      rw [map_mul, map_mul]
      have h' : simpleRootSL2 F4.tag K largeReeI1 A * (simpleRootSL2 F4.tag K largeReeI4 X *
          simpleRootSL2 F4.tag K largeReeI4 B) = simpleRootSL2 F4.tag K largeReeI1 A *
            (simpleRootSL2 F4.tag K largeReeI4 B * simpleRootSL2 F4.tag K largeReeI4 X) := by
        calc _ = simpleRootSL2 F4.tag K largeReeI4 X * simpleRootSL2 F4.tag K largeReeI1 A *
              simpleRootSL2 F4.tag K largeReeI4 B := by rw [← hcomm A X]; group
          _ = _ := by rw [mul_assoc, ← h]; group
      exact mul_left_cancel h'
    rw [hAB, SL2_eq_one_of_mem_center hA, SL2_eq_one_of_mem_center hB, map_one, map_one,
      one_mul]
  have hFt : F4.finiteReeAut K a ⟨t', ht'A⟩ = ⟨t', ht'A⟩ := by
    refine Subtype.ext ?_
    have h := hx1
    rw [hx, inv_mul_eq_one] at h
    exact h.symm
  have ht'Γ : t' ∈ F4.reeGamma K a := mem_reeGamma.2 ⟨ht'A, hFt⟩
  refine ⟨t', ⟨ht'Γ, ht'T⟩, ?_⟩
  rw [inv_mul_cancel_left]
  refine ⟨?_, hm'M⟩
  have h := mul_mem (inv_mem ht'Γ) hy
  rwa [inv_mul_cancel_left] at h

end Descent

section Cent

variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]

theorem reeGamma_inf_rootSpan_eq_rankOneGroupOne
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    F4.reeGamma K a ⊓ rootSpan F4.tag K f4S03 = rankOneGroupOne K a := by
  rw [← reeGamma_inf_rootSpan_eq hK, rankOneGroupOne_eq_range hK]
  ext x
  constructor
  · rintro ⟨_, ⟨A, rfl⟩, rfl⟩
    exact ⟨A, rfl⟩
  · rintro ⟨A, rfl⟩
    exact ⟨f4Phi hK A, ⟨A, rfl⟩, rfl⟩

theorem cent_torusPair
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hpq : p ∣ 2 ^ (2 * a + 1) - 1) {w : Kˣ} (hw : IsPrimitiveRoot w p) :
    (∀ r ∈ rankOneGroupOne K a, r * torusPair a (w, w ^ 2) = torusPair a (w, w ^ 2) * r) ∧
    ∀ y ∈ F4.reeGamma K a, y * torusPair a (w, w ^ 2) = torusPair a (w, w ^ 2) * y →
      ∃ h ∈ F4.reeGamma K a ⊓ torusGroup F4.tag K, h⁻¹ * y ∈ rankOneGroupOne K a := by
  have hT : torusPair (K := K) a (w, w ^ 2) ∈ torusGroup F4.tag K := by
    rw [LargeReeCover.torusPair_apply]
    exact mul_mem (mul_mem (torusElt_mem_torusGroup _ _) (torusElt_mem_torusGroup _ _))
      (mul_mem (torusElt_mem_torusGroup _ _) (torusElt_mem_torusGroup _ _))
  obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hT
  have hA' : ∀ β : Fin F4.tag.rank → ℤ, IsRoot F4.tag β → rootChar l β =
      w ^ ((3 * β (f4i 1) - 2 * β (f4i 2)) + (2 : ℤ) ^ a * (3 * β (f4i 2) - 4 * β (f4i 1))) := by
    intro β hβ
    rw [rootChar_eq_torusWeight hl hβ, LargeReeCover.torusWeight_apply,
      ← torusExp_combo ((2 : ℤ) ^ a) β, zpow_add, zpow_mul]
    simp
  have hwp : w ^ p = 1 := hw.pow_eq_one
  have hap : ∀ i, l i ^ p = 1 := fun i => by
    have h := hA' (Pi.single i 1) (IsRoot.basis i)
    rw [rootChar_single] at h
    rw [h, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hwp, one_zpow]
  have hθ : (p : ℤ) ∣ 2 * ((2 : ℤ) ^ a) ^ 2 - 1 := by
    have h1 : ((2 ^ (2 * a + 1) - 1 : ℕ) : ℤ) = 2 * ((2 : ℤ) ^ a) ^ 2 - 1 := by
      rw [Nat.cast_sub Nat.one_le_two_pow]
      push_cast
      ring
    rw [← h1]
    exact Int.natCast_dvd_natCast.2 hpq
  have hker := f4_kernel_sub hp h5 hθ hw l hA'
  have hSker : ∀ α ∈ f4S03, IsRoot F4.tag α ∧ rootChar l α = 1 := fun α hα => by
    refine ⟨isRoot_of_mem_f4S03 hα, ?_⟩
    rw [hA' α (isRoot_of_mem_f4S03 hα), (coord_f4S03 hα).1, (coord_f4S03 hα).2]
    simp
  have ha1 : l ≠ 1 := by
    intro h1
    have h := hA' (Pi.single (f4i 1) 1) (IsRoot.basis _)
    rw [h1, rootChar_single] at h
    have hdvd := (hw.zpow_eq_one_iff_dvd _).1 h.symm
    simp only [Pi.single_eq_same] at hdvd
    have h12 : (Pi.single (f4i 1) (1 : ℤ) : Fin F4.tag.rank → ℤ) (f4i 2) = 0 := by decide
    rw [h12] at hdvd
    have h1' : (p : ℤ) ∣ 1 := by
      have e : (1 : ℤ) = (3 - 4 * (2 : ℤ) ^ a) * (3 + 4 * (2 : ℤ) ^ a) +
          8 * (2 * ((2 : ℤ) ^ a) ^ 2 - 1) := by ring
      rw [e]
      refine dvd_add (Dvd.dvd.mul_right ?_ _) (Dvd.dvd.mul_left hθ _)
      convert hdvd using 1
      ring
    have := Int.eq_one_of_dvd_one (by positivity) h1'
    have := hp.one_lt
    omega
  have hcR : rankOneGroupOne K a ≤ centralizer {torusPair (K := K) a (w, w ^ 2)} := by
    rw [hl, ← reeGamma_inf_rootSpan_eq_rankOneGroupOne hK]
    exact inf_le_right.trans (rootSpan_le_centralizer_of_char_one hSker)
  refine ⟨fun r hr => mem_centralizer_singleton_iff.1 (hcR hr), fun y hy hc => ?_⟩
  have hc' : y * rootDiagUnit F4.tag l = rootDiagUnit F4.tag l * y := by
    rw [← hl]
    exact hc
  have hTM := CFSG.RankThree.PartOne.KE.mem_torus_mul_rootSpan_of_commute hp
    (CFSG.RankThree.PartOne.KE.not_dvd_card_weylGroup_F4 hp (by omega)) hap ha1
    (fun α hα => isRoot_of_mem_f4S03 hα) (fun α hα => neg_mem_f4S03 hα) hker
    (mem_reeGamma.1 hy).1 hc'
  obtain ⟨h, hh, hhy⟩ := exists_torus_mul_of_mem hK hy hTM
  exact ⟨h, hh, by rwa [reeGamma_inf_rootSpan_eq_rankOneGroupOne hK] at hhy⟩

end Cent

end CFSG.ComponentClassification.RankTwoExceptional.ReeSec8
