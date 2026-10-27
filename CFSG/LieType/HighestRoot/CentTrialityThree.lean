module

public import CFSG.LieType.HighestRoot.CentTriality
public import CFSG.LieType.HighestRoot.CentTrialityRoots
public import CFSG.LieType.HighestRoot.CentTrialityFixed
public import CFSG.LieType.Steinberg.TwistedD4.Perfect
public import CFSG.LieType.HighestRoot.CentChevalleyInner
public import CFSG.LieType.HighestRoot.CentIsogeny
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.GroupTheory.LocalCores.Fitting

public section

namespace CFSG.LieType.HighestRoot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.G2D4Models
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement

section SL2

variable {K : Type} [Field K]

theorem isQuasisimple_SL2_of_four_le [Finite K] (h4 : 4 ≤ Nat.card K) :
    CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) K) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have h4' : ∃ s : Finset K, s.card = 4 := by
    obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4)
    exact ⟨t, ht⟩
  have hperf := CFSG.LinearGroups.special_linear_isPerfect (K := K) (n := 2) le_rfl (Or.inr h4')
  obtain ⟨-, hsimple, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := K) (n := 2) le_rfl
    (Or.inr h4')
  refine ⟨hperf, hsimple, ?_⟩
  by_contra hab
  simp only [not_exists, not_not] at hab
  have hle : commutator (Matrix.SpecialLinearGroup (Fin 2) K) ≤
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff]
    change (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))) ⁅x, y⁆ = 1
    rw [map_commutatorElement, commutatorElement_def, hab (QuotientGroup.mk' _ x),
      mul_inv_cancel_right, mul_inv_cancel]
  rw [Group.isPerfect_def.mp hperf] at hle
  obtain ⟨a, b, hne⟩ := exists_pair_ne
    (Matrix.SpecialLinearGroup (Fin 2) K ⧸ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  exact hne (QuotientGroup.eq.mpr (hle (Subgroup.mem_top _)))

theorem mul_self_eq_one_of_mem_center {A : Type*} [Group A]
    (e : A ≃* Matrix.SpecialLinearGroup (Fin 2) K) {x : A} (hx : x ∈ Subgroup.center A) :
    x * x = 1 := by
  have hc : e x ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) := by
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro g
    obtain ⟨g, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, hx g]
  obtain ⟨r, hr, hrx⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hc
  apply e.injective
  rw [map_mul, map_one]
  ext p q
  rw [Matrix.SpecialLinearGroup.coe_mul, ← hrx, ← map_mul]
  simp only [Fintype.card_fin] at hr
  rw [← pow_two, hr, map_one]
  rfl

end SL2

section Main

variable {K : Type} [Field K]

theorem ringChar_ne_two_of_card_eq_27 [Finite K] (hK27 : Nat.card K = 27) :
    ringChar K ≠ 2 := by
  have : Fintype K := Fintype.ofFinite K
  intro h2
  have h2' : (2 : K) = 0 := by
    have h := ringChar.Nat.cast_ringChar (R := K)
    rw [h2] at h
    exact_mod_cast h
  have h27 : (27 : K) = 0 := by
    have h := FiniteField.cast_card_eq_zero K
    rw [← Nat.card_eq_fintype_card, hK27] at h
    exact_mod_cast h
  exact one_ne_zero (by linear_combination h27 - 13 * h2' : (1 : K) = 0)

theorem card_rootSubgroup
    (β : Fin d4.rank → ℤ) :
    Nat.card (rootSubgroup d4 K β) = Nat.card K := by
  refine (Nat.card_congr (Equiv.ofBijective (fun c : K => (⟨pinnedX d4 K β c,
    mem_rootSubgroup.2 ⟨c, rfl⟩⟩ : rootSubgroup d4 K β)) ⟨fun c d h => ?_, fun g => ?_⟩)).symm
  · exact pinnedX_injective d4 K β (congrArg Subtype.val h)
  · obtain ⟨c, hc⟩ := mem_rootSubgroup.1 g.2
    exact ⟨c, Subtype.ext hc⟩

theorem coe_xPar_mem_rootSubgroup
    {γ : Fin d4.rank → ℤ} (hγ : IsRoot d4 γ) (c : K) :
    ((xPar (rootOperatorFamily d4) γ c : adjointGroup d4 K) : ModGL d4 K) ∈
      rootSubgroup d4 K γ := by
  have h := xPar_mem (F := rootOperatorFamily d4) (K := K) hγ c
  rw [rootGroup_eq_subgroupOf hγ] at h
  exact Subgroup.mem_subgroupOf.1 h

theorem xOrbit_eq_mul
    (σ : K →+* K) {β : Fin d4.rank → ℤ} (hβ : IsT4Outer β) {s : ℤ}
    (hs : s = 1 ∨ s = -1) (c : K) :
    ∃ w ∈ Subgroup.centralizer (pairGroup d4 K β : Set (ModGL d4 K)),
      ((xOrbit σ (s • β) c : adjointGroup d4 K) : ModGL d4 K) =
        ((xPar (rootOperatorFamily d4) (s • β) c : adjointGroup d4 K) : ModGL d4 K) * w := by
  have hρ : rho (s • β) = s • rho β := rfl
  have hρρ : rho (rho (s • β)) = s • rho (rho β) := rfl
  have hb1 := isT4Outer_rho hβ
  have hb2 := isT4Outer_rho hb1
  have hmem : ∀ {γ : Fin d4.rank → ℤ}, IsT4Outer γ → γ ≠ β → ∀ d : K,
      ((xPar (rootOperatorFamily d4) (s • γ) d : adjointGroup d4 K) : ModGL d4 K) ∈
        Subgroup.centralizer (pairGroup d4 K β : Set (ModGL d4 K)) := by
    intro γ hγ hne d
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hx : ((xPar (rootOperatorFamily d4) (s • γ) d : adjointGroup d4 K) : ModGL d4 K) ∈
        pairGroup d4 K γ := by
      rcases hs with rfl | rfl
      · have h := coe_xPar_mem_rootSubgroup (K := K) (isRoot_of_isT4Frame (Or.inr hγ)) d
        rw [one_smul]
        exact Subgroup.mem_sup_left h
      · have h := coe_xPar_mem_rootSubgroup (K := K) (IsRoot.neg (isRoot_of_isT4Frame
          (Or.inr hγ))) d
        rw [neg_one_smul]
        exact Subgroup.mem_sup_right h
    exact (commute_t4 (Or.inr hβ) (Or.inr hγ) hne hx hy).eq.symm
  refine ⟨((xPar (rootOperatorFamily d4) (rho (s • β)) (twistSign σ (s • β) * σ c) :
      adjointGroup d4 K) : ModGL d4 K) * ((xPar (rootOperatorFamily d4) (rho (rho (s • β)))
        (twistSign σ (s • β) * twistSign σ (rho (s • β)) * σ (σ c)) : adjointGroup d4 K) :
          ModGL d4 K), mul_mem ?_ ?_, ?_⟩
  · rw [hρ]
    exact hmem hb1 (rho_ne_of_isT4Outer hβ) _
  · rw [hρρ]
    exact hmem hb2 (rho_rho_ne_of_isT4Outer hβ) _
  · rw [xOrbit]
    simp only [Subgroup.coe_mul]
    group

theorem pow_three_eq_one_of_mem_rootSubgroup
    (h3 : (3 : K) = 0) {β : Fin d4.rank → ℤ}
    {x : ModGL d4 K} (hx : x ∈ rootSubgroup d4 K β) : x ^ 3 = 1 := by
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
  rw [pow_succ, pow_two, ← pinnedX_add, ← pinnedX_add,
    show c + c + c = (3 : K) * c by ring, h3, zero_mul, pinnedX_zero]

variable [Finite K]

theorem eq_rankOne_long_of_card_eq_three
    (hK27 : Nat.card K = 27) {σ : K →+* K}
    (hσ3 : ∀ c, σ c = c ^ 3) {F : Type} [Field F] [Finite F] (hF3 : Nat.card F = 3)
    {z : twistedGroup σ} (hz : z ∈ rankOne (twistedRootGroup σ) (ng 0)) (h2 : orderOf z = 2)
    {L : Subgroup (twistedGroup σ)}
    (hLC : L ≤ Subgroup.centralizer ({z} : Set (twistedGroup σ)))
    (hCL : Subgroup.centralizer ({z} : Set (twistedGroup σ)) ≤
      Subgroup.normalizer (L : Set (twistedGroup σ)))
    (eL : L ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    L = rankOne (twistedRootGroup σ) (ng 0) := by
  have hK := ringChar_ne_two_of_card_eq_27 hK27
  have hσ : ∀ c, σ (σ (σ c)) = c := sigma_three_of_card (q := 3) (by rw [hK27]; norm_num) hσ3
  have h3K : (3 : K) = 0 := by
    have : Fintype K := Fintype.ofFinite K
    have h := FiniteField.cast_card_eq_zero K
    rw [← Nat.card_eq_fintype_card, hK27] at h
    have h27 : (3 : K) ^ 3 = 0 := by
      rw [show (3 : K) ^ 3 = ((27 : ℕ) : K) by norm_num]
      exact h
    exact pow_eq_zero_iff (by norm_num) |>.1 h27
  set a := signTuple d4 K (nd 2) with ha_def
  have ha : ∀ j, a j = 1 ∨ a j = -1 := signTuple_eq_one_or_eq_neg_one (nd 2)
  set ι := td4Incl σ with hι
  have hzC : ι z = rootDiagUnit d4 a := by
    rw [hι, td4Incl_eq_of_mem hK hz h2, aLongTD4_eq_signTuple]
  have hcommz : ∀ g : twistedGroup σ, g ∈ Subgroup.centralizer ({z} : Set (twistedGroup σ)) →
      ι g * rootDiagUnit d4 a = rootDiagUnit d4 a * ι g := by
    intro g hg
    rw [← hzC, ← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 hg]
  set L' := L.map ι with hL'
  have eL' : L' ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (Subgroup.equivMapOfInjective L ι (td4Incl_injective σ)).symm.trans eL
  have : Finite (ModGL d4 K) := finite_modGL
  have hLX : L' ≤ toralCentralizer d4 K a := by
    rintro _ ⟨l, hl, rfl⟩
    refine mem_toralCentralizer.2 ⟨(l : adjointGroup d4 K).2, ?_⟩
    rw [← hcommz l (hLC hl)]
    group
  have hK3 : Nat.Coprime 3 (Nat.card K - 1) := by
    rw [hK27]
    norm_num
  set χ := signChar d4 K (nd 2) with hχ
  have hker : rootCharKernel a = kernelRoots χ := rootCharKernel_signTuple_eq hK
  have hLS : L' ≤ rootSpan d4 K (kernelRoots χ) := by
    rw [← hker]
    exact le_rootSpan_of_closure_eq_top_of_coprime hK3 hK ha hLX
      (closure_orderOf_three_eq_top_of_mulEquiv hF3 eL')
  have hSz : ∀ u : twistedGroup σ, ι u ∈ rootSpan d4 K (rootCharKernel a) →
      u ∈ Subgroup.centralizer ({z} : Set (twistedGroup σ)) := by
    intro u hu
    have h := (mem_toralCentralizer.1 (rootSpan_rootCharKernel_le_toralCentralizer a hu)).2
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply td4Incl_injective σ
    rw [map_mul, map_mul, ← hι, hzC]
    calc ι u * rootDiagUnit d4 a = (rootDiagUnit d4 a * ι u * (rootDiagUnit d4 a)⁻¹) *
        rootDiagUnit d4 a := by rw [h]
      _ = rootDiagUnit d4 a * ι u := by group
  have hcent : ∀ β, IsT4Outer β →
      L' ≤ Subgroup.centralizer (pairGroup d4 K β : Set (ModGL d4 K)) := by
    intro β hβ
    have hβF : IsT4Frame β := Or.inr hβ
    have hβr := isRoot_of_isT4Frame hβF
    have hSk := componentRootSpan_t4 hK hβF
    obtain ⟨-, ⟨e⟩, -⟩ := odd_arbitrary_root_pair_SL2_p_components d4 K hK hβr
    have hq : CFSG.IsQuasisimple (pairGroup d4 K β) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv e
        (isQuasisimple_SL2_of_four_le (by rw [hK27]; norm_num))
    have hgen : ∀ {s : ℤ}, (s = 1 ∨ s = -1) → ∀ x ∈ rootSubgroup d4 K (s • β),
        x ∈ actLike (pairGroup d4 K β) (Subgroup.normalizer (L' : Set (ModGL d4 K))) := by
      intro s hs x hx
      have hsr : IsRoot d4 (s • β) := by
        rcases hs with rfl | rfl
        · rwa [one_smul]
        · rw [neg_one_smul]; exact IsRoot.neg hβr
      have hxA : x ∈ pairGroup d4 K β := by
        rcases hs with rfl | rfl
        · rw [one_smul] at hx; exact Subgroup.mem_sup_left hx
        · rw [neg_one_smul] at hx; exact Subgroup.mem_sup_right hx
      have hxH : x ∈ adjointGroup d4 K := rootSubgroup_le_adjointGroup _ hx
      have hx' : (⟨x, hxH⟩ : adjointGroup d4 K) ∈ rootGroup (rootOperatorFamily d4) K (s • β) := by
        rw [rootGroup_eq_subgroupOf hsr]
        exact Subgroup.mem_subgroupOf.2 hx
      obtain ⟨c, hc⟩ := (mem_rootGroup_iff hsr _).1 hx'
      have hne : rho (s • β) ≠ s • β := by
        intro h
        apply rho_ne_of_isT4Outer hβ
        have h' : s • rho β = s • β := h
        rcases hs with rfl | rfl
        · simpa using h'
        · simpa using h'
      have hu : xOrbit σ (s • β) c ∈ twistedGroup σ :=
        twistedRootSubgroupD4_le_twistedGroup σ (isRoot_proj hsr) (xOrbit_mem hσ hsr hne c)
      set u : twistedGroup σ := ⟨_, hu⟩
      obtain ⟨w, hw, hxw⟩ := xOrbit_eq_mul σ hβ hs c
      have hιu : ι u = x * w := by
        rw [hι, td4Incl_apply]
        change ((xOrbit σ (s • β) c : adjointGroup d4 K) : ModGL d4 K) = x * w
        rw [hxw, hc]
      have hρs : rho (s • β) = s • rho β := rfl
      have hρρs : rho (rho (s • β)) = s • rho (rho β) := rfl
      have hkr : ∀ {γ : Fin d4.rank → ℤ}, IsT4Outer γ → s • γ ∈ rootCharKernel a := by
        intro γ hγ
        rw [t4_mem_kernel_iff hK]
        rcases hs with rfl | rfl
        · exact ⟨γ, Or.inr hγ, Or.inl (one_smul _ _)⟩
        · exact ⟨γ, Or.inr hγ, Or.inr (neg_one_smul _ _)⟩
      have hmemS : ∀ {γ : Fin d4.rank → ℤ}, s • γ ∈ rootCharKernel a → IsRoot d4 (s • γ) →
          ∀ d : K, ((xPar (rootOperatorFamily d4) (s • γ) d : adjointGroup d4 K) :
            ModGL d4 K) ∈ rootSpan d4 K (rootCharKernel a) := fun hγ hγr d =>
        (le_iSup₂_of_le _ hγ le_rfl : rootSubgroup d4 K _ ≤ rootSpan d4 K (rootCharKernel a))
          (coe_xPar_mem_rootSubgroup hγr d)
      have hρr : IsRoot d4 (s • rho β) := hρs ▸ isRoot_rho hsr
      have hρρr : IsRoot d4 (s • rho (rho β)) := hρρs ▸ isRoot_rho (isRoot_rho hsr)
      have huS : ι u ∈ rootSpan d4 K (rootCharKernel a) := by
        rw [hι, td4Incl_apply]
        change ((xOrbit σ (s • β) c : adjointGroup d4 K) : ModGL d4 K) ∈ _
        rw [xOrbit, Subgroup.coe_mul, Subgroup.coe_mul, hρρs, hρs]
        exact mul_mem (mul_mem (hmemS (hkr hβ) hsr c)
          (hmemS (hkr (isT4Outer_rho hβ)) hρr _))
          (hmemS (hkr (isT4Outer_rho (isT4Outer_rho hβ))) hρρr _)
      have hN : ι u ∈ Subgroup.normalizer (L' : Set (ModGL d4 K)) :=
        Subgroup.le_normalizer_map ι ⟨u, hCL (hSz u huS), rfl⟩
      refine ⟨hxA, ι u, hN, fun y hy => ?_⟩
      rw [hιu]
      have hwy := (Subgroup.mem_centralizer_iff.1 hw) y hy
      calc x * y * x⁻¹ = x * (y * w) * w⁻¹ * x⁻¹ := by group
        _ = x * (w * y) * w⁻¹ * x⁻¹ := by rw [hwy]
        _ = x * w * y * (x * w)⁻¹ := by group
    have hproj : pairGroup d4 K β ≤
        actLike (pairGroup d4 K β) (Subgroup.normalizer (L' : Set (ModGL d4 K))) :=
      sup_le (fun x hx => hgen (Or.inl rfl) x (by rwa [one_smul]))
        (fun x hx => hgen (Or.inr rfl) x (by rwa [neg_one_smul]))
    have : Finite L' := Finite.of_equiv _ eL'.symm.toEquiv
    refine le_centralizer_of_isQuasisimple hq (fun l hl => ?_) (fun g hg => (hproj hg).2)
      (X := rootSubgroup d4 K β) le_sup_left (fun x hx hcen => ?_) ?_
    ·
      obtain ⟨j, hj, c, hc, rfl⟩ := exists_eq_mul_of_mem_rootSpan χ
        ⟦⟨β, mem_kernelRoots_t4 hK hβF⟩⟧ (hLS hl)
      rw [hSk] at hj hc
      refine ⟨j, hj, fun y hy => ?_⟩
      have hjy : j * y * j⁻¹ ∈ pairGroup d4 K β := mul_mem (mul_mem hj hy) (inv_mem hj)
      have hcj := (Subgroup.mem_centralizer_iff.1 hc) _ hjy
      calc c * j * y * (c * j)⁻¹ = c * (j * y * j⁻¹) * c⁻¹ := by group
        _ = (j * y * j⁻¹) * c * c⁻¹ := by rw [← hcj]
        _ = j * y * j⁻¹ := by group
    ·
      have hxc : (⟨x, Subgroup.mem_sup_left hx⟩ : pairGroup d4 K β) ∈
          Subgroup.center (pairGroup d4 K β) := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (hcen g g.2).symm
      have hx2 : x * x = 1 := congrArg Subtype.val (mul_self_eq_one_of_mem_center e.symm hxc)
      have hx3 := pow_three_eq_one_of_mem_rootSubgroup h3K hx
      calc x = x ^ 3 * (x * x)⁻¹ := by group
        _ = 1 := by rw [hx3, hx2]; group
    · rw [card_rootSubgroup, hK27, card_eq_24 hF3 eL']
      norm_num
  set k₀ : KernelComponent χ := ⟦⟨t4c, mem_kernelRoots_t4 hK (Or.inl rfl)⟩⟧ with hk₀
  have hS₀ : componentRootSpan K χ k₀ = pairGroup d4 K t4c := componentRootSpan_t4 hK (Or.inl rfl)
  have hLk : ∀ x ∈ L', ∀ k, k ≠ k₀ → ∀ y ∈ componentRootSpan K χ k, x * y = y * x := by
    intro x hx k hk y hy
    obtain ⟨β, hβ, rfl⟩ := exists_t4_of_class hK k
    rcases hβ with hβc | hβo
    · exact absurd (by subst hβc; rfl) hk
    · rw [componentRootSpan_t4 hK (Or.inr hβo)] at hy
      exact ((Subgroup.mem_centralizer_iff.1 (hcent β hβo hx)) y hy).symm
  have h3 : ∀ x ∈ L', x ^ 3 = 1 → x ∈ pairGroup d4 K t4c := by
    intro x hx hx3
    obtain ⟨j, hj, t, ⟨htT, htJ⟩, rfl⟩ := exists_eq_mul_of_commute χ k₀ (hLS hx) (hLk x hx)
    rw [hS₀] at hj htJ
    have hcomm' : Commute t j := ((Subgroup.mem_centralizer_iff.1 htJ) j hj).symm
    rw [hcomm'.mul_pow] at hx3
    have ht3 : t ^ 3 ∈ pairGroup d4 K t4c := by
      rw [eq_inv_of_mul_eq_one_left hx3]
      exact inv_mem (pow_mem hj 3)
    have hcop : Nat.Coprime 3 (orderOf t) :=
      Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one
        (pow_card_sub_one_eq_one_of_mem_diagonalGroup (torusGroup_le_diagonalGroup htT))) hK3
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    have htJc : t ∈ pairGroup d4 K t4c := by
      rw [← hm]
      exact pow_mem ht3 m
    exact mul_mem htJc hj
  have hgen3 := closure_orderOf_three_eq_top_of_mulEquiv hF3 eL'
  have hLJ : L' ≤ pairGroup d4 K t4c := by
    intro x hx
    have hle' : Subgroup.closure {y : L' | orderOf y = 3} ≤ (pairGroup d4 K t4c).subgroupOf L' :=
      (Subgroup.closure_le _).2 fun y hy => Subgroup.mem_subgroupOf.2 (h3 y.1 y.2 (by
        have hy' : orderOf (y : ModGL d4 K) = 3 := by
          rw [Subgroup.orderOf_coe]
          exact hy
        rw [← hy']
        exact pow_orderOf_eq_one _))
    exact Subgroup.mem_subgroupOf.1 (hle' (hgen3 ▸ Subgroup.mem_top (⟨x, hx⟩ : L')))
  have hLL : L ≤ rankOne (twistedRootGroup σ) (ng 0) := by
    intro l hl
    have h1 : ι l ∈ pairGroup d4 K t4c := hLJ ⟨l, hl, rfl⟩
    refine mem_rankOne_long_of_mem_rankOneTwo hσ ?_
    change (l : adjointGroup d4 K) ∈ rootGroup (rootOperatorFamily d4) K (Pi.single (nd 2) 1) ⊔
      rootGroup (rootOperatorFamily d4) K (-Pi.single (nd 2) 1)
    rw [rootGroup_eq_subgroupOf (isRoot_single _ _),
      rootGroup_eq_subgroupOf (IsRoot.neg (isRoot_single _ _)),
      ← Subgroup.subgroupOf_sup (rootSubgroup_le_adjointGroup _) (rootSubgroup_le_adjointGroup _)]
    exact Subgroup.mem_subgroupOf.2 h1
  have hcard : Nat.card (rankOne (twistedRootGroup σ) (ng 0)) ≤ Nat.card L := by
    calc Nat.card (rankOne (twistedRootGroup σ) (ng 0)) ≤
        Nat.card (Matrix.SpecialLinearGroup (Fin 2) (fixedField σ)) := card_rankOne_long_le hσ
      _ = 24 := card_eq_24 (card_fixedField_eq_three hK hσ3) (MulEquiv.refl _)
      _ = Nat.card L := (card_eq_24 hF3 eL).symm
  have : Finite (twistedGroup σ) := by
    have : Finite (adjointGroup d4 K) := inferInstance
    infer_instance
  exact Subgroup.eq_of_le_of_card_ge hLL hcard

end Main

end CFSG.LieType.HighestRoot
