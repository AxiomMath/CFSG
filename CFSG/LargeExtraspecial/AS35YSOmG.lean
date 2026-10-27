module

public import CFSG.LargeExtraspecial.AS35YSIrrXB
public import CFSG.LargeExtraspecial.AS35YLSIrrA
public import CFSG.LargeExtraspecial.AS35YSFrame

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.ClassicalGroups.Orthogonal
  AS35YR

namespace AS35YS

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}

theorem exists_frame_of_isTypeA [FiniteDimensional (ZMod 2) V] (hq : q.polarBilin.Nondegenerate)
    {τ : V ≃ₗ[ZMod 2] V} (hA : IsTypeA q τ 2) :
    ∃ F : Frame q, commSpace τ = F.ell ∧ τ = F.t := by
  have hO : τ ∈ TauCeti.QuadraticMap.orthogonalGroup q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hA.1
  have hne : commSpace τ ≠ ⊥ := by
    intro h
    have := hA.2.2.2.1
    rw [h, finrank_bot] at this
    exact absurd this (by norm_num)
  obtain ⟨a, haℓ, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hlt : Submodule.span (ZMod 2) {a} < commSpace τ := by
    refine lt_of_le_of_ne ((Submodule.span_singleton_le_iff_mem _ _).mpr haℓ) fun h => ?_
    have h1 := finrank_span_singleton (K := ZMod 2) ha0
    rw [h, hA.2.2.2.1] at h1
    exact absurd h1 (by norm_num)
  obtain ⟨b, hbℓ, hbn⟩ := IsConcreteLE.exists_of_lt hlt
  have hb0 : b ≠ 0 := fun h => hbn (h ▸ Submodule.zero_mem _)
  have hab : a ≠ b := fun h => hbn (h ▸ Submodule.mem_span_singleton_self a)
  have hspan := AS35YL.span_pair_eq_YL hA.2.2.2.1 haℓ hbℓ ha0 hb0 hab
  obtain ⟨F, rfl, rfl⟩ := exists_frame hq (hA.2.2.2.2 _ haℓ) (hA.2.2.2.2 _ hbℓ)
    (polar_commSpace_eq_zero hO hA.2.2.1 haℓ hbℓ) ha0 hb0 hab
  have hℓ : commSpace τ = F.ell := hspan.symm
  exact ⟨F, hℓ, F.eq_t_of_isTypeA hq hA hℓ⟩

theorem comm_t_of_fix_YS [FiniteDimensional (ZMod 2) V] (F : Frame q)
    (hq : q.polarBilin.Nondegenerate) {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup q) (ga : g F.a = F.a) (gb : g F.b = F.b) :
    g * F.t = F.t * g := by
  have h := F.conj_t_eq hq hg fun z hz => by
    rw [Frame.apply_eq_of_mem_ell ga gb hz]
    exact hz
  calc g * F.t = g * F.t * g⁻¹ * g := by group
    _ = F.t * g := by rw [h]

theorem finrank_Xp_add_eq [FiniteDimensional (ZMod 2) V] (hq : q.polarBilin.Nondegenerate)
    (F : Frame q) : finrank (ZMod 2) F.Xp + 4 = finrank (ZMod 2) V := by
  set H := Submodule.span (ZMod 2) ({F.a, F.b, F.c, F.c'} : Set V) with hH
  have hle := F.finrank_Xp_add hq
  have h1 : finrank (ZMod 2) F.Xp = finrank (ZMod 2) V - finrank (ZMod 2) H :=
    LinearMap.BilinForm.finrank_orthogonal hq H
  have hHV := Submodule.finrank_le H
  let φ : H →ₗ[ZMod 2] (Fin 4 → ZMod 2) :=
    { toFun := fun x => ![polar q x F.c', polar q x F.c, polar q x F.b, polar q x F.a]
      map_add' := fun x y => by
        ext i
        fin_cases i <;> simp [polar_add_left]
      map_smul' := fun r x => by
        ext i
        fin_cases i <;> simp [polar_smul_left] }
  have hsurj : Function.Surjective φ := by
    have hca : polar q F.c' F.a = 1 := by rw [polar_comm]; exact F.ac'
    have hcb : polar q F.c F.b = 1 := by rw [polar_comm]; exact F.bc
    have hba : polar q F.b F.a = 0 := by rw [polar_comm]; exact F.ab
    have hca' : polar q F.c F.a = 0 := by rw [polar_comm]; exact F.ac
    have hcb' : polar q F.c' F.b = 0 := by rw [polar_comm]; exact F.bc'
    have hcc : polar q F.c' F.c = 0 := by rw [polar_comm]; exact F.cc'
    have hmem : ∀ x ∈ ({F.a, F.b, F.c, F.c'} : Set V), x ∈ H := fun x hx => Submodule.subset_span hx
    intro f
    refine ⟨f 0 • ⟨F.a, hmem _ (by simp)⟩ + f 1 • ⟨F.b, hmem _ (by simp)⟩ +
      f 2 • ⟨F.c, hmem _ (by simp)⟩ + f 3 • ⟨F.c', hmem _ (by simp)⟩, ?_⟩
    ext i
    fin_cases i <;> simp [φ, polar_add_left, polar_smul_left, F.ac', F.bc, F.ab,
      F.ac, F.bc', F.cc', hca, hcb, hba, hca', hcb', hcc, F.qa, F.qb, F.qc, F.qc']
  have h4 : 4 ≤ finrank (ZMod 2) H := by
    have := LinearMap.finrank_range_le φ
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fin_fun] at this
    exact this
  omega

theorem omega_bound_YS [FiniteDimensional (ZMod 2) V] [Finite V]
    (hq : q.polarBilin.Nondegenerate) {τ : V ≃ₗ[ZMod 2] V} (hA : IsTypeA q τ 2)
    {P Y : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hPU : ∀ p ∈ P, (∀ v, q (p v) = q v) ∧ (∀ v ∈ commSpace τ, p v = v) ∧
      ∀ v ∈ fixSpace τ, p v - v ∈ commSpace τ)
    (hYP : Y ≤ P) (hτY : τ ∈ Y) {y : V ≃ₗ[ZMod 2] V} (hyY : y ∈ Y) (hy1 : y ≠ 1) (hyτ : y ≠ τ)
    (hΩ : ∀ g : V ≃ₗ[ZMod 2] V, (∀ v, q (g v) = q v) → Even (finrank (ZMod 2) (commSpace g)) →
      g * τ = τ * g → ∀ x ∈ Y, g * x * g⁻¹ ∈ Y) :
    Nat.card P ≤ 2 ^ (2 * finrank (ZMod 2) V - 7) ∧
      (8 ≤ finrank (ZMod 2) V → 2 ^ (2 * finrank (ZMod 2) V - 8) ≤ Nat.card Y) ∧
      (finrank (ZMod 2) V = 6 → 32 ≤ Nat.card Y ∨
        (8 ≤ Nat.card Y ∧ ∀ x ∈ Y, ∀ x' ∈ Y, x * x' = x' * x)) := by
  obtain ⟨F, hFℓ, rfl⟩ := exists_frame_of_isTypeA hq hA
  have hdim := finrank_Xp_add_eq hq F
  have hcardX : Nat.card F.Xp = 2 ^ (finrank (ZMod 2) V - 4) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    congr 1
    omega
  have hU : ∀ p ∈ P, F.InU p := by
    intro p hp
    obtain ⟨hiso, hfix, hsub⟩ := hPU p hp
    refine ⟨TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hiso,
      hfix _ (hFℓ ▸ F.a_mem_ell), hfix _ (hFℓ ▸ F.b_mem_ell), fun v ha hb => ?_⟩
    have hv : v ∈ fixSpace F.t := by
      rw [fixSpace_eq_orthogonal_commSpace hq F.t_mem F.t_mul_self, F.commSpace_t,
        OrthoF2.mem_orthogonal_iff_polar]
      intro u hu
      obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hu
      rw [polar_add_right, polar_smul_right, polar_smul_right, ha, hb]
      simp
    have := hsub v hv
    rwa [hFℓ] at this
  have hs : ∀ g : V ≃ₗ[ZMod 2] V, g ∈ TauCeti.QuadraticMap.orthogonalGroup q →
      Even (finrank (ZMod 2) (commSpace g)) → g * F.t = F.t * g → ∀ x ∈ Y, g * x * g⁻¹ ∈ Y :=
    fun g hg hev hc => hΩ g (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg) hev hc
  have hR : RadHyp0 F Y :=
    ⟨fun p hp => hU p (hYP hp),
      hs F.s₁ F.s₁_mem (F.even_finrank_commSpace_s₁ hq) (F.s₁_comm hq),
      hs F.s₂ F.s₂_mem (F.even_finrank_commSpace_s₂ hq) (F.s₂_comm hq)⟩
  set Y'' := F.Y Y hR.inU with hY''
  have hYX : Y'' ≤ F.Xp := fun z hz => hR.mem_Xp hz
  obtain ⟨y₀, hy₀, hy₀0⟩ := hR.exists_ne_zero_mem_Y hyY hy1 hyτ
  have hy₀' : y₀ ∈ Y'' := hy₀
  have hY0 : Y'' ≠ ⊥ := fun h => hy₀0 (by rw [h, Submodule.mem_bot] at hy₀'; exact hy₀')
  have hlevi : LeviInv F Y'' := by
    refine ⟨fun v hv w hw hv1 hw1 z hz => ?_, fun u hu w hw hu0 hw0 huw z hz => ?_⟩
    · obtain ⟨fa, fb, fc, fc'⟩ := Frame.refl1_fix hv hv1
      obtain ⟨ga, gb, gc, gc'⟩ := Frame.refl1_fix hw hw1
      have hg := mul_mem (refl1_mem hv1) (refl1_mem hw1)
      have hfa : (refl1 q v hv1 * refl1 q w hw1) F.a = F.a := by
        rw [LinearEquiv.mul_apply, ga, fa]
      have hfb : (refl1 q v hv1 * refl1 q w hw1) F.b = F.b := by
        rw [LinearEquiv.mul_apply, gb, fb]
      have hgY := hR.apply_mem_Y hg hfa hfb (by rw [LinearEquiv.mul_apply, gc, fc])
        (by rw [LinearEquiv.mul_apply, gc', fc'])
        (hs _ hg (even_finrank_commSpace_refl1_mul hq hv1 hw1)
          (comm_t_of_fix_YS F hq hg hfa hfb)) hz
      rwa [LinearEquiv.mul_apply] at hgY
    · obtain ⟨sa, sb, sc, sc'⟩ := Frame.siegel_fix hu hw hu0 hw0 huw
      have hg := eichler_mem_orthogonalGroup q u w
      exact hR.apply_mem_Y hg sa sb sc sc'
        (hs _ hg (even_finrank_commSpace_siegel hq hu0 hw0 huw)
          (comm_t_of_fix_YS F hq hg sa sb)) hz
  have : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod 2] V => (e : V → V))
      (fun _ _ h => LinearEquiv.ext (congrFun h))
  have : Finite Y := Subtype.finite
  have : Finite P := Subtype.finite
  refine ⟨?_, fun h8 => ?_, fun h6 => ?_⟩
  · have h := card_le_of_inU F hU
    rw [hcardX, ← pow_add, ← pow_succ'] at h
    calc Nat.card P ≤ 2 ^ (finrank (ZMod 2) V - 4 + (finrank (ZMod 2) V - 4) + 1) := h
      _ = 2 ^ (2 * finrank (ZMod 2) V - 7) := by congr 1; omega
  · have hXle := hlevi.Xp_le hq (by omega) hYX hY0
    have hcY : Nat.card F.Xp ≤ Nat.card Y'' :=
      Nat.card_le_card_of_injective (fun x => (⟨x, hXle x.2⟩ : Y''))
        fun x x' hxx => Subtype.ext (congrArg (fun z : Y'' => (z : V)) hxx)
    have hle : Nat.card Y'' * Nat.card Y'' ≤ Nat.card Y := hR.card_Y_mul_le
    calc 2 ^ (2 * finrank (ZMod 2) V - 8) =
        2 ^ (finrank (ZMod 2) V - 4) * 2 ^ (finrank (ZMod 2) V - 4) := by
          rw [← pow_add]; congr 1; omega
      _ ≤ Nat.card Y'' * Nat.card Y'' := by rw [← hcardX]; exact Nat.mul_le_mul hcY hcY
      _ ≤ Nat.card Y := hle
  · have hle : 2 * (Nat.card Y'' * Nat.card Y'') ≤ Nat.card Y := hR.two_mul_card_Y_le hτY
    have hX2 : finrank (ZMod 2) F.Xp = 2 := by omega
    by_cases hXle : F.Xp ≤ Y''
    · left
      have hcY : Nat.card F.Xp ≤ Nat.card Y'' :=
        Nat.card_le_card_of_injective (fun x => (⟨x, hXle x.2⟩ : Y''))
          fun x x' hxx => Subtype.ext (congrArg (fun z : Y'' => (z : V)) hxx)
      rw [hcardX, h6] at hcY
      have : 4 * 4 ≤ Nat.card Y'' * Nat.card Y'' := Nat.mul_le_mul hcY hcY
      omega
    · right
      have hlt : Y'' < F.Xp := lt_of_le_of_ne hYX fun h => hXle h.ge
      have h1 : finrank (ZMod 2) Y'' = 1 := by
        have h2 := Submodule.finrank_lt_finrank_of_lt hlt
        have h3 : 0 < finrank (ZMod 2) Y'' :=
          Nat.pos_of_ne_zero fun h0 => hY0 (Submodule.finrank_eq_zero.mp h0)
        omega
      have hline : ∀ z ∈ Y'', z = 0 ∨ z = y₀ := by
        intro z hz
        have hy₀0' : (⟨y₀, hy₀⟩ : Y'') ≠ 0 := fun h0 => hy₀0 (congrArg Subtype.val h0)
        obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hy₀0').mp h1 ⟨z, hz⟩
        have hc' : c • y₀ = z := congrArg Subtype.val hc
        rcases Frame.zmod2_cases_YR c with rfl | rfl
        · left; rw [← hc', zero_smul]
        · right; rw [← hc', one_smul]
      have hY2 : 2 ≤ Nat.card Y'' := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, h1]
        norm_num
      refine ⟨?_, fun x hx x' hx' => hR.commute_of_le_span hline hx hx'⟩
      have : 2 * 2 ≤ Nat.card Y'' * Nat.card Y'' := Nat.mul_le_mul hY2 hY2
      omega

end AS35YS

end CFSG.LargeExtraspecial
