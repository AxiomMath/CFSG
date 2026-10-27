module

public import CFSG.ClassicalGroups.Orthogonal.Eichler
import CFSG.ClassicalGroups.Orthogonal.RootGroupCard
import CFSG.RankThree.GF2n.Smith81.Orth212C5Alg

public section

namespace CFSG.ClassicalGroups.Orthogonal

open QuadraticMap Module

variable {F V : Type*} [Field F] [Finite F] [CharP F 2] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V}

private def eichlerBlockRoot (Q : QuadraticForm F V) (W : Submodule F V) (z : V) :
    Subgroup (V ≃ₗ[F] V) where
  carrier := {g | ∃ a ∈ W, polar Q z a = 0 ∧ eichler Q z a = g}
  one_mem' := ⟨0, W.zero_mem, by rw [polar_zero_right], eichler_zero_right Q z⟩
  mul_mem' := by
    rintro g h ⟨a, haW, hza, rfl⟩ ⟨b, hbW, hzb, rfl⟩
    exact ⟨a + b, W.add_mem haW hbW, by rw [polar_add_right, hza, hzb, add_zero],
      by rw [eichler_mul hza hzb]⟩
  inv_mem' := by
    rintro g ⟨a, haW, hza, rfl⟩
    exact ⟨-a, W.neg_mem haW, by rw [polar_neg_right, hza, neg_zero],
      by rw [eichler_inv hza]⟩

private def eichlerBlockRootTwo (Q : QuadraticForm F V) (W : Submodule F V) (z y : V) :
    Subgroup (V ≃ₗ[F] V) where
  carrier := {g | ∃ b ∈ W, polar Q z b = 0 ∧ polar Q y b = 0 ∧ eichler Q y b = g}
  one_mem' := ⟨0, W.zero_mem, by rw [polar_zero_right], by rw [polar_zero_right],
    eichler_zero_right Q y⟩
  mul_mem' := by
    rintro g h ⟨a, haW, hza, hya, rfl⟩ ⟨b, hbW, hzb, hyb, rfl⟩
    exact ⟨a + b, W.add_mem haW hbW,
      by rw [polar_add_right, hza, hzb, add_zero],
      by rw [polar_add_right, hya, hyb, add_zero],
      by rw [eichler_mul hya hyb]⟩
  inv_mem' := by
    rintro g ⟨a, haW, hza, hya, rfl⟩
    exact ⟨-a, W.neg_mem haW, by rw [polar_neg_right, hza, neg_zero],
      by rw [polar_neg_right, hya, neg_zero], by rw [eichler_inv hya]⟩

omit [Finite F] [CharP F 2] [FiniteDimensional F V] in
private theorem mem_eichlerBlockRoot {Q : QuadraticForm F V} {W : Submodule F V} {z : V}
    {g : V ≃ₗ[F] V} :
    g ∈ eichlerBlockRoot Q W z ↔ ∃ a ∈ W, polar Q z a = 0 ∧ eichler Q z a = g :=
  Iff.rfl

omit [Finite F] [CharP F 2] [FiniteDimensional F V] in
private theorem mem_eichlerBlockRootTwo {Q : QuadraticForm F V} {W : Submodule F V} {z y : V}
    {g : V ≃ₗ[F] V} :
    g ∈ eichlerBlockRootTwo Q W z y ↔
      ∃ b ∈ W, polar Q z b = 0 ∧ polar Q y b = 0 ∧ eichler Q y b = g :=
  Iff.rfl

theorem exists_card_eq_sixtyFour_commute_eichler (hF : ∀ a : F, a = 0 ∨ a = 1)
    (hQ : (polarBilin Q).Nondegenerate) {W E : Submodule F V} (hWE : IsCompl W E)
    (hperp : ∀ w ∈ W, ∀ e ∈ E, polar Q w e = 0) (hW : finrank F W = 6) {z y : V}
    (hzW : z ∈ W) (hyW : y ∈ W) (hz0 : z ≠ 0) (hz : Q z = 0) (hy : Q y = 0)
    (hzy : polar Q z y = 0) (hyz : y ∉ F ∙ z) :
    ∃ T : Subgroup (V ≃ₗ[F] V), T ≤ elementaryGroup Q ∧
      (∀ h ∈ T, (∀ w ∈ W, h w ∈ W) ∧ ∀ e ∈ E, h e = e) ∧
      (∀ h ∈ T, h * eichler Q z y = eichler Q z y * h) ∧ Nat.card T = 64 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hVfin : Finite V := Module.finite_of_finite F
  have hVEfin : Finite (V ≃ₗ[F] V) :=
    Finite.of_injective (fun e : V ≃ₗ[F] V => (e : V → V))
      fun e₁ e₂ h => LinearEquiv.ext fun v => congrFun h v
  have hcardF : Nat.card F = 2 := by
    rw [Nat.card_eq_two_iff' (0 : F)]
    refine ⟨1, one_ne_zero, fun a ha => ?_⟩
    rcases hF a with h | h
    · exact absurd h ha
    · exact h
  have hnd : ∀ u : V, (∀ v : V, polar Q u v = 0) → u = 0 := by
    intro u hu
    exact hQ.1 u (fun v => by simpa using hu v)
  have hli : LinearIndependent F ![z, y] := by
    have hpair : y ≠ 0 ∧ ∀ c : F, c • y ≠ z := by
      refine ⟨?_, ?_⟩
      · intro hy0
        exact hyz (by rw [hy0]; exact Submodule.zero_mem _)
      · intro c hc
        apply hyz
        have hyc : y = c⁻¹ • z := by
          by_cases hc0 : c = 0
          · rw [hc0, zero_smul] at hc
            exact absurd hc.symm hz0
          · rw [← hc, inv_smul_smul₀ hc0]
        rw [hyc]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    rw [linearIndependent_fin2]
    simpa using hpair
  obtain ⟨f₁, f₂, h11, h12, h21, h22⟩ :=
    CFSG.RankThree.GF2n.Smith81.OrthC5.exists_dual (q := Q) hnd hli
  have hf₁mem : f₁ ∈ (W : Submodule F V) ⊔ E := by
    rw [hWE.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨w₁, hw₁W, e₁, he₁E, hf₁⟩ := Submodule.mem_sup.mp hf₁mem
  have hf₂mem : f₂ ∈ (W : Submodule F V) ⊔ E := by
    rw [hWE.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨w₂, hw₂W, e₂, he₂E, hf₂⟩ := Submodule.mem_sup.mp hf₂mem
  have hzw₁ : polar Q z w₁ = 1 := by
    have h := h11
    rw [← hf₁, polar_add_right, hperp z hzW e₁ he₁E, add_zero] at h
    exact h
  have hyw₁ : polar Q y w₁ = 0 := by
    have h := h12
    rw [← hf₁, polar_add_right, hperp y hyW e₁ he₁E, add_zero] at h
    exact h
  have hzw₂ : polar Q z w₂ = 0 := by
    have h := h21
    rw [← hf₂, polar_add_right, hperp z hzW e₂ he₂E, add_zero] at h
    exact h
  have hyw₂ : polar Q y w₂ = 1 := by
    have h := h22
    rw [← hf₂, polar_add_right, hperp y hyW e₂ he₂E, add_zero] at h
    exact h
  have hf₂z : polar Q f₂ z = 0 := by rw [polar_comm, h21]
  have hf₂y : polar Q f₂ y = 1 := by rw [polar_comm, h22]
  let φz : W →ₗ[F] F := (polarBilin Q z).comp W.subtype
  let Wz : Submodule F W := LinearMap.ker φz
  have hφz : φz ≠ 0 := by
    intro h
    have hval := LinearMap.congr_fun h ⟨w₁, hw₁W⟩
    have hzero : polar Q z w₁ = 0 := by simpa [φz] using hval
    rw [hzw₁] at hzero
    exact one_ne_zero hzero
  have hfrWz : finrank F Wz = 5 := by
    have h := Module.Dual.finrank_ker_add_one_of_ne_zero (f := φz) hφz
    rw [hW] at h
    have h' : Nat.succ (finrank F Wz) = Nat.succ 5 := by simpa using h
    exact Nat.succ.inj h'
  let φy : W →ₗ[F] F := (polarBilin Q y).comp W.subtype
  let Φ : W →ₗ[F] F × F := φz.prod φy
  let Wzy : Submodule F W := LinearMap.ker Φ
  have hWzmem : ∀ x : W, x ∈ Wz ↔ polar Q z x = 0 := by
    intro x
    change φz x = 0 ↔ polar Q z x = 0
    simp [φz, QuadraticMap.polarBilin_apply_apply]
  have hWzymem : ∀ x : W, x ∈ Wzy ↔ polar Q z x = 0 ∧ polar Q y x = 0 := by
    intro x
    change Φ x = 0 ↔ _
    simp [Φ, φz, φy, QuadraticMap.polarBilin_apply_apply, Prod.ext_iff]
  have hΦ1 : Φ ⟨w₁, hw₁W⟩ = (1, 0) := by
    ext <;> simp [Φ, φz, φy, hzw₁, hyw₁]
  have hΦ2 : Φ ⟨w₂, hw₂W⟩ = (0, 1) := by
    ext <;> simp [Φ, φz, φy, hzw₂, hyw₂]
  have hrange : LinearMap.range Φ = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨a, b⟩ -
    refine ⟨a • (⟨w₁, hw₁W⟩ : W) + b • (⟨w₂, hw₂W⟩ : W), ?_⟩
    rw [map_add, map_smul, map_smul, hΦ1, hΦ2]
    ext <;> simp
  have hfrRange : finrank F (LinearMap.range Φ) = 2 := by
    rw [hrange, finrank_top, Module.finrank_prod]
    simp
  have hfrWzy : finrank F Wzy = 4 := by
    have h := LinearMap.finrank_range_add_finrank_ker Φ
    rw [hfrRange, hW] at h
    rw [add_comm] at h
    have h' : Nat.succ (Nat.succ (finrank F Wzy)) = Nat.succ (Nat.succ 4) := by
      simpa using h
    exact Nat.succ.inj (Nat.succ.inj h')
  have hzWz : (⟨z, hzW⟩ : W) ∈ Wz := by
    change φz ⟨z, hzW⟩ = 0
    simpa [φz] using polar_self_eq_zero hz
  let zWz : Wz := ⟨⟨z, hzW⟩, hzWz⟩
  have hzWz0 : zWz ≠ 0 := by
    intro h
    apply hz0
    have := congrArg (fun x : Wz => (((x : Wz) : W) : V)) h
    simpa [zWz] using this
  let L : Submodule F Wz := Submodule.span F {zWz}
  have hfrL : finrank F L = 1 := by
    simpa [L] using finrank_span_singleton hzWz0
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (p := L)
  have hfrC : finrank F C = 4 := by
    have h := Submodule.finrank_add_eq_of_isCompl hC
    rw [hfrL, hfrWz] at h
    rw [add_comm] at h
    have h' : Nat.succ (finrank F C) = Nat.succ 4 := by simpa using h
    exact Nat.succ.inj h'
  have hcardC : Nat.card C = 16 := by
    rw [Module.natCard_eq_pow_finrank (K := F) (V := C), hfrC, hcardF]
    norm_num
  have hy0 : y ≠ 0 := by
    intro hy0
    exact hyz (by rw [hy0]; exact Submodule.zero_mem _)
  let yW : W := ⟨y, hyW⟩
  have hyWzy : yW ∈ Wzy := (hWzymem yW).mpr ⟨hzy, polar_self_eq_zero hy⟩
  let yWzy : Wzy := ⟨yW, hyWzy⟩
  have hyWzy0 : yWzy ≠ 0 := by
    intro h
    apply hy0
    have := congrArg (fun x : Wzy => (((x : Wzy) : W) : V)) h
    simpa [yWzy, yW] using this
  let L' : Submodule F Wzy := Submodule.span F {yWzy}
  have hfrL' : finrank F L' = 1 := by
    have h := finrank_span_singleton (K := F) (v := yWzy) hyWzy0
    exact h
  obtain ⟨C', hC'⟩ := Submodule.exists_isCompl (p := L')
  have hfrC' : finrank F C' = 3 := by
    have h := Submodule.finrank_add_eq_of_isCompl hC'
    rw [hfrL', hfrWzy] at h
    rw [add_comm] at h
    have h' : Nat.succ (finrank F C') = Nat.succ 3 := by simpa using h
    exact Nat.succ.inj h'
  have hcardC' : Nat.card C' = 8 := by
    rw [Module.natCard_eq_pow_finrank (K := F) (V := C'), hfrC', hcardF]
    norm_num
  let A : Subgroup (V ≃ₗ[F] V) := eichlerBlockRoot Q W z
  let A' : Subgroup (V ≃ₗ[F] V) := eichlerBlockRootTwo Q W z y
  let Asup : Subgroup (V ≃ₗ[F] V) := A ⊔ A'
  let Ainf : Subgroup (V ≃ₗ[F] V) := A ⊓ A'
  have hAmem : ∀ g : V ≃ₗ[F] V, g ∈ A ↔
      ∃ a ∈ W, polar Q z a = 0 ∧ eichler Q z a = g := by
    intro g
    simpa [A] using mem_eichlerBlockRoot (Q := Q) (W := W) (z := z) (g := g)
  have hA'mem : ∀ g : V ≃ₗ[F] V, g ∈ A' ↔
      ∃ b ∈ W, polar Q z b = 0 ∧ polar Q y b = 0 ∧ eichler Q y b = g := by
    intro g
    simpa [A'] using mem_eichlerBlockRootTwo (Q := Q) (W := W) (z := z) (y := y) (g := g)
  let fA : C → A := fun c =>
    ⟨eichler Q z (((c : Wz) : W) : V),
      ⟨((c : Wz) : W), ((c : Wz) : W).2, by
        exact (hWzmem ((c : Wz) : W)).mp (c : Wz).2, rfl⟩⟩
  have hfA_inj : Function.Injective fA := by
    intro c d hcd
    have hcd' : eichler Q z (((c : Wz) : W) : V) =
        eichler Q z (((d : Wz) : W) : V) := congrArg Subtype.val hcd
    have hcz : polar Q z (((c : Wz) : W) : V) = 0 :=
      (hWzmem ((c : Wz) : W)).mp (c : Wz).2
    have hdz : polar Q z (((d : Wz) : W) : V) = 0 :=
      (hWzmem ((d : Wz) : W)).mp (d : Wz).2
    obtain ⟨t, ht⟩ := (eichler_eq_eichler_iff hQ hz hz0 hcz hdz).mp hcd'
    have hW_eq : ((d : Wz) : W) = ((c : Wz) : W) + t • zWz := by
      apply Subtype.ext
      simpa [zWz] using ht
    have hdsub : (d : Wz) - (c : Wz) = t • zWz := by
      apply Subtype.ext
      rw [Submodule.coe_sub, Submodule.coe_smul]
      exact sub_eq_iff_eq_add.mpr (by rw [add_comm] at hW_eq; exact hW_eq)
    have hzmemL : (d : Wz) - (c : Wz) ∈ L := by
      rw [hdsub]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    have hCmem : (d : Wz) - (c : Wz) ∈ C := C.sub_mem d.2 c.2
    have hzero : (d : Wz) - (c : Wz) = 0 := by
      have hmem : (d : Wz) - (c : Wz) ∈ L ⊓ C := ⟨hzmemL, hCmem⟩
      rw [disjoint_iff.mp hC.disjoint, Submodule.mem_bot] at hmem
      exact hmem
    exact Subtype.ext (sub_eq_zero.mp hzero).symm
  have hfA_surj : Function.Surjective fA := by
    intro g
    obtain ⟨a, haW, hza, hga⟩ := (hAmem (g : V ≃ₗ[F] V)).mp g.2
    let aW : W := ⟨a, haW⟩
    have haWz : aW ∈ Wz := by
      change φz aW = 0
      simpa [φz] using hza
    let aWz : Wz := ⟨aW, haWz⟩
    have hmem : aWz ∈ L ⊔ C := by
      rw [hC.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨l, hlL, c, hcC, hlc⟩ := Submodule.mem_sup.mp hmem
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hlL
    have hlV : (((l : Wz) : W) : V) = t • z := by
      have := congrArg (fun x : Wz => (((x : Wz) : W) : V)) ht
      simpa [zWz] using this.symm
    have ha_eq : a = (((c : Wz) : W) : V) + t • z := by
      have h1 : (((l : Wz) : W) : V) + (((c : Wz) : W) : V) = a := by
        have := congrArg (fun x : Wz => (((x : Wz) : W) : V)) hlc
        simpa [aWz, aW] using this
      calc a = (((l : Wz) : W) : V) + (((c : Wz) : W) : V) := h1.symm
        _ = t • z + (((c : Wz) : W) : V) := by rw [hlV]
        _ = (((c : Wz) : W) : V) + t • z := add_comm _ _
    refine ⟨⟨c, hcC⟩, ?_⟩
    apply Subtype.ext
    rw [← hga]
    show eichler Q z (((c : Wz) : W) : V) = eichler Q z a
    rw [ha_eq, eichler_add_smul_self hz (((c : Wz) : W) : V) t]
  have hcardA : Nat.card A = 16 := by
    rw [← Nat.card_eq_of_bijective fA ⟨hfA_inj, hfA_surj⟩]
    exact hcardC
  let fA' : C' → A' := fun c =>
    ⟨eichler Q y (((c : Wzy) : W) : V),
      ⟨((c : Wzy) : W), ((c : Wzy) : W).2,
        ((hWzymem ((c : Wzy) : W)).mp (c : Wzy).2).1,
        ((hWzymem ((c : Wzy) : W)).mp (c : Wzy).2).2, rfl⟩⟩
  have hfA'_inj : Function.Injective fA' := by
    intro c d hcd
    have hcd' : eichler Q y (((c : Wzy) : W) : V) =
        eichler Q y (((d : Wzy) : W) : V) := congrArg Subtype.val hcd
    have hcy : polar Q y (((c : Wzy) : W) : V) = 0 :=
      ((hWzymem ((c : Wzy) : W)).mp (c : Wzy).2).2
    have hdy : polar Q y (((d : Wzy) : W) : V) = 0 :=
      ((hWzymem ((d : Wzy) : W)).mp (d : Wzy).2).2
    obtain ⟨t, ht⟩ := (eichler_eq_eichler_iff hQ hy hy0 hcy hdy).mp hcd'
    have hW_eq : ((d : Wzy) : W) = ((c : Wzy) : W) + t • yWzy := by
      apply Subtype.ext
      simpa [yWzy, yW] using ht
    have hdsub : (d : Wzy) - (c : Wzy) = t • yWzy := by
      apply Subtype.ext
      simpa [Submodule.coe_sub, Submodule.coe_smul] using
        sub_eq_iff_eq_add.mpr (by rw [add_comm] at hW_eq; exact hW_eq)
    have hzmemL' : (d : Wzy) - (c : Wzy) ∈ L' := by
      rw [hdsub]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    have hC'mem : (d : Wzy) - (c : Wzy) ∈ C' := C'.sub_mem d.2 c.2
    have hzero : (d : Wzy) - (c : Wzy) = 0 := by
      have hmem : (d : Wzy) - (c : Wzy) ∈ L' ⊓ C' := ⟨hzmemL', hC'mem⟩
      rw [disjoint_iff.mp hC'.disjoint, Submodule.mem_bot] at hmem
      exact hmem
    exact Subtype.ext (sub_eq_zero.mp hzero).symm
  have hfA'_surj : Function.Surjective fA' := by
    intro g
    obtain ⟨b, hbW, hzb, hyb, hgb⟩ := (hA'mem (g : V ≃ₗ[F] V)).mp g.2
    let bW : W := ⟨b, hbW⟩
    have hbWzy : bW ∈ Wzy := (hWzymem bW).mpr ⟨hzb, hyb⟩
    let bWzy : Wzy := ⟨bW, hbWzy⟩
    have hmem : bWzy ∈ L' ⊔ C' := by
      rw [hC'.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨l, hlL, c, hcC, hlc⟩ := Submodule.mem_sup.mp hmem
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hlL
    have hlV : (((l : Wzy) : W) : V) = t • y := by
      have := congrArg (fun x : Wzy => (((x : Wzy) : W) : V)) ht
      simpa [yWzy, yW] using this.symm
    have hb_eq : b = (((c : Wzy) : W) : V) + t • y := by
      have h1 : (((l : Wzy) : W) : V) + (((c : Wzy) : W) : V) = b := by
        have := congrArg (fun x : Wzy => (((x : Wzy) : W) : V)) hlc
        simpa [bWzy, bW] using this
      calc b = (((l : Wzy) : W) : V) + (((c : Wzy) : W) : V) := h1.symm
        _ = t • y + (((c : Wzy) : W) : V) := by rw [hlV]
        _ = (((c : Wzy) : W) : V) + t • y := add_comm _ _
    refine ⟨⟨c, hcC⟩, ?_⟩
    apply Subtype.ext
    rw [← hgb]
    show eichler Q y (((c : Wzy) : W) : V) = eichler Q y b
    rw [hb_eq, eichler_add_smul_self hy (((c : Wzy) : W) : V) t]
  have hcardA' : Nat.card A' = 8 := by
    rw [← Nat.card_eq_of_bijective fA' ⟨hfA'_inj, hfA'_surj⟩]
    exact hcardC'
  let P : Subgroup (V ≃ₗ[F] V) :=
    { carrier := {g | (∀ w ∈ W, g w ∈ W) ∧ ∀ e ∈ E, g e = e}
      one_mem' := by
        refine ⟨fun w hw => ?_, fun e _ => rfl⟩
        simpa using hw
      mul_mem' := by
        rintro g k ⟨hgW, hgE⟩ ⟨hkW, hkE⟩
        refine ⟨fun w hw => hgW (k w) (hkW w hw), fun e he => ?_⟩
        rw [LinearEquiv.mul_apply, hkE e he, hgE e he]
      inv_mem' := by
        rintro g ⟨hgW, hgE⟩
        refine ⟨fun w hw => ?_, fun e he => ?_⟩
        · have hmem : g⁻¹ w ∈ (W : Submodule F V) ⊔ E := by
            rw [hWE.sup_eq_top]
            exact Submodule.mem_top
          obtain ⟨x, hxW, e, heE, hxe⟩ := Submodule.mem_sup.mp hmem
          have hw_eq : w = g x + e := by
            have h := congrArg (fun v => g v) hxe
            rw [map_add, hgE e heE, LinearEquiv.apply_inv_apply'] at h
            exact h.symm
          have he0 : e = 0 := by
            have heW : e ∈ W := by
              have heq : e = w - g x := by
                rw [hw_eq]
                abel
              rw [heq]
              exact W.sub_mem hw (hgW x hxW)
            have hmem2 : e ∈ W ⊓ E := ⟨heW, heE⟩
            rwa [disjoint_iff.mp hWE.disjoint, Submodule.mem_bot] at hmem2
          rw [← hxe, he0, add_zero]
          exact hxW
        · have h : g (g⁻¹ e) = g e := by
            rw [LinearEquiv.apply_inv_apply', hgE e he]
          exact g.injective h }
  have hA_le_P : A ≤ P := by
    intro g hg
    obtain ⟨a, haW, hza, rfl⟩ := (hAmem g).mp hg
    refine ⟨fun w hw => ?_, fun e he => ?_⟩
    · rw [eichler_apply hz hza]
      exact W.sub_mem (W.add_mem hw (W.smul_mem _ haW)) (W.smul_mem _ hzW)
    · rw [eichler_apply hz hza]
      have hze : polar Q z e = 0 := hperp z hzW e he
      have hez : polar Q e z = 0 := by rw [polar_comm, hze]
      have hea : polar Q e a = 0 := by rw [polar_comm, hperp a haW e he]
      rw [hez, hea]
      simp
  have hA'_le_P : A' ≤ P := by
    intro g hg
    obtain ⟨b, hbW, hzb, hyb, rfl⟩ := (hA'mem g).mp hg
    refine ⟨fun w hw => ?_, fun e he => ?_⟩
    · rw [eichler_apply hy hyb]
      exact W.sub_mem (W.add_mem hw (W.smul_mem _ hbW)) (W.smul_mem _ hyW)
    · rw [eichler_apply hy hyb]
      have hye : polar Q y e = 0 := hperp y hyW e he
      have hey : polar Q e y = 0 := by rw [polar_comm, hye]
      have heb : polar Q e b = 0 := by rw [polar_comm, hperp b hbW e he]
      rw [hey, heb]
      simp
  have hA_le_K : A ≤ elementaryGroup Q ⊓ P := by
    refine le_inf (fun g hg => ?_) hA_le_P
    obtain ⟨a, haW, hza, rfl⟩ := (hAmem g).mp hg
    exact eichler_mem_elementaryGroup Q z a
  have hA'_le_K : A' ≤ elementaryGroup Q ⊓ P := by
    refine le_inf (fun g hg => ?_) hA'_le_P
    obtain ⟨b, hbW, hzb, hyb, rfl⟩ := (hA'mem g).mp hg
    exact eichler_mem_elementaryGroup Q y b
  have hsup_le_K : A ⊔ A' ≤ elementaryGroup Q ⊓ P := sup_le hA_le_K hA'_le_K
  have hA'_normalizes : A' ≤ Subgroup.normalizer (A : Set (V ≃ₗ[F] V)) := by
    rw [Subgroup.le_normalizer_iff]
    intro g hg h hh
    obtain ⟨b, hbW, hzb, hyb, rfl⟩ := (hA'mem g).mp hg
    obtain ⟨a, haW, hza, rfl⟩ := (hAmem h).mp hh
    have hgA' : eichler Q y b ∈ A' := (hA'mem _).mpr ⟨b, hbW, hzb, hyb, rfl⟩
    have hgz : eichler Q y b z = z := by
      rw [eichler_apply hy hyb]
      simp [hzy, hzb]
    have hgaW : eichler Q y b a ∈ W := (hA'_le_P hgA').1 a haW
    have hgO : eichler Q y b ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      eichler_mem_orthogonalGroup Q y b
    have hgz' : (eichler Q y b)⁻¹ z = z := by
      refine (eichler Q y b).injective ?_
      rw [LinearEquiv.apply_inv_apply', hgz]
    have hginvO : (eichler Q y b)⁻¹ ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      Subgroup.inv_mem _ hgO
    have hB : polar Q z (eichler Q y b a) = 0 := by
      have h := (polar_map_of_mem hginvO z (eichler Q y b a)).symm
      rw [hgz', LinearEquiv.inv_apply_apply', hza] at h
      exact h
    refine ⟨eichler Q y b a, hgaW, hB, ?_⟩
    have hconj := eichler_conj hgO z a
    rw [hgz] at hconj
    exact hconj.symm
  have hswap : eichler Q z y = eichler Q y z :=
    CFSG.RankThree.GF2n.Smith81.OrthC5.eichler_swap hz hy hzy
  have hA_cent : A ≤ Subgroup.centralizer
      ({eichler Q z y} : Set (V ≃ₗ[F] V)) := by
    intro g hg
    obtain ⟨a, haW, hza, rfl⟩ := (hAmem g).mp hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [eichler_mul hza hzy, eichler_mul hzy hza, add_comm a y]
  have hA'_cent : A' ≤ Subgroup.centralizer
      ({eichler Q z y} : Set (V ≃ₗ[F] V)) := by
    intro g hg
    obtain ⟨b, hbW, hzb, hyb, rfl⟩ := (hA'mem g).mp hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [hswap]
    have hyz' : polar Q y z = 0 := by rw [polar_comm, hzy]
    rw [eichler_mul hyb hyz', eichler_mul hyz' hyb, add_comm b z]
  have hsup_cent : A ⊔ A' ≤ Subgroup.centralizer
      ({eichler Q z y} : Set (V ≃ₗ[F] V)) := sup_le hA_cent hA'_cent
  have hA2 : IsPGroup 2 A := by
    refine IsPGroup.of_exponent_dvd_pow (n := 1) ?_
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun g => ?_
    have hgroot : (g : V ≃ₗ[F] V) ∈ rootGroup Q z := by
      obtain ⟨a, haW, hza, hga⟩ := (hAmem (g : V ≃ₗ[F] V)).mp g.2
      rw [← hga]
      exact eichler_mem_rootGroup hza
    exact Subtype.ext (by simpa [pow_two] using
      sq_eq_one_of_mem_rootGroup h2 hgroot)
  have hA'2 : IsPGroup 2 A' := by
    refine IsPGroup.of_exponent_dvd_pow (n := 1) ?_
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun g => ?_
    have hgroot : (g : V ≃ₗ[F] V) ∈ rootGroup Q y := by
      obtain ⟨b, hbW, hzb, hyb, hgb⟩ := (hA'mem (g : V ≃ₗ[F] V)).mp g.2
      rw [← hgb]
      exact eichler_mem_rootGroup hyb
    exact Subtype.ext (by simpa [pow_two] using
      sq_eq_one_of_mem_rootGroup h2 hgroot)
  have hsup2 : IsPGroup 2 ↥Asup :=
    IsPGroup.to_sup_of_normal_left' hA2 hA'2 hA'_normalizes
  have hInfCard : Nat.card ↥Ainf ≤ 2 := by
    have hsub : Ainf ≤ Subgroup.zpowers (eichler Q z y) := by
      intro g hg
      obtain ⟨hgA, hgA'⟩ := Subgroup.mem_inf.mp hg
      obtain ⟨a, haW, hza, hga⟩ := (hAmem g).mp hgA
      obtain ⟨b, hbW, hzb, hyb, hgb⟩ := (hA'mem g).mp hgA'
      have hv_eval : eichler Q z a f₂ = eichler Q y b f₂ := by rw [hga, hgb]
      rw [eichler_apply hz hza, eichler_apply hy hyb] at hv_eval
      simp only [hf₂z, hf₂y, zero_smul, one_smul, mul_zero, mul_one, add_zero] at hv_eval
      have hb_span : b ∈ Submodule.span F ({y, z} : Set V) := by
        rw [Submodule.mem_span_pair]
        refine ⟨polar Q f₂ b + Q b, -(polar Q f₂ a), ?_⟩
        have h1 : -(polar Q f₂ a • z) = b - (polar Q f₂ b + Q b) • y := by
          have hv' : f₂ + (-(polar Q f₂ a • z)) =
              f₂ + (b + -((polar Q f₂ b + Q b) • y)) := by
            simpa [sub_eq_add_neg, add_assoc] using hv_eval
          have h := add_left_cancel hv'
          simpa [sub_eq_add_neg] using h
        rw [neg_smul, h1]
        abel
      obtain ⟨c, d, hcd⟩ := Submodule.mem_span_pair.mp hb_span
      have hb_eq2 : b = d • z + c • y := by
        rw [← hcd]
        abel
      have hg_eq : g = eichler Q y (d • z) := by
        rw [← hgb, hb_eq2, eichler_add_smul_self hy (d • z) c]
      rcases hF d with hd | hd
      · rw [hg_eq, hd, zero_smul, eichler_zero_right]
        exact Subgroup.one_mem _
      · rw [hg_eq, hd, one_smul, hswap]
        exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩
    have hcard_zpowers : Nat.card (Subgroup.zpowers (eichler Q z y)) ≤ 2 := by
      have he2 : (eichler Q z y) ^ 2 = 1 := by
        rw [pow_two, eichler_mul hzy hzy, ← two_smul F y, h2, zero_smul]
        exact eichler_zero_right Q z
      have hdvd : orderOf (eichler Q z y) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr he2
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) hdvd
    exact le_trans (Subgroup.card_le_of_le hsub) hcard_zpowers
  have hprod_gen : Nat.card (A' ⊔ A : Subgroup (V ≃ₗ[F] V)) *
      Nat.card (A' ⊓ A : Subgroup (V ≃ₗ[F] V)) = Nat.card A' * Nat.card A := by
    have hr : A.relIndex A' = A.relIndex (A' ⊔ A) := by
      have hnormA : (A.subgroupOf A').Normal :=
        Subgroup.normal_subgroupOf_of_le_normalizer hA'_normalizes
      have hnormAsup : (A.subgroupOf (A' ⊔ A)).Normal :=
        Subgroup.normal_subgroupOf_sup_of_le_normalizer hA'_normalizes
      exact Nat.card_congr
        (QuotientGroup.quotientInfEquivProdNormalizerQuotient A' A hA'_normalizes).toEquiv
    have h1 := Subgroup.relIndex_mul_card (H := A) (K := A')
    have h2 := Subgroup.relIndex_mul_card (H := A) (K := A' ⊔ A)
    rw [inf_eq_left.mpr (le_sup_right : A ≤ A' ⊔ A)] at h2
    rw [inf_comm] at h1
    rw [← h2, ← h1, hr]
    ring
  have hprod : Nat.card ↥Asup * Nat.card ↥Ainf = 128 := by
    have h := hprod_gen
    rw [sup_comm A' A, inf_comm A' A, hcardA, hcardA'] at h
    have h' : Nat.card ↥Asup * Nat.card ↥Ainf = 128 := by
      simpa [Asup, Ainf] using h
    exact h'
  have h64 : 64 ≤ Nat.card ↥Asup := by
    have h128 : 128 ≤ Nat.card ↥Asup * 2 := by
      calc 128 = Nat.card ↥Asup * Nat.card ↥Ainf := hprod.symm
        _ ≤ Nat.card ↥Asup * 2 := Nat.mul_le_mul_left _ hInfCard
    refine Nat.le_of_mul_le_mul_right ?_ (by norm_num : 0 < 2)
    simpa using h128
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card
    (p := 2) (n := 6) Nat.prime_two hsup2 (by simpa using h64)
  let T : Subgroup (V ≃ₗ[F] V) := H.map Asup.subtype
  refine ⟨T, ?_, ?_, ?_, ?_⟩
  · intro h hh
    obtain ⟨x, hxH, rfl⟩ := Subgroup.mem_map.mp hh
    exact (hsup_le_K x.2).1
  · intro h hh
    obtain ⟨x, hxH, rfl⟩ := Subgroup.mem_map.mp hh
    exact (hsup_le_K x.2).2
  · intro h hh
    obtain ⟨x, hxH, rfl⟩ := Subgroup.mem_map.mp hh
    exact Subgroup.mem_centralizer_singleton_iff.mp (hsup_cent x.2)
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hH]
    norm_num

end CFSG.ClassicalGroups.Orthogonal
