module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcFldLayer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81A3UniAut
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcFldBase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ModelGenB

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction CFSG.SeitzReduction.EPilot
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)


variable {τ : Tag} {K : Type} [Field K]

section Conj

variable {p : ℕ} [NeZero p] (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {A₀ : SL2 K}
  (hA₀ : A₀ ^ p = 1)

theorem frameHom_conj_frameSL2 (x : Fin (frameSize τ) → Multiplicative (ZMod p))
    (i : Fin (frameSize τ)) (B : SL2 K) :
    frameHom hτ hA₀ x * frameSL2 τ K i B * (frameHom hτ hA₀ x)⁻¹ =
      frameSL2 τ K i (A₀ ^ (Multiplicative.toAdd (x i)).val * B *
        (A₀ ^ (Multiplicative.toAdd (x i)).val)⁻¹) := by
  classical
  set E := frameHom hτ hA₀ with hE
  set C := A₀ ^ (Multiplicative.toAdd (x i)).val with hC
  obtain ⟨y, hy⟩ : ∃ y, y = (Pi.mulSingle i (x i))⁻¹ * x := ⟨_, rfl⟩
  have hyi : y i = 1 := by
    rw [hy, Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_eq_same, inv_mul_cancel]
  have hEx : E x = frameSL2 τ K i C * E y := by
    have hxy : x = Pi.mulSingle i (x i) * y := by rw [hy, mul_inv_cancel_left]
    conv_lhs => rw [hxy]
    rw [map_mul, frameHom_mulSingle, frameFactor_apply, sl2PowHom_apply]
  set S : Subgroup (Fin (frameSize τ) → Multiplicative (ZMod p)) :=
    (Subgroup.centralizer (Set.range (frameSL2 τ K i))).comap E with hS
  have hyS : y ∈ S := by
    rw [← Finset.univ_prod_mulSingle y]
    refine Subgroup.prod_mem _ fun j _ => ?_
    by_cases hj : j = i
    · subst hj
      rw [hyi, Pi.mulSingle_one]
      exact one_mem _
    · rw [hS, Subgroup.mem_comap, frameHom_mulSingle, Subgroup.mem_centralizer_iff]
      rintro _ ⟨B', rfl⟩
      rw [frameFactor_apply]
      exact frameSL2_commute hτ (Ne.symm hj) _ _
  have hEy : E y * frameSL2 τ K i B = frameSL2 τ K i B * E y :=
    (Subgroup.mem_centralizer_iff.1 hyS _ ⟨B, rfl⟩).symm
  rw [hEx, map_mul, map_mul, map_inv]
  calc frameSL2 τ K i C * E y * frameSL2 τ K i B * (frameSL2 τ K i C * E y)⁻¹
      = frameSL2 τ K i C * (E y * frameSL2 τ K i B) * (E y)⁻¹ * (frameSL2 τ K i C)⁻¹ := by
        group
    _ = _ := by rw [hEy]; group

end Conj

theorem map_uSL_ringEquiv (σ : K ≃+* K) (c : K) :
    Matrix.SpecialLinearGroup.map σ.toRingHom (uSL c) = uSL (σ c) := by
  refine Subtype.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_uSL]

theorem map_vSL_ringEquiv (σ : K ≃+* K) (c : K) :
    Matrix.SpecialLinearGroup.map σ.toRingHom (vSL c) = vSL (σ c) := by
  refine Subtype.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_vSL]

theorem map_HSL_neg_one_ringEquiv (σ : K ≃+* K) :
    Matrix.SpecialLinearGroup.map σ.toRingHom (HSL (-1)) = HSL (-1) := by
  refine Subtype.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_HSL]

theorem modelBGen_frame [Finite K] (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hK2 : ringChar K ≠ 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0)
    (hpQ : p ∣ Nat.card K ^ 2 - 1) {σ : K ≃+* K} (hσ : orderOf σ = p)
    (hout : entrywiseAdjointAut τ σ ∉
      (MulAut.conj : ↥(adjointGroup τ K) →* MulAut ↥(adjointGroup τ K)).range) :
    ModelGen.ModelBGen p (frameSize τ) ↥(adjointGroup τ K) (entrywiseAdjointAut τ σ) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Finite ↥(adjointGroup τ K) := generated_group_finite τ K
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hd := hrRootData_of hτ
  set X := ↥(adjointGroup τ K)
  set ψ := entrywiseAdjointAut τ σ with hψ
  have hpK0 := dvd_card_fixSubfield_sq_sub_one hp hσ hpQ
  haveI : Finite (fixSubfield σ) := Subtype.finite
  obtain ⟨B₀, hB₀⟩ := exists_orderOf_eq_sl2 hp hpK0
  set A₀ := fixIncl σ B₀ with hA₀def
  have hA₀ : orderOf A₀ = p := by rw [hA₀def, orderOf_injective _ (fixIncl_injective σ), hB₀]
  have hA₀p : A₀ ^ p = 1 := hA₀ ▸ pow_orderOf_eq_one A₀
  have hA₀1 : A₀ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hA₀
    exact hp.one_lt.ne hA₀
  have hA₀σ : Matrix.SpecialLinearGroup.map σ.toRingHom A₀ = A₀ := map_fixIncl σ B₀
  set E := frameHom hτ (K := K) hA₀p with hE
  have hEinj : Function.Injective E := frameHom_injective hτ hodd hA₀
  set i₀ := frame0 τ with hi₀
  set i₁ := frame1 hτ with hi₁
  have hi₁₀ : i₁ ≠ i₀ := frame1_ne_frame0 hτ
  set A : Subgroup X := E.range with hA
  set A₁ : Subgroup X := (frameFactor (τ := τ) (K := K) hA₀p i₀).range with hA₁
  set J : Subgroup X := (rootSpan τ K (perpRoots τ)).subgroupOf (adjointGroup τ K) with hJ
  set t : X := frameSL2 τ K i₀ (HSL (-1)) with ht
  have hAr : A = ⨆ i, (frameFactor (τ := τ) (K := K) hA₀p i).range := range_frameHom hτ hA₀p
  have hJq : CFSG.Open.IsQuasisimple ↥(rootSpan τ K (perpRoots τ)) := by
    rcases hτ with rfl | rfl | rfl | rfl
    · exact isQuasisimple_perpLevi_F4 hK2
    · exact isQuasisimple_perpLevi_E6 hK2
    · exact isQuasisimple_perpLevi_E7 hK2
    · exact isQuasisimple_perpLevi_E8 hK2
  have hpJ : p ∣ Nat.card ↥(rootSpan τ K (perpRoots τ)) := by
    have hmem := coe_frameSL2_mem_perp (K := K) hτ hi₁₀ A₀
    have hord : orderOf ((frameSL2 τ K i₁ A₀ : X) : ModGL τ K) = p := by
      rw [Subgroup.orderOf_coe, orderOf_injective _ (frameSL2_injective i₁), hA₀]
    rw [← hord]
    exact Subgroup.orderOf_dvd_natCard _ hmem
  have eJ : ↥J ≃* ↥(rootSpan τ K (perpRoots τ)) :=
    Subgroup.subgroupOfEquivOfLe (rootSpan_le_adjointGroup K _)
  have hJXq : CFSG.Open.IsQuasisimple ↥J :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Gen.Co15.isQuasisimple_of_equiv eJ.symm hJq
  have hpJX : p ∣ Nat.card ↥J := by rw [Nat.card_congr eJ.toEquiv]; exact hpJ
  have hfac0 : ∀ s, ∀ j ∈ rootSpan τ K (perpRoots τ),
      ((frameFactor (τ := τ) (K := K) hA₀p i₀ s : X) : ModGL τ K) * j =
        j * ((frameFactor (τ := τ) (K := K) hA₀p i₀ s : X) : ModGL τ K) := fun s j hj => by
    rw [frameFactor_apply]
    exact frameSL2_zero_commute_perp hτ _ hj
  have ht_coe : ((t : X) : ModGL τ K) = rootDiagUnit τ (Pi.mulSingle (highNode τ) (-1 : Kˣ)) := by
    rw [ht, coe_frameSL2_frame0 hτ, ← rootTorusSL2_highRoot hτ]
    rfl
  have htcomm : ∀ B : SL2 K, frameSL2 τ K i₀ B * t = t * frameSL2 τ K i₀ B := fun B => by
    rw [ht, ← map_mul, ← map_mul, HSL_neg_one_mul_comm]
  refine ⟨?_, hout, A, A₁, J, t, ?_, ?_, ?_, ?_, ?_, ?_, ?_, map_perpJ_entrywiseAdjointAut σ, ?_,
    glaPLayer_perpJ_inf_fix_ne_bot hτ hK2 hp hp2 σ hpK0, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [hψ, ← entrywiseAdjointAut_pow, ← hσ, pow_orderOf_eq_one, entrywiseAdjointAut_one]
  ·
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨u, hu⟩ := x.2
      obtain ⟨v, hv⟩ := y.2
      change (x : X) * y = y * x
      rw [← hu, ← hv, ← map_mul, ← map_mul, mul_comm]
    · rintro _ ⟨x, rfl⟩
      rw [← map_pow]
      have : x ^ p = 1 := by
        funext i
        apply Multiplicative.toAdd.injective
        rw [Pi.pow_apply, toAdd_pow, Pi.one_apply, toAdd_one, nsmul_eq_mul, ZMod.natCast_self,
          zero_mul]
      rw [this, map_one]
  ·
    rw [hA, card_range_of_injective' hEinj, Nat.card_pi, card_multiplicative_zmod,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ·
    intro a ha
    have hle : A ≤ fixSubgroup ψ := by
      rw [hAr]
      refine iSup_le fun i => ?_
      rintro _ ⟨s, rfl⟩
      rw [mem_fixSubgroup, frameFactor_apply, sl2PowHom_apply, hψ, entrywise_frameSL2, map_pow,
        hA₀σ]
    exact hle ha
  ·
    rw [hAr]
    exact le_iSup (fun i => (frameFactor (τ := τ) (K := K) hA₀p i).range) i₀
  ·
    have hinj : Function.Injective (frameFactor (τ := τ) (K := K) hA₀p i₀) :=
      (frameSL2_injective i₀).comp (sl2PowHom_injective hA₀)
    rw [hA₁, card_range_of_injective' hinj, card_multiplicative_zmod]
  ·
    refine CFSG.LocalAnalysis.GLTheoremA.KD264Gen.Co15.glaPComponent_subgroupOf _ hp _
      (rootSpan_le_adjointGroup K _) ?_ ?_ hJq hpJ
    · rintro l hl _ ⟨s, rfl⟩
      exact (hfac0 s l hl).symm
    · intro g hg hcomm l hl
      have hgc := hcomm (frameFactor (τ := τ) (K := K) hA₀p i₀ (Multiplicative.ofAdd 1)) ⟨_, rfl⟩
      rw [frameFactor_apply, sl2PowHom_apply, toAdd_ofAdd, ZMod.val_one, pow_one,
        coe_frameSL2_frame0 hτ] at hgc
      have hC : ∀ c : (AlgebraicClosure K)ˣ, c ≠ 1 → c ^ 2 ≠ 1 →
          toralCentralizer τ (AlgebraicClosure K) (Pi.mulSingle (highNode τ) c) ≤
            toralCentralizer τ (AlgebraicClosure K) (Pi.mulSingle (highNode τ) (-1)) :=
        fun c hc1 hc2 => toralCentralizer_mulSingle_le hc1 hc2 hd.abs_le hd.highRoot_highNode (-1)
      have hgt := centralizer_rootSL2_highRoot_le hτ hp hp2 hpK hA₀p hA₀1 hC
        (Subgroup.mem_inf.2 ⟨hg, Subgroup.mem_centralizer_singleton_iff.2 hgc⟩)
      exact (Subgroup.mem_normalizer_iff.1 (toralCentralizer_neg_one_le_normalizer hK2 hd.abs_le
        hd.eq_highRoot hd.highRoot_highNode hd.iform_eq_zero_iff hd.exists_nbr hgt) l).1 hl
  ·
    rw [hAr]
    refine iSup_le fun i => ?_
    by_cases hi : i = i₀
    · subst hi
      refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
      rintro _ ⟨s, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      exact Subtype.ext (hfac0 s j (Subgroup.mem_subgroupOf.1 hj)).symm
    · refine le_trans ?_ (Subgroup.le_normalizer (H := J))
      rintro _ ⟨s, rfl⟩
      rw [hJ, Subgroup.mem_subgroupOf, frameFactor_apply]
      exact coe_frameSL2_mem_perp hτ hi _
  ·
    intro a ha k hk hcore
    obtain ⟨x, rfl⟩ := ha
    set α : X →* X := (MulAut.conj (E x) * ψ ^ k).toMonoidHom with hα
    have hαj : ∀ j, α j = E x * (ψ ^ k) j * (E x)⁻¹ := fun j => rfl
    have hfix := CFSG.LocalAnalysis.GLTheoremA.H81.UniA3.eq_of_mul_inv_mem_glaPPrimeCoreOf hp hJXq
      hpJX α fun j hj => by
        have h1 := (GLAPPrimeCoreOf p J).inv_mem (hcore j hj)
        rw [mul_inv_rev, inv_inv] at h1
        rw [hαj]
        exact h1
    have hψk : ψ ^ k = entrywiseAdjointAut τ (σ ^ k) := by rw [hψ, entrywiseAdjointAut_pow]
    have hkey : ∀ i, i ≠ i₀ → ∀ B : SL2 K,
        A₀ ^ (Multiplicative.toAdd (x i)).val *
            Matrix.SpecialLinearGroup.map (σ ^ k).toRingHom B *
          (A₀ ^ (Multiplicative.toAdd (x i)).val)⁻¹ = B := by
      intro i hi B
      have hmem : frameSL2 τ K i B ∈ J := by
        rw [hJ, Subgroup.mem_subgroupOf]
        exact coe_frameSL2_mem_perp hτ hi B
      have h1 := hfix _ hmem
      rw [hαj, hψk, entrywise_frameSL2, frameHom_conj_frameSL2] at h1
      exact frameSL2_injective i h1
    have hC1 : ∀ i, i ≠ i₀ → A₀ ^ (Multiplicative.toAdd (x i)).val = 1 := by
      intro i hi
      set C := A₀ ^ (Multiplicative.toAdd (x i)).val with hC
      have hu := hkey i hi (uSL 1)
      have hv := hkey i hi (vSL 1)
      rw [map_uSL_ringEquiv, map_one] at hu
      rw [map_vSL_ringEquiv, map_one] at hv
      have hcen : C ∈ Subgroup.center (SL2 K) :=
        mem_center_of_commute_uSL_vSL (mul_inv_eq_iff_eq_mul.1 hu) (mul_inv_eq_iff_eq_mul.1 hv)
      have hCp : C ^ p = 1 := by rw [hC, ← pow_mul, mul_comm, pow_mul, hA₀p, one_pow]
      exact eq_one_of_mem_center_sl2_of_pow hodd hcen hCp
    have hx1 : ∀ i, i ≠ i₀ → x i = 1 := by
      intro i hi
      have h1 := orderOf_dvd_of_pow_eq_one (hC1 i hi)
      rw [hA₀] at h1
      have h0 : (Multiplicative.toAdd (x i)).val = 0 :=
        Nat.eq_zero_of_dvd_of_lt h1 (ZMod.val_lt _)
      apply Multiplicative.toAdd.injective
      rw [toAdd_one]
      exact (ZMod.val_eq_zero _).1 h0
    have hσk : σ ^ k = 1 := by
      refine RingEquiv.ext fun c => ?_
      have h1 := hkey i₁ hi₁₀ (uSL c)
      rw [hC1 i₁ hi₁₀, one_mul, inv_one, mul_one, map_uSL_ringEquiv] at h1
      have h2 := congrArg (fun g : SL2 K => (g : Matrix (Fin 2) (Fin 2) K) 0 1) h1
      simpa [coe_uSL] using h2
    have hk0 : k = 0 := by
      have h1 := orderOf_dvd_of_pow_eq_one hσk
      rw [hσ] at h1
      exact Nat.eq_zero_of_dvd_of_lt h1 hk
    refine ⟨hk0, ⟨x i₀, ?_⟩⟩
    have hx : x = Pi.mulSingle i₀ (x i₀) := by
      funext i
      by_cases hi : i = i₀
      · subst hi
        rw [Pi.mulSingle_eq_same]
      · rw [Pi.mulSingle_eq_of_ne hi, hx1 i hi]
    rw [hx, frameHom_mulSingle, Pi.mulSingle_eq_same]
  ·
    intro h1
    have h2 : HSL (-1 : Kˣ) = 1 := by
      apply frameSL2_injective i₀
      rw [map_one]
      exact h1
    have h3 := congrArg (fun g : SL2 K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h2
    simp [coe_HSL] at h3
    exact hK2 ((neg_one_eq_one_iff (R := K)).1 h3)
  ·
    rw [ht, ← map_pow, HSL_pow, show ((-1 : Kˣ) ^ 2) = 1 by norm_num, HSL_one, map_one]
  ·
    intro j hj
    rw [Subgroup.mem_centralizer_singleton_iff]
    refine Subtype.ext ?_
    have := frameSL2_zero_commute_perp (K := K) hτ (HSL (-1)) (Subgroup.mem_subgroupOf.1 hj)
    exact this.symm
  ·
    rw [hAr]
    refine iSup_le fun i => ?_
    rintro _ ⟨s, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, frameFactor_apply]
    by_cases hi : i = i₀
    · subst hi
      exact htcomm _
    · rw [ht]
      exact frameSL2_commute hτ hi _ _
  ·
    rw [ht, hψ, entrywise_frameSL2, map_HSL_neg_one_ringEquiv]

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

end
