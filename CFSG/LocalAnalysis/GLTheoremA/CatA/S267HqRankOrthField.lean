module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267HqRankSp4
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBOdd
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalLowDimCoverageCases
import CFSG.RankThree.CentralLift.ClassicalCenterTrivial
import CFSG.LieType.SeitzGeneration.InnerOrthogonal

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.HqRank

open CFSG.Open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.ComponentInitial

section Abstract

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

open CFSG.ComponentClassification.CatalogueBOrthogonalFive
  (selfAdjointSymplecticAction_kernel_le_center) in
theorem six_le_twoLocalRank_of_projOrth_field [Finite K] [FiniteDimensional K V] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 3 ≤ f) (hK : Nat.card K = p ^ f)
    (Q : QuadraticForm K V) (hV7 : 7 ≤ Module.finrank K V) (hB : (polarBilin Q).Nondegenerate)
    {X : Type} [Group X] [Finite X] (φ : X →* ProjOrthDerived Q) (hφ : Function.Surjective φ) :
    6 ≤ GLATwoLocalRank p X := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K p := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp2)
  have hKodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  set d := Module.finrank K V with hd
  obtain ⟨vb, hvo, hv1, hlast⟩ := CFSG.RankThree.Classical.exists_orthogonal_basis_quad_eq hKodd
    hd.symm (by omega) Q hB one_ne_zero
  set v0 : V := vb ⟨0, by omega⟩ with hv0def
  set v1 : V := vb ⟨1, by omega⟩ with hv1def
  have hQ0 : Q v0 = 1 := hv1 _ (by simp; omega)
  have hQ1 : Q v1 = 1 := hv1 _ (by simp; omega)
  have hp01 : polar Q v0 v1 = 0 := hvo _ _ (by simp [Fin.ext_iff])
  have hv00 : v0 ≠ 0 := vb.ne_zero _
  set u : Fin 5 → V := fun i => vb ⟨i.val + 2, by omega⟩ with hudef
  set U : Submodule K V := Submodule.span K (Set.range u) with hUdef
  have huQ : ∀ j, Q (u j) ≠ 0 := by
    intro j
    by_cases hj : j.val + 2 + 1 < d
    · rw [hudef, hv1 _ hj]
      exact one_ne_zero
    · have : (⟨j.val + 2, by omega⟩ : Fin d) = ⟨d - 1, by omega⟩ := Fin.ext (by simp; omega)
      rw [hudef]
      simp only
      rw [this]
      exact hlast
  have hupol : ∀ i j, i ≠ j → polar Q (u i) (u j) = 0 := fun i j hij =>
    hvo _ _ (fun h => hij (Fin.ext (by have := congrArg Fin.val h; simp at this <;> omega)))
  have hu0 : ∀ j, polar Q v0 (u j) = 0 := fun j =>
    hvo _ _ (fun h => by have := congrArg Fin.val h; simp at this)
  have hu1 : ∀ j, polar Q v1 (u j) = 0 := fun j =>
    hvo _ _ (fun h => by have := congrArg Fin.val h; simp at this <;> omega)
  have hUperp : ∀ x ∈ U, polar Q v0 x = 0 ∧ polar Q v1 x = 0 := by
    intro x hx
    have hle : U ≤ LinearMap.ker (polarBilin Q v0) ⊓ LinearMap.ker (polarBilin Q v1) := by
      rw [hUdef, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact ⟨by simpa using hu0 j, by simpa using hu1 j⟩
    obtain ⟨h0, h1⟩ := hle hx
    exact ⟨by simpa using h0, by simpa using h1⟩
  have hsep : ∀ x ∈ U, (∀ y ∈ U, polar Q x y = 0) → x = 0 := by
    intro x hx hxy
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hx
    have hc : ∀ j, c j = 0 := by
      intro j
      have h := hxy (u j) (Submodule.subset_span ⟨j, rfl⟩)
      have hexp : polar Q (∑ i, c i • u i) (u j) = c j * polar Q (u j) (u j) := by
        rw [← polarBilin_apply_apply, map_sum, LinearMap.sum_apply,
          Finset.sum_eq_single j (fun i _ hij => by
            rw [map_smul, LinearMap.smul_apply, polarBilin_apply_apply, hupol i j hij,
              smul_zero])
            (by simp)]
        rw [map_smul, LinearMap.smul_apply, polarBilin_apply_apply, smul_eq_mul]
      rw [hexp, polar_self, nsmul_eq_mul] at h
      rcases mul_eq_zero.1 h with h | h
      · exact h
      · exfalso
        rcases mul_eq_zero.1 h with h' | h'
        · exact h2 (by exact_mod_cast h')
        · exact huQ j h'
    simp [hc]
  have hU5 : Module.finrank K U = 5 := by
    rw [hUdef, finrank_span_eq_card]
    · simp
    · exact vb.linearIndependent.comp _ (fun i j h => Fin.ext (by
        have := congrArg Fin.val h; simp at this <;> omega))
  have hrefl : LinearMap.BilinForm.IsRefl (polarBilin Q) := fun x y h => by
    rw [polarBilin_apply_apply] at h ⊢
    rw [polar_comm]
    exact h
  have hQU : (polarBilin (Q.comp U.subtype)).Nondegenerate := by
    refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft (fun x y h => ?_)).2
      fun x hx => Subtype.ext (hsep x x.2 fun y hy => ?_)
    · rw [polarBilin_apply_apply] at h ⊢
      rw [polar_comm]
      exact h
    · have := hx ⟨y, hy⟩
      rwa [polarBilin_apply_apply] at this
  have hres : (LinearMap.BilinForm.restrict (polarBilin Q) U).Nondegenerate := by
    refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft (fun x y h => ?_)).2
      fun x hx => Subtype.ext (hsep x x.2 fun y hy => ?_)
    · change polarBilin Q x y = 0 at h
      change polarBilin Q y x = 0
      exact hrefl _ _ h
    · have := hx ⟨y, hy⟩
      change polarBilin Q x y = 0 at this
      rwa [polarBilin_apply_apply] at this
  set W : Submodule K V := LinearMap.BilinForm.orthogonal (polarBilin Q) U with hWdef
  have hUW : IsCompl U W :=
    LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate hrefl hres
  have horth : ∀ x ∈ U, ∀ w ∈ W, polar Q x w = 0 := fun x hx w hw => by
    have := (LinearMap.BilinForm.mem_orthogonal_iff.1 hw) x hx
    rwa [polarBilin_apply_apply] at this
  have hv0W : v0 ∈ W := LinearMap.BilinForm.mem_orthogonal_iff.2 fun x hx => by
    rw [polarBilin_apply_apply, polar_comm]
    exact (hUperp x hx).1
  obtain ⟨g₀, hg₀Ω, hg₀0, hg₀1, hg₀x⟩ := exists_mem_orthDerived_double_sign h2 hQ0 hQ1 hp01
  have hg₀O : g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup Q := Subgroup.commutator_le_self _ hg₀Ω
  have hg₀U : ∀ x ∈ U, g₀ x = x := fun x hx => hg₀x x (hUperp x hx).1 (hUperp x hx).2
  have hpolg : ∀ x y, polar Q (g₀ x) (g₀ y) = polar Q x y := fun x y => by
    have hQg := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 hg₀O
    simp only [polar, ← map_add, hQg]
  have hg₀W : ∀ w ∈ W, g₀ w ∈ W := by
    intro w hw
    refine LinearMap.BilinForm.mem_orthogonal_iff.2 fun x hx => ?_
    rw [polarBilin_apply_apply, ← hg₀U x hx, hpolg]
    exact horth x hx w hw
  have hg₀sq : g₀ * g₀ = 1 := by
    refine LinearEquiv.toLinearMap_injective (vb.ext fun k => ?_)
    change g₀ (g₀ (vb k)) = vb k
    by_cases hk0 : k = ⟨0, by omega⟩
    · rw [hk0]
      change g₀ (g₀ v0) = v0
      rw [hg₀0, map_neg, hg₀0, neg_neg]
    by_cases hk1 : k = ⟨1, by omega⟩
    · rw [hk1]
      change g₀ (g₀ v1) = v1
      rw [hg₀1, map_neg, hg₀1, neg_neg]
    have h1 : g₀ (vb k) = vb k :=
      hg₀x _ (hvo _ _ (fun h => hk0 h.symm)) (hvo _ _ (fun h => hk1 h.symm))
    rw [h1, h1]
  set Zs := (scalars K V).subgroupOf (orthDerived Q) with hZs
  set π : orthDerived Q →* ProjOrthDerived Q := QuotientGroup.mk' Zs with hπ
  set t : ProjOrthDerived Q := π ⟨g₀, hg₀Ω⟩ with ht
  have ht2 : t ^ 2 = 1 := by
    rw [ht, ← map_pow, pow_two]
    have : (⟨g₀, hg₀Ω⟩ : orthDerived Q) * ⟨g₀, hg₀Ω⟩ = 1 := Subtype.ext hg₀sq
    rw [this, map_one]
  have ht1 : t ≠ 1 := by
    intro h
    have hmem := (QuotientGroup.eq_one_iff (N := Zs) _).1 h
    rw [hZs, mem_subgroupOf] at hmem
    obtain ⟨c, hc⟩ := mem_scalars.mp hmem
    have hu00 : u 0 ≠ 0 := vb.ne_zero _
    have h1 := hc (u 0)
    change g₀ (u 0) = c • u 0 at h1
    rw [hg₀U _ (Submodule.subset_span ⟨0, rfl⟩)] at h1
    have hc1 : c = 1 := by
      have h1' : (c - 1) • u 0 = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
      rcases smul_eq_zero.mp h1' with h1' | h1'
      · exact sub_eq_zero.mp h1'
      · exact absurd h1' hu00
    have h0 := hc v0
    change g₀ v0 = c • v0 at h0
    rw [hg₀0, hc1, one_smul] at h0
    have : (2 : K) • v0 = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← h0]
      exact neg_add_cancel v0
    rcases smul_eq_zero.mp this with h' | h'
    · exact h2 h'
    · exact hv00 h'
  obtain ⟨dd, ψ, e, -, -, hcomm, -, -⟩ := orthogonal_five_derived hKodd (Q.comp U.subtype) hQU hU5
  set h2' := CFSG.ComponentClassification.CatalogueBOddQuadratic.two_ne_zero_of_odd_card hKodd
  set act := CFSG.ComponentClassification.CatalogueBOrthogonalFive.selfAdjointSymplecticAction h2'
  let eqv : StatedSp 2 K ≃*
      (CFSG.ComponentClassification.CatalogueBOrthogonalFive.symplecticMultiplier (K := K)).ker :=
    (MulEquiv.subgroupCongr
      (CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic (n := 2) (K := K))).trans
      CFSG.ComponentClassification.CatalogueBOrthogonalFive.symplecticKernelEquiv.symm
  obtain ⟨hemb_inj, hemb_O, -, -⟩ := orthogonal_complement_elementary_embedding Q hUW horth
  let ext' : TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype) →*
      TauCeti.QuadraticMap.orthogonalGroup Q :=
    ((orthExtend hUW).comp (TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype)).subtype
      ).codRestrict _ (fun g => hemb_O g g.2)
  let Φ₀ : StatedSp 2 K →* TauCeti.QuadraticMap.orthogonalGroup Q :=
    ext'.comp (e.symm.toMonoidHom.comp (act.comp eqv.toMonoidHom))
  have hΦ₀ : ∀ x, (Φ₀ x : V ≃ₗ[K] V) ∈ orthDerived Q := by
    intro x
    have h1 : e.symm (act (eqv x)) ∈
        commutator (TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype)) := by
      rw [hcomm]
      exact ⟨act (eqv x), ⟨eqv x, rfl⟩, rfl⟩
    have hle : (commutator (TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype))).map ext' ≤
        commutator (TauCeti.QuadraticMap.orthogonalGroup Q) := by
      rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator]
      exact Subgroup.commutator_mono le_top le_top
    have h3 := hle ⟨_, h1, rfl⟩
    rw [orthDerived, ← Subgroup.map_subtype_commutator]
    exact ⟨_, h3, rfl⟩
  let Φ : StatedSp 2 K →* orthDerived Q :=
    ((TauCeti.QuadraticMap.orthogonalGroup Q).subtype.comp Φ₀).codRestrict (orthDerived Q) hΦ₀
  let Ψ : StatedSp 2 K →* ProjOrthDerived Q := π.comp Φ
  have hΦval : ∀ x, ((Φ x : orthDerived Q) : V ≃ₗ[K] V) =
      orthExtend hUW ((e.symm (act (eqv x)) : _) : ↥U ≃ₗ[K] ↥U) := fun x => rfl
  have hcommΦ : ∀ x, ((Φ x : orthDerived Q) : V ≃ₗ[K] V) * g₀ = g₀ * (Φ x : orthDerived Q) := by
    intro x
    rw [hΦval]
    refine LinearEquiv.ext fun v => ?_
    obtain ⟨a, w, rfl⟩ := exists_add_of_isCompl hUW v
    have e1 : g₀ ((a : V) + w) = (a : V) + ((⟨g₀ w, hg₀W w w.2⟩ : W) : V) := by
      rw [map_add, hg₀U a a.2]
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, e1, orthExtend_apply, orthExtend_apply,
      map_add, hg₀U _ (Subtype.prop _)]
  have hJt : ∀ x, Ψ x * t = t * Ψ x := by
    intro x
    change π (Φ x) * π ⟨g₀, hg₀Ω⟩ = π ⟨g₀, hg₀Ω⟩ * π (Φ x)
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcommΦ x)
  have hto : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have hU₀ : IsPGroup 2 (zpowers t) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hto, pow_one])
  have hU₀ne : zpowers t ≠ ⊥ := by
    intro h
    have : t ∈ zpowers t := mem_zpowers t
    rw [h, mem_bot] at this
    exact ht1 this
  have hJU : Ψ.range ≤ normalizer ((zpowers t : Subgroup (ProjOrthDerived Q)) : Set _) := by
    rintro _ ⟨x, rfl⟩
    refine centralizer_le_normalizer _ (mem_centralizer_iff.2 fun y hy => ?_)
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
    exact (Commute.zpow_left (show Commute t (Ψ x) from (hJt x).symm) k).eq
  have hcenter : center (StatedSp 2 K) =
      (StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf (StatedSp 2 K) := by
    rw [show StatedSp 2 K = TauCeti.GLSymplectic (Fin 2) K from
      CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic (n := 2) (K := K)]
    exact CFSG.ClassicalGroups.Symplectic.center_GLSymplectic_eq (n := 2) (K := K)
  have hker : Ψ.ker ≤ (StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf (StatedSp 2 K) := by
    intro x hx
    rw [← hcenter]
    have h1 : Φ x ∈ Zs := (QuotientGroup.eq_one_iff (N := Zs) _).1 hx
    rw [hZs, mem_subgroupOf] at h1
    obtain ⟨c, hc⟩ := mem_scalars.mp h1
    have hv0' := hc v0
    have hdec : v0 = ((0 : U) : V) + ((⟨v0, hv0W⟩ : W) : V) := by simp
    rw [hΦval, hdec, orthExtend_apply] at hv0'
    simp only [map_zero, ZeroMemClass.coe_zero, zero_add] at hv0'
    have hc1 : c = 1 := by
      have h1' : (c - 1) • v0 = 0 := by rw [sub_smul, ← hv0', one_smul, sub_self]
      rcases smul_eq_zero.mp h1' with h1' | h1'
      · exact sub_eq_zero.mp h1'
      · exact absurd h1' hv00
    have hΦ1 : ((Φ x : orthDerived Q) : V ≃ₗ[K] V) = 1 :=
      LinearEquiv.ext fun v => by rw [hc, hc1, one_smul]; rfl
    have hh1 : ((e.symm (act (eqv x)) : _) : ↥U ≃ₗ[K] ↥U) = 1 :=
      hemb_inj (by rw [← hΦval, hΦ1, map_one])
    have hact : act (eqv x) = 1 := by
      have : e.symm (act (eqv x)) = 1 := Subtype.ext hh1
      simpa using this
    have hmemc := selfAdjointSymplecticAction_kernel_le_center h2' hact
    rw [mem_center_iff]
    intro y
    apply eqv.injective
    rw [map_mul, map_mul]
    exact mem_center_iff.1 hmemc (eqv y)
  let ρ : Ψ.range →* StatedProj (StatedSp 2 K) :=
    (QuotientGroup.map Ψ.ker ((StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf (StatedSp 2 K))
      (MonoidHom.id _) (fun x hx => hker hx)).comp
      (QuotientGroup.quotientKerEquivRange Ψ).symm.toMonoidHom
  have hρ : Function.Surjective ρ := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    refine ⟨QuotientGroup.quotientKerEquivRange Ψ (QuotientGroup.mk g), ?_⟩
    simp only [ρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    rfl
  exact le_twoLocalRank_of_section hp hU₀ hU₀ne hJU
    (fun X' _ _ φ' hφ' => six_le_pRank_of_surj_PSp4 hp hp2 hK hf (ρ.comp φ') (hρ.comp hφ')) φ hφ

end Abstract

section Models

theorem six_le_twoLocalRank_B_field {n : ℕ} (hn : 3 ≤ n) (Q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.B n Q).Valid) (hq2 : Q.p ≠ 2) (hr : 3 ≤ Q.exponent) {X : Type}
    [Group X] [Finite X] (φ : X →* (TauCeti.CFSGIndex.lie ⟨.B n Q, hv⟩).Group)
    (hφ : Function.Surjective φ) : 6 ≤ GLATwoLocalRank Q.p X := by
  haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
  set Fx := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B n Q, hv⟩)
  haveI : Finite Fx := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  have hcard : Nat.card Fx = Q.p ^ Q.exponent := by
    rw [CFSG.LieType.SeitzGeneration.card_fixedField_eq]
    simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
  let eB := CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj_odd n Q hv hq2
    (by omega)
  have h2 : (2 : Fx) ≠ 0 := Ring.two_ne_zero (by
    have : CharP Fx Q.p :=
      finite_field_prime_power_characteristic Q.prime_p Q.exponent_pos hcard
    rw [ringChar.eq Fx Q.p]; exact hq2)
  obtain ⟨e₂⟩ := CFSG.RankThree.CentralLift.nonempty_statedProj_mulEquiv_projOrthDerived
    (CFSG.LieType.Universal.Spin.coe_quadOdd n Fx)
  have hdim : 7 ≤ Module.finrank Fx (Fin n ⊕ Fin n ⊕ Unit → Fx) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit]
    omega
  let e := eB.trans e₂
  exact six_le_twoLocalRank_of_projOrth_field Q.prime_p hq2 hr hcard _ hdim
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadOdd n Fx h2) (e.toMonoidHom.comp φ)
    (e.surjective.comp hφ)

theorem six_le_twoLocalRank_D_field {n : ℕ} (hn : 4 ≤ n) (Q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.D n Q).Valid) (hq2 : Q.p ≠ 2) (hr : 3 ≤ Q.exponent) {X : Type}
    [Group X] [Finite X] (φ : X →* (TauCeti.CFSGIndex.lie ⟨.D n Q, hv⟩).Group)
    (hφ : Function.Surjective φ) : 6 ≤ GLATwoLocalRank Q.p X := by
  haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
  set Fx := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D n Q, hv⟩)
  haveI : Finite Fx := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  have hcard : Nat.card Fx = Q.p ^ Q.exponent := by
    rw [CFSG.LieType.SeitzGeneration.card_fixedField_eq]
    simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
  let eD := CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid n Q hv
  obtain ⟨e₂⟩ := CFSG.RankThree.CentralLift.nonempty_statedProj_mulEquiv_projOrthDerived
    (CFSG.LieType.Universal.Spin.coe_quadPlus n Fx)
  have hdim : 7 ≤ Module.finrank Fx (Fin n ⊕ Fin n → Fx) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  let e := eD.trans e₂
  exact six_le_twoLocalRank_of_projOrth_field Q.prime_p hq2 hr hcard _ hdim
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus n Fx) (e.toMonoidHom.comp φ)
    (e.surjective.comp hφ)

theorem six_le_twoLocalRank_twistedD_field {n : ℕ} (hn : 4 ≤ n) (Q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedD n Q).Valid) (hq2 : Q.p ≠ 2) (hr : 3 ≤ Q.exponent)
    {X : Type} [Group X] [Finite X] (φ : X →* (TauCeti.CFSGIndex.lie ⟨.twistedD n Q, hv⟩).Group)
    (hφ : Function.Surjective φ) : 6 ≤ GLATwoLocalRank Q.p X := by
  haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
  set Fx := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD n Q, hv⟩)
  haveI : Finite Fx := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  have hcard : Nat.card Fx = Q.p ^ Q.exponent := by
    rw [CFSG.LieType.SeitzGeneration.card_fixedField_eq]
    simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
  obtain ⟨b, c, hirr, ⟨eD⟩⟩ :=
    CFSG.RankThree.PartTwo.Census.Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid
      n Q hv
  obtain ⟨e₂⟩ := CFSG.RankThree.CentralLift.nonempty_statedProj_mulEquiv_projOrthDerived
    (CFSG.LieType.Universal.Spin.coe_quadMinus n Fx b c)
  have hdim : 7 ≤ Module.finrank Fx (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → Fx) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
    omega
  let e := eD.trans e₂
  exact six_le_twoLocalRank_of_projOrth_field Q.prime_p hq2 hr hcard _ hdim
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite n Fx hirr)
    (e.toMonoidHom.comp φ) (e.surjective.comp hφ)

end Models

end CFSG.LocalAnalysis.GLTheoremA.S267.HqRank
