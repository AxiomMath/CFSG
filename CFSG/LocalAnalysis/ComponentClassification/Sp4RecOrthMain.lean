module

public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecOrthUnique
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecOrthCore

public noncomputable section

namespace CFSG.ComponentClassification.Sp4Rec

open CFSG Subgroup Module
open scoped commutatorElement
open CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquare
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBFixedCentralQuotient (onQuotient fixedProjection)

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

omit [Finite K] [FiniteDimensional K V] in
theorem omegaScalars_le_center (Q : QuadraticForm K V) :
    omegaScalars Q ≤ center (orthogonalOmega Q) := by
  rintro z ⟨c, hc⟩
  rw [mem_center_iff]
  intro w
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  have hz : ∀ u, (z : V ≃ₗ[K] V) u = c • u := fun u => LinearMap.congr_fun hc u
  change (w : V ≃ₗ[K] V) ((z : V ≃ₗ[K] V) v) = (z : V ≃ₗ[K] V) ((w : V ≃ₗ[K] V) v)
  rw [hz, hz, map_smul]

theorem finite_linearEquiv' : Finite (V ≃ₗ[K] V) := by
  have : Finite V := Module.finite_of_finite K
  exact Finite.of_injective (fun g : V ≃ₗ[K] V => (g : V → V))
    (fun g h hgh => LinearEquiv.ext (congrFun hgh))

attribute [local instance] finite_linearEquiv'

theorem map_prodComm_of_right {G G' : Type*} [Group G] [Group G'] {N : Subgroup (G × G')}
    (h : N = (⊥ : Subgroup G).prod (N.map (MonoidHom.snd G G'))) :
    N.map (MulEquiv.prodComm : G × G' ≃* G' × G).toMonoidHom =
      ((N.map (MulEquiv.prodComm : G × G' ≃* G' × G).toMonoidHom).map
        (MonoidHom.fst G' G)).prod ⊥ := by
  have key : ∀ (a : G') (b : G),
      (a, b) ∈ N.map (MulEquiv.prodComm : G × G' ≃* G' × G).toMonoidHom ↔
        b = 1 ∧ a ∈ N.map (MonoidHom.snd G G') := by
    intro a b
    rw [mem_map_equiv]
    change (b, a) ∈ N ↔ _
    conv_lhs => rw [h]
    rw [mem_prod, mem_bot]
  ext ⟨a, b⟩
  rw [key, mem_prod, mem_bot]
  constructor
  · rintro ⟨rfl, ha⟩
    exact ⟨⟨(a, 1), (key a 1).mpr ⟨rfl, ha⟩, rfl⟩, rfl⟩
  · rintro ⟨⟨⟨a', b'⟩, hab', rfl⟩, hb⟩
    exact ⟨hb, ((key a' b').mp hab').2⟩

theorem pairConfig_orthogonalProj_false {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hdim : 7 ≤ finrank K V) {Q : QuadraticForm K V}
    (hQ : Q.polarBilin.Nondegenerate) {x : OrthogonalProj Q}
    {K₁ K₂ : Subgroup (OrthogonalProj Q)} (hc : PairConfig _ x K₁ K₂) : False := by
  classical
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hℓ.odd_of_ne_two hℓ2).pow
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_natCard hodd
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  set Z := omegaScalars Q with hZdef
  have hZ := omegaScalars_le_center Q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Z x
  set ψ := MulAut.conj g with hψdef
  have hψ : Z.map ψ.toMonoidHom = Z := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      change g * w * g⁻¹ ∈ Z
      rw [mem_center_iff.mp (hZ hw) g, mul_inv_cancel_right]
      exact hw
    · intro hz
      refine ⟨z, hz, ?_⟩
      change g * z * g⁻¹ = z
      rw [mem_center_iff.mp (hZ hz) g, mul_inv_cancel_right]
  have hfix : fixedSubgroup (onQuotient Z ψ hψ) =
      centralizer ({QuotientGroup.mk' Z g} : Set (OrthogonalProj Q)) := by
    ext y
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective Z y
    rw [mem_centralizer_singleton_iff]
    change onQuotient Z ψ hψ (QuotientGroup.mk' Z h) = QuotientGroup.mk' Z h ↔ _
    rw [CatalogueBFixedCentralQuotient.onQuotient_mk, hψdef, MulAut.conj_apply, map_mul, map_mul,
      map_inv, mul_inv_eq_iff_eq_mul]
    exact eq_comm
  set e₁ := MulEquiv.subgroupCongr hfix with he₁
  obtain ⟨M₁, M₂, hM₁, hM₂, hMne, hm₁, hm₂⟩ := exists_fixed_lifts Z hZ ψ hψ
    (CatalogueBAlternating.pComponent_map_equiv 2 e₁.symm _ hc.isPComponent_K)
    (CatalogueBAlternating.pComponent_map_equiv 2 e₁.symm _ hc.isPComponent_K') (by
      intro h
      apply hc.ne
      have h1 := subgroupOf_inj.mp (map_injective e₁.symm.injective h)
      rwa [inf_of_le_left hc.K_le, inf_of_le_left hc.K'_le] at h1)
  set π : fixedSubgroup ψ →* OrthogonalProj Q :=
    (fixedSubgroup (onQuotient Z ψ hψ)).subtype.comp (fixedProjection Z ψ hψ) with hπdef
  have hπ : ∀ y : fixedSubgroup ψ, π y = QuotientGroup.mk' Z (y : orthogonalOmega Q) :=
    fun y => rfl
  have hmemK : ∀ (L : Subgroup (OrthogonalProj Q)) (M : Subgroup (fixedSubgroup ψ)),
      M.map (fixedProjection Z ψ hψ) =
        (L.subgroupOf (centralizer {QuotientGroup.mk' Z g})).map e₁.symm.toMonoidHom →
      ∀ y ∈ M, π y ∈ L := by
    intro L M hML y hy
    have h1 : fixedProjection Z ψ hψ y ∈
        (L.subgroupOf (centralizer {QuotientGroup.mk' Z g})).map e₁.symm.toMonoidHom :=
      hML ▸ mem_map_of_mem _ hy
    obtain ⟨z, hz, hzy⟩ := h1
    have h3 : π y = (z : OrthogonalProj Q) := by
      rw [hπdef, MonoidHom.comp_apply, ← hzy]
      rfl
    rw [h3]
    exact mem_subgroupOf.mp hz
  have hsurjK : ∀ (L : Subgroup (OrthogonalProj Q)) (M : Subgroup (fixedSubgroup ψ)),
      L ≤ centralizer {QuotientGroup.mk' Z g} →
      M.map (fixedProjection Z ψ hψ) =
        (L.subgroupOf (centralizer {QuotientGroup.mk' Z g})).map e₁.symm.toMonoidHom →
      ∀ k ∈ L, ∃ y ∈ M, π y = k := by
    intro L M hLC hML k hk
    have h1 : e₁.symm ⟨k, hLC hk⟩ ∈ M.map (fixedProjection Z ψ hψ) := by
      rw [hML]
      exact mem_map_of_mem _ (mem_subgroupOf.mpr hk)
    obtain ⟨y, hy, hyk⟩ := h1
    refine ⟨y, hy, ?_⟩
    rw [hπdef, MonoidHom.comp_apply, hyk]
    rfl
  set A : V ≃ₗ[K] V := (g : V ≃ₗ[K] V) with hAdef
  have hcg : ∀ y : fixedSubgroup ψ, (y : orthogonalOmega Q) * g = g * y := by
    intro y
    have h1 : g * (y : orthogonalOmega Q) * g⁻¹ = y := y.2
    calc (y : orthogonalOmega Q) * g = g * y * g⁻¹ * g := by rw [h1]
      _ = g * y := by group
  have hx : ∀ y, π y * QuotientGroup.mk' Z g = QuotientGroup.mk' Z g * π y := fun y => by
    rw [hπ, ← map_mul, ← map_mul, hcg]
  have hfixmem : ∀ u : orthogonalOmega Q,
      (∀ v, (u : V ≃ₗ[K] V) (A v) = A ((u : V ≃ₗ[K] V) v)) → u ∈ fixedSubgroup ψ := by
    intro u hu
    change g * u * g⁻¹ = u
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change A ((u : V ≃ₗ[K] V) (A.symm v)) = (u : V ≃ₗ[K] V) v
    rw [← hu, LinearEquiv.apply_symm_apply]
  have hOmO : orthogonalOmega Q ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    Subgroup.commutator_le_self _
  set Y := CatalogueBOrthogonalScalarSquare.orthogonalOperatorCentralizer Q A.toLinearMap
    with hYdef
  have hκmem : ∀ y : fixedSubgroup ψ,
      (⟨((y : orthogonalOmega Q) : V ≃ₗ[K] V), hOmO (y : orthogonalOmega Q).2⟩ :
        TauCeti.QuadraticMap.orthogonalGroup Q) ∈ Y := by
    intro y v
    exact congrArg (fun u : orthogonalOmega Q => (u : V ≃ₗ[K] V) v) (hcg y)
  set κ : fixedSubgroup ψ →* Y :=
    { toFun := fun y => ⟨_, hκmem y⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl } with hκdef
  have hκ : Function.Injective κ := by
    intro y y' h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : Y => ((z : TauCeti.QuadraticMap.orthogonalGroup Q) : V ≃ₗ[K] V)) h
  set ι : Y →* (V ≃ₗ[K] V) := (TauCeti.QuadraticMap.orthogonalGroup Q).subtype.comp Y.subtype
    with hιdef
  have hικ : ∀ y : fixedSubgroup ψ, ι (κ y) = ((y : orthogonalOmega Q) : V ≃ₗ[K] V) :=
    fun y => rfl
  have hfromY : ∀ c : Y, ι c ∈ orthogonalOmega Q → c ∈ κ.range := by
    intro c hc
    refine ⟨⟨⟨ι c, hc⟩, hfixmem _ fun v => c.2 v⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rfl
  have hκn : κ.range.Normal := by
    constructor
    rintro _ ⟨y, rfl⟩ w
    apply hfromY
    have h1 : ι (w * κ y * w⁻¹) = ⁅ι w, ι (κ y)⁆ * ι (κ y) := by
      rw [commutatorElement_def, map_mul, map_mul, map_inv]
      group
    rw [h1, hικ]
    exact mul_mem (commutator_mem_commutator (w : TauCeti.QuadraticMap.orthogonalGroup Q).2
      (hOmO (y : orthogonalOmega Q).2)) (y : orthogonalOmega Q).2
  have hcomm : commutator Y ≤ κ.range := by
    intro c hc
    apply hfromY
    have h1 : (c : TauCeti.QuadraticMap.orthogonalGroup Q) ∈
        commutator (TauCeti.QuadraticMap.orthogonalGroup Q) := by
      have h2 : (commutator Y).map Y.subtype ≤
          commutator (TauCeti.QuadraticMap.orthogonalGroup Q) := by
        rw [_root_.commutator_def, _root_.commutator_def, map_commutator]
        exact commutator_mono le_top le_top
      exact h2 ⟨c, hc, rfl⟩
    show ι c ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆
    rw [← map_subtype_commutator]
    exact ⟨_, h1, rfl⟩
  have hπ1 : ∀ y, π y = 1 → ∃ c : K, ∀ v, ι (κ y) v = c • v := by
    intro y hy
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy
    obtain ⟨c, hc'⟩ := hy
    exact ⟨c, fun v => LinearMap.congr_fun hc' v⟩
  have hπx : ∀ y, π y = QuotientGroup.mk' Z g → ∃ c : K, ∀ v, A v = c • ι (κ y) v := by
    intro y hy
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hy
    obtain ⟨c, hc'⟩ := hy
    refine ⟨c, fun v => ?_⟩
    have h1 := LinearMap.congr_fun hc' v
    change ((y : orthogonalOmega Q) : V ≃ₗ[K] V).symm (A v) = c • v at h1
    rw [hικ, ← map_smul, ← h1, LinearEquiv.apply_symm_apply]
  have hAO : A ∈ TauCeti.QuadraticMap.orthogonalGroup Q := hOmO g.2
  have hx2 : g * g ∈ Z := by
    rw [← QuotientGroup.eq_one_iff (N := Z), QuotientGroup.mk_mul]
    have h1 := pow_orderOf_eq_one (QuotientGroup.mk' Z g)
    rw [hc.orderOf_x, pow_two] at h1
    exact h1
  obtain ⟨c, hcg⟩ := hx2
  have hAA : ∀ v, A (A v) = c • v := fun v => LinearMap.congr_fun hcg v
  obtain ⟨u, w, huw⟩ : ∃ u w : V, Q.polarBilin u w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨u, hu⟩ := exists_ne (0 : V)
    exact hu (hQ.1 u (fun w => hcon u w))
  have hcc : c * c = 1 := by
    have h1 : QuadraticMap.polar Q (A (A u)) (A (A w)) = QuadraticMap.polar Q u w := by
      rw [ClassicalGroups.Orthogonal.polar_map_of_mem hAO,
        ClassicalGroups.Orthogonal.polar_map_of_mem hAO]
    rw [hAA, hAA, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right] at h1
    have huw' : QuadraticMap.polar Q u w ≠ 0 := huw
    have h3 : (c * c - 1) * QuadraticMap.polar Q u w = 0 := by
      rw [smul_eq_mul, smul_eq_mul] at h1
      linear_combination h1
    exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right huw')
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hcc
  have hnonscalar : ∀ c' : K, A.toLinearMap ≠ c' • (1 : Module.End K V) := by
    intro c' hA
    have hgZ : g ∈ Z := ⟨c', hA⟩
    have h1 : QuadraticMap.polar Q (A u) (A w) = QuadraticMap.polar Q u w :=
      ClassicalGroups.Orthogonal.polar_map_of_mem hAO u w
    have hx1 : QuotientGroup.mk' Z g = 1 := (QuotientGroup.eq_one_iff _).mpr hgZ
    have := hc.orderOf_x
    rw [hx1, orderOf_one] at this
    exact absurd this (by norm_num)
  set dd : Kˣ := Units.mk0 c hc0 with hdd
  have hsquare : ∀ v, A (A v) = (dd : K) • v := hAA
  have hsim : ∀ v w, Q.polarBilin (A v) (A w) = ((1 : Kˣ) : K) * Q.polarBilin v w := by
    intro v w
    rw [Units.val_one, one_mul, QuadraticMap.polarBilin_apply_apply,
      QuadraticMap.polarBilin_apply_apply, ClassicalGroups.Orthogonal.polar_map_of_mem hAO]
  have hstr := CatalogueBOrthogonalScalarSquareStructure.scalar_square_centralizer_structure ℓ f
    hℓ hℓ2 hf hK (by omega) Q hQ A dd 1 hsquare hsim hnonscalar
  obtain ⟨-, -, hsplit, -⟩ := hstr
  have hMne' : M₁.map κ ≠ M₂.map κ := fun h => hMne (map_injective hκ h)
  have hN₁ := isPComponent_map_of_injective_normal κ hκ hM₁
  have hN₂ := isPComponent_map_of_injective_normal κ hκ hM₂
  rcases mul_self_eq_one_iff.mp hcc with hc1 | hc1
  ·
    have hdd1 : (dd : K) = ((1 : Kˣ) : K) ^ 2 := by
      rw [hdd, Units.val_mk0, hc1, Units.val_one, one_pow]
    obtain ⟨hcompl, hP, hM, hpos, -⟩ := hsplit 1 hdd1
    have hp : ((1 : Kˣ) : K) / (dd : K) = 1 := by
      rw [hdd, Units.val_mk0, hc1, div_one, Units.val_one]
    obtain ⟨-, hndP, hndM, e, he₁, he₂, -⟩ := hpos hp
    have hres : ∀ W : Submodule K V,
        (LinearMap.BilinForm.restrict Q.polarBilin W).Nondegenerate →
        (Q.comp W.subtype).polarBilin.Nondegenerate := by
      intro W hW
      have heq : (Q.comp W.subtype).polarBilin =
          LinearMap.BilinForm.restrict Q.polarBilin W := by
        rw [QuadraticMap.polarBilin_comp]
        ext x y
        rfl
      rw [heq]
      exact hW
    have hA₁ : ∀ v ∈ positiveSquareKernel A ((1 : Kˣ) : K), A v = ((1 : Kˣ) : K) • v := by
      intro v hv
      have h3 : (((1 : Kˣ) : K)⁻¹ • A.toLinearMap - (1 : Module.End K V)) v = 0 := hv
      rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero,
        Units.val_one, inv_one, one_smul] at h3
      rw [Units.val_one, one_smul]
      exact h3
    have hA₂ : ∀ v ∈ negativeSquareKernel A ((1 : Kˣ) : K), A v = (-((1 : Kˣ) : K)) • v := by
      intro v hv
      have h3 : (((1 : Kˣ) : K)⁻¹ • A.toLinearMap + (1 : Module.End K V)) v = 0 := hv
      rw [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
        add_eq_zero_iff_eq_neg, Units.val_one, inv_one, one_smul] at h3
      rw [Units.val_one, neg_one_smul]
      exact h3
    have hact₁ : ∀ (y : Y) (v : positiveSquareKernel A ((1 : Kˣ) : K)),
        ι y v = (((e y).1 : positiveSquareKernel A ((1 : Kˣ) : K) ≃ₗ[K]
          positiveSquareKernel A ((1 : Kˣ) : K)) v : V) := fun y v => (he₁ y v).symm
    have hact₂ : ∀ (y : Y) (v : negativeSquareKernel A ((1 : Kˣ) : K)),
        ι y v = (((e y).2 : negativeSquareKernel A ((1 : Kˣ) : K) ≃ₗ[K]
          negativeSquareKernel A ((1 : Kˣ) : K)) v : V) := fun y v => (he₂ y v).symm
    rcases CatalogueBProjectiveInvolutionProduct.pComponent_eq_left_or_right_factor 2
        ((M₁.map κ).map e.toMonoidHom) (CatalogueBAlternating.pComponent_map_equiv 2 e _ hN₁)
      with hl | hr
    · exact orth_left_false hodd hc π κ hκ ι hcomm hM₁ hM₂ hMne (hmemK K₁ M₁ hm₁)
        (hsurjK K₁ M₁ hc.K_le hm₁) (hsurjK K₂ M₂ hc.K'_le hm₂) hx hπ1 hπx hcompl hP hM hdim
        (hres _ hndP) (hres _ hndM) e hact₁ hact₂ (Units.ne_zero 1) hA₁ hA₂ hl
    · have hl' : (M₁.map κ).map (e.trans MulEquiv.prodComm).toMonoidHom =
          (((M₁.map κ).map (e.trans MulEquiv.prodComm).toMonoidHom).map
            (MonoidHom.fst _ _)).prod ⊥ := by
        rw [show (e.trans MulEquiv.prodComm).toMonoidHom =
          (MulEquiv.prodComm).toMonoidHom.comp e.toMonoidHom from rfl, ← map_map]
        exact map_prodComm_of_right hr
      exact orth_left_false hodd hc π κ hκ ι hcomm hM₁ hM₂ hMne (hmemK K₁ M₁ hm₁)
        (hsurjK K₁ M₁ hc.K_le hm₁) (hsurjK K₂ M₂ hc.K'_le hm₂) hx hπ1 hπx hcompl.symm hM hP
        hdim (hres _ hndM) (hres _ hndP) (e.trans MulEquiv.prodComm) (fun y v => hact₂ y v)
        (fun y v => hact₁ y v) (neg_ne_zero.mpr (Units.ne_zero 1)) hA₂
        (fun v hv => by rw [neg_neg]; exact hA₁ v hv) hl'
  ·
    have hm : ((1 : Kˣ) : K) / (dd : K) = -1 := by
      rw [hdd, Units.val_mk0, hc1, Units.val_one, div_neg, div_one]
    by_cases hsq : IsSquare (dd : K)
    · obtain ⟨b0, hb0⟩ := hsq
      have hb00 : b0 ≠ 0 := by
        rintro rfl
        apply dd.ne_zero
        rw [hb0, mul_zero]
      obtain ⟨-, hP, -, -, hneg⟩ := hsplit (Units.mk0 b0 hb00) (by
        rw [Units.val_mk0, sq]
        exact hb0)
      obtain ⟨-, -, -, -, -, -, e, -⟩ := hneg hm
      exact hMne' (map_injective e.injective (linEquiv_pComponent_eq
        (Submodule.one_le_finrank_iff.mpr hP)
        (CatalogueBAlternating.pComponent_map_equiv 2 e _ hN₁)
        (CatalogueBAlternating.pComponent_map_equiv 2 e _ hN₂)))
    · exact hMne' (orth_negative_nonsquare_pComponent_eq hodd Q hQ A.toLinearMap (dd : K)
        dd.ne_zero hsq
        (CatalogueBOrthogonalScalarSquareStructure.original_endomorphism_square A dd hsquare)
        (negative_square_adjoint Q A dd 1 dd.ne_zero hsquare hsim hm) (by omega) hN₁ hN₂)

end CFSG.ComponentClassification.Sp4Rec
