module

public import CFSG.ClassicalInvolution.SmallOrth.Orth3Block
public import CFSG.ClassicalInvolution.SmallOrth.Orth3Center
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthEigen

public section

namespace CFSG.ClassicalGroups.Orthogonal.Small

open QuadraticMap CFSG.Open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Q3
  CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

instance finite_elementaryGroup [Finite K] [FiniteDimensional K V] :
    Finite ↥(elementaryGroup Q) := by
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun g : V ≃ₗ[K] V => (g : V → V)) DFunLike.coe_injective
  infer_instance

theorem componentOddCore_elementaryGroup_eq_bot [Finite K] [FiniteDimensional K V]
    (hK : Nat.card K = 3) (hQ : (polarBilin Q).Nondegenerate) :
    componentClassificationOddCore ↥(elementaryGroup Q) = ⊥ :=
  eq_bot_of_odd_normal_of_card_three hK hQ _ (OddCore.odd_card _)

section Blocks

variable {W W' : Submodule K V}

theorem oddCoreIn_map_blockHom_eq_bot [Finite K] [FiniteDimensional K V] (hK : Nat.card K = 3)
    (hQ : (polarBilin Q).Nondegenerate)
    (hcen : ∀ z ∈ Subgroup.center ↥(elementaryGroup Q), (z : V ≃ₗ[K] V) ∈ scalars K V)
    (hc : IsCompl W W') (horth : ∀ u ∈ W, ∀ w ∈ W', polar Q u w = 0) (hW' : W' ≠ ⊥) :
    oddCoreIn ((blockHom Q hc horth).range.map
      (QuotientGroup.mk' (Subgroup.center ↥(elementaryGroup Q)))) = ⊥ := by
  have hJ : componentClassificationOddCore ↥(elementaryGroup (Q.comp W.subtype)) = ⊥ :=
    componentOddCore_elementaryGroup_eq_bot hK (nondegenerate_comp_subtype hQ hc horth)
  have hrange : ((QuotientGroup.mk' (Subgroup.center ↥(elementaryGroup Q))).comp
      (blockHom Q hc horth)).range = (blockHom Q hc horth).range.map
        (QuotientGroup.mk' (Subgroup.center ↥(elementaryGroup Q))) :=
    (MonoidHom.map_range _ _).symm
  rw [← hrange]
  refine oddCoreIn_range_eq_bot_of_injective _ ?_ hJ
  rw [injective_iff_map_eq_one]
  intro φ hφ
  have hz : blockHom Q hc horth φ ∈ Subgroup.center ↥(elementaryGroup Q) :=
    (QuotientGroup.eq_one_iff _).mp hφ
  obtain ⟨c, hcs⟩ := mem_scalars.mp (hcen _ hz)
  obtain ⟨w', hw'W', hw'0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW'
  have h1 : orthExtend hc (φ : W ≃ₗ[K] W) (w' : V) = w' := by
    have := orthExtend_apply hc (φ : W ≃ₗ[K] W) 0 ⟨w', hw'W'⟩
    simpa using this
  have hc1 : c = 1 := by
    have h2 : orthExtend hc (φ : W ≃ₗ[K] W) w' = c • w' := hcs w'
    rw [h1] at h2
    have h3 : (1 - c) • w' = 0 := by rw [sub_smul, one_smul, ← h2, sub_self]
    have := (smul_eq_zero.mp h3).resolve_right hw'0
    exact (sub_eq_zero.mp this).symm
  apply blockHom_injective hc horth
  rw [map_one]
  refine Subtype.ext (LinearEquiv.ext fun x => ?_)
  rw [hcs x, hc1, one_smul]
  rfl

theorem blockHom_range_le_centralizer (hc : IsCompl W W')
    (horth : ∀ u ∈ W, ∀ w ∈ W', polar Q u w = 0) {g : ↥(elementaryGroup Q)}
    (hW : (g : V ≃ₗ[K] V) ∈ stabSub W) (hW' : (g : V ≃ₗ[K] V) ∈ stabSub W')
    (hgc : ∀ φ : ↥(elementaryGroup (Q.comp W.subtype)),
      resHom W ⟨g, hW⟩ * φ = φ * resHom W ⟨g, hW⟩) :
    (blockHom Q hc horth).range ≤ Subgroup.centralizer ({g} : Set ↥(elementaryGroup Q)) := by
  rintro _ ⟨φ, rfl⟩
  exact Subgroup.mem_centralizer_singleton_iff.mpr (blockHom_commute hc horth hW hW' hgc φ)

theorem oddCoreIn_centralizer_eq_bot_of_two_blocks [Finite K] [FiniteDimensional K V]
    (hK : Nat.card K = 3) (hQ : (polarBilin Q).Nondegenerate) (hdim : 3 ≤ Module.finrank K V)
    (hc : IsCompl W W') (horth : ∀ u ∈ W, ∀ w ∈ W', polar Q u w = 0)
    (hW0 : W ≠ ⊥) (hW'0 : W' ≠ ⊥) (g : ↥(elementaryGroup Q))
    (hstab : ∀ b : ↥(elementaryGroup Q), b * g = g * b →
      (b : V ≃ₗ[K] V) ∈ stabSub W ∧ (b : V ≃ₗ[K] V) ∈ stabSub W')
    (hgc : ∀ (hg : (g : V ≃ₗ[K] V) ∈ stabSub W) (φ : ↥(elementaryGroup (Q.comp W.subtype))),
      resHom W ⟨g, hg⟩ * φ = φ * resHom W ⟨g, hg⟩)
    (hgc' : ∀ (hg : (g : V ≃ₗ[K] V) ∈ stabSub W')
      (φ : ↥(elementaryGroup (Q.comp W'.subtype))),
      resHom W' ⟨g, hg⟩ * φ = φ * resHom W' ⟨g, hg⟩) :
    oddCoreIn (Subgroup.centralizer ({(QuotientGroup.mk g : ↥(elementaryGroup Q) ⧸
      Subgroup.center ↥(elementaryGroup Q))} : Set (↥(elementaryGroup Q) ⧸
        Subgroup.center ↥(elementaryGroup Q)))) = ⊥ := by
  have hcen : ∀ z ∈ Subgroup.center ↥(elementaryGroup Q), (z : V ≃ₗ[K] V) ∈ scalars K V :=
    fun z hz => mem_scalars_of_mem_center hK hQ hdim hz
  have hZ := isPGroup_center_elementaryGroup hK hQ hdim
  have horth' : ∀ u ∈ W', ∀ w ∈ W, polar Q u w = 0 := fun u hu w hw => by
    rw [polar_comm]
    exact horth w hw u hu
  have hgW := hstab g rfl
  refine oddCoreIn_centralizer_eq_bot_of_blocks hZ g (ι := Bool)
    (fun i => cond i (blockHom Q hc horth).range (blockHom Q hc.symm horth').range)
    ?_ ?_ ?_ ?_
  · intro i
    cases i
    · exact blockHom_range_le_centralizer hc.symm horth' hgW.2 hgW.1 (hgc' hgW.2)
    · exact blockHom_range_le_centralizer hc horth hgW.1 hgW.2 (hgc hgW.1)
  · intro i b hb x hx
    obtain ⟨hbW, hbW'⟩ := hstab b (Subgroup.mem_centralizer_singleton_iff.mp hb)
    cases i
    · exact conj_blockHom_mem_range hc.symm horth' hbW' hbW hx
    · exact conj_blockHom_mem_range hc horth hbW hbW' hx
  · intro i
    cases i
    · exact oddCoreIn_map_blockHom_eq_bot hK hQ hcen hc.symm horth' hW0
    · exact oddCoreIn_map_blockHom_eq_bot hK hQ hcen hc horth hW'0
  · intro ν hν hcomm
    obtain ⟨hνW, hνW'⟩ := hstab ν (Subgroup.mem_centralizer_singleton_iff.mp hν)
    obtain ⟨e₁, h₁⟩ := exists_pow_res_eq_one hK hQ hc horth hνW hνW'
      (fun φ => (hcomm true _ ⟨φ, rfl⟩).symm)
    obtain ⟨e₂, h₂⟩ := exists_pow_res_eq_one hK hQ hc.symm horth' hνW' hνW
      (fun φ => (hcomm false _ ⟨φ, rfl⟩).symm)
    refine ⟨e₁ + e₂, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow]
    refine pow_eq_one_of_pow_res_eq_one hc hνW hνW' ?_ ?_
    · rw [pow_add, pow_mul, h₁, one_pow]
    · rw [add_comm, pow_add, pow_mul, h₂, one_pow]

end Blocks

section Involution

open CFSG.ClassicalInvolution.ModelFacts

variable {i b : V ≃ₗ[K] V}

theorem mem_stabSub_plusSp (hb : b * i = i * b) : b ∈ stabSub (plusSp i) := fun x =>
  ⟨fun hx => map_mem_plusSp hb hx, fun hx => by
    simpa using map_mem_plusSp (inv_mul_eq_mul_inv_of hb) hx⟩

theorem mem_stabSub_minusSp (hb : b * i = i * b) : b ∈ stabSub (minusSp i) := fun x =>
  ⟨fun hx => map_mem_minusSp hb hx, fun hx => by
    simpa using map_mem_minusSp (inv_mul_eq_mul_inv_of hb) hx⟩

theorem mem_scalars_of_plusSp_eq_bot (h2 : (2 : K) ≠ 0) (hii : i * i = 1) (h : plusSp i = ⊥) :
    i ∈ scalars K V := by
  refine mem_scalars.mpr ⟨-1, fun x => ?_⟩
  have h1 : projP i x = 0 := by
    have := projP_mem hii x
    rw [h, Submodule.mem_bot] at this
    exact this
  have h3 := projP_add_projM (i := i) h2 x
  rw [h1, zero_add] at h3
  have hm : x ∈ minusSp i := by
    rw [← h3]
    exact projM_mem hii x
  rw [mem_minusSp.mp hm, neg_one_smul]

theorem mem_scalars_of_minusSp_eq_bot (h2 : (2 : K) ≠ 0) (hii : i * i = 1) (h : minusSp i = ⊥) :
    i ∈ scalars K V := by
  refine mem_scalars.mpr ⟨1, fun x => ?_⟩
  have h1 : projM i x = 0 := by
    have := projM_mem hii x
    rw [h, Submodule.mem_bot] at this
    exact this
  have h3 := projP_add_projM (i := i) h2 x
  rw [h1, add_zero] at h3
  have hm : x ∈ plusSp i := by
    rw [← h3]
    exact projP_mem hii x
  rw [mem_plusSp.mp hm, one_smul]

theorem resHom_plusSp (hg : i ∈ stabSub (plusSp i)) : resHom (plusSp i) ⟨i, hg⟩ = 1 :=
  LinearEquiv.ext fun x => Subtype.ext (mem_plusSp.mp x.2)

theorem resHom_minusSp_comm (hg : i ∈ stabSub (minusSp i)) (φ : minusSp i ≃ₗ[K] minusSp i) :
    resHom (minusSp i) ⟨i, hg⟩ * φ = φ * resHom (minusSp i) ⟨i, hg⟩ := by
  refine LinearEquiv.ext fun x => ?_
  have h1 : resHom (minusSp i) ⟨i, hg⟩ x = -x := Subtype.ext (mem_minusSp.mp x.2)
  have h2 : resHom (minusSp i) ⟨i, hg⟩ (φ x) = -(φ x) :=
    Subtype.ext (mem_minusSp.mp (φ x).2)
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, h1, h2, map_neg]

theorem oddCoreIn_centralizer_eq_bot_of_involution [Finite K] [FiniteDimensional K V]
    (hK : Nat.card K = 3) (hQ : (polarBilin Q).Nondegenerate) (hdim : 3 ≤ Module.finrank K V)
    (g : ↥(elementaryGroup Q)) (hg2 : (g : V ≃ₗ[K] V) * g = 1)
    (hg : (g : V ≃ₗ[K] V) ∉ scalars K V) :
    oddCoreIn (Subgroup.centralizer ({(QuotientGroup.mk g : ↥(elementaryGroup Q) ⧸
      Subgroup.center ↥(elementaryGroup Q))} : Set (↥(elementaryGroup Q) ⧸
        Subgroup.center ↥(elementaryGroup Q)))) = ⊥ := by
  obtain ⟨-, h2⟩ := three_eq_zero_two_ne_zero_of_card_eq_three hK
  have hio : (g : V ≃ₗ[K] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    elementaryGroup_le_orthogonalGroup Q g.2
  have hc := isCompl_plusSp_minusSp h2 hg2
  have horth : ∀ u ∈ plusSp (g : V ≃ₗ[K] V), ∀ w ∈ minusSp (g : V ≃ₗ[K] V), polar Q u w = 0 :=
    fun u hu w hw => polar_plusSp_minusSp h2 hio hu hw
  have hW0 : plusSp (g : V ≃ₗ[K] V) ≠ ⊥ := fun h => hg (mem_scalars_of_plusSp_eq_bot h2 hg2 h)
  have hW'0 : minusSp (g : V ≃ₗ[K] V) ≠ ⊥ := fun h => hg (mem_scalars_of_minusSp_eq_bot h2 hg2 h)
  refine oddCoreIn_centralizer_eq_bot_of_two_blocks hK hQ hdim hc horth hW0 hW'0 g ?_ ?_ ?_
  · intro b hb
    have hb' : (b : V ≃ₗ[K] V) * (g : V ≃ₗ[K] V) = (g : V ≃ₗ[K] V) * b :=
      congrArg Subtype.val hb
    exact ⟨mem_stabSub_plusSp hb', mem_stabSub_minusSp hb'⟩
  · intro hgs φ
    rw [resHom_plusSp hgs, one_mul, mul_one]
  · intro hgs φ
    exact resHom_minusSp_comm hgs φ

end Involution

end CFSG.ClassicalGroups.Orthogonal.Small
