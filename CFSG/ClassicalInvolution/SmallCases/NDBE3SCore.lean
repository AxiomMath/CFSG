module

public import CFSG.ClassicalInvolution.SmallCases.NDBE3SModel
public import CFSG.ClassicalInvolution.SmallCases.NDBE1S

public section

namespace CFSG.ClassicalInvolution.NDB.SpinStd

open CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Balance.StrongBalance.Orth
  CFSG.ClassicalInvolution.Asc77 CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.NDB.FourFrame CFSG.ClassicalInvolution.NDB.ExoticModel QuadraticMap
open scoped MatrixGroups

variable {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V} {m : ℕ}

theorem commutator_le_self' {G : Type*} [Group G] (J : Subgroup G) : ⁅J, J⁆ ≤ J := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact J.mul_mem (J.mul_mem (J.mul_mem ha hb) (J.inv_mem ha)) (J.inv_mem hb)

omit [Finite F] [FiniteDimensional F V] in
theorem exists_frames (h2 : (2 : F) ≠ 0) (F₀ : HypFrame Q m) {i₀ i₁ i₂ : Fin m} (h01 : i₀ ≠ i₁)
    (h12 : i₁ ≠ i₂) (h02 : i₀ ≠ i₂) {θ : SL(3, F) →* spinGroup Q}
    (hker : θ.ker ≤ Subgroup.center SL(3, F)) {c : SL(3, F)}
    (hpair : (((B12 F).map (MulAut.conj c⁻¹).toMonoidHom).map θ =
          (F₀.longSL2 h01 true false).range ∧
        ((B23 F).map (MulAut.conj c⁻¹).toMonoidHom).map θ = (F₀.longSL2 h12 true false).range) ∨
      (((B12 F).map (MulAut.conj c⁻¹).toMonoidHom).map θ = (F₀.longSL2 h12 true false).range ∧
        ((B23 F).map (MulAut.conj c⁻¹).toMonoidHom).map θ =
          (F₀.longSL2 h01 true false).range)) :
    ∃ frX frY : Frame Q, spinAction Q (θ (c⁻¹ * SL3.u₁ * c)) = frX.La (-1) ∧
      spinAction Q (θ (c⁻¹ * SL3.u₂ * c)) = frY.La (-1) ∧
      (∃ P : HypPair Q, P.e ∈ frX.span ∧ P.e ∈ frY.span ∧ P.f ∈ frX.span ∧ P.f ∈ frY.span) ∧
      ∃ u ∈ frX.span, u ∈ frY.perp ∧ Q u ≠ 0 := by
  have hrel := frameRel_sl3 h2 θ hker c
  have hκy := thetaC_π_u₁ θ c
  have hy₁m : θ (c⁻¹ * SL3.u₁ * c) ∈ ((B12 F).map (MulAut.conj c⁻¹).toMonoidHom).map θ :=
    Subgroup.mem_map_of_mem θ (SL3.conj_mem c)
  have hy₂m : θ (c⁻¹ * SL3.u₂ * c) ∈ ((B23 F).map (MulAut.conj c⁻¹).toMonoidHom).map θ :=
    Subgroup.mem_map_of_mem θ ⟨SL3.u₂, SL3.u₂_mem, by simp⟩
  have hy₂sq : θ (c⁻¹ * SL3.u₂ * c) * θ (c⁻¹ * SL3.u₂ * c) = 1 := by
    rw [← hκy]
    calc θ (c⁻¹ * SL3.π * c) * θ (c⁻¹ * SL3.u₁ * c) * (θ (c⁻¹ * SL3.π * c))⁻¹ *
          (θ (c⁻¹ * SL3.π * c) * θ (c⁻¹ * SL3.u₁ * c) * (θ (c⁻¹ * SL3.π * c))⁻¹) =
        θ (c⁻¹ * SL3.π * c) * (θ (c⁻¹ * SL3.u₁ * c) * θ (c⁻¹ * SL3.u₁ * c)) *
          (θ (c⁻¹ * SL3.π * c))⁻¹ := by group
      _ = 1 := by rw [hrel.sq]; group
  have hy₂1 : θ (c⁻¹ * SL3.u₂ * c) ≠ 1 := by
    rw [← hκy]
    intro h
    apply hrel.ne_one
    calc θ (c⁻¹ * SL3.u₁ * c) = (θ (c⁻¹ * SL3.π * c))⁻¹ *
          (θ (c⁻¹ * SL3.π * c) * θ (c⁻¹ * SL3.u₁ * c) * (θ (c⁻¹ * SL3.π * c))⁻¹) *
          θ (c⁻¹ * SL3.π * c) := by group
      _ = 1 := by rw [h]; group
  have hP₀ : (vecPair F₀ i₁).e ∈ (F₀.toFrame h01 true false).span ∧
      (vecPair F₀ i₁).e ∈ (F₀.toFrame h12 true false).span ∧
      (vecPair F₀ i₁).f ∈ (F₀.toFrame h01 true false).span ∧
      (vecPair F₀ i₁).f ∈ (F₀.toFrame h12 true false).span :=
    ⟨vec_mem_span_snd F₀ h01 true, vec_mem_span_fst F₀ h12 true, vec_mem_span_snd F₀ h01 false,
      vec_mem_span_fst F₀ h12 false⟩
  have hne : (1 : F) ≠ 0 := one_ne_zero
  rcases hpair with ⟨hA, hB⟩ | ⟨hA, hB⟩
  · refine ⟨F₀.toFrame h01 true false, F₀.toFrame h12 true false, ?_, ?_,
      ⟨vecPair F₀ i₁, hP₀⟩, F₀.vec i₀ true + F₀.vec i₀ false,
      add_mem (vec_mem_span_fst F₀ h01 true) (vec_mem_span_fst F₀ h01 false),
      add_mem (vec_mem_perp F₀ h12 h01 h02 true) (vec_mem_perp F₀ h12 h01 h02 false),
      by rw [map_vec_add]; exact hne⟩
    · rw [eq_longSL2_neg_one F₀ h2 h01 (hA ▸ hy₁m) hrel.sq hrel.ne_one,
        spinAction_longSL2_neg_one]
    · rw [eq_longSL2_neg_one F₀ h2 h12 (hB ▸ hy₂m) hy₂sq hy₂1, spinAction_longSL2_neg_one]
  · refine ⟨F₀.toFrame h12 true false, F₀.toFrame h01 true false, ?_, ?_,
      ⟨vecPair F₀ i₁, hP₀.2.1, hP₀.1, hP₀.2.2.2, hP₀.2.2.1⟩, F₀.vec i₂ true + F₀.vec i₂ false,
      add_mem (vec_mem_span_snd F₀ h12 true) (vec_mem_span_snd F₀ h12 false),
      add_mem (vec_mem_perp F₀ h01 h02.symm h12.symm true)
        (vec_mem_perp F₀ h01 h02.symm h12.symm false),
      by rw [map_vec_add]; exact hne⟩
    · rw [eq_longSL2_neg_one F₀ h2 h12 (hA ▸ hy₁m) hrel.sq hrel.ne_one,
        spinAction_longSL2_neg_one]
    · rw [eq_longSL2_neg_one F₀ h2 h01 (hB ▸ hy₂m) hy₂sq hy₂1, spinAction_longSL2_neg_one]

theorem core (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F) (hQ : (polarBilin Q).Nondegenerate)
    (hV : 7 ≤ Module.finrank F V) (hrange : (spinAction Q).range = elementaryGroup Q)
    [Group.IsPerfect (spinGroup Q)] (F₀ : HypFrame Q m) {i₀ i₁ i₂ : Fin m} (h01 : i₀ ≠ i₁)
    (h12 : i₁ ≠ i₂) (h02 : i₀ ≠ i₂) {θ : SL(3, F) →* spinGroup Q}
    (hker : θ.ker ≤ Subgroup.center SL(3, F)) {c : SL(3, F)}
    (hpair : (((B12 F).map (MulAut.conj c⁻¹).toMonoidHom).map θ =
          (F₀.longSL2 h01 true false).range ∧
        ((B23 F).map (MulAut.conj c⁻¹).toMonoidHom).map θ = (F₀.longSL2 h12 true false).range) ∨
      (((B12 F).map (MulAut.conj c⁻¹).toMonoidHom).map θ = (F₀.longSL2 h12 true false).range ∧
        ((B23 F).map (MulAut.conj c⁻¹).toMonoidHom).map θ =
          (F₀.longSL2 h01 true false).range))
    (g : spinGroup Q) :
    (∀ (H : Type) [Group H] [Finite H] (ψ : spinGroup Q →* H),
      ψ.ker ≤ Subgroup.center (spinGroup Q) →
      alphaOf (Subgroup.closure ({toInducedAutOn ψ.range ⟨ψ (g * θ (c⁻¹ * SL3.u₁ * c) * g⁻¹),
          mem_normalizer_range ψ _⟩, toInducedAutOn ψ.range ⟨ψ (g * θ (c⁻¹ * SL3.u₂ * c) * g⁻¹),
          mem_normalizer_range ψ _⟩} : Set ↥(inducedAutOn ψ.range))) = ⊥) ∧
    Subgroup.centralizer ({g * θ (c⁻¹ * SL3.u₁ * c) * g⁻¹} : Set (spinGroup Q)) ⊔
      Subgroup.centralizer ({g * θ (c⁻¹ * SL3.u₂ * c) * g⁻¹} : Set (spinGroup Q)) ⊔
        Subgroup.centralizer ({g * θ (c⁻¹ * SL3.u₁ * c) * g⁻¹ * (g * θ (c⁻¹ * SL3.u₂ * c) * g⁻¹)} :
          Set (spinGroup Q)) = ⊤ := by
  classical
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  have hrel := frameRel_sl3 h2 θ hker c
  have hκy := thetaC_π_u₁ θ c
  set y₁ := θ (c⁻¹ * SL3.u₁ * c) with hy₁
  set y₂ := θ (c⁻¹ * SL3.u₂ * c) with hy₂
  set κ := θ (c⁻¹ * SL3.π * c) with hκ
  obtain ⟨frX, frY, hX, hY, ⟨P, he₁, he₂, hf₁, hf₂⟩, u, hu₁, hu₂, hu⟩ :=
    exists_frames h2 F₀ h01 h12 h02 hker hpair
  have hO : ∀ s : spinGroup Q, spinAction Q s ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    fun s => elementaryGroup_le_orthogonalGroup Q (hrange ▸ ⟨s, rfl⟩)
  have hE : ∀ s : spinGroup Q, spinAction Q s ∈ elementaryGroup Q := fun s => hrange ▸ ⟨s, rfl⟩
  have hy₁₂ : y₁ * y₂ = y₂ * y₁ := by rw [← hκy]; exact hrel.comm
  have hy₃ : y₁ * y₂ = κ * y₂ * κ⁻¹ := by
    rw [← hκy, ← hrel.sq_conj]
    group
  set fr₃ := frY.map (hO κ) with hfr₃
  have hc : frX.La (-1) * frY.La (-1) = frY.La (-1) * frX.La (-1) := by
    rw [← hX, ← hY, ← (spinAction Q).map_mul, ← (spinAction Q).map_mul, hy₁₂]
  have h3 : frX.La (-1) * frY.La (-1) = fr₃.La (-1) := by
    rw [hfr₃, Frame.map_La, ← hX, ← hY, ← (spinAction Q).map_mul, hy₃, (spinAction Q).map_mul,
      (spinAction Q).map_mul, (spinAction Q).map_inv]
  set g' := spinAction Q g with hg'
  set frX' := frX.map (hO g) with hfrX'
  set frY' := frY.map (hO g) with hfrY'
  set fr₃' := fr₃.map (hO g) with hfr₃'
  have hX' : spinAction Q (g * y₁ * g⁻¹) = frX'.La (-1) := by
    rw [hfrX', Frame.map_La, ← hX, map_mul, map_mul, map_inv]
  have hY' : spinAction Q (g * y₂ * g⁻¹) = frY'.La (-1) := by
    rw [hfrY', Frame.map_La, ← hY, map_mul, map_mul, map_inv]
  have hc' : frX'.La (-1) * frY'.La (-1) = frY'.La (-1) * frX'.La (-1) := by
    rw [← hX', ← hY', ← (spinAction Q).map_mul, ← (spinAction Q).map_mul]
    congr 1
    calc g * y₁ * g⁻¹ * (g * y₂ * g⁻¹) = g * (y₁ * y₂) * g⁻¹ := by group
      _ = g * (y₂ * y₁) * g⁻¹ := by rw [hy₁₂]
      _ = g * y₂ * g⁻¹ * (g * y₁ * g⁻¹) := by group
  have h3' : frX'.La (-1) * frY'.La (-1) = fr₃'.La (-1) := by
    rw [hfrX', hfrY', hfr₃', Frame.map_La, Frame.map_La, Frame.map_La, ← h3]
    group
  have hX3 : spinAction Q (g * y₁ * g⁻¹ * (g * y₂ * g⁻¹)) = fr₃'.La (-1) := by
    rw [(spinAction Q).map_mul, hX', hY', h3']
  set P' := mapPair (hO g) P with hP'
  have he₁' : P'.e ∈ frX'.span := map_mem_span_map (hO g) frX he₁
  have he₂' : P'.e ∈ frY'.span := map_mem_span_map (hO g) frY he₂
  have hf₁' : P'.f ∈ frX'.span := map_mem_span_map (hO g) frX hf₁
  have hf₂' : P'.f ∈ frY'.span := map_mem_span_map (hO g) frY hf₂
  have hu₁' : g' u ∈ frX'.span := map_mem_span_map (hO g) frX hu₁
  have hu₂' : g' u ∈ frY'.perp := map_mem_perp_map (hO g) frY hu₂
  have hu' : Q (g' u) ≠ 0 := by rw [map_of_mem (hO g)]; exact hu
  refine ⟨fun H _ _ ψ hψ => ?_, ?_⟩
  · obtain ⟨e, he, hkerE, hnorm, hcent⟩ := exists_hom_spin hodd hQ (by omega) hrange ψ hψ
    have := hnorm
    have key := alphaOf_frames_eq_bot frX' frY' fr₃' hodd h5 hQ hV hc' h3' P' he₁' he₂' hf₁' hf₂'
      hu₁' hu₂' hu' e hkerE hcent
    have e₁ : toInducedAutOn ψ.range ⟨ψ (g * y₁ * g⁻¹), mem_normalizer_range ψ _⟩ =
        e ⟨frX'.La (-1), frX'.La_mem_elementaryGroup (-1)⟩ := by
      rw [← he _ (hE _)]
      congr 1
      exact Subtype.ext hX'
    have e₂ : toInducedAutOn ψ.range ⟨ψ (g * y₂ * g⁻¹), mem_normalizer_range ψ _⟩ =
        e ⟨frY'.La (-1), frY'.La_mem_elementaryGroup (-1)⟩ := by
      rw [← he _ (hE _)]
      congr 1
      exact Subtype.ext hY'
    rw [e₁, e₂]
    exact key
  · have hperf : ∀ S : Submodule F V, PolarNondegOn Q S → ⁅elemOn Q S, elemOn Q S⁆ = elemOn Q S :=
      fun S hS => le_antisymm (commutator_le_self' _)
        (le_commutator_of_layerGenOn (layerGenOn_of_regular hodd h5 hS))
    have hneg : ((-1 : F) * -1) = 1 := by ring
    refine top_le_of_pieces hrange elemOn_le_elementaryGroup elemOn_le_elementaryGroup
      elemOn_le_elementaryGroup (hperf _ (nd_span frX' hQ)) (hperf _ (nd_span frY' hQ))
      (hperf _ (nd_perp fr₃' hQ))
      (elementaryGroup_le_frames frX' frY' fr₃' h2 hQ hc' h3' P' he₁' he₂' hf₁' hf₂' hu₁' hu₂' hu')
      (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_)
    · rw [hX']
      exact (comm_of_scalar_elemOn (frX'.La_mem_orthogonalGroup (-1)) hneg
        (fun v hv => by rw [La_neg_one_of_mem_span frX' hv, neg_one_smul]) hx).symm
    · rw [hY']
      exact (comm_of_scalar_elemOn (frY'.La_mem_orthogonalGroup (-1)) hneg
        (fun v hv => by rw [La_neg_one_of_mem_span frY' hv, neg_one_smul]) hx).symm
    · rw [hX3]
      exact (comm_of_scalar_elemOn (fr₃'.La_mem_orthogonalGroup (-1)) (one_mul 1)
        (fun v hv => by rw [La_neg_one_of_mem_perp fr₃' hv, one_smul]) hx).symm

end CFSG.ClassicalInvolution.NDB.SpinStd
