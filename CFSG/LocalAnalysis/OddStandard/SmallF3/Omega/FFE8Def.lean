module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFE8Sign
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFThetaSylow
public import TauCeti.Data.Finset.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

abbrev FFE8Idx : Type := Fin 2 ⊕ Fin 4

@[expose] def ffE8Norm (ε : ZMod 3) : FFE8Idx → ZMod 3 :=
  Sum.elim ![1, -1] fun _ => ε

@[expose] def ffE8Hat (J : Finset (Fin 4)) : Finset FFE8Idx :=
  J.map Function.Embedding.inr

@[expose] noncomputable def ffE8Group {ε : ZMod 3} (fr : PFrame Q FFE8Idx (ffE8Norm ε)) :
    Subgroup (OGroup Q) where
  carrier := {g | ∃ J : Finset (Fin 4), Even J.card ∧ g = fr.signChange (ffE8Hat J)}
  one_mem' := ⟨∅, by simp, by simp [ffE8Hat, fr.signChange_empty]⟩
  mul_mem' := by
    rintro a b ⟨J, hJ, rfl⟩ ⟨K, hK, rfl⟩
    refine ⟨symmDiff J K, (Finset.even_card_symmDiff_iff J K).mpr (iff_of_true hJ hK), ?_⟩
    rw [fr.signChange_mul]
    congr 1
    ext i
    cases i <;> simp [ffE8Hat, Finset.mem_symmDiff]
  inv_mem' := by
    rintro a ⟨J, hJ, rfl⟩
    exact ⟨J, hJ, inv_eq_of_mul_eq_one_right (fr.signChange_mul_self _)⟩

theorem mem_ffE8Group_iff {ε : ZMod 3} (fr : PFrame Q FFE8Idx (ffE8Norm ε)) {g : OGroup Q} :
    g ∈ ffE8Group fr ↔ ∃ J : Finset (Fin 4), Even J.card ∧ g = fr.signChange (ffE8Hat J) :=
  Iff.rfl

theorem ffE8Group_card {ε : ZMod 3} (fr : PFrame Q FFE8Idx (ffE8Norm ε)) :
    Nat.card (ffE8Group fr) = 8 := by
  let F : {J : Finset (Fin 4) // Even J.card} → ffE8Group fr := fun J =>
    ⟨fr.signChange (ffE8Hat J.1), J.1, J.2, rfl⟩
  have hF : Function.Bijective F := by
    refine ⟨fun J K h => ?_, ?_⟩
    · have h2 : ffE8Hat J.1 = ffE8Hat K.1 :=
        fr.signChange_injective (congrArg Subtype.val h)
      exact Subtype.ext
        (Finset.map_injective (Function.Embedding.inr : Fin 4 ↪ FFE8Idx)
          (by simpa [ffE8Hat] using h2))
    · rintro ⟨g, J, hJ, rfl⟩
      exact ⟨⟨J, hJ⟩, rfl⟩
  have hE : Nat.card {J : Finset (Fin 4) // Even J.card} = 8 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    decide
  rw [← Nat.card_congr (Equiv.ofBijective F hF), hE]

theorem ffE8Group_elemAb2 {ε : ZMod 3} (fr : PFrame Q FFE8Idx (ffE8Norm ε)) :
    IsElemAb2 (ffE8Group fr) 3 := by
  have hcomm : ∀ a b : ffE8Group fr, a * b = b * a := by
    intro a b
    obtain ⟨J, hJ, ha⟩ := (mem_ffE8Group_iff fr).mp a.2
    obtain ⟨K, hK, hb⟩ := (mem_ffE8Group_iff fr).mp b.2
    apply Subtype.ext
    change (a : OGroup Q) * b = (b : OGroup Q) * a
    rw [ha, hb, fr.signChange_comm]
  have hsq : ∀ x ∈ ffE8Group fr, x ^ 2 = 1 := by
    intro x hx
    obtain ⟨J, hJ, hx'⟩ := (mem_ffE8Group_iff fr).mp hx
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one, hx', pow_two,
      fr.signChange_mul_self]
  refine ⟨⟨IsMulCommutative.of_comm hcomm, hsq⟩, ?_⟩
  rw [ffE8Group_card fr]
  norm_num

theorem PFrame.signChange_mem_omegaGroup_iff (hQ : Q.Nondegenerate) {ι : Type} [Fintype ι]
    [DecidableEq ι] {c : ι → ZMod 3} (fr : PFrame Q ι c) (hc : ∀ i, c i = 1 ∨ c i = -1)
    (K : Finset ι) :
    fr.signChange K ∈ omegaGroup hQ ↔
      Even K.card ∧ Even (K.filter fun i => c i = -1).card := by
  exact ffE8Sign_mem_omega_iff hQ fr hc K

private lemma ffOutFFE8Def_norm_pm {ε : ZMod 3} (hε : ε = 1 ∨ ε = -1) (i : FFE8Idx) :
    ffE8Norm ε i = 1 ∨ ffE8Norm ε i = -1 := by
  rcases i with i | i
  · fin_cases i <;> simp [ffE8Norm]
  · simp only [ffE8Norm, Sum.elim_inr]
    exact hε

private lemma ffOutFFE8Def_hat_filter_card {ε : ZMod 3} (J : Finset (Fin 4)) :
    ((ffE8Hat J).filter fun i => ffE8Norm ε i = -1).card =
      if ε = -1 then J.card else 0 := by
  rw [ffE8Hat, Finset.filter_map, Finset.card_map]
  by_cases h : ε = -1
  · rw [if_pos h]
    congr 1
    rw [Finset.filter_true_of_mem]
    intro x _
    show ffE8Norm ε (Function.Embedding.inr x) = -1
    rw [show ffE8Norm ε (Function.Embedding.inr x) = ε from rfl, h]
  · rw [if_neg h, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x _
    show ¬ (ffE8Norm ε (Function.Embedding.inr x) = -1)
    rw [show ffE8Norm ε (Function.Embedding.inr x) = ε from rfl]
    exact h

theorem ffE8Group_le_omegaGroup (hQ : Q.Nondegenerate) {ε : ZMod 3} (hε : ε = 1 ∨ ε = -1)
    (fr : PFrame Q FFE8Idx (ffE8Norm ε)) : ffE8Group fr ≤ omegaGroup hQ := by
  intro g hg
  obtain ⟨J, hJ, rfl⟩ := (mem_ffE8Group_iff fr).mp hg
  rw [PFrame.signChange_mem_omegaGroup_iff hQ fr (ffOutFFE8Def_norm_pm hε)]
  refine ⟨?_, ?_⟩
  · rw [ffE8Hat, Finset.card_map]
    exact hJ
  · rw [ffOutFFE8Def_hat_filter_card]
    by_cases h : ε = -1
    · rw [if_pos h]
      exact hJ
    · rw [if_neg h]
      exact ⟨0, rfl⟩

@[expose] noncomputable def ffSim (Q : QuadraticForm (ZMod 3) V) : OGroup Q →* ProjSim Q :=
  (QuotientGroup.mk' (piSim Q)).comp (orthToSim Q)

private lemma ffOutFFE8Def_ffSim_apply (g : OGroup Q) :
    ffSim Q g = QuotientGroup.mk (orthToSim Q g) := by
  rw [ffSim, MonoidHom.comp_apply, QuotientGroup.mk'_apply]

theorem ffSim_eq_one_iff {g : OGroup Q} : ffSim Q g = 1 ↔ g = 1 ∨ g = piOrth Q := by
  rw [ffOutFFE8Def_ffSim_apply, QuotientGroup.eq_one_iff, mem_piSim_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl (orthToSim_injective (by rw [h, map_one]))
    · exact Or.inr (orthToSim_injective h)
  · rintro (rfl | rfl)
    · exact Or.inl (map_one _)
    · exact Or.inr rfl

@[expose] noncomputable def ffOmegaSim (hQ : Q.Nondegenerate) : Subgroup (ProjSim Q) :=
  (ffOmegaToSim hQ).range

theorem mem_ffOmegaSim_iff (hQ : Q.Nondegenerate) {x : ProjSim Q} :
    x ∈ ffOmegaSim hQ ↔ ∃ g ∈ omegaGroup hQ, ffSim Q g = x := by
  rw [ffOmegaSim, MonoidHom.mem_range]
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨g, hg, hgw⟩ := (mem_omegaProj_iff hQ).mp w.2
    refine ⟨g, hg, ?_⟩
    rw [ffOutFFE8Def_ffSim_apply, ffOmegaToSim_apply, ← hgw,
      projOrthToProjSim_toProj]
  · rintro ⟨g, hg, rfl⟩
    refine ⟨⟨toProj Q g, Subgroup.mem_map.mpr ⟨g, hg, rfl⟩⟩, ?_⟩
    rw [ffOmegaToSim_apply, projOrthToProjSim_toProj, ffOutFFE8Def_ffSim_apply]

theorem ffOmegaSim_eq_map (hQ : Q.Nondegenerate) :
    ffOmegaSim hQ = (omegaGroup hQ).map (ffSim Q) := by
  apply Subgroup.ext
  intro x
  rw [mem_ffOmegaSim_iff, Subgroup.mem_map]

structure FFE8VData (hQ : Q.Nondegenerate) (E : Subgroup (OGroup Q)) (t ν : OGroup Q) : Prop where
  le_omega : E ≤ omegaGroup hQ
  elemAb : IsElemAb2 E 3
  t_mem : t ∈ E
  t_sq : t * t = 1
  t_dim : invDim t = 4
  t_sign : invSign t = 1
  nu_cube : ν ^ 3 = 1
  nu_norm : ν ∈ Subgroup.normalizer (E : Set (OGroup Q))
  nu_fix : ∀ e ∈ E, ν * e = e * ν → e = 1 ∨ e = t

structure FFE8SData (hQ : Q.Nondegenerate) (Ē : Subgroup (ProjSim Q)) (z ν : ProjSim Q) : Prop where
  le_omega : Ē ≤ ffOmegaSim hQ
  elemAb : IsElemAb2 Ē 3
  z_mem : z ∈ Ē
  z_type : SimHasType z 4 1
  nu_mem : ν ∈ ffOmegaSim hQ
  nu_order : orderOf ν = 3
  nu_norm : ν ∈ Subgroup.normalizer (Ē : Set (ProjSim Q))
  nu_fix : ∀ e ∈ Ē, ν * e = e * ν → e = 1 ∨ e = z

private lemma ffOutFFE8Def_polar_similitude {σ : V ≃ₗ[ZMod 3] V} {μ : (ZMod 3)ˣ}
    (hσ : IsSimilitude Q σ μ) (x y : V) :
    QuadraticMap.polar Q (σ x) (σ y) = (μ : ZMod 3) * QuadraticMap.polar Q x y := by
  rw [QuadraticMap.polar, QuadraticMap.polar, ← map_add, hσ (x + y), hσ x, hσ y]
  ring

noncomputable def PFrame.ffSimMap {ι : Type} [Fintype ι] [DecidableEq ι] {c : ι → ZMod 3}
    (fr : PFrame Q ι c) (γ : V ≃ₗ[ZMod 3] V) (μ : (ZMod 3)ˣ) (hγ : IsSimilitude Q γ μ) :
    PFrame Q ι (fun i => (μ : ZMod 3) * c i) where
  b := fr.b.map γ
  norm := by
    intro i
    rw [Module.Basis.map_apply, hγ, fr.norm]
  orth := by
    intro i j hij
    rw [Module.Basis.map_apply, Module.Basis.map_apply,
      ffOutFFE8Def_polar_similitude hγ, fr.orth i j hij, mul_zero]

theorem PFrame.ffSimMap_signChange {ι : Type} [Fintype ι] [DecidableEq ι] {c : ι → ZMod 3}
    (fr : PFrame Q ι c) (γ : V ≃ₗ[ZMod 3] V) (μ : (ZMod 3)ˣ) (hγ : IsSimilitude Q γ μ)
    (J : Finset ι) :
    γ * (fr.signChange J : V ≃ₗ[ZMod 3] V) * γ⁻¹ =
      ((fr.ffSimMap γ μ hγ).signChange J : V ≃ₗ[ZMod 3] V) := by
  apply (fr.ffSimMap γ μ hγ).b.ext'
  intro i
  rw [(fr.ffSimMap γ μ hγ).signChange_basis J i]
  rw [show (fr.ffSimMap γ μ hγ).b = fr.b.map γ from rfl, Module.Basis.map_apply]
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  simp only [LinearEquiv.coe_inv]
  rw [LinearEquiv.symm_apply_apply, fr.signChange_basis J i]
  by_cases h : i ∈ J
  · rw [if_pos h, if_pos h, map_neg]
  · rw [if_neg h, if_neg h]

private def ffOutFFE8Def_swapIdx : FFE8Idx ≃ FFE8Idx :=
  Equiv.swap (Sum.inl (0 : Fin 2)) (Sum.inl 1)

private lemma ffOutFFE8Def_swapIdx_symm :
    ffOutFFE8Def_swapIdx.symm = ffOutFFE8Def_swapIdx :=
  Equiv.symm_swap _ _

private lemma ffOutFFE8Def_mem_hat_swap (J : Finset (Fin 4)) (i : FFE8Idx) :
    ffOutFFE8Def_swapIdx i ∈ ffE8Hat J ↔ i ∈ ffE8Hat J := by
  rcases i with i | i
  · fin_cases i <;> simp [ffOutFFE8Def_swapIdx, ffE8Hat]
  · have h : ffOutFFE8Def_swapIdx (Sum.inr i) = Sum.inr i :=
      Equiv.swap_apply_of_ne_of_ne (by simp) (by simp)
    rw [h]

noncomputable def PFrame.ffE8Neg {ε : ZMod 3} (fr : PFrame Q FFE8Idx (ffE8Norm ε))
    {γ : V ≃ₗ[ZMod 3] V} (hγ : IsSimilitude Q γ (-1)) : PFrame Q FFE8Idx (ffE8Norm (-ε)) where
  b := (fr.ffSimMap γ (-1) hγ).b.reindex ffOutFFE8Def_swapIdx
  norm := by
    intro j
    rw [Module.Basis.reindex_apply, ffOutFFE8Def_swapIdx_symm,
      (fr.ffSimMap γ (-1) hγ).norm]
    rcases j with j | j
    · fin_cases j <;> simp [ffE8Norm, ffOutFFE8Def_swapIdx]
    · have hsw : ffOutFFE8Def_swapIdx (Sum.inr j) = Sum.inr j :=
        Equiv.swap_apply_of_ne_of_ne (by simp) (by simp)
      rw [hsw]
      show (-1 : ZMod 3) * ε = -ε
      rw [neg_one_mul]
  orth := by
    intro i j hij
    simp only [Module.Basis.reindex_apply, ffOutFFE8Def_swapIdx_symm]
    exact (fr.ffSimMap γ (-1) hγ).orth _ _
      (fun h => hij (ffOutFFE8Def_swapIdx.injective h))

private lemma ffOutFFE8Def_neg_b {ε : ZMod 3} (fr : PFrame Q FFE8Idx (ffE8Norm ε))
    {γ : V ≃ₗ[ZMod 3] V} (hγ : IsSimilitude Q γ (-1)) (i : FFE8Idx) :
    (fr.ffE8Neg hγ).b i = (fr.ffSimMap γ (-1) hγ).b (ffOutFFE8Def_swapIdx i) := by
  simp only [PFrame.ffE8Neg, Module.Basis.reindex_apply,
    ffOutFFE8Def_swapIdx_symm]

private lemma ffOutFFE8Def_neg_signChange {ε : ZMod 3} (fr : PFrame Q FFE8Idx (ffE8Norm ε))
    {γ : V ≃ₗ[ZMod 3] V} (hγ : IsSimilitude Q γ (-1)) (J : Finset (Fin 4)) :
    (fr.ffSimMap γ (-1) hγ).signChange (ffE8Hat J) =
      (fr.ffE8Neg hγ).signChange (ffE8Hat J) := by
  apply Subtype.ext
  apply (fr.ffE8Neg hγ).b.ext'
  intro i
  nth_rewrite 1 [ffOutFFE8Def_neg_b fr hγ i]
  rw [(fr.ffSimMap γ (-1) hγ).signChange_basis (ffE8Hat J) (ffOutFFE8Def_swapIdx i),
    (fr.ffE8Neg hγ).signChange_basis (ffE8Hat J) i, ffOutFFE8Def_neg_b fr hγ i]
  have hm : ffOutFFE8Def_swapIdx i ∈ ffE8Hat J ↔ i ∈ ffE8Hat J :=
    ffOutFFE8Def_mem_hat_swap J i
  by_cases h : i ∈ ffE8Hat J
  · rw [if_pos (hm.mpr h), if_pos h]
  · rw [if_neg (fun hh => h (hm.mp hh)), if_neg h]

private lemma ffOutFFE8Def_simAct_signChange {ε : ZMod 3}
    (fr : PFrame Q FFE8Idx (ffE8Norm ε)) (γ : simGroup Q)
    (hγ : IsSimilitude Q (γ : V ≃ₗ[ZMod 3] V) (-1)) (J : Finset (Fin 4)) :
    simAct Q γ (fr.signChange (ffE8Hat J)) =
      (fr.ffE8Neg hγ).signChange (ffE8Hat J) := by
  apply Subtype.ext
  rw [coe_simAct,
    PFrame.ffSimMap_signChange fr (γ : V ≃ₗ[ZMod 3] V) (-1) hγ]
  exact congrArg Subtype.val (ffOutFFE8Def_neg_signChange fr hγ J)

theorem ffE8Group_simAct {ε : ZMod 3} (fr : PFrame Q FFE8Idx (ffE8Norm ε)) (γ : simGroup Q)
    (hγ : IsSimilitude Q (γ : V ≃ₗ[ZMod 3] V) (-1)) :
    (ffE8Group fr).map (simAct Q γ).toMonoidHom = ffE8Group (fr.ffE8Neg hγ) := by
  apply Subgroup.ext
  intro g
  constructor
  · intro hg
    obtain ⟨a, ha, hag⟩ := Subgroup.mem_map.mp hg
    obtain ⟨J, hJ, rfl⟩ := (mem_ffE8Group_iff fr).mp ha
    exact (mem_ffE8Group_iff (fr.ffE8Neg hγ)).mpr
      ⟨J, hJ, hag.symm.trans (ffOutFFE8Def_simAct_signChange fr γ hγ J)⟩
  · intro hg
    obtain ⟨J, hJ, rfl⟩ := (mem_ffE8Group_iff (fr.ffE8Neg hγ)).mp hg
    exact Subgroup.mem_map.mpr
      ⟨fr.signChange (ffE8Hat J), (mem_ffE8Group_iff fr).mpr ⟨J, hJ, rfl⟩,
        ffOutFFE8Def_simAct_signChange fr γ hγ J⟩

end CFSG.OddStandard.SmallF3.Omega
