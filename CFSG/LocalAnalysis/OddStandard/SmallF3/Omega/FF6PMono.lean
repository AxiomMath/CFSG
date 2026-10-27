module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PPerm
public import TauCeti.Data.Finset.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

@[expose] noncomputable def ffB0p (fr : PFrame Q (Option (Fin 5)) ffC) : Subgroup (OGroup Q) where
  carrier := {g | ∃ J : Finset (Option (Fin 5)), none ∉ J ∧ Even J.card ∧ g = fr.signChange J}
  one_mem' := ⟨∅, by simp, by simp, fr.signChange_empty.symm⟩
  mul_mem' := by
    rintro a b ⟨J, hJn, hJ, rfl⟩ ⟨K, hKn, hK, rfl⟩
    refine ⟨symmDiff J K, ?_, (Finset.even_card_symmDiff_iff J K).mpr (iff_of_true hJ hK),
      fr.signChange_mul J K⟩
    simp [Finset.mem_symmDiff, hJn, hKn]
  inv_mem' := by
    rintro a ⟨J, hJn, hJ, rfl⟩
    exact ⟨J, hJn, hJ, inv_eq_of_mul_eq_one_right (fr.signChange_mul_self J)⟩

theorem mem_ffB0p_iff (fr : PFrame Q (Option (Fin 5)) ffC) {g : OGroup Q} :
    g ∈ ffB0p fr ↔
      ∃ J : Finset (Option (Fin 5)), none ∉ J ∧ Even J.card ∧ g = fr.signChange J :=
  Iff.rfl

theorem ffB0p_card (fr : PFrame Q (Option (Fin 5)) ffC) : Nat.card (ffB0p fr) = 16 := by
  let E := {J : Finset (Option (Fin 5)) // none ∉ J ∧ Even J.card}
  let F : E → ffB0p fr := fun J => ⟨fr.signChange J.1, J.1, J.2.1, J.2.2, rfl⟩
  have hF : Function.Bijective F := by
    refine ⟨fun J K h => Subtype.ext (fr.signChange_injective (congrArg Subtype.val h)), ?_⟩
    rintro ⟨g, J, hJn, hJ, rfl⟩
    exact ⟨⟨J, hJn, hJ⟩, rfl⟩
  have hE : Nat.card E = 16 := by
    rw [Nat.card_eq_fintype_card,
      Fintype.card_subtype (fun J : Finset (Option (Fin 5)) => none ∉ J ∧ Even J.card)]
    decide
  rw [← Nat.card_congr (Equiv.ofBijective F hF), hE]

theorem ffB0p_comm (fr : PFrame Q (Option (Fin 5)) ffC) {a b : OGroup Q} (ha : a ∈ ffB0p fr)
    (hb : b ∈ ffB0p fr) : a * b = b * a := by
  obtain ⟨J, -, -, rfl⟩ := ha
  obtain ⟨K, -, -, rfl⟩ := hb
  exact fr.signChange_comm J K

theorem ffB0p_mul_self (fr : PFrame Q (Option (Fin 5)) ffC) {a : OGroup Q} (ha : a ∈ ffB0p fr) :
    a * a = 1 := by
  obtain ⟨J, -, -, rfl⟩ := ha
  exact fr.signChange_mul_self J

theorem ffMonoP_basis (fr : PFrame Q (Option (Fin 5)) ffC) (σ : Equiv.Perm (Fin 5))
    (K : Finset (Option (Fin 5))) (i : Option (Fin 5)) :
    (((fr.pOrth σ * fr.signChange K : OGroup Q) : V ≃ₗ[ZMod 3] V) (fr.b i)) =
      (if i ∈ K then (-1 : ZMod 3) else 1) • fr.b (Equiv.optionCongr σ i) := by
  rw [Submonoid.coe_mul, LinearEquiv.mul_apply, fr.signChange_basis K i]
  by_cases hi : i ∈ K
  · rw [if_pos hi, map_neg, fr.pOrth_basis]
    simp [hi]
  · rw [if_neg hi, fr.pOrth_basis]
    simp [hi]

theorem ffMonoP_index_eq (fr : PFrame Q (Option (Fin 5)) ffC) {i j : Option (Fin 5)}
    {a d : ZMod 3} (ha : a ≠ 0) (h : a • fr.b i = d • fr.b j) : i = j := by
  by_contra hij
  have hc := congrArg (fun x : V => fr.b.repr x i) h
  simp [Module.Basis.repr_self, Finsupp.smul_apply, hij] at hc
  exact ha hc

theorem ffMonoP_unique (fr : PFrame Q (Option (Fin 5)) ffC) {σ τ : Equiv.Perm (Fin 5)}
    {J K : Finset (Option (Fin 5))}
    (h : fr.pOrth σ * fr.signChange J = fr.pOrth τ * fr.signChange K) :
    σ = τ ∧ J = K := by
  have hστ : σ = τ := by
    apply Equiv.ext
    intro i
    have h1 : Equiv.optionCongr σ (some i) = Equiv.optionCongr τ (some i) := by
      refine ffMonoP_index_eq fr (a := if some i ∈ J then (-1 : ZMod 3) else 1)
        (d := if some i ∈ K then (-1 : ZMod 3) else 1) (by split_ifs <;> decide) ?_
      have hb := congrArg (fun g : OGroup Q => ((g : V ≃ₗ[ZMod 3] V) (fr.b (some i)))) h
      rwa [ffMonoP_basis, ffMonoP_basis] at hb
    exact Option.some.inj h1
  subst hστ
  exact ⟨rfl, fr.signChange_injective (mul_left_cancel h)⟩

theorem PFrame.pOrth_inv (fr : PFrame Q (Option (Fin 5)) ffC) (σ : Equiv.Perm (Fin 5)) :
    (fr.pOrth σ)⁻¹ = fr.pOrth σ⁻¹ := by
  have h : fr.pOrth σ * fr.pOrth σ⁻¹ = 1 := by
    rw [← fr.pOrth_mul, mul_inv_cancel, fr.pOrth_one]
  exact inv_eq_of_mul_eq_one_right h

theorem ffMonoP_mul (fr : PFrame Q (Option (Fin 5)) ffC) (σ τ : Equiv.Perm (Fin 5))
    (J K : Finset (Option (Fin 5))) :
    (fr.pOrth σ * fr.signChange J) * (fr.pOrth τ * fr.signChange K) =
      fr.pOrth (σ * τ) *
        fr.signChange (symmDiff (J.map (Equiv.optionCongr τ⁻¹).toEmbedding) K) := by
  have h1 : fr.signChange J * fr.pOrth τ =
      fr.pOrth τ * fr.signChange (J.map (Equiv.optionCongr τ⁻¹).toEmbedding) := by
    have h := fr.pOrth_mul_signChange τ⁻¹ J
    rw [← PFrame.pOrth_inv] at h
    calc fr.signChange J * fr.pOrth τ
        = fr.pOrth τ * ((fr.pOrth τ)⁻¹ * fr.signChange J) * fr.pOrth τ := by group
      _ = fr.pOrth τ * (fr.signChange (J.map (Equiv.optionCongr τ⁻¹).toEmbedding) *
            (fr.pOrth τ)⁻¹) * fr.pOrth τ := by rw [h]
      _ = fr.pOrth τ * fr.signChange (J.map (Equiv.optionCongr τ⁻¹).toEmbedding) := by group
  calc (fr.pOrth σ * fr.signChange J) * (fr.pOrth τ * fr.signChange K)
      = fr.pOrth σ * (fr.signChange J * fr.pOrth τ) * fr.signChange K := by group
    _ = fr.pOrth σ * (fr.pOrth τ * fr.signChange (J.map (Equiv.optionCongr τ⁻¹).toEmbedding)) *
          fr.signChange K := by rw [h1]
    _ = (fr.pOrth σ * fr.pOrth τ) *
          (fr.signChange (J.map (Equiv.optionCongr τ⁻¹).toEmbedding) * fr.signChange K) := by
          group
    _ = fr.pOrth (σ * τ) *
          fr.signChange (symmDiff (J.map (Equiv.optionCongr τ⁻¹).toEmbedding) K) := by
          rw [fr.pOrth_mul, fr.signChange_mul]

theorem ffMonoP_conj_signChange (fr : PFrame Q (Option (Fin 5)) ffC) (σ : Equiv.Perm (Fin 5))
    (J K : Finset (Option (Fin 5))) :
    (fr.pOrth σ * fr.signChange J) * fr.signChange K * (fr.pOrth σ * fr.signChange J)⁻¹ =
      fr.signChange (K.map (Equiv.optionCongr σ).toEmbedding) := by
  have hJ : (fr.signChange J)⁻¹ = fr.signChange J :=
    inv_eq_of_mul_eq_one_right (fr.signChange_mul_self J)
  calc (fr.pOrth σ * fr.signChange J) * fr.signChange K * (fr.pOrth σ * fr.signChange J)⁻¹
      = fr.pOrth σ * (fr.signChange J * fr.signChange K * (fr.signChange J)⁻¹) *
          (fr.pOrth σ)⁻¹ := by group
    _ = fr.pOrth σ * fr.signChange K * (fr.pOrth σ)⁻¹ := by
          rw [fr.signChange_comm J K, mul_assoc (fr.signChange K), hJ,
            fr.signChange_mul_self J, mul_one]
    _ = fr.signChange (K.map (Equiv.optionCongr σ).toEmbedding) := by
          rw [fr.pOrth_mul_signChange σ K, mul_assoc, mul_inv_cancel, mul_one]

@[expose] noncomputable def ffMonoP (fr : PFrame Q (Option (Fin 5)) ffC) : Subgroup (OGroup Q) where
  carrier := {g | ∃ (σ : Equiv.Perm (Fin 5)) (K : Finset (Option (Fin 5))),
    g = fr.pOrth σ * fr.signChange K}
  one_mem' := ⟨1, ∅, by rw [fr.pOrth_one, fr.signChange_empty, one_mul]⟩
  mul_mem' := by
    rintro a b ⟨σ, J, rfl⟩ ⟨τ, K, rfl⟩
    exact ⟨σ * τ, _, ffMonoP_mul fr σ τ J K⟩
  inv_mem' := by
    rintro a ⟨σ, J, rfl⟩
    refine ⟨σ⁻¹, J.map (Equiv.optionCongr σ).toEmbedding, ?_⟩
    apply inv_eq_of_mul_eq_one_right
    rw [ffMonoP_mul fr σ σ⁻¹ J (J.map (Equiv.optionCongr σ).toEmbedding)]
    rw [show (σ⁻¹)⁻¹ = σ from inv_inv σ]
    rw [symmDiff_self, Finset.bot_eq_empty, fr.signChange_empty, mul_inv_cancel,
      fr.pOrth_one, one_mul]

theorem mem_ffMonoP_iff (fr : PFrame Q (Option (Fin 5)) ffC) {g : OGroup Q} :
    g ∈ ffMonoP fr ↔ ∃ (σ : Equiv.Perm (Fin 5)) (K : Finset (Option (Fin 5))),
      g = fr.pOrth σ * fr.signChange K :=
  Iff.rfl

theorem mono_mem_ffMonoP (fr : PFrame Q (Option (Fin 5)) ffC) (σ : Equiv.Perm (Fin 5))
    (K : Finset (Option (Fin 5))) : fr.pOrth σ * fr.signChange K ∈ ffMonoP fr :=
  ⟨σ, K, rfl⟩

theorem ffB0p_le_ffMonoP (fr : PFrame Q (Option (Fin 5)) ffC) : ffB0p fr ≤ ffMonoP fr := by
  intro g hg
  obtain ⟨J, -, -, rfl⟩ := (mem_ffB0p_iff fr).mp hg
  exact ⟨1, J, by rw [fr.pOrth_one, one_mul]⟩

private theorem ffMonoP_choose_eq (fr : PFrame Q (Option (Fin 5)) ffC) {g : OGroup Q}
    (hg : g ∈ ffMonoP fr) {σ : Equiv.Perm (Fin 5)} {K : Finset (Option (Fin 5))}
    (h : g = fr.pOrth σ * fr.signChange K) :
    Classical.choose (mem_ffMonoP_iff fr |>.mp hg) = σ := by
  obtain ⟨L, hL⟩ := Classical.choose_spec (mem_ffMonoP_iff fr |>.mp hg)
  exact (ffMonoP_unique fr (hL.symm.trans h)).1

@[expose] noncomputable def ffMonoPRho (fr : PFrame Q (Option (Fin 5)) ffC) :
    ↥(ffMonoP fr) →* Equiv.Perm (Fin 5) where
  toFun g := Classical.choose (mem_ffMonoP_iff fr |>.mp g.2)
  map_one' := by
    refine ffMonoP_choose_eq fr (g := 1) (1 : ↥(ffMonoP fr)).2 (σ := 1)
      (K := (∅ : Finset (Option (Fin 5)))) ?_
    rw [fr.pOrth_one, fr.signChange_empty, one_mul]
  map_mul' := by
    intro g h
    obtain ⟨J, hJ⟩ := Classical.choose_spec (mem_ffMonoP_iff fr |>.mp g.2)
    obtain ⟨K, hK⟩ := Classical.choose_spec (mem_ffMonoP_iff fr |>.mp h.2)
    have hmul : ((g * h : ↥(ffMonoP fr)) : OGroup Q) =
        fr.pOrth (Classical.choose (mem_ffMonoP_iff fr |>.mp g.2) *
          Classical.choose (mem_ffMonoP_iff fr |>.mp h.2)) *
        fr.signChange (symmDiff (J.map (Equiv.optionCongr
          (Classical.choose (mem_ffMonoP_iff fr |>.mp h.2))⁻¹).toEmbedding) K) := by
      conv_lhs => rw [Subgroup.coe_mul, hJ, hK, ffMonoP_mul]
    rw [ffMonoP_choose_eq fr (g * h).2 hmul]

theorem ffMonoPRho_apply (fr : PFrame Q (Option (Fin 5)) ffC) (σ : Equiv.Perm (Fin 5))
    (K : Finset (Option (Fin 5))) :
    ffMonoPRho fr ⟨fr.pOrth σ * fr.signChange K, mono_mem_ffMonoP fr σ K⟩ = σ :=
  ffMonoP_choose_eq fr (mono_mem_ffMonoP fr σ K) rfl

theorem ffMonoPRho_spec (fr : PFrame Q (Option (Fin 5)) ffC) (g : ↥(ffMonoP fr)) :
    ∃ K : Finset (Option (Fin 5)),
      (g : OGroup Q) = fr.pOrth (ffMonoPRho fr g) * fr.signChange K :=
  Classical.choose_spec (mem_ffMonoP_iff fr |>.mp g.2)

theorem ffMonoPRho_eq_one_iff (fr : PFrame Q (Option (Fin 5)) ffC) (g : ↥(ffMonoP fr)) :
    ffMonoPRho fr g = 1 ↔ ∃ K : Finset (Option (Fin 5)), (g : OGroup Q) = fr.signChange K := by
  constructor
  · intro h
    obtain ⟨K, hK⟩ := ffMonoPRho_spec fr g
    exact ⟨K, by rw [hK, h, fr.pOrth_one, one_mul]⟩
  · rintro ⟨K, hK⟩
    change Classical.choose (mem_ffMonoP_iff fr |>.mp g.2) = 1
    refine ffMonoP_choose_eq fr g.2 (σ := 1) (K := K) ?_
    rw [hK, fr.pOrth_one, one_mul]

end CFSG.OddStandard.SmallF3.Omega
