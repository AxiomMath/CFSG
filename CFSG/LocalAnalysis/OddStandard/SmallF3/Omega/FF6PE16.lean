module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PD8
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private instance ffOutFF6PE16_decD8 : DecidablePred (· ∈ ffD8p) := fun σ =>
  decidable_of_iff' (σ * ffD8g = ffD8g * σ) (mem_ffD8p_iff σ)

private theorem ffOutFF6PE16_act_four (σ : Equiv.Perm (Fin 5)) (hσ : σ ∈ ffD8p) :
    ffAct σ {0, 1, 2, 3} = {0, 1, 2, 3} := by
  revert σ
  decide +kernel

@[expose] def ffOpt (J : Finset (Fin 5)) : Finset (Option (Fin 5)) :=
  J.map Function.Embedding.some

theorem ffOpt_injective : Function.Injective ffOpt := by
  intro J K h
  ext i
  have h' := congrArg (fun s : Finset (Option (Fin 5)) => some i ∈ s) h
  simpa [ffOpt] using h'

theorem mem_ffOpt_some (J : Finset (Fin 5)) (i : Fin 5) : some i ∈ ffOpt J ↔ i ∈ J := by
  simp [ffOpt]

theorem none_notMem_ffOpt (J : Finset (Fin 5)) : none ∉ ffOpt J := by
  rw [ffOpt, Finset.mem_map]
  rintro ⟨a, -, h⟩
  exact Option.some_ne_none a h

theorem ffOpt_card (J : Finset (Fin 5)) : (ffOpt J).card = J.card := by
  rw [ffOpt, Finset.card_map]

theorem ffOpt_symmDiff (J K : Finset (Fin 5)) :
    ffOpt (symmDiff J K) = symmDiff (ffOpt J) (ffOpt K) := by
  ext x
  cases x with
  | none =>
      have h1 : none ∉ ffOpt (symmDiff J K) := none_notMem_ffOpt _
      have h2 : none ∉ symmDiff (ffOpt J) (ffOpt K) := by
        simp [Finset.mem_symmDiff, none_notMem_ffOpt]
      simp [h1, h2]
  | some i =>
      rw [Finset.mem_symmDiff]
      simp only [mem_ffOpt_some, Finset.mem_symmDiff]

theorem ffOpt_map_optionCongr (σ : Equiv.Perm (Fin 5)) (J : Finset (Fin 5)) :
    (ffOpt J).map (Equiv.optionCongr σ).toEmbedding = ffOpt (ffAct σ J) := by
  have h : (Function.Embedding.some.trans (Equiv.optionCongr σ).toEmbedding) =
      (σ.toEmbedding.trans Function.Embedding.some) := by
    ext j
    rfl
  simp only [ffOpt, ffAct, Finset.map_map, h]

theorem exists_ffOpt_of_none_notMem {K : Finset (Option (Fin 5))} (h : none ∉ K) :
    ∃ J : Finset (Fin 5), K = ffOpt J := by
  refine ⟨Finset.univ.filter (fun i => some i ∈ K), ?_⟩
  ext x
  cases x with
  | none =>
      simp only [ffOpt, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun hk => absurd hk h, fun ⟨a, _, ha⟩ => (Option.some_ne_none a ha).elim⟩
  | some i =>
      rw [mem_ffOpt_some]
      simp

theorem mem_ffB0p_iff_ffOpt (fr : PFrame Q (Option (Fin 5)) ffC) {g : OGroup Q} :
    g ∈ ffB0p fr ↔ ∃ J : Finset (Fin 5), Even J.card ∧ g = fr.signChange (ffOpt J) := by
  rw [mem_ffB0p_iff fr]
  constructor
  · rintro ⟨K, hKn, hKe, rfl⟩
    obtain ⟨J, rfl⟩ := exists_ffOpt_of_none_notMem hKn
    exact ⟨J, by rwa [ffOpt_card] at hKe, rfl⟩
  · rintro ⟨J, hJ, rfl⟩
    exact ⟨ffOpt J, none_notMem_ffOpt J, by rwa [ffOpt_card], rfl⟩

theorem ffOpt_signChange_eq_iff (fr : PFrame Q (Option (Fin 5)) ffC) {J K : Finset (Fin 5)} :
    fr.signChange (ffOpt J) = fr.signChange (ffOpt K) ↔ J = K := by
  constructor
  · intro h
    exact ffOpt_injective (fr.signChange_injective h)
  · intro h
    rw [h]

theorem ffHat_conj_signChange_ffOpt (fr : PFrame Q (Option (Fin 5)) ffC)
    (σ : Equiv.Perm (Fin 5)) (J : Finset (Fin 5)) :
    ffHat fr σ * fr.signChange (ffOpt J) * (ffHat fr σ)⁻¹ =
      fr.signChange (ffOpt (ffAct σ J)) := by
  rw [ffHat_conj_signChange fr σ (ffOpt J), ffOpt_map_optionCongr]

theorem ffHat_mul_ffOpt (fr : PFrame Q (Option (Fin 5)) ffC) (σ τ : Equiv.Perm (Fin 5))
    (J K : Finset (Fin 5)) :
    (ffHat fr σ * fr.signChange (ffOpt J)) * (ffHat fr τ * fr.signChange (ffOpt K)) =
      ffHat fr (σ * τ) * fr.signChange (ffOpt (symmDiff (ffAct τ⁻¹ J) K)) := by
  have hinv : ∀ τ : Equiv.Perm (Fin 5), (ffHat fr τ)⁻¹ = ffHat fr τ⁻¹ := fun τ =>
    inv_eq_of_mul_eq_one_right (by rw [ffHat_mul, mul_inv_cancel, ffHat_one])
  have hmove : fr.signChange (ffOpt J) * ffHat fr τ =
      ffHat fr τ * fr.signChange (ffOpt (ffAct τ⁻¹ J)) := by
    have hconj : ffHat fr τ⁻¹ * fr.signChange (ffOpt J) * ffHat fr τ =
        fr.signChange (ffOpt (ffAct τ⁻¹ J)) := by
      have h := ffHat_conj_signChange_ffOpt fr τ⁻¹ J
      rw [hinv (τ⁻¹), inv_inv] at h
      exact h
    calc fr.signChange (ffOpt J) * ffHat fr τ
        = (ffHat fr τ * (ffHat fr τ)⁻¹) *
            (fr.signChange (ffOpt J) * ffHat fr τ) := by group
      _ = ffHat fr τ * (ffHat fr τ⁻¹ * fr.signChange (ffOpt J) * ffHat fr τ) := by
            rw [hinv τ]; group
      _ = ffHat fr τ * fr.signChange (ffOpt (ffAct τ⁻¹ J)) := by rw [hconj]
  calc (ffHat fr σ * fr.signChange (ffOpt J)) * (ffHat fr τ * fr.signChange (ffOpt K))
      = ffHat fr σ * (fr.signChange (ffOpt J) * ffHat fr τ) *
          fr.signChange (ffOpt K) := by group
    _ = ffHat fr σ * (ffHat fr τ * fr.signChange (ffOpt (ffAct τ⁻¹ J))) *
          fr.signChange (ffOpt K) := by rw [hmove]
    _ = (ffHat fr σ * ffHat fr τ) *
          (fr.signChange (ffOpt (ffAct τ⁻¹ J)) * fr.signChange (ffOpt K)) := by group
    _ = ffHat fr (σ * τ) * fr.signChange (ffOpt (symmDiff (ffAct τ⁻¹ J) K)) := by
          rw [ffHat_mul, fr.signChange_mul, ffOpt_symmDiff]

theorem mem_ffP0p_iff_hatOpt (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC)
    {g : OGroup Q} :
    g ∈ ffP0p hQ fr ↔ ∃ σ ∈ ffD8p, ∃ J : Finset (Fin 5), Even J.card ∧
      g = ffHat fr σ * fr.signChange (ffOpt J) := by
  rw [mem_ffP0p_iff_hat hQ fr]
  constructor
  · rintro ⟨σ, hσ, b, hb, rfl⟩
    obtain ⟨J, hJ, rfl⟩ := (mem_ffB0p_iff_ffOpt fr).mp hb
    exact ⟨σ, hσ, J, hJ, rfl⟩
  · rintro ⟨σ, hσ, J, hJ, rfl⟩
    exact ⟨σ, hσ, fr.signChange (ffOpt J),
      (mem_ffB0p_iff_ffOpt fr).mpr ⟨J, hJ, rfl⟩, rfl⟩

theorem ffMonoPRho_eq_of_hat (fr : PFrame Q (Option (Fin 5)) ffC) {g : ↥(ffMonoP fr)}
    {σ : Equiv.Perm (Fin 5)} {K : Finset (Option (Fin 5))}
    (h : (g : OGroup Q) = ffHat fr σ * fr.signChange K) : ffMonoPRho fr g = σ := by
  have h' : (g : OGroup Q) = fr.pOrth σ *
      fr.signChange (symmDiff (if Equiv.Perm.sign σ = 1 then ∅ else {none}) K) := by
    rw [h, ffHat, mul_assoc, fr.signChange_mul]
  have hg : g = ⟨fr.pOrth σ * fr.signChange
      (symmDiff (if Equiv.Perm.sign σ = 1 then ∅ else {none}) K),
      mono_mem_ffMonoP fr σ _⟩ := Subtype.ext h'
  rw [hg]
  exact ffMonoPRho_apply fr σ _

theorem ff6p_B0_normalE16 (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC) :
    IsNormalE16In (ffP0p hQ fr) (ffB0p fr) := by
  refine ⟨ffB0p_le_ffP0p hQ fr, ⟨⟨?_, ?_⟩, ?_⟩, ffB0p_normal_ffP0p hQ fr⟩
  · exact IsMulCommutative.of_comm fun a b => Subtype.ext (ffB0p_comm fr a.2 b.2)
  · intro x hx
    rw [pow_two]
    exact ffB0p_mul_self fr hx
  · rw [ffB0p_card]
    norm_num

@[expose] noncomputable def ffZ0p (fr : PFrame Q (Option (Fin 5)) ffC) : OGroup Q :=
  fr.signChange (ffOpt {0, 1, 2, 3})

theorem ffZ0p_mem_ffB0p (fr : PFrame Q (Option (Fin 5)) ffC) : ffZ0p fr ∈ ffB0p fr := by
  rw [ffZ0p]
  exact (mem_ffB0p_iff_ffOpt fr).mpr ⟨{0, 1, 2, 3}, ⟨2, by decide⟩, rfl⟩

theorem ffZ0p_mem_ffP0p (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC) :
    ffZ0p fr ∈ ffP0p hQ fr :=
  ffB0p_le_ffP0p hQ fr (ffZ0p_mem_ffB0p fr)

theorem ffZ0p_ne_one (fr : PFrame Q (Option (Fin 5)) ffC) : ffZ0p fr ≠ 1 := by
  intro h
  rw [ffZ0p] at h
  have h' : fr.signChange (ffOpt {0, 1, 2, 3}) = fr.signChange (ffOpt ∅) := by
    rw [h, ffOpt, Finset.map_empty, fr.signChange_empty]
  have hJ := (ffOpt_signChange_eq_iff fr).mp h'
  exact absurd hJ (by decide)

theorem ffZ0p_mul_self (fr : PFrame Q (Option (Fin 5)) ffC) : ffZ0p fr * ffZ0p fr = 1 := by
  rw [ffZ0p, fr.signChange_mul_self]

theorem ffZ0p_central (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC)
    {g : OGroup Q} (hg : g ∈ ffP0p hQ fr) : g * ffZ0p fr = ffZ0p fr * g := by
  obtain ⟨σ, hσ, J, -, hgEq⟩ := (mem_ffP0p_iff_hatOpt hQ fr).mp hg
  have hfix : ffAct σ {0, 1, 2, 3} = {0, 1, 2, 3} := ffOutFF6PE16_act_four σ hσ
  have hσz : ffHat fr σ * ffZ0p fr = ffZ0p fr * ffHat fr σ := by
    have hconj : ffHat fr σ * ffZ0p fr * (ffHat fr σ)⁻¹ = ffZ0p fr := by
      rw [ffZ0p, ffHat_conj_signChange_ffOpt fr σ {0, 1, 2, 3}, hfix]
    calc ffHat fr σ * ffZ0p fr
        = (ffHat fr σ * ffZ0p fr * (ffHat fr σ)⁻¹) * ffHat fr σ := by group
      _ = ffZ0p fr * ffHat fr σ := by rw [hconj]
  rw [hgEq]
  calc (ffHat fr σ * fr.signChange (ffOpt J)) * ffZ0p fr
      = ffHat fr σ * (fr.signChange (ffOpt J) * ffZ0p fr) := by group
    _ = ffHat fr σ * (ffZ0p fr * fr.signChange (ffOpt J)) := by
          rw [ffZ0p, fr.signChange_comm]
    _ = (ffHat fr σ * ffZ0p fr) * fr.signChange (ffOpt J) := by group
    _ = (ffZ0p fr * ffHat fr σ) * fr.signChange (ffOpt J) := by rw [hσz]
    _ = ffZ0p fr * (ffHat fr σ * fr.signChange (ffOpt J)) := by group

theorem ff6p_center_P0 (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC)
    {g : OGroup Q} (hg : g ∈ ffP0p hQ fr) (hc : ∀ h ∈ ffP0p hQ fr, h * g = g * h) :
    g = 1 ∨ g = ffZ0p fr := by
  obtain ⟨σ, hσ, J, hJe, rfl⟩ := (mem_ffP0p_iff_hatOpt hQ fr).mp hg
  have hfix : ∀ K : Finset (Fin 5), Even K.card → ffAct σ K = K := by
    intro K hK
    have hKmem : fr.signChange (ffOpt K) ∈ ffP0p hQ fr :=
      ffB0p_le_ffP0p hQ fr ((mem_ffB0p_iff_ffOpt fr).mpr ⟨K, hK, rfl⟩)
    have hcomm := hc (fr.signChange (ffOpt K)) hKmem
    have hgt : ffHat fr σ * fr.signChange (ffOpt J) * fr.signChange (ffOpt K) *
        (ffHat fr σ * fr.signChange (ffOpt J))⁻¹ = fr.signChange (ffOpt K) := by
      have h1 : (ffHat fr σ * fr.signChange (ffOpt J) * fr.signChange (ffOpt K) *
          (ffHat fr σ * fr.signChange (ffOpt J))⁻¹) *
          (ffHat fr σ * fr.signChange (ffOpt J))
          = fr.signChange (ffOpt K) * (ffHat fr σ * fr.signChange (ffOpt J)) := by
        rw [hcomm]; group
      exact mul_right_cancel h1
    have hcancel : ffHat fr σ * fr.signChange (ffOpt K) * (ffHat fr σ)⁻¹ =
        fr.signChange (ffOpt K) := by
      have hJt : fr.signChange (ffOpt J) * fr.signChange (ffOpt K) *
          (fr.signChange (ffOpt J))⁻¹ = fr.signChange (ffOpt K) := by
        rw [fr.signChange_comm (ffOpt J) (ffOpt K)]; group
      calc ffHat fr σ * fr.signChange (ffOpt K) * (ffHat fr σ)⁻¹
          = ffHat fr σ * (fr.signChange (ffOpt J) * fr.signChange (ffOpt K) *
              (fr.signChange (ffOpt J))⁻¹) * (ffHat fr σ)⁻¹ := by rw [hJt]
        _ = (ffHat fr σ * fr.signChange (ffOpt J)) * fr.signChange (ffOpt K) *
              (ffHat fr σ * fr.signChange (ffOpt J))⁻¹ := by group
        _ = fr.signChange (ffOpt K) := hgt
    have hconjK : fr.signChange (ffOpt (ffAct σ K)) = fr.signChange (ffOpt K) := by
      rw [← ffHat_conj_signChange_ffOpt fr σ K, hcancel]
    exact (ffOpt_signChange_eq_iff fr).mp hconjK
  have hσ1 : σ = 1 := ff_perm_eq_one_of_fix_even σ hfix
  subst hσ1
  have hc' : ∀ h ∈ ffP0p hQ fr,
      h * fr.signChange (ffOpt J) = fr.signChange (ffOpt J) * h := by
    intro h hh
    have h1 := hc h hh
    rwa [ffHat_one, one_mul] at h1
  rw [ffHat_one, one_mul]
  have hJfix : ∀ τ ∈ ffD8p, ffAct τ J = J := by
    intro τ hτ
    have hτP0 : ffHat fr τ ∈ ffP0p hQ fr :=
      (mem_ffP0p_iff_hat hQ fr).mpr ⟨τ, hτ, 1, Subgroup.one_mem _, by rw [mul_one]⟩
    have hcomm := hc' (ffHat fr τ) hτP0
    have hgt : ffHat fr τ * fr.signChange (ffOpt J) * (ffHat fr τ)⁻¹ =
        fr.signChange (ffOpt J) := by
      have h1 : (ffHat fr τ * fr.signChange (ffOpt J) * (ffHat fr τ)⁻¹) * ffHat fr τ =
          fr.signChange (ffOpt J) * ffHat fr τ := by
        rw [hcomm]; group
      exact mul_right_cancel h1
    have hconjJ : fr.signChange (ffOpt (ffAct τ J)) = fr.signChange (ffOpt J) := by
      rw [← ffHat_conj_signChange_ffOpt fr τ J, hgt]
    exact (ffOpt_signChange_eq_iff fr).mp hconjJ
  rcases ffD8_invariant_even hJe hJfix with hJ | hJ
  · left
    rw [hJ, ffOpt, Finset.map_empty, fr.signChange_empty]
  · right
    rw [hJ, ffZ0p]

end CFSG.OddStandard.SmallF3.Omega
