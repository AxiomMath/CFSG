module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6POmega

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

@[expose] def ffD8g : Equiv.Perm (Fin 5) := Equiv.swap 0 2 * Equiv.swap 1 3

@[expose] def ffD8p : Subgroup (Equiv.Perm (Fin 5)) :=
  Subgroup.centralizer {ffD8g}

theorem mem_ffD8p_iff (σ : Equiv.Perm (Fin 5)) : σ ∈ ffD8p ↔ σ * ffD8g = ffD8g * σ :=
  Subgroup.mem_centralizer_singleton_iff

private instance ffD8pDecidableMem : DecidablePred (· ∈ ffD8p) := fun σ =>
  decidable_of_iff' (σ * ffD8g = ffD8g * σ) (mem_ffD8p_iff σ)

private theorem ffD8g_eq_self_iff (i : Fin 5) : ffD8g i = i ↔ i = 4 := by
  revert i; decide

private theorem ffD8g_four : ffD8g 4 = 4 := by decide

theorem ffD8p_card : Nat.card ↥ffD8p = 8 := by
  rw [Nat.card_eq_fintype_card,
    Fintype.card_subtype (fun σ : Equiv.Perm (Fin 5) => σ ∈ ffD8p)]
  decide

theorem ffD8p_apply_four {σ : Equiv.Perm (Fin 5)} (hσ : σ ∈ ffD8p) : σ 4 = 4 := by
  have h := (mem_ffD8p_iff σ).mp hσ
  have happ : σ (ffD8g 4) = ffD8g (σ 4) := by
    have hc := congrFun (congrArg (fun e : Equiv.Perm (Fin 5) => (e : Fin 5 → Fin 5)) h) 4
    simpa only [Equiv.Perm.mul_apply] using hc
  rw [ffD8g_four] at happ
  exact (ffD8g_eq_self_iff (σ 4)).mp happ.symm

@[expose] noncomputable def ffP0p (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC) :
    Subgroup (OGroup Q) where
  carrier := {g | ∃ σ ∈ ffD8p, ∃ K : Finset (Option (Fin 5)),
    g = fr.pOrth σ * fr.signChange K ∧ g ∈ omegaGroup hQ}
  one_mem' := ⟨1, Subgroup.one_mem _, ∅, by rw [fr.pOrth_one, fr.signChange_empty, one_mul],
    Subgroup.one_mem _⟩
  mul_mem' := by
    rintro a b ⟨σ, hσ, J, rfl, ha⟩ ⟨τ, hτ, K, rfl, hb⟩
    exact ⟨σ * τ, Subgroup.mul_mem _ hσ hτ,
      symmDiff (J.map (Equiv.optionCongr τ⁻¹).toEmbedding) K,
      ffMonoP_mul fr σ τ J K, Subgroup.mul_mem _ ha hb⟩
  inv_mem' := by
    rintro a ⟨σ, hσ, J, rfl, ha⟩
    refine ⟨σ⁻¹, Subgroup.inv_mem _ hσ, J.map (Equiv.optionCongr σ).toEmbedding, ?_,
      Subgroup.inv_mem _ ha⟩
    apply inv_eq_of_mul_eq_one_right
    rw [ffMonoP_mul fr σ σ⁻¹ J (J.map (Equiv.optionCongr σ).toEmbedding)]
    rw [show (σ⁻¹)⁻¹ = σ from inv_inv σ]
    rw [symmDiff_self, Finset.bot_eq_empty, fr.signChange_empty, mul_inv_cancel,
      fr.pOrth_one, one_mul]

theorem mem_ffP0p_iff (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC)
    {g : OGroup Q} :
    g ∈ ffP0p hQ fr ↔ ∃ σ ∈ ffD8p, ∃ K : Finset (Option (Fin 5)),
      g = fr.pOrth σ * fr.signChange K ∧ g ∈ omegaGroup hQ :=
  Iff.rfl

theorem ffP0p_le_omega (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC) :
    ffP0p hQ fr ≤ omegaGroup hQ := by
  rintro g ⟨σ, -, K, -, hgω⟩
  exact hgω

private theorem ffOptionCongr_eq_none_iff (σ : Equiv.Perm (Fin 5)) (i : Option (Fin 5)) :
    Equiv.optionCongr σ i = none ↔ i = none := by
  cases i <;> simp

private theorem ffSymmDiff_erase (K : Finset (Option (Fin 5))) (σ : Equiv.Perm (Fin 5))
    (h : none ∈ K ↔ Equiv.Perm.sign σ = -1) :
    symmDiff (if Equiv.Perm.sign σ = 1 then (∅ : Finset (Option (Fin 5))) else {none})
      (K.erase none) = K := by
  by_cases hn : none ∈ K
  · have hs : Equiv.Perm.sign σ = -1 := h.mp hn
    rw [if_neg (by rw [hs]; decide)]
    ext x
    by_cases hx : x = none
    · subst hx; simp [Finset.mem_symmDiff, hn]
    · simp [Finset.mem_symmDiff, Finset.mem_erase, hx]
  · have hs : Equiv.Perm.sign σ = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1
      · exact h1
      · exact absurd (h.mpr h1) hn
    rw [if_pos hs, ← Finset.bot_eq_empty, bot_symmDiff, Finset.erase_eq_of_notMem hn]

theorem ffB0p_le_omega (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC) :
    ffB0p fr ≤ omegaGroup hQ := by
  rintro g ⟨J, hJn, hJ, rfl⟩
  have heq : fr.pOrth (1 : Equiv.Perm (Fin 5)) * fr.signChange J = fr.signChange J := by
    rw [fr.pOrth_one, one_mul]
  rw [← heq]
  refine (ff6p_mem_omega_iff hQ fr 1 J).mpr ⟨?_, ?_⟩
  · rw [Equiv.Perm.sign_one]
    constructor
    · intro h; exact absurd h hJn
    · intro h; exact absurd h (by decide)
  · rwa [Finset.erase_eq_of_notMem hJn]

theorem ffB0p_le_ffP0p (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC) :
    ffB0p fr ≤ ffP0p hQ fr := by
  rintro g ⟨J, hJn, hJ, rfl⟩
  refine ⟨1, Subgroup.one_mem _, J, ?_, ?_⟩
  · rw [fr.pOrth_one, one_mul]
  · exact ffB0p_le_omega hQ fr ((mem_ffB0p_iff fr).mpr ⟨J, hJn, hJ, rfl⟩)

theorem ffP0p_le_ffMonoP (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC) :
    ffP0p hQ fr ≤ ffMonoP fr := by
  rintro g ⟨σ, -, K, rfl, -⟩
  exact mono_mem_ffMonoP fr σ K

theorem mem_ffP0p_iff_hat (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC)
    {g : OGroup Q} :
    g ∈ ffP0p hQ fr ↔ ∃ σ ∈ ffD8p, ∃ b ∈ ffB0p fr, g = ffHat fr σ * b := by
  constructor
  · rintro ⟨σ, hσ, K, hEq, hOm⟩
    have hcrit := (ff6p_mem_omega_iff hQ fr σ K).mp (hEq ▸ hOm)
    refine ⟨σ, hσ, fr.signChange (K.erase none),
      (mem_ffB0p_iff fr).mpr ⟨K.erase none, Finset.notMem_erase none K, hcrit.2, rfl⟩, ?_⟩
    rw [hEq, ffHat, mul_assoc, fr.signChange_mul, ffSymmDiff_erase K σ hcrit.1]
  · rintro ⟨σ, hσ, b, hb, rfl⟩
    obtain ⟨J, hJn, hJ, rfl⟩ := (mem_ffB0p_iff fr).mp hb
    refine ⟨σ, hσ, symmDiff (if Equiv.Perm.sign σ = 1 then
        (∅ : Finset (Option (Fin 5))) else {none}) J, ?_, ?_⟩
    · rw [ffHat, mul_assoc, fr.signChange_mul]
    · exact Subgroup.mul_mem _ (ffHat_mem_omega hQ fr σ)
        (ffB0p_le_omega hQ fr ((mem_ffB0p_iff fr).mpr ⟨J, hJn, hJ, rfl⟩))

theorem ffP0p_card (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC) :
    Nat.card ↥(ffP0p hQ fr) = 2 ^ 7 := by
  let F : ↥ffD8p × ↥(ffB0p fr) → ↥(ffP0p hQ fr) := fun x =>
    ⟨ffHat fr x.1 * x.2, (mem_ffP0p_iff_hat hQ fr).mpr ⟨x.1, x.1.2, x.2, x.2.2, rfl⟩⟩
  have hF : Function.Bijective F := by
    refine ⟨?_, ?_⟩
    · rintro ⟨⟨σ, hσ⟩, ⟨b, hb⟩⟩ ⟨⟨τ, hτ⟩, ⟨b', hb'⟩⟩ h
      have hg : ffHat fr σ * b = ffHat fr τ * b' := congrArg Subtype.val h
      obtain ⟨J, hJn, hJ, rfl⟩ := (mem_ffB0p_iff fr).mp hb
      obtain ⟨J', hJ'n, hJ', rfl⟩ := (mem_ffB0p_iff fr).mp hb'
      have hg' : fr.pOrth σ * fr.signChange
            (symmDiff (if Equiv.Perm.sign σ = 1 then
              (∅ : Finset (Option (Fin 5))) else {none}) J) =
          fr.pOrth τ * fr.signChange
            (symmDiff (if Equiv.Perm.sign τ = 1 then
              (∅ : Finset (Option (Fin 5))) else {none}) J') := by
        simpa only [ffHat, mul_assoc, fr.signChange_mul] using hg
      obtain ⟨hστ, hε⟩ := ffMonoP_unique fr hg'
      subst hστ
      have hJJ' : J = J' := by
        have hh := congrArg (fun X => symmDiff
          (if Equiv.Perm.sign σ = 1 then (∅ : Finset (Option (Fin 5))) else {none}) X) hε
        rwa [symmDiff_symmDiff_cancel_left, symmDiff_symmDiff_cancel_left] at hh
      cases hJJ'
      exact Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)
    · rintro ⟨g, hg⟩
      obtain ⟨σ, hσ, b, hb, hEq⟩ := (mem_ffP0p_iff_hat hQ fr).mp hg
      exact ⟨(⟨σ, hσ⟩, ⟨b, hb⟩), Subtype.ext hEq.symm⟩
  have hcard : Nat.card ↥(ffP0p hQ fr) = Nat.card (↥ffD8p × ↥(ffB0p fr)) :=
    (Nat.card_congr (Equiv.ofBijective F hF)).symm
  calc Nat.card ↥(ffP0p hQ fr) = Nat.card (↥ffD8p × ↥(ffB0p fr)) := hcard
    _ = Nat.card ↥ffD8p * Nat.card ↥(ffB0p fr) := Nat.card_prod _ _
    _ = 8 * 16 := by rw [ffD8p_card, ffB0p_card]
    _ = 2 ^ 7 := by norm_num

theorem ffB0p_normal_ffP0p (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC) :
    ((ffB0p fr).subgroupOf (ffP0p hQ fr)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn
  rw [Subgroup.mem_subgroupOf]
  obtain ⟨J, hJn, hJ, hnJ⟩ := (mem_ffB0p_iff fr).mp hn
  obtain ⟨σ, hσ, K, hgK, -⟩ := (mem_ffP0p_iff hQ fr).mp g.2
  change (g : OGroup Q) * (n : OGroup Q) * (g : OGroup Q)⁻¹ ∈ ffB0p fr
  rw [hnJ, hgK, ffMonoP_conj_signChange fr σ K J]
  exact (mem_ffB0p_iff fr).mpr ⟨J.map (Equiv.optionCongr σ).toEmbedding,
    by
      rw [Finset.mem_map]
      rintro ⟨i, hi, hσi⟩
      exact hJn ((ffOptionCongr_eq_none_iff σ i).mp hσi ▸ hi),
    by rw [Finset.card_map]; exact hJ, rfl⟩

end CFSG.OddStandard.SmallF3.Omega
