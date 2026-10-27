module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFStarNorm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFMonoOmega

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem ffConjMono (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) 1)
    (σ : Equiv.Perm (Fin 6)) {K J : Finset (Fin 6)}
    (hK : fr.permOrth σ * fr.signChange K ∈ omegaGroup hQ)
    (hJ : fr.signChange J ∈ omegaGroup hQ)
    (hJmap : fr.signChange (J.map σ.toEmbedding) ∈ omegaGroup hQ) :
    omegaToProj hQ ⟨fr.permOrth σ * fr.signChange K, hK⟩ *
        omegaToProj hQ ⟨fr.signChange J, hJ⟩ *
        (omegaToProj hQ ⟨fr.permOrth σ * fr.signChange K, hK⟩)⁻¹ =
      omegaToProj hQ ⟨fr.signChange (J.map σ.toEmbedding), hJmap⟩ := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_omegaToProj]
  rw [← map_mul, ← map_inv, ← map_mul, ffMono_conj_signChange fr σ K J]

private theorem ff_toProj_signChange_compl (fr : NFrame Q (Fin 6) 1) (J : Finset (Fin 6)) :
    toProj Q (fr.signChange Jᶜ) = toProj Q (fr.signChange J) := by
  rw [show Jᶜ = symmDiff Finset.univ J by ext i; simp [Finset.mem_symmDiff],
    ← fr.signChange_mul, ← fr.piOrth_eq_signChange_univ, map_mul, toProj_piOrth, one_mul]

private theorem ff_map_eq_or_compl_of_omega_eq (hQ : Q.Nondegenerate)
    (fr : NFrame Q (Fin 6) 1) (σ : Equiv.Perm (Fin 6)) {J : Finset (Fin 6)}
    (hJω : fr.signChange J ∈ omegaGroup hQ)
    (hJmapω : fr.signChange (J.map σ.toEmbedding) ∈ omegaGroup hQ)
    (heq : omegaToProj hQ ⟨fr.signChange (J.map σ.toEmbedding), hJmapω⟩ =
      omegaToProj hQ ⟨fr.signChange J, hJω⟩) :
    J.map σ.toEmbedding = J ∨ J.map σ.toEmbedding = Jᶜ := by
  rcases omegaToProj_eq_iff hQ heq with h | h
  · left
    exact (fr.signChange_injective h).symm
  · right
    have h' : fr.signChange J = piOrth Q * fr.signChange (J.map σ.toEmbedding) := h
    have h2 : fr.signChange J = fr.signChange ((J.map σ.toEmbedding)ᶜ) := by
      rw [h', fr.piOrth_eq_signChange_univ, fr.signChange_mul,
        show symmDiff Finset.univ (J.map σ.toEmbedding) = (J.map σ.toEmbedding)ᶜ by
          ext i; simp [Finset.mem_symmDiff]]
    have h3 : J = (J.map σ.toEmbedding)ᶜ := fr.signChange_injective h2
    have h4 : J.map σ.toEmbedding = Jᶜ := by
      simpa using (congrArg compl h3).symm
    exact h4

private theorem ff_mem_ffB1_exists (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) 1)
    {b : ↥(omegaProj hQ)} (hb : b ∈ ffB1 hQ fr) :
    ∃ (J : Finset (Fin 6)) (hJe : Even J.card),
      b = omegaToProj hQ ⟨fr.signChange J, ffB0_le_omega hQ fr (signChange_mem_ffB0 fr hJe)⟩ := by
  have hb' : b ∈ ffStar hQ (ffB0 fr) := hb
  rw [mem_ffStar_iff hQ] at hb'
  obtain ⟨g, hgB0, hgb⟩ := hb'
  obtain ⟨J, hJe, hgJ⟩ := (mem_ffB0_iff fr).mp hgB0
  exact ⟨J, hJe, by
    rw [← hgb]
    exact congrArg (omegaToProj hQ) (Subtype.ext hgJ)⟩

@[expose] noncomputable def ffPermStar (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) 1) :
    alternatingGroup (Fin 6) →* ↥(omegaProj hQ) where
  toFun σ := omegaToProj hQ ⟨fr.permOrth (σ : Equiv.Perm (Fin 6)),
    fr.permOrth_mem_omegaGroup hQ σ.2⟩
  map_one' := by
    have hst : (⟨fr.permOrth ((1 : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)),
        fr.permOrth_mem_omegaGroup hQ (1 : alternatingGroup (Fin 6)).2⟩ :
        ↥(omegaGroup hQ)) = 1 := by
      apply Subtype.ext
      change fr.permOrth ((1 : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) = 1
      rw [Subgroup.coe_one, fr.permOrth_one]
    rw [hst, map_one]
  map_mul' σ τ := by
    have hst : (⟨fr.permOrth ((σ * τ : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)),
        fr.permOrth_mem_omegaGroup hQ (σ * τ).2⟩ : ↥(omegaGroup hQ)) =
        ⟨fr.permOrth (σ : Equiv.Perm (Fin 6)), fr.permOrth_mem_omegaGroup hQ σ.2⟩ *
        ⟨fr.permOrth (τ : Equiv.Perm (Fin 6)), fr.permOrth_mem_omegaGroup hQ τ.2⟩ := by
      apply Subtype.ext
      change fr.permOrth (((σ * τ : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6))) =
        fr.permOrth (σ : Equiv.Perm (Fin 6)) * fr.permOrth (τ : Equiv.Perm (Fin 6))
      rw [Subgroup.coe_mul, fr.permOrth_mul]
    rw [hst, map_mul]

theorem ffPermStar_apply (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) 1)
    (σ : alternatingGroup (Fin 6)) :
    ffPermStar hQ fr σ = omegaToProj hQ ⟨fr.permOrth (σ : Equiv.Perm (Fin 6)),
      fr.permOrth_mem_omegaGroup hQ σ.2⟩ :=
  rfl

theorem ffPermStar_conj (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) 1)
    (σ : alternatingGroup (Fin 6)) {J : Finset (Fin 6)} (hJ : Even J.card)
    (h₁ : fr.signChange J ∈ omegaGroup hQ)
    (h₂ : fr.signChange (J.map (σ : Equiv.Perm (Fin 6)).toEmbedding) ∈ omegaGroup hQ) :
    ffPermStar hQ fr σ * omegaToProj hQ ⟨fr.signChange J, h₁⟩ * (ffPermStar hQ fr σ)⁻¹ =
      omegaToProj hQ ⟨fr.signChange (J.map (σ : Equiv.Perm (Fin 6)).toEmbedding), h₂⟩ := by
  have hA : fr.permOrth (σ : Equiv.Perm (Fin 6)) * fr.signChange ∅ ∈ omegaGroup hQ := by
    rw [fr.signChange_empty, mul_one]
    exact fr.permOrth_mem_omegaGroup hQ σ.2
  have h := ffConjMono hQ fr (σ : Equiv.Perm (Fin 6)) (K := ∅) (J := J) hA h₁ h₂
  simpa [ffPermStar_apply, fr.signChange_empty] using h

private theorem ffPermStar_conj_mem (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) 1)
    (σ : alternatingGroup (Fin 6)) {b : ↥(omegaProj hQ)} (hb : b ∈ ffB1 hQ fr) :
    ffPermStar hQ fr σ * b * (ffPermStar hQ fr σ)⁻¹ ∈ ffB1 hQ fr := by
  obtain ⟨J, hJe, hbJ⟩ := ff_mem_ffB1_exists hQ fr hb
  have hJω : fr.signChange J ∈ omegaGroup hQ := ffB0_le_omega hQ fr (signChange_mem_ffB0 fr hJe)
  have hJmapω : fr.signChange (J.map (σ : Equiv.Perm (Fin 6)).toEmbedding) ∈ omegaGroup hQ :=
    ffB0_le_omega hQ fr (signChange_mem_ffB0 fr (by rw [Finset.card_map]; exact hJe))
  rw [hbJ, ffPermStar_conj hQ fr σ hJe hJω hJmapω]
  exact (mem_ffStar_iff hQ).mpr
    ⟨⟨fr.signChange (J.map (σ : Equiv.Perm (Fin 6)).toEmbedding), hJmapω⟩,
      signChange_mem_ffB0 fr (by rw [Finset.card_map]; exact hJe), rfl⟩

theorem ffPermStar_mem_normalizer (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (fr : NFrame Q (Fin 6) 1) (σ : alternatingGroup (Fin 6)) :
    ffPermStar hQ fr σ ∈
      Subgroup.normalizer ((ffB1 hQ fr : Subgroup ↥(omegaProj hQ)) : Set ↥(omegaProj hQ)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · exact ffPermStar_conj_mem hQ fr σ
  · intro hb
    have h1 := ffPermStar_conj_mem hQ fr σ⁻¹ hb
    have heq : ffPermStar hQ fr σ⁻¹ *
        (ffPermStar hQ fr σ * b * (ffPermStar hQ fr σ)⁻¹) *
        (ffPermStar hQ fr σ⁻¹)⁻¹ = b := by
      rw [map_inv]
      group
    rwa [heq] at h1

theorem ff_star_cent_omega (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (fr : NFrame Q (Fin 6) 1) :
    ∀ n : ↥(omegaProj hQ), (∀ b ∈ ffB1 hQ fr, n * b = b * n) → n ∈ ffB1 hQ fr := by
  intro n hcomm
  have hnrm : n ∈ Subgroup.normalizer
      ((ffB1 hQ fr : Subgroup ↥(omegaProj hQ)) : Set ↥(omegaProj hQ)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      rwa [show n * b * n⁻¹ = b by rw [hcomm b hb]; group]
    · intro hb
      have h1 : n * b = n * (n * b * n⁻¹) := by
        calc n * b = (n * b * n⁻¹) * n := by group
          _ = n * (n * b * n⁻¹) := by rw [hcomm (n * b * n⁻¹) hb]
      have h2 : b = n * b * n⁻¹ := mul_left_cancel h1
      rwa [h2]
  obtain ⟨σ, K, hK, hn_eq⟩ := ff_star_normalizer hQ hdim hsgn fr hnrm
  obtain ⟨hσ, hKe⟩ := (ffMono_mem_omega_iff hQ fr σ K).mp hK
  have hperm : ∀ J : Finset (Fin 6), Even J.card →
      J.map σ.toEmbedding = J ∨ J.map σ.toEmbedding = Jᶜ := by
    intro J hJe
    have hJω : fr.signChange J ∈ omegaGroup hQ :=
      ffB0_le_omega hQ fr (signChange_mem_ffB0 fr hJe)
    have hJb : omegaToProj hQ ⟨fr.signChange J, hJω⟩ ∈ ffB1 hQ fr :=
      (mem_ffStar_iff hQ).mpr ⟨⟨_, hJω⟩, signChange_mem_ffB0 fr hJe, rfl⟩
    have hfix : n * omegaToProj hQ ⟨fr.signChange J, hJω⟩ * n⁻¹ =
        omegaToProj hQ ⟨fr.signChange J, hJω⟩ := by
      rw [hcomm _ hJb]; group
    rw [hn_eq] at hfix
    have hJmapω : fr.signChange (J.map σ.toEmbedding) ∈ omegaGroup hQ :=
      ffB0_le_omega hQ fr (signChange_mem_ffB0 fr (by rw [Finset.card_map]; exact hJe))
    rw [ffConjMono hQ fr σ hK hJω hJmapω] at hfix
    exact ff_map_eq_or_compl_of_omega_eq hQ fr σ hJω hJmapω hfix
  have hσ1 : σ = 1 := ff_perm_eq_one_of_even σ hperm
  have hKω : fr.signChange K ∈ omegaGroup hQ :=
    ffB0_le_omega hQ fr (signChange_mem_ffB0 fr hKe)
  have hnB : n = omegaToProj hQ ⟨fr.signChange K, hKω⟩ := by
    have hst : (⟨fr.permOrth σ * fr.signChange K, hK⟩ : ↥(omegaGroup hQ)) =
        ⟨fr.signChange K, hKω⟩ := by
      apply Subtype.ext
      change fr.permOrth σ * fr.signChange K = fr.signChange K
      rw [hσ1, fr.permOrth_one, one_mul]
    rw [hn_eq]
    exact congrArg (omegaToProj hQ) hst
  rw [hnB]
  exact (mem_ffStar_iff hQ).mpr
    ⟨⟨fr.signChange K, hKω⟩, signChange_mem_ffB0 fr hKe, rfl⟩

theorem ff_star_trans (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (fr : NFrame Q (Fin 6) 1) :
    ∀ b ∈ ffB1 hQ fr, b ≠ 1 → ∀ b' ∈ ffB1 hQ fr, b' ≠ 1 →
      ∃ n ∈ Subgroup.normalizer ((ffB1 hQ fr : Subgroup ↥(omegaProj hQ)) : Set ↥(omegaProj hQ)),
        n * b * n⁻¹ = b' := by
  intro b hb hb1 b' hb' hb'1
  obtain ⟨J, hJe, hbJ⟩ := ff_mem_ffB1_exists hQ fr hb
  have hJω : fr.signChange J ∈ omegaGroup hQ :=
    ffB0_le_omega hQ fr (signChange_mem_ffB0 fr hJe)
  obtain ⟨J', hJ'e, hb'J'⟩ := ff_mem_ffB1_exists hQ fr hb'
  have hJ'ω : fr.signChange J' ∈ omegaGroup hQ :=
    ffB0_le_omega hQ fr (signChange_mem_ffB0 fr hJ'e)
  have hJ0 : J ≠ ∅ := by
    intro h0
    apply hb1
    rw [hbJ]
    have hst : (⟨fr.signChange J, hJω⟩ : ↥(omegaGroup hQ)) = 1 := by
      apply Subtype.ext
      change fr.signChange J = 1
      rw [h0, fr.signChange_empty]
    rw [hst]
    exact map_one _
  have hJ1 : J ≠ Finset.univ := by
    intro h1
    apply hb1
    rw [hbJ]
    have hst : (⟨fr.signChange J, hJω⟩ : ↥(omegaGroup hQ)) =
        ⟨piOrth Q, ff_piOrth_mem_omegaGroup_six_minus hQ hdim hsgn⟩ := by
      apply Subtype.ext
      change fr.signChange J = piOrth Q
      rw [h1, ← fr.piOrth_eq_signChange_univ]
    rw [hst]
    exact (omegaToProj_eq_one_iff hQ _).mpr (Or.inr rfl)
  have hJ'0 : J' ≠ ∅ := by
    intro h0
    apply hb'1
    rw [hb'J']
    have hst : (⟨fr.signChange J', hJ'ω⟩ : ↥(omegaGroup hQ)) = 1 := by
      apply Subtype.ext
      change fr.signChange J' = 1
      rw [h0, fr.signChange_empty]
    rw [hst]
    exact map_one _
  have hJ'1 : J' ≠ Finset.univ := by
    intro h1
    apply hb'1
    rw [hb'J']
    have hst : (⟨fr.signChange J', hJ'ω⟩ : ↥(omegaGroup hQ)) =
        ⟨piOrth Q, ff_piOrth_mem_omegaGroup_six_minus hQ hdim hsgn⟩ := by
      apply Subtype.ext
      change fr.signChange J' = piOrth Q
      rw [h1, ← fr.piOrth_eq_signChange_univ]
    rw [hst]
    exact (omegaToProj_eq_one_iff hQ _).mpr (Or.inr rfl)
  obtain ⟨σ, hσ, hJσ⟩ := ff_alt_trans_even hJe hJ'e hJ0 hJ1 hJ'0 hJ'1
  refine ⟨ffPermStar hQ fr ⟨σ, hσ⟩, ffPermStar_mem_normalizer hQ hdim hsgn fr ⟨σ, hσ⟩, ?_⟩
  rw [hbJ, hb'J']
  have hJmapω : fr.signChange (J.map σ.toEmbedding) ∈ omegaGroup hQ :=
    ffB0_le_omega hQ fr (signChange_mem_ffB0 fr (by rw [Finset.card_map]; exact hJe))
  rw [ffPermStar_conj hQ fr ⟨σ, hσ⟩ hJe hJω hJmapω]
  rcases hJσ with h | h
  · exact congrArg (omegaToProj hQ) (Subtype.ext (by
      change fr.signChange (J.map σ.toEmbedding) = fr.signChange J'
      rw [h]))
  · apply Subtype.ext
    rw [coe_omegaToProj, coe_omegaToProj]
    change toProj Q (fr.signChange (J.map σ.toEmbedding)) = toProj Q (fr.signChange J')
    rw [h]
    exact ff_toProj_signChange_compl fr J'

@[expose] noncomputable def ffStarLambda (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = -1) (fr : NFrame Q (Fin 6) 1) :
    alternatingGroup (Fin 6) →* MulAut ↥(ffB1 hQ fr) :=
  (Subgroup.normalizerMonoidHom (ffB1 hQ fr)).comp
    ((ffPermStar hQ fr).codRestrict
      (Subgroup.normalizer ((ffB1 hQ fr : Subgroup ↥(omegaProj hQ)) : Set ↥(omegaProj hQ)))
      (ffPermStar_mem_normalizer hQ hdim hsgn fr))

theorem ffStarLambda_apply (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (fr : NFrame Q (Fin 6) 1) (σ : alternatingGroup (Fin 6))
    (b : ↥(ffB1 hQ fr)) :
    ((ffStarLambda hQ hdim hsgn fr σ b : ↥(ffB1 hQ fr)) : ↥(omegaProj hQ)) =
      ffPermStar hQ fr σ * (b : ↥(omegaProj hQ)) * (ffPermStar hQ fr σ)⁻¹ := by
  have h1 : ffStarLambda hQ hdim hsgn fr σ b =
      (Subgroup.normalizerMonoidHom (ffB1 hQ fr) ⟨ffPermStar hQ fr σ,
        ffPermStar_mem_normalizer hQ hdim hsgn fr σ⟩) b := rfl
  rw [h1, Subgroup.normalizerMonoidHom_apply_apply_coe]

theorem ffStarLambda_injective (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (fr : NFrame Q (Fin 6) 1) :
    Function.Injective (ffStarLambda hQ hdim hsgn fr) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  have hperm : ∀ J : Finset (Fin 6), Even J.card →
      J.map (σ : Equiv.Perm (Fin 6)).toEmbedding = J ∨
        J.map (σ : Equiv.Perm (Fin 6)).toEmbedding = Jᶜ := by
    intro J hJe
    have hJω : fr.signChange J ∈ omegaGroup hQ :=
      ffB0_le_omega hQ fr (signChange_mem_ffB0 fr hJe)
    have hJb : omegaToProj hQ ⟨fr.signChange J, hJω⟩ ∈ ffB1 hQ fr :=
      (mem_ffStar_iff hQ).mpr ⟨⟨_, hJω⟩, signChange_mem_ffB0 fr hJe, rfl⟩
    have happ : (ffStarLambda hQ hdim hsgn fr σ)
        ⟨omegaToProj hQ ⟨fr.signChange J, hJω⟩, hJb⟩ =
        ⟨omegaToProj hQ ⟨fr.signChange J, hJω⟩, hJb⟩ := by
      rw [hσ]; rfl
    have happ' : ((ffStarLambda hQ hdim hsgn fr σ
        ⟨omegaToProj hQ ⟨fr.signChange J, hJω⟩, hJb⟩ : ↥(ffB1 hQ fr)) :
          ↥(omegaProj hQ)) = omegaToProj hQ ⟨fr.signChange J, hJω⟩ :=
      congrArg Subtype.val happ
    rw [ffStarLambda_apply] at happ'
    have hJmapω : fr.signChange (J.map (σ : Equiv.Perm (Fin 6)).toEmbedding) ∈ omegaGroup hQ :=
      ffB0_le_omega hQ fr (signChange_mem_ffB0 fr (by rw [Finset.card_map]; exact hJe))
    rw [ffPermStar_conj hQ fr σ hJe hJω hJmapω] at happ'
    exact ff_map_eq_or_compl_of_omega_eq hQ fr (σ : Equiv.Perm (Fin 6)) hJω hJmapω happ'
  have hσ1 : (σ : Equiv.Perm (Fin 6)) = 1 := ff_perm_eq_one_of_even σ hperm
  exact Subtype.ext hσ1

theorem ff_star_autIn_eq_range (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (fr : NFrame Q (Fin 6) 1) :
    autIn (⊤ : Subgroup ↥(omegaProj hQ)) (ffB1 hQ fr) = (ffStarLambda hQ hdim hsgn fr).range := by
  ext f
  rw [autIn, Subgroup.mem_map]
  constructor
  · rintro ⟨n, _, rfl⟩
    obtain ⟨σ, K, hK, hn_eq⟩ := ff_star_normalizer hQ hdim hsgn fr n.2
    obtain ⟨hσ, hKe⟩ := (ffMono_mem_omega_iff hQ fr σ K).mp hK
    refine ⟨⟨σ, hσ⟩, ?_⟩
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, ffStarLambda_apply]
    have hKω : fr.signChange K ∈ omegaGroup hQ :=
      ffB0_le_omega hQ fr (signChange_mem_ffB0 fr hKe)
    have hcB : omegaToProj hQ ⟨fr.signChange K, hKω⟩ ∈ ffB1 hQ fr :=
      (mem_ffStar_iff hQ).mpr ⟨⟨_, hKω⟩, signChange_mem_ffB0 fr hKe, rfl⟩
    have hn_split : (n : ↥(omegaProj hQ)) = ffPermStar hQ fr ⟨σ, hσ⟩ *
        omegaToProj hQ ⟨fr.signChange K, hKω⟩ := by
      rw [hn_eq, ffPermStar_apply, ← map_mul]
      rfl
    have hcc : omegaToProj hQ ⟨fr.signChange K, hKω⟩ * b =
        b * omegaToProj hQ ⟨fr.signChange K, hKω⟩ := by
      haveI : IsMulCommutative ↥(ffB1 hQ fr) := (ffB1_elemAb2 hQ hdim hsgn fr).1.1
      exact congrArg Subtype.val (mul_comm' (⟨_, hcB⟩ : ↥(ffB1 hQ fr)) b)
    rw [hn_split]
    have hkey : (ffPermStar hQ fr ⟨σ, hσ⟩ * omegaToProj hQ ⟨fr.signChange K, hKω⟩) * b *
        (ffPermStar hQ fr ⟨σ, hσ⟩ * omegaToProj hQ ⟨fr.signChange K, hKω⟩)⁻¹ =
        ffPermStar hQ fr ⟨σ, hσ⟩ * b * (ffPermStar hQ fr ⟨σ, hσ⟩)⁻¹ := by
      rw [show (ffPermStar hQ fr ⟨σ, hσ⟩ * omegaToProj hQ ⟨fr.signChange K, hKω⟩) * b *
            (ffPermStar hQ fr ⟨σ, hσ⟩ * omegaToProj hQ ⟨fr.signChange K, hKω⟩)⁻¹ =
          ffPermStar hQ fr ⟨σ, hσ⟩ *
            (omegaToProj hQ ⟨fr.signChange K, hKω⟩ * b *
              (omegaToProj hQ ⟨fr.signChange K, hKω⟩)⁻¹) *
            (ffPermStar hQ fr ⟨σ, hσ⟩)⁻¹ by group,
        show omegaToProj hQ ⟨fr.signChange K, hKω⟩ * b *
              (omegaToProj hQ ⟨fr.signChange K, hKω⟩)⁻¹ = b by rw [hcc]; group]
    exact hkey.symm
  · rintro ⟨σ, rfl⟩
    exact ⟨⟨ffPermStar hQ fr σ, ffPermStar_mem_normalizer hQ hdim hsgn fr σ⟩,
      by rw [Subgroup.mem_subgroupOf]; exact Subgroup.mem_top _, rfl⟩

theorem ff_star_autIn_equiv (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (fr : NFrame Q (Fin 6) 1) :
    Nonempty (↥(autIn (⊤ : Subgroup ↥(omegaProj hQ)) (ffB1 hQ fr)) ≃*
      alternatingGroup (Fin 6)) := by
  refine ⟨?_⟩
  exact ((MonoidHom.ofInjective (ffStarLambda_injective hQ hdim hsgn fr)).trans
    (MulEquiv.subgroupCongr (ff_star_autIn_eq_range hQ hdim hsgn fr).symm)).symm

end CFSG.OddStandard.SmallF3.Omega
