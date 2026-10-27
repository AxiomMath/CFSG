module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFThetaSylow
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFStarNorm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFMonoOmega
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MFix
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SGU1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private noncomputable def ffOutMonoMap (Q : QuadraticForm (ZMod 3) V) :
    OGroup Q →* ProjSim Q :=
  (projOrthToProjSim Q).comp (toProj Q)

private theorem ffOutMonoMap_congr {a b : OGroup Q} (h : toProj Q a = toProj Q b) :
    ffOutMonoMap Q a = ffOutMonoMap Q b := by
  change projOrthToProjSim Q (toProj Q a) = projOrthToProjSim Q (toProj Q b)
  rw [h]

private theorem ffOutMono_toProj_signChange_compl (fr : NFrame Q (Fin 6) 1)
    (K : Finset (Fin 6)) :
    toProj Q (fr.signChange Kᶜ) = toProj Q (fr.signChange K) := by
  rw [show Kᶜ = symmDiff Finset.univ K by ext i; simp [Finset.mem_symmDiff],
    ← fr.signChange_mul, ← fr.piOrth_eq_signChange_univ, map_mul, toProj_piOrth, one_mul]

private theorem ffOutMono_even_compl {K : Finset (Fin 6)} (hK : Even K.card) :
    Even Kᶜ.card := by
  obtain ⟨m, hm⟩ := hK
  have hle : K.card ≤ 6 := by simpa using Finset.card_le_univ K
  rw [Finset.card_compl, Fintype.card_fin]
  refine ⟨3 - m, ?_⟩
  omega

private theorem ffOutMono_projOrthToProjSim_projSimAct (δ : ProjSim Q) (y : ProjOrth Q) :
    projOrthToProjSim Q (projSimAct Q δ y) = δ * projOrthToProjSim Q y * δ⁻¹ := by
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective δ
  obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective (piGroup Q) y
  change QuotientGroup.mk (orthToSim Q (simAct Q γ t)) =
    QuotientGroup.mk γ * QuotientGroup.mk (orthToSim Q t) * (QuotientGroup.mk γ)⁻¹
  rw [sec9u_orthToSim_simAct, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]

private theorem ffOutMono_omegaToSim_act (hQ : Q.Nondegenerate)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) (x : ProjSim Q) (w : ↥(omegaProj hQ)) :
    ffOmegaToSim hQ (ffSimOmegaAct hQ h2 x w) = x * ffOmegaToSim hQ w * x⁻¹ := by
  rw [ffOmegaToSim_apply, coe_ffSimOmegaAct]
  exact ffOutMono_projOrthToProjSim_projSimAct x (w : ProjOrth Q)

@[expose] noncomputable def ffM (fr : NFrame Q (Fin 6) 1) (σ : Equiv.Perm (Fin 6))
    (K : Finset (Fin 6)) : ProjSim Q :=
  projOrthToProjSim Q (toProj Q (fr.permOrth σ * fr.signChange K))

private theorem ffM_one_signChange (fr : NFrame Q (Fin 6) 1) (J : Finset (Fin 6)) :
    ffM fr 1 J = ffOutMonoMap Q (fr.signChange J) := by
  change ffOutMonoMap Q (fr.permOrth 1 * fr.signChange J) =
    ffOutMonoMap Q (fr.signChange J)
  rw [fr.permOrth_one, one_mul]

theorem ffM_mul (fr : NFrame Q (Fin 6) 1) (σ τ : Equiv.Perm (Fin 6)) (J K : Finset (Fin 6)) :
    ffM fr σ J * ffM fr τ K = ffM fr (σ * τ) (symmDiff (J.map τ⁻¹.toEmbedding) K) := by
  change ffOutMonoMap Q (fr.permOrth σ * fr.signChange J) *
      ffOutMonoMap Q (fr.permOrth τ * fr.signChange K) =
      ffOutMonoMap Q (fr.permOrth (σ * τ) *
        fr.signChange (symmDiff (J.map τ⁻¹.toEmbedding) K))
  rw [← map_mul, ffMono_mul]

theorem ffM_one (fr : NFrame Q (Fin 6) 1) : ffM fr 1 ∅ = 1 := by
  change ffOutMonoMap Q (fr.permOrth 1 * fr.signChange ∅) = 1
  rw [fr.permOrth_one, fr.signChange_empty, mul_one, map_one]

theorem ffM_univ (fr : NFrame Q (Fin 6) 1) : ffM fr 1 Finset.univ = 1 := by
  change ffOutMonoMap Q (fr.permOrth 1 * fr.signChange Finset.univ) = 1
  rw [fr.permOrth_one, one_mul, ← fr.piOrth_eq_signChange_univ]
  change projOrthToProjSim Q (toProj Q (piOrth Q)) = 1
  rw [toProj_piOrth, map_one]

theorem ffM_compl (fr : NFrame Q (Fin 6) 1) (σ : Equiv.Perm (Fin 6)) (K : Finset (Fin 6)) :
    ffM fr σ Kᶜ = ffM fr σ K := by
  change ffOutMonoMap Q (fr.permOrth σ * fr.signChange Kᶜ) =
    ffOutMonoMap Q (fr.permOrth σ * fr.signChange K)
  apply ffOutMonoMap_congr
  rw [map_mul, map_mul, ffOutMono_toProj_signChange_compl]

theorem ffM_eq_iff (fr : NFrame Q (Fin 6) 1) {σ τ : Equiv.Perm (Fin 6)} {J K : Finset (Fin 6)} :
    ffM fr σ J = ffM fr τ K ↔ σ = τ ∧ (J = K ∨ J = Kᶜ) := by
  constructor
  · intro h
    have h' : toProj Q (fr.permOrth σ * fr.signChange J) =
        toProj Q (fr.permOrth τ * fr.signChange K) := projOrthToProjSim_injective h
    have hker : (fr.permOrth σ * fr.signChange J)⁻¹ *
        (fr.permOrth τ * fr.signChange K) ∈ piGroup Q := QuotientGroup.eq.mp h'
    rcases mem_piGroup_iff.mp hker with h1 | h2
    · have heq : fr.permOrth σ * fr.signChange J =
          fr.permOrth τ * fr.signChange K := inv_mul_eq_one.mp h1
      obtain ⟨hστ, hJK⟩ := ffMono_unique fr heq
      exact ⟨hστ, Or.inl hJK⟩
    · have hb : fr.permOrth τ * fr.signChange K =
          fr.permOrth σ * fr.signChange Jᶜ := by
        rw [inv_mul_eq_iff_eq_mul.mp h2, fr.piOrth_eq_signChange_univ, mul_assoc,
          fr.signChange_mul]
        congr 2
        ext i
        simp [Finset.mem_symmDiff]
      obtain ⟨hτσ, hKJ⟩ := ffMono_unique fr hb
      exact ⟨hτσ.symm, Or.inr (by rw [hKJ, compl_compl])⟩
  · rintro ⟨rfl, hJK | hJK⟩
    · rw [hJK]
    · rw [hJK, ffM_compl]

theorem ffM_inv (fr : NFrame Q (Fin 6) 1) (σ : Equiv.Perm (Fin 6)) (K : Finset (Fin 6)) :
    (ffM fr σ K)⁻¹ = ffM fr σ⁻¹ (K.map σ.toEmbedding) := by
  apply inv_eq_of_mul_eq_one_right
  calc ffM fr σ K * ffM fr σ⁻¹ (K.map σ.toEmbedding)
      = ffM fr (σ * σ⁻¹) (symmDiff (K.map (σ⁻¹)⁻¹.toEmbedding)
          (K.map σ.toEmbedding)) := ffM_mul fr σ σ⁻¹ K (K.map σ.toEmbedding)
    _ = ffM fr 1 ∅ := by
      rw [mul_inv_cancel, inv_inv, symmDiff_self, Finset.bot_eq_empty]
    _ = 1 := ffM_one fr

theorem ffM_conj_signChange (fr : NFrame Q (Fin 6) 1) (σ : Equiv.Perm (Fin 6))
    (J K : Finset (Fin 6)) :
    ffM fr σ J * ffM fr 1 K * (ffM fr σ J)⁻¹ = ffM fr 1 (K.map σ.toEmbedding) := by
  have h := congrArg (ffOutMonoMap Q) (ffMono_conj_signChange fr σ J K)
  simp only [map_mul, map_inv, ffM, ffOutMonoMap, MonoidHom.comp_apply,
    fr.permOrth_one, one_mul] at h ⊢
  exact h

theorem ffM_conj_perm (fr : NFrame Q (Fin 6) 1) (σ τ : Equiv.Perm (Fin 6))
    (K J : Finset (Fin 6)) :
    ∃ K' : Finset (Fin 6), ffM fr σ K * ffM fr τ J * (ffM fr σ K)⁻¹ = ffM fr (σ * τ * σ⁻¹) K' := by
  refine ⟨symmDiff (K.map ((τ * σ⁻¹)⁻¹).toEmbedding)
    (symmDiff (J.map σ.toEmbedding) (K.map σ.toEmbedding)), ?_⟩
  rw [ffM_inv, mul_assoc, ffM_mul, inv_inv, ffM_mul, mul_assoc]

theorem ffM_simInGStar (fr : NFrame Q (Fin 6) 1) (σ : Equiv.Perm (Fin 6)) (K : Finset (Fin 6)) :
    SimInGStar (ffM fr σ K) :=
  ⟨toProj Q (fr.permOrth σ * fr.signChange K), rfl⟩

@[expose] noncomputable def ffPS (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) 1) :
    Subgroup (ProjSim Q) :=
  (ffP1 hQ fr).map (ffOmegaToSim hQ)

@[expose] noncomputable def ffBS (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) 1) :
    Subgroup (ProjSim Q) :=
  (ffB1 hQ fr).map (ffOmegaToSim hQ)

theorem mem_ffPS_iff (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) 1) {x : ProjSim Q} :
    x ∈ ffPS hQ fr ↔ ∃ σ ∈ monoD, ∃ J : Finset (Fin 6), Even J.card ∧ x = ffM fr σ J := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    change w ∈ ffStar hQ (ffP0 hQ fr) at hw
    rw [mem_ffStar_iff] at hw
    obtain ⟨g, hg, rfl⟩ := hw
    obtain ⟨σ, hσ, J, hJ, hge⟩ := (mem_ffP0_iff hQ fr).mp hg
    have hgP : fr.permOrth σ * fr.signChange J ∈ ffP0 hQ fr := hge ▸ hg
    have hgω : fr.permOrth σ * fr.signChange J ∈ omegaGroup hQ := ffP0_le_omega hQ fr hgP
    have hg' : g = ⟨fr.permOrth σ * fr.signChange J, hgω⟩ := Subtype.ext hge
    rw [hg']
    exact ⟨σ, hσ, J, hJ, by rw [ffOmegaToSim_apply, coe_omegaToProj]; rfl⟩
  · rintro ⟨σ, hσ, J, hJ, rfl⟩
    have hp : fr.permOrth σ * fr.signChange J ∈ omegaGroup hQ :=
      ffP0_le_omega hQ fr ((mem_ffP0_iff hQ fr).mpr ⟨σ, hσ, J, hJ, rfl⟩)
    refine Subgroup.mem_map.mpr ⟨omegaToProj hQ ⟨_, hp⟩, ?_, ?_⟩
    · exact (mem_ffStar_iff hQ).mpr
        ⟨⟨_, hp⟩, (mem_ffP0_iff hQ fr).mpr ⟨σ, hσ, J, hJ, rfl⟩, rfl⟩
    · rw [ffOmegaToSim_apply, coe_omegaToProj]
      rfl

theorem mem_ffBS_iff (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) 1) {x : ProjSim Q} :
    x ∈ ffBS hQ fr ↔ ∃ J : Finset (Fin 6), Even J.card ∧ x = ffM fr 1 J := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    change w ∈ ffStar hQ (ffB0 fr) at hw
    rw [mem_ffStar_iff] at hw
    obtain ⟨g, hg, rfl⟩ := hw
    obtain ⟨J, hJ, hge⟩ := (mem_ffB0_iff fr).mp hg
    have hgB : fr.signChange J ∈ ffB0 fr := hge ▸ hg
    have hω : fr.signChange J ∈ omegaGroup hQ := ffB0_le_omega hQ fr hgB
    have hg' : g = ⟨fr.signChange J, hω⟩ := Subtype.ext hge
    rw [hg']
    exact ⟨J, hJ, by rw [ffM_one_signChange, ffOmegaToSim_apply, coe_omegaToProj]; rfl⟩
  · rintro ⟨J, hJ, rfl⟩
    have hω : fr.signChange J ∈ omegaGroup hQ :=
      ffB0_le_omega hQ fr ⟨J, hJ, rfl⟩
    refine Subgroup.mem_map.mpr ⟨omegaToProj hQ ⟨_, hω⟩, ?_, ?_⟩
    · exact (mem_ffStar_iff hQ).mpr ⟨⟨_, hω⟩, ⟨J, hJ, rfl⟩, rfl⟩
    · rw [ffM_one_signChange, ffOmegaToSim_apply, coe_omegaToProj]
      rfl

theorem ffM_mem_ffPS_iff (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) 1)
    (σ : Equiv.Perm (Fin 6)) (J : Finset (Fin 6)) :
    ffM fr σ J ∈ ffPS hQ fr ↔ σ ∈ monoD ∧ Even J.card := by
  constructor
  · intro h
    obtain ⟨τ, hτ, K, hK, hEq⟩ := (mem_ffPS_iff hQ fr).mp h
    obtain ⟨rfl, hJK | hJK⟩ := (ffM_eq_iff fr).mp hEq
    · exact ⟨hτ, by rw [hJK]; exact hK⟩
    · exact ⟨hτ, by rw [hJK]; exact ffOutMono_even_compl hK⟩
  · rintro ⟨hσ, hJ⟩
    exact (mem_ffPS_iff hQ fr).mpr ⟨σ, hσ, J, hJ, rfl⟩

theorem ffM_mem_ffBS_iff (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) 1)
    (σ : Equiv.Perm (Fin 6)) (J : Finset (Fin 6)) :
    ffM fr σ J ∈ ffBS hQ fr ↔ σ = 1 ∧ Even J.card := by
  constructor
  · intro h
    obtain ⟨K, hK, hEq⟩ := (mem_ffBS_iff hQ fr).mp h
    obtain ⟨hσ, hJK | hJK⟩ := (ffM_eq_iff fr).mp hEq
    · exact ⟨hσ, by rw [hJK]; exact hK⟩
    · exact ⟨hσ, by rw [hJK]; exact ffOutMono_even_compl hK⟩
  · rintro ⟨rfl, hJ⟩
    exact (mem_ffBS_iff hQ fr).mpr ⟨J, hJ, rfl⟩

theorem ffBS_le_ffPS (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) 1) :
    ffBS hQ fr ≤ ffPS hQ fr :=
  Subgroup.map_mono (ffB1_le_ffP1 hQ fr)

private theorem ffOutMono_conj_mem_ffBS (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) 1)
    (σ : Equiv.Perm (Fin 6)) (K : Finset (Fin 6)) {g : ProjSim Q} (hg : g ∈ ffBS hQ fr) :
    ffM fr σ K * g * (ffM fr σ K)⁻¹ ∈ ffBS hQ fr := by
  obtain ⟨J, hJ, rfl⟩ := (mem_ffBS_iff hQ fr).mp hg
  rw [ffM_conj_signChange]
  exact (mem_ffBS_iff hQ fr).mpr
    ⟨J.map σ.toEmbedding, by rw [Finset.card_map]; exact hJ, rfl⟩

theorem ffM_mem_normalizer_ffBS (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) 1)
    (σ : Equiv.Perm (Fin 6)) (K : Finset (Fin 6)) :
    ffM fr σ K ∈ normalizer (ffBS hQ fr : Set (ProjSim Q)) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro g
  constructor
  · intro hg
    exact ffOutMono_conj_mem_ffBS hQ fr σ K hg
  · intro hg
    have h := ffOutMono_conj_mem_ffBS hQ fr σ⁻¹ (K.map σ.toEmbedding) hg
    rw [← ffM_inv] at h
    have h' : (ffM fr σ K)⁻¹ * (ffM fr σ K * g * (ffM fr σ K)⁻¹) *
        ((ffM fr σ K)⁻¹)⁻¹ = g := by group
    rwa [h'] at h

theorem ff_normalizer_ffBS_monomial (hQ : Q.Nondegenerate)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) (fr : NFrame Q (Fin 6) 1) {x : ProjSim Q}
    (hx : x ∈ normalizer (ffBS hQ fr : Set (ProjSim Q))) :
    ∃ (σ : Equiv.Perm (Fin 6)) (K : Finset (Fin 6)), x = ffM fr σ K := by
  have hmap : (ffB1 hQ fr).map (ffSimOmegaAct hQ h2 x).toMonoidHom = ffB1 hQ fr := by
    apply le_antisymm
    · intro z hz
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
      have hy : ffOmegaToSim hQ w ∈ ffBS hQ fr :=
        Subgroup.mem_map.mpr ⟨w, hw, rfl⟩
      have hconj : x * ffOmegaToSim hQ w * x⁻¹ ∈ ffBS hQ fr :=
        (Subgroup.mem_set_normalizer_iff.mp hx (ffOmegaToSim hQ w)).mp hy
      rw [← ffOutMono_omegaToSim_act hQ h2 x w] at hconj
      obtain ⟨v, hv, hve⟩ := Subgroup.mem_map.mp hconj
      have hv' : v = ffSimOmegaAct hQ h2 x w := ffOmegaToSim_injective hQ hve
      rwa [hv'] at hv
    · intro b hb
      have hy : ffOmegaToSim hQ b ∈ ffBS hQ fr :=
        Subgroup.mem_map.mpr ⟨b, hb, rfl⟩
      have hxinv : x⁻¹ ∈ normalizer (ffBS hQ fr : Set (ProjSim Q)) :=
        (normalizer (ffBS hQ fr : Set (ProjSim Q))).inv_mem hx
      have hconj : x⁻¹ * ffOmegaToSim hQ b * (x⁻¹)⁻¹ ∈ ffBS hQ fr :=
        (Subgroup.mem_set_normalizer_iff.mp hxinv (ffOmegaToSim hQ b)).mp hy
      rw [← ffOutMono_omegaToSim_act hQ h2 x⁻¹ b] at hconj
      obtain ⟨v, hv, hve⟩ := Subgroup.mem_map.mp hconj
      have hv' : v = ffSimOmegaAct hQ h2 x⁻¹ b := ffOmegaToSim_injective hQ hve
      have hb' : ffSimOmegaAct hQ h2 x⁻¹ b ∈ ffB1 hQ fr := by rwa [hv'] at hv
      refine Subgroup.mem_map.mpr ⟨ffSimOmegaAct hQ h2 x⁻¹ b, hb', ?_⟩
      show ffSimOmegaAct hQ h2 x (ffSimOmegaAct hQ h2 x⁻¹ b) = b
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  obtain ⟨σ, K, hx'⟩ := ff_star_normalizes hQ h2 fr hmap
  exact ⟨σ, K, hx'⟩

theorem ffM_simInOmegaStar_iff (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = -1) (fr : NFrame Q (Fin 6) 1)
    (σ : Equiv.Perm (Fin 6)) (K : Finset (Fin 6)) :
    SimInOmegaStar hQ (ffM fr σ K) ↔ Equiv.Perm.sign σ = 1 ∧ Even K.card := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨g, hgω, hgy⟩ := (mem_omegaProj_iff hQ).mp hy
    have hto : toProj Q g = toProj Q (fr.permOrth σ * fr.signChange K) := by
      apply projOrthToProjSim_injective
      rw [hgy, hxy]
      rfl
    have hker : g⁻¹ * (fr.permOrth σ * fr.signChange K) ∈ piGroup Q :=
      QuotientGroup.eq.mp hto
    have hp : fr.permOrth σ * fr.signChange K ∈ omegaGroup hQ := by
      rcases mem_piGroup_iff.mp hker with h1 | h2
      · rw [(inv_mul_eq_one.mp h1).symm]
        exact hgω
      · rw [inv_mul_eq_iff_eq_mul.mp h2]
        exact Subgroup.mul_mem _ hgω (ff6m_piOrth_mem_omega hQ hdim hsgn)
    have hmem := (ffMono_mem_omega_iff hQ fr σ K).mp hp
    rwa [Equiv.Perm.mem_alternatingGroup] at hmem
  · rintro ⟨hsign, hK⟩
    refine ⟨toProj Q (fr.permOrth σ * fr.signChange K), ?_, rfl⟩
    rw [mem_omegaProj_iff]
    exact ⟨_, (ffMono_mem_omega_iff hQ fr σ K).mpr
      ⟨Equiv.Perm.mem_alternatingGroup.mpr hsign, hK⟩, rfl⟩

theorem ff_omegaToSim_act (hQ : Q.Nondegenerate) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (x : ProjSim Q) (w : ↥(omegaProj hQ)) :
    ffOmegaToSim hQ (ffSimOmegaAct hQ h2 x w) = x * ffOmegaToSim hQ w * x⁻¹ :=
  ffOutMono_omegaToSim_act hQ h2 x w

end CFSG.OddStandard.SmallF3.Omega
