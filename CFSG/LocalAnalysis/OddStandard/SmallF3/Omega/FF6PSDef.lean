module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PE16Cl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PSDefAux1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

@[expose] noncomputable def ffB1p (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC) :
    Subgroup ↥(omegaProj hQ) :=
  ffStar hQ (ffB0p fr)

@[expose] noncomputable def ffP1p (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC) :
    Subgroup ↥(omegaProj hQ) :=
  ffStar hQ (ffP0p hQ fr)

@[expose] noncomputable def ffZ0s (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC) :
    ↥(omegaProj hQ) :=
  omegaToProj hQ ⟨ffZ0p fr, ffB0p_le_omega hQ fr (ffZ0p_mem_ffB0p fr)⟩

theorem ffLift_ffStar_of_le (hQ : Q.Nondegenerate) (hπ : piOrth Q ∉ omegaGroup hQ)
    {S : Subgroup (OGroup Q)} (hS : S ≤ omegaGroup hQ) : ffLift hQ (ffStar hQ S) = S :=
  ffOutFF6PSDef_lift_ffStar_of_le hQ hπ hS

theorem ffLift_ffB1p (hQ : Q.Nondegenerate) (hπ : piOrth Q ∉ omegaGroup hQ)
    (fr : PFrame Q (Option (Fin 5)) ffC) : ffLift hQ (ffB1p hQ fr) = ffB0p fr := by
  rw [ffB1p]
  exact ffLift_ffStar_of_le hQ hπ (ffB0p_le_omega hQ fr)

theorem ffLift_ffP1p (hQ : Q.Nondegenerate) (hπ : piOrth Q ∉ omegaGroup hQ)
    (fr : PFrame Q (Option (Fin 5)) ffC) : ffLift hQ (ffP1p hQ fr) = ffP0p hQ fr := by
  rw [ffP1p]
  exact ffLift_ffStar_of_le hQ hπ (ffP0p_le_omega hQ fr)

theorem ffLift_card_of_not_mem (hQ : Q.Nondegenerate) (hπ : piOrth Q ∉ omegaGroup hQ)
    (U : Subgroup ↥(omegaProj hQ)) : Nat.card ↥(ffLift hQ U) = Nat.card ↥U :=
  ffOutFF6PSDef_lift_card hQ hπ U

theorem ffB1p_card (hQ : Q.Nondegenerate) (hπ : piOrth Q ∉ omegaGroup hQ)
    (fr : PFrame Q (Option (Fin 5)) ffC) : Nat.card ↥(ffB1p hQ fr) = 16 := by
  have h := ffLift_card_of_not_mem hQ hπ (ffB1p hQ fr)
  rw [ffLift_ffB1p hQ hπ fr, ffB0p_card] at h
  exact h.symm

theorem ffP1p_card (hQ : Q.Nondegenerate) (hπ : piOrth Q ∉ omegaGroup hQ)
    (fr : PFrame Q (Option (Fin 5)) ffC) : Nat.card ↥(ffP1p hQ fr) = 2 ^ 7 := by
  have h := ffLift_card_of_not_mem hQ hπ (ffP1p hQ fr)
  rw [ffLift_ffP1p hQ hπ fr, ffP0p_card] at h
  exact h.symm

theorem ffB1p_elemAb2 (hQ : Q.Nondegenerate) (hπ : piOrth Q ∉ omegaGroup hQ)
    (fr : PFrame Q (Option (Fin 5)) ffC) : IsElemAb2 (ffB1p hQ fr) 4 := by
  have hcomm : ∀ (a : ↥(omegaProj hQ)), a ∈ ffB1p hQ fr → ∀ (b : ↥(omegaProj hQ)),
      b ∈ ffB1p hQ fr → a * b = b * a := by
    intro a ha b hb
    rw [ffB1p] at ha hb
    rw [mem_ffStar_iff] at ha hb
    obtain ⟨g, hg, rfl⟩ := ha
    obtain ⟨g', hg', rfl⟩ := hb
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (ffB0p_comm fr hg hg')
  have hsq : ∀ x ∈ ffB1p hQ fr, x * x = 1 := by
    intro x hx
    rw [ffB1p] at hx
    rw [mem_ffStar_iff] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    rw [← map_mul]
    have h2 : g * g = 1 := Subtype.ext (ffB0p_mul_self fr hg)
    rw [h2, map_one]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact IsMulCommutative.of_comm fun a b => Subtype.ext (hcomm a a.2 b b.2)
  · intro x hx
    rw [pow_two]
    exact hsq x hx
  · rw [ffB1p_card hQ hπ fr]
    norm_num

theorem ffB1p_le_ffP1p (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC) :
    ffB1p hQ fr ≤ ffP1p hQ fr := by
  intro y hy
  rw [ffB1p] at hy
  rw [ffP1p]
  rw [mem_ffStar_iff] at hy ⊢
  obtain ⟨g, hg, hge⟩ := hy
  exact ⟨g, ffB0p_le_ffP0p hQ fr hg, hge⟩

theorem ffP1p_sylow (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (fr : PFrame Q (Option (Fin 5)) ffC) :
    IsSylow2Of (ffP1p hQ fr) (⊤ : Subgroup ↥(omegaProj hQ)) := by
  have hπ := ff_piOrth_not_mem_omegaGroup_six_plus hQ hdim hsgn
  refine ⟨le_top, IsPGroup.of_card (p := 2) (n := 7) (ffP1p_card hQ hπ fr), ?_⟩
  rw [Subgroup.relIndex_top_right]
  have h := Subgroup.card_mul_index (H := ffP1p hQ fr)
  rw [ffP1p_card hQ hπ fr, ff_natCard_omegaProj_six_plus hQ hdim hsgn] at h
  have hidx : (ffP1p hQ fr).index = 47385 := by omega
  rw [hidx]
  norm_num

theorem ffB1p_normalE16 (hQ : Q.Nondegenerate) (hπ : piOrth Q ∉ omegaGroup hQ)
    (fr : PFrame Q (Option (Fin 5)) ffC) : IsNormalE16In (ffP1p hQ fr) (ffB1p hQ fr) := by
  refine ⟨ffB1p_le_ffP1p hQ fr, ffB1p_elemAb2 hQ hπ fr, ?_⟩
  rw [Subgroup.normal_subgroupOf_iff (ffB1p_le_ffP1p hQ fr)]
  intro h k hh hk
  rw [ffB1p] at hh
  rw [mem_ffStar_iff] at hh
  obtain ⟨g', hg', hg'e⟩ := hh
  rw [ffP1p] at hk
  rw [mem_ffStar_iff] at hk
  obtain ⟨g, hg, hge⟩ := hk
  obtain ⟨K, hK, hg'K⟩ := (mem_ffB0p_iff_ffOpt fr).mp hg'
  obtain ⟨σ, hσ, J, hJ, hgJ⟩ := (mem_ffP0p_iff_hatOpt hQ fr).mp hg
  rw [ffB1p, mem_ffStar_iff]
  refine ⟨g * g' * g⁻¹, ?_, ?_⟩
  · rw [mem_ffB0p_iff_ffOpt]
    refine ⟨ffAct σ K, ?_, ?_⟩
    · rw [ffAct_card]; exact hK
    · show (g : OGroup Q) * (g' : OGroup Q) * (g : OGroup Q)⁻¹ =
        fr.signChange (ffOpt (ffAct σ K))
      rw [hgJ, hg'K]
      rw [show (ffHat fr σ * fr.signChange (ffOpt J)) * fr.signChange (ffOpt K) *
          (ffHat fr σ * fr.signChange (ffOpt J))⁻¹ =
          ffHat fr σ * (fr.signChange (ffOpt J) * fr.signChange (ffOpt K) *
            (fr.signChange (ffOpt J))⁻¹) * (ffHat fr σ)⁻¹ from by group]
      have hcommJK : fr.signChange (ffOpt J) * fr.signChange (ffOpt K) =
          fr.signChange (ffOpt K) * fr.signChange (ffOpt J) := fr.signChange_comm _ _
      have htconj : fr.signChange (ffOpt J) * fr.signChange (ffOpt K) *
          (fr.signChange (ffOpt J))⁻¹ = fr.signChange (ffOpt K) := by
        rw [hcommJK]
        group
      rw [htconj, ffHat_conj_signChange_ffOpt]
  · rw [map_mul, map_mul, map_inv, hge, hg'e]

theorem mem_ffB1p_iff (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC)
    {w : ↥(omegaProj hQ)} :
    w ∈ ffB1p hQ fr ↔ ∃ J : Finset (Fin 5), Even J.card ∧
      (w : ProjOrth Q) = toProj Q (fr.signChange (ffOpt J)) := by
  rw [ffB1p, mem_ffStar_iff]
  constructor
  · rintro ⟨g, hg, hgw⟩
    obtain ⟨J, hJ, hgJ⟩ := (mem_ffB0p_iff_ffOpt fr).mp hg
    refine ⟨J, hJ, ?_⟩
    have hw' : (w : ProjOrth Q) = toProj Q (g : OGroup Q) := by
      rw [← congrArg Subtype.val hgw, coe_omegaToProj]
    rw [hw', hgJ]
  · rintro ⟨J, hJ, hw⟩
    have hmem : fr.signChange (ffOpt J) ∈ ffB0p fr :=
      (mem_ffB0p_iff_ffOpt fr).mpr ⟨J, hJ, rfl⟩
    refine ⟨⟨fr.signChange (ffOpt J), ffB0p_le_omega hQ fr hmem⟩, hmem, ?_⟩
    apply Subtype.ext
    rw [coe_omegaToProj, hw]

theorem mem_ffP1p_iff (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC)
    {w : ↥(omegaProj hQ)} :
    w ∈ ffP1p hQ fr ↔ ∃ σ ∈ ffD8p, ∃ J : Finset (Fin 5), Even J.card ∧
      (w : ProjOrth Q) = toProj Q (ffHat fr σ * fr.signChange (ffOpt J)) := by
  rw [ffP1p, mem_ffStar_iff]
  constructor
  · rintro ⟨g, hg, hgw⟩
    obtain ⟨σ, hσ, J, hJ, hgσ⟩ := (mem_ffP0p_iff_hatOpt hQ fr).mp hg
    refine ⟨σ, hσ, J, hJ, ?_⟩
    have hw' : (w : ProjOrth Q) = toProj Q (g : OGroup Q) := by
      rw [← congrArg Subtype.val hgw, coe_omegaToProj]
    rw [hw', hgσ]
  · rintro ⟨σ, hσ, J, hJ, hw⟩
    have hmem : ffHat fr σ * fr.signChange (ffOpt J) ∈ ffP0p hQ fr :=
      (mem_ffP0p_iff_hatOpt hQ fr).mpr ⟨σ, hσ, J, hJ, rfl⟩
    refine ⟨⟨_, ffP0p_le_omega hQ fr hmem⟩, hmem, ?_⟩
    apply Subtype.ext
    rw [coe_omegaToProj, hw]

theorem ffLift_normalE16 (hQ : Q.Nondegenerate) (hπ : piOrth Q ∉ omegaGroup hQ)
    (fr : PFrame Q (Option (Fin 5)) ffC) {U : Subgroup ↥(omegaProj hQ)}
    (hU : IsNormalE16In (ffP1p hQ fr) U) : IsNormalE16In (ffP0p hQ fr) (ffLift hQ U) :=
  ffOutFF6PSDef_lift_normalE16 hQ hπ fr hU

theorem ffP1p_E16_unique (hQ : Q.Nondegenerate) (hπ : piOrth Q ∉ omegaGroup hQ)
    (fr : PFrame Q (Option (Fin 5)) ffC) {U W : Subgroup ↥(omegaProj hQ)}
    (hU : IsNormalE16In (ffP1p hQ fr) U) (hW : IsNormalE16In (ffP1p hQ fr) W)
    (hUne : U ≠ ffB1p hQ fr) (hWne : W ≠ ffB1p hQ fr) : U = W := by
  have hU0 := ffLift_normalE16 hQ hπ fr hU
  have hW0 := ffLift_normalE16 hQ hπ fr hW
  have hUne' : ffLift hQ U ≠ ffB0p fr := by
    intro h
    apply hUne
    rw [← ffStar_ffLift hQ U, h, ffB1p]
  have hWne' : ffLift hQ W ≠ ffB0p fr := by
    intro h
    apply hWne
    rw [← ffStar_ffLift hQ W, h, ffB1p]
  have heq : ffLift hQ U = ffLift hQ W := ff6p_E16_unique hQ fr hU0 hW0 hUne' hWne'
  calc U = ffStar hQ (ffLift hQ U) := (ffStar_ffLift hQ U).symm
    _ = ffStar hQ (ffLift hQ W) := by rw [heq]
    _ = W := ffStar_ffLift hQ W

theorem ffZ0s_mem_ffB1p (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC) :
    ffZ0s hQ fr ∈ ffB1p hQ fr := by
  rw [ffB1p, mem_ffStar_iff]
  exact ⟨⟨ffZ0p fr, ffB0p_le_omega hQ fr (ffZ0p_mem_ffB0p fr)⟩,
    ffZ0p_mem_ffB0p fr, rfl⟩

theorem ffZ0s_ne_one (hQ : Q.Nondegenerate) (hπ : piOrth Q ∉ omegaGroup hQ)
    (fr : PFrame Q (Option (Fin 5)) ffC) : ffZ0s hQ fr ≠ 1 := by
  intro h
  have h1 : (⟨ffZ0p fr, ffB0p_le_omega hQ fr (ffZ0p_mem_ffB0p fr)⟩ : omegaGroup hQ) = 1 := by
    apply omegaToProj_injective_of_not_mem hQ hπ
    rw [map_one]
    exact h
  exact ffZ0p_ne_one fr (congrArg Subtype.val h1)

theorem ffZ0s_mem_normalE16 (hQ : Q.Nondegenerate) (hπ : piOrth Q ∉ omegaGroup hQ)
    (fr : PFrame Q (Option (Fin 5)) ffC) {U : Subgroup ↥(omegaProj hQ)}
    (hU : IsNormalE16In (ffP1p hQ fr) U) : ffZ0s hQ fr ∈ U := by
  have hE16 := ffLift_normalE16 hQ hπ fr hU
  have hz : ffZ0p fr ∈ ffLift hQ U := ffZ0p_mem_E16 hQ fr hE16
  obtain ⟨hΩ, hUmem⟩ := (mem_ffLift_iff hQ).mp hz
  have heq : ffZ0s hQ fr = omegaToProj hQ ⟨ffZ0p fr, hΩ⟩ := by
    apply congrArg (omegaToProj hQ)
    exact Subtype.ext rfl
  rw [heq]
  exact hUmem

theorem ffZ0s_central (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC)
    {g : ↥(omegaProj hQ)} (hg : g ∈ ffP1p hQ fr) : g * ffZ0s hQ fr = ffZ0s hQ fr * g := by
  rw [ffP1p, mem_ffStar_iff] at hg
  obtain ⟨a, ha, hga⟩ := hg
  rw [← hga, ffZ0s]
  have hcomm : (a : OGroup Q) * ffZ0p fr = ffZ0p fr * (a : OGroup Q) :=
    ffZ0p_central hQ fr ha
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext hcomm

theorem ffP1p_center (hQ : Q.Nondegenerate) (hπ : piOrth Q ∉ omegaGroup hQ)
    (fr : PFrame Q (Option (Fin 5)) ffC) {g : ↥(omegaProj hQ)} (hg : g ∈ ffP1p hQ fr)
    (hc : ∀ h ∈ ffP1p hQ fr, h * g = g * h) : g = 1 ∨ g = ffZ0s hQ fr := by
  rw [ffP1p, mem_ffStar_iff] at hg
  obtain ⟨a, ha, hga⟩ := hg
  have hcomm : ∀ h ∈ ffP0p hQ fr, h * (a : OGroup Q) = (a : OGroup Q) * h := by
    intro h hh
    have hhΩ : h ∈ omegaGroup hQ := ffP0p_le_omega hQ fr hh
    have hhP : omegaToProj hQ ⟨h, hhΩ⟩ ∈ ffP1p hQ fr := by
      rw [ffP1p, mem_ffStar_iff]
      exact ⟨⟨h, hhΩ⟩, hh, rfl⟩
    have hc' := hc (omegaToProj hQ ⟨h, hhΩ⟩) hhP
    rw [← hga] at hc'
    have heq : (⟨h, hhΩ⟩ : omegaGroup hQ) * a = a * ⟨h, hhΩ⟩ := by
      apply omegaToProj_injective_of_not_mem hQ hπ
      change omegaToProj hQ ⟨h, hhΩ⟩ * omegaToProj hQ a =
        omegaToProj hQ a * omegaToProj hQ ⟨h, hhΩ⟩
      exact hc'
    exact congrArg Subtype.val heq
  rcases ff6p_center_P0 hQ fr ha hcomm with h1 | h1
  · left
    rw [← hga, show a = 1 from Subtype.ext h1, map_one]
  · right
    rw [← hga, ffZ0s]
    apply Subtype.ext
    rw [coe_omegaToProj, coe_omegaToProj]
    exact congrArg (toProj Q) h1

section Frame

variable {ι : Type} [Fintype ι] [DecidableEq ι] {c : ι → ZMod 3}

theorem PFrame.piOrth_eq_signChange_univ (fr : PFrame Q ι c) :
    piOrth Q = fr.signChange Finset.univ := by
  apply Subtype.ext
  apply fr.b.ext'
  intro i
  rw [coe_piOrth_apply, fr.signChange_basis Finset.univ i, if_pos (Finset.mem_univ i)]

theorem ff6p_toProj_signChange_compl (fr : PFrame Q ι c) (K : Finset ι) :
    toProj Q (fr.signChange Kᶜ) = toProj Q (fr.signChange K) := by
  rw [show Kᶜ = symmDiff Finset.univ K by ext i; simp [Finset.mem_symmDiff],
    ← fr.signChange_mul, ← fr.piOrth_eq_signChange_univ, map_mul, toProj_piOrth, one_mul]

theorem ff6p_toProj_signChange_eq_iff (fr : PFrame Q ι c) (J K : Finset ι) :
    toProj Q (fr.signChange J) = toProj Q (fr.signChange K) ↔ J = K ∨ J = Kᶜ := by
  constructor
  · intro h
    have h' : QuotientGroup.mk' (piGroup Q) (fr.signChange J) =
        QuotientGroup.mk' (piGroup Q) (fr.signChange K) := h
    rw [QuotientGroup.mk'_eq_mk'] at h'
    obtain ⟨z, hz, hzJ⟩ := h'
    rcases mem_piGroup_iff.mp hz with hz1 | hzπ
    · left
      apply fr.signChange_injective
      rw [← hzJ, hz1, mul_one]
    · right
      have hK : K = symmDiff J Finset.univ := by
        apply fr.signChange_injective
        rw [← hzJ, hzπ, fr.piOrth_eq_signChange_univ, fr.signChange_mul]
      have hK' : K = Jᶜ := by
        rw [hK]
        ext i
        simp [Finset.mem_symmDiff]
      rw [hK']
      simp
  · rintro (rfl | hJK)
    · rfl
    · rw [hJK]
      exact ff6p_toProj_signChange_compl fr K

end Frame

end CFSG.OddStandard.SmallF3.Omega
