module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14BlModelTorus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindOmegaMinusPiecesNormal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindOmegaMinusPiecesLevi
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSetup
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusIota

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open CFSG Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.UnitaryPilot (modelToG mem_modelToG modelToG_mono)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore centralizerPerfectCore_anti anisoNorm
  AnisoType anisoRotGL)
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_mono le_perfectCore_of_perfect
  perfectCore_perfect)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp)
open scoped commutatorElement

section Tail

variable {K : Type} [Field K] [Finite K] [CharP K 2] {r : ℕ}

theorem kOmM_perfectCore_le_suppGL_hyp_of_sep {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {Ts : Set (Fin r → Kˣ)} {t₀ : Fin r → Kˣ}
    (ht₀ : t₀ ∈ Ts)
    (hsep : ∀ a : Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2, a ∉ Set.range (kOmMPlaneEmb r) →
      kOmMWeight K r t₀ a ≠ 1) :
    perfectCore (StatedOmega (StatedQuadMinus (r + 1) K b c) ⊓
      centralizer (kOmMDiag K r '' Ts)) ≤ suppGL K (Set.range (kOmMEmb r)) := by
  set B := StatedOmega (StatedQuadMinus (r + 1) K b c) ⊓ centralizer (kOmMDiag K r '' Ts)
    with hBdef
  have hBC : ∀ x ∈ B, x ∈ centralizer (kOmMDiag K r '' Ts) := fun x hx => (mem_inf.1 hx).2
  have hw : ∀ (a : Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2), a ∉ Set.range (kOmMPlaneEmb r) →
      ∀ j : Fin 2, kOmMWeight K r t₀ (kOmMPlaneEmb r j) ≠ kOmMWeight K r t₀ a :=
    fun a ha j h => hsep a ha h.symm
  have hsep' : ∀ x ∈ B, ∀ (j : Fin 2) (a : Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2),
      a ∉ Set.range (kOmMPlaneEmb r) →
      (x : Matrix (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2)
        (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) K) (kOmMPlaneEmb r j) a = 0 ∧
      (x : Matrix (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2)
        (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) K) a (kOmMPlaneEmb r j) = 0 :=
    fun x hx j a ha => ⟨kOmM_mat_eq_zero_of_mem_centralizer (hBC x hx) ht₀ (hw a ha j),
      kOmM_mat_eq_zero_of_mem_centralizer (hBC x hx) ht₀ (hw a ha j).symm⟩
  set φ := F4Pilot.blockHom B kOmMPlaneEmb_injective
    (fun x hx i c hc => (hsep' x hx i c hc).1) with hφ
  have htype : ∀ x : B, ∃ n, AnisoType b c n ((φ x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    intro x
    have hiso : ∀ w, anisoNorm b c (((φ x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ w) =
        anisoNorm b c w := by
      intro w
      rw [hφ, F4Pilot.coe_blockHom, ← kOmM_statedQuadMinus_planeVec (r := r),
        ← kOmM_statedQuadMinus_planeVec (r := r),
        ← kOmM_mulVec_planeVec (fun a j ha => (hsep' x x.2 j a ha).2)]
      exact kOmM_isometry_of_mem (mem_inf.1 x.2).1 _
    rcases F4Pilot.isAnisoRot_or_isAnisoRef hirr hiso with h | h
    · exact ⟨0, Or.inl ⟨rfl, h⟩⟩
    · exact ⟨1, Or.inr ⟨rfl, h⟩⟩
  set D := (anisoRotGL b c).comap φ with hD
  have h2 : ⁅B, B⁆ ≤ D.map B.subtype := by
    rw [Subgroup.commutator_le]
    intro g hg h hh
    refine ⟨⁅(⟨g, hg⟩ : B), ⟨h, hh⟩⁆, ?_, rfl⟩
    change φ ⁅(⟨g, hg⟩ : B), ⟨h, hh⟩⁆ ∈ anisoRotGL b c
    rw [map_commutatorElement, F4Pilot.mem_anisoRotGL, commutatorElement_def, Units.val_mul,
      Units.val_mul, Units.val_mul]
    obtain ⟨m, hm⟩ := htype ⟨g, hg⟩
    obtain ⟨m', hm'⟩ := htype (⟨g, hg⟩ : B)⁻¹
    obtain ⟨n, hn⟩ := htype ⟨h, hh⟩
    obtain ⟨n', hn'⟩ := htype (⟨h, hh⟩ : B)⁻¹
    rw [map_inv] at hm' hn'
    exact F4Pilot.isAnisoRot_mul_mul_mul (F4Pilot.ne_zero_of_irr hirr) hm hm' hn hn'
      (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
      (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
  have hDker : ⁅D, D⁆ ≤ φ.ker := by
    have hle : (⁅D, D⁆).map φ ≤ ⊥ := by
      rw [Subgroup.map_commutator, ← F4Pilot.commutator_anisoRotGL (b := b) (c := c)]
      exact Subgroup.commutator_mono (Subgroup.map_comap_le _ _) (Subgroup.map_comap_le _ _)
    intro x hx
    exact (Subgroup.mem_bot.1 (hle ⟨x, hx, rfl⟩))
  have h3 : ⁅⁅B, B⁆, ⁅B, B⁆⁆ ≤ φ.ker.map B.subtype :=
    calc ⁅⁅B, B⁆, ⁅B, B⁆⁆ ≤ ⁅D.map B.subtype, D.map B.subtype⁆ := Subgroup.commutator_mono h2 h2
      _ = (⁅D, D⁆).map B.subtype := (Subgroup.map_commutator _ _ _).symm
      _ ≤ φ.ker.map B.subtype := Subgroup.map_mono hDker
  have h4 : φ.ker.map B.subtype ≤ suppGL K (Set.range (kOmMEmb r)) := by
    rintro _ ⟨y, hyker, rfl⟩
    have hy1 : ((y : GL (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) K) :
        Matrix (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2)
          (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) K).submatrix (kOmMPlaneEmb r)
            (kOmMPlaneEmb r) = 1 := by
      have := congrArg Units.val (MonoidHom.mem_ker.1 hyker)
      rwa [hφ, F4Pilot.coe_blockHom, Units.val_one] at this
    intro a a' haa
    by_cases ha : a ∈ Set.range (kOmMPlaneEmb r)
    · obtain ⟨i, rfl⟩ := ha
      by_cases ha' : a' ∈ Set.range (kOmMPlaneEmb r)
      · obtain ⟨j, rfl⟩ := ha'
        have h := congrFun (congrFun hy1 i) j
        rw [submatrix_apply] at h
        rw [B.coe_subtype, h, Matrix.one_apply, Matrix.one_apply]
        exact if_congr kOmMPlaneEmb_injective.eq_iff.symm rfl rfl
      · rw [B.coe_subtype, (hsep' _ y.2 i a' ha').1,
          Matrix.one_apply_ne (fun h => ha' ⟨i, h⟩)]
    · by_cases ha' : a' ∈ Set.range (kOmMPlaneEmb r)
      · obtain ⟨j, rfl⟩ := ha'
        rw [B.coe_subtype, (hsep' _ y.2 j a ha).2, Matrix.one_apply_ne (fun h => ha ⟨j, h.symm⟩)]
      · exact absurd ⟨kOmM_mem_range_emb_of_not_mem_plane ha,
          kOmM_mem_range_emb_of_not_mem_plane ha'⟩ haa
  have hpc : perfectCore B ≤ ⁅B, B⁆ :=
    calc perfectCore B = ⁅perfectCore B, perfectCore B⁆ := (perfectCore_perfect B).symm
      _ ≤ ⁅B, B⁆ := Subgroup.commutator_mono (perfectCore_le B) (perfectCore_le B)
  calc perfectCore B = ⁅perfectCore B, perfectCore B⁆ := (perfectCore_perfect B).symm
    _ ≤ ⁅⁅B, B⁆, ⁅B, B⁆⁆ := Subgroup.commutator_mono hpc hpc
    _ ≤ φ.ker.map B.subtype := h3
    _ ≤ suppGL K (Set.range (kOmMEmb r)) := h4

omit [Finite K] [CharP K 2] in
theorem kOmM_mulVec_vec_of_mem_suppGL {x : GL (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) K}
    (hx : x ∈ suppGL K (Set.range (kOmMEmb r))) :
    (x : Matrix (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2)
      (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) K) *ᵥ kOmMVec K r = kOmMVec K r := by
  have hu : (Sum.inr (Sum.inr 0) : Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) ∉
      Set.range (kOmMEmb r) := by
    rintro ⟨y, hy⟩
    exact kOmMEmb_ne_tail y 0 hy
  funext a
  have h1 := hx a (Sum.inr (Sum.inr 0)) (fun h => hu h.2)
  simp only [kOmMVec, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [h1, Matrix.one_apply]

end Tail

section Global


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem centralizerPerfectCore_spATorus_le_omegaMinus (hset : SeitzSetting G L) {r f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hr3 : 3 ≤ r) (e : L ≃* StatedSp (r + 1) K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (h : RootKindSp e t f (Fin.last r) .omegaMinus) {j : ℕ} (hjr : 2 * j ≤ r) :
    centralizerPerfectCore (modelToG e (spATorus K (r + 1) j)) ≤ centralizer ({t} : Set G) := by
  obtain ⟨b, c, hirr, Φ, σ, hN3, hN1⟩ := exists_kOmMParam hset hKc hf hr3 e htC ht (Fin.last r) h
  set T₀ := modelToG e (spATorus K (r + 1) j) with hT₀
  set H := centralizerPerfectCore T₀ with hHdef
  have hHE : H ≤ neighbourCore e (Fin.last r) :=
    centralizerPerfectCore_anti (modelToG_mono e (rootTorusSp_last_le_spATorus hjr))
  have hHperf : ⁅H, H⁆ = H := CFSG.Quasithin.perfectCore_perfect _
  have hHC : H ≤ centralizer (T₀ : Set G) := perfectCore_le _
  set H' : Subgroup (StatedOmega (StatedQuadMinus (r + 1) K b c)) :=
    (H.subgroupOf (neighbourCore e (Fin.last r))).map Φ.symm.toMonoidHom with hH'
  set P : Subgroup (GL (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) K) :=
    H'.map (StatedOmega (StatedQuadMinus (r + 1) K b c)).subtype with hP
  have hPperf : ⁅P, P⁆ = P := by
    rw [hP, ← Subgroup.map_commutator, hH', ← Subgroup.map_commutator,
      CFSG.SeitzReduction.commutator_subgroupOf_eq_self hHE hHperf]
  have hΦT : ∀ s ∈ spATorusParam K r j,
      ((Φ (kOmMIota hr3 hirr hKc hf (diagSp K r s)) : neighbourCore e (Fin.last r)) : G) ∈
        T₀ := by
    intro s hs
    rw [hN1, fieldSp_diagSp, coe_complSpEquiv_apply, spEmbed_last_diagSp]
    exact (mem_modelToG e).2 ⟨_, ⟨_, snoc_mem_spATorusParam hjr (map_mem_spATorusParam σ hs),
      rfl⟩, rfl⟩
  have hPB : P ≤ StatedOmega (StatedQuadMinus (r + 1) K b c) ⊓
      centralizer (kOmMDiag K r '' (spATorusParam K r j : Set (Fin r → Kˣ))) := by
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨(Φ.symm z).2, mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    have hzT := mem_centralizer_iff.1 (hHC hz) _ (hΦT s hs)
    set d := kOmMIota hr3 hirr hKc hf (diagSp K r s) with hd
    have hcomm : Φ.symm z * d = d * Φ.symm z := by
      apply Φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact Subtype.ext hzT.symm
    rw [← coe_kOmMIota_diagSp hr3 hirr hKc hf s, ← hd]
    exact (congrArg Subtype.val hcomm).symm
  have hK4 : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf
  obtain ⟨κ, hκ⟩ := exists_units_ne_one hK4
  have hsep : ∀ a : Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2,
      a ∉ Set.range (kOmMPlaneEmb r) → kOmMWeight K r (spASepParam j κ) a ≠ 1 := by
    intro a ha
    rcases a with i | i | i
    · rw [kOmMWeight_inl]
      exact fun h' => spASepParam_ne_one hκ i (Units.val_eq_one.1 h')
    · change (((spASepParam j κ i)⁻¹ : Kˣ) : K) ≠ 1
      exact fun h' => spASepParam_ne_one hκ i (inv_eq_one.1 (Units.val_eq_one.1 h'))
    · exact absurd ⟨i, rfl⟩ ha
  have hPsupp : P ≤ suppGL K (Set.range (kOmMEmb r)) :=
    (le_perfectCore_of_perfect hPB hPperf).trans
      (kOmM_perfectCore_le_suppGL_hyp_of_sep hirr (spASepParam_mem κ) hsep)
  intro x hx
  have hxE := hHE hx
  set g : StatedOmega (StatedQuadMinus (r + 1) K b c) := Φ.symm ⟨x, hxE⟩ with hg
  have hgP : (g : GL (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) K) ∈ P :=
    ⟨g, ⟨⟨x, hxE⟩, show x ∈ H from hx, rfl⟩, rfl⟩
  have hgv := kOmM_mulVec_vec_of_mem_suppGL (hPsupp hgP)
  have hgfix : g ∈ fixedSubgroup (kOmMBetaC K r b c) :=
    (mem_fixedSubgroup_kOmMBetaC_iff K hr3 hirr g).2 hgv
  have hβ : kOmMBetaC K r b c g = g := hgfix
  have h3 := hN3 g
  rw [hβ, hg, MulEquiv.apply_symm_apply] at h3
  rw [mem_centralizer_singleton_iff]
  calc x * t = t * x * t⁻¹ * t := by rw [h3]
    _ = t * x := by group

theorem spOmegaBTorusInput_omegaMinus : SpOmegaBTorusInput .omegaMinus := by
  intro G _ _ L hset n f K _ _ _ hn hKc hf e t ht hKt hroot _ j _ hjn
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 1 := ⟨n - 1, by omega⟩
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  exact centralizerPerfectCore_spATorus_le_omegaMinus hset hKc hf (by omega) e htC ht
    (hroot (Fin.last r)) (by omega)

end Global

end CFSG.SeitzReduction.SymplecticPilot
