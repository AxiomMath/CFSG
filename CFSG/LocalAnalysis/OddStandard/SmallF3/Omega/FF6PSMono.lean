module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PSSyl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PSCent

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private instance ffOutFF6PSMono_decD8 : DecidablePred (· ∈ ffD8p) := fun σ =>
  decidable_of_iff' (σ * ffD8g = ffD8g * σ) (mem_ffD8p_iff σ)

private theorem ffOutFF6PSMono_pow4 : ∀ σ : Equiv.Perm (Fin 5), σ ∈ ffD8p → σ ^ 4 = 1 := by
  decide +kernel

private theorem ffOutFF6PSMono_rho_eq_of_toProj_eq (fr : PFrame Q (Option (Fin 5)) ffC)
    {a b : ↥(ffMonoP fr)}
    (h : toProj Q (a : OGroup Q) = toProj Q (b : OGroup Q)) :
    ffMonoPRho fr a = ffMonoPRho fr b := by
  have hker : (a : OGroup Q)⁻¹ * (b : OGroup Q) ∈ piGroup Q := QuotientGroup.eq.mp h
  let pim : ↥(ffMonoP fr) :=
    ⟨fr.signChange Finset.univ, by
      have hmem := mono_mem_ffMonoP fr 1 Finset.univ
      rwa [fr.pOrth_one, one_mul] at hmem⟩
  have hpi1 : ffMonoPRho fr pim = 1 := by
    rw [ffMonoPRho_eq_one_iff fr pim]
    exact ⟨Finset.univ, rfl⟩
  rcases mem_piGroup_iff.mp hker with h1 | h2
  · have hab : a = b := Subtype.ext (inv_mul_eq_one.mp h1)
    rw [hab]
  · have hb : b = a * pim := by
      apply Subtype.ext
      show (b : OGroup Q) = (a : OGroup Q) * fr.signChange Finset.univ
      rw [← fr.piOrth_eq_signChange_univ, ← h2]
      group
    rw [hb, map_mul, hpi1, mul_one]

private theorem ffOutFF6PSMono_hat_mem_ffP1p (hQ : Q.Nondegenerate)
    (fr : PFrame Q (Option (Fin 5)) ffC) {σ : Equiv.Perm (Fin 5)} (hσ : σ ∈ ffD8p) :
    omegaToProj hQ ⟨ffHat fr σ, ffHat_mem_omega hQ fr σ⟩ ∈ ffP1p hQ fr := by
  rw [mem_ffP1p_iff hQ fr]
  refine ⟨σ, hσ, ∅, by simp, ?_⟩
  simp only [coe_omegaToProj, ffOpt, Finset.map_empty, fr.signChange_empty, mul_one]

theorem ffD8p_self_normalizing {σ : Equiv.Perm (Fin 5)}
    (h : ∀ τ ∈ ffD8p, σ * τ * σ⁻¹ ∈ ffD8p) : σ ∈ ffD8p := by
  revert σ
  decide +kernel

theorem ff6p_normalizer_mono (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (fr : PFrame Q (Option (Fin 5)) ffC) {x : ProjSim Q}
    (hxP : (ffP1p hQ fr).map (ffSimOmegaAct hQ h2 x).toMonoidHom = ffP1p hQ fr)
    (hxB : (ffB1p hQ fr).map (ffSimOmegaAct hQ h2 x).toMonoidHom = ffB1p hQ fr) :
    ∃ (σ : Equiv.Perm (Fin 5)) (K : Finset (Option (Fin 5))), σ ∈ ffD8p ∧
      x = projOrthToProjSim Q (toProj Q (fr.pOrth σ * fr.signChange K)) := by
  obtain ⟨σ, K, hx⟩ := ff6p_star_normalizes hQ h2 fr hxB
  refine ⟨σ, K, ?_, hx⟩
  refine ffD8p_self_normalizing (fun τ hτ => ?_)
  let p : ↥(omegaProj hQ) := omegaToProj hQ ⟨ffHat fr τ, ffHat_mem_omega hQ fr τ⟩
  have hp : p ∈ ffP1p hQ fr := ffOutFF6PSMono_hat_mem_ffP1p hQ fr hτ
  have hxp' : (ffSimOmegaAct hQ h2 x).toMonoidHom p ∈
      (ffP1p hQ fr).map (ffSimOmegaAct hQ h2 x).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hp
  have hxp : (ffSimOmegaAct hQ h2 x).toMonoidHom p ∈ ffP1p hQ fr := by
    rwa [hxP] at hxp'
  obtain ⟨τ', hτ'D, J, hJe, hw⟩ := (mem_ffP1p_iff hQ fr).mp hxp
  let m0 : OGroup Q := fr.pOrth σ * fr.signChange K
  let m : OGroup Q := m0 * ffHat fr τ * m0⁻¹
  let m' : OGroup Q := ffHat fr τ' * fr.signChange (ffOpt J)
  have hm0 : m0 ∈ ffMonoP fr := mono_mem_ffMonoP fr σ K
  have hhatτ : ffHat fr τ ∈ ffMonoP fr := by
    rw [ffHat]
    exact mono_mem_ffMonoP fr τ _
  have hm : m ∈ ffMonoP fr := by
    dsimp only [m]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hm0 hhatτ) (Subgroup.inv_mem _ hm0)
  have hm' : m' ∈ ffMonoP fr := by
    dsimp only [m']
    rw [ffHat, mul_assoc, fr.signChange_mul]
    exact mono_mem_ffMonoP fr τ' _
  have hcoe : ((ffSimOmegaAct hQ h2 x p : omegaProj hQ) : ProjOrth Q) = toProj Q m := by
    rw [coe_ffSimOmegaAct]
    have hpcoe : (p : ProjOrth Q) = toProj Q (ffHat fr τ) := by rw [coe_omegaToProj]
    rw [hpcoe, hx, projSimAct_projOrthToProjSim]
    dsimp only [m, m0]
    simp only [← map_mul, ← map_inv]
  have hmm' : toProj Q m = toProj Q m' := hcoe.symm.trans hw
  let ga : ↥(ffMonoP fr) := ⟨m, hm⟩
  let gb : ↥(ffMonoP fr) := ⟨m', hm'⟩
  have hρeq : ffMonoPRho fr ga = ffMonoPRho fr gb :=
    ffOutFF6PSMono_rho_eq_of_toProj_eq fr hmm'
  have hρa : ffMonoPRho fr ga = σ * τ * σ⁻¹ := by
    have hga : ga = ⟨m0, hm0⟩ * ⟨ffHat fr τ, hhatτ⟩ * (⟨m0, hm0⟩ : ↥(ffMonoP fr))⁻¹ := by
      apply Subtype.ext
      rfl
    rw [hga, map_mul, map_mul, map_inv]
    have h1 : ffMonoPRho fr ⟨m0, hm0⟩ = σ := by
      dsimp only [m0]
      exact ffMonoPRho_apply fr σ K
    have h2 : ffMonoPRho fr ⟨ffHat fr τ, hhatτ⟩ = τ := by
      apply ffMonoPRho_eq_of_hat fr (K := ∅)
      show ffHat fr τ = ffHat fr τ * fr.signChange ∅
      rw [fr.signChange_empty, mul_one]
    rw [h1, h2]
  have hρb : ffMonoPRho fr gb = τ' := by
    apply ffMonoPRho_eq_of_hat fr (K := ffOpt J)
    rfl
  have hconj : σ * τ * σ⁻¹ = τ' := hρa.symm.trans (hρeq.trans hρb)
  rw [hconj]
  exact hτ'D

theorem ff6p_normalizer_pow8 (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (fr : PFrame Q (Option (Fin 5)) ffC) {x : ProjSim Q}
    (hxP : (ffP1p hQ fr).map (ffSimOmegaAct hQ h2 x).toMonoidHom = ffP1p hQ fr)
    (hxB : (ffB1p hQ fr).map (ffSimOmegaAct hQ h2 x).toMonoidHom = ffB1p hQ fr) :
    x ^ 8 = 1 := by
  obtain ⟨σ, K, hσD, hx⟩ := ff6p_normalizer_mono hQ hdim hsgn h2 fr hxP hxB
  let g : ↥(ffMonoP fr) := ⟨fr.pOrth σ * fr.signChange K, mono_mem_ffMonoP fr σ K⟩
  have hσ4 : σ ^ 4 = 1 := ffOutFF6PSMono_pow4 σ hσD
  have hρg : ffMonoPRho fr g = σ := ffMonoPRho_apply fr σ K
  have hρ4 : ffMonoPRho fr (g ^ 4) = 1 := by
    rw [map_pow, hρg, hσ4]
  obtain ⟨J, hJ⟩ := (ffMonoPRho_eq_one_iff fr (g ^ 4)).mp hρ4
  have hg8 : ((g ^ 8 : ↥(ffMonoP fr)) : OGroup Q) = 1 := by
    have hsplit : g ^ 8 = g ^ 4 * g ^ 4 := by
      rw [show (8 : ℕ) = 4 + 4 from rfl, pow_add]
    rw [hsplit, Subgroup.coe_mul, hJ, fr.signChange_mul_self]
  rw [hx, ← map_pow, ← map_pow (toProj Q) (g : OGroup Q) 8, ← Subgroup.coe_pow,
    hg8, map_one, map_one]

theorem ff6p_normalizer_pow16 (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (fr : PFrame Q (Option (Fin 5)) ffC) {x : ProjSim Q}
    (hx : (ffP1p hQ fr).map (ffSimOmegaAct hQ h2 x).toMonoidHom = ffP1p hQ fr) :
    x ^ 16 = 1 := by
  by_cases hB : (ffB1p hQ fr).map (ffSimOmegaAct hQ h2 x).toMonoidHom = ffB1p hQ fr
  · have h8 := ff6p_normalizer_pow8 hQ hdim hsgn h2 fr hx hB
    rw [show (16 : ℕ) = 8 * 2 from rfl, pow_mul, h8, one_pow]
  · have hxG : ¬ SimInGStar x := fun hxG =>
      hB (ff6p_inG_normalizes_B1p hQ hdim hsgn h2 fr hxG hx)
    have hswap := ff6p_outer_swap hQ hdim hsgn h2 fr hxG hx
    have hPP : (ffP1p hQ fr).map (ffSimOmegaAct hQ h2 (x * x)).toMonoidHom =
        ffP1p hQ fr := by
      have hcomp : ffSimOmegaAct hQ h2 (x * x) =
          ffSimOmegaAct hQ h2 x * ffSimOmegaAct hQ h2 x := map_mul _ _ _
      rw [hcomp]
      have hval : ((ffSimOmegaAct hQ h2 x * ffSimOmegaAct hQ h2 x).toMonoidHom) =
          (ffSimOmegaAct hQ h2 x).toMonoidHom.comp
            (ffSimOmegaAct hQ h2 x).toMonoidHom := rfl
      rw [hval, ← Subgroup.map_map, hx, hx]
    have hBB : (ffB1p hQ fr).map (ffSimOmegaAct hQ h2 (x * x)).toMonoidHom =
        ffB1p hQ fr := by
      have hcomp : ffSimOmegaAct hQ h2 (x * x) =
          ffSimOmegaAct hQ h2 x * ffSimOmegaAct hQ h2 x := map_mul _ _ _
      rw [hcomp]
      have hval : ((ffSimOmegaAct hQ h2 x * ffSimOmegaAct hQ h2 x).toMonoidHom) =
          (ffSimOmegaAct hQ h2 x).toMonoidHom.comp
            (ffSimOmegaAct hQ h2 x).toMonoidHom := rfl
      rw [hval, ← Subgroup.map_map]
      exact hswap
    have h8 := ff6p_normalizer_pow8 hQ hdim hsgn h2 fr hPP hBB
    have h16 : (x * x) ^ 8 = x ^ 16 := by
      rw [← pow_two, ← pow_mul]
    rw [← h16]
    exact h8

theorem ff6p_normalizer_isPGroup (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (fr : PFrame Q (Option (Fin 5)) ffC) (T : Subgroup (ProjSim Q))
    (hT : ∀ x ∈ T,
      (ffP1p hQ fr).map (ffSimOmegaAct hQ h2 x).toMonoidHom = ffP1p hQ fr) :
    IsPGroup 2 T := by
  intro g
  refine ⟨4, ?_⟩
  apply Subtype.ext
  change (g : ProjSim Q) ^ (2 ^ 4) = 1
  rw [show 2 ^ 4 = 16 by norm_num]
  exact ff6p_normalizer_pow16 hQ hdim hsgn h2 fr (hT g g.2)

theorem ff6p_outer_eq_ts_mul (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (fr : PFrame Q (Option (Fin 5)) ffC) {x : ProjSim Q} (hxG : SimInGStar x)
    (hxP : (ffP1p hQ fr).map (ffSimOmegaAct hQ h2 x).toMonoidHom = ffP1p hQ fr)
    (hxΩ : ¬ SimInOmegaStar hQ x) :
    ∃ p ∈ ffP1p hQ fr, x = ffTs fr * ffOmegaToSim hQ p := by
  have hπ := ff_piOrth_not_mem_omegaGroup_six_plus hQ hdim hsgn
  have hxB := ff6p_inG_normalizes_B1p hQ hdim hsgn h2 fr hxG hxP
  obtain ⟨σ, K, hσD, hxe⟩ := ff6p_normalizer_mono hQ hdim hsgn h2 fr hxP hxB
  let ε : Finset (Option (Fin 5)) := if Equiv.Perm.sign σ = 1 then ∅ else {none}
  let K' : Finset (Option (Fin 5)) := symmDiff ε K
  have hsplit : fr.pOrth σ * fr.signChange K = ffHat fr σ * fr.signChange K' := by
    rw [ffHat, mul_assoc, fr.signChange_mul]
    rw [show symmDiff ε K' = K by
      dsimp only [K']
      exact symmDiff_symmDiff_cancel_left ε K]
  let p₀ : ↥(omegaProj hQ) := omegaToProj hQ ⟨ffHat fr σ, ffHat_mem_omega hQ fr σ⟩
  have hp₀ : p₀ ∈ ffP1p hQ fr := ffOutFF6PSMono_hat_mem_ffP1p hQ fr hσD
  let z : ProjSim Q := projOrthToProjSim Q (toProj Q (fr.signChange K'))
  have hx_eq : x = ffOmegaToSim hQ p₀ * z := by
    rw [hxe, hsplit]
    dsimp only [p₀, z]
    simp only [ffOmegaToSim_apply, coe_omegaToProj, ← map_mul]
  have hz : ∀ b ∈ ffB1p hQ fr, z * ffOmegaToSim hQ b = ffOmegaToSim hQ b * z := by
    intro b hb
    obtain ⟨J, hJe, hbJ⟩ := (mem_ffB1p_iff hQ fr).mp hb
    rw [ffOmegaToSim_apply, hbJ]
    dsimp only [z]
    simp only [← map_mul]
    rw [fr.signChange_comm K' (ffOpt J)]
  rcases ff6p_cent_sim_cases hQ h2 fr hz with ⟨b, hb, hzb⟩ | ⟨b, hb, hzb⟩
  · exfalso
    apply hxΩ
    refine ⟨↑(p₀ * b), (p₀ * b).2, ?_⟩
    have hco : projOrthToProjSim Q (↑(p₀ * b)) =
        ffOmegaToSim hQ p₀ * ffOmegaToSim hQ b := by
      rw [Subgroup.coe_mul, map_mul]
      rfl
    rw [hco, hx_eq, hzb]
  · refine ⟨p₀ * b, Subgroup.mul_mem _ hp₀ (ffB1p_le_ffP1p hQ fr hb), ?_⟩
    have hcomm := ffTs_comm_normalizer hQ h2 hπ fr (ffP1p_le_normalizer hQ hπ fr hp₀)
    rw [hx_eq, hzb]
    calc ffOmegaToSim hQ p₀ * (ffTs fr * ffOmegaToSim hQ b)
        = (ffOmegaToSim hQ p₀ * ffTs fr) * ffOmegaToSim hQ b := by group
      _ = (ffTs fr * ffOmegaToSim hQ p₀) * ffOmegaToSim hQ b := by rw [hcomm]
      _ = ffTs fr * (ffOmegaToSim hQ p₀ * ffOmegaToSim hQ b) := by group
      _ = ffTs fr * ffOmegaToSim hQ (p₀ * b) := by rw [map_mul]

end CFSG.OddStandard.SmallF3.Omega
