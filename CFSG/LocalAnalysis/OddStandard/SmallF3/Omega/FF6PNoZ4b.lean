module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PNoZ4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PSTypes
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84HP2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private noncomputable def ffOutFF6PNoZ4b_b04 (hQ : Q.Nondegenerate)
    (fr : PFrame Q (Option (Fin 5)) ffC) : ↥(omegaProj hQ) :=
  omegaToProj hQ ⟨fr.signChange (ffOpt ({0,4} : Finset (Fin 5))),
    ffB0p_le_omega hQ fr ((mem_ffB0p_iff_ffOpt fr).mpr
      ⟨({0,4} : Finset (Fin 5)), by decide, rfl⟩)⟩

private theorem ffOutFF6PNoZ4b_b04_val (hQ : Q.Nondegenerate)
    (fr : PFrame Q (Option (Fin 5)) ffC) :
    (ffOutFF6PNoZ4b_b04 hQ fr : ProjOrth Q) =
      toProj Q (fr.signChange (ffOpt ({0,4} : Finset (Fin 5)))) :=
  coe_omegaToProj hQ _

private theorem ffOutFF6PNoZ4b_b04_type (hQ : Q.Nondegenerate)
    (fr : PFrame Q (Option (Fin 5)) ffC) :
    SimHasType (ffOmegaToSim hQ (ffOutFF6PNoZ4b_b04 hQ fr)) 2 (-1) := by
  have hne0 : ffOpt ({0,4} : Finset (Fin 5)) ≠ ∅ := by decide
  have hneu : ffOpt ({0,4} : Finset (Fin 5)) ≠ Finset.univ := by decide
  have hcard : (ffOpt ({0,4} : Finset (Fin 5))).card = 2 := by rw [ffOpt_card]; decide
  have hif : (if none ∈ ffOpt ({0,4} : Finset (Fin 5)) then (-1 : ℤˣ) else 1) = 1 :=
    if_neg (none_notMem_ffOpt _)
  have h := ff6p_simHasType_signChange hQ fr (K := ffOpt ({0,4} : Finset (Fin 5))) hne0 hneu
  rw [hcard, hif] at h
  rw [show (-1 : ℤˣ) ^ (2 / 2) = -1 from by decide, one_mul] at h
  simpa [ffOmegaToSim_apply, ffOutFF6PNoZ4b_b04_val hQ fr] using h

private theorem ffOutFF6PNoZ4b_flip_apply (hQ : Q.Nondegenerate)
    (fr : PFrame Q (Option (Fin 5)) ffC) {z : ProjSim Q}
    (hflip : ∀ (J : Finset (Fin 5)) (b : ↥(omegaProj hQ)), Even J.card →
      (b : ProjOrth Q) = toProj Q (fr.signChange (ffOpt J)) →
      ((4 : Fin 5) ∉ J → z * ffOmegaToSim hQ b = ffOmegaToSim hQ b * z) ∧
        ((4 : Fin 5) ∈ J → ffOmegaToSim hQ b * z * (ffOmegaToSim hQ b)⁻¹ = z * z ^ 2)) :
    ffOmegaToSim hQ (ffOutFF6PNoZ4b_b04 hQ fr) * z *
        (ffOmegaToSim hQ (ffOutFF6PNoZ4b_b04 hQ fr))⁻¹ = z * z ^ 2 :=
  (hflip ({0,4} : Finset (Fin 5)) (ffOutFF6PNoZ4b_b04 hQ fr) (by decide)
    (ffOutFF6PNoZ4b_b04_val hQ fr)).2 (by decide)

private theorem ffOutFF6PNoZ4b_flip_conj (hQ : Q.Nondegenerate)
    (fr : PFrame Q (Option (Fin 5)) ffC) {z : ProjSim Q}
    (hh : ffOmegaToSim hQ (ffOutFF6PNoZ4b_b04 hQ fr) * z *
        (ffOmegaToSim hQ (ffOutFF6PNoZ4b_b04 hQ fr))⁻¹ = z * z ^ 2) :
    z⁻¹ * ffOmegaToSim hQ (ffOutFF6PNoZ4b_b04 hQ fr) * z =
      z ^ 2 * ffOmegaToSim hQ (ffOutFF6PNoZ4b_b04 hQ fr) := by
  calc z⁻¹ * ffOmegaToSim hQ (ffOutFF6PNoZ4b_b04 hQ fr) * z
      = z⁻¹ * (ffOmegaToSim hQ (ffOutFF6PNoZ4b_b04 hQ fr) * z *
          (ffOmegaToSim hQ (ffOutFF6PNoZ4b_b04 hQ fr))⁻¹) *
          ffOmegaToSim hQ (ffOutFF6PNoZ4b_b04 hQ fr) := by group
    _ = z⁻¹ * (z * z ^ 2) * ffOmegaToSim hQ (ffOutFF6PNoZ4b_b04 hQ fr) := by rw [hh]
    _ = z ^ 2 * ffOmegaToSim hQ (ffOutFF6PNoZ4b_b04 hQ fr) := by group

private theorem ffOutFF6PNoZ4b_act_mem (hQ : Q.Nondegenerate)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) (fr : PFrame Q (Option (Fin 5)) ffC)
    {z : ProjSim Q} (hv : z ^ 2 = ffOmegaToSim hQ (ffZ0s hQ fr))
    (hflip : ∀ (J : Finset (Fin 5)) (b : ↥(omegaProj hQ)), Even J.card →
      (b : ProjOrth Q) = toProj Q (fr.signChange (ffOpt J)) →
      ((4 : Fin 5) ∉ J → z * ffOmegaToSim hQ b = ffOmegaToSim hQ b * z) ∧
        ((4 : Fin 5) ∈ J → ffOmegaToSim hQ b * z * (ffOmegaToSim hQ b)⁻¹ = z * z ^ 2)) :
    ∀ b ∈ ffB1p hQ fr, ffSimOmegaAct hQ h2 z⁻¹ b ∈ ffB1p hQ fr := by
  intro b hb
  obtain ⟨J, hJe, hbJ⟩ := (mem_ffB1p_iff hQ fr).mp hb
  by_cases h4 : (4 : Fin 5) ∈ J
  · have hh := (hflip J b hJe hbJ).2 h4
    have hc : z⁻¹ * ffOmegaToSim hQ b * z = z ^ 2 * ffOmegaToSim hQ b := by
      calc z⁻¹ * ffOmegaToSim hQ b * z
          = z⁻¹ * (ffOmegaToSim hQ b * z * (ffOmegaToSim hQ b)⁻¹) *
              ffOmegaToSim hQ b := by group
        _ = z⁻¹ * (z * z ^ 2) * ffOmegaToSim hQ b := by rw [hh]
        _ = z ^ 2 * ffOmegaToSim hQ b := by group
    have hact : ffOmegaToSim hQ (ffSimOmegaAct hQ h2 z⁻¹ b) =
        ffOmegaToSim hQ (ffZ0s hQ fr * b) := by
      rw [ff_omegaToSim_act]
      simp only [inv_inv]
      rw [hc, hv, map_mul (ffOmegaToSim hQ)]
    rw [ffOmegaToSim_injective hQ hact]
    exact Subgroup.mul_mem _ (ffZ0s_mem_ffB1p hQ fr) hb
  · have hh := (hflip J b hJe hbJ).1 h4
    have hc : z⁻¹ * ffOmegaToSim hQ b * z = ffOmegaToSim hQ b := by
      calc z⁻¹ * ffOmegaToSim hQ b * z
          = z⁻¹ * (ffOmegaToSim hQ b * z) := by group
        _ = z⁻¹ * (z * ffOmegaToSim hQ b) := by rw [← hh]
        _ = ffOmegaToSim hQ b := by group
    have hact : ffOmegaToSim hQ (ffSimOmegaAct hQ h2 z⁻¹ b) = ffOmegaToSim hQ b := by
      rw [ff_omegaToSim_act]
      simp only [inv_inv]
      rw [hc]
    rw [ffOmegaToSim_injective hQ hact]
    exact hb

theorem ff6p_cent_B1p_sq (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (fr : PFrame Q (Option (Fin 5)) ffC) {z : ProjSim Q}
    (hz : ∀ b ∈ ffB1p hQ fr, z * ffOmegaToSim hQ b = ffOmegaToSim hQ b * z) : z * z = 1 := by
  have hπ := ff_piOrth_not_mem_omegaGroup_six_plus hQ hdim hsgn
  have hsq := (ffB1p_elemAb2 hQ hπ fr).1.2
  rcases ff6p_cent_sim_cases hQ h2 fr hz with ⟨b, hb, hzb⟩ | ⟨b, hb, hzb⟩
  · have hbb : b * b = 1 := by rw [← pow_two]; exact hsq b hb
    rw [hzb, ← map_mul (ffOmegaToSim hQ), hbb, map_one]
  · have hbb : b * b = 1 := by rw [← pow_two]; exact hsq b hb
    have hιb : ffOmegaToSim hQ b * ffOmegaToSim hQ b = 1 := by
      rw [← map_mul (ffOmegaToSim hQ), hbb, map_one]
    have hcomm : ffOmegaToSim hQ b * ffTs fr = ffTs fr * ffOmegaToSim hQ b :=
      (ffTs_comm_normalizer hQ h2 hπ fr (Subgroup.le_normalizer hb)).symm
    rw [hzb]
    calc (ffTs fr * ffOmegaToSim hQ b) * (ffTs fr * ffOmegaToSim hQ b)
        = ffTs fr * (ffOmegaToSim hQ b * ffTs fr) * ffOmegaToSim hQ b := by group
      _ = ffTs fr * (ffTs fr * ffOmegaToSim hQ b) * ffOmegaToSim hQ b := by rw [hcomm]
      _ = (ffTs fr * ffTs fr) * (ffOmegaToSim hQ b * ffOmegaToSim hQ b) := by group
      _ = 1 := by rw [ffTs_mul_self, hιb, mul_one]

theorem ff6p_z4_flip_z0 (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (fr : PFrame Q (Option (Fin 5)) ffC) {z : ProjSim Q} (hz4 : z ^ 4 = 1)
    (hv : z ^ 2 = ffOmegaToSim hQ (ffZ0s hQ fr))
    (hflip : ∀ (J : Finset (Fin 5)) (b : ↥(omegaProj hQ)), Even J.card →
      (b : ProjOrth Q) = toProj Q (fr.signChange (ffOpt J)) →
      ((4 : Fin 5) ∉ J → z * ffOmegaToSim hQ b = ffOmegaToSim hQ b * z) ∧
        ((4 : Fin 5) ∈ J → ffOmegaToSim hQ b * z * (ffOmegaToSim hQ b)⁻¹ = z * z ^ 2)) :
    False := by
  have hconj : z⁻¹ * ffOmegaToSim hQ (ffOutFF6PNoZ4b_b04 hQ fr) * z =
      z ^ 2 * ffOmegaToSim hQ (ffOutFF6PNoZ4b_b04 hQ fr) :=
    ffOutFF6PNoZ4b_flip_conj hQ fr (ffOutFF6PNoZ4b_flip_apply hQ fr hflip)
  have hmem := ffOutFF6PNoZ4b_act_mem hQ h2 fr hv hflip
  have hmaple : (ffB1p hQ fr).map (ffSimOmegaAct hQ h2 z⁻¹).toMonoidHom ≤ ffB1p hQ fr := by
    intro b hb
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hb
    exact hmem c hc
  have hcard := Subgroup.card_map_of_injective (K := ffB1p hQ fr)
    (f := (ffSimOmegaAct hQ h2 z⁻¹).toMonoidHom) (ffSimOmegaAct hQ h2 z⁻¹).injective
  have heq : (ffB1p hQ fr).map (ffSimOmegaAct hQ h2 z⁻¹).toMonoidHom = ffB1p hQ fr :=
    Subgroup.eq_of_le_of_card_ge hmaple (by rw [hcard])
  obtain ⟨σ, K, hzmono⟩ := ff6p_star_normalizes hQ h2 fr heq
  have hb04ι : ffOmegaToSim hQ (ffOutFF6PNoZ4b_b04 hQ fr) =
      projOrthToProjSim Q (toProj Q (fr.signChange (ffOpt ({0,4} : Finset (Fin 5))))) := by
    rw [ffOmegaToSim_apply, ffOutFF6PNoZ4b_b04_val]
  have hzA : z = (projOrthToProjSim Q (toProj Q (fr.pOrth σ * fr.signChange K)))⁻¹ := by
    rw [← hzmono, inv_inv]
  have hL : z⁻¹ * ffOmegaToSim hQ (ffOutFF6PNoZ4b_b04 hQ fr) * z =
      projOrthToProjSim Q
        (toProj Q (fr.signChange (ffOpt (ffAct σ ({0,4} : Finset (Fin 5)))))) := by
    calc z⁻¹ * ffOmegaToSim hQ (ffOutFF6PNoZ4b_b04 hQ fr) * z
        = projOrthToProjSim Q (toProj Q (fr.pOrth σ * fr.signChange K)) *
            projOrthToProjSim Q (toProj Q (fr.signChange (ffOpt ({0,4} : Finset (Fin 5))))) *
            (projOrthToProjSim Q (toProj Q (fr.pOrth σ * fr.signChange K)))⁻¹ := by
            rw [hzmono, hzA, hb04ι]
      _ = projOrthToProjSim Q (toProj Q ((fr.pOrth σ * fr.signChange K) *
            fr.signChange (ffOpt ({0,4} : Finset (Fin 5))) *
            (fr.pOrth σ * fr.signChange K)⁻¹)) :=
            ffOutFF6PSTypes_conj_map (f := (projOrthToProjSim Q).comp (toProj Q))
              (fr.pOrth σ * fr.signChange K) (fr.signChange (ffOpt ({0,4} : Finset (Fin 5))))
      _ = projOrthToProjSim Q
            (toProj Q (fr.signChange (ffOpt (ffAct σ ({0,4} : Finset (Fin 5)))))) := by
            rw [ffMonoP_conj_signChange fr σ K (ffOpt ({0,4} : Finset (Fin 5))),
              ffOpt_map_optionCongr]
  have hveq : z ^ 2 * ffOmegaToSim hQ (ffOutFF6PNoZ4b_b04 hQ fr) =
      projOrthToProjSim Q
        (toProj Q (fr.signChange (ffOpt ({1,2,3,4} : Finset (Fin 5))))) := by
    have hz0ι : z ^ 2 = projOrthToProjSim Q
        (toProj Q (fr.signChange (ffOpt ({0,1,2,3} : Finset (Fin 5))))) := by
      rw [hv, ffOutFF6PSTypes_ffOmegaToSim_ffZ0s]
    rw [hz0ι, hb04ι, ← map_mul (projOrthToProjSim Q), ← map_mul (toProj Q),
      fr.signChange_mul, ← ffOpt_symmDiff]
    rw [show symmDiff ({0,1,2,3} : Finset (Fin 5)) ({0,4} : Finset (Fin 5)) =
        ({1,2,3,4} : Finset (Fin 5)) by decide]
  have heq2 : projOrthToProjSim Q
        (toProj Q (fr.signChange (ffOpt (ffAct σ ({0,4} : Finset (Fin 5)))))) =
      projOrthToProjSim Q
        (toProj Q (fr.signChange (ffOpt ({1,2,3,4} : Finset (Fin 5))))) :=
    hL.symm.trans (hconj.trans hveq)
  have htoProj : toProj Q (fr.signChange (ffOpt (ffAct σ ({0,4} : Finset (Fin 5))))) =
      toProj Q (fr.signChange (ffOpt ({1,2,3,4} : Finset (Fin 5)))) :=
    projOrthToProjSim_injective heq2
  rcases (ff6p_toProj_signChange_eq_iff fr (ffOpt (ffAct σ ({0,4} : Finset (Fin 5))))
    (ffOpt ({1,2,3,4} : Finset (Fin 5)))).mp htoProj with h | h
  · have hc := congrArg Finset.card h
    simp only [ffOpt_card, ffAct_card] at hc
    have h2' : ({0,4} : Finset (Fin 5)).card = 2 := by decide
    have h4' : ({1,2,3,4} : Finset (Fin 5)).card = 4 := by decide
    omega
  · have hmem' : none ∈ ffOpt (ffAct σ ({0,4} : Finset (Fin 5))) := by
      rw [h, Finset.mem_compl]
      exact none_notMem_ffOpt _
    exact (none_notMem_ffOpt _) hmem'

theorem ff6p_z4_flip_ts (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (fr : PFrame Q (Option (Fin 5)) ffC) {z : ProjSim Q} (hz4 : z ^ 4 = 1)
    (hv : z ^ 2 = ffTs fr ∨ z ^ 2 = ffTs fr * ffOmegaToSim hQ (ffZ0s hQ fr))
    (hflip : ∀ (J : Finset (Fin 5)) (b : ↥(omegaProj hQ)), Even J.card →
      (b : ProjOrth Q) = toProj Q (fr.signChange (ffOpt J)) →
      ((4 : Fin 5) ∉ J → z * ffOmegaToSim hQ b = ffOmegaToSim hQ b * z) ∧
        ((4 : Fin 5) ∈ J → ffOmegaToSim hQ b * z * (ffOmegaToSim hQ b)⁻¹ = z * z ^ 2)) :
    False := by
  have hconj : z⁻¹ * ffOmegaToSim hQ (ffOutFF6PNoZ4b_b04 hQ fr) * z =
      z ^ 2 * ffOmegaToSim hQ (ffOutFF6PNoZ4b_b04 hQ fr) :=
    ffOutFF6PNoZ4b_flip_conj hQ fr (ffOutFF6PNoZ4b_flip_apply hQ fr hflip)
  have hconj' : z⁻¹ * ffOmegaToSim hQ (ffOutFF6PNoZ4b_b04 hQ fr) * (z⁻¹)⁻¹ =
      z ^ 2 * ffOmegaToSim hQ (ffOutFF6PNoZ4b_b04 hQ fr) := by
    simpa using hconj
  have hb04ι : ffOmegaToSim hQ (ffOutFF6PNoZ4b_b04 hQ fr) =
      projOrthToProjSim Q (toProj Q (fr.signChange (ffOpt ({0,4} : Finset (Fin 5))))) := by
    rw [ffOmegaToSim_apply, ffOutFF6PNoZ4b_b04_val]
  obtain ⟨α, hα⟩ := sec8t84h_simHasType_conj hQ (ffOutFF6PNoZ4b_b04_type hQ fr) z⁻¹
  rw [hconj'] at hα
  rcases hv with hv | hv
  · have hveq : z ^ 2 * ffOmegaToSim hQ (ffOutFF6PNoZ4b_b04 hQ fr) =
        projOrthToProjSim Q (toProj Q (fr.signChange
          ({none, some 0, some 4} : Finset (Option (Fin 5))))) := by
      rw [hv, ffTs, hb04ι, ← map_mul (projOrthToProjSim Q), ← map_mul (toProj Q),
        fr.signChange_mul]
      rw [show symmDiff ({none} : Finset (Option (Fin 5)))
          (ffOpt ({0,4} : Finset (Fin 5))) =
          ({none, some 0, some 4} : Finset (Option (Fin 5))) by decide]
    have hβ : ∃ β : ℤˣ,
        SimHasType (z ^ 2 * ffOmegaToSim hQ (ffOutFF6PNoZ4b_b04 hQ fr)) 3 β := by
      rw [hveq]
      have hcard : ({none, some 0, some 4} : Finset (Option (Fin 5))).card = 3 := by decide
      exact ⟨_, hcard ▸ ff6p_simHasType_signChange hQ fr
        (K := ({none, some 0, some 4} : Finset (Option (Fin 5)))) (by decide) (by decide)⟩
    obtain ⟨β, hβ⟩ := hβ
    rcases ff_simHasType_rank hQ hdim hα hβ with h | h <;> omega
  · have hveq : z ^ 2 * ffOmegaToSim hQ (ffOutFF6PNoZ4b_b04 hQ fr) =
        projOrthToProjSim Q
          (toProj Q (fr.signChange ({some 0} : Finset (Option (Fin 5))))) := by
      rw [hv, ffOutFF6PSTypes_tsz0_eq, hb04ι, ← map_mul (projOrthToProjSim Q),
        ← map_mul (toProj Q), fr.signChange_mul]
      rw [show symmDiff ({some 4} : Finset (Option (Fin 5)))
          (ffOpt ({0,4} : Finset (Fin 5))) =
          ({some 0} : Finset (Option (Fin 5))) by decide]
    have hβ : ∃ β : ℤˣ,
        SimHasType (z ^ 2 * ffOmegaToSim hQ (ffOutFF6PNoZ4b_b04 hQ fr)) 1 β := by
      rw [hveq]
      have hcard : ({some 0} : Finset (Option (Fin 5))).card = 1 := by decide
      exact ⟨_, hcard ▸ ff6p_simHasType_signChange hQ fr
        (K := ({some 0} : Finset (Option (Fin 5)))) (by decide) (by decide)⟩
    obtain ⟨β, hβ⟩ := hβ
    rcases ff_simHasType_rank hQ hdim hα hβ with h | h <;> omega

theorem ff6p_no_cyclic4 (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (fr : PFrame Q (Option (Fin 5)) ffC) {z : ProjSim Q} (hz4 : z ^ 4 = 1) (hz2 : z ^ 2 ≠ 1)
    (hnorm : ∀ p ∈ ffP1p hQ fr,
      ffOmegaToSim hQ p * z * (ffOmegaToSim hQ p)⁻¹ ∈ Subgroup.zpowers z) : False := by
  rcases ff6p_z4_flip hQ hdim hsgn fr hz4 hz2 hnorm with hcent | hflip
  · have hzz : z * z = 1 := ff6p_cent_B1p_sq hQ hdim hsgn h2 fr hcent
    exact hz2 (by rw [pow_two]; exact hzz)
  · rcases ff6p_z4_sq_cases hQ hdim hsgn h2 fr hz4 hz2 hnorm with hv | hv | hv
    · exact ff6p_z4_flip_z0 hQ hdim hsgn h2 fr hz4 hv hflip
    · exact ff6p_z4_flip_ts hQ hdim fr hz4 (Or.inl hv) hflip
    · exact ff6p_z4_flip_ts hQ hdim fr hz4 (Or.inr hv) hflip

end CFSG.OddStandard.SmallF3.Omega
