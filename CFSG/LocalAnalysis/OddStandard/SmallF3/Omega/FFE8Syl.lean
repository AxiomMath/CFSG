module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFE8Std
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PSMono
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFE8Def

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ffE8Syl_act_eq (hQ : Q.Nondegenerate) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (fr : PFrame Q (Option (Fin 5)) ffC) {x : ProjSim Q}
    (hx : x ∈ normalizer (ffP1Sim hQ fr : Set (ProjSim Q))) :
    (ffP1p hQ fr).map (ffSimOmegaAct hQ h2 x).toMonoidHom = ffP1p hQ fr := by
  have key : ∀ y ∈ normalizer (ffP1Sim hQ fr : Set (ProjSim Q)),
      (ffP1p hQ fr).map (ffSimOmegaAct hQ h2 y).toMonoidHom ≤ ffP1p hQ fr := by
    intro y hy w hw
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hw
    have h1 : ffOmegaToSim hQ (ffSimOmegaAct hQ h2 y p) ∈ ffP1Sim hQ fr := by
      rw [ff_omegaToSim_act]
      exact (mem_normalizer_iff.mp hy _).mp (Subgroup.mem_map_of_mem _ hp)
    obtain ⟨q, hq, hqe⟩ := Subgroup.mem_map.mp h1
    rw [ffOmegaToSim_injective hQ hqe] at hq
    exact hq
  refine le_antisymm (key x hx) fun w hw => ?_
  refine Subgroup.mem_map.mpr ⟨ffSimOmegaAct hQ h2 x⁻¹ w,
    key x⁻¹ (Subgroup.inv_mem _ hx) (Subgroup.mem_map_of_mem _ hw), ?_⟩
  change ffSimOmegaAct hQ h2 x (ffSimOmegaAct hQ h2 x⁻¹ w) = w
  rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

theorem ffE8Syl_normalizer_inf_le (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = 1)
    (fr : PFrame Q (Option (Fin 5)) ffC) :
    normalizer (ffP1Sim hQ fr : Set (ProjSim Q)) ⊓ ffOmegaSim hQ ≤ ffP1Sim hQ fr := by
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  haveI : Finite ↥(omegaProj hQ) := Nat.finite_of_card_ne_zero
    (by rw [ff_natCard_omegaProj_six_plus hQ hdim hsgn]; norm_num)
  have hp : IsPGroup 2 (normalizer (ffP1Sim hQ fr : Set (ProjSim Q))) :=
    ff6p_normalizer_isPGroup hQ hdim hsgn h2 fr _ fun x hx => ffE8Syl_act_eq hQ h2 fr hx
  have hT := hp.comap_of_injective (ffOmegaToSim hQ) (ffOmegaToSim_injective hQ)
  have hle : ffP1p hQ fr ≤
      (normalizer (ffP1Sim hQ fr : Set (ProjSim Q))).comap (ffOmegaToSim hQ) := fun p hp =>
    Subgroup.mem_comap.mpr (Subgroup.le_normalizer (Subgroup.mem_map_of_mem _ hp))
  have heq := IsSylow2Of.eq_of_le (ffP1p_sylow hQ hdim hsgn fr) le_top hT hle
  intro x hx
  obtain ⟨hxN, w, rfl⟩ := Subgroup.mem_inf.mp hx
  have hwT : w ∈ (normalizer (ffP1Sim hQ fr : Set (ProjSim Q))).comap (ffOmegaToSim hQ) := hxN
  rw [heq] at hwT
  exact Subgroup.mem_map_of_mem _ hwT

theorem ffE8Syl_card_P1Sim (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (fr : PFrame Q (Option (Fin 5)) ffC) :
    Nat.card ↥(ffP1Sim hQ fr) = 128 := by
  have hπ := ff_piOrth_not_mem_omegaGroup_six_plus hQ hdim hsgn
  rw [show ffP1Sim hQ fr = (ffP1p hQ fr).map (ffOmegaToSim hQ) from rfl,
    ← Nat.card_congr ((ffP1p hQ fr).equivMapOfInjective (ffOmegaToSim hQ)
      (ffOmegaToSim_injective hQ)).toEquiv, ffP1p_card hQ hπ fr]
  norm_num

theorem ffE8Syl_card_inf_le (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (fr : PFrame Q (Option (Fin 5)) ffC) {K : Subgroup (ProjSim Q)}
    (hK : ¬ ffP1Sim hQ fr ≤ K) : Nat.card ↥(ffP1Sim hQ fr ⊓ K) ≤ 64 := by
  have hc := ffE8Syl_card_P1Sim hQ hdim hsgn fr
  haveI : Finite ↥(ffP1Sim hQ fr) := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  have hne : Nat.card ↥(ffP1Sim hQ fr ⊓ K) ≠ 128 := fun h => hK (inf_eq_left.mp
    (Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hc, h])))
  have hdvd := Subgroup.card_dvd_of_le (inf_le_left : ffP1Sim hQ fr ⊓ K ≤ ffP1Sim hQ fr)
  rw [hc] at hdvd
  obtain ⟨e, he⟩ := hdvd
  have he2 : 2 ≤ e := by
    rcases Nat.lt_or_ge e 2 with h | h
    · interval_cases e <;> omega
    · exact h
  have h3 := Nat.mul_le_mul_left (Nat.card ↥(ffP1Sim hQ fr ⊓ K)) he2
  omega

theorem ffE8Syl_ts_comm (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (fr : PFrame Q (Option (Fin 5)) ffC) {x : ProjSim Q}
    (hx : x ∈ ffP1Sim hQ fr) : ffTs fr * x = x * ffTs fr := by
  obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hx
  exact ffTs_comm_normalizer hQ (by omega) (ff_piOrth_not_mem_omegaGroup_six_plus hQ hdim hsgn)
    fr (ffP1p_le_normalizer hQ (ff_piOrth_not_mem_omegaGroup_six_plus hQ hdim hsgn) fr hp)

theorem ffE8Syl_ts_mem_normalizer (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = 1)
    (fr : PFrame Q (Option (Fin 5)) ffC) :
    ffTs fr ∈ normalizer (ffP1Sim hQ fr : Set (ProjSim Q)) :=
  Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun h hh =>
    (ffE8Syl_ts_comm hQ hdim hsgn fr hh).symm)

theorem ffE8Syl_eq_normalizers (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (fr : PFrame Q (Option (Fin 5)) ffC) {Ē : Subgroup (ProjSim Q)}
    (hG : ∀ x ∈ normalizer (Ē : Set (ProjSim Q)), SimInGStar x)
    (hbad : ¬ ffP1Sim hQ fr ≤ normalizer (Ē : Set (ProjSim Q)))
    (hts : ffTs fr ∈ normalizer (Ē : Set (ProjSim Q))) {Y : Subgroup (ProjSim Q)}
    (hY : Nat.card Y = 128) (hYP : Y ≤ normalizer (ffP1Sim hQ fr : Set (ProjSim Q)))
    (hYE : Y ≤ normalizer (Ē : Set (ProjSim Q))) :
    Y = normalizer (ffP1Sim hQ fr : Set (ProjSim Q)) ⊓ normalizer (Ē : Set (ProjSim Q)) := by
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  haveI : Finite (ProjSim Q) :=
    Nat.finite_of_card_ne_zero (by rw [ff_natCard_projSim_six_plus hQ hdim hsgn]; norm_num)
  set N := normalizer (ffP1Sim hQ fr : Set (ProjSim Q)) ⊓ normalizer (Ē : Set (ProjSim Q))
  have hsub : ffOmegaSim hQ ⊓ N ≤ ffP1Sim hQ fr ⊓ normalizer (Ē : Set (ProjSim Q)) := by
    intro x hx
    obtain ⟨hxΩ, hxN⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨hxP, hxE⟩ := Subgroup.mem_inf.mp hxN
    exact ⟨ffE8Syl_normalizer_inf_le hQ hdim hsgn fr (Subgroup.mem_inf.mpr ⟨hxP, hxΩ⟩), hxE⟩
  have h64 : Nat.card ↥(ffOmegaSim hQ ⊓ N) ≤ 64 :=
    le_trans (Subgroup.card_le_of_le hsub) (ffE8Syl_card_inf_le hQ hdim hsgn fr hbad)
  have hrel : (ffOmegaSim hQ).relIndex N ∣ 2 := by
    rw [Subgroup.relIndex_dvd_two_iff']
    refine ⟨ffTs fr, ⟨ffE8Syl_ts_mem_normalizer hQ hdim hsgn fr, hts⟩, fun b hb => ?_⟩
    by_cases hbΩ : b ∈ ffOmegaSim hQ
    · exact Or.inr hbΩ
    · obtain ⟨p, hp, hbp⟩ := ff6p_outer_eq_ts_mul hQ hdim hsgn h2 fr (hG b hb.2)
        (ffE8Syl_act_eq hQ h2 fr hb.1) fun ⟨y, hy, hyb⟩ => hbΩ ⟨⟨y, hy⟩, hyb⟩
      refine Or.inl ?_
      rw [hbp, ← mul_assoc, ffTs_mul_self, one_mul]
      exact ⟨p, rfl⟩
  have hle : Nat.card N ≤ 128 := by
    rw [← Subgroup.relIndex_mul_card (H := ffOmegaSim hQ) (K := N)]
    calc _ ≤ 2 * 64 := Nat.mul_le_mul (Nat.le_of_dvd (by norm_num) hrel) h64
      _ = 128 := by norm_num
  exact Subgroup.eq_of_le_of_card_ge (le_inf hYP hYE) (by rw [hY]; exact hle)

theorem ffE8Syl_map_eq_of_normalE16 (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = 1)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) (fr : PFrame Q (Option (Fin 5)) ffC) {x : ProjSim Q}
    (hxG : SimInGStar x)
    (hxP : (ffP1p hQ fr).map (ffSimOmegaAct hQ h2 x).toMonoidHom = ffP1p hQ fr)
    {U : Subgroup ↥(omegaProj hQ)} (hU : IsNormalE16In (ffP1p hQ fr) U) :
    U.map (ffSimOmegaAct hQ h2 x).toMonoidHom = U := by
  have hπ := ff_piOrth_not_mem_omegaGroup_six_plus hQ hdim hsgn
  have hB := ff6p_inG_normalizes_B1p hQ hdim hsgn h2 fr hxG hxP
  by_cases hUB : U = ffB1p hQ fr
  · rw [hUB]
    exact hB
  · refine ffP1p_E16_unique hQ hπ fr (ff6p_map_normalE16 hQ h2 fr hxP hU) hU
      (fun hWB => hUB ?_) hUB
    exact Subgroup.map_injective (f := (ffSimOmegaAct hQ h2 x).toMonoidHom)
      (ffSimOmegaAct hQ h2 x).injective (hWB.trans hB.symm)

end CFSG.OddStandard.SmallF3.Omega
