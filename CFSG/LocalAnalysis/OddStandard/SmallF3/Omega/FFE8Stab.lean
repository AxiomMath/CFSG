module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFE8Cent
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFE8StabAux1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFE8StabAux2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PSTypes
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFE8Syl

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ffE8_model_stab (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (fr : PFrame Q (Option (Fin 5)) ffC)
    {Ē : Subgroup (ProjSim Q)} {z ν : ProjSim Q} (h : FFE8SData hQ Ē z ν)
    (hz : z = ffZ0Sim hQ fr)
    (hbad : ¬ ffP1Sim hQ fr ≤ normalizer (Ē : Set (ProjSim Q)))
    {Y : Subgroup (ProjSim Q)} (hY : Nat.card Y = 128)
    (hYP : Y ≤ normalizer (ffP1Sim hQ fr : Set (ProjSim Q)))
    (hYE : Y ≤ normalizer (Ē : Set (ProjSim Q))) :
    ∃ B : Subgroup (ProjSim Q), IsNormalE16In Y B ∧ ∃ y ∈ Y, y ∉ B ∧ ∀ b ∈ B, y * b = b * y := by
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  have hπ := ff_piOrth_not_mem_omegaGroup_six_plus hQ hdim hsgn
  obtain ⟨ε, hε, fr', hĒ, hzE⟩ := ffE8_frame_sim hQ hdim hsgn h
  have ht : fr'.signChange (ffE8Hat Finset.univ) = ffZ0p fr := by
    refine ffE8Stab_eq_of_ffSim_eq hQ hπ
      (ffE8Group_le_omegaGroup hQ hε fr' ⟨Finset.univ, by decide, rfl⟩)
      (ffB0p_le_omega hQ fr (ffZ0p_mem_ffB0p fr)) ?_
    rw [← hzE, hz]
    exact ffOutFF6PSTypes_ffOmegaToSim_ffZ0s hQ fr
  have hts : ffTs fr ∈ normalizer (Ē : Set (ProjSim Q)) := by
    rw [hĒ]
    exact ffE8Stab_ts_mem_normalizer fr' fr ht
  have hYN := ffE8Syl_eq_normalizers hQ hdim hsgn fr (ffE8_normalizer_mult hQ hdim hsgn h) hbad
    hts hY hYP hYE
  obtain ⟨γ, μ, hγ, hμ, hγP⟩ := ffE8Stab_exists_lift hQ hdim hsgn h2 fr hε
  have hB0 := ffE8Stab_conj_mem_normalizer hε fr' fr ht hγ hμ
    (ffE8Stab_simAct_z0 hQ hdim hsgn h2 fr hγP)
  set U : Subgroup ↥(omegaProj hQ) :=
    (ffB1p hQ fr).map (ffSimOmegaAct hQ h2 (QuotientGroup.mk γ)).toMonoidHom with hU
  have hUn : IsNormalE16In (ffP1p hQ fr) U :=
    ff6p_map_normalE16 hQ h2 fr hγP (ffB1p_normalE16 hQ hπ fr)
  have hUE : ∀ u ∈ U, ffOmegaToSim hQ u ∈ normalizer (Ē : Set (ProjSim Q)) := by
    intro u hu
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hu
    obtain ⟨g, hg, rfl⟩ := (mem_ffStar_iff hQ).mp hb
    change ffOmegaToSim hQ (ffSimOmegaAct hQ h2 (QuotientGroup.mk γ) (omegaToProj hQ g)) ∈ _
    rw [ff_omegaToSim_act,
      show ffOmegaToSim hQ (omegaToProj hQ g) = ffSim Q (g : OGroup Q) from rfl,
      ← ffE8Stab_ffSim_simAct, hĒ]
    exact Subgroup.le_normalizer_map (ffSim Q) (Subgroup.mem_map_of_mem _ (hB0 g hg))
  have hUP : ∀ u ∈ U, ffOmegaToSim hQ u ∈ normalizer (ffP1Sim hQ fr : Set (ProjSim Q)) :=
    fun u hu => Subgroup.le_normalizer (Subgroup.mem_map_of_mem _ (hUn.1 hu))
  have hBY : U.map (ffOmegaToSim hQ) ≤ Y := by
    rw [hYN]
    rintro x hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    exact ⟨hUP u hu, hUE u hu⟩
  refine ⟨U.map (ffOmegaToSim hQ), ⟨hBY, ffE8Stab_isElemAb2_map (ffOmegaToSim hQ)
    (ffOmegaToSim_injective hQ) hUn.2.1, ?_⟩, ffTs fr, ?_, ?_, ?_⟩
  · rw [Subgroup.normal_subgroupOf_iff hBY]
    intro b k hb hk
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hb
    have hk' : k ∈ normalizer (ffP1Sim hQ fr : Set (ProjSim Q)) ⊓
        normalizer (Ē : Set (ProjSim Q)) := by rw [← hYN]; exact hk
    have hmap := ffE8Syl_map_eq_of_normalE16 hQ hdim hsgn h2 fr
      (ffE8_normalizer_mult hQ hdim hsgn h k hk'.2) (ffE8Syl_act_eq hQ h2 fr hk'.1) hUn
    have hmem : ffSimOmegaAct hQ h2 k u ∈ U.map (ffSimOmegaAct hQ h2 k).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hu
    rw [hmap] at hmem
    rw [← ff_omegaToSim_act hQ h2 k u]
    exact Subgroup.mem_map_of_mem _ hmem
  · rw [hYN]
    exact ⟨ffE8Syl_ts_mem_normalizer hQ hdim hsgn fr, hts⟩
  · intro hmem
    obtain ⟨u, -, hu⟩ := Subgroup.mem_map.mp hmem
    exact ffTs_not_simInOmegaStar hQ hdim fr ⟨(u : ProjOrth Q), u.2, hu⟩
  · intro b hb
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hb
    exact ffTs_comm_normalizer hQ h2 hπ fr (ffP1p_le_normalizer hQ hπ fr (hUn.1 hu))

end CFSG.OddStandard.SmallF3.Omega
