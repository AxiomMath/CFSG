module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G6Om5TAlg
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MTrans
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGClosureFive
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FDLift

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec8t84g6t_reduce [Finite G] {K A : Subgroup G} {t : G} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V}
    (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 5) (hσ : quadSign Q = 1)
    (hK : IsOm5Q K) (e : ↥K ⧸ center ↥K ≃* omegaProj hQ) (htt : t * t = 1)
    (htK : t ∈ normalizer (K : Set G)) (hA : IsComponentIn A (K ⊓ centralizer ({t} : Set G)))
    (hL : IsL29 A) :
    ∃ u ∈ K ⊓ centralizer ({t} : Set G), u * u = 1 ∧ u ≠ 1 ∧ ¬ InnerOn A u := by
  haveI : Finite (ProjOrth Q) :=
    Nat.finite_of_card_ne_zero (by rw [natCard_projOrth_five hQ hdim]; norm_num)
  have hodd : Odd (Nat.card (center ↥K)) := by
    rw [ff_center_eq_oddCore_five hK]
    exact CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog.odd_card_oddCore
  obtain ⟨x, hx⟩ := ff_exists_induces hQ (Or.inl ⟨hdim, hσ⟩) e htK
  have hxx : x * x = 1 := ff6m_induces_sq hQ (by omega) e hx htt
  obtain ⟨y, hy⟩ := fg_simInGStar_of_odd hQ (by omega) (by rw [hdim]; decide) x
  have hyy : y * y = 1 := by
    apply projOrthToProjSim_injective (Q := Q)
    rw [map_mul, map_one, hy]
    exact hxx
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ↥K →* ↥(omegaProj hQ), ρ = ff6mPhi e := ⟨_, rfl⟩
  have hρcov : OddCentralCover ρ := hρ ▸ ff6m_phi_cover e hodd
  have hρker : ρ.ker ≤ center ↥K := by rw [hρ, ff6mPhi_ker e]
  have hcov : Sec4FDCover K t (omegaProj hQ) y ρ := by
    refine ⟨hρcov, htK, htt, hyy, ?_⟩
    intro l l' hl
    have h1 := hx.2 l l' hl
    rw [← hy, projSimAct_projOrthToProjSim] at h1
    rw [hρ]
    exact h1
  have hAK : A ≤ K := hA.1.trans inf_le_left
  have hA'T' : IsComponentIn (A.subgroupOf K) ((K ⊓ centralizer ({t} : Set G)).subgroupOf K) := by
    rw [← sec63PT_isComponentIn_map_iff K.subtype K.subtype_injective,
      Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAK,
      inf_eq_left.mpr inf_le_left]
    exact hA
  have hAT := sec63PT_isComponentIn_map ρ hρker hA'T'
  have hAT2 := (sec63PT_isComponentIn_map_iff (omegaProj hQ).subtype
    (omegaProj hQ).subtype_injective).mpr hAT
  have hD : (((K ⊓ centralizer ({t} : Set G)).subgroupOf K).map ρ).map (omegaProj hQ).subtype =
      omegaProj hQ ⊓ centralizer ({y} : Set (ProjOrth Q)) := by
    ext z
    constructor
    · rintro ⟨w, ⟨l, hl, rfl⟩, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨(ρ l).2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      exact hcov.image_comm l.2
        (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hl).2)
    · intro hz
      obtain ⟨hzΩ, hzy⟩ := Subgroup.mem_inf.mp hz
      obtain ⟨d, hdK, hdt, hdρ⟩ :=
        hcov.exists_lift hzΩ (Subgroup.mem_centralizer_singleton_iff.mp hzy)
      refine ⟨ρ ⟨d, hdK⟩, ⟨⟨d, hdK⟩, ?_, rfl⟩, hdρ⟩
      exact Subgroup.mem_inf.mpr ⟨hdK, Subgroup.mem_centralizer_singleton_iff.mpr hdt⟩
  rw [hD] at hAT2
  have hA'L : IsL29 (A.subgroupOf K) := by
    have h := (sec63PT_isL29_map_iff K.subtype K.subtype_injective
      (K := A.subgroupOf K)).mp
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAK] at h
    exact h hL
  have hρA := sec63PT_oddCentralCover_subgroupMap hρcov (A.subgroupOf K)
  have hρAL : IsL29 ((A.subgroupOf K).map ρ) :=
    (sec63PT_lieModel_psl_iff (ρ.subgroupMap (A.subgroupOf K)) hρA.surjective hρA.odd_card_ker
      2 3 2).mp hA'L
  have hAbL : IsL29 (((A.subgroupOf K).map ρ).map (omegaProj hQ).subtype) :=
    (sec63PT_isL29_map_iff (omegaProj hQ).subtype (omegaProj hQ).subtype_injective).mpr hρAL
  have hmodel : LieModel ↥(omegaProj hQ) .PSp 2 3 1 :=
    LieModel.of_mulEquiv e (ff_lieModel_center_five hK)
  have hsimple : IsSimpleGroup ↥(omegaProj hQ) :=
    (CFSG.LieType.Simplicity.fam_classical_converse ↥(omegaProj hQ)
      ⟨.PSp, 2, 3, 1, hmodel.statedClassicalModel_of_ne_zero (by norm_num : (2 : ℕ) ≠ 0)⟩).2.2
  obtain ⟨u₀, hu₀D, hu₀u₀, hu₀⟩ := sec8t84g6t_core hQ hdim hσ hsimple hyy hAT2 hAbL
  obtain ⟨hu₀Ω, hu₀y⟩ := Subgroup.mem_inf.mp hu₀D
  obtain ⟨v, hvK, hvt, hvv, hvρ⟩ :=
    hcov.exists_lift_invol hu₀Ω (Subgroup.mem_centralizer_singleton_iff.mp hu₀y) hu₀u₀
  have hv1 : v ≠ 1 := by
    intro h
    subst h
    have h1 : ((ρ ⟨1, hvK⟩ : ↥(omegaProj hQ)) : ProjOrth Q) = 1 := by
      rw [show (⟨1, hvK⟩ : ↥K) = 1 from rfl, map_one]
      rfl
    exact hu₀ 1 (Subgroup.one_mem _) 1 (Subgroup.one_mem _) (by rw [← hvρ, h1, one_mul])
  refine ⟨v, Subgroup.mem_inf.mpr ⟨hvK, Subgroup.mem_centralizer_singleton_iff.mpr hvt⟩, hvv,
    hv1, ?_⟩
  intro hin
  obtain ⟨a, haA, c, hc, hvac⟩ := ff_innerOn_decompose hin
  have haK : a ∈ K := hAK haA
  have hcK : c ∈ K := by
    have h : c = a⁻¹ * v := by rw [hvac]; group
    rw [h]
    exact K.mul_mem (K.inv_mem haK) hvK
  have hρv : ((ρ ⟨v, hvK⟩ : ↥(omegaProj hQ)) : ProjOrth Q) =
      ((ρ ⟨a, haK⟩ : ↥(omegaProj hQ)) : ProjOrth Q) *
        ((ρ ⟨c, hcK⟩ : ↥(omegaProj hQ)) : ProjOrth Q) := by
    have h : (⟨v, hvK⟩ : ↥K) = ⟨a, haK⟩ * ⟨c, hcK⟩ := Subtype.ext hvac
    rw [h, map_mul]
    rfl
  refine hu₀ _ ?_ _ ?_ (hvρ.symm.trans hρv)
  · exact ⟨ρ ⟨a, haK⟩, ⟨⟨a, haK⟩, haA, rfl⟩, rfl⟩
  · rw [Subgroup.mem_centralizer_iff]
    rintro b ⟨w, ⟨l, hl, rfl⟩, rfl⟩
    have hcomm : (l : G) * c = c * (l : G) := Subgroup.mem_centralizer_iff.mp hc (l : G) hl
    have h : l * ⟨c, hcK⟩ = ⟨c, hcK⟩ * l := Subtype.ext hcomm
    have h' := congrArg (fun z => ((ρ z : ↥(omegaProj hQ)) : ProjOrth Q)) h
    simp only [map_mul, Subgroup.coe_mul] at h'
    exact h'

end CFSG.OddStandard.SmallF3.Omega
