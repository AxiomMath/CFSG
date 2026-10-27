module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CDAdapt
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CDLift
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Struct
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CoverAct
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84HP2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {V : Type} [AddCommGroup V]
  [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V}
  {hQ : Q.Nondegenerate}

theorem sec5c_r_index (hdim : Module.finrank (ZMod 3) V = 6)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) (fr : NFrame Q (Fin 6) 1)
    {e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ} {r : G} {x : ProjSim Q} {α : ℤˣ}
    (hx : InducesViaP L (Subgroup.center ↥L) hQ e r x) (hxt : SimHasType x 1 α) {B : Subgroup G}
    (hrB : ∀ b ∈ B, r * b = b * r) (hU : ffImg (ff6mPhi e) B = ffB1 hQ fr) :
    ∃ i : Fin 6, x = projOrthToProjSim Q (toProj Q (fr.signChange {i})) := by
  refine sec5c_cent_type1 hQ hdim h2 fr hxt fun w hw => ?_
  rw [← hU] at hw
  obtain ⟨l, hlB, rfl⟩ := mem_ffImg_iff.mp hw
  apply Subtype.ext
  rw [coe_ffSimOmegaAct]
  have hl : (l : G) = r * (l : G) * r⁻¹ := by
    rw [hrB _ hlB]
    group
  exact (hx.2 l l hl).symm

theorem sec5c_r_not_mem (hdim : Module.finrank (ZMod 3) V = 6)
    {e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ} {r : G} {x : ProjSim Q} {α : ℤˣ}
    (hx : InducesViaP L (Subgroup.center ↥L) hQ e r x) (hxt : SimHasType x 1 α) : r ∉ L := by
  intro hr
  have h5 : 5 ≤ Module.finrank (ZMod 3) V := by omega
  have heq := ff_induces_unique hQ h5 e hx (inducesViaP_of_mem e (⟨r, hr⟩ : ↥L))
  exact ff_simHasType_odd_not_simInOmegaStar hQ hdim (show Odd 1 from ⟨0, rfl⟩) hxt
    ⟨_, (e (QuotientGroup.mk (⟨r, hr⟩ : ↥L))).2, heq.symm⟩

theorem sec5c_model (hS : Asc82SchurU43) {t : G} {S : Subgroup G} {z r : G} {B A : Subgroup G}
    (hR : Sec5RCtx G t L S z r B A) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V) (_ : FiniteDimensional (ZMod 3) V)
      (Q : QuadraticForm (ZMod 3) V) (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) 1) (i : Fin 6)
      (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (φc : ↥L →* omegaGroup hQ),
      IsCoverMap L φc ∧ (∀ l : ↥L, e (QuotientGroup.mk l) = omegaToProj hQ (φc l)) ∧
        Sec5CDAbs L B r i fr φc ∧ InducesViaP L (Subgroup.center ↥L) hQ e r
          (projOrthToProjSim Q (toProj Q (fr.signChange {i}))) := by
  have hL : IsOm6Z2 L := hR.toSec5Ctx.toSec5Setting.isOm6Z2
  have ht2 : orderOf t = 2 := hR.involution
  have htt : t * t = 1 := by rw [← pow_two, ← ht2]; exact pow_orderOf_eq_one t
  have htB : t ∈ B := hR.B_split.1
  have hBL : B ≤ L := fun b hb => (Subgroup.mem_inf.mp (hR.B_le hb)).1
  have htL : t ∈ L := hBL htB
  have htc : t ∈ centerIn L := sec5_mem_centerIn_iff.mpr ⟨htL, fun y hy =>
    Subgroup.mem_centralizer_iff.mp (hR.component.1 hy) t (Set.mem_singleton t)⟩
  have hrB : ∀ b ∈ B, r * b = b * r := fun b hb =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hR.B_le hb)).2 r (Set.mem_singleton r)
  obtain ⟨α, V, _, _, _, Q, hQ, e₀, x₀, hdim, hsgn, hx₀, hxt₀⟩ := hR.type_r
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  obtain ⟨fr⟩ := exists_nframe_six hQ hdim hsgn
  obtain ⟨y, hy⟩ := sec5c_adapt hS hL hdim hsgn h2 fr e₀ ht2 htc hBL hR.B_E32 htB
  have hx : InducesViaP L (Subgroup.center ↥L) hQ (ffAdapt h2 e₀ y) r (y⁻¹ * x₀ * y) :=
    inducesViaP_ffAdapt h2 e₀ y hx₀
  obtain ⟨α', hα'⟩ := sec8t84h_simHasType_conj hQ hxt₀ y⁻¹
  rw [inv_inv] at hα'
  obtain ⟨i, hi⟩ := sec5c_r_index hdim h2 fr hx hα' hrB hy
  obtain ⟨φc, hφ, he⟩ := t5_cover_of_model hS hL hdim hsgn (ffAdapt h2 e₀ y)
  obtain ⟨hmap, honto⟩ := sec5c_img_B0 hL hφ he fr ht2 htc htB hBL hy
  rw [hi] at hx hα'
  have hca : CoverAct L φc r (orthToSim Q (fr.signChange {i})) :=
    t5_coverAct_of_inducesViaP hL hφ he hx (projOrthToProjSim_toProj _).symm
  refine ⟨V, inferInstance, inferInstance, inferInstance, Q, hQ, fr, i, ffAdapt h2 e₀ y, φc, hφ,
    he, ⟨hdim, hsgn, hφ.oddCentralCover hL, hBL, fun b hb => ?_, fun a ha b hb => ?_, hmap, honto,
    ?_, sec5c_r_not_mem hdim hx hα', hrB, hx.1, fun l l' hl => ?_⟩, hx⟩
  · have h2b := hR.B_E32.1.2 b hb
    rwa [pow_two] at h2b
  · have := (hR.B_E32.1.1).is_comm.comm (⟨a, ha⟩ : ↥B) ⟨b, hb⟩
    exact congrArg Subtype.val this
  · obtain ⟨g, hg⟩ := hR.conj_r
    rw [← hg]
    calc g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [htt]; group
  · rw [hca.2 l l' hl, simAct_orthToSim]

end CFSG.OddStandard.SmallF3.Omega
