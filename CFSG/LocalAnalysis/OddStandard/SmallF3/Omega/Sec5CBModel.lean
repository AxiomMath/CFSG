module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CDModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CDPerm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CDZ

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

theorem sec5cb_model_of (hS : Asc82SchurU43) {t r : G} {L B : Subgroup G} (hL : IsOm6Z2 L)
    (ht2 : orderOf t = 2) (htc : t ∈ centerIn L) (htB : t ∈ B) (hBL : B ≤ L)
    (hE : IsElemAb2 B 5) (hrB : ∀ b ∈ B, r * b = b * r) (hrr : r * r = 1)
    (hr : ∃ α : ℤˣ, InducesTypeSome L r 6 (-1) 1 α) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V) (_ : FiniteDimensional (ZMod 3) V)
      (Q : QuadraticForm (ZMod 3) V) (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) 1) (i : Fin 6)
      (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (φc : ↥L →* omegaGroup hQ),
      IsCoverMap L φc ∧ (∀ l : ↥L, e (QuotientGroup.mk l) = omegaToProj hQ (φc l)) ∧
        Sec5CDAbs L B r i fr φc ∧ InducesViaP L (Subgroup.center ↥L) hQ e r
          (projOrthToProjSim Q (toProj Q (fr.signChange {i}))) := by
  obtain ⟨α, V, _, _, _, Q, hQ, e₀, x₀, hdim, hsgn, hx₀, hxt₀⟩ := hr
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  obtain ⟨fr⟩ := exists_nframe_six hQ hdim hsgn
  obtain ⟨y, hy⟩ := sec5c_adapt hS hL hdim hsgn h2 fr e₀ ht2 htc hBL hE htB
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
    hrr, sec5c_r_not_mem hdim hx hα', hrB, hx.1, fun l l' hl => ?_⟩, hx⟩
  · have h2b := hE.1.2 b hb
    rwa [pow_two] at h2b
  · have := hE.1.1.is_comm.comm (⟨a, ha⟩ : ↥B) ⟨b, hb⟩
    exact congrArg Subtype.val this
  · rw [hca.2 l l' hl, simAct_orthToSim]

theorem sec5cb_permModule_of (hS : Asc82SchurU43) {t r : G} {L B : Subgroup G} (hL : IsOm6Z2 L)
    (ht2 : orderOf t = 2) (htc : t ∈ centerIn L) (htB : t ∈ B) (hBL : B ≤ L)
    (hE : IsElemAb2 B 5) (hrB : ∀ b ∈ B, r * b = b * r) (hrr : r * r = 1)
    (hr : ∃ α : ℤˣ, InducesTypeSome L r 6 (-1) 1 α) :
    ∃ φ : (Fin 6 → ZMod 2) → G,
      IsPermModuleVia (n := 6) (fun _ => True) φ (zpowers r ⊔ B)
          (L ⊓ normalizer ((zpowers r ⊔ B : Subgroup G) : Set G)) (alternatingGroup (Fin 6)) ∧
        φ (fun _ => 1) = t ∧ ∃ i : Fin 6, φ (Pi.single i 1) = r := by
  obtain ⟨V, _, _, _, Q, hQ, fr, i, e, φc, hφ, he, habs, hind⟩ :=
    sec5cb_model_of hS hL ht2 htc htB hBL hE hrB hrr hr
  have htL : t ∈ L := hBL htB
  refine ⟨sec5c_phi L B r i fr φc, ?_, habs.phi_ones htL htB (hφ.map_central hL htc ht2 htL),
    ⟨i, habs.phi_single⟩⟩
  unfold IsPermModuleVia
  refine ⟨fun v w _ _ => habs.phi_add v w, fun v w _ _ hvw => habs.phi_inj hvw,
    fun x => ⟨fun hx => ?_, fun ⟨v, _, hv⟩ => habs.mem_A_iff.mpr ⟨v, hv⟩⟩, ?_, ?_⟩
  · obtain ⟨v, hv⟩ := habs.mem_A_iff.mp hx
    exact ⟨v, trivial, hv⟩
  · intro g hg
    obtain ⟨hgL, hgN⟩ := Subgroup.mem_inf.mp hg
    obtain ⟨σ, hσ, hform⟩ := habs.perm_of_mem ⟨g, hgL⟩ hgN
    exact ⟨σ, hσ, fun v _ => hform v⟩
  · intro σ hσ
    obtain ⟨g, hgN, hform⟩ := habs.exists_of_perm hσ
    exact ⟨g, Subgroup.mem_inf.mpr ⟨g.2, hgN⟩, fun v _ => hform v⟩

end CFSG.OddStandard.SmallF3.Omega
