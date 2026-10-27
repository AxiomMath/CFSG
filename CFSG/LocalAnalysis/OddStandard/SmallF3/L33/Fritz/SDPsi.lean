module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDSylowT
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDDataCore
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.OddStandard.SmallF3.L33.KD.SDPsi

open Subgroup Equiv CFSG.ComponentClassification.HSFLit CFSG.ComponentClassification.UnbalancedLayer

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X}

@[expose] noncomputable def psiOf (cfg : SDConfig t L) (M : SDModel ↥L)
    (T : Sylow 2 ↥(centralizer ({t} : Set X)))
    (hT : ∀ g ∈ (T : Subgroup ↥(centralizer ({t} : Set X))),
      SDAct.actC cfg.le_normalizer g ∈ SDAutP.P M.F) :
    ↥(Config.sylowIn T) →* Perm (ZMod 8) :=
  let f : ↥(T : Subgroup ↥(centralizer ({t} : Set X))) →* ↥(SDAutP.P M.F) :=
    ((SDAct.actC cfg.le_normalizer).comp (T : Subgroup _).subtype).codRestrict _
      (fun g => hT g g.2)
  ((H8.subtype).comp ((SDAutP.phi M.F).toMonoidHom.comp f)).comp
    (Subgroup.equivMapOfInjective (T : Subgroup _) (centralizer ({t} : Set X)).subtype
      (Subgroup.subtype_injective _)).symm.toMonoidHom

variable (cfg : SDConfig t L) (M : SDModel ↥L) (T : Sylow 2 ↥(centralizer ({t} : Set X)))
  (hT : ∀ g ∈ (T : Subgroup ↥(centralizer ({t} : Set X))),
    SDAct.actC cfg.le_normalizer g ∈ SDAutP.P M.F)

theorem psiOf_apply (g : ↥(centralizer ({t} : Set X))) (hg : g ∈ (T : Subgroup _)) :
    psiOf cfg M T hT ⟨(g : X), ⟨g, hg, rfl⟩⟩ =
      (SDAutP.phi M.F ⟨SDAct.actC cfg.le_normalizer g, hT g hg⟩ : Perm (ZMod 8)) := by
  have hx : (Subgroup.equivMapOfInjective (T : Subgroup ↥(centralizer ({t} : Set X)))
        (centralizer ({t} : Set X)).subtype (Subgroup.subtype_injective _)).symm
      ⟨(g : X), ⟨g, hg, rfl⟩⟩ = ⟨g, hg⟩ :=
    MulEquiv.symm_apply_apply (Subgroup.equivMapOfInjective
        (T : Subgroup ↥(centralizer ({t} : Set X)))
        (centralizer ({t} : Set X)).subtype (Subgroup.subtype_injective _)) ⟨g, hg⟩
  simp only [psiOf, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [hx]
  rfl

private lemma psiOf_eq_phi_actC (g : ↥(Config.sylowIn T))
    (c : ↥(centralizer ({t} : Set X))) (hcT : c ∈ (T : Subgroup _))
    (hceq : (g : X) = (c : X)) :
    psiOf cfg M T hT g =
      (SDAutP.phi M.F ⟨SDAct.actC cfg.le_normalizer c, hT c hcT⟩ : Perm (ZMod 8)) := by
  rw [show g = ⟨(c : X), ⟨c, hcT, rfl⟩⟩ from Subtype.ext hceq]
  exact psiOf_apply cfg M T hT c hcT

theorem psiOf_eq_one_iff (g : ↥(Config.sylowIn T)) :
    psiOf cfg M T hT g = 1 ↔ (g : X) ∈ coreActionKernel L := by
  obtain ⟨c, hcT, hceq⟩ := Subgroup.mem_map.mp g.2
  rw [psiOf_eq_phi_actC cfg M T hT g c hcT hceq.symm, ← hceq]
  have hsub : ((⟨SDAct.actC cfg.le_normalizer c, hT c hcT⟩ : ↥(SDAutP.P M.F)) = 1) ↔
      SDAct.actC cfg.le_normalizer c = 1 := Subtype.ext_iff
  have hsub2 : (H8.subtype (SDAutP.phi M.F
        ⟨SDAct.actC cfg.le_normalizer c, hT c hcT⟩) = 1) ↔
      SDAutP.phi M.F ⟨SDAct.actC cfg.le_normalizer c, hT c hcT⟩ = 1 :=
    map_eq_one_iff H8.subtype (Subgroup.subtype_injective H8)
  change H8.subtype (SDAutP.phi M.F ⟨SDAct.actC cfg.le_normalizer c, hT c hcT⟩) = 1 ↔
    (c : X) ∈ coreActionKernel L
  rw [hsub2, (SDAutP.phi M.F).map_eq_one_iff, hsub, ← MonoidHom.mem_ker,
    SDAct.mem_ker_actC cfg.le_normalizer]
  constructor
  · intro hc
    refine mem_coreActionKernel.mpr ⟨cfg.le_normalizer c.2, fun j hj => ?_⟩
    have hcomm : j * (c : X) = (c : X) * j := (mem_centralizer_iff.mp hc) j hj
    have h1 : j⁻¹ * (c : X)⁻¹ * j * (c : X) = 1 := by
      calc j⁻¹ * (c : X)⁻¹ * j * (c : X)
          = j⁻¹ * (c : X)⁻¹ * (j * (c : X)) := by group
        _ = j⁻¹ * (c : X)⁻¹ * ((c : X) * j) := by rw [hcomm]
        _ = 1 := by group
    rw [h1]
    exact one_mem _
  · intro hc
    exact mem_centralizer_iff.mpr (fun j hj => cfg.commute_kernel hj hc)

theorem psiOf_mem_H8 (g : ↥(Config.sylowIn T)) : psiOf cfg M T hT g ∈ H8 :=
  ((SDAutP.phi M.F) _).2

theorem psiOf_mem_S16 (g : ↥(Config.sylowIn T)) (hg : (g : X) ∈ L) :
    psiOf cfg M T hT g ∈ SD.S16 := by
  obtain ⟨c, hcT, hceq⟩ := Subgroup.mem_map.mp g.2
  rw [psiOf_eq_phi_actC cfg M T hT g c hcT hceq.symm]
  refine (SDAutP.phi_inner_iff M.F M.conj_injective
    ⟨SDAct.actC cfg.le_normalizer c, hT c hcT⟩).mp ?_
  rw [SDAutP.inn]
  refine ⟨⟨(g : X), hg⟩, ?_⟩
  have h1 : (⟨(g : X), cfg.le_centralizer hg⟩ : ↥(centralizer ({t} : Set X))) = c :=
    Subtype.ext hceq.symm
  change MulAut.conj (⟨(g : X), hg⟩ : ↥L) = SDAct.actC cfg.le_normalizer c
  rw [← h1]
  exact (SDAct.actC_of_mem cfg.le_normalizer cfg.le_centralizer (⟨(g : X), hg⟩ : ↥L)).symm

theorem exists_psiOf_eq {σ : Perm (ZMod 8)} (hσ : σ ∈ SD.S16) :
    ∃ g : ↥(Config.sylowIn T), (g : X) ∈ L ∧ psiOf cfg M T hT g = σ := by
  obtain ⟨p, hpPin, hpσ⟩ := SDAutP.exists_mem_Pin_phi_eq M.F M.conj_injective hσ
  have hconj (u : ↥(Config.sylowIn T ⊓ L : Subgroup X)) :
      MulAut.conj (⟨(u : X), u.2.2⟩ : ↥L) ∈ SDAutP.Pin M.F := by
    obtain ⟨c, hcT, hceq⟩ := Subgroup.mem_map.mp u.2.1
    rw [SDAutP.Pin_eq_inf M.F M.conj_injective]
    refine ⟨?_, ⟨⟨(u : X), u.2.2⟩, rfl⟩⟩
    have h1 : (⟨(u : X), cfg.le_centralizer u.2.2⟩ : ↥(centralizer ({t} : Set X))) = c :=
      Subtype.ext hceq.symm
    rw [← SDAct.actC_of_mem cfg.le_normalizer cfg.le_centralizer (⟨(u : X), u.2.2⟩ : ↥L), h1]
    exact hT c hcT
  let φ : ↥(Config.sylowIn T ⊓ L : Subgroup X) → ↥(SDAutP.Pin M.F) :=
    fun u => ⟨MulAut.conj (⟨(u : X), u.2.2⟩ : ↥L), hconj u⟩
  have hinj : Function.Injective φ := by
    intro u v huv
    have h1 : MulAut.conj (⟨(u : X), u.2.2⟩ : ↥L) =
        MulAut.conj (⟨(v : X), v.2.2⟩ : ↥L) := congrArg Subtype.val huv
    have h2 : (⟨(u : X), u.2.2⟩ : ↥L) = ⟨(v : X), v.2.2⟩ := M.conj_injective h1
    exact Subtype.ext (congrArg (Subtype.val : ↥L → X) h2)
  have hcard : Nat.card ↥(Config.sylowIn T ⊓ L : Subgroup X) =
      Nat.card ↥(SDAutP.Pin M.F) := by
    rw [SDSylowT.card_inf_L cfg.le_normalizer cfg.le_centralizer M T,
      SDAutP.card_Pin M.F M.conj_injective]
  have hbij : Function.Bijective φ :=
    (Nat.bijective_iff_injective_and_card φ).mpr ⟨hinj, hcard⟩
  obtain ⟨u, hu⟩ := hbij.2 ⟨(p : MulAut ↥L), hpPin⟩
  obtain ⟨c, hcT, hceq⟩ := Subgroup.mem_map.mp u.2.1
  have hψ : psiOf cfg M T hT ⟨(u : X), u.2.1⟩ =
      (SDAutP.phi M.F ⟨SDAct.actC cfg.le_normalizer c, hT c hcT⟩ : Perm (ZMod 8)) :=
    psiOf_eq_phi_actC cfg M T hT ⟨(u : X), u.2.1⟩ c hcT hceq.symm
  refine ⟨⟨(u : X), u.2.1⟩, u.2.2, ?_⟩
  have hpc : (⟨SDAct.actC cfg.le_normalizer c, hT c hcT⟩ : ↥(SDAutP.P M.F)) = p := by
    apply Subtype.ext
    have h1 : (⟨(u : X), cfg.le_centralizer u.2.2⟩ : ↥(centralizer ({t} : Set X))) = c :=
      Subtype.ext hceq.symm
    calc SDAct.actC cfg.le_normalizer c
        = SDAct.actC cfg.le_normalizer
            (⟨(u : X), cfg.le_centralizer u.2.2⟩ : ↥(centralizer ({t} : Set X))) := by rw [h1]
      _ = MulAut.conj (⟨(u : X), u.2.2⟩ : ↥L) :=
          SDAct.actC_of_mem cfg.le_normalizer cfg.le_centralizer (⟨(u : X), u.2.2⟩ : ↥L)
      _ = (p : MulAut ↥L) :=
          congrArg (Subtype.val : ↥(SDAutP.Pin M.F) → MulAut ↥L) hu
  rw [hψ, hpc, hpσ]

@[expose] noncomputable def sdData : SDData t L where
  config := cfg
  syl := T
  ψ := psiOf cfg M T hT
  ψ_eq_one_iff := psiOf_eq_one_iff cfg M T hT
  ψ_mem_H8 := psiOf_mem_H8 cfg M T hT
  ψ_mem_S16 := fun g hg => psiOf_mem_S16 cfg M T hT g hg
  exists_ψ_eq := fun _ hσ => exists_psiOf_eq cfg M T hT hσ

structure ModelCompat (M : SDModel ↥L) (A : SDData t L) : Prop where
  act_mem : ∀ g : ↥(centralizer ({t} : Set X)), g ∈ (A.syl : Subgroup ↥(centralizer ({t} : Set X)))
    → SDAct.actC A.config.le_normalizer g ∈ SDAutP.P M.F
  ψ_eq : ∀ (g : ↥(centralizer ({t} : Set X))) (hg : g ∈ (A.syl : Subgroup _)),
    A.ψ ⟨(g : X), ⟨g, hg, rfl⟩⟩ =
      (SDAutP.phi M.F ⟨SDAct.actC A.config.le_normalizer g, act_mem g hg⟩ : Perm (ZMod 8))

theorem modelCompat_sdData : ModelCompat M (sdData cfg M T hT) :=
  ⟨hT, psiOf_apply cfg M T hT⟩

theorem exists_sdData (cfg : SDConfig t L) (M : SDModel ↥L) :
    ∃ A : SDData t L, ModelCompat M A := by
  obtain ⟨T, hT⟩ := SDSylowT.exists_sylow_compat cfg.le_normalizer cfg.le_centralizer M
  exact ⟨sdData cfg M T hT, modelCompat_sdData cfg M T hT⟩

end CFSG.OddStandard.SmallF3.L33.KD.SDPsi
