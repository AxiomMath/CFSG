module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1OmCAbs
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1OmTransport
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Parts
public import CFSG.LocalAnalysis.GLTheoremA.S10.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S11.Defs
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.I145GW
public import CFSG.LocalAnalysis.GLTheoremA.S4S.KData
public import CFSG.LocalAnalysis.GLTheoremA.S9.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.Milestones.CL_LIT_Gorenstein_Walter_L_balance

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.GroupTheory.WeirSylow

local notation "Ω[" Q "]" =>
  ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆

section Iso

theorem omCoreShape_of_mulEquiv {T T' : Type} [Group T] [Finite T] [Group T'] [Finite T']
    (e : T ≃* T') (h : OmCoreShape T') : OmCoreShape T := by
  intro E hE hmax
  have hp : Nat.Prime 3 := Nat.prime_three
  set E' : Subgroup T' := E.map (e : T →* T') with hE'
  have hE'el : IsElemAbelian 3 E' := isElemAbelian_of_map 3 e hE
  have hpE : CFSG.Open.pRank 3 E' = CFSG.Open.pRank 3 E := pRank_map_mulEquiv 3 e E
  have hmax' : ∀ E'' : Subgroup T', IsElemAbelian 3 E'' →
      CFSG.Open.pRank 3 E'' ≤ CFSG.Open.pRank 3 E' := by
    intro E'' hE''
    have h1 := hmax (E''.map (e.symm : T' →* T)) (isElemAbelian_of_map 3 e.symm hE'')
    have h2 := pRank_map_mulEquiv 3 e.symm E''
    rw [hpE]
    omega
  obtain ⟨F', hFle, hFel, hFrank, L', hLsub, hLq, hLdvd⟩ := h E' hE'el hmax'
  refine ⟨F'.map (e.symm : T' →* T), ?_, isElemAbelian_of_map 3 e.symm hFel, ?_,
    L'.map (e.symm : T' →* T), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 (hFle hy)
    have : e.symm y = z := by rw [← hzy]; exact e.symm_apply_apply z
    show e.symm y ∈ E
    rw [this]
    exact hz
  · rw [pRank_map_mulEquiv 3 e.symm F', ← hpE]
    exact hFrank
  · have := CFSG.SignalizerFunctorTheorem.TransportA.isSubnormal_map e.symm hLsub
    rw [om_centralizer_map_mulEquiv e.symm F'] at this
    exact this
  · exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (MulEquiv.subgroupMap e.symm L') hLq
  · rw [← om_card_quotient_center_mulEquiv e.symm L']
    exact hLdvd

end Iso

section Derived

open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC

theorem omIsSubnormal_subgroupOf_of_conj {G : Type*} [Group G] {Ω C L : Subgroup G} (hCΩ : C ≤ Ω)
    (hLC : L ≤ C) (hconj : ∀ g ∈ C, ∀ x ∈ L, g * x * g⁻¹ ∈ L) :
    CFSG.Open.IsSubnormal (L.subgroupOf Ω) (C.subgroupOf Ω) := by
  refine CFSG.Open.IsSubnormal.step (fun x hx => ?_) ?_ (CFSG.Open.IsSubnormal.refl _)
  · rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hLC hx
  · constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hg : ((g : Subgroup.subgroupOf C Ω) : Ω).1 ∈ C := Subgroup.mem_subgroupOf.1 g.2
    have := hconj _ hg _ hn
    simpa using this

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem omCoreShape_derived (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : Module.finrank (ZMod 2) V = 2 * n) (hn : 5 ≤ n ∨ (n = 4 ∧ ¬ IsPlusType Q)) :
    OmCoreShape ↥(Ω[Q]) := by
  intro E hE hmax
  have hp : Nat.Prime 3 := Nat.prime_three
  set Ê : Subgroup (V ≃ₗ[ZMod 2] V) := E.map (Ω[Q]).subtype with hÊ
  have hÊle : Ê ≤ Ω[Q] := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hÊel : IsElemAbelian 3 Ê := CFSG.SectionRank.isElemAbelian_map hE (Ω[Q]).subtype
  have hcardÊ : Nat.card Ê = Nat.card E :=
    Subgroup.card_map_of_injective (f := (Ω[Q]).subtype) Subtype.val_injective
  have hmaxc : ∀ E' : Subgroup (V ≃ₗ[ZMod 2] V), E' ≤ Ω[Q] → IsElemAbelian 3 E' →
      Nat.card E' ≤ Nat.card Ê := by
    intro E' hE'Ω hE'el
    have hE''el : IsElemAbelian 3 (E'.subgroupOf (Ω[Q])) :=
      om_isElemAbelian_of_map_injective (Ω[Q]).subtype Subtype.val_injective (by
        rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hE'Ω]
        exact hE'el)
    have h1 := hmax _ hE''el
    obtain ⟨k, hk⟩ := om_exists_card_eq_pow hp hE''el
    obtain ⟨k', hk'⟩ := om_exists_card_eq_pow hp hE
    rw [om_pRank_eq_of_card hp hE''el hk, om_pRank_eq_of_card hp hE hk'] at h1
    have : Nat.card E' = Nat.card (E'.subgroupOf (Ω[Q])) :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE'Ω).toEquiv).symm
    rw [this, hcardÊ, hk, hk']
    exact Nat.pow_le_pow_right (by norm_num) h1
  obtain ⟨s, j, F, L, hcardE, hFE, hFel, hcardF, hrank, hL1, hL2, hL3, hL4⟩ :=
    omCore_abstract hQ hdim hn hÊle hÊel hmaxc
  have hEs : Nat.card E = 3 ^ s := by rw [← hcardÊ]; exact hcardE
  have hFΩ : F ≤ Ω[Q] := hFE.trans hÊle
  have hLΩ : L ≤ Ω[Q] := hL1.trans inf_le_left
  have hFel' : IsElemAbelian 3 (F.subgroupOf (Ω[Q])) :=
    om_isElemAbelian_of_map_injective (Ω[Q]).subtype Subtype.val_injective (by
      rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hFΩ]
      exact hFel)
  have hcF' : Nat.card (F.subgroupOf (Ω[Q])) = 3 ^ j := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFΩ).toEquiv]
    exact hcardF
  refine ⟨F.subgroupOf (Ω[Q]), ?_, hFel', ?_, L.subgroupOf (Ω[Q]), ?_, ?_, ?_⟩
  · intro x hx
    have hx' : (x : V ≃ₗ[ZMod 2] V) ∈ Ê := hFE (Subgroup.mem_subgroupOf.1 hx)
    obtain ⟨y, hy, hyx⟩ := hx'
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  · rw [om_pRank_eq_of_card hp hFel' hcF', om_pRank_eq_of_card hp hE hEs]
    exact hrank
  · have hcent : Subgroup.centralizer ((F.subgroupOf (Ω[Q]) : Subgroup ↥(Ω[Q])) : Set ↥(Ω[Q])) =
        (Ω[Q] ⊓ Subgroup.centralizer (F : Set (V ≃ₗ[ZMod 2] V))).subgroupOf (Ω[Q]) := by
      ext x
      simp only [Subgroup.mem_centralizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
        SetLike.mem_coe]
      constructor
      · intro h
        refine ⟨x.2, fun f hf => ?_⟩
        have := h ⟨f, hFΩ hf⟩ hf
        exact congrArg Subtype.val this
      · rintro ⟨-, h⟩ f hf
        exact Subtype.ext (h f.1 hf)
    rw [hcent]
    exact omIsSubnormal_subgroupOf_of_conj inf_le_left hL1 hL2
  · exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hLΩ).symm hL3
  · have e := Subgroup.subgroupOfEquivOfLe hLΩ
    rw [Nat.card_congr (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).toEquiv]
    exact hL4

end Derived

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
