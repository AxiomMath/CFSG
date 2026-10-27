module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55CaseB
public import CFSG.GH74.GLS.Stage2.Signalizer.L52TwoData
public import CFSG.GH74.GLS.Stage2.Signalizer.L52TwoCore

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.ABGLocalTools
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S T Tstar : Subgroup G} {p : ℕ}
  {H P : Subgroup G} {g : G} {X Y : Subgroup G}

theorem prime (h : Cfg55E G z k S T Tstar p H P g X Y) : p.Prime := h.c51.prime

theorem odd (h : Cfg55E G z k S T Tstar p H P g X Y) : p ≠ 2 := h.c51.odd

theorem T_le (h : Cfg55E G z k S T Tstar p H P g X Y) : T ≤ H := h.c51.T_le

theorem P_le (h : Cfg55E G z k S T Tstar p H P g X Y) : P ≤ H := h.c51.maxi.1.1

theorem P_pgroup (h : Cfg55E G z k S T Tstar p H P g X Y) : IsPGroup p ↥P := h.c51.maxi.1.2.1

theorem T_norm (h : Cfg55E G z k S T Tstar p H P g X Y) : T ≤ normalizer (P : Set G) :=
  h.c51.maxi.1.2.2.1

theorem cover (h : Cfg55E G z k S T Tstar p H P g X Y) :
    Covers (H ⊓ normalizer (P : Set G)) Tstar (pPrimeCoreOf 2 Tstar) :=
  h.c51.maxi.1.2.2.2

theorem g_mem (h : Cfg55E G z k S T Tstar p H P g X Y) : g ∈ P := h.s53.1

theorem g_mem_H (h : Cfg55E G z k S T Tstar p H P g X Y) : g ∈ H := P_le h (g_mem h)

theorem chief (h : Cfg55E G z k S T Tstar p H P g X Y) : IsChiefFactorIn H X Y :=
  h.s53.2.2.2.1

theorem X_pgroup (h : Cfg55E G z k S T Tstar p H P g X Y) : IsPGroup p ↥X := by
  have hp : Fact p.Prime := ⟨prime h⟩
  have hOp : IsPGroup p ↥(Op p H) := (pCore_isPGroup (G := ↥H) (p := p)).map H.subtype
  exact hOp.to_le h.s53.2.2.1

theorem quad_comm (h : Cfg55E G z k S T Tstar p H P g X Y) :
    ∀ x ∈ X, ⁅⁅x, g⁆, g⁆ ∈ Y := fun _ hx =>
  h.s53.2.2.2.2.1 (Subgroup.commutator_mem_commutator
    (Subgroup.commutator_mem_commutator hx (Subgroup.mem_zpowers g)) (Subgroup.mem_zpowers g))

theorem H_ne_top (h : Cfg55E G z k S T Tstar p H P g X Y) : H ≠ ⊤ :=
  H_ne_top_of_ctx51 h.ctx h.c51

structure UPart (z : G) (k : Kind) (S T Tstar : Subgroup G) (t : G) (q : ℕ) : Prop where
  kind : IsClassicalKind k
  udata : L52Two.UData z t
  four : IVK.IsFourSubgroup (L52Two.U4 z t)
  t_mem : t ∈ S
  U_le_T : L52Two.U4 z t ≤ T
  T_sylow : IsSylowOf 2 T (centralizer ((L52Two.U4 z t : Subgroup G) : Set G))
  T_le_S : T ≤ S
  Tstar_eq : Tstar = pLayerOf 2 (centralizer ((L52Two.U4 z t : Subgroup G) : Set G)) ⊔ T
  dih : ∃ D : Subgroup G, IsInternalDirectProduct (zpowers z ⊔ zpowers t) D
    (S ⊓ centralizer ({t} : Set G)) ∧ IsDihedral ↥D
  q_odd : Odd q
  q_gt : 3 < q
  L2 : IVK.IsL2 (↥(pLayerOf 2 (centralizer ((L52Two.U4 z t : Subgroup G) : Set G))) ⧸
    pPrimeCore 2 ↥(pLayerOf 2 (centralizer ((L52Two.U4 z t : Subgroup G) : Set G))))
    (fun r => r = q)
  cls : ∀ x₁ : G, IsNonCentralInvolution x₁ → IsConj x₁ (z * t)

theorem exists_uPart (h : Cfg55E G z k S T Tstar p H P g X Y) :
    ∃ (t : G) (q : ℕ), UPart z k S T Tstar t q := by
  obtain ⟨U, hUS, hU4, hzU, ⟨t₁, ht₁U, hsw₁c⟩, hT, hTS, hTstar⟩ :
      ∃ U : Subgroup G, U ≤ S ∧ IVK.IsFourSubgroup U ∧ z ∈ U ∧ (∃ t ∈ U, SwapsComps z t) ∧
        IsSylowOf 2 T (centralizer (U : Set G)) ∧ T ≤ S ∧
        Tstar = pLayerOf 2 (centralizer (U : Set G)) ⊔ T := by
    rcases h.c51.T5 with ⟨h1, -, -⟩ | ⟨-, h2⟩
    · exact absurd h1 h.two
    · exact h2
  obtain ⟨hcl, q, L₁, L₂, x₀, hP₁₂, hx, hpat⟩ :=
    L52Two.two_class_pattern h.ctx.detail.l4_two h.ctx h.two
  obtain ⟨L₁', L₂', hne', hcomps', hsw'⟩ := hsw₁c
  have hsw₁ : Swaps z t₁ L₁ L₂ :=
    L52Two.swaps_transport hne' (hcomps'.symm.trans hP₁₂.comps) hsw'
  obtain ⟨t, htS, hu, hUeq, hD, ⟨q', hq'o, hq'3, hL2⟩, hcls⟩ :=
    L52Two.data52_of_pattern h.ctx.central h.ctx.sylow hP₁₂ hx hpat hUS hU4 hzU ht₁U hsw₁
  subst hUeq
  exact ⟨t, q', hcl, hu, hU4, htS,
    L52Two.le_of_isSylowOf_centralizer hu.isPGroup_U4 hu.comm_U4 hT, hT, hTS, hTstar, hD,
    hq'o, hq'3, hL2, hcls⟩

theorem z_mem_H {t : G} {q : ℕ} (h : Cfg55E G z k S T Tstar p H P g X Y)
    (hU : UPart z k S T Tstar t q) : z ∈ H :=
  T_le h (hU.U_le_T (Subgroup.mem_sup_left (Subgroup.mem_zpowers z)))

theorem t_mem_H {t : G} {q : ℕ} (h : Cfg55E G z k S T Tstar p H P g X Y)
    (hU : UPart z k S T Tstar t q) : t ∈ H :=
  T_le h (hU.U_le_T (Subgroup.mem_sup_right (Subgroup.mem_zpowers t)))

theorem U_le_H {t : G} {q : ℕ} (h : Cfg55E G z k S T Tstar p H P g X Y)
    (hU : UPart z k S T Tstar t q) : L52Two.U4 z t ≤ H :=
  hU.U_le_T.trans (T_le h)

omit [Finite G] in
theorem T_le_centralizer {t : G} {q : ℕ} (hU : UPart z k S T Tstar t q) :
    T ≤ centralizer ((L52Two.U4 z t : Subgroup G) : Set G) :=
  hU.T_sylow.le

omit [Finite G] in
theorem T_isPGroup {t : G} {q : ℕ} (hU : UPart z k S T Tstar t q) : IsPGroup 2 ↥T :=
  hU.T_sylow.isPGroup

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
