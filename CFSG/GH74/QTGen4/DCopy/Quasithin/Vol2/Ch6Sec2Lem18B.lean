module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec2Lem17C
public import CFSG.Quasithin.Vol2.Ch12Sec8OneTwelve
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem18A

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
  CFSG.LieType.BorelTits CFSG.Quasithin.ASInputs
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G}

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem four_lt_ch618_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (h512 : Stmt5_1_2_F4)
    (h614 : Stmt6_1_4_F4) (h615 : Stmt6_1_5_F4) (h626 : Stmt6_2_6_F4) (h6210 : Stmt6_2_10_F4)
    (h6211 : Stmt6_2_11_F4) (h6212 : Stmt6_2_12_F4) (hlt : ch6ZS T L V < V ⊓ uCh611 T L V) :
    4 < (centerOf (uCh611 T L V)).relIndex (uCh611 T L V) := by
  obtain ⟨U₀, hU₀U, -, hU₀es, hU₀32, -⟩ :=
    h.exists_extraspecial_ch615_F4 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt
  have hZ2 : Nat.card (zCh611 T) = 2 := h.card_omega_F4 h331 h432 h512 h614 h615
  have hUH : uCh611 T L V ≤ hCh611 T := h.uCh611_le_h_F4 h331 h432 h512 h614 h615
  have hZc : ∀ z ∈ zCh611 T, ∀ u ∈ uCh611 T L V, u * z = z * u := fun z hz u hu =>
    (Subgroup.mem_centralizer_iff.mp (hUH hu) z hz).symm
  have hcomm : ∀ a ∈ uCh611 T L V, ∀ b ∈ uCh611 T L V, a * b * a⁻¹ * b⁻¹ ∈ zCh611 T :=
    fun a ha b hb => h.comm_mem_ch615_F4 h331 h432 h512 h614 h615 ha hb
  obtain ⟨-, -, hcen⟩ := extraspecial_facts_ch615 hZ2 hU₀U hZc hcomm hU₀es
  have hle : centerOf (uCh611 T L V) ⊓ U₀ ≤ zCh611 T := fun x hx => hcen x hx.2 hx.1
  have hcard : Nat.card ↥(centerOf (uCh611 T L V) ⊓ U₀) ≤ 2 :=
    hZ2 ▸ Subgroup.card_le_of_le hle
  have h1 := Subgroup.relIndex_mul_card (centerOf (uCh611 T L V)) U₀
  have hne : (centerOf (uCh611 T L V)).relIndex (uCh611 T L V) ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  have h2 := Subgroup.relIndex_le_of_le_right hU₀U hne
  have h3 : 2 ^ 5 ≤ (centerOf (uCh611 T L V)).relIndex U₀ * 2 :=
    hU₀32.trans (h1 ▸ Nat.mul_le_mul_left _ hcard)
  omega

theorem two_ch618_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (h512 : Stmt5_1_2_F4)
    (h614 : Stmt6_1_4_F4) (h615 : Stmt6_1_5_F4) (h626 : Stmt6_2_6_F4) (h6210 : Stmt6_2_10_F4)
    (h6211 : Stmt6_2_11_F4) (h6212 : Stmt6_2_12_F4) (hG : G11.TheoremG112Fix)
    (hlt : ch6ZS T L V < V ⊓ uCh611 T L V) {l : G} (hl : l ∈ lsCh617 T L V)
    (hlH : l ∉ hCh611 T) {A : Type} [AddCommGroup A] [Module (ZMod 2) A] [Finite A]
    {B : LinearMap.BilinForm (ZMod 2) A} {β : ↥(uCh611 T L V) →* Multiplicative A}
    {ρ : ↥(hCh611 T) →* (A ≃ₗ[ZMod 2] A)}
    (hR : IsSymplecticRealization (hCh611 T) (uCh611 T L V) (centerOf (uCh611 T L V)) A B β ρ)
    {v₁ : A} {Wsp : Submodule (ZMod 2) A}
    (hv₁ : ∀ z : ↥(uCh611 T L V), (z : G) ∈ ch6ZS T L V →
      (z : G) ∉ centerOf (uCh611 T L V) → Multiplicative.toAdd (β z) = v₁)
    (hW : ∀ a : A, a ∈ Wsp ↔ ∃ e : ↥(uCh611 T L V),
      (e : G) ∈ uCh611 T L V ⊓ conjSubgroup (uCh611 T L V) l ∧ Multiplicative.toAdd (β e) = a) :
    G111Hyp B ρ.range v₁ Wsp (((conjSubgroup (uCh611 T L V) l ⊓
        Subgroup.centralizer (ch6ZS T L V : Set G)).subgroupOf (hCh611 T)).map ρ)
        (((conjSubgroup (centerOf (uCh611 T L V)) l).subgroupOf (hCh611 T)).map ρ) ∧
      G11.G112ConclusionFix B ρ.range (((conjSubgroup (uCh611 T L V) l ⊓
        Subgroup.centralizer (ch6ZS T L V : Set G)).subgroupOf (hCh611 T)).map ρ) := by
  have S := h.setting_ch617_F4 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt
  have hg := h.good_ch617_F4 h331 h432 h512 h614 h615 hl hlH
  have hU := h.uA_eq_ch617_F4 h331 h432 h512 h614 h615
  have hNZ := h.normalizer_Z_eq_ch617_F4 h331 h432 h512 h614 h615
  have hZ2 : Nat.card (zCh611 T) = 2 := h.card_omega_F4 h331 h432 h512 h614 h615
  have hZZS := h.omega_le_ZS_F4 h331 h432 h512 h614 h615
  have hHN : hCh611 T ≤ Subgroup.normalizer (uCh611 T L V : Set G) :=
    hCh611_le_normalizer_u T L V

  obtain ⟨z, -, -, d, -, -, -, haS, haZ, -⟩ := h.gens_ch617_F4 h331 h432 h512 h614 h615
  set a := d⁻¹ * z * d with ha
  have haU : a ∈ uCh611 T L V := le_conjClosure _ _ haS
  have haZU : a ∉ centerOf (uCh611 T L V) := by
    intro haZU
    have : a ∈ V ⊓ centerOf (uCh611 T L V) := ⟨haS.1, haZU⟩
    rw [h.inf_centerOf_eq_ch616_F4 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt] at this
    exact haZ this

  have hsqtk : IsQuotientOfSQTKTauCeti
      ↥((realHat_ch618 hR).img (Subgroup.normalizer (zCh611 T : Set G))) := by
    have := h.simple
    have hcore := CFSG.QuasithinUnique.qtkeCore_of_cat h.nonabelian h.qtke
    have hP : pCoreOf 2 (Subgroup.normalizer (zCh611 T : Set G)) ≠ ⊥ := by
      intro hb
      have h1 := LieType.BorelTits.le_pCoreOf_normalizer 2 (zCh611 T)
        (IsPGroup.of_card (n := 1) (by rw [hZ2, pow_one]))
      rw [hb, le_bot_iff] at h1
      rw [h1, Subgroup.card_bot] at hZ2
      norm_num at hZ2
    exact L1294.isQuotientOfSQTK_img (realHat_ch618 hR) (hNZ ▸ hHN) (hcore.1 _ hP)
  have key := S.twelve_of_eq hg hU (realHat_ch618 hR)
    (h.four_lt_ch618_F4 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt) haS haZ hG hsqtk
  have hW' : uCh611 T L V ⊓ Subgroup.centralizer (ch6ZS T L V : Set G) =
      L128A.wA (ch6ZS T L V) (zCh611 T) := (h.wA_eq_ch617_F4 h331 h432 h512 h614 h615).symm
  rw [hW', h.E_eq_ch617_F4 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt hg,
    h.X_eq_ch617_F4 h331 h432 h512 h614 h615 (ls_le_ch617 hl).2, rconj_eq_conjSubgroup_ch617,
    hNZ] at key
  obtain ⟨-, h111, h112⟩ := key

  have hXH : conjSubgroup (uCh611 T L V) l ⊓ Subgroup.centralizer (ch6ZS T L V : Set G) ≤
      hCh611 T := inf_le_right.trans (Subgroup.centralizer_le hZZS)
  have hZX : conjSubgroup (centerOf (uCh611 T L V)) l ≤
      conjSubgroup (uCh611 T L V) l ⊓ Subgroup.centralizer (ch6ZS T L V : Set G) := by
    have := L128A.Setting.rconj_centerOf_le_rconj_wA (ch6ZS T L V) (zCh611 T) l
    rwa [h.X_eq_ch617_F4 h331 h432 h512 h614 h615 (ls_le_ch617 hl).2, rconj_eq_conjSubgroup_ch617,
      hU] at this
  have e1 := realHat_img_self_ch618 hR hHN
  have e2 := realHat_img_ch618 hR hHN hXH
  have e3 := realHat_img_ch618 hR hHN (hZX.trans hXH)
  have e4 : (realHat_ch618 hR).π a = v₁ := by
    rw [realHat_pi_ch618 hR haU]
    exact hv₁ ⟨a, haU⟩ haS haZU
  have e5 := realHat_hat_ch618 hR (E := uCh611 T L V ⊓ conjSubgroup (uCh611 T L V) l) Wsp hW
  rw [e1, e2, e3, e4, e5] at h111
  rw [e1, e2] at h112
  exact ⟨h111, h112⟩

end Hyp6Sec2

end CFSG.Quasithin.H13
