module

public import CFSG.GH74.QTGen4.Ch6.G112A2
public import CFSG.GH74.QTGen4.Leaves.RealizationRank
public import CFSG.Quasithin.EmptyFaithful.SzN28X0Main
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec2Lem18B
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec2Thm19B
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec2Thm19Inputs
public import CFSG.Quasithin.Vol2.Ch6Sec2Thm19A

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
  CFSG.LieType.BorelTits CFSG.Quasithin.ASInputs
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G}

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem false_ch619_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (h512 : Stmt5_1_2_F4)
    (h614 : Stmt6_1_4_F4) (h615 : Stmt6_1_5_F4) (h625 : Stmt6_2_5_F4) (h626 : Stmt6_2_6_F4)
    (h6210 : Stmt6_2_10_F4) (h6211 : Stmt6_2_11_F4) (h6212 : Stmt6_2_12_F4)
    (hG : G11.TheoremG112Fix) (hA2 : CFSG.GH74.QTGen4.G112ConclA2_le4) (hS8 : Res6219S8_F4)
    (hlt : ch6ZS T L V < V ⊓ uCh611 T L V) : False := by
  classical

  obtain ⟨z, hzZ, -, d, hdLS, -, -, haS, haZ, -⟩ := h.gens_ch617_F4 h331 h432 h512 h614 h615
  have hdH : d ∉ hCh611 T := by
    intro hdH
    apply haZ
    have hzd : z * d = d * z := Subgroup.mem_centralizer_iff.mp hdH z hzZ
    have e : d⁻¹ * z * d = z := by
      calc d⁻¹ * z * d = d⁻¹ * (z * d) := by group
        _ = d⁻¹ * (d * z) := by rw [hzd]
        _ = z := by group
    rw [e]
    exact hzZ
  set a := d⁻¹ * z * d with ha

  obtain ⟨hcomm, hZZU, -, -, -, hsq2, hZ2⟩ := h.ustruct_ch616_F4 h331 h432 h512 h614 h615
  obtain ⟨A, _, _, _, B, β, ρ, hR⟩ := exists_realization_ch619 (hCh611_le_normalizer_u T L V)
    hZZU hZ2 hsq2 (fun x hx y hy => h.comm_mem_ch615_F4 h331 h432 h512 h614 h615 hx hy)
    (fun x hx => by
      have := h.sq_mem_ch615_F4 h331 h432 h512 h614 h615 hx
      rwa [pow_two] at this)
  have haU : a ∈ uCh611 T L V := le_conjClosure _ _ haS
  have hVZU := h.inf_centerOf_eq_ch616_F4 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt
  have haZU : a ∉ centerOf (uCh611 T L V) := by
    intro haZU
    have : a ∈ V ⊓ centerOf (uCh611 T L V) := ⟨haS.1, haZU⟩
    rw [hVZU] at this
    exact haZ this

  have hZS4 : Nat.card (ch6ZS T L V) = 4 := by rw [h.toHyp611Nat.card_ZS]; norm_num
  have hZZS := h.omega_le_ZS_F4 h331 h432 h512 h614 h615
  obtain ⟨z₀, hz₀Z, hz₀1⟩ : ∃ z₀ ∈ zCh611 T, z₀ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : zCh611 T = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
    rw [this, Subgroup.card_bot] at hZ2
    omega
  have hv₁ : ∀ w : ↥(uCh611 T L V), (w : G) ∈ ch6ZS T L V →
      (w : G) ∉ centerOf (uCh611 T L V) → Multiplicative.toAdd (β w) = piA_ch619 hR a := by
    intro w hwS hwZU
    rw [← piA_eq_ch619 hR w.2]
    have hwZ : (w : G) ∉ zCh611 T := fun hwZ => hwZU (hZZU hwZ)
    rw [piA_eq_iff_ch619 hR w.2 haU]
    rcases L128P.eq_of_mem_four hZZS hZ2 hZS4 hz₀Z hz₀1 haZ haS hwS with e | e | e | e
    · exact absurd (e ▸ (zCh611 T).one_mem) hwZ
    · exact absurd (e ▸ hz₀Z) hwZ
    · rw [e, inv_mul_cancel]
      exact Subgroup.one_mem _
    · rw [e]
      have hz₀U := hZZU hz₀Z
      have hc : a * z₀ = z₀ * a := Subgroup.mem_centralizer_iff.mp hz₀U.2 a haU
      have e3 : (z₀ * a)⁻¹ * a = z₀⁻¹ := by
        calc (z₀ * a)⁻¹ * a = (a * z₀)⁻¹ * a := by rw [hc]
          _ = z₀⁻¹ := by group
      rw [e3]
      exact Subgroup.inv_mem _ hz₀U
  let Wsp : Submodule (ZMod 2) A :=
    { carrier := {x | ∃ e : ↥(uCh611 T L V),
        (e : G) ∈ uCh611 T L V ⊓ conjSubgroup (uCh611 T L V) d ∧ Multiplicative.toAdd (β e) = x}
      add_mem' := by
        rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
        exact ⟨e * e', Subgroup.mul_mem _ he he', by rw [map_mul, toAdd_mul]⟩
      zero_mem' := ⟨1, Subgroup.one_mem _, by rw [map_one, toAdd_one]⟩
      smul_mem' := by
        rintro c _ ⟨e, he, rfl⟩
        have hc : c = 0 ∨ c = 1 := by revert c; decide
        rcases hc with rfl | rfl
        · exact ⟨1, Subgroup.one_mem _, by rw [map_one, toAdd_one, zero_smul]⟩
        · exact ⟨e, he, by rw [one_smul]⟩ }
  have hW : ∀ x : A, x ∈ Wsp ↔ ∃ e : ↥(uCh611 T L V),
      (e : G) ∈ uCh611 T L V ⊓ conjSubgroup (uCh611 T L V) d ∧ Multiplicative.toAdd (β e) = x :=
    fun x => Iff.rfl

  obtain ⟨h111, h112⟩ := h.two_ch618_F4 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hG hlt hdLS
    hdH hR hv₁ hW

  obtain ⟨v, hv, hvU⟩ := h.exists_not_mem_U_ch615_F4 h6210 h6211 h6212 hlt
  have hd4 := h.four_le_finrank_ch619_F4 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt hR
  have hfin : Finite G := CFSG.GH74.QTGen4.Finite4.finite (G := G)
  have hle4 : Module.finrank (ZMod 2) A ≤ 4 :=
    CFSG.GH74.QTGen4.finrank_realization_le_four
      (CFSG.GH74.QTGen4.Finite4.gen4 (G := G)) β hR.1
  have htX := h.mem_map_X_ch619_F4 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt hR hdLS hdH hv
  have hrk := h.finrank_range_ch619_F4 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt hR hv hvU
  have hv₁R : piA_ch619 hR a ∈
      LinearMap.range ((ρ ⟨v, h.V_le_hCh611 hv⟩).toLinearMap - LinearMap.id) :=
    (h.mem_range_iff_ch619_F4 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt hR hv hvU _).mpr
      ⟨a, ⟨haS.1, haU⟩, rfl⟩
  have ha2 := h.isA2_ch619_F4 h331 h432 h512 h614 h615 hR hv
  have hfix := h.fix_ch619_F4 h331 h432 h512 h614 h615 h625 h626 h6210 h6211 h6212 hlt hR hv hvU haS
    haZ
  have hA2' : G112Conclusion B ρ.range (((conjSubgroup (uCh611 T L V) d ⊓
      Subgroup.centralizer (ch6ZS T L V : Set G)).subgroupOf (hCh611 T)).map ρ) ∨
      G11.G112Concl6U33 ρ.range → False := by
    intro hc
    obtain ⟨γ, hγ, hγR, hγv⟩ := hA2 A B ρ.range (piA_ch619 hR a) Wsp _ _ h111 hc hd4 hle4 _ htX hrk
      hv₁R ha2
    exact hγv (hfix γ hγ hγR)
  rcases h112 with h112 | h8 | h6
  · exact hA2' (Or.inl h112)
  · rcases hZZU.lt_or_eq with hZlt | hZeq
    · exact hS8 G T M L V h hlt hZlt d hdLS hdH A B β ρ hR h8
    · exact s8NoTrivialX0 A B ρ.range (piA_ch619 hR a) Wsp _ _ h111 h8
        (h.map_eq_bot_ch619_F4 h331 h432 h512 h614 h615 hR hdLS hZeq.symm)
  · exact hA2' (Or.inr h6)

end Hyp6Sec2

theorem stmt6_2_19Case2_of_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (h512 : Stmt5_1_2_F4)
    (h614 : Stmt6_1_4_F4) (h615 : Stmt6_1_5_F4) (h625 : Stmt6_2_5_F4) (h626 : Stmt6_2_6_F4)
    (h6210 : Stmt6_2_10_F4) (h6211 : Stmt6_2_11_F4) (h6212 : Stmt6_2_12_F4)
    (hG : G11.TheoremG112Fix) (hA2 : CFSG.GH74.QTGen4.G112ConclA2_le4) (hS8 : Res6219S8_F4) : Stmt6_2_19Case2_F4 := by
  intro G _ _ T M L V h hlt
  exact h.false_ch619_F4 h331 h432 h512 h614 h615 h625 h626 h6210 h6211 h6212 hG hA2 hS8 hlt

end CFSG.Quasithin.H13
