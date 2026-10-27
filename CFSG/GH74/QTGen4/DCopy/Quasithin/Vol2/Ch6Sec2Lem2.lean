module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem2
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Lem6Three
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6StatementsSec2
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem513

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped LinearAlgebra.Projectivization

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G}

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem omega_le_V_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (h512 : Stmt5_1_2_F4)
    (h614 : Stmt6_1_4_F4) (h615 : Stmt6_1_5_F4) : quasithinOmegaOneCenter T ≤ V := by
  have h5 := h.toHyp5_0_1
  have hRred := isTwoReducedIn_reducedAggregate (L ⊔ T)
  have hRL : ⁅reducedAggregate (L ⊔ T), L⁆ = V := by
    rw [← h.toHyp611.lemma_6_1_6_three_F4 h331 h432 h512 h614 h615, h.comm_eq]
  intro z hz
  refine mem_of_odd_orbit_ch6 hRred.2.2.1 (le_sup_left.trans hRred.2.1) ?_ ?_
    (h5.omega_le_reducedAggregate hz) ?_
  · intro r hr x hx
    have : x * r * x⁻¹ * r⁻¹ ∈ ⁅L, reducedAggregate (L ⊔ T)⁆ :=
      Subgroup.commutator_mem_commutator hx hr
    rwa [Subgroup.commutator_comm, hRL] at this
  · have hT := h.toHyp611.inf_centralizer_eq_bot_F4 h331 h432 h615
    refine le_bot_iff.mp fun x hx => ?_
    rw [← hT]
    exact ⟨h5.reducedAggregate_le_T hx.1, hx.2⟩
  · have hsyl : IsSylowTwoOf (T ⊓ L) L :=
      A4.isSylowTwoOf_inf_normal (h5.isSylowTwoOf le_sup_right) le_sup_left
        h5.sup_le_normalizer
    have hle : T ⊓ L ≤ L ⊓ Subgroup.centralizer ({z} : Set G) := by
      intro x hx
      refine ⟨hx.2, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      rw [Set.mem_singleton_iff.mp hy]
      have hzT : z ∈ Subgroup.centralizer (T : Set G) := by
        refine (Subgroup.closure_le _).mpr ?_ hz
        rintro y ⟨⟨-, hy⟩, -⟩
        exact hy
      exact (Subgroup.mem_centralizer_iff.mp hzT x hx.1).symm
    have hdvd := Subgroup.relIndex_dvd_of_le_left L hle
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    intro h2
    exact hsyl.2.2 (h2.trans hdvd)

theorem not_centralizer_omega_le_F4 (h331 : Stmt3_3_1_F4) (h615 : Stmt6_1_5_F4) :
    ¬ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ M := by
  obtain ⟨H, hH⟩ := h.toHyp5_0_1.exists_isHStar_F4 h331
  exact fun hle => hH.2.1 ((h615 G T M L V 2 h.toHyp611 H hH).trans hle)

theorem exists_not_mem_centralizer_ZS_F4 (h331 : Stmt3_3_1_F4) (h615 : Stmt6_1_5_F4) :
    ∃ t ∈ T, t ∉ Subgroup.centralizer (ch6ZS T L V : Set G) := by
  by_contra hcon
  push Not at hcon
  apply h.not_centralizer_omega_le_F4 h331 h615
  have hZS : ch6ZS T L V ≤ quasithinOmegaOneCenter T := fun z hz =>
    Subgroup.subset_closure ⟨⟨h.toHyp611.le_T hz.1, Subgroup.mem_centralizer_iff.mpr
      fun t ht => (Subgroup.mem_centralizer_iff.mp (hcon t ht) z hz).symm⟩,
      h.toHyp611.isElemAbelian.2 z hz.1⟩
  exact (Subgroup.centralizer_le hZS).trans h.centralizer_le

theorem card_omega_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (h512 : Stmt5_1_2_F4)
    (h614 : Stmt6_1_4_F4) (h615 : Stmt6_1_5_F4) : Nat.card (quasithinOmegaOneCenter T) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, htT, htZ⟩ := h.exists_not_mem_centralizer_ZS_F4 h331 h615
  have hZV := h.omega_le_V_F4 h331 h432 h512 h614 h615
  have hZC : quasithinOmegaOneCenter T ≤ Subgroup.centralizer (T : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨⟨-, hy⟩, -⟩
    exact hy
  set U := ch6ZS T L V ⊓ Subgroup.centralizer ({t} : Set G) with hU
  have hZU : quasithinOmegaOneCenter T ≤ U := fun z hz =>
    ⟨⟨hZV hz, Subgroup.centralizer_le inf_le_left (hZC hz)⟩,
      Subgroup.mem_centralizer_iff.mpr fun y hy => by
        rw [Set.mem_singleton_iff.mp hy]
        exact Subgroup.mem_centralizer_iff.mp (hZC hz) t htT⟩
  have hUne : U ≠ ch6ZS T L V := by
    intro heq
    apply htZ
    refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
    rw [← heq] at hz
    exact (Subgroup.mem_centralizer_iff.mp hz.2 t rfl).symm
  have hZS4 : Nat.card (ch6ZS T L V) = 4 := by
    rw [h.toHyp611Nat.card_ZS]; norm_num
  have hU2 : Nat.card U ≤ 2 := by
    have hdvd : Nat.card U ∣ 4 := hZS4 ▸ Subgroup.card_dvd_of_le inf_le_left
    have hne : Nat.card U ≠ 4 := by
      intro h4
      exact hUne (Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h4, hZS4]))
    have : Nat.card U ∈ Nat.divisors 4 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have hd : Nat.divisors 4 = {1, 2, 4} := by decide
    rw [hd] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    omega
  have hZ2 : Nat.card (quasithinOmegaOneCenter T) ≤ 2 :=
    (Subgroup.card_le_of_le hZU).trans hU2
  have hZne : quasithinOmegaOneCenter T ≠ ⊥ :=
    CFSG.Quasithin.quasithinOmegaOneCenter_ne_bot h.sylow.1
      (fun hb => h.toHyp611Nat.ZS_ne_bot (le_bot_iff.mp (hb ▸ fun x hx =>
        h.toHyp611.le_T hx.1)))
  have hZ1 : 1 < Nat.card (quasithinOmegaOneCenter T) := by
    rw [Finite.one_lt_card_iff_nontrivial]
    exact (Subgroup.nontrivial_iff_ne_bot _).mpr hZne
  omega

end Hyp6Sec2

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem card_autOn_sup_F4 (h331 : Stmt3_3_1_F4) (h615 : Stmt6_1_5_F4) :
    Nat.card ↥(autOn (L ⊔ T) V) = 120 := by
  classical
  set D := h.toHyp611Nat.data with hD
  set f : ↥(autOn (L ⊔ T) V) →* Equiv.Perm (ℙ D.K (Fin 2 → D.K)) :=
    D.projPerm.comp (Subgroup.inclusion h.toHyp611Nat.autOn_sup_le_semilinSub) with hf
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro φ hφ
    exact Subtype.ext (h.toHyp611Nat.eq_one_of_projPerm_ch6 φ.2 hφ)
  have hP : Nat.card (ℙ D.K (Fin 2 → D.K)) = 5 := by
    rw [Projectivization.card_of_finrank_two D.K (Fin 2 → D.K) (Module.finrank_fin_fun D.K),
      D.card]
    norm_num
  have hle : Nat.card ↥(autOn (L ⊔ T) V) ≤ 120 := by
    have := Nat.card_le_card_of_injective f hinj
    rwa [Nat.card_perm, hP] at this
  have hdvd : 60 ∣ Nat.card ↥(autOn (L ⊔ T) V) := by
    rw [← h.toHyp611Nat.card_autOn_L_ch6]
    exact Subgroup.card_dvd_of_le (A4.autOn_mono le_sup_left)

  obtain ⟨t, htT, htZ⟩ := h.exists_not_mem_centralizer_ZS_F4 h331 h615
  have htN : t ∈ Subgroup.normalizer (V : Set G) := h.toHyp611.T_le_normalizer htT
  have htX : conjAct V ⟨t, htN⟩ ∈ autOn (L ⊔ T) V :=
    mem_autOn_iff.mpr ⟨⟨t, htN⟩, Subgroup.mem_sup_right htT, rfl⟩
  have htL : conjAct V ⟨t, htN⟩ ∉ autOn L V := by
    intro htL
    obtain ⟨g, hgL, hg⟩ := mem_autOn_iff.mp htL
    obtain ⟨A, hA⟩ := D.exists_matrix_of_mem g hgL
    obtain ⟨v, hv, hlev⟩ := h.toHyp611Nat.exists_line
    apply htZ
    refine h.toHyp611Nat.mem_centralizer_ZS_of_linear hv hlev htT fun c w => ?_
    have e : ∀ w, D.conj ⟨t, htN⟩ w = (A : Matrix (Fin 2) (Fin 2) D.K).mulVec w := fun w => by
      rw [← D.trAut_conjAct, ← hg, D.trAut_conjAct, hA]
    rw [e, e, Matrix.mulVec_smul]
  have hne : Nat.card ↥(autOn (L ⊔ T) V) ≠ 60 := by
    intro h60
    apply htL
    have heq : autOn L V = autOn (L ⊔ T) V := Subgroup.eq_of_le_of_card_ge
      (A4.autOn_mono le_sup_left) (by rw [h60, h.toHyp611Nat.card_autOn_L_ch6])
    rw [heq]
    exact htX
  have hpos : 0 < Nat.card ↥(autOn (L ⊔ T) V) := Nat.card_pos
  obtain ⟨k, hk⟩ := hdvd
  rcases k with _ | _ | k
  · omega
  · omega
  · omega

theorem nonempty_autOn_mulEquiv_perm_F4 (h331 : Stmt3_3_1_F4) (h615 : Stmt6_1_5_F4) :
    Nonempty (↥(autOn (L ⊔ T) V) ≃* Equiv.Perm (Fin 5)) := by
  classical
  set D := h.toHyp611Nat.data with hD
  set f : ↥(autOn (L ⊔ T) V) →* Equiv.Perm (ℙ D.K (Fin 2 → D.K)) :=
    D.projPerm.comp (Subgroup.inclusion h.toHyp611Nat.autOn_sup_le_semilinSub) with hf
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro φ hφ
    exact Subtype.ext (h.toHyp611Nat.eq_one_of_projPerm_ch6 φ.2 hφ)
  have hP : Nat.card (ℙ D.K (Fin 2 → D.K)) = 5 := by
    rw [Projectivization.card_of_finrank_two D.K (Fin 2 → D.K) (Module.finrank_fin_fun D.K),
      D.card]
    norm_num
  have hbij : Function.Bijective f := hinj.bijective_of_nat_card_le (by
    rw [Nat.card_perm, hP, h.card_autOn_sup_F4 h331 h615]; rfl)
  exact ⟨(MulEquiv.ofBijective f hbij).trans (Finite.equivFinOfCardEq hP).permCongrHom⟩

end Hyp6Sec2

theorem stmt6_2_2_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (h512 : Stmt5_1_2_F4) (h614 : Stmt6_1_4_F4)
    (h615 : Stmt6_1_5_F4) : Stmt6_2_2_F4 := fun _ _ _ _ _ _ _ h =>
  ⟨h.nonempty_autOn_mulEquiv_perm_F4 h331 h615, h.card_omega_F4 h331 h432 h512 h614 h615,
    h.not_centralizer_omega_le_F4 h331 h615⟩

end CFSG.Quasithin.H13
