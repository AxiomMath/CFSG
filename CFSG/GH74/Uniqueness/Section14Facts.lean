module

public import CFSG.GH74.Uniqueness.Section14J
public import CFSG.GH74.Uniqueness.Section14Defs
public import CFSG.GH74.Uniqueness.Section14Lem45

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

namespace Sec14

variable {c : Ctx12 Z M} {n : ℕ} {Q : Sylow 2 ↥c.L}

theorem cent_D_K (S : ZDSetup X Z M) (h : LData c n 2)
    (hQ : (M ⊓ c.L).subgroupOf c.L = normalizer ((Q : Subgroup c.L) : Set c.L)) :
    ∀ d ∈ c.D, (∀ k ∈ kGrp M c.t, d * k = k * d) →
      ∃ k ∈ kGrp M c.t, ∃ j ∈ centralizer (c.L : Set X), d = k * j := by
  intro d hd hdK
  set σ := conjAut c.L ⟨d, D_le_N h hd⟩ with hσ
  have hσQ : ∀ x ∈ (Q : Subgroup ↥c.L), σ x ∈ (Q : Subgroup ↥c.L) := by
    intro x hx
    have h1 : (d * (x : X) * d⁻¹) ∈ pGrp c Q :=
      (mem_normalizer_iff.mp (D_norm_P h hQ hd) x).mp (mem_map_of_mem _ hx)
    obtain ⟨y, hy, hye⟩ := mem_pGrp_iff.mp h1
    have : y = σ x := Subtype.ext hye
    rw [← this]
    exact hy
  have hσD : ∀ y ∈ Bender.cartan (Q : Subgroup ↥c.L) c.tL, σ y = y := by
    intro y hy
    apply Subtype.ext
    have hyK : (y : X) ∈ kGrp M c.t := by
      rw [K_eq_map h hQ]
      exact mem_map_of_mem _ hy
    change d * y * d⁻¹ = y
    rw [hdK _ hyK, mul_inv_cancel_right]
  obtain ⟨d₀, hd₀, hσd₀⟩ := h.bender.aut_eq_conj_cartan_suzuki Q (c.tL_mul_self S.invariant)
    (Ctx12.tL_not_mem_borel hQ) σ hσQ hσD
  have hd₀K : (d₀ : X) ∈ kGrp M c.t := by
    rw [K_eq_map h hQ]
    exact mem_map_of_mem _ hd₀
  refine ⟨d₀, hd₀K, (d₀ : X)⁻¹ * d, ?_, by group⟩
  rw [mem_centralizer_iff]
  intro l hl
  have h1 := congrArg Subtype.val (hσd₀ ⟨l, hl⟩)
  change d * l * d⁻¹ = (d₀ : X) * l * (d₀ : X)⁻¹ at h1
  calc l * ((d₀ : X)⁻¹ * d) = (d₀ : X)⁻¹ * ((d₀ : X) * l * (d₀ : X)⁻¹) * d := by group
    _ = (d₀ : X)⁻¹ * (d * l * d⁻¹) * d := by rw [h1]
    _ = (d₀ : X)⁻¹ * d * l := by group

theorem U_ne_bot (h12 : Sec12Results Z M) (h : LData c n 2) {U : Subgroup X}
    (hU : ABGLocalTools.IsSylowOf 2 U (centralizer (c.L : Set X))) : U ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, huD, hu2⟩ := exists_involution_D c
  have huJ := mem_J_of_involution h12 h huD hu2
  have h2 : 2 ∣ Nat.card (centralizer (c.L : Set X)) := by
    have := orderOf_dvd_natCard (⟨u, huJ⟩ : ↥(centralizer (c.L : Set X)))
    rwa [Subgroup.orderOf_mk, hu2] at this
  intro hbot
  have h1 := hU.card_eq
  rw [hbot, card_bot] at h1
  have : 0 < (Nat.card (centralizer (c.L : Set X))).factorization 2 :=
    Nat.prime_two.factorization_pos_of_dvd Nat.card_pos.ne' h2
  have := Nat.one_lt_pow this.ne' (by norm_num : 1 < 2)
  omega

theorem exists_facts14
    (S : ZDSetup X Z M) (h12 : Sec12Results Z M) (h131 : Prop131Stmt Z M)
    (c : Ctx12 Z M) {n : ℕ} (h : LData c n 2) :
    ∃ (r : ℕ) (Q : Sylow 2 ↥c.L) (U S2 : Subgroup X),
      Facts14 Z M c.t n r c.L (kGrp M c.t) (centralizer (c.L : Set X)) (zHull Z M) (pGrp c Q) U
        (pGrp c Q ⊔ U) S2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := h.borel
  obtain ⟨U, hU⟩ := ABGLocalTools.exists_isSylowOf 2 (centralizer (c.L : Set X))
  have hn : 1 ≤ n := by have := (n_odd h).2; omega
  obtain ⟨r, hr, hdvd, hprim⟩ := exists_zsigmondy (n_odd h).2
  set T := pGrp c Q ⊔ U with hT
  have hT2 : IsPGroup 2 ↥T := isPGroup_T S h hQ hU
  obtain ⟨Q₂, hQ₂⟩ := (hT2.comap_subtype (K := normalizer (T : Set X))).exists_le_sylow
  set S2 := (Q₂ : Subgroup ↥(normalizer (T : Set X))).map (normalizer (T : Set X)).subtype
  have hS2 : ABGLocalTools.IsSylowOf 2 S2 (normalizer (T : Set X)) := ⟨Q₂, rfl⟩
  have hTS2 : T ≤ S2 := by
    intro x hx
    exact ⟨⟨x, le_normalizer hx⟩, hQ₂ (by simpa [mem_subgroupOf] using hx), rfl⟩
  have hUsq := U_sq S h12 h hQ hU hS2 hTS2
  refine ⟨r, Q, U, S2, ?_⟩
  exact
    { n_odd := (n_odd h).1
      three_le := (n_odd h).2
      r_prime := hr
      r_ne_two := zsig_ne_two hn hdvd
      invariant := S.invariant
      t_not_mem := c.htM
      zM := by
        intro x hxM
        have e := h.zM_eq
        constructor
        · intro hxZ
          have : x ∈ zM Z M := ⟨hxZ, hxM⟩
          rw [e] at this
          exact this
        · intro hx
          have : x ∈ (zHull Z M : Set X) \ {1} := hx
          rw [← e] at this
          exact this.1
      Mo_le_M := (closure_le _).mpr Set.inter_subset_right
      Mo_normal := h.m_normal
      normalizer_Mo_le := by
        intro g hg
        have hzMo : c.z ∈ zHull Z M := subset_closure ⟨c.hz, c.hzM⟩
        have h1 := (mem_normalizer_iff.mp (inv_mem hg) c.z).mp hzMo
        rw [inv_inv] at h1
        exact (S.prodDisc.2.2.1 c.z c.hz c.hzM g).mp
          ((closure_le _).mpr Set.inter_subset_right h1)
      centralizer_Mo_le := C0_le_M S
      card_M := card_M S h12 h
      r_not_dvd_D := r_not_dvd_D h12 h131 h hr hdvd hprim
      K_eq := h.k_eq'
      K_card := by rw [h.k_eq']; exact h.k_card
      K_comm := by
        intro a ha b hb
        rw [h.k_eq'] at ha hb
        exact Bender.mul_comm_of_isCyclic h.k_cyclic ha hb
      K_trans := K_trans S h hQ
      K_fpf_P := K_fpf_P S h hQ
      cent_K_M := cent_K_M S h12 h
      cent_K_C0 := cent_K_C0 S h12 h hQ
      conj_D := conj_D S h12 h
      D_norm_L := D_le_N h
      D_norm_P := D_norm_P h hQ
      cent_D_K := cent_D_K S h hQ
      card_D := card_D h
      J_eq := rfl
      J_le_D := h.centralizer_le
      L_inf_J := L_inf_J h
      NY_le := fun _ hYJ hY => normalizer_le_of_le_J S h hYJ hY
      conj_J_NL := fun _ hv hv1 _ hw hw1 _ hg => mem_normalizer_of_conj_J S h hv hv1 hw hw1 hg
      NL_eq := NL_eq h
      NL_P := NL_P S h hQ
      coprime_J := lemma144b S h12 h131 h hQ hr hdvd hprim
      card_J_14 := card_J_14 h12 h131 h hU hUsq
      big_U := big_U h12 h131 h hU hUsq
      card_U_le := card_U_le h12 h131 h hU hUsq
      Mo_le_P := Mo_le_P S h hQ
      P_le_L := P_le_L
      P_le_M := P_le_M hQ
      card_Mo := h.m_card
      card_P := card_P S h hQ
      Mo_sq := Mo_sq S h
      Mo_central := Mo_central S h hQ
      center_P := center_P S h hQ
      comm_P := comm_P S h hQ
      P_sq := P_sq S h hQ
      P_sq_ne := P_sq_ne S h hQ
      P_sq_inj := P_sq_inj S h hQ
      U_le_J := hU.le
      U_ne_bot := U_ne_bot h12 h hU
      U_sylow_J := hU
      U_sylow_D := U_sylow_D h hU
      U_sq := hUsq
      cent_U_J := cent_U_J h12 h131 h hU hUsq
      T_eq := rfl
      comm_T := comm_T S h hQ hU hUsq
      T_sylow := T_sylow S h hQ hU
      cent_Mo_NL := cent_Mo_NL S h hQ
      cent_Mo_u := cent_Mo_u S h12 h131 h hQ hU hUsq
      two_part := two_part S h12 h hQ hU
      M_eq := lemma145a S h12 h131 h hQ hr hdvd hprim
      two_C0 := by
        intro g hg hg2
        obtain ⟨k, hk⟩ := hg2 ⟨g, mem_zpowers g⟩
        exact lemma145b S h12 h131 h hQ hr hdvd hprim g hg k
          (by simpa using congrArg Subtype.val hk)
      S2_sylow := hS2
      T_le_S2 := hTS2
      not_norm_sylow := fun R hR => lemma144a S h12 h131 h hr hdvd hprim R hR
      conj_U := conj_U h12 h hU }

end Sec14

end CFSG.GH74.Uniqueness
