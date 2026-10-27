module

public import CFSG.GH74.Uniqueness.Section15Defs
public import CFSG.GH74.Uniqueness.Section15FactsBasic
public import CFSG.GH74.Uniqueness.Section15FactsNY
public import CFSG.GH74.Uniqueness.Section15Bender
public import CFSG.GH74.Uniqueness.Section15BenderJ

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem LData.out_cyclic_D {c : Ctx12 Z M} {n : ℕ} (hL : LData c n 1) :
    ∃ g₀ ∈ c.D, ∀ d ∈ c.D, ∃ i : ℕ, d * (g₀ ^ i)⁻¹ ∈ c.D ⊓ c.L ⊔ centralizer (c.L : Set X) := by
  obtain ⟨g₀, hg₀, hgen⟩ := bender_out_cyclic hL.bender
  obtain ⟨l₀, hl₀, d₀, hd₀, rfl⟩ := hL.N_eq g₀ hg₀
  have hd₀N : d₀ ∈ normalizer (c.L : Set X) := hL.D_le_N hd₀
  have hpow : ∀ i : ℕ, ∃ l ∈ c.L, (l₀ * d₀) ^ i = l * d₀ ^ i := by
    intro i
    induction i with
    | zero => exact ⟨1, one_mem _, by simp⟩
    | succ i ih =>
      obtain ⟨l, hl, hli⟩ := ih
      have hconj : d₀ ^ i * l₀ * (d₀ ^ i)⁻¹ ∈ c.L :=
        (mem_normalizer_iff.mp (pow_mem hd₀N i) l₀).mp hl₀
      refine ⟨l * (d₀ ^ i * l₀ * (d₀ ^ i)⁻¹), mul_mem hl hconj, ?_⟩
      rw [pow_succ, hli, pow_succ]
      group
  have hJn : ∀ j ∈ centralizer (c.L : Set X), ∀ l ∈ c.L, j * l * j⁻¹ ∈ c.L := by
    intro j hj l hl
    rw [← mem_centralizer_iff.mp hj l hl, mul_inv_cancel_right]
    exact hl
  refine ⟨d₀, hd₀, fun d hd => ?_⟩
  obtain ⟨i, hi⟩ := hgen d (hL.D_le_N hd)
  obtain ⟨l, hl, hli⟩ := hpow i
  have hmem : d * (d₀ ^ i)⁻¹ ∈ c.L ⊔ centralizer (c.L : Set X) := by
    have e : d * (d₀ ^ i)⁻¹ = (d * ((l₀ * d₀) ^ i)⁻¹) * l := by
      rw [hli]
      group
    rw [e]
    exact mul_mem hi (mem_sup_left hl)
  obtain ⟨l', hl', j, hj, hlj⟩ := exists_mul_of_sup_eq hJn hmem
  have hdD : d * (d₀ ^ i)⁻¹ ∈ c.D := mul_mem hd (inv_mem (pow_mem hd₀ i))
  have hjD : j ∈ c.D := hL.centralizer_le hj
  have hl'D : l' ∈ c.D := by
    have e : l' = d * (d₀ ^ i)⁻¹ * j⁻¹ := by rw [hlj]; group
    rw [e]
    exact mul_mem hdD (inv_mem hjD)
  refine ⟨i, ?_⟩
  rw [hlj]
  exact mul_mem (mem_sup_left (mem_inf.mpr ⟨hl'D, hl'⟩)) (mem_sup_right hj)

theorem ZDSetup.facts15
    (S : ZDSetup X Z M) (h12 : Sec12Results Z M) (h131 : Prop131Stmt Z M)
    {c : Ctx12 Z M} {n : ℕ} (hL : LData c n 1) :
    Facts15 M n c.L c.D (c.D ⊓ c.L) (centralizer (c.L : Set X)) (zHull Z M) (oTwoIn M) := by
  have hZ := S.invariant
  obtain ⟨Q, hQ⟩ := hL.borel
  have hQM : (Q : Subgroup c.L).map c.L.subtype = zHull Z M := hL.map_sylow_eq_zHull hZ hQ
  have hRM : (Bender.rootCenter (Q : Subgroup c.L)).map c.L.subtype = zHull Z M :=
    hL.map_subtype_rootCenter hZ hQ
  have hDL : (Bender.cartan (Q : Subgroup c.L) c.tL).map c.L.subtype = c.D ⊓ c.L :=
    Ctx12.map_subtype_cartan hQ
  obtain ⟨u, huD, hu2, huJ⟩ := ZDSetup.exists_inv_J h131 hL
  have hLu := h131 c n 1 hL u huD hu2
  obtain ⟨f, hf⟩ := (h12.l1214 c n 1 hL u huD hu2 hLu).2
  have hΩ := S.ncard_omega_15 h12 h131 hL
  exact
    { two_le := hL.hn
      D_le := inf_le_left
      card_M := hΩ.2
      oddGen := S.closure_odd_M
      fusion := fun x hx hx2 g hg => S.exists_mem_conj_of_isPGroup hx hx2 hg
      conj_D := S.conj_D_15 h12 hL
      Mo_le_M := Cor713.zHull_le M
      Mo_le_L := hL.m_le
      Mo_normal := hL.m_normal
      card_Mo := hL.m_card
      Mo_sq := hL.mo_sq
      cent_Mo_le := S.centralizer_zHull_le c
      K_eq := rfl
      card_K := hL.k_card
      K_cyclic := hL.k_cyclic
      K_trans := hL.K_trans hZ
      K_fpf := hL.K_fpf hZ
      J_eq := rfl
      J_le_D := hL.centralizer_le
      L_inf_J := hL.L_inf_J
      exists_inv_J := ⟨u, huJ, hu2⟩
      D_le_N := hL.D_le_N
      N_eq := hL.N_eq
      NM_eq := hL.NM_eq hZ
      NY_le := fun Y hYJ hY => S.normalizer_le_normalizer_L hL hΩ.1 hYJ hY
      cent_Mo_N := by
        intro g hg hcomm
        have := bender_cent_sylow hL.bender Q hg (fun x hx => hcomm x (hQM ▸ hx))
        rwa [hRM] at this
      cent_K_D := by
        intro d hd hcomm
        have hdM : d ∈ M := (mem_inf.mp hd).1
        have := bender_cent_cartan hL.bender Q (c.tL_mul_self hZ) (Ctx12.tL_not_mem_borel hQ)
          (hL.D_le_N hd) (fun x hx => by
            rw [hQM] at hx ⊢
            exact hL.m_normal d hdM x hx) (fun x hx => hcomm x (hDL ▸ hx))
        rwa [hDL] at this
      out_cyclic := hL.out_cyclic_D
      out_three := fun h3 g hg hg2 => by
        subst h3
        exact bender_out_three hL.bender hg hg2
      rank_le := fun A hA hsq => bender_rank_le hL.bender A hA hsq
      inv_comm := fun v hv hv2 => (h12.l129 c n 1 hL v hv hv2).1
      inv_conj := fun v hv hv2 g hg => S.inv_conj_normalizer h131 hL hv hv2 hg
      J_prime := bender_J_prime hL.bender _ f hf
      J_dihedral := fun h2 hcop => bender_J_dihedral hL.bender _ f hf ⟨u, huJ, hu2⟩ h2 hcop
      J_frob := bender_J_frob hL.bender _ f hf
      V_le := oTwoIn_le M
      V_normal := fun g hg v hv => oTwoIn_conj_mem M hg hv
      V_pgroup := oTwoIn_isPGroup M
      V_max := fun N hNM hn hp => le_oTwoIn hNM hn hp
      V_comm := S.oTwoIn_comm hL }

end CFSG.GH74.Uniqueness
