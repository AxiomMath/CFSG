module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4I0A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4I0C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutAmbient
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.WreathB

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

@[expose] def z4iPsi (t tau x₁ x₂ rho : G) :
    ↥(ctxNQ t tau x₁ x₂ rho) →* MulAut ↥(ctxQ t tau x₁ x₂ rho) where
  toFun g := Outside.conjAut (ctxQ t tau x₁ x₂ rho) (g : G) g.2
  map_one' := Outside.conjAut_one _ _
  map_mul' a b := Outside.conjAut_mul _ a.2 b.2 (mul_mem a.2 b.2)

theorem z4iPsi_apply_coe (g : ↥(ctxNQ t tau x₁ x₂ rho)) (q : ↥(ctxQ t tau x₁ x₂ rho)) :
    ((z4iPsi t tau x₁ x₂ rho g q : ↥(ctxQ t tau x₁ x₂ rho)) : G) = (g : G) * q * (g : G)⁻¹ :=
  rfl

theorem z4iPsi_eq_one_iff (g : ↥(ctxNQ t tau x₁ x₂ rho)) :
    z4iPsi t tau x₁ x₂ rho g = 1 ↔ (g : G) ∈ ctxCQ t tau x₁ x₂ rho := by
  constructor
  · intro h
    rw [ctxCQ, Subgroup.mem_centralizer_iff]
    intro q hq
    have h1 : z4iPsi t tau x₁ x₂ rho g ⟨q, hq⟩ = ⟨q, hq⟩ := by
      rw [h]
      rfl
    have h2 : (g : G) * q * (g : G)⁻¹ = q := by
      have := congrArg (fun x : ↥(ctxQ t tau x₁ x₂ rho) => (x : G)) h1
      simpa [z4iPsi_apply_coe] using this
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2.symm
  · intro h
    apply MulEquiv.ext
    intro q
    show (z4iPsi t tau x₁ x₂ rho g) q = q
    apply Subtype.ext
    rw [z4iPsi_apply_coe]
    change (g : G) * (q : G) * (g : G)⁻¹ = (q : G)
    have hcomm : (q : G) * (g : G) = (g : G) * (q : G) :=
      Subgroup.mem_centralizer_iff.mp h (q : G) q.2
    rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]

theorem ctxKI_le_NQ (t tau x₁ x₂ rho : G) :
    ctxKI t tau x₁ x₂ rho ≤ ctxNQ t tau x₁ x₂ rho :=
  fun _ hk => hk.2.1

@[expose] def z4iPsiK (t tau x₁ x₂ rho : G) :
    ↥(ctxKI t tau x₁ x₂ rho) →* MulAut ↥(ctxQ t tau x₁ x₂ rho) :=
  (z4iPsi t tau x₁ x₂ rho).comp (Subgroup.inclusion (ctxKI_le_NQ t tau x₁ x₂ rho))

@[expose] def z4iV (t tau x₁ x₂ rho : G) : Subgroup ↥(ctxQ t tau x₁ x₂ rho) :=
  (fourGrp x₁ x₂).subgroupOf (ctxQ t tau x₁ x₂ rho)

theorem z4i_relIndex_eq_card (t tau x₁ x₂ rho : G) :
    (ctxCQ t tau x₁ x₂ rho).relIndex (ctxKI t tau x₁ x₂ rho) =
      Nat.card (z4iPsiK t tau x₁ x₂ rho).range := by
  rw [Subgroup.relIndex]
  have hker : (ctxCQ t tau x₁ x₂ rho).subgroupOf (ctxKI t tau x₁ x₂ rho) =
      (z4iPsiK t tau x₁ x₂ rho).ker := by
    ext k
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, z4iPsiK, MonoidHom.comp_apply,
      z4iPsi_eq_one_iff, Subgroup.coe_inclusion]
  rw [hker, Subgroup.index_ker]

namespace Ctx4Z

@[expose] def z4iRhoBar (hz : Ctx4Z t L S x₁ x₂ lam rho tau) : MulAut ↥(ctxQ t tau x₁ x₂ rho) :=
  z4iPsi t tau x₁ x₂ rho ⟨rho, hz.z4i_rho_mem_NQ⟩

@[expose] def z4iTauBar (hz : Ctx4Z t L S x₁ x₂ lam rho tau) : MulAut ↥(ctxQ t tau x₁ x₂ rho) :=
  z4iPsi t tau x₁ x₂ rho ⟨tau, hz.z4i_tau_mem_NQ⟩

theorem z4i_rhoBar_pow_three (hz : Ctx4Z t L S x₁ x₂ lam rho tau) : hz.z4iRhoBar ^ 3 = 1 := by
  have hrho3 : rho ^ 3 = 1 := by
    have := pow_orderOf_eq_one rho
    rwa [hz.ord_rho] at this
  change z4iPsi t tau x₁ x₂ rho ⟨rho, hz.z4i_rho_mem_NQ⟩ ^ 3 = 1
  rw [← map_pow]
  have h3 : (⟨rho, hz.z4i_rho_mem_NQ⟩ : ↥(ctxNQ t tau x₁ x₂ rho)) ^ 3 = 1 := by
    apply Subtype.ext
    simpa using hrho3
  rw [h3, map_one]

theorem z4i_tauBar_fixY (hz : Ctx4Z t L S x₁ x₂ lam rho tau) :
    hz.z4iTauBar ∈ S4B.z4iFixY ↥(ctxQ t tau x₁ x₂ rho) := by
  intro q hq
  apply Subtype.ext
  change ((z4iPsi t tau x₁ x₂ rho ⟨tau, hz.z4i_tau_mem_NQ⟩ q :
      ↥(ctxQ t tau x₁ x₂ rho)) : G) = (q : G)
  rw [z4iPsi_apply_coe]
  change tau * (q : G) * tau⁻¹ = (q : G)
  have hq2 : (q : G) ^ 2 = 1 := by
    have := congrArg (fun x : ↥(ctxQ t tau x₁ x₂ rho) => (x : G)) hq
    simpa using this
  have hqY : (q : G) ∈ ctxYq t tau x₁ x₂ rho :=
    (hz.mem_Y_iff (q : G)).mpr ⟨q.2, hq2⟩
  have hcomm : tau * (q : G) = (q : G) * tau := hz.tau_cent_Y (q : G) hqY
  rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]

theorem z4i_tauBar_V (hz : Ctx4Z t L S x₁ x₂ lam rho tau) (q : ↥(ctxQ t tau x₁ x₂ rho)) :
    hz.z4iTauBar q * q⁻¹ ∈ z4iV t tau x₁ x₂ rho := by
  rw [z4iV, Subgroup.mem_subgroupOf]
  have h1 : ((hz.z4iTauBar q : ↥(ctxQ t tau x₁ x₂ rho)) : G) = tau * (q : G) * tau⁻¹ := by
    change ((z4iPsi t tau x₁ x₂ rho ⟨tau, hz.z4i_tau_mem_NQ⟩ q :
      ↥(ctxQ t tau x₁ x₂ rho)) : G) = tau * (q : G) * tau⁻¹
    rw [z4iPsi_apply_coe]
  have h2 : tau * (q : G) * tau⁻¹ = (q : G)⁻¹ := hz.tau_inv_Q (q : G) q.2
  have hcoe : ((hz.z4iTauBar q * q⁻¹ : ↥(ctxQ t tau x₁ x₂ rho)) : G) = ((q : G)⁻¹) ^ 2 := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, h1, h2, pow_two]
  rw [hcoe]
  exact (hz.V_eq_sq (((q : G)⁻¹) ^ 2)).mpr ⟨(q : G)⁻¹, inv_mem q.2, rfl⟩

theorem z4i_rhoBar_comm_tauBar (hz : Ctx4Z t L S x₁ x₂ lam rho tau) :
    hz.z4iRhoBar * hz.z4iTauBar = hz.z4iTauBar * hz.z4iRhoBar := by
  change z4iPsi t tau x₁ x₂ rho ⟨rho, hz.z4i_rho_mem_NQ⟩ *
      z4iPsi t tau x₁ x₂ rho ⟨tau, hz.z4i_tau_mem_NQ⟩ =
    z4iPsi t tau x₁ x₂ rho ⟨tau, hz.z4i_tau_mem_NQ⟩ *
      z4iPsi t tau x₁ x₂ rho ⟨rho, hz.z4i_rho_mem_NQ⟩
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  simpa using hz.tau_rho.symm

theorem z4i_tauBar_ne_one (hz : Ctx4Z t L S x₁ x₂ lam rho tau) : hz.z4iTauBar ≠ 1 := by
  intro h
  apply hz.z4i_tau_not_mem_C
  exact (z4iPsi_eq_one_iff ⟨tau, hz.z4i_tau_mem_NQ⟩).mp
    (by change z4iPsi t tau x₁ x₂ rho ⟨tau, hz.z4i_tau_mem_NQ⟩ = 1; exact h)

theorem z4i_card_V (hz : Ctx4Z t L S x₁ x₂ lam rho tau) :
    Nat.card (z4iV t tau x₁ x₂ rho) = 4 := by
  rw [z4iV]
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hz.toCtx4Q.V_le_Q).toEquiv]
  exact hz.wreath.fourGrp_eq_omega.2.2

theorem z4i_hdet (hz : Ctx4Z t L S x₁ x₂ lam rho tau) :
    ∀ σ ∈ S4B.z4iFixY ↥(ctxQ t tau x₁ x₂ rho), ∀ τ ∈ S4B.z4iFixY ↥(ctxQ t tau x₁ x₂ rho),
      σ ⟨x₁, hz.x₁_mem_Q⟩ = τ ⟨x₁, hz.x₁_mem_Q⟩ → σ ⟨x₂, hz.x₂_mem_Q⟩ = τ ⟨x₂, hz.x₂_mem_Q⟩ →
        σ = τ := by
  intro σ hσ τ hτ hx1 hx2
  obtain ⟨V', v₁, v₂, hZV⟩ := hz.data_V
  rcases hZV with ⟨_, _, hQeq, _, hYeq, _, _, _, _, _, _, _, _, _, _⟩
  have hV'leY : V' ≤ ctxYq t tau x₁ x₂ rho := by
    rw [hYeq]
    exact le_sup_right
  set k : Set G := ({x₁, x₂} : Set G) ∪ (V' : Set G) with hk
  have hQcl : ctxQ t tau x₁ x₂ rho = closure k := by
    rw [hk, hQeq, baseGrp, Subgroup.sup_eq_closure, Subgroup.closure_union,
      Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  have key : ∀ x (hx : x ∈ closure k), ∀ hQ : x ∈ ctxQ t tau x₁ x₂ rho,
      σ ⟨x, hQ⟩ = τ ⟨x, hQ⟩ := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
        intro hQ
        rcases hy with hy | hy
        · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
          rcases hy with hyx1 | hyx2
          · have hsub : (⟨y, hQ⟩ : ↥(ctxQ t tau x₁ x₂ rho)) =
                ⟨x₁, hz.x₁_mem_Q⟩ := by
              apply Subtype.ext
              exact hyx1
            rw [hsub]
            exact hx1
          · have hsub : (⟨y, hQ⟩ : ↥(ctxQ t tau x₁ x₂ rho)) =
                ⟨x₂, hz.x₂_mem_Q⟩ := by
              apply Subtype.ext
              exact hyx2
            rw [hsub]
            exact hx2
        · have hyY : y ∈ ctxYq t tau x₁ x₂ rho := hV'leY hy
          have hy2 : y ^ 2 = 1 := ((hz.mem_Y_iff y).mp hyY).2
          have hq2 : (⟨y, hQ⟩ : ↥(ctxQ t tau x₁ x₂ rho)) ^ 2 = 1 := by
            apply Subtype.ext
            simpa using hy2
          rw [hσ ⟨y, hQ⟩ hq2, hτ ⟨y, hQ⟩ hq2]
    | one =>
        intro hQ
        have hsub : (⟨1, hQ⟩ : ↥(ctxQ t tau x₁ x₂ rho)) = 1 := Subtype.ext rfl
        rw [hsub, map_one, map_one]
    | mul x y hx hy ihx ihy =>
        intro hQ
        have hxQ : x ∈ ctxQ t tau x₁ x₂ rho := by rw [hQcl]; exact hx
        have hyQ : y ∈ ctxQ t tau x₁ x₂ rho := by rw [hQcl]; exact hy
        calc σ ⟨x * y, hQ⟩
            = σ (⟨x, hxQ⟩ * ⟨y, hyQ⟩) := congrArg σ (Subtype.ext rfl)
          _ = σ ⟨x, hxQ⟩ * σ ⟨y, hyQ⟩ := map_mul _ _ _
          _ = τ ⟨x, hxQ⟩ * τ ⟨y, hyQ⟩ := by rw [ihx hxQ, ihy hyQ]
          _ = τ (⟨x, hxQ⟩ * ⟨y, hyQ⟩) := (map_mul _ _ _).symm
          _ = τ ⟨x * y, hQ⟩ := (congrArg τ (Subtype.ext rfl)).symm
    | inv x hx ih =>
        intro hQ
        have hxQ : x ∈ ctxQ t tau x₁ x₂ rho := by rw [hQcl]; exact hx
        calc σ ⟨x⁻¹, hQ⟩
            = σ (⟨x, hxQ⟩⁻¹) := congrArg σ (Subtype.ext rfl)
          _ = (σ ⟨x, hxQ⟩)⁻¹ := map_inv _ _
          _ = (τ ⟨x, hxQ⟩)⁻¹ := by rw [ih hxQ]
          _ = τ (⟨x, hxQ⟩⁻¹) := (map_inv _ _).symm
          _ = τ ⟨x⁻¹, hQ⟩ := (congrArg τ (Subtype.ext rfl)).symm
  refine MulEquiv.ext fun q => ?_
  exact key q.1 (hQcl ▸ q.2) q.2

theorem z4i_psi_fixY (hz : Ctx4Z t L S x₁ x₂ lam rho tau) (g : ↥(ctxNQ t tau x₁ x₂ rho))
    (hg : (g : G) ∈ ctxEcY t tau x₁ x₂ rho) :
    z4iPsi t tau x₁ x₂ rho g ∈ S4B.z4iFixY ↥(ctxQ t tau x₁ x₂ rho) := by
  intro q hq
  apply Subtype.ext
  change ((z4iPsi t tau x₁ x₂ rho g q : ↥(ctxQ t tau x₁ x₂ rho)) : G) = (q : G)
  rw [z4iPsi_apply_coe]
  change (g : G) * (q : G) * (g : G)⁻¹ = (q : G)
  have hq2 : (q : G) ^ 2 = 1 := by
    have := congrArg (fun x : ↥(ctxQ t tau x₁ x₂ rho) => (x : G)) hq
    simpa using this
  have hqY : (q : G) ∈ ctxYq t tau x₁ x₂ rho :=
    (hz.mem_Y_iff (q : G)).mpr ⟨q.2, hq2⟩
  have hcomm : (q : G) * (g : G) = (g : G) * (q : G) :=
    Subgroup.mem_centralizer_iff.mp hg.2 (q : G) hqY
  rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]

theorem z4iPsiK_mem_comm (hz : Ctx4Z t L S x₁ x₂ lam rho tau)
    (k : ↥(ctxKI t tau x₁ x₂ rho)) :
    z4iPsiK t tau x₁ x₂ rho k ∈ ⁅S4B.z4iFixY ↥(ctxQ t tau x₁ x₂ rho), zpowers hz.z4iRhoBar⁆ := by
  set B : Subgroup (MulAut ↥(ctxQ t tau x₁ x₂ rho)) :=
    ⁅S4B.z4iFixY ↥(ctxQ t tau x₁ x₂ rho), zpowers hz.z4iRhoBar⁆ with hB
  set D : Subgroup G :=
    (B.comap (z4iPsi t tau x₁ x₂ rho)).map (ctxNQ t tau x₁ x₂ rho).subtype with hD
  have hclaim : ⁅ctxEcY t tau x₁ x₂ rho, zpowers rho⁆ ⊔ ctxCQ t tau x₁ x₂ rho ≤ D := by
    rw [hD]
    refine sup_le ?_ ?_
    · rw [Subgroup.commutator_le]
      intro e he g hg
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hg
      have heL : e ∈ ctxNQ t tau x₁ x₂ rho := he.1
      have hgL : g ∈ ctxNQ t tau x₁ x₂ rho := by
        rw [← hn]
        exact zpow_mem hz.z4i_rho_mem_NQ n
      have hmemL : ⁅e, g⁆ ∈ ctxNQ t tau x₁ x₂ rho := by
        rw [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem heL hgL) (inv_mem heL)) (inv_mem hgL)
      rw [Subgroup.mem_map]
      refine ⟨⟨⁅e, g⁆, hmemL⟩, ?_, rfl⟩
      rw [Subgroup.mem_comap]
      let r' : ↥(ctxNQ t tau x₁ x₂ rho) := ⟨rho, hz.z4i_rho_mem_NQ⟩
      let e' : ↥(ctxNQ t tau x₁ x₂ rho) := ⟨e, heL⟩
      let g' : ↥(ctxNQ t tau x₁ x₂ rho) := ⟨g, hgL⟩
      have he'fix : z4iPsi t tau x₁ x₂ rho e' ∈ S4B.z4iFixY ↥(ctxQ t tau x₁ x₂ rho) :=
        z4i_psi_fixY hz e' he
      have hg'zp : z4iPsi t tau x₁ x₂ rho g' ∈ zpowers hz.z4iRhoBar := by
        have hg'r : g' = r' ^ n := by
          apply Subtype.ext
          rw [Subgroup.coe_zpow]
          simpa using hn.symm
        refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
        calc hz.z4iRhoBar ^ n = (z4iPsi t tau x₁ x₂ rho r') ^ n := rfl
          _ = z4iPsi t tau x₁ x₂ rho (r' ^ n) := (map_zpow _ _ _).symm
          _ = z4iPsi t tau x₁ x₂ rho g' := by rw [hg'r]
      have hmap : z4iPsi t tau x₁ x₂ rho ⟨⁅e, g⁆, hmemL⟩ =
          ⁅z4iPsi t tau x₁ x₂ rho e', z4iPsi t tau x₁ x₂ rho g'⁆ := by
        have h1 : (⟨⁅e, g⁆, hmemL⟩ : ↥(ctxNQ t tau x₁ x₂ rho)) = ⁅e', g'⁆ := Subtype.ext rfl
        rw [h1, map_commutatorElement]
      rw [hmap, hB]
      exact Subgroup.commutator_mem_commutator he'fix hg'zp
    · intro c hc
      rw [Subgroup.mem_map]
      refine ⟨⟨c, ctxCQ_le_ctxNQ t tau x₁ x₂ rho hc⟩, ?_, rfl⟩
      rw [Subgroup.mem_comap]
      have h1 : z4iPsi t tau x₁ x₂ rho ⟨c, ctxCQ_le_ctxNQ t tau x₁ x₂ rho hc⟩ = 1 :=
        (z4iPsi_eq_one_iff ⟨c, ctxCQ_le_ctxNQ t tau x₁ x₂ rho hc⟩).mpr (by simpa using hc)
      rw [h1]
      exact B.one_mem
  have hkD : (k : G) ∈ D := hclaim k.2.1
  rw [hD, Subgroup.mem_map] at hkD
  obtain ⟨g, hgB, hgk⟩ := hkD
  rw [Subgroup.mem_comap] at hgB
  rw [z4iPsiK, MonoidHom.comp_apply]
  have hgi : g = Subgroup.inclusion (ctxKI_le_NQ t tau x₁ x₂ rho) k := by
    apply Subtype.ext
    rw [Subgroup.coe_inclusion]
    exact hgk
  rw [← hgi]
  exact hgB

theorem z4iPsiK_conj_mem (hz : Ctx4Z t L S x₁ x₂ lam rho tau)
    {σ : MulAut ↥(ctxQ t tau x₁ x₂ rho)} (hσ : σ ∈ (z4iPsiK t tau x₁ x₂ rho).range) :
    hz.z4iRhoBar * σ * hz.z4iRhoBar⁻¹ ∈ (z4iPsiK t tau x₁ x₂ rho).range := by
  obtain ⟨k, rfl⟩ := hσ
  refine ⟨⟨rho * (k : G) * rho⁻¹, hz.z4i_rho_norm_KI k.2⟩, ?_⟩
  set r' : ↥(ctxNQ t tau x₁ x₂ rho) := ⟨rho, hz.z4i_rho_mem_NQ⟩ with hr'
  set k' : ↥(ctxNQ t tau x₁ x₂ rho) := ⟨k, ctxKI_le_NQ t tau x₁ x₂ rho k.2⟩ with hk'
  have hincl : (Subgroup.inclusion (ctxKI_le_NQ t tau x₁ x₂ rho)
      ⟨rho * (k : G) * rho⁻¹, hz.z4i_rho_norm_KI k.2⟩ : ↥(ctxNQ t tau x₁ x₂ rho)) =
      r' * k' * r'⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_inclusion, Subgroup.coe_mul, Subgroup.coe_inv, hr', hk']
  have hzpsi : z4iPsi t tau x₁ x₂ rho (r' * k' * r'⁻¹) =
      hz.z4iRhoBar * z4iPsiK t tau x₁ x₂ rho k * hz.z4iRhoBar⁻¹ := by
    rw [map_mul, map_mul, map_inv]
    rw [show z4iPsi t tau x₁ x₂ rho r' = hz.z4iRhoBar from rfl,
      show z4iPsi t tau x₁ x₂ rho k' = z4iPsiK t tau x₁ x₂ rho k from rfl]
  rw [z4iPsiK, MonoidHom.comp_apply, hincl, hzpsi]
  rfl

end Ctx4Z

end CFSG.OddStandard.SmallF3.HarrisU33
