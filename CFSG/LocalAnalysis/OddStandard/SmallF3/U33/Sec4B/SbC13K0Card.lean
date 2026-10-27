module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC13K0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP0a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC13T
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQab

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private lemma c13K_om_inv (hc : Ctx13M t L S x₁ x₂ lam rho tau om) : om⁻¹ = om :=
  inv_eq_of_mul_eq_one_right hc.om_sq

private lemma c13K_conj_ttau_inv (hc : Ctx13M t L S x₁ x₂ lam rho tau om) :
    om⁻¹ * (t * tau) * om = t := by
  rw [c13K_om_inv hc]
  calc om * (t * tau) * om = om * (om * t * om⁻¹) * om := by rw [hc.t_om]
    _ = t := by
      calc om * (om * t * om⁻¹) * om = (om * om) * t * (om⁻¹ * om) := by group
        _ = t := by rw [hc.om_sq, c13K_om_inv hc, hc.om_sq]; group

private lemma c13K_conj_mem_Q (hc : Ctx13M t L S x₁ x₂ lam rho tau om) {x : G}
    (hx : x ∈ ctxQ t tau x₁ x₂ rho) : om * x * om⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
  hc.normal_Q.2 om (c13K_mem_M hc).2.2.1 x hx

private lemma c13K_conj_t_to_ttau (hc : Ctx13M t L S x₁ x₂ lam rho tau om) {x : G}
    (hx : x ∈ centralizer ({t} : Set G)) :
    om * x * om⁻¹ ∈ centralizer ({t * tau} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
  have h1 : om⁻¹ * (t * tau) * om = t := c13K_conj_ttau_inv hc
  calc (om * x * om⁻¹) * (t * tau)
      = om * x * (om⁻¹ * (t * tau) * om) * om⁻¹ := by group
    _ = om * x * t * om⁻¹ := by rw [h1]
    _ = om * (x * t) * om⁻¹ := by group
    _ = om * (t * x) * om⁻¹ := by rw [hx]
    _ = (t * tau) * (om * x * om⁻¹) := by
        rw [← hc.t_om]
        group

private lemma c13K_conj_ttau_to_t (hc : Ctx13M t L S x₁ x₂ lam rho tau om) {x : G}
    (hx : x ∈ centralizer ({t * tau} : Set G)) :
    om⁻¹ * x * om ∈ centralizer ({t} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
  have h2 : om⁻¹ * (t * tau) * om = t := c13K_conj_ttau_inv hc
  calc (om⁻¹ * x * om) * t
      = om⁻¹ * x * (om * t * om⁻¹) * om := by group
    _ = om⁻¹ * x * (t * tau) * om := by rw [hc.t_om]
    _ = om⁻¹ * (x * (t * tau)) * om := by group
    _ = om⁻¹ * ((t * tau) * x) * om := by rw [hx]
    _ = (om⁻¹ * (t * tau) * om) * (om⁻¹ * x * om) := by group
    _ = t * (om⁻¹ * x * om) := by rw [h2]

theorem c13K_card_base (hc : Ctx13M t L S x₁ x₂ lam rho tau om) :
    Nat.card ↥(baseGrp x₁ x₂) = 16 := by
  obtain ⟨V', v₁, v₂, hV⟩ := hc.data_V
  have hVcard : Nat.card V' = 4 := hV.2.1
  have hQeq : ctxQ t tau x₁ x₂ rho = baseGrp x₁ x₂ ⊔ V' := hV.2.2.1
  have hVbot : baseGrp x₁ x₂ ⊓ V' = ⊥ := hV.2.2.2.1
  have hbaseLeQ : baseGrp x₁ x₂ ≤ ctxQ t tau x₁ x₂ rho := hc.base_le_Q
  have hVleQ : V' ≤ ctxQ t tau x₁ x₂ rho := by rw [hQeq]; exact le_sup_right
  have hcomm : ∀ h ∈ baseGrp x₁ x₂, ∀ k ∈ V', h * k = k * h := by
    intro h hh k hk
    exact hc.Q_comm h (hbaseLeQ hh) k (hVleQ hk)
  have hformula := card_sup_mul_card_inf (H := baseGrp x₁ x₂) (K := V') hcomm
  rw [← hQeq, hVbot, Subgroup.card_bot, hVcard, IsZ4Z4E4.card hc.q_iso] at hformula
  omega

theorem c13K_card_C_ttau (hc : Ctx13M t L S x₁ x₂ lam rho tau om) :
    Nat.card ↥(ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * tau} : Set G)) = 16 := by
  let B : Subgroup G := ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G)
  let C : Subgroup G := ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * tau} : Set G)
  change Nat.card ↥C = 16
  have hB : B = baseGrp x₁ x₂ := (c13K_lemma4_12a hc).2.2.1
  have hCB : C = B.map (MulAut.conj om).toMonoidHom := by
    apply le_antisymm
    · intro c hcC
      have hcQ : c ∈ ctxQ t tau x₁ x₂ rho := (Subgroup.mem_inf.mp hcC).1
      have hcCent : c ∈ centralizer ({t * tau} : Set G) := (Subgroup.mem_inf.mp hcC).2
      refine Subgroup.mem_map.mpr ⟨om * c * om, ?_, ?_⟩
      · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · have h := c13K_conj_mem_Q hc hcQ
          rwa [c13K_om_inv hc] at h
        · have h := c13K_conj_ttau_to_t hc hcCent
          rwa [c13K_om_inv hc] at h
      · show (MulAut.conj om) (om * c * om) = c
        rw [MulAut.conj_apply, c13K_om_inv hc]
        calc om * (om * c * om) * om = (om * om) * c * (om * om) := by group
          _ = c := by rw [hc.om_sq]; group
    · intro x hx
      obtain ⟨b, hbB, rfl⟩ := Subgroup.mem_map.mp hx
      have hbQ : b ∈ ctxQ t tau x₁ x₂ rho := (Subgroup.mem_inf.mp hbB).1
      have hbCent : b ∈ centralizer ({t} : Set G) := (Subgroup.mem_inf.mp hbB).2
      exact Subgroup.mem_inf.mpr ⟨c13K_conj_mem_Q hc hbQ,
        c13K_conj_t_to_ttau hc hbCent⟩
  rw [hCB, Subgroup.card_map_of_injective (MulAut.conj om).injective, hB, c13K_card_base hc]

theorem c13K_ncard_Tp (hc : Ctx13M t L S x₁ x₂ lam rho tau om) :
    (c13KTp t tau x₁ x₂ rho).ncard = 32 := by
  let C : Subgroup G := ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * tau} : Set G)
  let D : Subgroup G := baseGrp x₁ x₂
  have hset : c13KTp t tau x₁ x₂ rho =
      (t • ((C : Subgroup G) : Set G)) ∪ ((t * tau) • ((D : Subgroup G) : Set G)) := by
    ext s
    rw [c13K_mem_Tp_iff hc s, Set.mem_union, Set.mem_smul_set, Set.mem_smul_set]
    constructor
    · rintro (⟨c, hcC, hcs⟩ | ⟨d, hdD, hds⟩)
      · left; exact ⟨c, hcC, by rw [smul_eq_mul]; exact hcs.symm⟩
      · right; exact ⟨d, hdD, by rw [smul_eq_mul]; exact hds.symm⟩
    · rintro (⟨c, hcC, hcs⟩ | ⟨d, hdD, hds⟩)
      · rw [smul_eq_mul] at hcs
        exact Or.inl ⟨c, hcC, hcs.symm⟩
      · rw [smul_eq_mul] at hds
        exact Or.inr ⟨d, hdD, hds.symm⟩
  have hdisj : Disjoint (t • ((C : Subgroup G) : Set G))
      ((t * tau) • ((D : Subgroup G) : Set G)) := by
    rw [Set.disjoint_left]
    intro s hs hs'
    rw [Set.mem_smul_set] at hs hs'
    obtain ⟨c, hcC, hcs⟩ := hs
    obtain ⟨d, hdD, hds⟩ := hs'
    rw [smul_eq_mul] at hcs hds
    have hcd : c = tau * d := by
      have h1 : t * c = t * (tau * d) := by
        calc t * c = s := hcs
          _ = (t * tau) * d := hds.symm
          _ = t * (tau * d) := by group
      exact mul_left_cancel h1
    have hcQ : c ∈ ctxQ t tau x₁ x₂ rho := (Subgroup.mem_inf.mp hcC).1
    have hdQ : d ∈ ctxQ t tau x₁ x₂ rho := hc.base_le_Q hdD
    exact (c13K_not_mem_Q hc).2.1 (by
      have htau : tau = c * d⁻¹ := by rw [hcd]; group
      have hmem := (ctxQ t tau x₁ x₂ rho).mul_mem hcQ ((ctxQ t tau x₁ x₂ rho).inv_mem hdQ)
      simpa [htau] using hmem)
  rw [hset, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _),
    Set.ncard_smul_set, Set.ncard_smul_set,
    ← Nat.card_coe_set_eq (C : Set G), ← Nat.card_coe_set_eq (D : Set G)]
  change Nat.card ↥(ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * tau} : Set G)) +
    Nat.card ↥(baseGrp x₁ x₂) = 32
  rw [c13K_card_C_ttau hc, c13K_card_base hc]

theorem c13K_ncard_tM (hc : Ctx13M t L S x₁ x₂ lam rho tau om) :
    (conjIn (ctxM t tau x₁ x₂) t).ncard = 8 :=
  p0_ncard_tM { toCtx10 := hc.toCtx10, tM := hc.tM }

theorem c13K_card_CM_t (hc : Ctx13M t L S x₁ x₂ lam rho tau om) :
    Nat.card ↥(ctxM t tau x₁ x₂ ⊓ centralizer ({t} : Set G)) = 384 := by
  have h := card_eq_ncard_conjIn_mul (ctxM t tau x₁ x₂) t
  rw [c13K_ncard_tM hc, hc.card_M] at h
  omega
end CFSG.OddStandard.SmallF3.HarrisU33.S4B
