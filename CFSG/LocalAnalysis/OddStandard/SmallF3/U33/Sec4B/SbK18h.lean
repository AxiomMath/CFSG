module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18g
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18f
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Fix
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18Lift

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

private lemma comm_of_conj_eq_self {u g : G} (h : u * g * u⁻¹ = g) : u * g = g * u := by
  calc u * g = (u * g * u⁻¹) * u := by group
    _ = g * u := by rw [h]

private lemma mem_centralizer_singleton {u g : G} (h : u * g = g * u) :
    g ∈ centralizer ({u} : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  rw [hy]
  exact h

theorem k18_card_CQ_u (hc : Ctx13 t L S x₁ x₂ lam rho tau om) {V' : Subgroup G} {v₁ v₂ : G}
    (hV : Ctx13V t tau x₁ x₂ lam rho om V' v₁ v₂) :
    8 ≤ Nat.card ↥(ctxQ t tau x₁ x₂ rho ⊓ centralizer ({lam * t} : Set G)) := by
  obtain ⟨hV1, hV2, hVQ, hVbase, hVrho, hVu, hVY, hVfix, hv₁V, hv₁ne, hv₁t, hv₂V,
    hv₂nv₁, hVgen, hv₂t, hv₂u, hVcent, hω₁, hω₂⟩ := hV
  have hx12Q : x₁ * x₂ ∈ ctxQ t tau x₁ x₂ rho :=
    hc.base_le_Q ((baseGrp x₁ x₂).mul_mem (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp)))
  have hx12C : x₁ * x₂ ∈ centralizer ({lam * t} : Set G) :=
    mem_centralizer_singleton (comm_of_conj_eq_self (k18_u_x₁x₂ hc))
  have hv₁fix : v₁ ∈ V' ⊓ centralizer ({lam * t} : Set G) := by
    rw [hVfix]
    exact Subgroup.mem_zpowers v₁
  have hv₁V' : v₁ ∈ V' := hv₁fix.1
  have hv₁C : v₁ ∈ centralizer ({lam * t} : Set G) := hv₁fix.2
  have hP1Q : zpowers (x₁ * x₂) ≤ ctxQ t tau x₁ x₂ rho :=
    Subgroup.zpowers_le.mpr hx12Q
  have hP1C : zpowers (x₁ * x₂) ≤ centralizer ({lam * t} : Set G) :=
    Subgroup.zpowers_le.mpr hx12C
  have hP2V' : zpowers v₁ ≤ V' := Subgroup.zpowers_le.mpr hv₁V'
  have hV'Q : V' ≤ ctxQ t tau x₁ x₂ rho := by
    rw [hVQ]
    exact le_sup_right
  have hP2Q : zpowers v₁ ≤ ctxQ t tau x₁ x₂ rho := hP2V'.trans hV'Q
  have hP2C : zpowers v₁ ≤ centralizer ({lam * t} : Set G) :=
    Subgroup.zpowers_le.mpr hv₁C
  have hP1base : zpowers (x₁ * x₂) ≤ baseGrp x₁ x₂ :=
    Subgroup.zpowers_le.mpr ((baseGrp x₁ x₂).mul_mem (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp)))
  have hinf : zpowers (x₁ * x₂) ⊓ zpowers v₁ = ⊥ := by
    have hle : zpowers (x₁ * x₂) ⊓ zpowers v₁ ≤ (⊥ : Subgroup G) :=
      hVbase ▸ inf_le_inf hP1base hP2V'
    exact le_bot_iff.mp hle
  have hnorm : ∀ k ∈ zpowers v₁, ∀ h ∈ zpowers (x₁ * x₂), k * h * k⁻¹ ∈ zpowers (x₁ * x₂) := by
    intro k hk h hh
    have hkQ : k ∈ ctxQ t tau x₁ x₂ rho := hP2Q hk
    have hhQ : h ∈ ctxQ t tau x₁ x₂ rho := hP1Q hh
    have hcomm : k * h = h * k := IsZ4Z4E4.comm hc.q_iso hkQ hhQ
    have hkh : k * h * k⁻¹ = h := by rw [hcomm]; group
    rw [hkh]
    exact hh
  have hcardP2 : Nat.card (zpowers v₁) = 2 := by
    have hv₁sq : v₁ ^ 2 = 1 := hV1.2 v₁ hv₁V'
    have hord : orderOf v₁ = 2 := orderOf_eq_prime hv₁sq hv₁ne
    rw [Nat.card_zpowers, hord]
  have hcardP1 : Nat.card (zpowers (x₁ * x₂)) = 4 := by
    have hnot : ¬ (x₁ * x₂) ^ 2 ^ 1 = 1 := by
      simpa using hc.wreath.sq_x₁x₂_ne_one
    have hfin : (x₁ * x₂) ^ 2 ^ (1 + 1) = 1 := by
      have h4 : (x₁ * x₂) ^ 4 = 1 := by
        rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add]
        exact hc.wreath.sq_x₁x₂_mul_self
      simpa using h4
    have hord := orderOf_eq_prime_pow (x := x₁ * x₂) (p := 2) (n := 1) hnot hfin
    rw [Nat.card_zpowers]
    simpa using hord
  have hcard : Nat.card ↥(zpowers (x₁ * x₂) ⊔ zpowers v₁) = 8 := by
    rw [card_sup_eq_mul hnorm hinf, hcardP1, hcardP2]
  have hle : zpowers (x₁ * x₂) ⊔ zpowers v₁ ≤
      ctxQ t tau x₁ x₂ rho ⊓ centralizer ({lam * t} : Set G) :=
    sup_le (fun x hx => ⟨hP1Q hx, hP1C hx⟩) (fun x hx => ⟨hP2Q hx, hP2C hx⟩)
  have hcardle := Subgroup.card_le_of_le hle
  rw [hcard] at hcardle
  exact hcardle

theorem k18_exists_fixed_Xi (hc : Ctx18 t L S x₁ x₂ lam rho tau om 𝒮) {V' : Subgroup G}
    {v₁ v₂ : G} (hV : Ctx13V t tau x₁ x₂ lam rho om V' v₁ v₂) :
    ∃ ξ ∈ ctxXi t tau x₁ x₂ rho, ξ ∉ ctxQ t tau x₁ x₂ rho ∧ (lam * t) * ξ * (lam * t)⁻¹ = ξ := by
  have hQ_lt_Xi : ctxQ t tau x₁ x₂ rho < ctxXi t tau x₁ x₂ rho := by
    refine lt_of_le_of_ne (l18_Q_le_Xi hc.toCtx13) ?_
    intro heq
    have hQ64 : Nat.card (ctxQ t tau x₁ x₂ rho) = 64 := IsZ4Z4E4.card hc.toCtx13.q_iso
    have hXi256 : Nat.card (ctxXi t tau x₁ x₂ rho) = 2 ^ 8 := k18_card_Xi hc
    rw [heq, hXi256] at hQ64
    norm_num at hQ64
  have hnormXi : ∀ n ∈ ctxXi t tau x₁ x₂ rho,
      (lam * t) * n * (lam * t)⁻¹ ∈ ctxXi t tau x₁ x₂ rho :=
    (l18_Xi_normal hc.toCtx13).2 (lam * t) (k18_u_mem_K hc.toCtx13)
  have hnormQ : ∀ e ∈ ctxQ t tau x₁ x₂ rho,
      (lam * t) * e * (lam * t)⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
    k18_u_normalizes_Q hc.toCtx13
  obtain ⟨n, hnXi, hnQ, hncoset⟩ :=
    exists_fixed_coset (l18_Xi_pgroup hc.toCtx13) hQ_lt_Xi (k18_u_sq hc.toCtx13)
      hnormXi hnormQ
  obtain ⟨q, hqQ, hfix⟩ :=
    exists_fixed_mul_of_free (Q := ctxQ t tau x₁ x₂ rho)
      (A₀ := closure ({x₁, v₂} : Set G)) (u := lam * t) (n := n)
      (k18_u_sq hc.toCtx13)
      (fun a ha b hb => IsZ4Z4E4.comm hc.toCtx13.q_iso ha hb)
      (k18_A0_le_Q hc.toCtx13 hV) (k18_u_normalizes_Q hc.toCtx13)
      (k18_free_A0 hc.toCtx13 hV).1 (k18_free_A0 hc.toCtx13 hV).2 hncoset
  refine ⟨n * q, ?_, ?_, ?_⟩
  · exact (ctxXi t tau x₁ x₂ rho).mul_mem hnXi ((l18_Q_le_Xi hc.toCtx13) hqQ)
  · intro hmem
    apply hnQ
    have hn : n = (n * q) * q⁻¹ := by group
    rw [hn]
    exact (ctxQ t tau x₁ x₂ rho).mul_mem hmem ((ctxQ t tau x₁ x₂ rho).inv_mem hqQ)
  · exact hfix

theorem k18_card_CXi_u (hc : Ctx18 t L S x₁ x₂ lam rho tau om 𝒮) {V' : Subgroup G}
    {v₁ v₂ : G} (hV : Ctx13V t tau x₁ x₂ lam rho om V' v₁ v₂) :
    16 ≤ Nat.card ↥(ctxXi t tau x₁ x₂ rho ⊓ centralizer ({lam * t} : Set G)) := by
  obtain ⟨ξ, hξXi, hξQ, hξfix⟩ := k18_exists_fixed_Xi hc hV
  have hξC : ξ ∈ centralizer ({lam * t} : Set G) :=
    mem_centralizer_singleton (comm_of_conj_eq_self hξfix)
  have hle : ctxQ t tau x₁ x₂ rho ⊓ centralizer ({lam * t} : Set G) ≤
      ctxXi t tau x₁ x₂ rho ⊓ centralizer ({lam * t} : Set G) :=
    inf_le_inf (l18_Q_le_Xi hc.toCtx13) le_rfl
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hle
  have hmemH1 : ξ ∈ ctxXi t tau x₁ x₂ rho ⊓ centralizer ({lam * t} : Set G) := ⟨hξXi, hξC⟩
  have hnotmemH0 : ξ ∉ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({lam * t} : Set G) :=
    fun h => hξQ h.1
  have hm_ne_zero : m ≠ 0 := by
    intro hm0
    have hpos : 0 < Nat.card ↥(ctxXi t tau x₁ x₂ rho ⊓ centralizer ({lam * t} : Set G)) :=
      Nat.card_pos
    rw [hm, hm0, mul_zero] at hpos
    exact lt_irrefl 0 hpos
  have hm_ne_one : m ≠ 1 := by
    intro hm1
    have hcard_le : Nat.card ↥(ctxXi t tau x₁ x₂ rho ⊓ centralizer ({lam * t} : Set G)) ≤
        Nat.card ↥(ctxQ t tau x₁ x₂ rho ⊓ centralizer ({lam * t} : Set G)) := by
      rw [hm, hm1, mul_one]
    have heq := Subgroup.eq_of_le_of_card_ge hle hcard_le
    exact hnotmemH0 (heq.symm ▸ hmemH1)
  have hm_ge_two : 2 ≤ m := by omega
  have hcardH0 : 8 ≤ Nat.card ↥(ctxQ t tau x₁ x₂ rho ⊓ centralizer ({lam * t} : Set G)) :=
    k18_card_CQ_u hc.toCtx13 hV
  have hmul : 8 * 2 ≤
      Nat.card ↥(ctxQ t tau x₁ x₂ rho ⊓ centralizer ({lam * t} : Set G)) * m :=
    Nat.mul_le_mul hcardH0 hm_ge_two
  have hgoal : 8 * 2 ≤
      Nat.card ↥(ctxXi t tau x₁ x₂ rho ⊓ centralizer ({lam * t} : Set G)) := by
    rw [hm]
    exact hmul
  norm_num at hgoal
  exact hgoal

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
