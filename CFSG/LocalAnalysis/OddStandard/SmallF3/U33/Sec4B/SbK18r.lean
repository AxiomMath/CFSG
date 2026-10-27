module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18Nrm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18n
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18i

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

private lemma k18r_conj_mem_centralizer {A : Subgroup G} {g k : G}
    (hg : g ∈ normalizer (A : Set G)) (hk : k ∈ centralizer (A : Set G)) :
    g * k * g⁻¹ ∈ centralizer (A : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hk ⊢
  intro y hy
  have hgy : g⁻¹ * y * g ∈ A := by
    have hginv : g⁻¹ ∈ normalizer (A : Set G) := (normalizer (A : Set G)).inv_mem hg
    simpa using (Subgroup.mem_normalizer_iff.mp hginv y).mp hy
  calc y * (g * k * g⁻¹) = g * ((g⁻¹ * y * g) * k) * g⁻¹ := by group
    _ = g * (k * (g⁻¹ * y * g)) * g⁻¹ := by rw [hk (g⁻¹ * y * g) hgy]
    _ = (g * k * g⁻¹) * y := by group

theorem k18_sylowV_of_Fu (hc : Ctx18A t L S x₁ x₂ lam rho tau om 𝒮)
    (hFu : ∀ {g e : G}, e ∈ ctxOK t tau x₁ x₂ rho → g * t * g⁻¹ = e * (lam * t) →
      ∃ o ∈ ctxOK t tau x₁ x₂ rho, e * (lam * t) = o * (lam * t) * o⁻¹) :
    IsSylowIn 2 (ctxOK t tau x₁ x₂ rho)
      (centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G)) := by
  have hc13 : Ctx13 t L S x₁ x₂ lam rho tau om := hc.toCtx13
  have hc18S : Ctx18S t L S x₁ x₂ lam rho tau om 𝒮 := hc.toCtx18S
  have hc18 : Ctx18 t L S x₁ x₂ lam rho tau om 𝒮 := hc.toCtx18
  obtain ⟨V', v₁, v₂, hV⟩ := hc13.data_V
  have h𝒮V : ∀ k ∈ 𝒮, ∀ v ∈ fourGrp x₁ x₂, k * v * k⁻¹ ∈ fourGrp x₁ x₂ :=
    (k18_sylow_normalizes hc18S).1
  have h𝒮norm : 𝒮 ≤ normalizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) :=
    fun k hk => mem_normalizer_of_conj_le (h𝒮V k hk)
  have h𝒮2 : IsPGroup 2 𝒮 := hc.sylow.2.1
  obtain ⟨ℰ, hℰ, h𝒮ℰ⟩ := exists_isSylowIn_of_le h𝒮norm h𝒮2
  have hℰ2 : IsPGroup 2 ℰ := hℰ.2.1
  have hT : IsSylowIn 2 (ℰ ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G))
      (centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G)) :=
    isSylowIn_inf_centralizer_of_normalizer hℰ
  have hOcent : ctxOK t tau x₁ x₂ rho ≤
      centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
    intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h := k18_OK_cent_V hc13 n hn v hv
    calc v * n = (n * v * n⁻¹) * n := by rw [h]
      _ = n * v := by group
  have hOKT : ctxOK t tau x₁ x₂ rho ≤
      ℰ ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) :=
    le_inf ((l18_OK_le_sylow hc18S).trans h𝒮ℰ) hOcent
  have hTle : ℰ ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) ≤
      ctxOK t tau x₁ x₂ rho := by
    by_contra hle
    have hlt : ctxOK t tau x₁ x₂ rho <
        ℰ ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) :=
      lt_of_le_of_ne hOKT (fun h => hle (le_of_eq h.symm))
    have hT2 : IsPGroup 2
        (ℰ ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) : Subgroup G) :=
      hℰ2.to_le inf_le_left
    have huS : lam * t ∈ 𝒮 :=
      𝒮.mul_mem (l18_T_le_sylow hc18S).2.2.2 (l18_T_le_sylow hc18S).1
    have hu2 : (lam * t) * (lam * t) = 1 := k18_u_sq hc13
    have huNorm : (lam * t) ∈ normalizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) :=
      mem_normalizer_of_conj_le (h𝒮V (lam * t) huS)
    have huT : ∀ n ∈ ℰ ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G),
        (lam * t) * n * (lam * t)⁻¹ ∈
          ℰ ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
      intro n hn
      exact ⟨ℰ.mul_mem (ℰ.mul_mem (h𝒮ℰ huS) hn.1) (ℰ.inv_mem (h𝒮ℰ huS)),
        k18r_conj_mem_centralizer huNorm hn.2⟩
    have huK : lam * t ∈ ctxK t tau x₁ x₂ rho := k18_u_mem_K hc13
    have huOK : ∀ e ∈ ctxOK t tau x₁ x₂ rho,
        (lam * t) * e * (lam * t)⁻¹ ∈ ctxOK t tau x₁ x₂ rho :=
      fun e he => (l18_OK_normal).2 (lam * t) huK e he
    obtain ⟨n, hnT, hnOKne, he⟩ := exists_fixed_coset hT2 hlt hu2 huT huOK
    have heOK : n⁻¹ * ((lam * t) * n * (lam * t)⁻¹) ∈ ctxOK t tau x₁ x₂ rho := he
    obtain ⟨h, hh⟩ := l17_tlam_conj hc13
    have hh' : h * t * h⁻¹ = lam * t := by rw [hh, (l17_lam_comm hc13).1]
    have hg : (n⁻¹ * h) * t * (n⁻¹ * h)⁻¹ =
        (n⁻¹ * ((lam * t) * n * (lam * t)⁻¹)) * (lam * t) := by
      rw [show (n⁻¹ * h) * t * (n⁻¹ * h)⁻¹ = n⁻¹ * (h * t * h⁻¹) * n by group, hh']
      group
    obtain ⟨o, hoOK, hoo⟩ := hFu heOK hg
    have hnu : n⁻¹ * (lam * t) * n = o * (lam * t) * o⁻¹ :=
      calc n⁻¹ * (lam * t) * n =
            (n⁻¹ * ((lam * t) * n * (lam * t)⁻¹)) * (lam * t) := by group
        _ = o * (lam * t) * o⁻¹ := hoo
    have hcomm : (n * o) * (lam * t) = (lam * t) * (n * o) := by
      calc (n * o) * (lam * t) = n * (o * (lam * t)) := by group
        _ = n * (o * (lam * t) * o⁻¹ * o) := by group
        _ = n * ((o * (lam * t) * o⁻¹) * o) := by group
        _ = n * ((n⁻¹ * (lam * t) * n) * o) := by rw [hnu]
        _ = (lam * t) * (n * o) := by group
    have hxcent : n * o ∈ centralizer ({lam * t} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcomm
    have hxℰ : n * o ∈ ℰ := ℰ.mul_mem hnT.1 (h𝒮ℰ ((l18_OK_le_sylow hc18S) hoOK))
    have hxC : n * o ∈ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) :=
      Subgroup.mul_mem _ hnT.2 (hOcent hoOK)
    have hD1 : 2 ^ 7 ≤ Nat.card ↥(𝒮 ⊓ centralizer ({lam * t} : Set G)) :=
      k18_card_Csylow_u hc18 hV
    have hD2 : Nat.card ↥(ℰ ⊓ centralizer ({lam * t} : Set G)) ≤ 2 ^ 7 :=
      card_le_of_le_centralizer_conj (S := S)
        (P := ℰ ⊓ centralizer ({lam * t} : Set G))
        ⟨hc.le_invCent, hc.isPGroup, hc.relIndex_odd⟩ (Ctx4.card_S_seven hc.toCtx4)
        hh' (hℰ2.to_le inf_le_left) inf_le_right
    have hD12 : 𝒮 ⊓ centralizer ({lam * t} : Set G) ≤
        ℰ ⊓ centralizer ({lam * t} : Set G) :=
      inf_le_inf_right _ h𝒮ℰ
    have hDeq : 𝒮 ⊓ centralizer ({lam * t} : Set G) =
        ℰ ⊓ centralizer ({lam * t} : Set G) :=
      Subgroup.eq_of_le_of_card_ge hD12 (le_trans hD2 hD1)
    have hxS : n * o ∈ 𝒮 := by
      have hx : n * o ∈ ℰ ⊓ centralizer ({lam * t} : Set G) := ⟨hxℰ, hxcent⟩
      rw [← hDeq] at hx
      exact hx.1
    have hxOK : n * o ∈ ctxOK t tau x₁ x₂ rho := by
      have hmem : n * o ∈ 𝒮 ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) :=
        ⟨hxS, hxC⟩
      rwa [k18_cent_V_eq hc18S] at hmem
    have hnOK : n ∈ ctxOK t tau x₁ x₂ rho := by
      have : n = (n * o) * o⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ hxOK (Subgroup.inv_mem _ hoOK)
    exact hnOKne hnOK
  have hTOK : ℰ ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) =
      ctxOK t tau x₁ x₂ rho := le_antisymm hTle hOKT
  rwa [← hTOK]

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
