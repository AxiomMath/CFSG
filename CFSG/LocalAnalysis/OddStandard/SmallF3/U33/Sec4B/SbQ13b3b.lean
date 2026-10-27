module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13b1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13b2a

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private lemma fourGrp_le_closure_insert (a b c : G) :
    fourGrp a b ≤ Subgroup.closure ({a ^ 2, (a * b) ^ 2, c} : Set G) := by
  rw [fourGrp]
  refine Subgroup.closure_mono ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  tauto

theorem q13b_E8_V_le_of_le_cent (h : Q13Om t L S x₁ x₂ lam rho tau om) {𝒮 F : Subgroup G}
    (h𝒮 : IsPGroup 2 𝒮) (hU : ctxU t tau x₁ x₂ lam ≤ 𝒮) (hF : NormalIn F 𝒮)
    (hFe : CFSG.Open.IsElemAbelian 2 F) (hFc : Nat.card F = 8)
    (hFt : F ≤ centralizer ({t} : Set G)) :
    fourGrp x₁ x₂ ≤ F ∧ F ≤ ctxU t tau x₁ x₂ lam := by
  have hFS_le : F ≤ S := by
    have hle : F ≤ 𝒮 ⊓ centralizer ({t} : Set G) := le_inf hF.1 hFt
    rwa [q13b_cent_t h h𝒮 hU] at hle
  refine ⟨?_, hFS_le.trans h.c11.S_le_U⟩
  have hFS : NormalIn F S :=
    ⟨hFS_le, fun g hg k hk => hF.2 g (hU (h.c11.S_le_U hg)) k hk⟩
  rcases h.c11.l46 F hFS hFe hFc with hV | hV | hV | hV | hV
  · rw [hV]; exact fourGrp_le_closure_insert x₁ x₂ t
  · rw [hV]; exact fourGrp_le_closure_insert x₁ x₂ tau
  · rw [hV]; exact fourGrp_le_closure_insert x₁ x₂ (t * tau)
  · rw [hV]; exact fourGrp_le_closure_insert x₁ x₂ (tau * (x₁ * x₂))
  · rw [hV]; exact fourGrp_le_closure_insert x₁ x₂ (t * tau * (x₁ * x₂))

theorem q13b_E8_cent_four (h : Q13Om t L S x₁ x₂ lam rho tau om) {𝒮 F : Subgroup G}
    (h𝒮 : IsPGroup 2 𝒮) (hU : ctxU t tau x₁ x₂ lam ≤ 𝒮) (hF : NormalIn F 𝒮)
    (hFe : CFSG.Open.IsElemAbelian 2 F) (hFc : Nat.card F = 8)
    (h4 : Nat.card ↥(F ⊓ centralizer ({t} : Set G)) = 4) :
    F ⊓ centralizer ({t} : Set G) = fourGrp x₁ x₂ := by
  let D : Subgroup G := F ⊓ centralizer ({t} : Set G)
  have hS_cent : S ≤ centralizer ({t} : Set G) := by
    rw [← q13b_cent_t h h𝒮 hU]
    exact inf_le_right
  have hDS_le : D ≤ S := by
    have hle : D ≤ 𝒮 ⊓ centralizer ({t} : Set G) :=
      le_inf (inf_le_left.trans hF.1) inf_le_right
    rwa [q13b_cent_t h h𝒮 hU] at hle
  have hDS : NormalIn D S := by
    refine ⟨hDS_le, fun g hg k hk => ?_⟩
    exact Subgroup.mem_inf.mpr
      ⟨hF.2 g (hU (h.c11.S_le_U hg)) k hk.1,
       (centralizer ({t} : Set G)).mul_mem
         ((centralizer ({t} : Set G)).mul_mem (hS_cent hg) hk.2)
         ((centralizer ({t} : Set G)).inv_mem (hS_cent hg))⟩
  have hDe : CFSG.Open.IsElemAbelian 2 D := hFe.mono inf_le_left
  have h4' : Nat.card D = 4 := h4
  have hRcard : (Nat.card F - 1) * 2 ^ 7 < Nat.card 𝒮 := by
    rw [hFc]
    have hbound : (8 - 1) * 2 ^ 7 < 2 ^ 10 := by norm_num
    refine lt_of_lt_of_le hbound ?_
    rw [← q13b_card_U h]
    exact Subgroup.card_le_of_le hU
  have hnoconj : ∀ g : G, ∀ v ∈ D, g * t * g⁻¹ ≠ v := by
    intro g v hv heq
    exact q13b_tG_not_mem_normal h.c11.toCtx10 (R := 𝒮) (A := F) h𝒮 hRcard hF g
      (by rw [heq]; exact hv.1)
  change D = fourGrp x₁ x₂
  exact (h.c11.l45 D hDS hDe h4' hnoconj).1

theorem q13b_le_N_S (h : Q13Om t L S x₁ x₂ lam rho tau om) {𝒮 F : Subgroup G}
    (h𝒮 : IsPGroup 2 𝒮) (hU : ctxU t tau x₁ x₂ lam ≤ 𝒮) (hF : NormalIn F 𝒮)
    (hFe : CFSG.Open.IsElemAbelian 2 F) (hFc : Nat.card F = 8)
    (hV : F ⊓ centralizer ({t} : Set G) = fourGrp x₁ x₂) :
    F ≤ normalizer (S : Set G) ⊓ 𝒮 := by
  have hS_cent : S ≤ centralizer ({t} : Set G) := by
    rw [← q13b_cent_t h h𝒮 hU]
    exact inf_le_right
  have hDS_le : F ⊓ centralizer ({t} : Set G) ≤ S := by
    have hle : F ⊓ centralizer ({t} : Set G) ≤ 𝒮 ⊓ centralizer ({t} : Set G) :=
      le_inf (inf_le_left.trans hF.1) inf_le_right
    rwa [q13b_cent_t h h𝒮 hU] at hle
  have hfourF : fourGrp x₁ x₂ ≤ F := by rw [← hV]; exact inf_le_left
  have hfourC : fourGrp x₁ x₂ ≤ centralizer ({t} : Set G) := by
    rw [← hV]; exact inf_le_right
  have hfourS : fourGrp x₁ x₂ ≤ S := by rw [← hV]; exact hDS_le
  have hcard : Nat.card F = 2 * Nat.card (fourGrp x₁ x₂) := by
    simp [hFc, (h.c11.wreath.fourGrp_eq_omega).2.2]
  intro f hf
  refine ⟨?_, hF.1 hf⟩
  refine Subgroup.mem_normalizer_fintype (fun n hn => ?_)
  have hn𝒮 : n ∈ 𝒮 := hU (h.c11.S_le_U hn)
  have hcomm := q13b_comm_mem_of_index_two (F := F) (F₀ := fourGrp x₁ x₂)
    hfourF hcard (g := n)
    (fun x hx => hF.2 n hn𝒮 x hx)
    (fun x hx => by
      rw [← hV]
      exact Subgroup.mem_inf.mpr
        ⟨hF.2 n hn𝒮 x (hfourF hx),
         (centralizer ({t} : Set G)).mul_mem
           ((centralizer ({t} : Set G)).mul_mem (hS_cent hn) (hfourC hx))
           ((centralizer ({t} : Set G)).inv_mem (hS_cent hn))⟩)
    (fun x hx => by
      rw [← hV]
      exact Subgroup.mem_inf.mpr
        ⟨by simpa only [inv_inv] using
            hF.2 n⁻¹ (hU (h.c11.S_le_U (S.inv_mem hn))) x (hfourF hx),
         (centralizer ({t} : Set G)).mul_mem
           ((centralizer ({t} : Set G)).mul_mem (hS_cent (S.inv_mem hn)) (hfourC hx))
           (hS_cent hn)⟩)
    f hf
  have heq : f * n * f⁻¹ = (n * f * n⁻¹ * f⁻¹)⁻¹ * n := by group
  rw [heq]
  exact S.mul_mem (S.inv_mem (hfourS hcomm)) hn

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
