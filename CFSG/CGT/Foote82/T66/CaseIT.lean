module

public import CFSG.CGT.Foote82.T66.CaseISq
public import CFSG.CGT.Foote82.T66.CitedCaseI
import CFSG.Quasithin.Background.A1cTransferVariants
import CFSG.CGT.Foote82.T66.Overgroup

public section

namespace CFSG.CGT.Foote82

namespace CaseIAux

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo CFSG.QuasithinUnique
open Equiv Equiv.Perm CaseIPerm CaseIHeart
open scoped commutatorElement

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {G L H₁ : Subgroup (GLV V)} {z : GLV V} {v : V} {m : ℕ}
  {ψ : ↥H₁ ≃* Equiv.Perm (Fin (m + 6 + 2))}

theorem Hyp.map_comap_alt (h : Hyp G L z v H₁ m ψ) :
    ((alternatingGroup (Fin (m + 6 + 2))).comap ψ.toMonoidHom).map H₁.subtype = HH G L v := by
  rw [h.H_eq]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨ψ y, hy, pe_psi y⟩
  · rintro ⟨σ, hσ, rfl⟩
    refine ⟨ψ.symm σ, ?_, rfl⟩
    show ψ (ψ.symm σ) ∈ alternatingGroup (Fin (m + 6 + 2))
    rw [MulEquiv.apply_symm_apply]
    exact hσ

theorem Hyp.not_conj_even (h : Hyp G L z v H₁ m ψ)
    (hK2 : ∀ Q : Subgroup (GLV V), Q ≤ KK G L → IsPGroup 2 Q → Nat.card Q ≤ 2)
    {σ : Perm (Fin (m + 6 + 2))} (hσσ : σ * σ = 1) (hsign : sign σ = 1) {c : GLV V}
    (hcG : c ∈ G) (hc : pe ψ σ = c * z * c⁻¹) : False := by
  obtain ⟨τ, rfl⟩ := exists_mul_self_eq hσσ hsign
  refine h.not_sq hK2 (w := c⁻¹ * pe ψ τ * c)
    (G.mul_mem (G.mul_mem (G.inv_mem hcG) (h.H₁_le_G (pe_mem τ))) hcG) ?_
  rw [map_mul] at hc
  calc c⁻¹ * pe ψ τ * c * (c⁻¹ * pe ψ τ * c) = c⁻¹ * (pe ψ τ * pe ψ τ) * c := by group
    _ = c⁻¹ * (c * z * c⁻¹) * c := by rw [hc]
    _ = z := by group

theorem Hyp.isSwap_of_conj (h : Hyp G L z v H₁ m ψ)
    (hK2 : ∀ Q : Subgroup (GLV V), Q ≤ KK G L → IsPGroup 2 Q → Nat.card Q ≤ 2)
    (h25 : CaseIFooteLemma25) {σ : Perm (Fin (m + 6 + 2))}
    (hc : ∃ c ∈ G, pe ψ σ = c * z * c⁻¹) : σ.IsSwap := by
  obtain ⟨c, hcG, hc⟩ := hc
  have hz2 := h.std.orderOf_s
  have hσ2 : orderOf σ = 2 := by
    rw [← orderOf_injective (pe ψ) pe_injective σ, hc,
      show c * z * c⁻¹ = (MulAut.conj c).toMonoidHom z from rfl,
      orderOf_injective _ (MulAut.conj c).injective, hz2]
  have hσσ : σ * σ = 1 := mul_self_of_orderOf_two hσ2
  rcases Int.units_eq_one_or (sign σ) with hs | hs
  · exact (h.not_conj_even hK2 hσσ hs hcG hc).elim
  ·
    obtain ⟨β, hβ⟩ := h.heartFor
    have hex : ∃ β' : ↥(commSpace (((alternatingGroup (Fin (m + 6 + 2))).comap
        ψ.toMonoidHom).map H₁.subtype) ⊤) →+ altHeart (m + 6 + 2), Function.Surjective β' ∧
        β'.ker = ((fixedSpace (((alternatingGroup (Fin (m + 6 + 2))).comap
          ψ.toMonoidHom).map H₁.subtype)).comap (commSpace (((alternatingGroup
            (Fin (m + 6 + 2))).comap ψ.toMonoidHom).map H₁.subtype) ⊤).subtype).toAddSubgroup ∧
        ∀ (x : ↥H₁) (w w' : ↥(commSpace (((alternatingGroup (Fin (m + 6 + 2))).comap
            ψ.toMonoidHom).map H₁.subtype) ⊤)),
          (w' : V) = (x : GLV V) (w : V) → ∀ y : evenWeight (m + 6 + 2),
            β' w = (y : altHeart (m + 6 + 2)) →
              β' w' = (evenWeightPerm (ψ x) y : altHeart (m + 6 + 2)) := by
      rw [h.map_comap_alt]
      exact ⟨β, hβ.surj, hβ.ker, fun x w w' hw y hy => hβ.equiv x w w' hw y hy⟩
    have hz' : ψ ⟨z, h.z_mem_H₁⟩ = swap 0 1 := h.data.ψ_z
    have ht₂ : ψ ⟨pe ψ σ, pe_mem σ⟩ = σ := psi_pe σ
    rcases h25 V H₁ (m + 6 + 2) ψ (by omega) hex ⟨z, h.z_mem_H₁⟩ ⟨pe ψ σ, pe_mem σ⟩
        (by rw [hz']; exact ⟨0, 1, ne01, rfl⟩) (by rw [ht₂]; exact hσσ) (by rw [ht₂]; exact hs)
      with h1 | h1
    · rwa [ht₂] at h1
    · exfalso
      have e : Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers (pe ψ σ)) ⊤) =
          Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers z) ⊤) := by
        rw [hc]; exact finrank_conj c z
      simp only at h1
      omega

theorem Hyp.T_max (h : Hyp G L z v H₁ m ψ)
    (hK2 : ∀ Q : Subgroup (GLV V), Q ≤ KK G L → IsPGroup 2 Q → Nat.card Q ≤ 2)
    (h25 : CaseIFooteLemma25) (T₀ : Sylow 2 (Perm (Fin (m + 6 + 2))))
    (hzT : swap 0 1 ∈ T₀) (hyT : swap 2 3 ∈ T₀) {Q : Subgroup (GLV V)} (hQG : Q ≤ G)
    (hQ2 : IsPGroup 2 Q) (hTQ : (T₀ : Subgroup (Perm (Fin (m + 6 + 2)))).map (pe ψ) ≤ Q) :
    Q = (T₀ : Subgroup (Perm (Fin (m + 6 + 2)))).map (pe ψ) :=
  h.syl_criterion T₀ hzT hyT (fun σ _ hc => h.isSwap_of_conj hK2 h25 hc) hQG hQ2 hTQ

theorem Hyp.T_le_G (h : Hyp G L z v H₁ m ψ) (T₀ : Subgroup (Perm (Fin (m + 6 + 2)))) :
    T₀.map (pe ψ) ≤ G := by
  rintro _ ⟨σ, -, rfl⟩
  exact h.H₁_le_G (pe_mem σ)

theorem Hyp.T_not_dvd (h : Hyp G L z v H₁ m ψ)
    (hK2 : ∀ Q : Subgroup (GLV V), Q ≤ KK G L → IsPGroup 2 Q → Nat.card Q ≤ 2)
    (h25 : CaseIFooteLemma25) (T₀ : Sylow 2 (Perm (Fin (m + 6 + 2))))
    (hzT : swap 0 1 ∈ T₀) (hyT : swap 2 3 ∈ T₀) :
    ¬ 2 ∣ ((T₀ : Subgroup (Perm (Fin (m + 6 + 2)))).map (pe ψ)).relIndex G := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T := (T₀ : Subgroup (Perm (Fin (m + 6 + 2)))).map (pe ψ) with hT
  have hT2 : IsPGroup 2 T := T₀.isPGroup'.map _
  have hT' : IsPGroup 2 (T.subgroupOf G) := hT2.comap_subtype
  obtain ⟨P, hP⟩ := hT'.exists_le_sylow
  have hPmap : (P : Subgroup ↥G).map G.subtype = T := by
    refine h.T_max hK2 h25 T₀ hzT hyT (Subgroup.map_subtype_le _) (P.isPGroup'.map _) ?_
    intro x hx
    exact ⟨⟨x, h.T_le_G _ hx⟩, hP (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  have hPeq : (P : Subgroup ↥G) = T.subgroupOf G := by
    rw [← hPmap]
    exact (Subgroup.comap_map_eq_self_of_injective G.subtype_injective _).symm
  rw [Subgroup.relIndex, ← hPeq]
  exact P.not_dvd_index

theorem relIndex_alt (T₀ : Subgroup (Perm (Fin (m + 6 + 2)))) (hzT : swap 0 1 ∈ T₀) :
    ((T₀ ⊓ alternatingGroup (Fin (m + 6 + 2))).map (pe ψ)).relIndex (T₀.map (pe ψ)) = 2 := by
  rw [Subgroup.relIndex_map_map_of_injective _ _ pe_injective]
  set f : ↥T₀ →* ℤˣ := Equiv.Perm.sign.comp T₀.subtype with hf
  have hker : f.ker = (T₀ ⊓ alternatingGroup (Fin (m + 6 + 2))).subgroupOf T₀ := by
    ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf, hf,
      MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      Equiv.Perm.mem_alternatingGroup]
    exact ⟨fun h1 => ⟨x.2, h1⟩, fun h1 => h1.2⟩
  have hsurj : Function.Surjective f := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, map_one f⟩
    · exact ⟨⟨swap 0 1, hzT⟩, by simp [hf, sign_swap ne01]⟩
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker, MonoidHom.range_eq_top.2 hsurj,
    Subgroup.card_top, Nat.card_eq_fintype_card]
  rfl

theorem Hyp.exists_N₂ (h : Hyp G L z v H₁ m ψ)
    (hK2 : ∀ Q : Subgroup (GLV V), Q ≤ KK G L → IsPGroup 2 Q → Nat.card Q ≤ 2)
    (h25 : CaseIFooteLemma25) :
    ∃ N₂ : Subgroup (GLV V), N₂ ≤ G ∧ (N₂.subgroupOf G).Normal ∧ (∀ x ∈ G, x ^ 2 ∈ N₂) ∧
      z ∉ N₂ := by
  obtain ⟨T₀, hzT, hyT⟩ := exists_sylow_T₀ (m := m)
  set T := (T₀ : Subgroup (Perm (Fin (m + 6 + 2)))).map (pe ψ) with hT
  set T₁ := ((T₀ : Subgroup (Perm (Fin (m + 6 + 2)))) ⊓
    alternatingGroup (Fin (m + 6 + 2))).map (pe ψ) with hT₁
  have hT₁T : T₁ ≤ T := Subgroup.map_mono inf_le_left
  refine CFSG.Quasithin.thompson_transfer_exists_normal_subgroup (h.T_le_G _) (T₀.isPGroup'.map _)
    (h.T_not_dvd hK2 h25 T₀ hzT hyT) hT₁T (relIndex_alt _ hzT) h.z_mem_G h.std.orderOf_s ?_
  rintro x hxG ⟨σ, ⟨-, hσA⟩, hσ⟩
  have hσ2 : orderOf σ = 2 := by
    rw [← orderOf_injective (pe ψ) pe_injective σ, hσ,
      show x⁻¹ * z * x = (MulAut.conj x⁻¹).toMonoidHom z by simp [MulAut.conj_apply],
      orderOf_injective _ (MulAut.conj x⁻¹).injective, h.std.orderOf_s]
  exact h.not_conj_even hK2 (mul_self_of_orderOf_two hσ2) hσA (G.inv_mem hxG)
    (by rw [hσ, inv_inv])

theorem commutator_le_of_sq {G N₂ : Subgroup (GLV V)} (hN₂G : N₂ ≤ G)
    (hN : (N₂.subgroupOf G).Normal) (hsq : ∀ x ∈ G, x ^ 2 ∈ N₂) : ⁅G, G⁆ ≤ N₂ := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have hconj : ∀ g ∈ G, ∀ n ∈ N₂, g * n * g⁻¹ ∈ N₂ := by
    intro g hg n hn
    have := hN.conj_mem ⟨n, hN₂G hn⟩ (Subgroup.mem_subgroupOf.2 hn) ⟨g, hg⟩
    exact Subgroup.mem_subgroupOf.1 this
  have e : ⁅a, b⁆ = (a * b) ^ 2 * (b⁻¹ * (a⁻¹) ^ 2 * b) * (b⁻¹) ^ 2 := by
    rw [commutatorElement_def, sq, sq, sq]; group
  rw [e]
  refine N₂.mul_mem (N₂.mul_mem (hsq _ (G.mul_mem ha hb)) ?_) (hsq _ (G.inv_mem hb))
  have := hconj b⁻¹ (G.inv_mem hb) _ (hsq _ (G.inv_mem ha))
  rwa [inv_inv] at this

theorem layerIn_le_of_sq {G N₂ : Subgroup (GLV V)} (hN₂G : N₂ ≤ G)
    (hN : (N₂.subgroupOf G).Normal) (hsq : ∀ x ∈ G, x ^ 2 ∈ N₂) : layerIn G ≤ N₂ := by
  rw [layerIn_eq_sSup]
  refine sSup_le fun Q hQ => ?_
  have hQG : Q ≤ G := hQ.1
  rw [← commutator_eq_self_of_isQuasisimple hQ.2.2]
  exact (Subgroup.commutator_mono hQG hQG).trans (commutator_le_of_sq hN₂G hN hsq)

theorem Hyp.z_not_mem_layerIn (h : Hyp G L z v H₁ m ψ)
    (hK2 : ∀ Q : Subgroup (GLV V), Q ≤ KK G L → IsPGroup 2 Q → Nat.card Q ≤ 2)
    (h25 : CaseIFooteLemma25) : z ∉ layerIn G := by
  obtain ⟨N₂, hN₂G, hN, hsq, hz⟩ := h.exists_N₂ hK2 h25
  exact fun hzE => hz (layerIn_le_of_sq hN₂G hN hsq hzE)

theorem Hyp.H_le_layerIn (h : Hyp G L z v H₁ m ψ) : HH G L v ≤ layerIn G :=
  h.std.extremal.setup.le_layerIn_of_perfect h.H_le_G
    (commutator_eq_self_of_isQuasisimple h.H_isComponentOf.2.2)

end CaseIAux

end CFSG.CGT.Foote82
