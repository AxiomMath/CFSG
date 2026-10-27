module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84E3UpA
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

private lemma sec8t84_isElemAbelian_of_le {G : Type*} [Group G] {E : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian 2 E) {H : Subgroup G} (hH : H ≤ E) :
    CFSG.Open.IsElemAbelian 2 H := by
  refine ⟨?_, ?_⟩
  · rw [isMulCommutative_iff]
    intro a b
    apply Subtype.ext
    simpa using isMulCommutative_iff.mp hE.1 ⟨a, hH a.2⟩ ⟨b, hH b.2⟩
  · intro x hx
    exact hE.2 x (hH hx)

theorem sec8t84_rank_up {G : Type} [Group G] [Finite G] {t : G} {S P B1 B2 : Subgroup G}
    (hS : IsSylow2Of S (centralizer ({t} : Set G))) (hPS : P ≤ S)
    (hSP : Nat.card S ≤ 2 * Nat.card P)
    (hP : ∀ B : Subgroup G, B ≤ P → CFSG.Open.IsElemAbelian 2 B → Nat.card B = 16 →
      B = B1 ∨ B = B2)
    {A : Subgroup G} (hA : A ≤ centralizer ({t} : Set G)) (hAe : CFSG.Open.IsElemAbelian 2 A) :
    Nat.card A < 2 ^ 6 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C : Subgroup G := centralizer ({t} : Set G)
  have hAC : A ≤ C := hA
  have hA2 : IsPGroup 2 A := fun x => ⟨1, Subtype.ext (by simpa using hAe.2 x x.2)⟩
  obtain ⟨P₀, hP₀⟩ := hS.exists_sylow
  have hAc2 : IsPGroup 2 (A.subgroupOf C) :=
    hA2.of_equiv (Subgroup.subgroupOfEquivOfLe hAC).symm
  obtain ⟨Q, hAQ⟩ := hAc2.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (M := ↥C) P₀ Q
  have hcQ : (Q : Subgroup ↥C) = (P₀ : Subgroup ↥C).map (MulAut.conj c).toMonoidHom := by
    rw [← hc, Sylow.coe_subgroup_smul]
    rfl
  have hconj : ∀ k ∈ A, (c : G)⁻¹ * k * ((c : G)⁻¹)⁻¹ ∈ S := by
    intro k hk
    have hkQ : (⟨k, hAC hk⟩ : ↥C) ∈
        (P₀ : Subgroup ↥C).map (MulAut.conj c).toMonoidHom := by
      rw [← hcQ]
      exact hAQ ((Subgroup.mem_subgroupOf).mpr hk)
    obtain ⟨s, hsP, hsk⟩ := Subgroup.mem_map.mp hkQ
    have h2 : (c : G) * (C.subtype s) * (c : G)⁻¹ = k := by
      have h3 := congrArg (fun x : ↥C => (x : G)) hsk
      simpa [MulAut.conj_apply, mul_assoc] using h3
    have hs_eq : C.subtype s = (c : G)⁻¹ * k * ((c : G)⁻¹)⁻¹ := by
      rw [inv_inv, ← h2]
      group
    have hmemS : C.subtype s ∈ S := by
      rw [← hP₀]
      exact Subgroup.mem_map_of_mem C.subtype hsP
    rw [← hs_eq]
    exact hmemS
  let f : G →* G := (MulAut.conj ((c : G)⁻¹)).toMonoidHom
  let A' : Subgroup G := A.map f
  have hA'S : A' ≤ S := by
    rintro _ ⟨a, ha, rfl⟩
    simpa [f, MulAut.conj_apply] using hconj a ha
  have hf : Function.Injective f := (MulAut.conj ((c : G)⁻¹)).injective
  have hcardA' : Nat.card A' = Nat.card A := Subgroup.card_map_of_injective hf
  have hA'e : CFSG.Open.IsElemAbelian 2 A' := CFSG.SectionRank.isElemAbelian_map hAe f
  have hQel : CFSG.Open.IsElemAbelian 2 (P ⊓ A') :=
    sec8t84_isElemAbelian_of_le hA'e inf_le_right
  have hcardQ : Nat.card (P ⊓ A' : Subgroup G) ≤ 16 := sec8t84_no_e32 hP inf_le_left hQel
  have hrelS_ne : P.relIndex S ≠ 0 := by
    intro h0
    have h := Subgroup.relIndex_mul_card (H := P) (K := S)
    rw [h0, zero_mul] at h
    exact Nat.card_pos.ne' h.symm
  have hcardS : Nat.card S = P.relIndex S * Nat.card P := by
    have h := Subgroup.relIndex_mul_card (H := P) (K := S)
    rw [inf_eq_left.mpr hPS] at h
    exact h.symm
  have hrelS : P.relIndex S ≤ 2 := by
    have hle : P.relIndex S * Nat.card P ≤ 2 * Nat.card P := by
      rw [← hcardS]; exact hSP
    exact le_of_mul_le_mul_right hle Nat.card_pos
  have hrelA' : P.relIndex A' ≤ 2 := by
    have h1 : P.relIndex A' ≤ P.relIndex S :=
      Subgroup.relIndex_le_of_le_right (H := P) (K := A') (L := S) hA'S hrelS_ne
    exact h1.trans hrelS
  have hinf : (P ⊓ A').relIndex A' = P.relIndex A' := Subgroup.inf_relIndex_right P A'
  have hcardA'eq : Nat.card A' = (P ⊓ A').relIndex A' * Nat.card (P ⊓ A' : Subgroup G) := by
    have h := Subgroup.relIndex_mul_card (H := P ⊓ A') (K := A')
    rw [inf_assoc, inf_idem] at h
    exact h.symm
  have hcardA'le : Nat.card A' ≤ 2 * Nat.card (P ⊓ A' : Subgroup G) := by
    rw [hcardA'eq, hinf]
    exact mul_le_mul_left hrelA' (Nat.card (P ⊓ A' : Subgroup G))
  have hA'32 : Nat.card A' ≤ 32 := by
    calc Nat.card A' ≤ 2 * Nat.card (P ⊓ A' : Subgroup G) := hcardA'le
      _ ≤ 2 * 16 := mul_le_mul_right hcardQ 2
      _ = 32 := by norm_num
  calc Nat.card A = Nat.card A' := hcardA'.symm
    _ ≤ 32 := hA'32
    _ < 2 ^ 6 := by norm_num

end CFSG.OddStandard.SmallF3.Omega
