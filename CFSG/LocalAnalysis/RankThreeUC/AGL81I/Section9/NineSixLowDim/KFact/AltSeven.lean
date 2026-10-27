module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.KFact.Gen
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact

open Equiv Equiv.Perm

private abbrev t₁ : Perm (Fin 7) := swap 0 1 * swap 1 2

private abbrev t₂ : Perm (Fin 7) := swap 3 4 * swap 4 5

private abbrev i₁ : Perm (Fin 7) := swap 3 4 * swap 5 6

private abbrev i₂ : Perm (Fin 7) := swap 3 5 * swap 4 6

private abbrev i₃ : Perm (Fin 7) := swap 0 1 * swap 2 6

private abbrev i₄ : Perm (Fin 7) := swap 0 2 * swap 1 6

private theorem swap_mul_swap_mem {a b c d : Fin 7} (hab : a ≠ b) (hcd : c ≠ d) :
    swap a b * swap c d ∈ alternatingGroup (Fin 7) := by
  rw [mem_alternatingGroup, Perm.sign_mul, sign_swap hab, sign_swap hcd]
  rfl

private theorem eq_top_of_mem_involutions (H : Subgroup (alternatingGroup (Fin 7)))
    (h₁ : ⟨i₁, swap_mul_swap_mem (by decide) (by decide)⟩ ∈ H)
    (h₂ : ⟨i₂, swap_mul_swap_mem (by decide) (by decide)⟩ ∈ H)
    (h₃ : ⟨i₃, swap_mul_swap_mem (by decide) (by decide)⟩ ∈ H)
    (h₄ : ⟨i₄, swap_mul_swap_mem (by decide) (by decide)⟩ ∈ H) : H = ⊤ := by
  set K := H.map (alternatingGroup (Fin 7)).subtype
  have m₁ : i₁ ∈ K := ⟨_, h₁, rfl⟩
  have m₂ : i₂ ∈ K := ⟨_, h₂, rfl⟩
  have m₃ : i₃ ∈ K := ⟨_, h₃, rfl⟩
  have m₄ : i₄ ∈ K := ⟨_, h₄, rfl⟩
  have htr : MulAction.IsPretransitive K (Fin 7) := by
    rw [MulAction.isPretransitive_iff_base 0]
    intro x
    have hw : ∀ g ∈ K, g 0 = x → ∃ k : K, k • (0 : Fin 7) = x := fun g hg h => ⟨⟨g, hg⟩, h⟩
    fin_cases x
    · exact hw 1 K.one_mem rfl
    · exact hw _ m₃ (by decide)
    · exact hw _ m₄ (by decide)
    · exact hw _ (K.mul_mem m₁ (K.mul_mem m₂ (K.mul_mem m₃ m₄))) (by decide)
    · exact hw _ (K.mul_mem m₂ (K.mul_mem m₃ m₄)) (by decide)
    · exact hw _ (K.mul_mem m₁ (K.mul_mem m₃ m₄)) (by decide)
    · exact hw _ (K.mul_mem m₃ m₄) (by decide)
  have hprim : MulAction.IsPreprimitive K (Fin 7) :=
    MulAction.IsPreprimitive.of_prime_card (by simp; norm_num)
  have h3 : (i₁ * i₃) ^ 2 = swap 2 5 * swap 2 6 := by decide
  have hle := alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim
    (isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide))
    (h3 ▸ K.pow_mem (K.mul_mem m₁ m₃) 2)
  refine eq_top_iff.mpr fun g _ => ?_
  obtain ⟨h, hh, he⟩ := hle g.2
  exact (Subtype.ext he : h = g) ▸ hh

private theorem not_three_dvd_orderOf {i : Perm (Fin 7)} (hi : i ∈ alternatingGroup (Fin 7))
    (h2 : i ^ 2 = 1) (h1 : i ≠ 1) : ¬ 3 ∣ orderOf (⟨i, hi⟩ : alternatingGroup (Fin 7)) := by
  rw [Subgroup.orderOf_mk, orderOf_eq_prime h2 h1]
  norm_num

private theorem mem_fixPPrime {E : Subgroup (MulAut (alternatingGroup (Fin 7)))}
    {t i : Perm (Fin 7)} (hi : i ∈ alternatingGroup (Fin 7)) (h2 : i ^ 2 = 1) (h1 : i ≠ 1)
    (ht : t ≠ 1) (hti : t * i * t⁻¹ = i)
    (hE : MulAut.conjNormal (H := alternatingGroup (Fin 7)) t ∈ E) :
    (⟨i, hi⟩ : alternatingGroup (Fin 7)) ∈ fixPPrime 3 E := by
  refine ⟨not_three_dvd_orderOf hi h2 h1, _, hE, fun h => ht ?_, Subtype.ext ?_⟩
  · exact GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 7 (by norm_num)
      (h.trans (map_one _).symm)
  · rw [MulAut.conjNormal_apply]
    exact hti

private theorem closure_fixPPrime_eq_top (Q : Subgroup (Perm (Fin 7))) (h₁ : t₁ ∈ Q)
    (h₂ : t₂ ∈ Q) :
    Subgroup.closure (fixPPrime 3
      (Q.map (MulAut.conjNormal (H := alternatingGroup (Fin 7))))) = ⊤ := by
  have e₁ := Subgroup.mem_map_of_mem (MulAut.conjNormal (H := alternatingGroup (Fin 7))) h₁
  have e₂ := Subgroup.mem_map_of_mem (MulAut.conjNormal (H := alternatingGroup (Fin 7))) h₂
  apply eq_top_of_mem_involutions <;> apply Subgroup.subset_closure
  · exact mem_fixPPrime _ (by decide) (by decide) (by decide) (by decide) e₁
  · exact mem_fixPPrime _ (by decide) (by decide) (by decide) (by decide) e₁
  · exact mem_fixPPrime _ (by decide) (by decide) (by decide) (by decide) e₂
  · exact mem_fixPPrime _ (by decide) (by decide) (by decide) (by decide) e₂

private theorem isPGroup_zpowers {t : Perm (Fin 7)} (h3 : t ^ 3 = 1) (h1 : t ≠ 1) :
    IsPGroup 3 (Subgroup.zpowers t) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime h3 h1, pow_one])

private theorem exists_sylow_mem :
    ∃ Q : Sylow 3 (Perm (Fin 7)), t₁ ∈ Q ∧ t₂ ∈ Q := by
  have hc : Commute t₂ t₁ := (by decide : t₂ * t₁ = t₁ * t₂)
  have hn : Subgroup.zpowers t₁ ≤
      Subgroup.normalizer (Subgroup.zpowers t₂ : Set (Perm (Fin 7))) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, rfl⟩
    exact (hc.zpow_left k).eq
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨Q, hQ⟩ := ((isPGroup_zpowers (t := t₁) (by decide) (by decide)).to_sup_of_normal_right'
    (isPGroup_zpowers (t := t₂) (by decide) (by decide)) hn).exists_le_sylow
  exact ⟨Q, hQ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)),
    hQ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))⟩

theorem pPrimeGenAt_three_alt_seven : PPrimeGenAt 3 (alternatingGroup (Fin 7)) := by
  intro E _ hcard
  set c : Perm (Fin 7) →* MulAut (alternatingGroup (Fin 7)) := MulAut.conjNormal
  have hc : Function.Bijective c :=
    GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num) (by norm_num)
  have hEF : (E.comap c).map c = E := Subgroup.map_comap_eq_self_of_surjective hc.2 E
  have hF : Nat.card (E.comap c) = 3 ^ 2 := by
    rw [← hcard, ← hEF, Subgroup.card_map_of_injective hc.1, hEF]
  have hidx : (E.comap c).index = 560 := by
    have h := (E.comap c).card_mul_index
    rw [hF, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at h
    simp [Nat.factorial] at h
    omega
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨Q, hQ₁, hQ₂⟩ := exists_sylow_mem
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Perm (Fin 7)) Q
    ((IsPGroup.of_card hF).toSylow (by rw [hidx]; norm_num))
  have hFQ : E.comap c = (Q : Subgroup (Perm (Fin 7))).map (MulAut.conj g).toMonoidHom := by
    rw [← IsPGroup.toSylow_coe (IsPGroup.of_card hF) (by rw [hidx]; norm_num), ← hg]
    rfl
  have key : E = ((Q : Subgroup (Perm (Fin 7))).map c).map (MulAut.conj (c g)).toMonoidHom := by
    rw [← hEF, hFQ, Subgroup.map_map, Subgroup.map_map]
    congr 1
  rw [key, closure_fixPPrime_map_conj, closure_fixPPrime_eq_top Q hQ₁ hQ₂]
  exact Subgroup.map_top_of_surjective _ (c g).surjective

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact
