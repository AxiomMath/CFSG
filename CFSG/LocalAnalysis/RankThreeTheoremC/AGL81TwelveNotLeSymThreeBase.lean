module

public import Mathlib.GroupTheory.IsSubnormal
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSG.ClassicalInvolution.Q3.TwinLemmaBasic
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.SymThree

open Equiv

theorem pCore_eq_bot_of_mulEquiv {G G' : Type*} [Group G] [Group G'] (p : ℕ) (e : G ≃* G')
    (h : CFSG.pCore p G' = ⊥) : CFSG.pCore p G = ⊥ := by
  have h1 := CFSG.pCore_map_iso p e
  rw [h] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 h1

theorem eq_bot_of_isSubnormal_isPGroup {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (h : CFSG.pCore p H = ⊥) {N : Subgroup H} (hN : N.IsSubnormal) (hp : IsPGroup p N) :
    N = ⊥ := by
  have h1 := CFSG.ClassicalInvolution.Q3.Twin.le_pCore_of_isSubnormal hN hp
  rw [h] at h1
  exact le_bot_iff.1 h1

theorem card_perm_fin_three : Nat.card (Perm (Fin 3)) = 6 := by
  rw [Nat.card_perm, Nat.card_fin]
  rfl

theorem card_eq_six_of_mulEquiv {X : Type*} [Group X] (e : X ≃* Perm (Fin 3)) :
    Nat.card X = 6 :=
  (Nat.card_congr e.toEquiv).trans card_perm_fin_three

theorem card_alternatingGroup_fin_three : Nat.card (alternatingGroup (Fin 3)) = 3 := by
  have h := two_mul_nat_card_alternatingGroup (α := Fin 3)
  rw [card_perm_fin_three] at h
  omega

theorem exists_isSubnormal_card_three {Q : Type*} [Group Q] {X : Subgroup Q}
    (hX : X.IsSubnormal) (e : X ≃* Perm (Fin 3)) :
    ∃ T : Subgroup Q, T.IsSubnormal ∧ Nat.card T = 3 := by
  have hA : (alternatingGroup (Fin 3)).Normal := inferInstance
  let TX : Subgroup X := (alternatingGroup (Fin 3)).map e.symm.toMonoidHom
  have hTX : TX.Normal := hA.map e.symm.toMonoidHom e.symm.surjective
  refine ⟨TX.map X.subtype, hTX.isSubnormal.trans' hX, ?_⟩
  rw [Subgroup.card_map_of_injective X.subtype_injective,
    Subgroup.card_map_of_injective e.symm.injective, card_alternatingGroup_fin_three]

theorem false_of_isSubnormal_symThree {H : Type*} [Group H] [Finite H]
    (h3 : CFSG.pCore 3 H = ⊥) {X : Subgroup H} (hX : X.IsSubnormal) (e : X ≃* Perm (Fin 3)) :
    False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T, hTs, hT3⟩ := exists_isSubnormal_card_three hX e
  have hTp : IsPGroup 3 T := IsPGroup.of_card (n := 1) (by rw [hT3]; norm_num)
  have hT : T = ⊥ := eq_bot_of_isSubnormal_isPGroup h3 hTs hTp
  rw [hT, Subgroup.card_bot] at hT3
  omega

theorem range_eq_bot_of_isSubnormal {H : Type*} [Group H] [Finite H]
    (h2 : CFSG.pCore 2 H = ⊥) (h3 : CFSG.pCore 3 H = ⊥) (ψ : Perm (Fin 3) →* H)
    (hψ : ψ.range.IsSubnormal) : ψ.range = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : Nat.card ψ.range ∣ 6 := by
    have h := Subgroup.card_range_dvd ψ
    rwa [card_perm_fin_three] at h
  have hpos : 0 < Nat.card ψ.range := Nat.card_pos
  have hle : Nat.card ψ.range ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
  have hker := Subgroup.card_ker_mul_card_range ψ
  rw [card_perm_fin_three] at hker
  have hcases : Nat.card ψ.range = 1 ∨ Nat.card ψ.range = 2 ∨ Nat.card ψ.range = 3 ∨
      Nat.card ψ.range = 6 := by
    have h4 : Nat.card ψ.range ≠ 4 := by
      intro h
      rw [h] at hdvd
      norm_num at hdvd
    have h5 : Nat.card ψ.range ≠ 5 := by
      intro h
      rw [h] at hdvd
      norm_num at hdvd
    omega
  rcases hcases with hc | hc | hc | hc
  · exact Subgroup.eq_bot_of_card_eq _ hc
  · exact eq_bot_of_isSubnormal_isPGroup h2 hψ (IsPGroup.of_card (n := 1) (by rw [hc]; norm_num))
  · exact eq_bot_of_isSubnormal_isPGroup h3 hψ (IsPGroup.of_card (n := 1) (by rw [hc]; norm_num))
  · have hkerone : Nat.card ψ.ker = 1 := by
      rw [hc] at hker
      omega
    have hinj : Function.Injective ψ :=
      (MonoidHom.ker_eq_bot_iff ψ).1 (Subgroup.eq_bot_of_card_eq _ hkerone)
    exact (false_of_isSubnormal_symThree h3 hψ (MonoidHom.ofInjective hinj).symm).elim

theorem eq_top_of_card_le_six {Q : Type*} [Group Q] [Finite Q] (hQ : Nat.card Q ≤ 6)
    {X : Subgroup Q} (eX : X ≃* Perm (Fin 3)) : X = ⊤ := by
  have h6 := card_eq_six_of_mulEquiv eX
  refine Subgroup.eq_top_of_card_eq X (le_antisymm (Subgroup.card_le_card_group X) ?_)
  omega

theorem eq_of_card_le_six {Q : Type*} [Group Q] [Finite Q] (hQ : Nat.card Q ≤ 6)
    {X W : Subgroup Q} (eX : X ≃* Perm (Fin 3)) (eW : W ≃* Perm (Fin 3)) : X = W :=
  (eq_top_of_card_le_six hQ eX).trans (eq_top_of_card_le_six hQ eW).symm

@[expose] def kleinFourFinset : Finset (Perm (Fin 4)) :=
  {1, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 3 * swap 1 2}

theorem kleinFourFinset_mul :
    ∀ a ∈ kleinFourFinset, ∀ b ∈ kleinFourFinset, a * b ∈ kleinFourFinset := by
  unfold kleinFourFinset
  decide +kernel

theorem kleinFourFinset_inv : ∀ a ∈ kleinFourFinset, a⁻¹ ∈ kleinFourFinset := by
  unfold kleinFourFinset
  decide +kernel

theorem kleinFourFinset_conj :
    ∀ a ∈ kleinFourFinset, ∀ g : Perm (Fin 4), g * a * g⁻¹ ∈ kleinFourFinset := by
  unfold kleinFourFinset
  decide +kernel

theorem card_kleinFourFinset : kleinFourFinset.card = 4 := by
  unfold kleinFourFinset
  decide +kernel

@[expose] def kleinFourS4 : Subgroup (Perm (Fin 4)) where
  carrier := {p | p ∈ kleinFourFinset}
  mul_mem' := fun {a b} ha hb => kleinFourFinset_mul a ha b hb
  one_mem' := by
    unfold kleinFourFinset
    simp
  inv_mem' := fun {a} ha => kleinFourFinset_inv a ha

instance kleinFourS4_normal : kleinFourS4.Normal :=
  ⟨fun n hn g => kleinFourFinset_conj n hn g⟩

theorem card_kleinFourS4 : Nat.card kleinFourS4 = 4 := by
  have h : Nat.card kleinFourS4 = Nat.card (↑kleinFourFinset : Set (Perm (Fin 4))) := rfl
  rw [h, Nat.card_coe_set_eq, Set.ncard_coe_finset, card_kleinFourFinset]

theorem four_le_card_pCore_of_mulEquiv_perm_four {R : Type*} [Group R] [Finite R]
    (e : R ≃* Perm (Fin 4)) : 4 ≤ Nat.card (CFSG.pCore 2 R) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let V : Subgroup R := kleinFourS4.map e.symm.toMonoidHom
  have hVn : V.Normal := Subgroup.Normal.map inferInstance e.symm.toMonoidHom e.symm.surjective
  have hV4 : Nat.card V = 4 := by
    rw [Subgroup.card_map_of_injective e.symm.injective, card_kleinFourS4]
  have hVp : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hV4]; norm_num)
  have hle : V ≤ CFSG.pCore 2 R := le_sSup ⟨hVn, hVp⟩
  have h := Subgroup.card_le_of_le hle
  omega

theorem card_quotient_pCore_le_of_card_le {R : Type*} [Group R] [Finite R]
    (h : Nat.card R ≤ 6) : Nat.card (R ⧸ CFSG.pCore 2 R) ≤ 6 :=
  (Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)).trans h

theorem card_quotient_pCore_le_six_of_mulEquiv_perm_four {R : Type*} [Group R] [Finite R]
    (e : R ≃* Perm (Fin 4)) : Nat.card (R ⧸ CFSG.pCore 2 R) ≤ 6 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 R)
  have h24 : Nat.card R = 24 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
    rfl
  have h4 := four_le_card_pCore_of_mulEquiv_perm_four e
  by_contra hcon
  have h7 : 7 ≤ Nat.card (R ⧸ CFSG.pCore 2 R) := by omega
  have := Nat.mul_le_mul h7 h4
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.SymThree
