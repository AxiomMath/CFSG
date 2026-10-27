module

public import CFSG.CGT.PushingUpLit.A78One.OneStmts
import CFSG.CGT.PushingUpLit.A78One.CjLemmas
import CFSG.CGT.PushingUpLit.A78One.Dict
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.CGT.PushingUpLit.A78One

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.Quasithin
open CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.T2K

variable {G : Type} [Group G] [Finite G]

namespace EndSwap

omit [Finite G] in
private theorem mem_normalizer_iff_cj {g : G} {H : Subgroup G} :
    g ∈ Subgroup.normalizer (H : Set G) ↔ cj g H = H :=
  Subgroup.mem_normalizer_iff_map_conj_eq

omit [Finite G] in
private theorem cj_injective {g : G} {H K : Subgroup G} (h : cj g H = cj g K) : H = K := by
  rw [← cjx_inv_cj g H, h, cjx_inv_cj]

omit [Finite G] in
private theorem cj_inv_of_cj {g : G} {H : Subgroup G} (h : cj g H = H) : cj g⁻¹ H = H := by
  calc cj g⁻¹ H = cj g⁻¹ (cj g H) := by rw [h]
    _ = H := cjx_inv_cj g H

omit [Finite G] in
private theorem isMaxElemAbelian_cj {S A : Subgroup G} (hA : IsMaxElemAbelian S A) {g : G}
    (h : cj g A ≤ S) : IsMaxElemAbelian S (cj g A) :=
  ⟨h, cjx_isElemAbelian hA.2.1 g, fun B hB hBe => by
    rw [cjx_card]
    exact hA.2.2 B hB hBe⟩

omit [Finite G] in
private theorem fix_or_swap {S P Q : Subgroup G}
    (hmax : ∀ A, IsMaxElemAbelian S A ↔ A = P ∨ A = Q) (hne : P ≠ Q) {g : G}
    (hP : cj g P ≤ S) (hQ : cj g Q ≤ S) :
    (cj g P = P ∧ cj g Q = Q) ∨ (cj g P = Q ∧ cj g Q = P) := by
  have h1 := (hmax _).1 (isMaxElemAbelian_cj ((hmax P).2 (Or.inl rfl)) hP)
  have h2 := (hmax _).1 (isMaxElemAbelian_cj ((hmax Q).2 (Or.inr rfl)) hQ)
  have hinj : cj g P ≠ cj g Q := fun h => hne (cj_injective h)
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h1.trans h2.symm) hinj
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (h1.trans h2.symm) hinj

omit [Finite G] in
private theorem fix_of_fix {S P Q : Subgroup G}
    (hmax : ∀ A, IsMaxElemAbelian S A ↔ A = P ∨ A = Q) (hne : P ≠ Q) {g : G}
    (hS : cj g S = S) (hP : cj g P = P) : cj g Q = Q := by
  have hPS : P ≤ S := ((hmax P).2 (Or.inl rfl)).1
  have hQS : Q ≤ S := ((hmax Q).2 (Or.inr rfl)).1
  rcases fix_or_swap hmax hne (hP.le.trans hPS) ((cjx_mono g hQS).trans hS.le) with
    ⟨_, h⟩ | ⟨h, _⟩
  · exact h
  · exact absurd (hP.symm.trans h) hne

omit [Finite G] in
private theorem fix_or_swap_sup {T' P Q : Subgroup G}
    (hmax : ∀ A, IsMaxElemAbelian T' A ↔ A = P ∨ A = Q) (hne : P ≠ Q) {g : G}
    (hg : cj g (P ⊔ Q) = P ⊔ Q) :
    (cj g P = P ∧ cj g Q = Q) ∨ (cj g P = Q ∧ cj g Q = P) := by
  have hJ : P ⊔ Q ≤ T' :=
    sup_le ((hmax P).2 (Or.inl rfl)).1 ((hmax Q).2 (Or.inr rfl)).1
  exact fix_or_swap hmax hne ((cjx_mono g le_sup_left).trans (hg.le.trans hJ))
    ((cjx_mono g le_sup_right).trans (hg.le.trans hJ))

private theorem exists_swap {M T T' P Q : Subgroup G} {x : G}
    (hSyl : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hmax : ∀ A, IsMaxElemAbelian T' A ↔ A = P ∨ A = Q)
    (hmaxT : ∀ A, IsMaxElemAbelian T A ↔ A = P ∨ A = Q) (hne : P ≠ Q)
    (hxT : x ∈ Subgroup.normalizer (T' : Set G)) (hxP : cj x⁻¹ P = Q)
    (hN : Subgroup.normalizer (P : Set G) ≤ M)
    (hMP : ∀ g ∈ M, g ∈ Subgroup.normalizer (T : Set G) → cj g P = P) :
    ∃ x' : G, x' ∈ Subgroup.normalizer (T : Set G) ∧ x' ∉ M ∧ cj x'⁻¹ P = Q ∧
      cj x'⁻¹ Q = P := by
  have hPT' : P ≤ T' := ((hmax P).2 (Or.inl rfl)).1
  have hxT' : cj x⁻¹ T' = T' := cj_inv_of_cj (mem_normalizer_iff_cj.1 hxT)
  have hxQ : cj x⁻¹ Q = P := by
    rcases fix_or_swap hmax hne ((cjx_mono x⁻¹ hPT').trans hxT'.le)
      ((cjx_mono x⁻¹ ((hmax Q).2 (Or.inr rfl)).1).trans hxT'.le) with ⟨h, _⟩ | ⟨_, h⟩
    · exact absurd (h.symm.trans hxP) hne
    · exact h
  have hcxQ : cj x Q = P := by rw [← hxP, cjx_cj_inv]
  have hcxP : cj x P = Q := by rw [← hxQ, cjx_cj_inv]
  have hTfix : ∀ t ∈ T, cj t P = P ∧ cj t Q = Q := fun t ht =>
    have htP : cj t P = P := hMP t (hSyl.le ht) (Subgroup.le_normalizer ht)
    ⟨htP, fix_of_fix hmaxT hne (mem_normalizer_iff_cj.1 (Subgroup.le_normalizer ht)) htP⟩
  have hJfix : ∀ g : G, cj g P = P → cj g Q = Q → cj g (P ⊔ Q) = P ⊔ Q := fun g h1 h2 => by
    rw [cjx_sup, h1, h2]
  obtain ⟨N3, hN3⟩ : ∃ N3 : Subgroup G,
      ∀ g, g ∈ N3 ↔ (cj g (P ⊔ Q) = P ⊔ Q ∧ cj g P = P) :=
    ⟨Subgroup.normalizer ((P ⊔ Q : Subgroup G) : Set G) ⊓ Subgroup.normalizer (P : Set G),
      fun g => by simp only [Subgroup.mem_inf, mem_normalizer_iff_cj]⟩
  have hN3M : N3 ≤ M := fun g hg => hN (mem_normalizer_iff_cj.2 ((hN3 g).1 hg).2)
  have hTN3 : T ≤ N3 := fun t ht =>
    (hN3 t).2 ⟨hJfix t (hTfix t ht).1 (hTfix t ht).2, (hTfix t ht).1⟩
  have hTsyl := hSyl.of_le hTN3 hN3M
  have hS : ∀ y ∈ cj x⁻¹ T, cj y P = P ∧ cj y Q = Q := by
    intro y hy
    rw [cjx_mem, inv_inv] at hy
    obtain ⟨h1, h2⟩ := hTfix _ hy
    have key : ∀ Z, cj y Z = cj x⁻¹ (cj (x * y * x⁻¹) (cj x Z)) := fun Z => by
      simp only [cjx_cj]
      rw [show x⁻¹ * (x * y * x⁻¹ * x) = y by group]
    exact ⟨by rw [key, hcxP, h2, hxQ], by rw [key, hcxQ, h1, hxP]⟩
  have hSN3 : cj x⁻¹ T ≤ N3 := fun y hy =>
    (hN3 y).2 ⟨hJfix y (hS y hy).1 (hS y hy).2, (hS y hy).1⟩
  have hSsyl : CFSG.ABGLocalTools.IsSylowOf 2 (cj x⁻¹ T) N3 :=
    CFSG.ABGLocalTools.isSylowOf_of_card hSN3 (by rw [cjx_card]; exact hTsyl.card_eq)
  obtain ⟨k, hk3, hk⟩ := hTsyl.exists_mem_conj hSsyl
  have hkT : cj x⁻¹ T = cj k T := Subgroup.ext fun y => (hk y).trans (cjx_mem k T y).symm
  obtain ⟨hkJ, hkP⟩ := (hN3 k).1 hk3
  have hkQ : cj k Q = Q := by
    rcases fix_or_swap_sup hmax hne hkJ with ⟨_, h⟩ | ⟨h, _⟩
    · exact h
    · exact absurd (hkP.symm.trans h) hne
  have hxk : x * k ∈ Subgroup.normalizer (T : Set G) := by
    rw [mem_normalizer_iff_cj, ← cjx_cj, ← hkT, cjx_cj_inv]
  have h3 : cj (x * k)⁻¹ P = Q := by
    rw [mul_inv_rev, ← cjx_cj, hxP, cj_inv_of_cj hkQ]
  have h4 : cj (x * k)⁻¹ Q = P := by
    rw [mul_inv_rev, ← cjx_cj, hxQ, cj_inv_of_cj hkP]
  refine ⟨x * k, hxk, fun hM => hne ?_, h3, h4⟩
  exact (hMP _ (M.inv_mem hM) (Subgroup.inv_mem _ hxk)).symm.trans h3

private theorem not_isSylow_of_swap {T T' P Q : Subgroup G} {x' : G}
    (hmax : ∀ A, IsMaxElemAbelian T' A ↔ A = P ∨ A = Q)
    (hmaxT : ∀ A, IsMaxElemAbelian T A ↔ A = P ∨ A = Q) (hne : P ≠ Q)
    (hTP : ∀ t ∈ T, cj t P = P) (hx' : x' ∈ Subgroup.normalizer (T : Set G))
    (h3 : cj x'⁻¹ P = Q) (h4 : cj x'⁻¹ Q = P) :
    ¬ CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ := by
  intro hsyl
  have hcP : cj x' P = Q := by rw [← h4, cjx_cj_inv]
  have hcQ : cj x' Q = P := by rw [← h3, cjx_cj_inv]
  have hTfix : ∀ t ∈ T, cj t P = P ∧ cj t Q = Q := fun t ht =>
    ⟨hTP t ht, fix_of_fix hmaxT hne
      (mem_normalizer_iff_cj.1 (Subgroup.le_normalizer ht)) (hTP t ht)⟩
  obtain ⟨N, hN⟩ : ∃ N : Subgroup G,
      ∀ g, g ∈ N ↔ (cj g T = T ∧ cj g (P ⊔ Q) = P ⊔ Q) :=
    ⟨Subgroup.normalizer (T : Set G) ⊓ Subgroup.normalizer ((P ⊔ Q : Subgroup G) : Set G),
      fun g => by simp only [Subgroup.mem_inf, mem_normalizer_iff_cj]⟩
  obtain ⟨K, hK⟩ : ∃ K : Subgroup G, ∀ g, g ∈ K ↔ (g ∈ N ∧ cj g P = P) :=
    ⟨N ⊓ Subgroup.normalizer (P : Set G), fun g => by
      simp only [Subgroup.mem_inf, mem_normalizer_iff_cj]⟩
  have hKN : K ≤ N := fun g hg => ((hK g).1 hg).1
  have hTK : T ≤ K := fun t ht =>
    (hK t).2 ⟨(hN t).2 ⟨mem_normalizer_iff_cj.1 (Subgroup.le_normalizer ht),
      by rw [cjx_sup, (hTfix t ht).1, (hTfix t ht).2]⟩, (hTfix t ht).1⟩
  have hx'N : x' ∈ N :=
    (hN x').2 ⟨mem_normalizer_iff_cj.1 hx', by rw [cjx_sup, hcP, hcQ, sup_comm]⟩
  have hidx : K.relIndex N = 2 := by
    show (K.subgroupOf N).index = 2
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨x', hx'N⟩, fun b => ?_⟩
    obtain ⟨b, hbN⟩ := b
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    rcases fix_or_swap_sup hmax hne ((hN b).1 hbN).2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine Or.inr ⟨(hK b).2 ⟨hbN, h1⟩, fun hbx => hne ?_⟩
      have := ((hK _).1 hbx).2
      rw [← cjx_cj, hcP, h2] at this
      exact this.symm
    · refine Or.inl ⟨(hK _).2 ⟨N.mul_mem hbN hx'N, by rw [← cjx_cj, hcP, h2]⟩, fun hb' => hne ?_⟩
      exact ((hK b).1 hb').2.symm.trans h1
  have hsylN := hsyl.of_le (hTK.trans hKN) le_top
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hsylN
  apply hsylN.2.2
  rw [← Subgroup.relIndex_mul_relIndex T K N hTK hKN, hidx]
  exact Dvd.intro_left _ rfl

end EndSwap

section Ending

variable {L M : Subgroup G} {n : ℕ} {T T' : Subgroup G} {x : G}

omit [Finite G] in
private theorem cexP_ne_bot (e : EndData L M n T T' x) : cexP L T ≠ ⊥ := by
  intro h
  apply e.ne
  rw [h]
  exact (Subgroup.map_bot _).symm

private theorem cj_cexP_of_mem (c : CexCtx L M n T T' x) {g : G} (hgM : g ∈ M)
    (hgT : g ∈ Subgroup.normalizer (T : Set G)) : cj g (cexP L T) = cexP L T :=
  EndSwap.mem_normalizer_iff_cj.1 (Subgroup.inf_normalizer_le_normalizer_inf ⟨hgT,
    mem_normalizer_centralizer (NatBlock.le_normalizer_blockU_of_le c.nM hgM)⟩)

theorem exists_x' (c : CexCtx L M n T T' x) (e : EndData L M n T T' x) :
    ∃ x' : G, x' ∈ Subgroup.normalizer (T : Set G) ∧ x' ∉ M ∧
      cj x'⁻¹ (cexP L T) = cj x⁻¹ (cexP L T) ∧ cj x'⁻¹ (cj x⁻¹ (cexP L T)) = cexP L T :=
  EndSwap.exists_swap c.sylow e.maxElem (fun A => c.isMax_iff.trans (e.maxElem A)) e.ne c.hx rfl
    (c.normalizer_le (cexP_ne_bot e) (isPGroup_cexP c.sylow)
      (le_normalizer_P_of c.hyp c.nM c.sylow))
    fun _ hgM hgT => cj_cexP_of_mem c hgM hgT

theorem not_isSylow_top (c : CexCtx L M n T T' x) (e : EndData L M n T T' x) :
    ¬ CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ := by
  obtain ⟨x', hx', -, h3, h4⟩ := exists_x' c e
  exact EndSwap.not_isSylow_of_swap e.maxElem (fun A => c.isMax_iff.trans (e.maxElem A)) e.ne
    (fun t ht => cj_cexP_of_mem c (c.sylow.le ht) (Subgroup.le_normalizer ht)) hx' h3 h4

end Ending

end CFSG.CGT.PushingUpLit.A78One
