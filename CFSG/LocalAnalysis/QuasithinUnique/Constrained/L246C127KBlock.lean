module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Main
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127DegMain
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCZOdd
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127DegLin2
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin CFSG.SectionRank
open scoped commutatorElement

@[expose] def AltEvenExcludedBig : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (L K T : Subgroup Γ) (m n : ℕ), Even m → 10 ≤ m → Odd n →
    3 ≤ n → n ≤ m → Nonempty (↥L ≃* alternatingGroup (Fin m)) → K ≤ L →
    Nonempty (↥K ≃* alternatingGroup (Fin n)) → IsSylowTwoOf T L → IsSubnormal K (K ⊔ T) → False

namespace L246C127

@[expose] def KBlockTypeOf {G : Type} [Group G] (K : Subgroup G) : Prop :=
  (∃ e : ℕ, 1 < e ∧ IsLin2Type K e) ∨ ∃ k : ℕ, 1 ≤ k ∧ IsAltType K (2 ^ k + 1)

theorem card_sl3_two : Nat.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) = 168 := by
  rw [Matrix.card_SL_field]
  simp [Fin.prod_univ_three, ZMod.card]

variable {G : Type} [Group G] [Finite G]

namespace Deg

theorem exists_normFixed_of_blockType {P T K : Subgroup G} (hB : IsBlock2 P K) (hK : KBlockTypeOf K)
    (hT2 : IsPGroup 2 T) (hUT : blockU K ≤ T) (hKJ : ⁅K, thompsonJ T⁆ = K) :
    ∃ u ∈ blockU K, u ∉ blockZ K ∧
      ∀ x ∈ T ⊓ Subgroup.normalizer (K : Set G), x * u * x⁻¹ = u := by
  have hsh : IsShort2 K := hB.1
  rcases hK with ⟨n, hn, hlin⟩ | ⟨k, hk, halt⟩
  · exact exists_normFixed_lin2 (C1GN.isChiBlock_of_isChi0Block hB ⟨hB, Or.inl ⟨n, hn, hlin⟩⟩) hn
      hlin hT2 hUT hKJ
  · rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · have hk1 : k = 1 := by omega
      subst hk1
      exact exists_normFixed_of_blockZ_eq_bot hsh (blockZ_eq_bot_of_alt3 hsh halt) hT2
    · have hodd : Odd (2 ^ k + 1) := (Nat.even_pow.2 ⟨even_two, by omega⟩).add_one
      have h5 : 5 ≤ 2 ^ k + 1 := by
        have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
        omega
      exact exists_normFixed_of_blockZ_eq_bot hsh
        (AppC.blockZ_eq_bot_of_alt_odd hsh hodd h5 halt) hT2

end Deg

namespace Setting

variable {X T P K : Subgroup G} (S : Setting X T P K)

include S

theorem not_le_centralizer_omega_of_blockType (hK : KBlockTypeOf K) (hKJ : ⁅K, thompsonJ T⁆ = K) :
    ¬ K ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  intro hKC
  have hP2 : CharTwo P := CFSG.Quasithin.C1GN.charTwo_of_le S.charTwo S.sylow S.TP S.PX
  obtain ⟨u, hu, huZ, hfix⟩ :=
    Deg.exists_normFixed_of_blockType S.block hK S.sylow.2.1 S.blockU_le_T hKJ
  obtain ⟨z, hz, k, hk, hzk⟩ := Deg.exists_central_not_centralized hP2 S.sylow.2.1 S.TP S.block
    S.blockU_le_T hu huZ hfix
  exact hzk (Subgroup.mem_centralizer_iff.1 (hKC hk) z hz)

theorem degree_cases_K (hV : IsElemAbelian 2 (VZ T X)) (hUV : blockU K ≤ VZ T X)
    (htype : KBlockTypeOf K) {n : ℕ} (e : ↥(autI hV K) ≃* alternatingGroup (Fin n)) :
    n = 3 ∨ n = 5 ∨ ∃ k : ℕ, 3 ≤ k ∧ n = 2 ^ k + 1 := by
  rcases htype with ⟨e', he', hlin⟩ | ⟨k, hk, halt⟩
  · rcases S.degree_eq_three_or_five hV hUV (Or.inl ⟨e', he', hlin⟩) e with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases alt_degree_cases e (S.isQuasisimple_or_card_three_autI hV hUV) with h3 | h5
    · exact Or.inl h3
    · right
      obtain ⟨α, hα, hker, -⟩ := halt
      have hn4 : 4 ≤ Nat.card (Fin n) := by
        rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega
      have hc : Subgroup.center ↥(autI hV K) = ⊥ :=
        center_eq_bot_of_mulEquiv e (alternatingGroup.center_eq_bot hn4)
      obtain ⟨φ⟩ := S.nonempty_equiv_of_center_eq_bot hV hUV α hα hker hc
      have hcard := Nat.card_congr (e.symm.trans φ).toEquiv
      have hpos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      haveI : Nontrivial (Fin n) := ⟨⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩⟩
      haveI : Nontrivial (Fin (2 ^ k + 1)) := ⟨⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩⟩
      rw [nat_card_alternatingGroup, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Nat.card_eq_fintype_card (α := Fin (2 ^ k + 1)), Fintype.card_fin, Fintype.card_fin] at hcard
      have h1 : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
      have h2 : 2 ∣ (2 ^ k + 1).factorial := Nat.dvd_factorial (by norm_num) (by omega)
      have hfac : n.factorial = (2 ^ k + 1).factorial := by omega
      have hnk : n = 2 ^ k + 1 := (Nat.factorial_inj (by omega)).1 hfac
      by_cases hk3 : 3 ≤ k
      · exact Or.inr ⟨k, hk3, hnk⟩
      · have hk' : k = 1 ∨ k = 2 := by omega
        rcases hk' with rfl | rfl
        · omega
        · exact Or.inl (by omega)

theorem isEmpty_equiv_sl3_K (hV : IsElemAbelian 2 (VZ T X)) (hUV : blockU K ≤ VZ T X)
    (htype : KBlockTypeOf K) :
    IsEmpty (↥(autI hV K) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  rcases htype with ⟨e', he', hlin⟩ | ⟨k, hk, halt⟩
  · exact S.isEmpty_equiv_sl3 hV hUV (Or.inl ⟨e', he', hlin⟩)
  · refine ⟨fun e => ?_⟩
    obtain ⟨α, hα, hker, -⟩ := halt
    have hc : Subgroup.center ↥(autI hV K) = ⊥ := center_eq_bot_of_mulEquiv e center_sl3_eq_bot
    obtain ⟨φ⟩ := S.nonempty_equiv_of_center_eq_bot hV hUV α hα hker hc
    have hcard := Nat.card_congr (e.symm.trans φ).toEquiv
    have hpos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    haveI : Nontrivial (Fin (2 ^ k + 1)) := ⟨⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩⟩
    rw [card_sl3_two, nat_card_alternatingGroup, Nat.card_eq_fintype_card (α := Fin (2 ^ k + 1)),
      Fintype.card_fin] at hcard
    have h2 : 2 ∣ (2 ^ k + 1).factorial := Nat.dvd_factorial (by norm_num) (by omega)
    have hfac : (2 ^ k + 1).factorial = 336 := by omega
    have hmono : ∀ j : ℕ, 6 ≤ j → 720 ≤ j.factorial := fun j hj => by
      calc 720 = (6 : ℕ).factorial := by decide
        _ ≤ j.factorial := Nat.factorial_le hj
    by_cases hk2 : 2 ≤ k
    · have h4 : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
      by_cases hk3 : 3 ≤ k
      · have h8 : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
        have := hmono (2 ^ k + 1) (by omega)
        omega
      · have : k = 2 := by omega
        subst this
        revert hfac
        decide
    · have : k = 1 := by omega
      subst this
      revert hfac
      decide

theorem exists_block_of_concl_K (hodd : AltEvenExcluded) (hoddBig : AltEvenExcludedBig)
    (hV : IsElemAbelian 2 (VZ T X)) (hUV : blockU K ≤ VZ T X) (htype : KBlockTypeOf K)
    (hB : Bridge.B113Concl (autI hV X) (autI hV K)) :
    ∃ L : Subgroup G, IsBlock2 X L ∧ K ≤ L ∧ blockU K ≤ blockU L ∧ blockU L ≤ VZ T X ∧
      (K = L ∨ ∃ m n : ℕ, Odd m ∧ Odd n ∧ 3 ≤ m ∧ 3 ≤ n ∧
        IsAltQuotient L (Subgroup.centralizer (VZ T X : Set G)) m ∧
        IsAltQuotient K (Subgroup.centralizer (VZ T X : Set G)) n) := by
  have hq0 := S.isQuasisimple_or_card_three_autI hV hUV
  have hKX : K ≤ X := S.KP.trans S.PX
  have hKaX : autI hV K ≤ autI hV X := autI_mono hV hKX
  have hself : IsSubnormal (autI hV K) (autI hV X) → ∃ L : Subgroup G, IsBlock2 X L ∧ K ≤ L ∧
      blockU K ≤ blockU L ∧ blockU L ≤ VZ T X ∧ K = L := by
    intro hsub
    obtain ⟨L, hL, hKL, hUL, hULV, -, -, hLK⟩ := S.exists_block_lift hV hUV hKaX hsub le_rfl hq0
      (fun N hN _ hKN => le_antisymm hN hKN)
    exact ⟨L, hL, hKL, hUL, hULV, (hLK rfl).symm⟩
  rcases hB with ⟨-, hF⟩ | hcomp | ⟨Lstar, hLcomp, hKL, m, ⟨eL⟩, hrest⟩
  · obtain ⟨L, hL, hKL, hUL, hULV, hKe⟩ := hself (isSubnormal_of_le_center_fitting hF)
    exact ⟨L, hL, hKL, hUL, hULV, Or.inl hKe⟩
  · obtain ⟨L, hL, hKL, hUL, hULV, hKe⟩ := hself hcomp.2.1
    exact ⟨L, hL, hKL, hUL, hULV, Or.inl hKe⟩
  · obtain ⟨hLle, hLsub, hLqs⟩ := hLcomp
    have hqL : CFSG.IsQuasisimple ↥Lstar := B1Red.isQuasisimple_of_open hLqs
    have hm5 : 5 ≤ m := alt_five_le_of_quasisimple eL hqL
    have hsimpL : IsSimpleGroup ↥Lstar :=
      (MulEquiv.isSimpleGroup_congr eL).2 (Bridge.alt_isSimple hm5)
    have hKnt : Nontrivial ↥(autI hV K) := nontrivial_of_quasisimple_or_card_three hq0
    have hnc : ∀ N : Subgroup (MulAut (IntMod (VZ T X) hV)), N ≤ Lstar →
        (N.subgroupOf Lstar).Normal → autI hV K ≤ N → N = Lstar := by
      intro N hNL hNn hKN
      have : (N.subgroupOf Lstar).Normal := hNn
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf Lstar) with h | h
      · exfalso
        have hN0 : N = ⊥ := disjoint_self.1 ((Subgroup.subgroupOf_eq_bot.1 h).mono_right hNL)
        rw [hN0] at hKN
        exact (Subgroup.nontrivial_iff_ne_bot _).1 hKnt (le_bot_iff.1 hKN)
      · exact le_antisymm hNL (Subgroup.subgroupOf_eq_top.1 h)
    obtain ⟨L, hL, hKL', hUL, hULV, hautL, -, hLK⟩ :=
      S.exists_block_lift hV hUV hLle hLsub hKL (Or.inl hqL) hnc
    by_cases hKe : autI hV K = Lstar
    · exact ⟨L, hL, hKL', hUL, hULV, Or.inl (hLK hKe).symm⟩
    · refine ⟨L, hL, hKL', hUL, hULV, Or.inr ?_⟩
      have hLN : L ≤ Subgroup.normalizer (VZ T X : Set G) := hL.2.1.trans S.hXV
      have eL' : ↥(autI hV L) ≃* alternatingGroup (Fin m) :=
        (MulEquiv.subgroupCongr hautL).trans eL
      have hLalt := isAltQuotient_of_equiv hV hLN eL'
      rcases hrest with ⟨n, hnm, ⟨eK⟩⟩ | ⟨⟨eK3⟩, hm7⟩
      · have hn : n = 3 ∨ n = 5 ∨ ∃ k : ℕ, 3 ≤ k ∧ n = 2 ^ k + 1 :=
          S.degree_cases_K hV hUV htype eK
        have hnodd : Odd n := by
          rcases hn with h | h | ⟨k, hk, hnk⟩
          · rw [h]; decide
          · rw [h]; decide
          · rw [hnk]; exact (Nat.even_pow.2 ⟨even_two, by omega⟩).add_one
        have hn3 : 3 ≤ n := by
          rcases hn with h | h | ⟨k, hk, hnk⟩
          · omega
          · omega
          · have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
            omega
        have hmodd : Odd m := by
          rcases Nat.even_or_odd m with he | ho
          · exfalso
            have hsyl : IsSylowTwoOf (autI hV T ⊓ Lstar) Lstar :=
              isSylowTwoOf_inf_of_isSubnormal' hLsub (B2F.isSylowTwoOf_autI hV S.hXV S.sylow)
            have hsubK : IsSubnormal (autI hV K) (autI hV K ⊔ (autI hV T ⊓ Lstar)) :=
              A3.subnormal_of_le_of_le (S.isSubnormal_autI_sup hV) le_sup_left
                (sup_le le_sup_left (inf_le_left.trans le_sup_right))
            by_cases hm10 : 10 ≤ m
            · exact hoddBig _ Lstar (autI hV K) (autI hV T ⊓ Lstar) m n he hm10 hnodd hn3 hnm
                ⟨eL⟩ hKL ⟨eK⟩ hsyl hsubK
            · have h68 : m = 6 ∨ m = 8 := by
                obtain ⟨r, hr⟩ := he
                omega
              have hn35 : n = 3 ∨ n = 5 := by
                rcases hn with h | h | ⟨k, hk, hnk⟩
                · exact Or.inl h
                · exact Or.inr h
                · exfalso
                  have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
                  omega
              exact hodd _ Lstar (autI hV K) (autI hV T ⊓ Lstar) m n h68 hn35 ⟨eL⟩ hKL ⟨eK⟩ hsyl
                hsubK
          · exact ho
        exact ⟨m, n, hmodd, hnodd, by omega, hn3, hLalt, isAltQuotient_of_equiv hV S.hKN eK⟩
      · exact ((S.isEmpty_equiv_sl3_K hV hUV htype).false eK3).elim

end Setting

end L246C127

end CFSG.QuasithinUnique
