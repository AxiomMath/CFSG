module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockDefs
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsPL
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockReduce
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockQuotient
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockTargets
import CFSG.LocalAnalysis.AGLEmbedding.A15ComponentsAux
import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsSpTwo
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimOrders

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

namespace LeviBlock

theorem card_alternatingGroup_ne_u42 (n : ℕ) (hn : 2 ≤ n) :
    Nat.card (alternatingGroup (Fin n)) ≠ 25920 := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  have hAc := two_mul_nat_card_alternatingGroup (α := Fin n)
  rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin] at hAc
  intro h
  rw [h] at hAc
  by_cases h9 : 9 ≤ n
  · have := Nat.factorial_le h9
    rw [← hAc] at this
    exact absurd this (by decide)
  · interval_cases n <;> revert hAc <;> decide

theorem nine_le_of_dvd_factorial {n : ℕ} (h : 3 ^ 4 ∣ n.factorial) : 9 ≤ n := by
  by_contra hn
  interval_cases n <;> revert h <;> decide

theorem isPGroup_ker_comp_mk {X Q : Type*} [Group X] [Group Q] (e : X ⧸ CFSG.pCore 2 X ≃* Q) :
    IsPGroup 2 (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 X))).ker := by
  have hker : (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 X))).ker = CFSG.pCore 2 X := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    change e (QuotientGroup.mk' _ x) = 1 ↔ _
    rw [map_eq_one_iff e e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  rw [hker]
  exact CFSG.pCore_isPGroup

theorem not_three_dvd_of_isPGroup_two {X : Type*} [Group X] [Finite X] {K : Subgroup X}
    (hK : IsPGroup 2 K) : ¬ 3 ∣ Nat.card K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hK
  rw [hk]
  intro h
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h) (by norm_num)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem subgroupOf_data {P O W : Subgroup G} (hOP : O ≤ P) (hWP : W ≤ P)
    (hPO : P ≤ Subgroup.normalizer (O : Set G))
    (hPWO : P ≤ Subgroup.normalizer ((W ⊔ O : Subgroup G) : Set G)) (hWW : ⁅W, W⁆ = W) :
    (O.subgroupOf P).Normal ∧ (W.subgroupOf P ⊔ O.subgroupOf P).Normal ∧
      Nat.card (O.subgroupOf P) = Nat.card O ∧
      (W.subgroupOf P ⊔ O.subgroupOf P).index = (W ⊔ O).relIndex P ∧
      ⁅W.subgroupOf P, W.subgroupOf P⁆ = W.subgroupOf P := by
  refine ⟨(Subgroup.normal_subgroupOf_iff_le_normalizer hOP).mpr hPO, ?_,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOP).toEquiv, ?_, ?_⟩
  · rw [← Subgroup.subgroupOf_sup hWP hOP]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (sup_le hWP hOP)).mpr hPWO
  · rw [← Subgroup.subgroupOf_sup hWP hOP]
    rfl
  · apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hWP, hWW]

theorem dvd_of_dvd_two_pow_mul' {a m : ℕ} (h : 3 ^ 4 ∣ 2 ^ a * m) : 3 ^ 4 ∣ m :=
  (Nat.Coprime.pow 4 a (by norm_num : Nat.Coprime 3 2)).dvd_of_dvd_mul_left h

theorem false_of_perm_case {P : Subgroup G} {O W : Subgroup ↥P} {d : TauCeti.ValidLieTypeIndex}
    {n : ℕ} (e : ↥P ⧸ CFSG.pCore 2 ↥P ≃* Equiv.Perm (Fin n)) (h81 : 3 ^ 4 ∣ Nat.card P)
    (hcard : Nat.card (CatGroup d) = 25920) [IsSimpleGroup (CatGroup d)] [Finite (CatGroup d)]
    (h3U : 3 ∣ Nat.card (CatGroup d)) (hOn : O.Normal) (hOc : Nat.Coprime 3 (Nat.card O))
    {i : ℕ} (hidx : (W ⊔ O).index = i)
    (hi : i ≤ 2) (hW : ⁅W, W⁆ = W) (ψ : ↥W →* CatGroup d) (hψ : Function.Surjective ψ) :
    False := by
  obtain ⟨a, ha⟩ := card_eq_of_quotient_pCore e
  rw [ha, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at h81
  have hn := nine_le_of_dvd_factorial (dvd_of_dvd_two_pow_mul' h81)
  have := hOn
  have hρ := e.surjective.comp (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥P))
  have hdvd := card_dvd_ker_of_perm (by omega)
    (by rw [hcard]; exact card_alternatingGroup_ne_u42 n (by omega))
    (e.toMonoidHom.comp (QuotientGroup.mk' _)) hρ hOc (hidx ▸ hi) hW ψ hψ
  exact not_three_dvd_of_isPGroup_two (isPGroup_ker_comp_mk e) (h3U.trans hdvd)

omit [Finite G] in
theorem surjective_snd_comp {X : Type*} [Group X] {r s : ℕ}
    (φ : X ⧸ CFSG.pCore 2 X ≃* Equiv.Perm (Fin r) × Equiv.Perm (Fin s)) :
    Function.Surjective ((MonoidHom.snd _ _).comp
      (φ.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 X)))) :=
  Prod.snd_surjective.comp (φ.surjective.comp (QuotientGroup.mk'_surjective _))

end LeviBlock

theorem kFactBlockLeviU42_of (hTPL : CitedBlockTransvectionPL) (hA7 : CitedBlockAltSevenPL)
    (hC : KFactCompParabLeviU42) : KFactBlockLeviU42 := by
  intro G _ _ M S L hK hA hL h93 hX hS _ O V hVM hO hV hPO hOc hPVO hrel hVV d ψ hd hψ hker hQ hZ
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hcard, hsimp⟩ := LeviBlock.catGroup_u42_facts hd
  have : Finite (CatGroup d) := Finite.of_surjective ψ hψ
  obtain ⟨ψ', hψ', hk'⟩ := LeviBlock.exists_surj_barM (by rw [hcard]; norm_num) hVM ψ hψ
  have h81 : 3 ^ 4 ∣ Nat.card (blockParabolic M S L) := by
    obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow 3 ↥(blockParabolic M S L)))
    rw [← hQ Q]
    exact Subgroup.card_subgroup_dvd_card _
  have h243 : ¬ 3 ^ 5 ∣ Nat.card (blockParabolic M S L) := by
    intro h5
    obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow 3 ↥(blockParabolic M S L)))
    have := Q.pow_dvd_card_of_pow_dvd_card h5
    rw [hQ Q] at this
    exact absurd (Nat.le_of_dvd (by norm_num) this) (by norm_num)
  have hWp := commutator_barM_eq_self hVM hVV
  obtain ⟨hOn, hWOn, hOcard, hidx, hWp'⟩ := LeviBlock.subgroupOf_data hO hV hPO hPVO hWp
  set ψ₁ := ψ'.comp (Subgroup.subgroupOfEquivOfLe hV).toMonoidHom with hψ₁d
  have hψ₁ : Function.Surjective ψ₁ := hψ'.comp (MulEquiv.surjective _)
  have hOc' : Nat.Coprime 3 (Nat.card ((O.subgroupOf (blockParabolic M S L)))) := by
    rw [hOcard]; exact hOc
  have h3U : 3 ∣ Nat.card (CatGroup d) := by rw [hcard]; norm_num
  rcases h93 with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact absurd h1 hX
  · exact hC _ _ _ (LeviBlock.compParab_of_nineThreeTwo hA hL hS h2) hZ O (barM M V) hO hPO hOc
      hV hPVO hrel hWp d ψ' hd hψ' (Nat.Coprime.coprime_dvd_right hk' hker) hQ
  · exfalso
    rcases hTPL G M S L hK hA hL hX hS h3 with ⟨k, d', hk, hd', ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
    · obtain ⟨hTs, h29⟩ := kFactSpTwoSimple_holds k d' hk hd'
      have : Finite (CatGroup d') :=
        Finite.of_surjective _ (e.surjective.comp (QuotientGroup.mk'_surjective _))
      have h3Q : 3 ∣ Nat.card (CatGroup d') := by
        obtain ⟨q, hq2, hdq⟩ := hd'
        have hq : q.p = 2 ∧ q.exponent = 1 := by
          rw [TauCeti.PrimePower.card_def] at hq2
          exact Nat.prime_two.pow_eq_iff.mp hq2
        rw [card_catGroup_B_even hk hq.1 hdq, hq.2, pow_one]
        unfold ordBC
        rw [show Nat.gcd 2 (2 - 1) = 1 by norm_num, Nat.div_one]
        exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun i => 2 ^ (2 * i) - 1)
          (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)) _
      have := hOn
      have := hWOn
      rcases LeviBlock.card_dvd_ker_of_simple (U := CatGroup d) h3Q
          (e.toMonoidHom.comp (QuotientGroup.mk' _))
          (e.surjective.comp (QuotientGroup.mk'_surjective _)) hOc' ψ₁ hψ₁ with h | h
      · exact LeviBlock.not_three_dvd_of_isPGroup_two (LeviBlock.isPGroup_ker_comp_mk e)
          (h3U.trans h)
      · rw [hcard] at h
        change 2 ^ 9 ∣ Nat.card (CatGroup d') at h29
        rw [h] at h29
        exact absurd h29 (by norm_num)
    · obtain ⟨a, ha⟩ := LeviBlock.card_eq_of_quotient_pCore e
      change Nat.card (blockParabolic M S L) = 2 ^ a * Nat.card (Equiv.Perm (Fin n)) at ha
      rw [ha, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at h81
      have := LeviBlock.nine_le_of_dvd_factorial (LeviBlock.dvd_of_dvd_two_pow_mul' h81)
      omega
  · exact (hZ (by rw [h4.2.1])).elim
  · exact absurd (h81.trans (hA7 G M S L hK hA hL hX hS h5)) (by norm_num)
  · obtain ⟨-, n, -, ⟨e⟩⟩ := h6
    exact (LeviBlock.false_of_perm_case e h81 hcard h3U hOn hOc' hidx hrel hWp' ψ₁ hψ₁).elim
  · obtain ⟨-, n, -, ⟨e⟩⟩ := h7
    exact (LeviBlock.false_of_perm_case e h81 hcard h3U hOn hOc' hidx hrel hWp' ψ₁ hψ₁).elim
  · exfalso
    obtain ⟨-, N, r, ⟨m, hm⟩, hr, h0, h2', h4', -, φ, -⟩ := h8
    have hs : 6 ≤ N - 2 * r := by omega
    have := hOn
    have hρ := LeviBlock.surjective_snd_comp φ
    have hdvd := LeviBlock.card_dvd_ker_of_perm (U := CatGroup d) (by omega)
      (by rw [hcard]; exact LeviBlock.card_alternatingGroup_ne_u42 _ (by omega)) _ hρ hOc'
      (hidx ▸ hrel) hWp' ψ₁ hψ₁
    have hP := Subgroup.card_ker_mul_card_of_surjective hρ
    have hfin : Nat.card (Fin (N - 2 * r)) = N - 2 * r := by simp
    rw [Nat.card_perm, hfin] at hP
    rw [hcard] at hdvd
    apply h243
    rw [← hP]
    have h9 : 3 ^ 2 ∣ (N - 2 * r).factorial :=
      (show 3 ^ 2 ∣ (6 : ℕ).factorial by decide).trans (Nat.factorial_dvd_factorial hs)
    exact (pow_dvd_pow 3 (by norm_num : 5 ≤ 4 + 2)).trans
      (pow_add 3 4 2 ▸ Nat.mul_dvd_mul ((show 3 ^ 4 ∣ 25920 by norm_num).trans hdvd) h9)

end CFSG.AGLEmbedding
