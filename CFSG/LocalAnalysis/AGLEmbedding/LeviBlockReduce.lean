module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockDefs
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactsThreeFivesParabolic
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsPL
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGroups
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockTargets
import CFSG.LocalAnalysis.AGLEmbedding.LemmaBIrrGlue
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizerAux
import CFSG.LocalAnalysis.AGLEmbedding.A15ComponentsAux
import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsIVTypes
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimUnitaryLie

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

namespace LeviBlock

section Glue

variable {G : Type} [Group G] [Finite G]

theorem odd_card_center_barM {M L : Subgroup G} (hL : IsTwoPrimeComponent M L) :
    Odd (Nat.card (Subgroup.center ↥(barM M L))) := by
  rw [card_center_eq_card_inf_centralizer, ← Nat.coprime_two_left]
  exact coprime_two_card_inf_centralizer (pCore_quotient_pCore_eq_bot' 2) hL.component.2.1

theorem compParab_of_nineThreeTwo {M S L : Subgroup G} (hA : Asc81bHyp M S)
    (hL : IsWeakSBlock M S L) (hS : ¬ IsSylowTwoOf (S ⊓ L) L) (h2 : NineThreeTwo M S L) :
    CompParab (barM M L) (blockPL M S L) :=
  ⟨hL.component, h2.1, odd_card_center_barM hL.toIsTwoPrimeComponent, h2.2.1,
    barM_normalizer_inf_ne_of_asc81bHyp hA hL, ne_inf_normalizer_of_asc81bHyp hA hL hS h2⟩

end Glue

section BarM

variable {G : Type} [Group G] [Finite G]

noncomputable def toBarM {M V : Subgroup G} (hVM : V ≤ M) : ↥V →* ↥(barM M V) :=
  ((QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hVM)).codRestrict
    (barM M V) (fun v => ⟨⟨v, hVM v.2⟩, Subgroup.mem_subgroupOf.mpr v.2, rfl⟩)

omit [Finite G] in
theorem toBarM_surjective {M V : Subgroup G} (hVM : V ≤ M) :
    Function.Surjective (toBarM hVM) := by
  rintro ⟨_, ⟨m, hm, rfl⟩⟩
  exact ⟨⟨m, Subgroup.mem_subgroupOf.mp hm⟩, rfl⟩

omit [Finite G] in
theorem isPGroup_ker_toBarM {M V : Subgroup G} (hVM : V ≤ M) :
    IsPGroup 2 (toBarM hVM).ker := by
  rintro ⟨v, hv⟩
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨v, hVM v.2⟩ = 1 :=
    congrArg Subtype.val (MonoidHom.mem_ker.mp hv)
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥M)) ⟨_, h1⟩
  refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
  have := congrArg (fun x : CFSG.pCore 2 ↥M => ((x : ↥M) : G)) hk
  simpa using this

omit [Finite G] in
theorem exists_surj_barM {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (h3 : 3 ∣ Nat.card Q) {M V : Subgroup G} (hVM : V ≤ M) (ψ : ↥V →* Q)
    (hψ : Function.Surjective ψ) :
    ∃ ψ' : ↥(barM M V) →* Q, Function.Surjective ψ' ∧ Nat.card ψ'.ker ∣ Nat.card ψ.ker := by
  obtain ⟨ψ', hs, hk⟩ := exists_factor (toBarM hVM) (toBarM_surjective hVM) ψ hψ
    (le_ker_of_isPGroup_two h3 ψ hψ (isPGroup_ker_toBarM hVM))
  exact ⟨ψ', hs, (Subgroup.card_dvd_of_le hk).trans (Subgroup.card_map_dvd _ _)⟩

end BarM

theorem card_eq_of_quotient_pCore {X Q : Type*} [Group X] [Group Q] [Finite X]
    (e : X ⧸ CFSG.pCore 2 X ≃* Q) : ∃ a : ℕ, Nat.card X = 2 ^ a * Nat.card Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := X))
  exact ⟨a, by rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 X),
    Nat.card_congr e.toEquiv, ha, mul_comm]⟩

theorem dvd_of_dvd_two_pow_mul {p a m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : p ∣ 2 ^ a * m) :
    p ∣ m :=
  (Nat.Coprime.pow_right a ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)).dvd_of_dvd_mul_left h

theorem three_pow_seven_dvd_factorial {n : ℕ} (h : 19 ∣ n.factorial) : 3 ^ 7 ∣ n.factorial := by
  have h19 : 19 ≤ n := (Nat.Prime.dvd_factorial (by norm_num)).mp h
  exact (show 3 ^ 7 ∣ (19 : ℕ).factorial by decide).trans (Nat.factorial_dvd_factorial h19)

theorem three_pow_seven_dvd_ordBC {k : ℕ} (h : 19 ∣ ordBC k 2) : 3 ^ 7 ∣ ordBC k 2 := by
  unfold ordBC at h ⊢
  rw [show Nat.gcd 2 (2 - 1) = 1 by norm_num, Nat.div_one] at h ⊢
  have hP := dvd_of_dvd_two_pow_mul (by norm_num) (by norm_num) h
  obtain ⟨i, hi, hi19⟩ := (Prime.dvd_finsetProd_iff (Nat.prime_iff.mp (by norm_num)) _).mp hP
  have hi9 : 9 ≤ i := by
    by_contra hlt
    have hi1 := (Finset.mem_Icc.mp hi).1
    interval_cases i <;> revert hi19 <;> decide
  have hk : 9 ≤ k := le_trans hi9 (Finset.mem_Icc.mp hi).2
  refine Dvd.dvd.mul_left ((show 3 ^ 7 ∣ ∏ i ∈ Finset.Icc 1 6, (2 ^ (2 * i) - 1) by decide).trans
    (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.Icc_subset_Icc le_rfl (by omega)))) _

end LeviBlock

theorem kFactBlockNoSU38_of (hTPL : CitedBlockTransvectionPL) (hA7 : CitedBlockAltSevenPL)
    (hC : KFactCompParabSU38) : KFactBlockNoSU38 := by
  intro G _ _ M S L hK hA hL h93 hX hS _ O V hVM hO hV hPO hOc hPVO hVV d ψ hd hψ
  have hd' := hd
  obtain ⟨q, hqp, -, hdq⟩ := hd'
  have : IsSimpleGroup (CatGroup d) := unitaryTarget_isSimpleGroup ⟨q, hqp, hdq⟩
  have : Finite (CatGroup d) := Finite.of_surjective ψ hψ
  obtain ⟨ψ', hψ', -⟩ :=
    LeviBlock.exists_surj_barM (by rw [LeviBlock.card_catGroup_u38 hd]; norm_num) hVM ψ hψ
  have h19 : 19 ∣ Nat.card (blockParabolic M S L) :=
    (((show 19 ∣ Nat.card (CatGroup d) by rw [LeviBlock.card_catGroup_u38 hd]; norm_num).trans
      (Subgroup.card_dvd_of_surjective hψ')).trans (Subgroup.card_dvd_of_le hV))
  rcases h93 with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact absurd h1 hX
  · exact hC _ _ _ (LeviBlock.compParab_of_nineThreeTwo hA hL hS h2) O (barM M V) hO hPO hOc hV
      hPVO (commutator_barM_eq_self hVM hVV) d ψ' hd hψ'
  · rcases hTPL G M S L hK hA hL hX hS h3 with ⟨k, d', hk, ⟨q', hq', hdq'⟩, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
    · obtain ⟨a, ha⟩ := LeviBlock.card_eq_of_quotient_pCore e
      have hq2 : q'.p = 2 ∧ q'.exponent = 1 := by
        rw [TauCeti.PrimePower.card_def] at hq'
        exact Nat.prime_two.pow_eq_iff.mp hq'
      have hN : Nat.card (CatGroup d') = ordBC k 2 := by
        rw [card_catGroup_B_even hk hq2.1 hdq', hq2.2, pow_one]
      change Nat.card (blockParabolic M S L) = 2 ^ a * Nat.card (CatGroup d') at ha
      rw [ha, hN] at h19 ⊢
      exact Dvd.dvd.mul_left (LeviBlock.three_pow_seven_dvd_ordBC
        (LeviBlock.dvd_of_dvd_two_pow_mul (by norm_num) (by norm_num) h19)) _
    · exfalso
      obtain ⟨a, ha⟩ := LeviBlock.card_eq_of_quotient_pCore e
      change Nat.card (blockParabolic M S L) = 2 ^ a * Nat.card (Equiv.Perm (Fin n)) at ha
      rw [ha, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at h19
      have := (Nat.Prime.dvd_factorial (by norm_num)).mp
        (LeviBlock.dvd_of_dvd_two_pow_mul (by norm_num) (by norm_num) h19)
      omega
  · exact absurd (h19.trans (card_blockPL_dvd_of_nineThreeFour h4)) (by norm_num)
  · exact absurd (h19.trans (hA7 G M S L hK hA hL hX hS h5)) (by norm_num)
  · obtain ⟨-, n, -, ⟨e⟩⟩ := h6
    obtain ⟨a, ha⟩ := LeviBlock.card_eq_of_quotient_pCore e
    change Nat.card (blockParabolic M S L) = 2 ^ a * Nat.card (Equiv.Perm (Fin n)) at ha
    rw [ha, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at h19 ⊢
    exact Dvd.dvd.mul_left (LeviBlock.three_pow_seven_dvd_factorial
      (LeviBlock.dvd_of_dvd_two_pow_mul (by norm_num) (by norm_num) h19)) _
  · obtain ⟨-, n, -, ⟨e⟩⟩ := h7
    obtain ⟨a, ha⟩ := LeviBlock.card_eq_of_quotient_pCore e
    change Nat.card (blockParabolic M S L) = 2 ^ a * Nat.card (Equiv.Perm (Fin n)) at ha
    rw [ha, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at h19 ⊢
    exact Dvd.dvd.mul_left (LeviBlock.three_pow_seven_dvd_factorial
      (LeviBlock.dvd_of_dvd_two_pow_mul (by norm_num) (by norm_num) h19)) _
  · obtain ⟨-, N, r, -, -, -, -, -, -, φ, -⟩ := h8
    obtain ⟨a, ha⟩ := LeviBlock.card_eq_of_quotient_pCore φ
    change Nat.card (blockParabolic M S L) =
      2 ^ a * Nat.card (Equiv.Perm (Fin r) × Equiv.Perm (Fin (N - 2 * r))) at ha
    rw [ha, Nat.card_prod, Nat.card_perm, Nat.card_perm, Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_fin] at h19 ⊢
    have h19' := LeviBlock.dvd_of_dvd_two_pow_mul (by norm_num) (by norm_num) h19
    rcases (Nat.Prime.dvd_mul (by norm_num)).mp h19' with h | h
    · exact Dvd.dvd.mul_left
        (Dvd.dvd.mul_right (LeviBlock.three_pow_seven_dvd_factorial h) _) _
    · exact Dvd.dvd.mul_left
        (Dvd.dvd.mul_left (LeviBlock.three_pow_seven_dvd_factorial h) _) _

theorem kFactBlockThreeFivesParabolic_of (h : KFactCompParabThreeFives) :
    KFactBlockThreeFivesParabolic := by
  intro G _ _ M S L _ hA hL _ hS h2 O J hO hN h5 hsec hJ hcomm
  exact h _ _ _ (LeviBlock.compParab_of_nineThreeTwo hA hL hS h2) O J hO hN h5 hsec hJ hcomm

end CFSG.AGLEmbedding
