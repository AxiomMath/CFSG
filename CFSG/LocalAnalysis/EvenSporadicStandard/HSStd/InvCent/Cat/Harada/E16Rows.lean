module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.AutBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HOvL2
public import CFSG.GH74.Uniqueness.Bender.Core
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.Parts
public import Certificates.Data.A5

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent.Harada

open Subgroup CFSG.ComponentClassification.OuterAutomorphisms Equiv.Perm CFSG.GorensteinWalter
open CFSG.GH74.Uniqueness.Bender

theorem card_zpowers_sup_zpowers {G : Type*} [Group G] [Finite G] {a b : G}
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : a * b = b * a) (hne : a ≠ b) :
    Nat.card ↥(zpowers a ⊔ zpowers b) = 4 := by
  have hcomm : ∀ x ∈ zpowers a, ∀ y ∈ zpowers b, x * y = y * x := by
    rintro x ⟨m, rfl⟩ y ⟨n, rfl⟩
    exact (Commute.zpow_zpow (show Commute a b from hab) m n).eq
  have hdisj : zpowers a ⊓ zpowers b = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxa, hxb⟩
    rw [Subgroup.mem_bot]
    rcases eq_one_or_eq_of_mem_zpowers (mul_self_eq_one_of_orderOf_eq_two ha) hxa with h | h
    · exact h
    · rcases eq_one_or_eq_of_mem_zpowers (mul_self_eq_one_of_orderOf_eq_two hb) hxb with h' | h'
      · exact h'
      · exact absurd (h.symm.trans h') hne
  rw [card_sup_eq_mul_of_commute hcomm hdisj, Nat.card_zpowers, Nat.card_zpowers, ha, hb]

theorem isElemAbelian_closure_of_commute {G : Type*} [Group G] {k : Set G}
    (hcomm : k.Pairwise Commute) (hsq : ∀ x ∈ k, x * x = 1) :
    CFSG.Open.IsElemAbelian 2 (closure k) := by
  have : IsMulCommutative (closure k) := isMulCommutative_closure hcomm
  refine ⟨this, fun x hx => ?_⟩
  have hc : ∀ y ∈ closure k, ∀ z ∈ closure k, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨y, hy⟩ : closure k) ⟨z, hz⟩)
  have key : x * x = 1 := by
    refine closure_induction (p := fun y _ => y * y = 1) (fun y hy => hsq y hy) ?_ ?_ ?_ hx
    · simp
    · intro y z hy hz hy2 hz2
      calc y * z * (y * z) = y * (z * y) * z := by group
        _ = y * (y * z) * z := by rw [← hc y hy z hz]
        _ = (y * y) * (z * z) := by group
        _ = 1 := by rw [hy2, hz2, one_mul]
    · intro y hy hy2
      calc y⁻¹ * y⁻¹ = (y * y)⁻¹ := by group
        _ = 1 := by rw [hy2, inv_one]
  simpa [pow_two] using key

namespace TwoCfg

variable {G : Type*} [Group G] [Finite G] {t v : G} {J : Subgroup G} (h : TwoCfg t v J)

include h

theorem exists_elemAbelian_sixteen (htop : centralizer ({t} : Set G) ≠ ⊤) :
    ∃ A : Subgroup G, CFSG.Open.IsElemAbelian 2 A ∧ Nat.card ↥A = 16 := by
  obtain ⟨e⟩ := h.hJ
  have hι := embJ_injective J e
  set p : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 2 3 with hp
  set q : Equiv.Perm (Fin 5) := Equiv.swap 0 2 * Equiv.swap 1 3 with hq
  set a : G := embJ J e p with ha
  set b : G := embJ J e q with hb
  have hpp : p * p = 1 := by rw [hp]; decide
  have hqq : q * q = 1 := by rw [hq]; decide
  have hpq : p * q = q * p := by rw [hp, hq]; decide
  have hp1 : p ≠ 1 := by rw [hp]; decide
  have hq1 : q ≠ 1 := by rw [hq]; decide
  have hpq' : p ≠ q := by rw [hp, hq]; decide
  have haa : a * a = 1 := by rw [ha, ← map_mul, hpp, map_one]
  have hbb : b * b = 1 := by rw [hb, ← map_mul, hqq, map_one]
  have hab : a * b = b * a := by rw [ha, hb, ← map_mul, ← map_mul, hpq]
  have ha1 : a ≠ 1 := fun h1 => hp1 (hι (by rw [← ha, h1, map_one]))
  have hb1 : b ≠ 1 := fun h1 => hq1 (hι (by rw [← hb, h1, map_one]))
  have hne : a ≠ b := fun h1 => hpq' (hι h1)
  have hao : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact haa) ha1
  have hbo : orderOf b = 2 := orderOf_eq_prime (by rw [sq]; exact hbb) hb1
  have haJ : a ∈ J := embJ_mem J e p
  have hbJ : b ∈ J := embJ_mem J e q
  set W : Subgroup G := zpowers a ⊔ zpowers b with hW
  have hWJ : W ≤ J := sup_le ((zpowers_le).2 haJ) ((zpowers_le).2 hbJ)
  have hWcard : Nat.card W = 4 := card_zpowers_sup_zpowers hao hbo hab hne
  have hVW : ∀ x ∈ fourGroup t v, ∀ y ∈ W, x * y = y * x := fun x hx y hy => h.hcomm x hx y (hWJ hy)
  have hVWdisj : fourGroup t v ⊓ W = ⊥ := by
    rw [eq_bot_iff]
    exact (inf_le_inf_left _ hWJ).trans h.hdisj.le
  refine ⟨fourGroup t v ⊔ W, ?_, ?_⟩
  · have hE : fourGroup t v ⊔ W = closure ({t, v, a, b} : Set G) := by
      refine le_antisymm (sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)) ?_
      · exact (zpowers_le).2 (subset_closure (by simp))
      · exact (zpowers_le).2 (subset_closure (by simp))
      · exact (zpowers_le).2 (subset_closure (by simp))
      · exact (zpowers_le).2 (subset_closure (by simp))
      · refine (closure_le _).2 ?_
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with hx | hx | hx | hx <;> rw [hx]
        · exact mem_sup_left (mem_sup_left (mem_zpowers t))
        · exact mem_sup_left (mem_sup_right (mem_zpowers v))
        · exact mem_sup_right (mem_sup_left (mem_zpowers a))
        · exact mem_sup_right (mem_sup_right (mem_zpowers b))
    rw [hE]
    have ctv : Commute t v := h.tv_comm
    have cta : Commute t a :=
      h.hcomm t (h.mem_fourGroup.2 (Or.inr (Or.inl rfl))) a haJ
    have ctb : Commute t b :=
      h.hcomm t (h.mem_fourGroup.2 (Or.inr (Or.inl rfl))) b hbJ
    have cva : Commute v a :=
      h.hcomm v (h.mem_fourGroup.2 (Or.inr (Or.inr (Or.inl rfl)))) a haJ
    have cvb : Commute v b :=
      h.hcomm v (h.mem_fourGroup.2 (Or.inr (Or.inr (Or.inl rfl)))) b hbJ
    have cab : Commute a b := hab
    refine isElemAbelian_closure_of_commute ?_ ?_
    · intro x hx y hy _
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy <;> rw [hx, hy] <;>
        first | exact Commute.refl _ | assumption | (apply Commute.symm; assumption)
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx | hx | hx <;> rw [hx]
      · exact h.t_sq
      · exact h.hv
      · exact haa
      · exact hbb
  · rw [card_sup_eq_mul_of_commute hVW hVWdisj, h.card_fourGroup htop, hWcard]

end TwoCfg

theorem no_E16_of_normal {D : Type*} [Group D] [Finite D] (S : Subgroup D) [S.Normal]
    (hC : centralizer (S : Set D) = ⊥)
    (hS : ∀ E : Subgroup ↥S, CFSG.Open.IsElemAbelian 2 E → Nat.card E ≤ 4) (m : ℕ)
    (hm : Nat.card (Outer ↥S) ∣ m) (hm2 : ∀ k : ℕ, 2 ^ k ∣ m → 2 ^ k ≤ 2) :
    ¬ ∃ A : Subgroup D, CFSG.Open.IsElemAbelian 2 A ∧ Nat.card ↥A = 16 := by
  rintro ⟨A, hA, hcard⟩
  have hA2 : ∀ a ∈ A, a * a = 1 := fun a ha => by simpa [pow_two] using hA.2 a ha
  obtain ⟨r, hr, hrdvd, k, hk⟩ :=
    CFSG.EvenSporadicStandard.HSStd.HOv.exists_card_eq_mul_outer S hC hA2
  have hr2 : r ≤ 2 := by rw [hk]; exact hm2 k (hk ▸ hrdvd.trans hm)
  have hAS : Nat.card ↥(A ⊓ S) ≤ 4 := by
    have h1 := hS _ (CFSG.EvenSporadicStandard.HSStd.HOv.isElemAbelian_subgroupOf_inf S hA)
    exact (Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : A ⊓ S ≤ S)).toEquiv).symm.le.trans h1
  have : 16 ≤ 4 * 2 := by rw [← hcard, hr]; exact Nat.mul_le_mul hAS hr2
  omega

theorem no_E16_of_L35 {D : Type} [Group D] [Finite D] (S : Subgroup D) [S.Normal]
    (hC : centralizer (S : Set D) = ⊥) (hL : CFSG.Blueprint.LieModel ↥S .PSL 3 5 1) :
    ¬ ∃ A : Subgroup D, CFSG.Open.IsElemAbelian 2 A ∧ Nat.card ↥A = 16 := by
  have hM := CFSG.EvenSporadicStandard.HSStd.HOv.statedClassicalModel_of_lieModel (by norm_num) hL
  obtain ⟨-, -, -, -, hout⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound ↥S 3 5 1 hM
  refine no_E16_of_normal S hC
    (fun E hE => CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_elemAbelian_two_le_four_of_PSL3
      (by norm_num) (by norm_num) hL E hE) 2 ?_ (fun k hk => Nat.le_of_dvd (by norm_num) hk)
  have h := hout le_rfl
  have h2 : 2 * 1 * Nat.gcd 3 (5 ^ 1 - 1) = 2 := by decide
  rwa [h2] at h

theorem no_E16_of_U35 {D : Type} [Group D] [Finite D] (S : Subgroup D) [S.Normal]
    (hC : centralizer (S : Set D) = ⊥) (hL : CFSG.Blueprint.LieModel ↥S .PSU 3 5 1) :
    ¬ ∃ A : Subgroup D, CFSG.Open.IsElemAbelian 2 A ∧ Nat.card ↥A = 16 := by
  have hM := CFSG.EvenSporadicStandard.HSStd.HOv.statedClassicalModel_of_lieModel (by norm_num) hL
  have hout := (CFSG.LocalAnalysis.ComponentInitial.unitary_model_outer_two_part_bound ↥S 3 5 1
    hM).2.2.1
  have h6 : 2 * 1 * Nat.gcd 3 (5 ^ 1 + 1) = 6 := by decide
  rw [h6] at hout
  refine no_E16_of_normal S hC ?_ 6 (by rw [hout]) ?_
  · intro E hE
    obtain ⟨k, hk, hkr⟩ := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_le_of_pRank hE
    have := CFSG.Quasithin.H13.KGInsp4316.pRank_two_le_two_of_psu3_odd (by norm_num)
      (by norm_num) hM
    rw [hk]
    exact Nat.pow_le_pow_right (by norm_num) (hkr.trans this) |>.trans (by norm_num)
  · intro k hk
    have h1 : 2 ^ k ≤ 6 := Nat.le_of_dvd (by norm_num) hk
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · interval_cases k <;> norm_num
    · have h2 : 2 ^ 2 ∣ 2 ^ k := pow_dvd_pow 2 hk2
      have h3 := dvd_trans h2 hk
      norm_num at h3

theorem no_E16_of_L225 {D : Type} [Group D] [Finite D] (S : Subgroup D) [S.Normal]
    (hC : centralizer (S : Set D) = ⊥) (hL : CFSG.Blueprint.LieModel ↥S .PSL 2 5 2) :
    ¬ ∃ A : Subgroup D, CFSG.Open.IsElemAbelian 2 A ∧ Nat.card ↥A = 16 := by
  rintro ⟨A, hA, hcardA⟩
  have hM := CFSG.EvenSporadicStandard.HSStd.HOv.statedClassicalModel_of_lieModel (by norm_num) hL
  obtain ⟨-, K, _, _, hK, ⟨e1⟩⟩ := hM
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hK25 : Nat.card K = 5 ^ 2 := hK
  have hodd : IsOddPrimePower (Nat.card K) := ⟨5, 2, by norm_num, by decide, by norm_num, hK25⟩
  have h3 : 3 < Nat.card K := by rw [hK25]; norm_num
  let φ : ↥S ≃* PSL2 K :=
    e1.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  let Φ : PGammaL2 K ≃* MulAut (PSL2 K) := MulEquiv.ofBijective
    (pGammaL2ToMulAutPSL2 K hodd h3)
    ⟨pGammaL2ToMulAutPSL2_injective K hodd h3, pGammaL2ToMulAutPSL2_surjective K hK25 hodd h3⟩
  let ι : D →* PGammaL2 K := Φ.symm.toMonoidHom.comp (HL34.actionHom S φ)
  have hι : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro d hd
    have h1 : HL34.actionHom S φ d = 1 := by
      have : Φ.symm (HL34.actionHom S φ d) = 1 := hd
      exact Φ.symm.injective (this.trans (map_one _).symm)
    have h2 := (HL34.actionHom_eq_one_iff S φ d).1 h1
    rw [hC, mem_bot] at h2
    exact h2
  have hA' : ∀ x ∈ A.map ι, x ^ 2 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hA.2 a ha, map_one]
  have := CFSG.EvenSporadicStandard.HSStd.HOv.card_le_eight_of_pGammaL2 K
    (by norm_num : Nat.Prime 5) hK25 hodd (A.map ι) hA'
  rw [Subgroup.card_map_of_injective hι, hcardA] at this
  omega

theorem noTwoCfgL225_holds : NoTwoCfgL225 := by
  intro G _ _ S hSn hS hcent t v J h _
  haveI := hSn
  have htop : centralizer ({t} : Set G) ≠ ⊤ := centralizer_singleton_ne_top hcent h.t_ne_one
  exact no_E16_of_L225 S hcent hS (h.exists_elemAbelian_sixteen htop)

theorem noTwoCfgL35_holds : NoTwoCfgL35 := by
  intro G _ _ S hSn hS hcent t v J h _
  haveI := hSn
  have htop : centralizer ({t} : Set G) ≠ ⊤ := centralizer_singleton_ne_top hcent h.t_ne_one
  exact no_E16_of_L35 S hcent hS (h.exists_elemAbelian_sixteen htop)

theorem noTwoCfgU35_holds : NoTwoCfgU35 := by
  intro G _ _ S hSn hS hcent t v J h _
  haveI := hSn
  have htop : centralizer ({t} : Set G) ≠ ⊤ := centralizer_singleton_ne_top hcent h.t_ne_one
  exact no_E16_of_U35 S hcent hS (h.exists_elemAbelian_sixteen htop)

end CFSG.EvenSporadicStandard.HSStd.InvCent.Harada
