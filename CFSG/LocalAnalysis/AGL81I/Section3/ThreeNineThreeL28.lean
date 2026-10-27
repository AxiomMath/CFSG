module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineThreeM11
public import CFSG.GH74.KGroups.L28
public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaPlus.Groups.PSL2
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporOrder
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineThreeFamilies

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.Open CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem perm_fin_nine_orderOf_ne_21 (σ : Equiv.Perm (Fin 9)) : orderOf σ ≠ 21 := by
  intro h
  have hl : σ.cycleType.lcm = 21 := by rw [Equiv.Perm.lcm_cycleType, h]
  have hsum : σ.cycleType.sum ≤ 9 := by
    rw [Equiv.Perm.sum_cycleType]
    exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin 9)
  have hmem : ∀ n ∈ σ.cycleType, n = 3 ∨ n = 7 := by
    intro n hn
    have h1 : n ∣ 21 := h ▸ Equiv.Perm.dvd_of_mem_cycleType hn
    have h2 : 2 ≤ n := Equiv.Perm.two_le_of_mem_cycleType hn
    have h3 : n ≤ 9 := (Multiset.le_sum_of_mem hn).trans hsum
    interval_cases n <;> omega
  have h7 : 7 ∈ σ.cycleType := by
    by_contra h7
    have : σ.cycleType.lcm ∣ 3 := Multiset.lcm_dvd.mpr fun n hn => by
      rcases hmem n hn with rfl | rfl
      · exact dvd_rfl
      · exact absurd hn h7
    rw [hl] at this
    norm_num at this
  have h3 : 3 ∈ σ.cycleType := by
    by_contra h3
    have : σ.cycleType.lcm ∣ 7 := Multiset.lcm_dvd.mpr fun n hn => by
      rcases hmem n hn with rfl | rfl
      · exact absurd hn h3
      · exact dvd_rfl
    rw [hl] at this
    norm_num at this
  have h3' : 3 ∈ σ.cycleType.erase 7 := (Multiset.mem_erase_of_ne (by norm_num)).mpr h3
  have he := Multiset.sum_erase h7
  have hle := Multiset.le_sum_of_mem h3'
  omega

theorem exists_orderOf_eq_21_of_card_eq_63 {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 63) : ∃ x : G, orderOf x = 21 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let P : Sylow 7 G := default
  have h7 : (7 : ℕ) ^ (63 : ℕ).factorization 7 = 7 :=
    (pow_eq_pow_factorization_of_eq (a := 1) (k := 9) (by norm_num) (by norm_num)
      (by norm_num)).symm
  have hP : Nat.card (P : Subgroup G) = 7 := by
    rw [Sylow.card_eq_multiplicity, hG, h7]
  have hidx : (P : Subgroup G).index = 9 := by
    have := (P : Subgroup G).card_mul_index
    rw [hP, hG] at this
    omega
  have hn1 : (Subgroup.normalizer ((P : Subgroup G) : Set G)).index = 1 := by
    have hmod := card_sylow_modEq_one (p := 7) (G := G)
    have hdvd := Sylow.card_dvd_index P
    have e1 : Nat.card (Sylow 7 G) =
        (Subgroup.normalizer ((P : Subgroup G) : Set G)).index := Sylow.card_eq_index_normalizer P
    rw [hidx] at hdvd
    rw [← e1]
    have key : ∀ m ∈ Nat.divisors 9, m ≡ 1 [MOD 7] → m = 1 := by decide
    exact key _ (Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩) hmod
  have hNtop : Subgroup.normalizer ((P : Subgroup G) : Set G) = ⊤ := Subgroup.index_eq_one.mp hn1
  set H : Subgroup G := (P : Subgroup G) with hH
  let f := H.normalizerMonoidHom
  have hNcard : Nat.card (Subgroup.normalizer (H : Set G)) = 63 := by
    rw [hNtop, Subgroup.card_top, hG]
  have hcard : Nat.card (Subgroup.normalizer (H : Set G)) = Nat.card f.range * Nat.card f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  have hAut : Nat.card (MulAut H) = 6 := by
    haveI : IsCyclic H := isCyclic_of_prime_card hP
    rw [IsCyclic.card_mulAut, hP]
    decide
  have hr : Nat.card f.range ∣ 6 := hAut ▸ Subgroup.card_subgroup_dvd_card f.range
  have h3ker : 3 ∣ Nat.card f.ker := by
    have hrk : Nat.card f.range * Nat.card f.ker = 63 := hcard.symm.trans hNcard
    have hr6 : Nat.card f.range ≤ 6 := Nat.le_of_dvd (by norm_num) hr
    have hr0 : 0 < Nat.card f.range := Nat.card_pos
    interval_cases hrc : Nat.card f.range <;> omega
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := f.ker) 3 h3ker
  have hyC : ((y : Subgroup.normalizer (H : Set G)) : G) ∈ Subgroup.centralizer (H : Set G) := by
    have hmem : (y : Subgroup.normalizer (H : Set G)) ∈
        (Subgroup.centralizer (H : Set G)).subgroupOf (Subgroup.normalizer (H : Set G)) := by
      rw [← Subgroup.normalizerMonoidHom_ker]
      exact y.2
    exact Subgroup.mem_subgroupOf.mp hmem
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := H) 7 (hP ▸ dvd_rfl : 7 ∣ Nat.card H)
  refine ⟨(x : G) * ((y : Subgroup.normalizer (H : Set G)) : G), ?_⟩
  have hcomm : Commute (x : G) ((y : Subgroup.normalizer (H : Set G)) : G) :=
    Subgroup.mem_centralizer_iff.mp hyC (x : G) x.2
  have hx' : orderOf (x : G) = 7 := by rw [Subgroup.orderOf_coe, hx]
  have hy' : orderOf ((y : Subgroup.normalizer (H : Set G)) : G) = 3 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hy]
  rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hx', hy']; norm_num), hx', hy']

variable {X : Type} [Group X] [Finite X] {K E D X₁ : Subgroup X} {d : ℕ}

theorem false_of_threeNineHyp_L28 (h : ThreeNineHyp K E D X₁ 3 d)
    (hK : StatedClassicalModel ↥K .PSL 2 2 3) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact d.Prime := ⟨h.d_prime⟩
  have : K.Normal := h.normal
  obtain ⟨e2⟩ := CFSG.GH74.KGroups.PSL2.psl2_equiv_of_stated (F := GaloisField 2 3) 2 3
    (by norm_num) (GaloisField.card 2 3 (by norm_num)) hK
  have hsimple : IsSimpleGroup ↥K :=
    CFSG.GF2Type.Smith1979.OmegaPlus.isSimpleGroup_of_mulEquiv_psl28 e2
  have hcard : Nat.card ↥K = 504 := by
    rw [Nat.card_congr e2.toEquiv, CFSG.Walter.psl2_even_card (f := 3) (by norm_num)]
    norm_num
  have hZ : Subgroup.center ↥K = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center ↥K) with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨a, b, hab⟩ := CFSG.GF2Type.Smith1979.OmegaPlus.exists_ne_comm_of_mulEquiv_psl28 e2
      exact hab ((Subgroup.mem_center_iff.mp (h1 ▸ Subgroup.mem_top b)) a)
  have hOut : Nat.card (Outer ↥K) = 3 := by
    have hAut := CFSG.GF2Type.Smith1979.OmegaPlus.card_mulAut_of_mulEquiv_psl28 e2
    have hinn := CFSG.Sporadic.Schreier.card_inner_of_center_eq_bot hZ
    have hq := (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥K).card_eq_card_quotient_mul_card_subgroup
    change Nat.card (MulAut ↥K ⧸ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥K) = 3
    rw [hAut, hinn, hcard] at hq
    omega
  have hdOut : ¬ d ∣ Nat.card (Outer ↥K) := by
    rw [hOut]
    intro hd
    exact h.d_ne ((Nat.prime_dvd_prime_iff_eq h.d_prime Nat.prime_three).mp hd)
  have hDK : D ≤ K := h.D_le_K_of_not_dvd hZ hdOut
  obtain ⟨SD, hSD⟩ := h.exists_sylow_normalizer_le hZ hdOut
  have hmd := index_modEq_one_of_normalizer_le SD hSD
  obtain ⟨hdY, -⟩ := h.dvd_card_of_subgroupOf_le hDK le_rfl
  have hdK : d ∣ 504 := hcard ▸ (hdY.trans (Subgroup.card_subgroup_dvd_card _))
  have hd7 : d = 7 := by
    have hfac : (504 : ℕ) = 2 ^ 3 * 3 ^ 2 * 7 := by norm_num
    rw [hfac] at hdK
    rcases (Nat.Prime.dvd_mul h.d_prime).mp hdK with h1 | h1
    · rcases (Nat.Prime.dvd_mul h.d_prime).mp h1 with h1 | h1
      · exact absurd ((Nat.prime_dvd_prime_iff_eq h.d_prime Nat.prime_two).mp
          (h.d_prime.dvd_of_dvd_pow h1)) h.d_ne_two
      · exact absurd ((Nat.prime_dvd_prime_iff_eq h.d_prime Nat.prime_three).mp
          (h.d_prime.dvd_of_dvd_pow h1)) h.d_ne
    · exact (Nat.prime_dvd_prime_iff_eq h.d_prime (by norm_num)).mp h1
  subst hd7
  obtain ⟨Q, hEQ⟩ := (CFSG.Open.IsElemAbelian.isPGroup h.elem).exists_le_sylow
  have hQtop : CFSG.ABGLocalTools.IsSylowOf 3 (Q : Subgroup X) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_top, Q.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact Q.not_dvd_index
  have hQK : CFSG.ABGLocalTools.IsSylowOf 3 ((Q : Subgroup X) ⊓ K) K :=
    hQtop.inf_of_le_normalizer le_top (by rw [Subgroup.normalizer_eq_top_iff.mpr h.normal])
  have hQcard := hQK.card_eq
  have hQY : ((Q : Subgroup X) ⊓ K).subgroupOf K ≤ X₁.subgroupOf K := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact h.normQ Q Q.isPGroup' hEQ
      (Subgroup.mem_inf.mpr ⟨Subgroup.le_normalizer (Subgroup.mem_inf.mp hx).1,
        le_sup_left (a := K) (Subgroup.mem_inf.mp hx).2⟩)
  have h9 : (3 : ℕ) ^ (504 : ℕ).factorization 3 = 9 :=
    (pow_eq_pow_factorization_of_eq (a := 2) (k := 56) Nat.prime_three (by norm_num)
      (by norm_num)).symm
  have h9Y : 9 ∣ Nat.card (X₁.subgroupOf K) := by
    have := Subgroup.card_dvd_of_le hQY
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, hQcard, hcard,
      h9] at this
  have h63 : 63 ∣ Nat.card (X₁.subgroupOf K) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 9 7) h9Y hdY
  have hY1 : (X₁.subgroupOf K).index ≠ 1 := fun h1 => by
    apply h.not_K_le
    intro x hx
    have : (⟨x, hx⟩ : ↥K) ∈ X₁.subgroupOf K := (Subgroup.index_eq_one.mp h1) ▸ Subgroup.mem_top _
    exact this
  have hidx := index_dvd_div_of_dvd_card h63
  rw [hcard] at hidx
  have key : ∀ m ∈ Nat.divisors 8, m ≡ 1 [MOD 7] → m ≠ 1 → m = 8 := by decide
  have h8 := key _ (Nat.mem_divisors.mpr ⟨hidx, by norm_num⟩) hmd hY1
  have hYcard : Nat.card (X₁.subgroupOf K) = 63 := by
    have hmul := (X₁.subgroupOf K).card_mul_index
    rw [hcard, h8] at hmul
    omega
  obtain ⟨y, hy⟩ := exists_orderOf_eq_21_of_card_eq_63 hYcard
  obtain ⟨e⟩ := CFSG.GH74.KGroups.L28.equiv_of_lieModel (K := ↥K) (Or.inl ⟨by decide, hK⟩)
  apply perm_fin_nine_orderOf_ne_21 ((e (y : ↥K) : CFSG.GH74.KGroups.L28.QP.originalSubgroup) :
    Equiv.Perm (Fin 9))
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hy]

theorem threeNineThreeL28_holds : ThreeNineThreeL28 :=
  fun _ _ _ _ _ _ _ _ h hK => false_of_threeNineHyp_L28 h hK

end CFSG.LocalAnalysis.AGL81I.Section3
