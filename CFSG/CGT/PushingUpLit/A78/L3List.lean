module

public import CFSG.CGT.PushingUpLit.A78.L3WC
import CFSG.Adapters.WholeGroupLayer
public import CFSG.CGT.Timmesfeld75.SimpleCase
public import CFSG.CGT.Timmesfeld75.StdPair
public import CFSG.RankThree.PartOne.S12.ModelTransport
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.Foundations.Basic

public section

namespace CFSG.CGT.PushingUpLit.A78

open CFSG.CGT.Timmesfeld75 CFSG.Timmesfeld.ARS

variable {G : Type} [Group G] [Finite G] {J V V₂ Z : Subgroup G} {e : ℕ}

section Sylow

theorem card_eq_of_sylow_two {P : Subgroup G} (hP : IsPGroup 2 P) (hPi : ¬ 2 ∣ P.index) :
    Nat.card P = 2 ^ (Nat.card G).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  simpa using (hP.toSylow hPi).card_eq_multiplicity

theorem two_pow_le_card_of_sylow {P : Subgroup G} (hP : IsPGroup 2 P) (hPi : ¬ 2 ∣ P.index)
    {k : ℕ} (hk : 2 ^ k ∣ Nat.card G) : 2 ^ k ≤ Nat.card P := by
  rw [card_eq_of_sylow_two hP hPi]
  exact Nat.pow_le_pow_right (by norm_num)
    ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 hk)

theorem card_center_eq_of_sylow {P Q : Subgroup G} (hP : IsPGroup 2 P) (hPi : ¬ 2 ∣ P.index)
    (hQ : IsPGroup 2 Q) (hQi : ¬ 2 ∣ Q.index) :
    Nat.card (Subgroup.center P) = Nat.card (Subgroup.center Q) := by
  obtain ⟨n, -, hn⟩ := exists_conj_of_sylow_le (N := ⊤) hP hPi hQ hQi le_top le_top
  subst hn
  let φ : ↥P ≃* ↥(conjSub P n) := MulEquiv.subgroupMap (MulAut.conj n) P
  have h1 : (Subgroup.center ↥P).map φ.toMonoidHom = Subgroup.center ↥(conjSub P n) :=
    Subgroup.map_center_eq φ
  rw [← h1]
  exact (Subgroup.card_map_of_injective φ.injective).symm

end Sylow

section Orders

theorem two_pow_dvd_card_psl' {K : Type} [Field K] [Finite K] {f m : ℕ}
    (hK : Nat.card K = 2 ^ f) (hm : 2 ≤ m) :
    2 ^ (f * (m * (m - 1) / 2)) ∣
      Nat.card (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL m K)) := by
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by omega)]
  have hgP : Nat.gcd m (Nat.card K - 1) ∣ ∏ j ∈ Finset.Icc 2 m, (Nat.card K ^ j - 1) := by
    have h1 : Nat.gcd m (Nat.card K - 1) ∣ Nat.card K - 1 := Nat.gcd_dvd_right _ _
    have h2 : Nat.card K - 1 ∣ Nat.card K ^ 2 - 1 := by
      simpa using Nat.sub_dvd_pow_sub_pow (Nat.card K) 1 2
    have h3 : Nat.card K ^ 2 - 1 ∣ ∏ j ∈ Finset.Icc 2 m, (Nat.card K ^ j - 1) :=
      Finset.dvd_prod_of_mem (fun j => Nat.card K ^ j - 1) (Finset.mem_Icc.2 ⟨le_refl 2, hm⟩)
    exact h1.trans (h2.trans h3)
  have hq : Nat.card K ^ (m * (m - 1) / 2) = 2 ^ (f * (m * (m - 1) / 2)) := by
    rw [hK, ← pow_mul]
  rw [Nat.mul_div_assoc _ hgP, hq]
  exact Dvd.intro _ rfl

end Orders

section Endgame

open CFSG.Assembly.RankThreeEven (projSL)

theorem L3Local.endgame (h : L3Local G J V V₂ Z e) (hSCL : SimpleCaseListStmt)
    (hL : ListWCIdentification) : Nonempty (G ≃* projSL 3 (GaloisField 2 e)) := by
  have := h.simple
  have he3 := h.three_le
  have hV64 : 64 ≤ Nat.card V := by
    rw [h.card_V]
    calc 64 = 2 ^ 6 := by norm_num
      _ ≤ 2 ^ (2 * e) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hwc : IsWC V := h.isWC
  have hlist : ListGroup G := hSCL G h.nonabelian V hwc (by omega)
  have hstd : StdPair G V := hL G hlist V hwc (by omega)
  have hJ2 : Nat.card J = 2 ^ (Nat.card G).factorization 2 :=
    card_eq_of_sylow_two h.pgroup h.odd_index
  have hv2 : (Nat.card G).factorization 2 = 3 * e :=
    Nat.pow_right_injective (le_refl 2) (hJ2.symm.trans h.card_J)
  have sylow_card : ∀ S : Sylow 2 G, Nat.card (S : Subgroup G) = 2 ^ (3 * e) := by
    intro S
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [hv2.symm]
    simpa using S.card_eq_multiplicity
  have center_card : ∀ S : Sylow 2 G, Nat.card (Subgroup.center (S : Subgroup G)) = 2 ^ e := by
    intro S
    rw [card_center_eq_of_sylow S.isPGroup' S.not_dvd_index h.pgroup h.odd_index]
    exact h.card_center_J
  have sylow_case : (∃ S : Sylow 2 G, (S : Subgroup G) = V) → False := by
    rintro ⟨S, hS⟩
    have h1 := sylow_card S
    rw [hS, h.card_V] at h1
    have := Nat.pow_right_injective (le_refl 2) h1
    omega
  have center_case : (∃ S : Sylow 2 G,
      V = (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype) → False := by
    rintro ⟨S, hS⟩
    have h1 : Nat.card V = Nat.card (Subgroup.center (S : Subgroup G)) := by
      rw [hS]
      exact Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
    rw [h.card_V, center_card S] at h1
    have := Nat.pow_right_injective (le_refl 2) h1
    omega
  rcases hlist with ⟨m, s, hm, hs', hmod⟩ | ⟨s, hs', hmod⟩ | ⟨s, hodd, hs3, hmod⟩ |
    ⟨k, hk6, hk9, hk⟩ | hM22 | hM23 | hM24
  · by_cases hm3 : 3 ≤ m
    · obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := id hmod
      have hcardV := (hstd.of_psl hm3 K hK eK).1
      rw [h.card_V] at hcardV
      have h2 : 2 * e = s * (m - 1) := Nat.pow_right_injective (le_refl 2) hcardV
      have hdvd : 2 ^ (s * (m * (m - 1) / 2)) ∣ Nat.card G := by
        rw [Nat.card_congr eK.toEquiv]
        exact two_pow_dvd_card_psl' hK (by omega)
      have hle := two_pow_le_card_of_sylow h.pgroup h.odd_index hdvd
      rw [h.card_J] at hle
      have hle' : s * (m * (m - 1) / 2) ≤ 3 * e := Nat.pow_le_pow_iff_right (by norm_num) |>.1 hle
      have hmn : s * (m * (m - 1) / 2) = m * e := by
        have hev : 2 ∣ m * (m - 1) := (Nat.even_mul_pred_self m).two_dvd
        have h3 : 2 * (m * (m - 1) / 2) = m * (m - 1) := Nat.mul_div_cancel' hev
        have h4 : 2 * (s * (m * (m - 1) / 2)) = 2 * (m * e) := by
          calc 2 * (s * (m * (m - 1) / 2)) = s * (2 * (m * (m - 1) / 2)) := by ring
            _ = s * (m * (m - 1)) := by rw [h3]
            _ = m * (s * (m - 1)) := by ring
            _ = m * (2 * e) := by rw [h2]
            _ = 2 * (m * e) := by ring
        omega
      rw [hmn] at hle'
      have hm3' : m ≤ 3 := by
        by_contra hcon
        push Not at hcon
        have : 3 * e < m * e := Nat.mul_lt_mul_of_pos_right hcon (by omega)
        omega
      have hm' : m = 3 := by omega
      subst hm'
      have hse : s = e := by omega
      subst hse
      exact CFSG.RankThree.PartOne.projSL_of_statedClassicalModel hmod
    · have hm2 : m = 2 := by omega
      subst hm2
      exact (sylow_case (hstd.of_psl2 hmod).2.1).elim
  · exact (center_case (hstd.of_psu3 hs' hmod).2.1).elim
  · exact (center_case (hstd.of_sz hodd hs3 hmod).2.1).elim
  · have hcard := hstd.card_alternating hk6 hk9 hk
    split_ifs at hcard <;> omega
  · have := hstd.card_sporadic (Or.inl hM22)
    omega
  · have := hstd.card_sporadic (Or.inr (Or.inl hM23))
    omega
  · have := hstd.card_sporadic (Or.inr (Or.inr hM24))
    omega

theorem L3Local.endgame_fitting (h : L3Local G J V V₂ Z e) (hSCL : SimpleCaseListStmt)
    (hL : ListWCIdentification) :
    Nonempty (CFSG.generalizedFitting G ≃* projSL 3 (GaloisField 2 e)) := by
  have := h.simple
  obtain ⟨φ⟩ := h.endgame hSCL hL
  exact ⟨(MulEquiv.subgroupCongr (CFSG.Adapters.generalizedFitting_eq_top_of_isSimpleGroup G)).trans
    (Subgroup.topEquiv.trans φ)⟩

end Endgame

end CFSG.CGT.PushingUpLit.A78
