module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCGCoreOrthogonal
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBLSmallBinaryOrthogonal
public import CFSG.LinearAlgebra.SteinbergBQKernelBlocks

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup CFSG.RankThree.GroupTheory.SteinbergBY SteinbergCG
open TauCeti.QuadraticMap (orthogonalGroup)
open scoped IsMulCommutative

namespace SteinbergCG

theorem le_two_of_dvd_six_of_dvd_two_pow {a n : ℕ} (h6 : a ∣ 6) (h2 : a ∣ 2 ^ n) : a ≤ 2 := by
  obtain ⟨k, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k <;> norm_num
  · exfalso
    have h4 : 4 ∣ 2 ^ k := by
      rw [show k = 2 + (k - 2) by omega, pow_add]
      exact Dvd.intro _ rfl
    have := h4.trans h6
    omega

theorem le_four_of_dvd_eight {a : ℕ} (h8 : a ∣ 8) (hne : a ≠ 8) : a ≤ 4 := by
  have ha : a ∈ Nat.divisors 8 := Nat.mem_divisors.mpr ⟨h8, by norm_num⟩
  have : Nat.divisors 8 = {1, 2, 4, 8} := by decide
  rw [this] at ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  omega

end SteinbergCG

theorem extraspecial_width_one_two_rank_at_most_two {H : Type*} [Group H] [Finite H]
    (hH : CFSG.IsCharacteristicP 2 H) (hQ : IsExtraspecialPGroup 2 (CFSG.pCore 2 H))
    (hQ8 : Nat.card (CFSG.pCore 2 H) = 8) :
    CFSG.pRank 2 H ≤ 2 ∧
    ∀ z : CFSG.pCore 2 H, center (CFSG.pCore 2 H) = zpowers z →
      (∀ (x : CFSG.pCore 2 H) (ε : ZMod 2), x ^ 2 = z ^ ε.val →
        sqVal z (x : CFSG.pCore 2 H ⧸ center (CFSG.pCore 2 H)) = ε) ∧
      ((∃ v : CFSG.pCore 2 H ⧸ center (CFSG.pCore 2 H), v ≠ 1 ∧ sqVal z v = 0) →
        CFSG.pCore 2 H = ⊤) ∧
      ((∀ v : CFSG.pCore 2 H ⧸ center (CFSG.pCore 2 H), sqVal z v = 0 → v = 1) →
        ∀ S : Sylow 2 H, CFSG.pCore 2 H ≤ S ∧ (CFSG.pCore 2 H).relIndex S ≤ 2 ∧
          ∀ E : Subgroup H, E ≤ S → IsElementaryAbelian 2 E →
            Nat.card (E ⊓ CFSG.pCore 2 H : Subgroup H) ≤ 2 ∧ Nat.card E ≤ 4) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := CFSG.pCore 2 H with hQdef
  have hQ2 : IsPGroup 2 Q := CFSG.pCore_isPGroup
  have hZ2 : Nat.card (center Q) = 2 := hQ.2.2.2
  have hrank : (∀ E : Subgroup H, IsElementaryAbelian 2 E → Nat.card E ≤ 4) →
      CFSG.pRank 2 H ≤ 2 := by
    intro h
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
    refine CFSG.SectionRank.pRank_le (by norm_num) fun E _ hE => ?_
    exact h E ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 E).mpr hE)
  have key : ∀ z : Q, center Q = zpowers z →
      ((∀ (x : Q) (ε : ZMod 2), x ^ 2 = z ^ ε.val → sqVal z (x : Q ⧸ center Q) = ε) ∧
        ((∃ v : Q ⧸ center Q, v ≠ 1 ∧ sqVal z v = 0) → Q = ⊤) ∧
        ((∀ v : Q ⧸ center Q, sqVal z v = 0 → v = 1) →
          ∀ S : Sylow 2 H, Q ≤ S ∧ Q.relIndex S ≤ 2 ∧
            ∀ E : Subgroup H, E ≤ S → IsElementaryAbelian 2 E →
              Nat.card (E ⊓ Q : Subgroup H) ≤ 2 ∧ Nat.card E ≤ 4)) ∧
      CFSG.pRank 2 H ≤ 2 := by
    intro z hz
    have HQ := commPairHyp_of_extraspecial hQ hz
    have := HQ.isElementaryAbelian_quotient
    obtain ⟨-, -, -, hsq, -⟩ := extraspecial_centralizer_orthogonal_action hH hQ hz
    have : Finite (Additive (Q ⧸ center Q)) := inferInstanceAs (Finite (Q ⧸ center Q))
    have : FiniteDimensional (ZMod 2) (Additive (Q ⧸ center Q)) := Module.Finite.of_finite
    have hdim : Module.finrank (ZMod 2) (Additive (Q ⧸ center Q)) = 2 :=
      finrank_quotient_center (w := 1) hQ (by rw [hQ8]; norm_num)
    have hO := (small_binary_orthogonal_two_subgroups_and_stabilizers (sqQuad HQ hz)
      (polarBilin_sqQuad_nondegenerate HQ hz) (Or.inl hdim)).1 hdim
    have : Finite (orthogonalGroup (sqQuad HQ hz)) :=
      have := CFSG.LinearAlgebra.SteinbergBQ.finite_linearEquiv_zmod2
        (V := Additive (Q ⧸ center Q))
      inferInstance
    have hOpos : 0 < Nat.card (orthogonalGroup (sqQuad HQ hz)) := Nat.card_pos
    have hidx : Q.index ∣ Nat.card (orthogonalGroup (sqQuad HQ hz)) := by
      rw [index_eq_card_range hH hQ HQ hz]
      exact Subgroup.card_subgroup_dvd_card _
    have hidx0 : Q.index ≠ 0 := index_ne_zero_of_finite
    have hsing : (∃ v : Q ⧸ center Q, v ≠ 1 ∧ sqVal z v = 0) → Q = ⊤ := by
      rintro ⟨v, hv1, hv0⟩
      have hO2 := (hO.2.2 ⟨Additive.ofMul v, fun h => hv1 (Additive.ofMul.injective h), hv0⟩).2
      have hle : Q.index ≤ 2 := (Nat.le_of_dvd hOpos hidx).trans hO2
      have hcardH : Nat.card H = 8 * Q.index := by rw [← hQ8, card_mul_index]
      have hH2 : IsPGroup 2 H := by
        rcases (show Q.index = 1 ∨ Q.index = 2 by omega) with h | h
        · exact IsPGroup.of_card (n := 3) (by rw [hcardH, h]; norm_num)
        · exact IsPGroup.of_card (n := 4) (by rw [hcardH, h]; norm_num)
      refine eq_top_iff.mpr ?_
      rw [hQdef, CFSG.pCore]
      exact le_sSup ⟨inferInstance, hH2.to_subgroup ⊤⟩
    have haniso : (∀ v : Q ⧸ center Q, sqVal z v = 0 → v = 1) →
        ∀ S : Sylow 2 H, Q ≤ S ∧ Q.relIndex S ≤ 2 ∧
          ∀ E : Subgroup H, E ≤ S → IsElementaryAbelian 2 E →
            Nat.card (E ⊓ Q : Subgroup H) ≤ 2 ∧ Nat.card E ≤ 4 := by
      intro han S
      have hsqz : ∀ x : Q, x ∉ center Q → x ^ 2 = z := by
        intro x hx
        have h1 : sqVal z (x : Q ⧸ center Q) ≠ 0 := fun h0 =>
          hx ((QuotientGroup.eq_one_iff x).mp (han _ h0))
        rw [HQ.sq_eq_zpow_sqVal hz x, SmallBinaryOrthogonal.eq_one_of_ne_zero h1]
        exact pow_one z
      have hQS : Q ≤ S := hQ2.le_sylow_of_normal S
      obtain ⟨f, hf⟩ := hO.2.1
      have h6 : Q.index ∣ 6 := by
        refine hidx.trans ((Subgroup.card_dvd_of_injective f hf).trans ?_)
        rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
        rfl
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp S.isPGroup'
      have hrel : Q.relIndex S ≤ 2 :=
        le_two_of_dvd_six_of_dvd_two_pow ((relIndex_dvd_index_of_le hQS).trans h6)
          (hn ▸ relIndex_dvd_card Q S)
      refine ⟨hQS, hrel, fun E hES hE => ?_⟩
      have hEQ : E ⊓ Q ≤ (center Q).map Q.subtype := by
        intro y hy
        obtain ⟨hyE, hyQ⟩ := mem_inf.mp hy
        refine ⟨⟨y, hyQ⟩, ?_, rfl⟩
        by_contra hc
        have h1 := hsqz ⟨y, hyQ⟩ hc
        have h2 : y ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian y hyE
        apply HQ.z_ne_one
        rw [← h1]
        exact Subtype.ext h2
      have hcEQ : Nat.card (E ⊓ Q : Subgroup H) ≤ 2 := by
        refine (card_le_of_le hEQ).trans ?_
        rw [card_map_of_injective Q.subtype_injective, hZ2]
      refine ⟨hcEQ, ?_⟩
      have h1 := relIndex_mul_card Q E
      have h2 : Q.relIndex E ≤ Q.relIndex S :=
        relIndex_le_of_le_right hES index_ne_zero_of_finite
      rw [inf_comm] at h1
      rw [← h1]
      calc Q.relIndex E * Nat.card (E ⊓ Q : Subgroup H) ≤ 2 * 2 :=
            Nat.mul_le_mul (h2.trans hrel) hcEQ
        _ = 4 := by norm_num
    have hrk : CFSG.pRank 2 H ≤ 2 := by
      refine hrank fun E hE => ?_
      by_cases hs : ∃ v : Q ⧸ center Q, v ≠ 1 ∧ sqVal z v = 0
      · have hQt := hsing hs
        have h8 : Nat.card E ∣ 8 := by
          rw [← hQ8, hQt, card_top]
          exact card_subgroup_dvd_card E
        refine le_four_of_dvd_eight h8 fun hE8 => ?_
        have hEt : E = ⊤ := by
          rw [← card_eq_iff_eq_top, hE8, ← hQ8, hQt, card_top]
        have hcomm : ∀ a b : H, a * b = b * a := fun a b =>
          congrArg Subtype.val (mul_comm' (⟨a, hEt ▸ mem_top a⟩ : E) ⟨b, hEt ▸ mem_top b⟩)
        have hctop : center Q = ⊤ := eq_top_iff.mpr fun x _ =>
          mem_center_iff.mpr fun g => Subtype.ext (hcomm _ _)
        rw [hctop, card_top, hQ8] at hZ2
        exact absurd hZ2 (by norm_num)
      · push Not at hs
        have han : ∀ v : Q ⧸ center Q, sqVal z v = 0 → v = 1 := fun v hv =>
          by_contra fun h => hs v h hv
        have hE2 : IsPGroup 2 E := CFSG.IsElementaryAbelian.isPGroup 2 E
        obtain ⟨S, hES⟩ := hE2.exists_le_sylow
        exact ((haniso han S).2.2 E hES hE).2
    exact ⟨⟨hsq, hsing, haniso⟩, hrk⟩
  obtain ⟨z, hz⟩ := exists_center_eq_zpowers hZ2
  exact ⟨(key z hz).2, fun z hz => (key z hz).1⟩

end CFSG.LocalAnalysis.GorensteinLyons
