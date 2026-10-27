module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Solvable
import CFSG.FeitThompson.Local.SimpleGroupNormalizerProper
import CFSG.FeitThompson.OddOrder.PGroupNormalizerCondition

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

variable {G : Type*} [Group G] {p : ℕ}

private theorem natCard_lt_natCard_of_lt [Finite G] {H K : Subgroup G} (h : H < K) :
    Nat.card H < Nat.card K :=
  lt_of_le_of_ne (Subgroup.card_le_of_le h.le) fun heq =>
    h.ne (Subgroup.eq_of_le_of_card_ge h.le heq.ge)

theorem natCard_le_pow_factorization_of_isPGroup [Finite G] {K S : Subgroup G} (hp : p.Prime)
    (hSK : S ≤ K) (hS : IsPGroup p S) : Nat.card S ≤ p ^ (Nat.card K).factorization p := by
  have := Fact.mk hp
  obtain ⟨n, hn⟩ := hS.exists_card_eq
  have h1 : p ^ n ∣ Nat.card K := hn ▸ Subgroup.card_dvd_of_le hSK
  exact hn ▸ Nat.pow_le_pow_right hp.one_lt.le
    ((hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 h1)

theorem lt_inf_normalizer_of_lt [Finite G] {R T : Subgroup G} (hp : p.Prime) (hT : IsPGroup p T)
    (hRT : R < T) : R < normalizer (R : Set G) ⊓ T := by
  have := Fact.mk hp
  have hnc : NormalizerCondition T := normalizerCondition_of_isPGroup hT
  have hlt : R.subgroupOf T < ⊤ :=
    lt_top_iff_ne_top.2 fun h => hRT.not_ge (Subgroup.subgroupOf_eq_top.1 h)
  obtain ⟨x, hx1, hx2⟩ :=
    SetLike.exists_of_lt (Subgroup.subgroupOf_normalizer_eq hRT.le ▸ hnc _ hlt)
  refine (le_inf le_normalizer hRT.le).lt_of_not_ge fun hle => hx2 ?_
  exact Subgroup.mem_subgroupOf.2 (hle ⟨Subgroup.mem_subgroupOf.1 hx1, x.2⟩)

theorem natCard_eq_pow_factorization_of_normalizer_le [Finite G] (hp : p.Prime)
    {M P : Subgroup G} (hPcard : Nat.card P = p ^ (Nat.card M).factorization p)
    (hNP : normalizer (P : Set G) ≤ M) : Nat.card P = p ^ (Nat.card G).factorization p := by
  have := Fact.mk hp
  obtain ⟨T, hT⟩ := (IsPGroup.of_card hPcard).exists_le_sylow
  rcases eq_or_lt_of_le hT with h | hlt
  · rw [h, T.card_eq_multiplicity]
  · exact absurd (natCard_le_pow_factorization_of_isPGroup hp (inf_le_left.trans hNP)
      (T.isPGroup'.to_le inf_le_right))
      (by have := natCard_lt_natCard_of_lt (lt_inf_normalizer_of_lt hp T.isPGroup' hlt); omega)

theorem exists_le_natCard_eq_pow_factorization [Finite G] (hp : p.Prime) {H R : Subgroup G}
    (hRH : R ≤ H) (hR : IsPGroup p R) :
    ∃ T : Subgroup G, R ≤ T ∧ T ≤ H ∧ Nat.card T = p ^ (Nat.card H).factorization p := by
  have := Fact.mk hp
  obtain ⟨T, hT⟩ := (hR.of_equiv (Subgroup.subgroupOfEquivOfLe hRH).symm).exists_le_sylow
  refine ⟨(T : Subgroup H).map H.subtype, ?_, Subgroup.map_subtype_le _, ?_⟩
  · rw [← Subgroup.map_subgroupOf_eq_of_le hRH]
    exact Subgroup.map_mono hT
  · rw [Subgroup.card_map_of_injective H.subtype_injective, T.card_eq_multiplicity]

theorem exists_sylow_map_subtype_eq [Finite G] (hp : p.Prime) {H R : Subgroup G} (hRH : R ≤ H)
    (hRcard : Nat.card R = p ^ (Nat.card H).factorization p) :
    ∃ S : Sylow p H, (S : Subgroup H).map H.subtype = R := by
  have := Fact.mk hp
  have hcard : Nat.card (R.subgroupOf H) = p ^ (Nat.card H).factorization p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRH).toEquiv, hRcard]
  exact ⟨Sylow.ofCard (R.subgroupOf H) hcard, by
    simp [Sylow.ofCard, Subgroup.map_subgroupOf_eq_of_le hRH]⟩

variable [Finite G] [IsSimpleGroup G] {M H B R P : Subgroup G}

theorem normalizer_le_of_maximal_inf (hp : p.Prime) (hM : IsCoatom M) (hB : ⊥ < B)
    (hmax : ∀ D : Subgroup G, IsCoatom D → D ≠ M → B ≤ D →
      p ^ (Nat.card (D ⊓ M : Subgroup G)).factorization p ≤
        p ^ (Nat.card (H ⊓ M : Subgroup G)).factorization p)
    (hBR : B ≤ R) (hRcard : Nat.card R = p ^ (Nat.card (H ⊓ M : Subgroup G)).factorization p)
    (hRP : R ≤ P) (hPM : P ≤ M) (hPcard : Nat.card P = p ^ (Nat.card M).factorization p)
    (hNP : normalizer (P : Set G) ≤ M) : normalizer (R : Set G) ≤ M := by
  have hPp : IsPGroup p P := IsPGroup.of_card hPcard
  have hNRlt : normalizer (R : Set G) < ⊤ :=
    normalizer_lt_top_of_isSimpleGroup (hB.trans_le hBR) ((hRP.trans hPM).trans_lt hM.lt_top)
  rcases eq_or_lt_of_le hRP with rfl | hRlt
  · exact hNP
  · by_contra hcon
    obtain ⟨D, hD, hDle⟩ :=
      (IsCoatomic.eq_top_or_exists_le_coatom (normalizer (R : Set G))).resolve_left hNRlt.ne
    have h1 := natCard_le_pow_factorization_of_isPGroup hp
      (le_inf (inf_le_left.trans hDle) (inf_le_right.trans hPM))
      (hPp.to_le (inf_le_right (a := normalizer (R : Set G))))
    have h2 := natCard_lt_natCard_of_lt (lt_inf_normalizer_of_lt hp hPp hRlt)
    have h3 := hmax D hD (fun h => hcon (h ▸ hDle)) (hBR.trans (le_normalizer.trans hDle))
    rw [← hRcard] at h3
    exact absurd (h2.trans_le (h1.trans h3)) (lt_irrefl _)

omit [IsSimpleGroup G] in
theorem natCard_eq_pow_factorization_of_inf_of_normalizer_le (hp : p.Prime) (hRH : R ≤ H)
    (hRcard : Nat.card R = p ^ (Nat.card (H ⊓ M : Subgroup G)).factorization p)
    (hNRM : normalizer (R : Set G) ≤ M) : Nat.card R = p ^ (Nat.card H).factorization p := by
  obtain ⟨T, hRT, hTH, hTcard⟩ :=
    exists_le_natCard_eq_pow_factorization hp hRH (IsPGroup.of_card hRcard)
  rcases eq_or_lt_of_le hRT with rfl | hRlt
  · exact hTcard
  · have hTp : IsPGroup p T := IsPGroup.of_card hTcard
    have h1 := natCard_le_pow_factorization_of_isPGroup hp
      (le_inf (inf_le_right.trans hTH) (inf_le_left.trans hNRM))
      (hTp.to_le (inf_le_right (a := normalizer (R : Set G))))
    have h2 := natCard_lt_natCard_of_lt (lt_inf_normalizer_of_lt hp hTp hRlt)
    rw [← hRcard] at h1
    exact absurd (h2.trans_le h1) (lt_irrefl _)

theorem normalizer_le_and_natCard_eq_of_maximal_inf (hp : p.Prime)
    (_hna : ¬ IsMulCommutative G) (_hodd : Odd (Nat.card G))
    (_hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable K)
    (hM : IsCoatom M) (_hH : IsCoatom H) (_hHM : H ≠ M)
    (hB : ⊥ < B) (_hBp : IsPGroup p B) (_hBHM : B ≤ H ⊓ M)
    (hmax : ∀ D : Subgroup G, IsCoatom D → D ≠ M → B ≤ D →
      p ^ (Nat.card (D ⊓ M : Subgroup G)).factorization p ≤
        p ^ (Nat.card (H ⊓ M : Subgroup G)).factorization p)
    (hBR : B ≤ R) (hRHM : R ≤ H ⊓ M)
    (hRcard : Nat.card R = p ^ (Nat.card (H ⊓ M : Subgroup G)).factorization p)
    (hRP : R ≤ P) (hPM : P ≤ M) (hPcard : Nat.card P = p ^ (Nat.card M).factorization p)
    (hNP : normalizer (P : Set G) ≤ M) :
    normalizer (R : Set G) ≤ M ∧ Nat.card R = p ^ (Nat.card H).factorization p ∧
      ∃ S : Sylow p H, (S : Subgroup H).map H.subtype = R := by
  have hNRM := normalizer_le_of_maximal_inf hp hM hB hmax hBR hRcard hRP hPM hPcard hNP
  have hSylow := natCard_eq_pow_factorization_of_inf_of_normalizer_le (M := M) hp
    (hRHM.trans inf_le_left) hRcard hNRM
  exact ⟨hNRM, hSylow, exists_sylow_map_subtype_eq hp (hRHM.trans inf_le_left) hSylow⟩

end CFSG.FeitThompson
