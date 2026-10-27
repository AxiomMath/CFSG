module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BLift
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017RedCenter

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S8 CFSG.LocalAnalysis.GLTheoremA.H1017
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem card_le_prime_of_centMod {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {J A : Subgroup G}
    (hA : IsElemAbelian p A) (hAJ : ∀ a ∈ A, CentMod p J a)
    (V E : Subgroup (PQuot p J)) (hV : V ≠ ⊥) (hV2 : IsPGroup 2 V)
    (hE : IsElemAbelian p E) (hEV : E ≤ Subgroup.normalizer (V : Set (PQuot p J)))
    (hlt : p ^ GLATwoLocalRank p G * Nat.card (Subgroup.center (PQuot p J)) <
      Nat.card E * p ^ 2) :
    Nat.card A ≤ p := by
  have hAN : A ≤ Subgroup.normalizer (J : Set G) := fun a ha => (hAJ a ha).1
  have hAc : ∀ a ∈ A, ∀ k ∈ J, ⁅k, a⁆ ∈ GLAPPrimeCoreOf p J := fun a ha k hk =>
    (centMod_iff.1 (hAJ a ha)).2 k hk
  obtain ⟨P, W, hP, hP2, hWP, hW, hcard⟩ :=
    twoLocal_of_witness_gen hp hp2 hA hAN hAc V E hV hV2 hE hEV
  have hWle := card_le_pow_glaTwoLocalRank hp hW hP hP2 hWP
  have h1 : Nat.card E * Nat.card A < Nat.card E * p ^ 2 :=
    lt_of_le_of_lt (hcard.trans (Nat.mul_le_mul_right _ hWle)) hlt
  have h2 : Nat.card A < p ^ 2 := Nat.lt_of_mul_lt_mul_left h1
  obtain ⟨k, hk⟩ := exists_card_eq_pow_of_isElemAbelian hp hA
  rw [hk] at h2 ⊢
  have hk2 : k < 2 := (Nat.pow_lt_pow_iff_right hp.one_lt).1 h2
  calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
    _ = p := pow_one p

private theorem witness_of_attained {p : ℕ} {J : Subgroup G} {s : TauCeti.SporadicName}
    {r w : ℕ} (hJcat : catalogIs (PSimple p J) (sporIs s))
    (hZ : Nat.card (Subgroup.center (PQuot p J)) = 1) (hw : TwoRankAttained p s w)
    (hlt : p ^ r < p ^ w * p ^ 2) :
    ∃ V E : Subgroup (PQuot p J), V ≠ ⊥ ∧ IsPGroup 2 V ∧ IsElemAbelian p E ∧
      E ≤ Subgroup.normalizer (V : Set (PQuot p J)) ∧
        p ^ r * Nat.card (Subgroup.center (PQuot p J)) < Nat.card E * p ^ 2 := by
  have hbot : Subgroup.center (PQuot p J) = ⊥ := Subgroup.eq_bot_of_card_eq _ hZ
  obtain ⟨i, hi, ⟨e⟩⟩ := hJcat
  have e' : PQuot p J ≃* PSimple p J :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hbot.symm)
  obtain ⟨E, T, hE, hEc, hT, hT2, hET⟩ := hw (PQuot p J) ⟨i, hi, ⟨e'.trans e⟩⟩
  exact ⟨T, E, hT, hT2, hE, hET, by rw [hZ, hEc, mul_one]; exact hlt⟩

private theorem witness_of_cover {J : Subgroup G} {s : TauCeti.SporadicName} {r w : ℕ}
    (hJcat : catalogIs (PSimple 3 J) (sporIs s))
    (hZ : Nat.card (Subgroup.center (PQuot 3 J)) = 3) (hw : CoverTwoRankAttained s w)
    (hlt : 3 ^ r * 3 < 3 ^ w * 3 ^ 2) :
    ∃ V E : Subgroup (PQuot 3 J), V ≠ ⊥ ∧ IsPGroup 2 V ∧ IsElemAbelian 3 E ∧
      E ≤ Subgroup.normalizer (V : Set (PQuot 3 J)) ∧
        3 ^ r * Nat.card (Subgroup.center (PQuot 3 J)) < Nat.card E * 3 ^ 2 := by
  obtain ⟨E, T, hE, hEc, hT, hT2, hET⟩ := hw (PQuot 3 J) hJcat hZ
  exact ⟨T, E, hT, hT2, hE, hET, by rw [hZ, hEc]; exact hlt⟩

private theorem exists_witness (hT : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers)
    (h : I301BRes) {p : ℕ} {X J : Subgroup G} {row : Row} (hJ : GLAPComponent p X J)
    (hprow : p = row.prime) (hJcat : catalogIs (PSimple p J) (sporIs row.name)) :
    ∃ V E : Subgroup (PQuot p J), V ≠ ⊥ ∧ IsPGroup 2 V ∧ IsElemAbelian p E ∧
      E ≤ Subgroup.normalizer (V : Set (PQuot p J)) ∧
        p ^ row.rank * Nat.card (Subgroup.center (PQuot p J)) < Nat.card E * p ^ 2 := by
  subst hprow
  have h3 := Nat.prime_three
  cases row with
  | ly =>
    exact witness_of_attained hJcat
      (center_pQuot_eq_bot_of_spor hT h3 hJ hJcat (by decide)) h.witLy (by decide)
  | co2 =>
    exact witness_of_attained hJcat
      (center_pQuot_eq_bot_of_spor hT h3 hJ hJcat (by decide)) h.witCo2 (by decide)
  | co1 =>
    exact witness_of_attained hJcat
      (center_pQuot_eq_bot_of_spor hT h3 hJ hJcat (by decide)) h.witCo1 (by decide)
  | fi24 =>
    rcases card_center_pQuot_of_spor hT h3 hJ hJcat (by decide) with hZ | hZ
    · exact witness_of_attained hJcat hZ h.witFi24 (by decide)
    · exact witness_of_cover hJcat hZ h.witFi24Cover (by decide)
  | fi24h =>
    rcases card_center_pQuot_of_spor hT h3 hJ hJcat (by decide) with hZ | hZ
    · exact witness_of_attained hJcat hZ h.witFi24 (by decide)
    · exact witness_of_cover hJcat hZ h.witFi24Cover (by decide)
  | suz =>
    rcases card_center_pQuot_of_spor hT h3 hJ hJcat (by decide) with hZ | hZ
    · exact witness_of_attained hJcat hZ h.witSuz (by decide)
    · exact witness_of_cover hJcat hZ h.witSuzCover (by decide)
  | suzh =>
    rcases card_center_pQuot_of_spor hT h3 hJ hJcat (by decide) with hZ | hZ
    · exact witness_of_attained hJcat hZ h.witSuz (by decide)
    · exact witness_of_cover hJcat hZ h.witSuzCover (by decide)
  | th =>
    exact witness_of_attained hJcat
      (center_pQuot_eq_bot_of_spor hT h3 hJ hJcat (by decide)) h.witTh (by decide)
  | m3 =>
    exact witness_of_attained hJcat
      (center_pQuot_eq_bot_of_spor hT h3 hJ hJcat (by decide)) h.witM3 (by decide)
  | m5 =>
    exact witness_of_attained hJcat
      (center_pQuot_eq_bot_of_spor hT Nat.prime_five hJ hJcat (by decide)) h.witM5 (by decide)

theorem card_le_prime_of_row (hT : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers)
    (h : I301BRes) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X J : Subgroup G} {row : Row}
    (hJ : GLAPComponent p X J) (hprow : p = row.prime)
    (hJcat : catalogIs (PSimple p J) (sporIs row.name)) (hrank : GLATwoLocalRank p G = row.rank)
    {A : Subgroup G} (hA : IsElemAbelian p A) (hAJ : ∀ a ∈ A, CentMod p J a) :
    Nat.card A ≤ p := by
  obtain ⟨V, E, hV, hV2, hE, hEV, hlt⟩ := exists_witness hT h hJ hprow hJcat
  exact card_le_prime_of_centMod hp hp2 hA hAJ V E hV hV2 hE hEV (by rw [hrank]; exact hlt)

theorem mem_zpowers_of_centMod {p : ℕ} {a y : G} {J : Subgroup G} (ha : orderOf a = p)
    (haJ : CentMod p J a)
    (hrk : ∀ A : Subgroup G, IsElemAbelian p A → (∀ x ∈ A, CentMod p J x) → Nat.card A ≤ p)
    (hy : y ^ p = 1) (hyJ : CentMod p J y) (hay : a * y = y * a) : y ∈ Subgroup.zpowers a := by
  have hap : a ^ p = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  set S : Subgroup G := Subgroup.zpowers a ⊔ Subgroup.zpowers y with hS
  have hSel : IsElemAbelian p S :=
    S8.L84.isElemAbelian_sup_of_commute (isElemAbelian_zpowers hap) (isElemAbelian_zpowers hy)
      (fun u hu v hv => by
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
        exact (Commute.zpow_zpow (show Commute a y from hay) m n).eq)
  have hSle : S ≤ centModSubgroup p J :=
    sup_le (Subgroup.zpowers_le.2 (centMod_iff.1 haJ)) (Subgroup.zpowers_le.2 (centMod_iff.1 hyJ))
  have hcard := hrk S hSel fun x hx => centMod_iff.2 (hSle hx)
  have heq : Subgroup.zpowers a = S :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [Nat.card_zpowers, ha]; exact hcard)
  rw [heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)

end CFSG.LocalAnalysis.GLTheoremA.H301B

end
