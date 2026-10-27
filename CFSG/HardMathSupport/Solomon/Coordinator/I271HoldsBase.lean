module

public import CFSG.HardMathSupport.Solomon.Proving.L34Cover
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.I27_1Gen
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_6_9_1

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Solomon.UniquenessMaximal

section PrimeCore

variable {X : Type} [Group X] [Finite X]

theorem i271h_primeCoreOf_eq_bot {p : ℕ} (hO : GLAPPrimeCore p X = ⊥) {K : Subgroup X}
    (hK : GLAPComponent p ⊤ K) : GLAPPrimeCoreOf p K = ⊥ :=
  le_bot_iff.1 ((glaPPrimeCoreOf_le_of_isSubnormal p hK.2.1).trans
    (glaPPrimeCoreOf_top_eq_bot_of_eq_bot hO).le)

theorem i271h_primeCore_eq_bot {p : ℕ} (hO : GLAPPrimeCore p X = ⊥) {K : Subgroup X}
    (hK : GLAPComponent p ⊤ K) : GLAPPrimeCore p ↥K = ⊥ := by
  have h := i271h_primeCoreOf_eq_bot hO hK
  unfold GLAPPrimeCoreOf at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).1 h

end PrimeCore

theorem i271h_center_isPGroup {p : ℕ} (hp : p.Prime) {Y : Type*} [Group Y] [Finite Y]
    (hO : GLAPPrimeCore p Y = ⊥) : IsPGroup p (Subgroup.center Y) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [IsPGroup.iff_orderOf]
  rintro ⟨g, hg⟩
  rw [Subgroup.orderOf_mk]
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' p hp.ne_one
  refine ⟨k, ?_⟩
  have hy : orderOf (g ^ (p ^ k)) = m := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ hp.ne_zero) (hkm ▸ dvd_mul_right _ _), hkm,
      Nat.mul_div_cancel_left _ (pow_pos hp.pos _)]
  have hnormal : (Subgroup.zpowers (g ^ (p ^ k))).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ hg _))
  have hcop : Nat.Coprime p (Nat.card (Subgroup.zpowers (g ^ (p ^ k)))) := by
    rw [Nat.card_zpowers, hy]
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 hm
  have hle : Subgroup.zpowers (g ^ (p ^ k)) ≤ GLAPPrimeCore p Y := le_sSup ⟨hnormal, hcop⟩
  rw [hO] at hle
  have h1 : g ^ (p ^ k) = 1 := Subgroup.mem_bot.mp (hle (Subgroup.mem_zpowers _))
  rw [h1, orderOf_one] at hy
  rw [hkm, ← hy, mul_one]

theorem i271h_pCore_three_eq_center {Y : Type} [Group Y] [Finite Y]
    (hq : CFSG.Open.IsQuasisimple Y) (hO : GLAPPrimeCore 3 Y = ⊥) :
    CFSG.pCore 3 Y = Subgroup.center Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine le_antisymm (Proving.pCore_three_le_center_of_quasisimple hq) ?_
  exact CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCore 3 _ inferInstance
    (i271h_center_isPGroup Nat.prime_three hO)

theorem i271h_pRank_coe {G : Type*} [Group G] [Finite G] (p : ℕ) (H : Subgroup G) :
    CFSG.pRank p ↥H = CFSG.Open.pRank p H :=
  (CFSG.SectionRank.pRank_eq_open_pRank_top p H).trans
    (CFSG.SectionRank.pRank_eq_pRank_top_subgroup H).symm

section GOne

variable {X : Type} [Group X] [Finite X]

theorem i271h_isInGOne_of_le {p : ℕ} {B K : Subgroup X}
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) (h : K ≤ coreIn p 3 B K) : IsInGOne p B K := by
  unfold IsInGOne
  rw [bClosure_eq_of_le_normalizer hBN]
  exact le_antisymm h (iSup₂_le fun Q _ => inf_le_left)

theorem i271h_le_coreIn_of_le_centralizer {p : ℕ} {B K S E : Subgroup X} (hEB : E ≤ B)
    (hE : 3 ≤ CFSG.Open.pRank p E) (hS : S ≤ K ⊓ Subgroup.centralizer (E : Set X)) : S ≤ coreIn p 3 B K := by
  unfold coreIn
  exact hS.trans (le_iSup₂_of_le (f := fun (Q : Subgroup X) (_ : Q ≤ B ∧ 3 ≤ CFSG.Open.pRank p Q) =>
    K ⊓ Subgroup.normalizer (Q : Set X)) E ⟨hEB, hE⟩
    (inf_le_inf_left _ (Subgroup.centralizer_le_normalizer (E : Set X))))

end GOne

section Aut

variable {X : Type} [Group X] [Finite X]

theorem i271h_dQ_eq_centralizer {K : Subgroup X} (h : GLAPPrimeCoreOf 3 K = ⊥) :
    dQ K = Subgroup.centralizer (K : Set X) := by
  ext g
  rw [mem_dQ, h, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨-, -, hg⟩ y hy
    have := Subgroup.mem_bot.1 (hg y hy)
    calc y * g = (y * g * y⁻¹ * g⁻¹) * g * y := by group
      _ = g * y := by rw [this]; group
  · intro hg
    refine ⟨?_, ?_, fun y hy => ?_⟩
    · exact Subgroup.centralizer_le_normalizer (K : Set X)
        (Subgroup.mem_centralizer_iff.2 hg)
    · rw [Subgroup.mem_normalizer_iff]
      intro x
      simp only [SetLike.mem_coe, Subgroup.mem_bot]
      constructor
      · rintro rfl; group
      · intro hx
        have := congrArg (fun z => g⁻¹ * z * g) hx
        simpa [mul_assoc] using this
    · rw [Subgroup.mem_bot]
      have := hg y hy
      calc y * g * y⁻¹ * g⁻¹ = (y * g) * (g * y)⁻¹ := by group
        _ = 1 := by rw [this]; group

theorem i271h_autOrderIn_eq_relIndex {B K : Subgroup X} (hBN : B ≤ Subgroup.normalizer (K : Set X)) :
    autOrderIn B K = (Subgroup.centralizer (K : Set X)).relIndex B := by
  unfold autOrderIn
  rw [inf_of_le_left hBN]

end Aut

end CFSG.HardMathSupport.Solomon.Coordinator
