module

public import CFSG.HardMathSupport.Dickson.Bal207.Restate
public import CFSG.HardMathSupport.Dickson.Bal207.Center
import CFSG.GH74.Uniqueness.SU.SU1Basic
import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Models
import CFSG.Adapters.TauCetiLieModels
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinDBridge

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier
  CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier

theorem d4Eight_three_le_pRank {Y : Type} [Group Y] [Finite Y] (d : TauCeti.ValidLieTypeIndex)
    (hd : IsD4EightIdx d.1) (e : Y ≃* (TauCeti.CFSGIndex.lie d).Group) :
    3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y) := by
  obtain ⟨d1, hv⟩ := d
  cases d1 with
  | D r q =>
    obtain ⟨rfl, hp, -⟩ := hd
    obtain ⟨⟨-, -, hm⟩, F, _, hF, hcard, ⟨e'⟩⟩ :=
      CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even 4 q hv hp e
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Fintype F := Fintype.ofFinite F
    have : CharP F 2 :=
      charP_of_card_eq_prime_pow (f := q.exponent) (by rw [← Nat.card_eq_fintype_card, hcard, hp])
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e']
    exact CFSG.SectionRank.ClassicalEven.omegaPlus_three_le_pRank_three (K := F) hm
  | _ => simp [IsD4EightIdx] at hd

theorem d4Eight_three_dvd_card {Y : Type} [Group Y] [Finite Y] (d : TauCeti.ValidLieTypeIndex)
    (hd : IsD4EightIdx d.1) (e : Y ≃* (TauCeti.CFSGIndex.lie d).Group) : 3 ∣ Nat.card Y := by
  obtain ⟨E, -, -, hEc⟩ := CFSG.GH74.Uniqueness.SU.SU1.exists_isElemAbelian_of_le_pRank
    Nat.prime_three (H := (⊤ : Subgroup Y)) (k := 3) (d4Eight_three_le_pRank d hd e)
  have h3 : 3 ∣ Nat.card E := by
    rw [hEc]
    exact dvd_pow_self 3 (by norm_num)
  exact h3.trans (Subgroup.card_subgroup_dvd_card E)

theorem bal207PlusDvdD4Eight_holds : Bal207PlusDvdD4Eight := by
  intro X _ _ K _ hK
  obtain ⟨d, hd, ⟨e⟩⟩ := hK
  exact (d4Eight_three_dvd_card d hd e).trans (Subgroup.card_quotient_dvd_card _)

theorem d4Eight_coprime_center (hGA : GriessAllModelsStatement) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) (hK : IsLieQuot K IsD4EightIdx) :
    Nat.Coprime 3 (Nat.card (Subgroup.center K)) := by
  obtain ⟨⟨dd, hv⟩, hd, ⟨e⟩⟩ := hK
  cases dd with
  | D r q =>
    obtain ⟨rfl, hp2, -⟩ := hd
    have hL := CFSG.Models.lieModel_D 4 q hv (MulEquiv.refl _)
    rw [hp2] at hL
    have heven : Even (2 ^ q.exponent) := (Nat.even_pow' q.exponent_pos.ne').mpr even_two
    have hg : ¬ 3 ∣ (genericOrders .POmegaPlus 4 2 q.exponent).1 := by
      simp only [genericOrders, if_pos heven]
      norm_num
    exact centerAux_coprime_of_card_le_one Nat.prime_three
      ((center_torsion_le hGA hq e hL Nat.prime_three).trans
        (centerAux_torsBound_eq_one (Or.inl rfl) hg).le)
  | _ => simp [IsD4EightIdx] at hd

theorem d4Eight_not_isCyclic_sylow {K : Type} [Group K] [Finite K] (hK : IsLieQuot K IsD4EightIdx)
    (P : Sylow 3 K) : ¬ IsCyclic P := by
  obtain ⟨d, hd, ⟨e⟩⟩ := hK
  obtain ⟨E, -, hE, hEc⟩ := CFSG.GH74.Uniqueness.SU.SU1.exists_isElemAbelian_of_le_pRank
    Nat.prime_three (H := (⊤ : Subgroup (K ⧸ Subgroup.center K))) (k := 2)
    ((by norm_num : 2 ≤ 3).trans (d4Eight_three_le_pRank d hd e))
  exact rankAux_not_isCyclic_sylow_of_surjective Nat.prime_three
    (f := QuotientGroup.mk' (Subgroup.center K)) (QuotientGroup.mk'_surjective _)
    (rankAux_not_isCyclic_sylow Nat.prime_three hE hEc) P

theorem d4Eight_aut (hGA : GriessAllModelsStatement) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) (hK : IsLieQuot K IsD4EightIdx) (α : MulAut K)
    (hα : α ^ 3 = 1) :
    ∃ y : K, y ^ 3 = 1 ∧ α y = y ∧ MulAut.conj y ∉ Subgroup.zpowers α :=
  rankAux_fix Nat.prime_three (by norm_num) (d4Eight_coprime_center hGA hq hK)
    (d4Eight_not_isCyclic_sylow hK) α hα

theorem rankAux_noncyclic_complement {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {K B : Subgroup X} (hSC : IsSCp p ⊤ B) (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (h : ∀ α : MulAut ↥K, α ^ p = 1 →
      ∃ y : ↥K, y ^ p = 1 ∧ α y = y ∧ MulAut.conj y ∉ Subgroup.zpowers α) :
    ∃ A : Subgroup X, A ≤ B ∧ ¬ IsCyclic ↥A ∧ A ⊓ Subgroup.centralizer (K : Set X) = ⊥ ∧
      A ⊔ (B ⊓ Subgroup.centralizer (K : Set X)) = B := by
  by_contra hex
  have hBel : IsElemAbelian p B := hSC.2.1
  obtain ⟨A, hAB, hAC, hAsup⟩ := rankAux_exists_complement (K := K) hp hBel
  have hcyc : IsCyclic ↥A := by
    by_contra hnc
    exact hex ⟨A, hAB, hnc, hAC, hAsup⟩
  obtain ⟨x, hxA⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top A).mp hcyc
  have hxB : x ∈ B := hAB (hxA ▸ Subgroup.mem_zpowers x)
  have hxN : x ∈ Subgroup.normalizer (K : Set X) := hBN hxB
  have hxp : x ^ p = 1 := hBel.2 x hxB
  have hαp : K.normalizerMonoidHom ⟨x, hxN⟩ ^ p = 1 := by
    rw [← map_pow]
    have h1 : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (K : Set X))) ^ p = 1 :=
      Subtype.ext (by simpa using hxp)
    rw [h1, map_one]
  obtain ⟨y, hyp, hyα, hyz⟩ := h _ hαp
  rw [← hxA] at hAsup
  exact hyz (rankAux_conj_mem_zpowers hSC hxN hAsup hyp hyα)

theorem bal207PlusRankD4Eight_of_griess (hGA : GriessAllModelsStatement) :
    Bal207PlusRankD4Eight := by
  intro X _ _ _ K B hcomp hSC hBN hK
  exact rankAux_noncyclic_complement Nat.prime_three hSC hBN
    fun α hα => d4Eight_aut hGA hcomp.2.2 hK α hα

end CFSG.HardMathSupport.Dickson.Bal207
