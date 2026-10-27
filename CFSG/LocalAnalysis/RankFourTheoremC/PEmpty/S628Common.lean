module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Faithful
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yBasic
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Strong
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62xDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC (SmallRankSylowTwo smallRankS smallRankR smallRankD)
open scoped commutatorElement

structure S62Config {G : Type} [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M : Subgroup G)
    (x z : G) (T : Subgroup G) : Prop where
  situation : Situation G p P M
  point : Point P M x
  central : Central P z
  prop614 : Prop614At M x z
  sylowTwo : SmallRankSylowTwo P M T

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G}
  {T : Subgroup G}

namespace S62Config

theorem prime (c : S62Config p P M x z T) : p.Prime := c.situation.prime

theorem ne_two (c : S62Config p P M x z T) : p ≠ 2 := c.situation.ne_two

theorem B_le_P (c : S62Config p P M x z T) : zpowers x ⊔ zpowers z ≤ (P : Subgroup G) :=
  sup_le (zpowers_le.mpr c.point.mem) (zpowers_le.mpr c.central.mem)

theorem B_le_M (c : S62Config p P M x z T) : zpowers x ⊔ zpowers z ≤ M :=
  c.B_le_P.trans c.situation.sylow_le

theorem T_le_M (c : S62Config p P M x z T) : T ≤ M :=
  c.sylowTwo.le_core.trans (sSup_le fun _ hK => hK.1)

theorem S_le_M (c : S62Config p P M x z T) : smallRankS x T ≤ M :=
  inf_le_left.trans c.T_le_M

theorem S_isPGroup (c : S62Config p P M x z T) : IsPGroup 2 (smallRankS x T) :=
  c.sylowTwo.isPGroup.to_le inf_le_left

theorem z_mem_centralizer (c : S62Config p P M x z T) : z ∈ centralizer ({x} : Set G) :=
  mem_centralizer_singleton_iff.mpr
    (mem_centralizer_iff.mp c.central.centralizes x c.point.mem).symm

theorem x_mem_centralizer (_c : S62Config p P M x z T) : x ∈ centralizer ({x} : Set G) :=
  mem_centralizer_singleton_iff.mpr rfl

theorem z_le_normalizer_S (c : S62Config p P M x z T) :
    zpowers z ≤ normalizer (smallRankS x T : Set G) := by
  rw [zpowers_le]
  exact inf_normalizer_le_normalizer_inf ⟨c.sylowTwo.normalized c.central.mem,
    le_normalizer c.z_mem_centralizer⟩

theorem B_le_normalizer_S (c : S62Config p P M x z T) :
    zpowers x ⊔ zpowers z ≤ normalizer (smallRankS x T : Set G) := by
  refine sup_le ?_ c.z_le_normalizer_S
  rw [zpowers_le]
  exact inf_normalizer_le_normalizer_inf ⟨c.sylowTwo.normalized c.point.mem,
    le_normalizer c.x_mem_centralizer⟩

theorem B_le_centralizer (c : S62Config p P M x z T) :
    zpowers x ⊔ zpowers z ≤ centralizer ({x} : Set G) :=
  sup_le (zpowers_le.mpr c.x_mem_centralizer) (zpowers_le.mpr c.z_mem_centralizer)

theorem R_ne_bot (c : S62Config p P M x z T) : smallRankR x z T ≠ ⊥ := by
  obtain ⟨v, hv, hzv⟩ := exists_mem_inf_centralizer_not_commute c.situation c.point c.central
    c.sylowTwo
  intro hbot
  have hle : zpowers z ≤ centralizer ((smallRankS x T : Subgroup G) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
  exact hzv (mem_centralizer_iff.mp (hle (mem_zpowers z)) v hv).symm

theorem S_ne_bot (c : S62Config p P M x z T) : smallRankS x T ≠ ⊥ := by
  obtain ⟨v, hv, hzv⟩ := exists_mem_inf_centralizer_not_commute c.situation c.point c.central
    c.sylowTwo
  intro hbot
  have hv1 : v = 1 := Subgroup.mem_bot.mp (hbot ▸ hv)
  exact hzv (by rw [hv1, mul_one, one_mul])

theorem commutator_pCoreOf_ne_bot (c : S62Config p P M x z T) :
    ⁅zpowers z, pCoreOf 2 M ⊓ centralizer ({x} : Set G)⁆ ≠ ⊥ := by
  obtain ⟨v, hv, hzv⟩ := exists_mem_pCoreOf_inf_centralizer_not_commute c.situation c.point
    c.central
  intro hbot
  have hle : zpowers z ≤ centralizer ((pCoreOf 2 M ⊓ centralizer ({x} : Set G) : Subgroup G) :
      Set G) := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
  exact hzv (mem_centralizer_iff.mp (hle (mem_zpowers z)) v hv).symm

theorem normalizer_zpowers_le' (c : S62Config p P M x z T) :
    normalizer (zpowers z : Set G) ≤ M :=
  normalizer_zpowers_le c.situation c.central

theorem centralizer_le_M (c : S62Config p P M x z T) : centralizer ({z} : Set G) ≤ M :=
  (CFSG.LocalAnalysis.RankThreeTheoremC.sr628_centralizer_le_normalizer_zpowers z).trans
    c.normalizer_zpowers_le'

theorem pCoreOf_two_le_T (c : S62Config p P M x z T) : pCoreOf 2 M ≤ T := by
  have hp := c.prime
  have hT := c.sylowTwo
  have hN2 : IsPGroup 2 (pCoreOf 2 M) :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_isPGroup 2 M
  have hNM : pCoreOf 2 M ≤ M := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le 2 M
  have hnorm : ((pCoreOf 2 M).subgroupOf M).Normal :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_normal_subgroupOf 2 M M le_rfl
      (by rw [Subgroup.subgroupOf_self]; infer_instance)
  have hMN : M ≤ normalizer (pCoreOf 2 M : Set G) := le_normalizer_of_normal_subgroupOf hNM
  have hKM : rankThreePrimeCore p M ≤ M := sSup_le fun _ hK => hK.1
  have hcop : p.Coprime (Nat.card (pCoreOf 2 M)) := by
    obtain ⟨n, hn⟩ := hN2.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp Nat.prime_two).mpr c.ne_two)
  have hNK : pCoreOf 2 M ≤ rankThreePrimeCore p M :=
    le_sSup ⟨hNM, normal_subgroupOf_of_le_normalizer hMN, hcop⟩
  have hTK : IsPGroup 2 (T.subgroupOf (rankThreePrimeCore p M)) :=
    hT.isPGroup.of_equiv (subgroupOfEquivOfLe hT.le_core).symm
  have : (pCoreOf 2 M |>.subgroupOf (rankThreePrimeCore p M)).Normal :=
    normal_subgroupOf_of_le_normalizer (hKM.trans hMN)
  have hle := (hN2.of_equiv (subgroupOfEquivOfLe hNK).symm).le_sylow_of_normal
    (hTK.toSylow hT.index_odd)
  intro n hn
  have hmem : (⟨n, hNK hn⟩ : rankThreePrimeCore p M) ∈
      (pCoreOf 2 M).subgroupOf (rankThreePrimeCore p M) := mem_subgroupOf.mpr hn
  exact mem_subgroupOf.mp (hle hmem)

theorem normalizer_le (c : S62Config p P M x z T) {S₀ : Subgroup G} (hS₀S : S₀ ≤ smallRankS x T)
    (hS₀1 : S₀ ≠ ⊥) (hz : zpowers z ≤ normalizer (S₀ : Set G)) :
    normalizer (S₀ : Set G) ≤ M := by
  have hS₀2 : IsPGroup 2 S₀ := c.S_isPGroup.to_le hS₀S
  have hxC : x ∈ centralizer (S₀ : Set G) := by
    rw [mem_centralizer_iff]
    intro h hh
    exact mem_centralizer_singleton_iff.mp (hS₀S hh).2
  have hxN : x ∈ normalizer (S₀ : Set G) := Subgroup.centralizer_le_normalizer (S₀ : Set G) hxC
  have hB : zpowers x ⊔ zpowers z ≤ normalizer (S₀ : Set G) :=
    sup_le (zpowers_le.mpr hxN) hz
  exact c.prop614 (normalizer (S₀ : Set G)) ⟨S₀, hS₀1, hS₀2, rfl⟩ hB
    ⟨S₀, le_inf le_normalizer (hS₀S.trans c.S_le_M), hS₀1, hS₀2, hB⟩

theorem R_le_S (c : S62Config p P M x z T) : smallRankR x z T ≤ smallRankS x T := by
  refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
  have hanorm : a ∈ normalizer (smallRankS x T : Set G) := c.z_le_normalizer_S ha
  have h1 : a * b * a⁻¹ ∈ smallRankS x T := (mem_normalizer_iff.mp hanorm b).mp hb
  rw [commutatorElement_def]
  exact mul_mem h1 (inv_mem hb)

theorem z_le_normalizer_R (c : S62Config p P M x z T) :
    zpowers z ≤ normalizer (smallRankR x z T : Set G) := by
  rw [zpowers_le, mem_normalizer_iff_map_conj_eq]
  have hzS : (smallRankS x T).map (MulAut.conj z).toMonoidHom = smallRankS x T :=
    mem_normalizer_iff_map_conj_eq.mp (c.z_le_normalizer_S (mem_zpowers z))
  have hzz : (zpowers z).map (MulAut.conj z).toMonoidHom = zpowers z := by
    rw [MonoidHom.map_zpowers]
    simp [MulAut.conj_apply]
  have h := Subgroup.map_commutator (H₁ := zpowers z) (H₂ := smallRankS x T)
    (MulAut.conj z).toMonoidHom
  rw [hzS, hzz] at h
  exact h

end S62Config

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
