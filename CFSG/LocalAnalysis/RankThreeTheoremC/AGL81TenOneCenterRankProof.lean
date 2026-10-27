module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111ElevenTwentySeven
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeCfg
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieZZComp

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem agl81TenOneCenterRank_of (h98 : AGL81NineEightFour G) (h85 : Asc81bEightFive)
    (hD2 : NoXBlockFor G) (hZc : KFactBlockCenterCyclic) : AGL81TenOneCenterRank G := by
  intro hS p P M H Q K hd L hL hLn V hVL hVe hVc
  have hT := hd.toTwoLocalPhaseThree' hS h98
  have hK : Open.IsKGroup ↥M := (hT.toTwoLocalPair.isKGroup_of_isKProper hS.kProper).1
  have hA : Asc81bHyp M (pCoreOf 2 H) := hT.asc81bHyp
  have hLM : L ≤ M := hL.le
  have hVM : V ≤ M := hVL.trans hLM
  have hpc : pCoreOf 2 L ≤ pCoreOf 2 M := pCoreOf_le_of_normal_subgroupOf 2 L M hLM hLn
  have hX : ¬ InClassXBlock L := (hT.nineThree_not_one hK h85 hD2 hL).1
  have hSyl := hT.not_isSylowTwoOf_inf hK h85 hD2 hL
  let g : ↥V →* ↥M ⧸ CFSG.pCore 2 ↥M :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hVM)
  have hrange : g.range = barM M V := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  have hAL : barM M V ≤ barM M L := Subgroup.map_mono fun x hx => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hVL hx
  have hAC : barM M V ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rintro _ ⟨v, hv, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨l, hl, rfl⟩
    change (v : G) ∈ V at hv
    change (l : G) ∈ L at hl
    have hc : (v : G) * l * (v : G)⁻¹ * (l : G)⁻¹ ∈ pCoreOf 2 M := hpc (hVc v hv l hl)
    have hc' : v * l * v⁻¹ * l⁻¹ ∈ CFSG.pCore 2 ↥M := by
      obtain ⟨y, hy, hyx⟩ := hc
      have : y = v * l * v⁻¹ * l⁻¹ := Subtype.ext (by simpa using hyx)
      exact this ▸ hy
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (v * l * v⁻¹ * l⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hc'
    simp only [map_mul, map_inv] at h1
    exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)).symm
  have hV3 : ∀ v : ↥V, v ^ 3 = 1 := fun v => Subtype.ext (hVe.2 _ v.2)
  have hAp : IsPGroup 3 (barM M V) := by
    rw [← hrange]
    rintro ⟨_, v, rfl⟩
    exact ⟨1, Subtype.ext (by simp [← map_pow, hV3 v])⟩
  have hcyc : IsCyclic (barM M V) :=
    hZc G M (pCoreOf 2 H) L hK hA hL hX hSyl 3 Nat.prime_three (by norm_num) (barM M V) hAL hAC
      hAp
  have hinj : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro v hv
    have hmem : Subgroup.inclusion hVM v ∈ CFSG.pCore 2 ↥M := (QuotientGroup.eq_one_iff _).mp hv
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥M) ⟨_, hmem⟩
    have h2 : v ^ (2 ^ k) = 1 := by
      apply Subgroup.inclusion_injective hVM
      rw [map_pow, map_one]
      exact congrArg Subtype.val hk
    have hd : orderOf v ∣ Nat.gcd (2 ^ k) 3 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one (hV3 v))
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left k (by norm_num))] at hd
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)
  have : IsCyclic ↥V := by
    rw [← hrange] at hcyc
    exact isCyclic_of_surjective (MonoidHom.ofInjective hinj).symm.toMonoidHom
      (MonoidHom.ofInjective hinj).symm.surjective
  exact card_le_of_isCyclic_of_forall_pow_eq_one (by norm_num) hV3

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
