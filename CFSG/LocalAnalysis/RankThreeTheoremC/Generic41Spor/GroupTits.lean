module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupBridge
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupWitness
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivialSporadicTits
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallTitsOrbits
import CFSG.RankThree.PartOne.CTP.SeitzExcModels
import CFSG.Sporadic.Schreier.TitsOuter
import CFSG.Sporadic.Schreier.TitsInv
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Defs
public import CFSG.Sporadic.Schreier.TitsLocal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open Subgroup CFSG.Sporadic.Schreier.Tits CFSG.AGLEmbeddingD2
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivial


structure TitsFacts : Prop where
  sylow : ∀ (K : Type) [Group K] [Finite K], IsTitsType 5 K → SylowIsPlane 5 K
  noOuter : ∀ (K : Type) [Group K] [Finite K], IsTitsType 5 K → NoOuterP 5 K
  trans : ∀ (K : Type) [Group K] [Finite K], IsTitsType 5 K → NormalizerTransitive 5 K
  maximal : ∀ (K : Type) [Group K] [Finite K], IsTitsType 5 K → NormalizerMaximal 5 K
  sigTriv : SignalizerTrivialX IsTitsType 5
  lemma45 : Lemma45Facts IsTitsType 5 TitsShape

theorem tits_local {K : Type} [Group K] [Finite K] (hK : IsTitsType 5 K) (S : Sylow 5 K) :
    Nat.card (S : Subgroup K) = 5 ^ 2 ∧
      (∀ Y : Subgroup K, normalizer ((S : Subgroup K) : Set K) ≤ Y →
        Y = normalizer ((S : Subgroup K) : Set K) ∨ Y = ⊤) ∧
      ∀ x ∈ (S : Subgroup K), x ^ 5 = 1 := by
  obtain ⟨-, hv, ⟨e⟩⟩ := hK
  have hd : (⟨.tits, hv⟩ : TauCeti.ValidLieTypeIndex).1 = .tits := rfl
  obtain ⟨eS⟩ := titsModelEquiv K 2 1 (CFSG.RankThree.PartOne.CTP.reeTitsModel_tits ⟨hv, ⟨e⟩⟩)
  have hKc : Subgroup.centralizer (((⊤ : Subgroup K) : Subgroup K) : Set K) = ⊥ := by
    rw [Subgroup.coe_top, Subgroup.centralizer_univ,
      CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivial.center_eq_bot_of_mulEquiv
        eS titsD_center]
  obtain ⟨-, hcard, hmax, -, -, t, htN, m, -, -, hm, -, -, -, -, hline⟩ :=
    d2TorusLocalAt_tits ⟨.tits, hv⟩ hd K ⊤ inferInstance hKc ⟨Subgroup.topEquiv.trans e⟩ 5 rfl S
  refine ⟨hcard, hmax, ?_⟩
  exact CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivial.pow_eq_one_of_torus
    Nat.prime_five hcard htN fun Y₀ hY₀ hY₀c => by simpa using hline 1 one_pos (by omega) Y₀ hY₀ hY₀c

theorem tits_sylow : ∀ (K : Type) [Group K] [Finite K], IsTitsType 5 K → SylowIsPlane 5 K := by
  intro K _ _ hK S
  obtain ⟨hcard, -, hexp⟩ := tits_local hK S
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : IsMulCommutative ↥(S : Subgroup K) := IsPGroup.isMulCommutative_of_card_eq_prime_sq hcard
  exact ⟨⟨inferInstance, hexp⟩, hcard⟩

theorem tits_trans : ∀ (K : Type) [Group K] [Finite K], IsTitsType 5 K → NormalizerTransitive 5 K := by
  intro K _ _ hK S
  obtain ⟨-, hv, ⟨e⟩⟩ := hK
  obtain ⟨eD⟩ := CFSG.AGLEmbedding.KFactProofs.SmallIdent.nonempty_equiv_tits (K := K)
    ⟨⟨.tits, hv⟩, rfl, ⟨e⟩⟩
  exact CFSG.AGLEmbedding.KFactProofs.SmallIdent.OrbitTrans.of_equiv_all (by norm_num) eD
    CFSG.AGLEmbedding.KFactProofs.SmallIdent.orbitTrans_titsD S

theorem tits_noOuter : ∀ (K : Type) [Group K] [Finite K], IsTitsType 5 K → NoOuterP 5 K := by
  intro K _ _ hK
  obtain ⟨-, hv, ⟨e⟩⟩ := hK
  have hd : (⟨.tits, hv⟩ : TauCeti.ValidLieTypeIndex).1 = .tits := rfl
  unfold NoOuterP
  rw [card_outer_tits_of_mulEquiv ⟨.tits, hv⟩ hd e]
  norm_num

theorem tits_maximal : ∀ (K : Type) [Group K] [Finite K], IsTitsType 5 K → NormalizerMaximal 5 K := by
  intro K _ _ hK S
  exact (tits_local hK S).2.1

theorem tits_sigTriv : SignalizerTrivialX IsTitsType 5 :=
  signalizerTrivialX_of_on Nat.prime_five fun K _ _ hK =>
    signalizerTrivialTits_holds K hK.2

theorem tits_witness_D : ∃ u₀ : titsD, orderOf u₀ = 5 ∧ TwoWitness u₀ := by
  obtain ⟨-, -, -, -, -, -, -, hHD, hHcard, hJcard, hJn, hCJ, -⟩ :=
    CTUC_Tits_two_involution_classes_and_centralizer_two_kernels
  have hJH : titsJ ≤ titsH := titsJ_le_titsH
  have hHle : titsH ≤ titsD := hHD ▸ inf_le_left
  have hJle : titsJ ≤ titsD := hJH.trans hHle
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := titsH) 5 (by rw [hHcard]; norm_num)
  have hxJ : (x : Equiv.Perm (Fin 1755)) ∈ normalizer (titsJ : Set (Equiv.Perm (Fin 1755))) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJH).1 hJn x.2
  have hxord : orderOf (x : Equiv.Perm (Fin 1755)) = 5 := by rw [Subgroup.orderOf_coe]; exact hx
  refine ⟨⟨(x : Equiv.Perm (Fin 1755)), hHle x.2⟩, ?_, titsJ.subgroupOf titsD, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_mk]; exact hxord
  · refine IsPGroup.of_card (n := 9) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJle).toEquiv, hJcard]
    norm_num
  · rw [Subgroup.mem_normalizer_iff]
    intro y
    have := Subgroup.mem_normalizer_iff.mp hxJ (y : Equiv.Perm (Fin 1755))
    simpa [Subgroup.mem_subgroupOf] using this
  · by_contra hcon
    have hcomm : ∀ v ∈ titsJ, v * (x : Equiv.Perm (Fin 1755)) = (x : Equiv.Perm (Fin 1755)) * v := by
      intro v hv
      by_contra hne
      apply hcon
      refine ⟨⟨v, hJle hv⟩, Subgroup.mem_subgroupOf.2 hv, ?_⟩
      intro h
      apply hne
      have := congrArg Subtype.val h
      exact this.symm
    have hxc : (x : Equiv.Perm (Fin 1755)) ∈ titsH ⊓ Subgroup.centralizer (titsJ : Set (Equiv.Perm (Fin 1755))) :=
      ⟨x.2, Subgroup.mem_centralizer_iff.2 hcomm⟩
    have hxJ' : (x : Equiv.Perm (Fin 1755)) ∈ titsJ := hCJ hxc
    have hdvd : orderOf (x : Equiv.Perm (Fin 1755)) ∣ Nat.card titsJ := by
      have h1 := orderOf_dvd_natCard (⟨(x : Equiv.Perm (Fin 1755)), hxJ'⟩ : titsJ)
      rwa [Subgroup.orderOf_mk] at h1
    rw [hxord, hJcard] at hdvd
    omega

theorem tits_witness : ∀ (K : Type) [Group K] [Finite K], IsTitsType 5 K →
    ∀ u : K, orderOf u = 5 → TwoWitness u := by
  intro K _ _ hK u hu
  have htrans := tits_trans K hK
  obtain ⟨-, hv, ⟨e⟩⟩ := hK
  obtain ⟨eD⟩ := CFSG.AGLEmbedding.KFactProofs.SmallIdent.nonempty_equiv_tits (K := K)
    ⟨⟨.tits, hv⟩, rfl, ⟨e⟩⟩
  obtain ⟨u₀, hu₀, h₀⟩ := tits_witness_D
  have h₀' : TwoWitness (eD.symm u₀) := h₀.of_mulEquiv eD.symm
  exact h₀'.of_orbit Nat.prime_five htrans (by rw [MulEquiv.orderOf_eq]; exact hu₀) hu

theorem tits_lemma45 : Lemma45Facts IsTitsType 5 TitsShape := by
  refine lemma45Facts_of_inner Nat.prime_five (by norm_num) ?_
  intro X _ _ K hK R U₀ hUR hUe hUc hshape
  obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hshape
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  have hU₀ : U₀ = Subgroup.zpowers u := eq_zpowers_of_card_prime Nat.prime_five hUc hu.1 hu1'
  have huK : u ∈ K := hu.2
  have hord : orderOf u = 5 := by
    rw [← Nat.card_zpowers, ← hU₀]; exact hUc
  have hW : TwoWitness (⟨u, huK⟩ : K) :=
    tits_witness K hK.2.2 ⟨u, huK⟩ (by rw [Subgroup.orderOf_mk]; exact hord)
  exact ⟨hU₀ ▸ (Subgroup.zpowers_le.2 huK), kwitness_to_x K huK hW hU₀⟩

theorem titsFacts_holds : TitsFacts :=
  ⟨tits_sylow, tits_noOuter, tits_trans, tits_maximal, tits_sigTriv, tits_lemma45⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
