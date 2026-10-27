module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47GraphEnd
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ}

namespace Standing.Setup42

variable {h : Standing t L p f} {S : Subgroup X} {hS : IsSylowOf 2 S (centralizer ({t} : Set X))}
  {w z : X}

theorem exists_J_of_sl2 (hGA : TBLit.GriessMultipliersOdd) (hσ : Setup42 h hS w z)
    (i j : ℕ) (hzβ : z ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)) {k : ℕ}
    (hk : 1 ≤ k) (hs5 : 5 ≤ p ^ k) {Y : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))}
    (hYle : Y ≤ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
      centralizer {(QuotientGroup.mk ⟨z, hzβ⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))})
    (hYsub : (Y.subgroupOf (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
      centralizer {(QuotientGroup.mk ⟨z, hzβ⟩ :
        MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))})).IsSubnormal)
    (hYsl : IsSLTwoOver (p ^ k) ↥Y)
    (hzY : (QuotientGroup.mk ⟨z, hzβ⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∈ Y) :
    ∃ J : Subgroup X, IsTwoComponentIn J (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j} ⊓
        centralizer {z}) ∧ IsMTypeSchur p ↥J ∧ z ∈ J ∧
      IsSLTwoOver (p ^ k) (↥J ⧸ pPrimeCore 2 ↥J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : p.Prime := h.config.prime
  have hp2 : p ≠ 2 := h.config.ne_two
  have hEn : (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).Normal := by
    have := LocalCores.layer_characteristic (G := MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))
    infer_instance
  obtain ⟨hYq, hYZ, hYm, hYO⟩ := Lemma47.sl2_facts hp hp2 hk hs5 hYsl
  have hYq2 : IsTwoQuasisimple ↥Y := ⟨hYq.1, LocalCores.isQuasisimple_of_mulEquiv
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hYO.symm)) hYq⟩
  have hYp : IsPComponent 2 (Y.subgroupOf (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
      centralizer {(QuotientGroup.mk ⟨z, hzβ⟩ :
        MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))})) :=
    (isTwoComponentIn_iff hYle).mp ⟨hYle, hYsub, hYq2⟩
  have hN : ((layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
      centralizer {(QuotientGroup.mk ⟨z, hzβ⟩ :
        MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))}).subgroupOf
      (centralizer {(QuotientGroup.mk ⟨z, hzβ⟩ :
        MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))})).IsSubnormal := by
    rw [inf_subgroupOf_right]
    exact (hEn.subgroupOf _).isSubnormal
  have hYp' := UnbalancedCorr.isPComponent_subgroupOf_of_isSubnormal hYle inf_le_right hN hYp
  obtain ⟨J, hJle, hJp, hzJ, -, g, hg, hgk⟩ :=
    Lemma47.exists_lift_two_component hzβ hσ.z_order (hYle.trans inf_le_right) hYp' hzY
  have hJ2 : IsTwoComponentIn J (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j} ⊓
      centralizer {z}) := (isTwoComponentIn_iff hJle).mpr hJp
  obtain ⟨eO⟩ := GSThmB.OddQuot.nonempty_pPrimeCore_equiv_of_surjective g hg hgk
  obtain ⟨F, hF1, hF2, hF, ⟨eF⟩⟩ := hYsl
  exact ⟨J, hJ2, isMTypeSchur_of_surjective hGA hp hp2 g hg hgk hJ2.2.2.1 hYq hYO hYZ hYm, hzJ,
    ⟨F, hF1, hF2, hF, ⟨eO.trans ((QuotientGroup.quotientMulEquivOfEq hYO).trans
      (QuotientGroup.quotientBot.trans eF))⟩⟩⟩

theorem lemma35_L3U3 [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X) (hcat : ¬ Blueprint.Catalog X)
    (_hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hI : AutPSL2InvolutionInput) (h219 : Harris82Lemma219Input) (h35 : Harris81Lemma35Step)
    (hC8 : AlternatingCoverInvolutionFact) (hσ : Setup42 h hS w z) (i j : ℕ) {J : Subgroup X}
    (hJ : IsTwoComponentIn J (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j} ⊓
      centralizer {z})) (hM : IsMTypeSchur p ↥J) (hzJ : z ∈ J) {k : ℕ} (hk : 1 ≤ k)
    (hs5 : 5 ≤ p ^ k) (hJsl : IsSLTwoOver (p ^ k) (↥J ⧸ pPrimeCore 2 ↥J)) :
    ∃ K : Subgroup X, IsTwoComponentIn K (centralizer {z}) ∧
      J = GSThmB.layerIn (K ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) ∧
      K.map (MulAut.conj (w ^ (orderOf w / 2) * t ^ i * z ^ j)).toMonoidHom = K ∧
      IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K) ∧
      Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K)) = 16 ∧
      GrSLit.IsL34Type ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K)) ∧
      IsSLTwoOver 7 (↥J ⧸ pPrimeCore 2 ↥J) := by
  have hp : p.Prime := h.config.prime
  have hp2 : p ≠ 2 := h.config.ne_two
  have hβ2 := hσ.orderOf_beta i j
  have hzβ := hσ.z_mem_centralizer_beta hFC hKC i j
  have hz1 : z ≠ 1 := fun h1 => by
    have := hσ.z_order
    rw [h1, orderOf_one] at this
    exact absurd this (by norm_num)
  have hW := Lemma47.fourGroup_closure_pair hβ2 hσ.z_order (hσ.z_ne_beta i j)
    (mem_centralizer_singleton_iff.mp hzβ).symm
  have hCW := Lemma47.centralizer_closure_pair (w ^ (orderOf w / 2) * t ^ i * z ^ j) z
  have hJW : IsTwoComponentIn J (centralizer ((closure {w ^ (orderOf w / 2) * t ^ i * z ^ j, z} :
      Subgroup X) : Set X)) := by
    rw [hCW]; exact hJ
  have hzW : z ∈ (closure {w ^ (orderOf w / 2) * t ^ i * z ^ j, z} : Subgroup X) :=
    subset_closure (Set.mem_insert_of_mem _ rfl)
  have hβW : w ^ (orderOf w / 2) * t ^ i * z ^ j ∈
      (closure {w ^ (orderOf w / 2) * t ^ i * z ^ j, z} : Subgroup X) :=
    subset_closure (Set.mem_insert _ _)
  have hβz : w ^ (orderOf w / 2) * t ^ i * z ^ j ∉ zpowers z := by
    intro h1
    rcases eq_one_or_eq_of_mem_zpowers_two hσ.z_order h1 with h1 | h1
    · rw [h1, orderOf_one] at hβ2; exact absurd hβ2 (by norm_num)
    · exact hσ.z_ne_beta i j h1.symm
  have hJW' : J ⊓ (closure {w ^ (orderOf w / 2) * t ^ i * z ^ j, z} : Subgroup X) ≠ ⊥ := by
    intro hb
    have : z ∈ (⊥ : Subgroup X) := hb ▸ ⟨hzJ, hzW⟩
    exact hz1 (mem_bot.mp this)
  obtain ⟨-, -, hKc, hKβ, hJeq, hcases⟩ :=
    h35 X hnonab hK hcat p hp hp2 _ hW.1 hW.2 J hJW hM k hk hs5 hJsl hJW' z ⟨hzJ, hzW⟩ hz1 _
      hβW hβz _ rfl
  set K := GSThmB.conjClosure J (GSThmB.layerIn (centralizer {z}))
  have h44z := (hσ.isPGroup_quot_centralizer_z hI).1
  have htz := hσ.t_mem_centralizer_z
  have hKt := map_conj_eq_of_isTwoComponentIn h219 h.config.orderOf_eq htz h44z hKc
  have hCK := isPGroup_quot_inf_centralizer h44z hKc.1
  have htN := Lemma47.mem_normalizer_of_map_conj_eq hKt
  have ht2 : t * t = 1 := by rw [← sq, ← h.config.orderOf_eq, pow_orderOf_eq_one]
  have hKK : ⁅K, K⁆ = K := Lemma47.commutator_self_eq_of_isPerfect hKc.2.2.1
  obtain ⟨eZ⟩ := FooteLit.nonempty_fusionZStar_quotient_equiv ↥K
  refine ⟨K, hKc, hJeq, hKβ, ?_⟩
  rcases hcases with ⟨-, hsl, hq, h16, hL⟩ | ⟨-, -, n, hn, -, -, ⟨e⟩⟩ | ⟨-, -, n, hn, -, -, ⟨e⟩⟩
  · exact ⟨hq, h16, hL, hsl⟩
  · exact absurd hCK (hC8 X K t (2 * n + 1) (by omega) hKK ⟨eZ.trans e⟩ htN ht2)
  · exact absurd hCK (hC8 X K t (2 * n) (by omega) hKK ⟨eZ.trans e⟩ htN ht2)

end Standing.Setup42

end CFSG.ComponentClassification.HarrisLit
