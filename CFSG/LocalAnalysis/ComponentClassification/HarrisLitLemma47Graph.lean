module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Lift

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ}

namespace Standing.Setup42

variable {h : Standing t L p f} {S : Subgroup X} {hS : IsSylowOf 2 S (centralizer ({t} : Set X))}
  {w z : X}

theorem z_mem_centralizer_beta (hFC : AutPSL2FieldCentralizerInput)
    (hKC : AutPSL2CentralizerInput) (hσ : Setup42 h hS w z) (i j : ℕ) :
    z ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) :=
  (centralizerResidual_le (hσ.z_mem_Dstar hFC hKC i j).2).2

theorem z_ne_beta (hσ : Setup42 h hS w z) (i j : ℕ) : z ≠ w ^ (orderOf w / 2) * t ^ i * z ^ j := by
  intro hzβ
  apply hσ.rho_beta_not_mem_inn i j
  have hzH : z ∈ centralizer ({t} : Set X) := hS.le hσ.z_mem.1
  have h1 := h.rho_mem_innAut (mem_sup_right hσ.z_mem.2) hzH
  rwa [show (⟨z, hzH⟩ : ↥(centralizer ({t} : Set X))) = ⟨_, hσ.beta_mem_H i j⟩ from
    Subtype.ext hzβ] at h1

theorem exists_two_components [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hGA : TBLit.GriessMultipliersOdd) (hσ : Setup42 h hS w z) (i j : ℕ) {k : ℕ}
    (hk : 1 ≤ k) (hs5 : 5 ≤ p ^ k)
    (hgraph : ∀ w' ∈ GSThmB.layerIn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
        centralizer {hσ.tBar i j}), orderOf w' = 2 →
      ∃ X₁ X₂ : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)), X₁ ≠ X₂ ∧
        X₁ ≤ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓ centralizer {w'} ∧
        X₂ ≤ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓ centralizer {w'} ∧
        (X₁.subgroupOf (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
          centralizer {w'})).IsSubnormal ∧
        (X₂.subgroupOf (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
          centralizer {w'})).IsSubnormal ∧
        X₁ ≤ centralizer (X₂ : Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ∧
        X₁ ⊓ X₂ = zpowers w' ∧ IsSLTwoOver (p ^ k) ↥X₁ ∧ IsSLTwoOver (p ^ k) ↥X₂) :
    ∃ J₁ J₂ : Subgroup X, J₁ ≠ J₂ ∧
      (IsTwoComponentIn J₁ (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j} ⊓
          centralizer {z}) ∧ IsMTypeSchur p ↥J₁ ∧ z ∈ J₁ ∧
        IsSLTwoOver (p ^ k) (↥J₁ ⧸ pPrimeCore 2 ↥J₁)) ∧
      (IsTwoComponentIn J₂ (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j} ⊓
          centralizer {z}) ∧ IsMTypeSchur p ↥J₂ ∧ z ∈ J₂ ∧
        IsSLTwoOver (p ^ k) (↥J₂ ⧸ pPrimeCore 2 ↥J₂)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : p.Prime := h.config.prime
  have hp2 : p ≠ 2 := h.config.ne_two
  have hzβ := hσ.z_mem_centralizer_beta hFC hKC i j
  have hO : pPrimeCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) = ⊥ :=
    pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have hzK : (QuotientGroup.mk ⟨z, hzβ⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∈
      GSThmB.layerIn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
        centralizer {hσ.tBar i j}) := by
    rw [hσ.layerIn_layer_centralizer_tBar hnonab hK hSch hFC hKC i j]
    exact ⟨⟨z, hzβ⟩, (hσ.z_mem_Dstar hFC hKC i j).2, rfl⟩
  have hz2 : orderOf (QuotientGroup.mk ⟨z, hzβ⟩ :
      MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) = 2 := by
    have hz2' : z ^ 2 = 1 := by
      have h1 := pow_orderOf_eq_one z
      rwa [hσ.z_order] at h1
    have hsq : (⟨z, hzβ⟩ : ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))) ^ 2
        = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hz2')
    refine orderOf_eq_prime (by rw [← QuotientGroup.mk_pow, hsq, QuotientGroup.mk_one]) ?_
    intro h1
    rw [QuotientGroup.eq_one_iff] at h1
    have hdvd := Subgroup.orderOf_dvd_natCard _ h1
    rw [Subgroup.orderOf_mk, hσ.z_order] at hdvd
    exact absurd hdvd (Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card)
  obtain ⟨X₁, X₂, hne, hX₁, hX₂, hs₁, hs₂, -, hint, hsl₁, hsl₂⟩ := hgraph _ hzK hz2
  have hEn : (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).Normal := by
    have := LocalCores.layer_characteristic (G := MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))
    infer_instance
  have hzX : ∀ Y : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)),
      X₁ ⊓ X₂ ≤ Y → (QuotientGroup.mk ⟨z, hzβ⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∈ Y :=
    fun Y hY => hY (hint ▸ mem_zpowers _)
  have hlift : ∀ Y : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)),
      Y ≤ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
        centralizer {(QuotientGroup.mk ⟨z, hzβ⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))} →
      (Y.subgroupOf (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
        centralizer {(QuotientGroup.mk ⟨z, hzβ⟩ :
          MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))})).IsSubnormal →
      IsSLTwoOver (p ^ k) ↥Y →
      (QuotientGroup.mk ⟨z, hzβ⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∈ Y →
      ∃ J : Subgroup X, IsTwoComponentIn J (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j} ⊓
          centralizer {z}) ∧ IsMTypeSchur p ↥J ∧ z ∈ J ∧
        IsSLTwoOver (p ^ k) (↥J ⧸ pPrimeCore 2 ↥J) ∧
        (J.subgroupOf (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j})).map
          (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer
            ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))) = Y := by
    intro Y hYle hYsub hYsl hzY
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
    obtain ⟨J, hJle, hJp, hzJ, hJmap, g, hg, hgk⟩ :=
      Lemma47.exists_lift_two_component hzβ hσ.z_order (hYle.trans inf_le_right) hYp' hzY
    have hJ2 : IsTwoComponentIn J (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j} ⊓
        centralizer {z}) := (isTwoComponentIn_iff hJle).mpr hJp
    obtain ⟨eO⟩ := GSThmB.OddQuot.nonempty_pPrimeCore_equiv_of_surjective g hg hgk
    obtain ⟨F, hF1, hF2, hF, ⟨eF⟩⟩ := hYsl
    exact ⟨J, hJ2, isMTypeSchur_of_surjective hGA hp hp2 g hg hgk hJ2.2.2.1 hYq hYO hYZ hYm,
      hzJ, ⟨F, hF1, hF2, hF, ⟨eO.trans ((QuotientGroup.quotientMulEquivOfEq hYO).trans
        (QuotientGroup.quotientBot.trans eF))⟩⟩, hJmap⟩
  obtain ⟨J₁, hJ₁, hM₁, hz₁, hJsl₁, hmap₁⟩ := hlift X₁ hX₁ hs₁ hsl₁ (hzX X₁ inf_le_left)
  obtain ⟨J₂, hJ₂, hM₂, hz₂, hJsl₂, hmap₂⟩ := hlift X₂ hX₂ hs₂ hsl₂ (hzX X₂ inf_le_right)
  refine ⟨J₁, J₂, fun h12 => hne ?_, ⟨hJ₁, hM₁, hz₁, hJsl₁⟩, ⟨hJ₂, hM₂, hz₂, hJsl₂⟩⟩
  rw [← hmap₁, ← hmap₂, h12]

end Standing.Setup42

end CFSG.ComponentClassification.HarrisLit
