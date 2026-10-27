module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma46b
import CFSG.GroupTheory.Fitting.LayerTopBot

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools
open scoped commutatorElement

theorem pCore_le_centralizer_layer {G : Type*} [Group G] [Finite G] :
    pCore 2 G ≤ centralizer (layer G : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.WholeGroup.pCore_le_centralizer_layer 2

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ}

omit [Finite X] in
theorem betaBar_mem_pCore {β : X} (hβ2 : β ^ 2 = 1) : betaBar β ∈ pCore 2 (MBar β) := by
  refine (le_sSup (s := {K : Subgroup (MBar β) | K.Normal ∧ IsPGroup 2 K})
    ⟨?_, ?_⟩ : zpowers (betaBar β) ≤ pCore 2 (MBar β)) (mem_zpowers _)
  · refine ⟨fun n hn g => ?_⟩
    have hnc : n ∈ center (MBar β) := (zpowers_le.mpr (betaBar_mem_center β)) hn
    rw [mem_center_iff.mp hnc g, mul_inv_cancel_right]
    exact hn
  · refine IsPGroup.of_card (n := (orderOf (betaBar β)).factorization 2) ?_
    rw [Nat.card_zpowers]
    have hd : orderOf (betaBar β) ∣ 2 ^ 1 := by
      rw [pow_one]
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [betaBar, ← QuotientGroup.mk_pow,
        show (⟨β, mem_centralizer_singleton_iff.mpr rfl⟩ : ↥(centralizer ({β} : Set X))) ^ 2 =
          1 from Subtype.ext (by rw [Subgroup.coe_pow, hβ2, Subgroup.coe_one]),
        QuotientGroup.mk_one]
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    rw [hk, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]

namespace Standing.Setup42

variable {h : Standing t L p f} {S : Subgroup X} {hS : IsSylowOf 2 S (centralizer ({t} : Set X))}
  {w z : X}

theorem KBar_le_layer [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hσ : Setup42 h hS w z) (i j : ℕ) :
    KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j) ≤
      layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
  rw [← hσ.layerIn_layer_centralizer_tBar hnonab hK hSch hFC hKC i j]
  exact (map_subtype_le _).trans inf_le_left

theorem lemma46f [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hσ : Setup42 h hS w z) (i j : ℕ) :
    pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔ zpowers (hσ.tBar i j) ≤
        centralizer (KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j) :
          Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ∧
      (Nat.card ↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔
          zpowers (hσ.tBar i j)) = 4 ∨
        (∃ k : ℕ, 2 ≤ k ∧ Nonempty (↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔
          zpowers (hσ.tBar i j)) ≃* DihedralGroup (2 ^ k))) ∨
        ∃ n : ℕ, 4 ≤ n ∧ Nonempty (↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔
          zpowers (hσ.tBar i j)) ≃* CFSG.Open.SemidihedralGroup n)) ∧
      betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) ∈
        pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓ centralizer {hσ.tBar i j} ∧
      pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓ centralizer {hσ.tBar i j} ≤
        closure {hσ.tBar i j, betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hβ2 := hσ.sq_eq_one_of_mem_X (beta_mem_X i j)
  have hβO := betaBar_mem_pCore hβ2
  have hOK : pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ≤
      centralizer (KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j) :
        Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) :=
    pCore_le_centralizer_layer.trans
      (centralizer_le (hσ.KBar_le_layer hnonab hK hSch hFC hKC i j))
  have hQK : pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔ zpowers (hσ.tBar i j) ≤
      centralizer (KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j) :
        Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) :=
    sup_le hOK (zpowers_le.mpr (hσ.tBar_mem_centralizer_K i j))
  have htt : t ^ 2 = 1 := by
    have := pow_orderOf_eq_one t
    rwa [h.config.orderOf_eq] at this
  have ht2 : IsPGroup 2 (zpowers (hσ.tBar i j)) := by
    have hd : orderOf (hσ.tBar i j) ∣ 2 ^ 1 := by
      rw [pow_one]
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [tBar, ← QuotientGroup.mk_pow,
        show (⟨t, hσ.t_mem_centralizer_beta i j⟩ :
          ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))) ^ 2 = 1 from
          Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact htt),
        QuotientGroup.mk_one]
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hk])
  have hQ2 : IsPGroup 2 ↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔
      zpowers (hσ.tBar i j)) := by
    have := pCore_normal (p := 2) (G := MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))
    exact IsPGroup.to_sup_of_normal_left pCore_isPGroup ht2
  obtain ⟨hshape, hcen⟩ := hσ.shape_of_le_centralizer_K hFC hKC i j _ hQ2 hQK
    (mem_sup_right (mem_zpowers _)) (mem_sup_left hβO)
  refine ⟨hQK, hshape, ⟨hβO, mem_centralizer_singleton_iff.mpr ?_⟩,
    (inf_le_inf_right _ le_sup_left).trans hcen⟩
  exact (mem_center_iff.mp (betaBar_mem_center _) _).symm

end Standing.Setup42

end CFSG.ComponentClassification.HarrisLit
