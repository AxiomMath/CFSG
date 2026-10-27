module

public import CFSG.Open.Defs
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Nilpotent
import CFSG.LocalAnalysis.ComponentClassification.Quasisimple

public section

namespace GL83.I243.Cover

variable {p : ℕ} {K : Type*} [Group K]

variable (p K) in
@[expose] def primeCentre : Subgroup K :=
  (CFSG.pPrimeCore p ↥(Subgroup.center K)).map (Subgroup.center K).subtype

theorem primeCentre_le_center : primeCentre p K ≤ Subgroup.center K := by
  rintro _ ⟨z, -, rfl⟩
  exact z.2

instance primeCentre_normal : (primeCentre p K).Normal :=
  Subgroup.normal_of_le_center primeCentre_le_center

theorem coprime_card_primeCentre [Finite K] [Fact p.Prime] :
    Nat.Coprime p (Nat.card (primeCentre p K)) := by
  have h : Nat.card (primeCentre p K) = Nat.card (CFSG.pPrimeCore p ↥(Subgroup.center K)) :=
    Subgroup.card_map_of_injective (Subgroup.center K).subtype_injective
  rw [h]
  exact CFSG.pPrimeCore_coprime_card

theorem pCore_le_center [Finite K] [Fact p.Prime] (hq : CFSG.Open.IsQuasisimple K) :
    CFSG.pCore p K ≤ Subgroup.center K := by
  have hn : (CFSG.pCore p K).Normal := CFSG.pCore_normal
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq
    (CFSG.pCore p K) with h | h
  · exact h
  · exfalso
    have hp : IsPGroup p (⊤ : Subgroup K) := h ▸ CFSG.pCore_isPGroup
    have := (hp.of_equiv Subgroup.topEquiv).isNilpotent
    have : Group.IsPerfect K := ⟨hq.1⟩
    have : Nontrivial K := CFSG.ComponentClassification.Quasisimple.nontrivial hq
    exact Group.IsPerfect.not_isSolvable K inferInstance

theorem exists_mul_eq_of_mem_center [Finite K] [Fact p.Prime] {z : K}
    (hz : z ∈ Subgroup.center K) :
    ∃ a ∈ CFSG.pCore p K, ∃ n ∈ primeCentre p K, a * n = z := by
  have htop := CFSG.nilpotent_top_le_pCore_sup_pPrimeCore (Q := ↥(Subgroup.center K)) (p := p)
    inferInstance
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_right.1
    (htop (Subgroup.mem_top (⟨z, hz⟩ : ↥(Subgroup.center K))))
  have hle : (CFSG.pCore p ↥(Subgroup.center K)).map (Subgroup.center K).subtype ≤
      CFSG.pCore p K := by
    apply le_sSup
    refine ⟨Subgroup.normal_of_le_center ?_, CFSG.pCore_isPGroup.map _⟩
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  exact ⟨(a : K), hle ⟨a, ha, rfl⟩, (b : K), ⟨b, hb, rfl⟩, congrArg Subtype.val hab⟩

theorem center_quotient_eq_map (hq : CFSG.Open.IsQuasisimple K) :
    Subgroup.center (K ⧸ primeCentre p K) =
      (Subgroup.center K).map (QuotientGroup.mk' (primeCentre p K)) := by
  have : Group.IsPerfect K := ⟨hq.1⟩
  exact (CFSG.ComponentClassification.Quasisimple.center_map_of_central_kernel
    (QuotientGroup.mk' (primeCentre p K)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']; exact primeCentre_le_center)).symm

theorem center_quotient_eq [Finite K] [Fact p.Prime] (hq : CFSG.Open.IsQuasisimple K) :
    Subgroup.center (K ⧸ primeCentre p K) =
      (CFSG.pCore p K).map (QuotientGroup.mk' (primeCentre p K)) := by
  rw [center_quotient_eq_map hq]
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨a, ha, n, hn, rfl⟩ := exists_mul_eq_of_mem_center (p := p) hz
    refine ⟨a, ha, ?_⟩
    have hn1 : QuotientGroup.mk' (primeCentre p K) n = 1 := (QuotientGroup.eq_one_iff n).2 hn
    rw [map_mul, hn1, mul_one]
  · exact Subgroup.map_mono (pCore_le_center hq)

theorem isQuasisimple_quotient (hq : CFSG.Open.IsQuasisimple K) :
    CFSG.Open.IsQuasisimple (K ⧸ primeCentre p K) :=
  CFSG.ComponentClassification.Quasisimple.central_quotient hq _ primeCentre_le_center

theorem nonempty_equiv_center_quotient (hq : CFSG.Open.IsQuasisimple K) :
    Nonempty ((K ⧸ primeCentre p K) ⧸ Subgroup.center (K ⧸ primeCentre p K) ≃*
      K ⧸ Subgroup.center K) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq (center_quotient_eq_map hq)).trans
    (QuotientGroup.quotientQuotientEquivQuotient (primeCentre p K) (Subgroup.center K)
      primeCentre_le_center)⟩

theorem isPGroup_center_quotient [Finite K] [Fact p.Prime] (hq : CFSG.Open.IsQuasisimple K) :
    IsPGroup p ↥(Subgroup.center (K ⧸ primeCentre p K)) := by
  rw [center_quotient_eq hq]
  exact CFSG.pCore_isPGroup.map _

theorem isCyclic_center_quotient [Finite K] [Fact p.Prime] (hq : CFSG.Open.IsQuasisimple K)
    (hcyc : IsCyclic ↥(CFSG.pCore p K)) :
    IsCyclic ↥(Subgroup.center (K ⧸ primeCentre p K)) := by
  rw [center_quotient_eq hq]
  exact isCyclic_of_surjective
    ((QuotientGroup.mk' (primeCentre p K)).subgroupMap (CFSG.pCore p K))
    ((QuotientGroup.mk' (primeCentre p K)).subgroupMap_surjective _)

theorem center_quotient_ne_bot [Finite K] [Fact p.Prime] (hq : CFSG.Open.IsQuasisimple K)
    (hZ : CFSG.pCore p K ≠ ⊥) : Subgroup.center (K ⧸ primeCentre p K) ≠ ⊥ := by
  rw [center_quotient_eq hq]
  intro h
  apply hZ
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (p := p) (G := K)).exists_card_eq
  have hdisj : Disjoint (CFSG.pCore p K) (primeCentre p K) :=
    Subgroup.disjoint_of_coprime_natCard (by
      rw [ha]
      exact Nat.Coprime.pow_left a coprime_card_primeCentre)
  exact hdisj.eq_bot_of_le h

end GL83.I243.Cover
