module

public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdInputs
public import CFSG.GH74.Generic.S45.LQData
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Core
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Sections

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.ABGLocalTools Blueprint
open CFSG.ComponentClassification.RestrictedStd

variable {N : Type} [Group N] [Finite N] {L K Q : Subgroup N}

theorem Ivk73Cfg.exists_involution (h : Ivk73Cfg N L K Q) :
    ∃ u : N, orderOf u = 2 ∧ u ∈ centralizer (K : Set N) := by
  obtain ⟨u, huQ, -, -, hu2, -, -, -⟩ := C3.Layer1.U1a.exists_commuting_involutions h.Q_rank
  exact ⟨u, hu2, h.Q_sylow.le huQ⟩

theorem Ivk73Cfg.isComponentOf_centralizer (h : Ivk73Cfg N L K Q) {y : N} (hy2 : orderOf y = 2)
    (hy : y ∈ centralizer (K : Set N)) :
    CFSG.Assembly.IsComponentOf K (centralizer ({y} : Set N)) :=
  (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf
    (h.terminal y hy2 hy).1).2 (h.terminal y hy2 hy).2

theorem Ivk73Cfg.pPrimeCore_eq_center
    (h : Ivk73Cfg N L K Q) : pPrimeCore 2 ↥K = center ↥K := by
  have hnt : Nontrivial (↥K ⧸ pPrimeCore 2 ↥K) := CFSG.LocalCores.isQuasisimple_nontrivial h.K_u2.1
  have hle : pPrimeCore 2 ↥K ≤ center ↥K := by
    rcases LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple h.K_quasi (pPrimeCore 2 ↥K) with
      hle | htop
    · exact hle
    · exfalso
      have : Subsingleton (↥K ⧸ pPrimeCore 2 ↥K) := by
        rw [htop]
        exact QuotientGroup.subsingleton_quotient_top
      exact (not_nontrivial_iff_subsingleton.2 this) hnt
  refine le_antisymm hle ?_
  intro z hz
  have hodd := odd_center_K h.kbar_cases
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine LocalAnalysis.ComponentInitial.mem_pPrimeCore_of_mem_center hz ?_
  have h1 : orderOf (⟨z, hz⟩ : center ↥K) ∣ Nat.card (center ↥K) := orderOf_dvd_natCard _
  have h2 : orderOf z = orderOf (⟨z, hz⟩ : center ↥K) := (Subgroup.orderOf_mk z hz).symm
  rw [h2]
  exact (Nat.coprime_two_left.2 (Odd.of_dvd_nat hodd h1))

theorem Ivk73Cfg.smallSource
    (h : Ivk73Cfg N L K Q) : SmallSource K := by
  have hc := h.kbar_cases
  have hodd := odd_center_K hc
  have hZ := h.pPrimeCore_eq_center
  let e : (↥K ⧸ pPrimeCore 2 ↥K) ≃* (↥K ⧸ center ↥K) := QuotientGroup.quotientMulEquivOfEq hZ
  rcases hc with hL2 | hA
  · obtain ⟨-, -, -, q, hq5, hqodd, -, hP⟩ := Generic.S45.LAlt.hasL2Model_data hL2
    obtain ⟨p, f, hp, hf, ⟨hq5', hqo'⟩, hmodel⟩ := hP (fun x => 5 ≤ x ∧ Odd x) ⟨hq5, hqodd⟩
    refine Or.inl ⟨p, f, hp, ?_, hf, hq5', LieType.CurtisTits.lieModel_of_mulEquiv e hmodel, hodd⟩
    rintro rfl
    have h2 : Even (2 ^ f) := (Nat.even_pow.2 ⟨even_two, by omega⟩)
    exact (Nat.not_even_iff_odd.2 hqo') h2
  · obtain ⟨eA⟩ := hA
    exact Or.inr (Or.inl ⟨⟨e.symm.trans eA⟩, hodd⟩)

theorem Ivk73Cfg.centralizer_eq_bot (h : Ivk73Cfg N L K Q) : centralizer (L : Set N) = ⊥ := by
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  exact h.cent_trivial n fun l hl => (Subgroup.mem_centralizer_iff.1 hn l hl).symm

theorem Ivk73Cfg.exists_noncomm (h : Ivk73Cfg N L K Q) : ∃ a b : ↥L, a * b ≠ b * a :=
  exists_noncomm_of_le_isQuasisimple h.K_le h.K_quasi

theorem Ivk73Cfg.exists_hsrc
    (h : Ivk73Cfg N L K Q) :
    ∃ p f : ℕ, p ≠ 2 ∧
      (CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥K ⧸ center ↥K) .PSL 2 p f ∨
        Nonempty (↥K ⧸ center ↥K ≃* alternatingGroup (Fin 7)) ∨
        CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥K ⧸ center ↥K) .PSL 3 2 2) := by
  rcases h.smallSource with ⟨p, f, -, hp2, -, -, hmodel, -⟩ | ⟨hA, -⟩ | h34
  · exact ⟨p, f, hp2, Or.inl (Generic.S45.LQ.stated_of_lieModel_PSL hmodel)⟩
  · exact ⟨3, 1, by norm_num, Or.inr (Or.inl hA)⟩
  · exact ⟨3, 1, by norm_num, Or.inr (Or.inr (Generic.S45.LQ.stated_of_lieModel_PSL h34))⟩

end CFSG.GH74.GLS.IVK
