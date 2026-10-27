module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5YSpecB
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.InvClasses
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableKP
public import Certificates.Certificate442202
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeK
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableKSpec

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Simple2S5

open Subgroup CFSG.EvenSporadicStandard.HNRecog

theorem centFacts_of_K {r : WClass} {t : Equiv.Perm (Fin 1408)} {O : Subgroup (Equiv.Perm (Fin 1408))}
    {s₁ s₂ : Equiv.Perm (Fin 1408)} {i : ℕ} (hr : ClassSpec r t)
    (hcent : r.centOrder = 30720) (h : CentFactsK t O s₁ s₂ r.centGens i) :
    CentFacts t O s₁ s₂ := by
  have hC : Nat.card ↥(P1408 ⊓ Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin 1408)))) =
      30720 := hr.cent_card.trans hcent
  have hcl : closure (elemW '' {w | w ∈ r.centGens}) =
      P1408 ⊓ Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin 1408))) := hr.cent_eq
  refine
    { card_O := h.card_O
      O_le := h.O_le
      mem_O := h.mem_O
      norm_O := ?_
      card_C := ?_
      s₁_mem := h.s₁_mem
      s₂_mem := h.s₂_mem
      s₁_sq := h.s₁_sq
      s₂_pow := h.s₂_pow }
  · rw [← hcl]
    refine norm_of_gens O ?_
    rintro _ ⟨w, hw, rfl⟩ o ho
    exact h.norm_gens w hw o ho
  · have hDC : pPrime ⊓ Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin 1408))) ≤
        P1408 ⊓ Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin 1408))) := by
      intro x hx
      exact Subgroup.mem_inf.2
        ⟨pPrime_le (Subgroup.mem_inf.1 hx).1, (Subgroup.mem_inf.1 hx).2⟩
    have hgC : elemW (r.centGens.getD i []) ∈
        P1408 ⊓ Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin 1408))) := by
      have h' := elemW_getD_mem r.centGens i
      rw [hcl] at h'
      exact h'
    have hgnot : elemW (r.centGens.getD i []) ∉
        pPrime ⊓ Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin 1408))) := by
      intro hx
      have hp : elemW (r.centGens.getD i []) ∈ pPrime := (Subgroup.mem_inf.1 hx).1
      exact h.swap (Subgroup.mem_inf.1 hp).2
    have hlt : Nat.card ↥(pPrime ⊓
        Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin 1408)))) < 30720 := by
      by_contra hge
      have hge' : 30720 ≤ Nat.card ↥(pPrime ⊓
          Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin 1408)))) := le_of_not_gt hge
      have heq := Subgroup.eq_of_le_of_card_ge hDC (by rw [hC]; exact hge')
      exact hgnot (by rw [heq]; exact hgC)
    have hdvd : Nat.card ↥(pPrime ⊓
        Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin 1408)))) ∣
        Nat.card ↥(P1408 ⊓ Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin 1408)))) :=
      Subgroup.card_dvd_of_le hDC
    rw [hC] at hdvd
    have := two_mul_le_of_dvd_of_lt hdvd hlt
    omega

section Cert

theorem yFacts_of_cert (hP : Nat.card ↥P1408 = 177408000) : YFacts := by
  have hspec := invClasses_classSpec hP
  have hK : YFactsK := Certificates.certificate442202
  exact
    { z := centFacts_of_K hspec.1 rfl hK.z
      az := centFacts_of_K hspec.2.1 rfl hK.az
      card_y₀ := hK.card_y₀
      card_y₁ := hK.card_y₁
      pairs_z := hK.pairs_z
      pairs_az := hK.pairs_az }

end Cert

end CFSG.EvenSporadicStandard.HNRecog.Simple2S5

end
