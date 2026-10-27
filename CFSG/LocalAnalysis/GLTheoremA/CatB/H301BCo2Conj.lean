module

public import CFSG.Sporadic.Co2Schreier.Classes
import CFSG.RankThree.PartTwo.Census.Sporadic.Centralizer
public import CFSG.Sporadic.Co2Schreier.ThirdE

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B.Co2Conj

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.Co2Schreier

private theorem card_centralizer_conj {g x y : Equiv.Perm (Fin 2300)} (hg : g ∈ co2P)
    (h : g * x * g⁻¹ = y) :
    Nat.card ↥(co2P ⊓ Subgroup.centralizer ({y} : Set (Equiv.Perm (Fin 2300)))) =
      Nat.card ↥(co2P ⊓ Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 2300)))) := by
  subst h
  exact CFSG.RankThree.PartTwo.Census.card_inf_centralizer_conj co2P
    (fun m hm => co2P.mul_mem (co2P.mul_mem hg hm) (co2P.inv_mem hg))
    (fun m hm => co2P.mul_mem (co2P.mul_mem (co2P.inv_mem hg) hm) hg) x


theorem exists_conj_locZ {z' : Equiv.Perm (Fin 2300)} (hz : z' ∈ co2P) (h2 : z' * z' = 1)
    (h1 : z' ≠ 1)
    (h27 : 27 ∣ Nat.card ↥(co2P ⊓ Subgroup.centralizer ({z'} : Set (Equiv.Perm (Fin 2300))))) :
    ∃ g ∈ co2P, g * z' * g⁻¹ = locZ := by
  have key : ∀ y : co2P, IsConj (⟨z', hz⟩ : co2P) y → ∃ g ∈ co2P, g * z' * g⁻¹ = y := by
    intro y hy
    obtain ⟨c, hc⟩ := isConj_iff.1 hy
    exact ⟨c, c.2, congrArg Subtype.val hc⟩
  rcases invol_cases ⟨z', hz⟩ (Subtype.ext h2) (fun h => h1 (congrArg Subtype.val h)) with
    h | h | h
  · exact key zP h
  · obtain ⟨g, hg, hgt⟩ : ∃ g ∈ co2P, g * z' * g⁻¹ = locT := key tP h
    have ht : Nat.card ↥(co2P ⊓ Subgroup.centralizer ({locT} : Set (Equiv.Perm (Fin 2300)))) =
        41287680 := by
      rw [← locD_eq_centralizer, card_locD]
    rw [← card_centralizer_conj hg hgt, ht] at h27
    norm_num at h27
  · obtain ⟨g, hg, hgu⟩ : ∃ g ∈ co2P, g * z' * g⁻¹ = locU := key uP h
    have hu : Nat.card ↥(co2P ⊓ Subgroup.centralizer ({locU} : Set (Equiv.Perm (Fin 2300)))) =
        1474560 := card_locH3
    rw [← card_centralizer_conj hg hgu, hu] at h27
    norm_num at h27

end CFSG.LocalAnalysis.GLTheoremA.H301B.Co2Conj

end
