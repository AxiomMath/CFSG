module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenSL3SupC
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenCase234

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open Matrix
open CFSG.LocalAnalysis.AGL81TheoremCD.Section12 (ThreeTenTorusExclusion)

theorem d_le_I_of_threeTenHyp_of_isSLType {H : Type} [Group H] [Finite H]
    {I D P Y : Subgroup H} {p d : ℕ} (hhyp : ThreeTenHyp I D P Y p d)
    (e : ↥I ≃* SpecialLinearGroup (Fin 3) (ZMod p))
    (htor : ThreeTenTorusExclusion p d) : D ≤ I := by
  have hhyp' : ThreeTenHyp I D P Y p d := hhyp
  obtain ⟨-, -, hd, -, -, hI, hD, -, -, -, -, -⟩ := hhyp'
  haveI hInormal : I.Normal := normal_of_oPPrimeHull_eq hI
  haveI hFact : Fact d.Prime := ⟨hd⟩
  let C : Subgroup H := Subgroup.centralizer (I : Set H)
  haveI hCnormal : C.Normal := Subgroup.normal_centralizer
  have hDle : D ≤ I ⊔ C := d_le_sup_centralizer_of_threeTenHyp hhyp e htor
  have hbot : D ⊓ C = ⊥ := centralizer_inf_eq_bot_of_threeTenHyp hhyp
  have hSyl : CFSG.ABGLocalTools.IsSylowOf d (D ⊓ C) C :=
    hD.inf_of_le_normalizer le_top Subgroup.le_normalizer_of_normal
  have hCdvd : ¬ d ∣ Nat.card ↥C := by
    have h := (CFSG.ABGLocalTools.isSylowOf_iff.mp hSyl).2.2
    rwa [hbot, Subgroup.relIndex_bot_left] at h
  have hrel_dvd_C : I.relIndex D ∣ Nat.card ↥C := by
    have h1 : I.relIndex D * (I ⊔ D).relIndex (I ⊔ C) = I.relIndex (I ⊔ C) := by
      rw [← Subgroup.relIndex_sup_left D I]
      exact Subgroup.relIndex_mul_relIndex I (I ⊔ D) (I ⊔ C) le_sup_left
        (sup_le le_sup_left hDle)
    have h2 : I.relIndex (I ⊔ C) = I.relIndex C := Subgroup.relIndex_sup_left C I
    have h3 : I.relIndex D ∣ I.relIndex C :=
      ⟨(I ⊔ D).relIndex (I ⊔ C), (h1.trans h2).symm⟩
    exact h3.trans (Subgroup.relIndex_dvd_card I C)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hD.isPGroup
  have hrel_dvd_D : I.relIndex D ∣ d ^ k := by
    rw [← hk]
    exact Subgroup.relIndex_dvd_card I D
  have hcop : Nat.Coprime (Nat.card ↥C) (d ^ k) := hd.coprime_pow_of_not_dvd hCdvd
  have hone : I.relIndex D = 1 := Nat.eq_one_of_dvd_coprimes hcop hrel_dvd_C hrel_dvd_D
  exact Subgroup.relIndex_eq_one.mp hone

end CFSG.LocalAnalysis.AGL81I.Section3
