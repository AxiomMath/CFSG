module

public import CFSG.GH74.GLS.NT44.RigidFamily
import CFSG.GroupTheory.SylowNormalIndex
import CFSG.GroupTheory.PCore.CommonQuotientTransport
import CFSG.GroupTheory.PGroup.PrimePartTransport
import CFSG.GroupTheory.MulAutCongr
import CFSG.GH74.GLS.Stage1.Thm4.Alt51Q1
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.theorem_4_20_c
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Hat

public section

namespace CFSG.GH74.GLS.NT44

open Subgroup CFSG.ABGLocalTools.IsSylowOf CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm4
  CFSG.GH74.GLS.Stage1.Thm2
open scoped commutatorElement Pointwise

private lemma exists_hatMap_eq_of_mem_center {G : Type} [Group G] {X : Subgroup G}
    (h : zStar X ≤ X) (c : Subgroup.center (Recip.Hat X)) :
    ∃ z : ↥(zStar X), TwoThin.hatMap h z = (c : Recip.Hat X) := by
  obtain ⟨k, hk⟩ := Recip.hatMk_surjective X (c : Recip.Hat X)
  have hkcenter : Recip.hatMk X k ∈ Subgroup.center (Recip.Hat X) := by
    rw [hk]
    exact c.2
  have hkz : (k : G) ∈ zStar X :=
    (CFSG.GH74.GLS.Stage1.Thm4.Alt51.mem_zStar_iff_hat_mem_center (K := X) k).mpr hkcenter
  refine ⟨⟨(k : G), hkz⟩, ?_⟩
  have hsub : Subgroup.inclusion h ⟨(k : G), hkz⟩ = k := Subtype.ext rfl
  simp only [TwoThin.hatMap, MonoidHom.comp_apply, hsub]
  exact hk

theorem isSylowOf_zStar_kz_of_coverage {G : Type} [Group G] [Finite G]
    {fullQ : Type} [Group fullQ]
    {x t : G} {W : Subgroup G}
    (hW : CFSG.ABGLocalTools.IsSylowOf 2 W (zStar (Kz fullQ x)))
    (htW : t ∈ W)
    (hcovx : (Kz fullQ x ⊓ Kz fullQ t) ⊔ pPrimeCoreOf 2 (Kz fullQ x) = Kz fullQ x)
    (hcovt : (Kz fullQ x ⊓ Kz fullQ t) ⊔ pPrimeCoreOf 2 (Kz fullQ t) = Kz fullQ t) :
    CFSG.ABGLocalTools.IsSylowOf 2 W (zStar (Kz fullQ t)) := by
  classical
  let P : Subgroup G := Kz fullQ x
  let R : Subgroup G := Kz fullQ t
  let D : Subgroup G := P ⊓ R
  have hcovxP : D ⊔ pPrimeCoreOf 2 P = P := by simpa only [P, D] using hcovx
  have hcovtR : D ⊔ pPrimeCoreOf 2 R = R := by simpa only [D, R] using hcovt
  have hzPle : zStar P ≤ P := inf_le_left
  have hzRle : zStar R ≤ R := inf_le_left
  have hDP : D ≤ P := inf_le_left
  have hDR : D ≤ R := inf_le_right
  have hWP : W ≤ P := fun _ h => (hW.le h).1
  have hbot : W ⊓ pPrimeCoreOf 2 P = ⊥ :=
    CFSG.inf_eq_bot_of_pSubgroup_and_pPrime_card (p := 2) (H := W)
      (K := pPrimeCoreOf 2 P) hW.isPGroup
      (Nat.coprime_two_left.mpr (TwoThin.card_pPrimeCoreOf_odd P))
  have hWcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := by
    intro a ha b hb
    have hcabW : ⁅b, a⁆ ∈ W := by
      rw [commutatorElement_def]
      exact W.mul_mem (W.mul_mem (W.mul_mem hb ha) (W.inv_mem hb)) (W.inv_mem ha)
    have hcabO : ⁅b, a⁆ ∈ pPrimeCoreOf 2 P :=
      (hW.le ha).2.2.2 b (hWP hb)
    have hcab : ⁅b, a⁆ = 1 := by
      have hmem : ⁅b, a⁆ ∈ W ⊓ pPrimeCoreOf 2 P := ⟨hcabW, hcabO⟩
      rw [hbot] at hmem
      exact Subgroup.mem_bot.mp hmem
    exact ((commutatorElement_eq_one_iff_mul_comm (g₁ := b) (g₂ := a)).mp hcab).symm
  have hWcent : W ≤ centralizer ({t} : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact (hWcomm w hw t htW).symm
  have hWNR : W ≤ normalizer (R : Set G) :=
    hWcent.trans (centralizer_le_normalizer_kz (Q := fullQ) (z := t))
  have hWNP : W ≤ normalizer (P : Set G) := hWP.trans Subgroup.le_normalizer
  have hWND : W ≤ normalizer (D : Set G) := by
    intro w hw
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hWNP hw) y).mp hy.1,
        (Subgroup.mem_normalizer_iff.mp (hWNR hw) y).mp hy.2⟩
    · intro hy
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hWNP hw) y).mpr hy.1,
        (Subgroup.mem_normalizer_iff.mp (hWNR hw) y).mpr hy.2⟩
  let H : Subgroup G := P ⊓ normalizer (D : Set G)
  have hWH : W ≤ H := le_inf hWP hWND
  have hDH : D ≤ H := le_inf hDP Subgroup.le_normalizer
  have hHP : H ≤ P := inf_le_left
  have hHN : H ≤ normalizer (D : Set G) := inf_le_right
  have hsup : (D.subgroupOf P) ⊔ (pPrimeCore 2 ↥P) = ⊤ := by
    apply Subgroup.map_injective (f := P.subtype) P.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hDP, Subgroup.map_top,
      Subgroup.range_subtype]
    exact hcovxP
  have hrel : (D.subgroupOf P).relIndex (pPrimeCore 2 ↥P) = (D.subgroupOf P).relIndex ⊤ := by
    calc (D.subgroupOf P).relIndex (pPrimeCore 2 ↥P)
        = (D.subgroupOf P).relIndex ((pPrimeCore 2 ↥P) ⊔ (D.subgroupOf P)) :=
          (CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal (pPrimeCore 2 ↥P)
            (D.subgroupOf P)).symm
      _ = (D.subgroupOf P).relIndex ⊤ := by rw [sup_comm, hsup]
  have hrel_top : (D.subgroupOf P).relIndex ⊤ = D.relIndex P := by
    rw [← Subgroup.subgroupOf_self (H := P), Subgroup.relIndex_subgroupOf (le_refl P)]
  have hcopP : Nat.Coprime 2 (D.relIndex P) := by
    rw [← hrel_top, ← hrel]
    exact Nat.Coprime.coprime_dvd_right
      (Subgroup.relIndex_dvd_card (H := D.subgroupOf P) (K := pPrimeCore 2 ↥P))
      (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥P))
  have hnotdvdP : ¬ 2 ∣ D.relIndex P :=
    (Nat.prime_two.coprime_iff_not_dvd).mp hcopP
  have hcopH : Nat.Coprime 2 (D.relIndex H) :=
    Nat.Coprime.coprime_dvd_right
      ⟨H.relIndex P, (Subgroup.relIndex_mul_relIndex D H P hDH hHP).symm⟩ hcopP
  have hnotdvdH : ¬ 2 ∣ D.relIndex H :=
    (Nat.prime_two.coprime_iff_not_dvd).mp hcopH
  have hWD : W ≤ D :=
    CFSG.ABGLocalTools.le_of_isPGroup_of_not_dvd_relIndex (p := 2) (R := W) (M := H) (N := D)
      hW.isPGroup hWH hDH hHN hnotdvdH
  have hDO : D ≤ normalizer (pPrimeCoreOf 2 P : Set G) := by
    intro d hd
    exact TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer (hDP hd))
  have hcovxProd : ∀ k ∈ P, ∃ c ∈ D, ∃ o ∈ pPrimeCoreOf 2 P, k = c * o := by
    intro k hk
    have hk' : k ∈ (D ⊔ pPrimeCoreOf 2 P : Subgroup G) := by
      rw [hcovxP]
      exact hk
    have hset : ((D ⊔ pPrimeCoreOf 2 P : Subgroup G) : Set G) =
        (D : Set G) * (pPrimeCoreOf 2 P : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right D (pPrimeCoreOf 2 P) hDO
    change k ∈ ((D ⊔ pPrimeCoreOf 2 P : Subgroup G) : Set G) at hk'
    rw [hset, Set.mem_mul] at hk'
    obtain ⟨c, hc, o, ho, hco⟩ := hk'
    exact ⟨c, hc, o, ho, hco.symm⟩
  have hDOt : D ≤ normalizer (pPrimeCoreOf 2 R : Set G) := by
    intro d hd
    exact TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer (hDR hd))
  have hcovtProd : ∀ k ∈ R, ∃ c ∈ D, ∃ o ∈ pPrimeCoreOf 2 R, k = c * o := by
    intro k hk
    have hk' : k ∈ (D ⊔ pPrimeCoreOf 2 R : Subgroup G) := by
      rw [hcovtR]
      exact hk
    have hset : ((D ⊔ pPrimeCoreOf 2 R : Subgroup G) : Set G) =
        (D : Set G) * (pPrimeCoreOf 2 R : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right D (pPrimeCoreOf 2 R) hDOt
    change k ∈ ((D ⊔ pPrimeCoreOf 2 R : Subgroup G) : Set G) at hk'
    rw [hset, Set.mem_mul] at hk'
    obtain ⟨c, hc, o, ho, hco⟩ := hk'
    exact ⟨c, hc, o, ho, hco.symm⟩
  have hsurjP : Function.Surjective (TwoThin.hatMap hDP) :=
    TwoThin.hatMap_surjective hDP hcovxProd
  have hsurjR : Function.Surjective (TwoThin.hatMap hDR) :=
    TwoThin.hatMap_surjective hDR hcovtProd
  obtain ⟨-, -, e, he, -, -⟩ :=
    CFSG.common_pPrimeCore_quotient_transport (p := 2) (D := D) (B := P) (H := R)
      hDP hDR hsurjP hsurjR
  have hWzR : W ≤ zStar R := by
    intro w hw
    have hwD : w ∈ D := hWD hw
    have hwP : w ∈ P := hDP hwD
    have hwR : w ∈ R := hDR hwD
    have hcsecP : w ∈ Recip.cSec P := (hW.le hw).2
    have hphiP : Recip.phi P w (Subgroup.le_normalizer hwP) = 1 :=
      (Recip.phi_eq_one_iff P (Subgroup.le_normalizer hwP)).mpr hcsecP
    have hconjP : MulAut.conj (Recip.hatMk P ⟨w, hwP⟩) = 1 := by
      rw [← Recip.phi_of_mem P hwP]
      exact hphiP
    have hqR : Recip.hatMk R ⟨w, hwR⟩ = e (Recip.hatMk P ⟨w, hwP⟩) := by
      have h := he ⟨w, hwD⟩
      change e (TwoThin.hatMap hDP ⟨w, hwD⟩) = TwoThin.hatMap hDR ⟨w, hwD⟩ at h
      change TwoThin.hatMap hDR ⟨w, hwD⟩ = e (TwoThin.hatMap hDP ⟨w, hwD⟩)
      exact h.symm
    have hconjR : MulAut.conj (Recip.hatMk R ⟨w, hwR⟩) = 1 := by
      rw [hqR, ← CFSG.mulAut_congr_conj e (Recip.hatMk P ⟨w, hwP⟩), hconjP]
      ext y
      simp
    have hphiR : Recip.phi R w (Subgroup.le_normalizer hwR) = 1 := by
      rw [Recip.phi_of_mem R hwR]
      exact hconjR
    have hcsecR : w ∈ Recip.cSec R :=
      (Recip.phi_eq_one_iff R (Subgroup.le_normalizer hwR)).mp hphiR
    exact ⟨hwR, hcsecR⟩
  have hcenterP : ∀ z : ↥(zStar P), TwoThin.hatMap hzPle z ∈ Subgroup.center (Recip.Hat P) := by
    intro z
    exact (CFSG.GH74.GLS.Stage1.Thm4.Alt51.mem_zStar_iff_hat_mem_center
      (K := P) ⟨(z : G), z.2.1⟩).mp z.2
  let fPz : ↥(zStar P) →* Subgroup.center (Recip.Hat P) :=
    (TwoThin.hatMap hzPle).codRestrict (Subgroup.center (Recip.Hat P)) hcenterP
  have hsurjPz : Function.Surjective fPz := by
    intro c
    obtain ⟨z, hz⟩ := exists_hatMap_eq_of_mem_center hzPle c
    refine ⟨z, Subtype.ext ?_⟩
    have hz' : (fPz z : Recip.Hat P) = (c : Recip.Hat P) := by
      dsimp only [fPz]
      rw [MonoidHom.codRestrict_apply]
      exact hz
    exact hz'
  have hkerPz : ¬ 2 ∣ Nat.card fPz.ker := by
    have hker : fPz.ker = (TwoThin.hatMap hzPle).ker := by
      dsimp only [fPz]
      rw [MonoidHom.ker_codRestrict]
    rw [hker]
    exact (Nat.prime_two.coprime_iff_not_dvd).mp
      (Nat.coprime_two_left.mpr (TwoThin.odd_card_ker_hatMap hzPle))
  have hfacP : (Nat.card (Subgroup.center (Recip.Hat P))).factorization 2 =
      (Nat.card ↥(zStar P)).factorization 2 :=
    CFSG.GroupTheory.factorization_eq_of_surjective_ker_not_dvd (p := 2) fPz hsurjPz hkerPz
  have hcenterR : ∀ z : ↥(zStar R), TwoThin.hatMap hzRle z ∈ Subgroup.center (Recip.Hat R) := by
    intro z
    exact (CFSG.GH74.GLS.Stage1.Thm4.Alt51.mem_zStar_iff_hat_mem_center
      (K := R) ⟨(z : G), z.2.1⟩).mp z.2
  let fRz : ↥(zStar R) →* Subgroup.center (Recip.Hat R) :=
    (TwoThin.hatMap hzRle).codRestrict (Subgroup.center (Recip.Hat R)) hcenterR
  have hsurjRz : Function.Surjective fRz := by
    intro c
    obtain ⟨z, hz⟩ := exists_hatMap_eq_of_mem_center hzRle c
    refine ⟨z, Subtype.ext ?_⟩
    have hz' : (fRz z : Recip.Hat R) = (c : Recip.Hat R) := by
      dsimp only [fRz]
      rw [MonoidHom.codRestrict_apply]
      exact hz
    exact hz'
  have hkerRz : ¬ 2 ∣ Nat.card fRz.ker := by
    have hker : fRz.ker = (TwoThin.hatMap hzRle).ker := by
      dsimp only [fRz]
      rw [MonoidHom.ker_codRestrict]
    rw [hker]
    exact (Nat.prime_two.coprime_iff_not_dvd).mp
      (Nat.coprime_two_left.mpr (TwoThin.odd_card_ker_hatMap hzRle))
  have hfacR : (Nat.card (Subgroup.center (Recip.Hat R))).factorization 2 =
      (Nat.card ↥(zStar R)).factorization 2 :=
    CFSG.GroupTheory.factorization_eq_of_surjective_ker_not_dvd (p := 2) fRz hsurjRz hkerRz
  have hcenterCard : Nat.card (Subgroup.center (Recip.Hat P)) =
      Nat.card (Subgroup.center (Recip.Hat R)) :=
    Nat.card_congr (Subgroup.centerCongr e).toEquiv
  have hsrc : Nat.card W = 2 ^ (Nat.card ↥(zStar P)).factorization 2 := by
    simpa only [P] using hW.card_eq
  have htgt : Nat.card W = 2 ^ (Nat.card ↥(zStar R)).factorization 2 := by
    rw [hsrc]
    congr 1
    rw [← hfacP, ← hfacR, hcenterCard]
  exact CFSG.ABGLocalTools.isSylowOf_of_card (p := 2) hWzR htgt

end CFSG.GH74.GLS.NT44

end
