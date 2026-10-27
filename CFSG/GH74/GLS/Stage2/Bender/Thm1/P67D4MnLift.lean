module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnTorus
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnFrame
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MonoIdx

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley

theorem d4Minus_mapsRootLines_pow {τ : Tag} {R : Type} [CommRing R]
    {g : (Module.End R (RootModule τ R))ˣ} {w : WeylGroup τ} (hg : MapsRootLines g w) (k : ℕ) :
    MapsRootLines (g ^ k) (w ^ k) := by
  induction k with
  | zero => simpa using mapsRootLines_one
  | succ k ih => simpa only [pow_succ] using ih.mul hg

theorem d4Minus_oppositionWeyl_comm (u : WeylGroup TwistTag.D4.tag) :
    trialityOppositionWeyl * u = u * trialityOppositionWeyl := by
  refine ext_single fun i => ?_
  rw [mul_smul, mul_smul, trialityOppositionWeyl_smul, trialityOppositionWeyl_smul, smul_neg]

theorem d4Minus_comm_mem_torus {L : Type} [Field L] {x : ModGL TwistTag.D4.tag L}
    {w : WeylGroup TwistTag.D4.tag} (hx : x ∈ monomialSubgroup TwistTag.D4.tag L)
    (hxw : MapsRootLines x w) :
    x⁻¹ * trialityOpposition L * x * (trialityOpposition L)⁻¹ ∈ torusGroup TwistTag.D4.tag L := by
  have hz := trialityOpposition_mem_monomialSubgroup (K := L)
  refine mem_torusGroup_of_mapsRootLines_one
    (mul_mem (mul_mem (mul_mem (inv_mem hx) hz) hx) (inv_mem hz)) ?_
  have h := (((hxw.inv).mul (mapsRootLines_trialityOpposition (K := L))).mul hxw).mul
    (mapsRootLines_trialityOpposition (K := L)).inv
  have hc : w⁻¹ * trialityOppositionWeyl * w * trialityOppositionWeyl⁻¹ = 1 := by
    calc w⁻¹ * trialityOppositionWeyl * w * trialityOppositionWeyl⁻¹
        = w⁻¹ * (trialityOppositionWeyl * w) * trialityOppositionWeyl⁻¹ := by group
      _ = w⁻¹ * (w * trialityOppositionWeyl) * trialityOppositionWeyl⁻¹ := by
          rw [d4Minus_oppositionWeyl_comm]
      _ = 1 := by group
  rwa [hc] at h

theorem exists_d4Minus_lift {L : Type} [Field L] [IsAlgClosed L] (Fr : L →+* L) {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) :
    ∃ m : ModGL TwistTag.D4.tag L, m ∈ monomialSubgroup TwistTag.D4.tag L ∧
      diagramMap TwistTag.D4 L * m = m * diagramMap TwistTag.D4 L ∧
      trialityOpposition L * twistHom TwistTag.D4 L Fr m * (trialityOpposition L)⁻¹ = m ∧
      m ∉ torusGroup TwistTag.D4.tag L ∧ m ^ 3 ∈ torusGroup TwistTag.D4.tag L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card (relWeylTwist TwistTag.D4) = 12 := card_relWeylTwist_D4
  have : Finite (relWeylTwist TwistTag.D4) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3
    (by rw [hcard]; norm_num : 3 ∣ Nat.card (relWeylTwist TwistTag.D4))
  have hw : (x : WeylGroup TwistTag.D4.tag) ∈ relWeylTwist TwistTag.D4 := x.2
  have hw3 : orderOf (x : WeylGroup TwistTag.D4.tag) = 3 := by
    rw [Subgroup.orderOf_coe, hx]
  set w : WeylGroup TwistTag.D4.tag := (x : WeylGroup TwistTag.D4.tag) with hwdef
  set n := canonicalRep (coxeterSystem TwistTag.D4.tag) L w with hndef
  set z := trialityOpposition L with hzdef
  set P := diagramMap TwistTag.D4 L with hPdef
  have hnM : n ∈ monomialSubgroup TwistTag.D4.tag L := canonicalRep_mem_monomialSubgroup L w
  have hnW : MapsRootLines n w := mapsRootLines_canonicalRep w
  have hPn : P * n = n * P := diagramMap_comm_canonicalRep hw
  have hnF : twistHom TwistTag.D4 L Fr n = n :=
    ((mem_twistedFixedGroup_iff_twistHom _ _ _).1
      (canonicalRep_mem_twistedFixedGroup TwistTag.D4 L Fr ((mem_relWeylTwist _).1 hw))).2
  have heT : n⁻¹ * z * n * z⁻¹ ∈ torusGroup TwistTag.D4.tag L :=
    d4Minus_comm_mem_torus (L := L) hnM hnW
  have hPe : P * (n⁻¹ * z * n * z⁻¹) = (n⁻¹ * z * n * z⁻¹) * P := by
    have hPn' : Commute P n := hPn
    have hPz' : Commute P z := diagramMap_comm_trialityOpposition
    exact (((hPn'.inv_right.mul_right hPz').mul_right hPn').mul_right hPz'.inv_right)
  obtain ⟨h, hhT, hPh, hLangEq⟩ := d4Minus_torus_lang Fr hFr heT hPe
  have hhM : h ∈ monomialSubgroup TwistTag.D4.tag L := torusGroup_le_monomialSubgroup hhT
  have hmW : MapsRootLines (n * h) w := by
    simpa using hnW.mul (mapsRootLines_of_mem_torusGroup hhT)
  refine ⟨n * h, mul_mem hnM hhM, ?_, ?_, ?_, ?_⟩
  · rw [← mul_assoc, hPn, mul_assoc, hPh, mul_assoc]
  · rw [map_mul, hnF]
    set k := z * twistHom TwistTag.D4 L Fr h * z⁻¹ with hk
    have hk' : k = (n⁻¹ * z * n * z⁻¹)⁻¹ * h := by
      have h1 : k⁻¹ = h⁻¹ * (n⁻¹ * z * n * z⁻¹) := by
        rw [← hLangEq]
        group
      rw [← inv_inv k, h1, mul_inv_rev, inv_inv]
    calc z * (n * twistHom TwistTag.D4 L Fr h) * z⁻¹ = (z * n * z⁻¹) * k := by
          rw [hk]
          group
      _ = (z * n * z⁻¹) * ((n⁻¹ * z * n * z⁻¹)⁻¹ * h) := by rw [hk']
      _ = n * h := by group
  · intro hmT
    have h1 : w = 1 := hmW.unique (mapsRootLines_of_mem_torusGroup hmT)
    rw [h1, orderOf_one] at hw3
    omega
  · have hm3 := d4Minus_mapsRootLines_pow hmW 3
    have hw1 : w ^ 3 = 1 := by simpa [hw3] using pow_orderOf_eq_one w
    rw [hw1] at hm3
    exact mem_torusGroup_of_mapsRootLines_one (pow_mem (mul_mem hnM hhM) 3) hm3

end CFSG.GH74.GLS.Stage2.Bender.Thm1
