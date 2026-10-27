module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxHeGenB

public section

namespace CFSG.ComponentClassification.SolMax.HeGen

open CFSG.Sporadic.HeldB CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier.Native Subgroup

@[expose] def heGenSigmas : List (Equiv.Perm (Fin 240)) := heInnerSigma0.map (permOrId 240)

theorem rep_heGenSigma (h : ℕ) (hh : h < heGenSigmas.length) :
    Rep 240 sigArrs[h]! (heGenSigmas.getD h 1) ∧
      Rep 240 (sigArrs.map (invCand 240))[h]! (heGenSigmas.getD h 1)⁻¹ := by
  have hh' : h < heInnerSigma0.length := by simpa [heGenSigmas] using hh
  have hc := permChk_spec (heGenInner_parts.1 _ (List.getElem_mem hh'))
  have e1 : sigArrs[h]! = heInnerSigma0[h] := by
    rw [getElem!_pos sigArrs h (by simpa [sigArrs] using hh')]
    simp only [sigArrs, List.getElem_toArray]
  have e2 : (sigArrs.map (invCand 240))[h]! = invCand 240 heInnerSigma0[h] := by
    rw [getElem!_pos (sigArrs.map (invCand 240)) h (by simpa [sigArrs] using hh'),
      Array.getElem_map]
    simp only [sigArrs, List.getElem_toArray]
  have e3 : heGenSigmas.getD h 1 = permOrId 240 heInnerSigma0[h] := by
    rw [List.getD_eq_getElem _ _ hh]
    simp only [heGenSigmas, List.getElem_map]
  rw [e1, e2, e3]
  exact hc

@[expose] noncomputable def heGenSP (w : List ℤ) : Equiv.Perm (Fin 240) :=
  evalSignedWord heGenSigmas w

theorem rep_heGenSP {w : List ℤ} (hw : lettersOK 9 w = true) :
    Rep 240 (sWord w) (heGenSP w) :=
  rep_wordA_evalSignedWord (fun h hh => (rep_heGenSigma h hh).1)
    (fun h hh => (rep_heGenSigma h hh).2) hw

theorem heGenSP_mem (w : List ℤ) : heGenSP w ∈ heX0.originalSubgroup := by
  rw [heX0, certificate_originalSubgroup]
  exact evalSignedWord_mem _ (fun g hg => subset_closure hg) w

@[expose] noncomputable def heGenX5 : Equiv.Perm (Fin 240) := heGenSP wX5

@[expose] noncomputable def heGenKP (w : List ℤ) : Equiv.Perm (Fin 240) :=
  heGenSP w * heGenX5 * (heGenSP w)⁻¹

theorem heGenX5_pow : heGenX5 ^ 5 = 1 := by
  obtain ⟨-, h1, -, -, -, h5, -⟩ := heGenInner_parts
  have r : Rep 240 x5A heGenX5 := rep_heGenSP h1
  have := eq_of_eqA (rep_compA r (rep_compA r (rep_compA r (rep_compA r r)))) rep_idA h5
  rw [pow_succ', pow_succ', pow_succ', pow_succ', pow_one]
  exact this

theorem permOrId_kA {w : List ℤ} (hw : w ∈ wK) :
    permOrId 240 (kA w) = heGenKP w := by
  obtain ⟨-, h1, h2, -, h3, -⟩ := heGenInner_parts
  have rs : Rep 240 (sWord w) (heGenSP w) := rep_heGenSP (h2 w hw)
  have rx : Rep 240 x5A heGenX5 := rep_heGenSP h1
  have rk : Rep 240 (kA w) (heGenSP w * (heGenX5 * (heGenSP w)⁻¹)) :=
    rep_compA rs (rep_compA rx (rep_inv_of_permChk rs (h3 w hw).1))
  rw [heGenKP, mul_assoc]
  exact (permChk_spec (h3 w hw).2).1.unique rk

theorem card_heGenK : Nat.card heGenK.originalSubgroup = 40320 := by
  obtain ⟨-, -, -, -, -, -, -, hc, ho⟩ := heGenInner_parts
  rw [← heGenK.orderCertificate_eq_card hc, ho]

theorem false_of_normal_heX0
    {N : Subgroup (Equiv.Perm (Fin 240))} (hNX : N ≤ heX0.originalSubgroup)
    (hN : ∀ g ∈ heX0.originalSubgroup, ∀ n ∈ N, g * n * g⁻¹ ∈ N) (h5 : 5 ∣ Nat.card N)
    (hlt : Nat.card N < 40320) : False := by
  set X := heX0.originalSubgroup with hXdef
  have hX : Nat.card X = 80640 := card_heX0
  have hfive : ∀ y ∈ X, y ^ 5 = 1 → y ∈ N := by
    intro y hy hy5
    have hN' : (N.subgroupOf X).Normal := ⟨fun n hn g => by
      rw [mem_subgroupOf] at hn ⊢
      exact hN g g.2 n hn⟩
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf X)
    have hN'c : Nat.card (N.subgroupOf X) = Nat.card N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNX).toEquiv
    have hq : Nat.Coprime 5 (Nat.card (X ⧸ N.subgroupOf X)) := by
      rw [Nat.Prime.coprime_iff_not_dvd (by norm_num)]
      intro hq5
      have h25 : 5 * 5 ∣ 80640 := by
        rw [← hX, hcard, hN'c]
        exact Nat.mul_dvd_mul hq5 h5
      norm_num at h25
    have hy5' : (⟨y, hy⟩ : X) ^ 5 = 1 := Subtype.ext (by simpa using hy5)
    have h1 : ((⟨y, hy⟩ : X) : X ⧸ N.subgroupOf X) ^ 5 = 1 := by
      rw [← QuotientGroup.mk_pow, hy5', QuotientGroup.mk_one]
    have h2 : ((⟨y, hy⟩ : X) : X ⧸ N.subgroupOf X) ^ Nat.card (X ⧸ N.subgroupOf X) = 1 :=
      pow_card_eq_one'
    have h3 := pow_gcd_eq_one.2 ⟨h1, h2⟩
    rw [Nat.Coprime.gcd_eq_one hq, pow_one, QuotientGroup.eq_one_iff] at h3
    exact mem_subgroupOf.1 h3
  have hK : heGenK.originalSubgroup ≤ N := by
    rw [heGenK, certificate_originalSubgroup, closure_le]
    intro g hg
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hg
    rw [permOrId_kA hw]
    refine hfive _ (mul_mem (mul_mem (heGenSP_mem w) (heGenSP_mem wX5))
      (inv_mem (heGenSP_mem w))) ?_
    rw [heGenKP, conj_pow, heGenX5_pow, mul_one, mul_inv_cancel]
  have := Subgroup.card_le_of_le hK
  rw [card_heGenK] at this
  omega

end CFSG.ComponentClassification.SolMax.HeGen
