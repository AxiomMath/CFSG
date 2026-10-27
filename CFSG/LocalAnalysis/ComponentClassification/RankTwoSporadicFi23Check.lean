module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi23
public import Certificates.Certificate15011
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo2Pair
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo2Roots
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicGenCensus

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Fi23

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic
  CFSG.ComponentClassification.RankTwoSporadic.Cert
  CFSG.ComponentClassification.RankTwoSporadic.RootCensus

theorem fi23_facts : Fi23CensusFacts :=
  Certificates.certificate15011

theorem fi23_yCensus17_of_facts
    (h : Fi23CensusFacts) :
    YCensus17 (fi23P.subgroupOf fi23P) (fun _ => False) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold Fi23CensusFacts Fi23CensusFactsOn at h
  rw [← fi23P_eq_closure_permsA] at h
  obtain ⟨x, T, hTP, hcard, hx, hw⟩ := h
  let xW : ℕ → ↥fi23P := fun i => if hi : i < 3 then ⟨x i, (hx i hi).1⟩ else 1
  have hxW : ∀ i, i < 3 → ((xW i : ↥fi23P) : Equiv.Perm (Fin 31671)) = x i := fun i hi => by
    simp only [xW, hi, dite_true]
  have hN : (fi23P.subgroupOf fi23P).Normal := by
    rw [subgroupOf_self]
    infer_instance
  have hidx : (fi23P.subgroupOf fi23P).index ≤ 2 := by
    rw [subgroupOf_self, index_top]
    norm_num
  have hconj : ∀ g : ↥fi23P, (g : Equiv.Perm (Fin 31671)) ^ 2 = 1 →
      (g : Equiv.Perm (Fin 31671)) ≠ 1 → ∀ j < 3, fixP (g : Equiv.Perm (Fin 31671)) = fixP (x j) →
      IsConj g (xW j) := by
    intro g hg2 hg1 j hj hgj
    obtain ⟨-, hx2, hx1, -, -⟩ := hx j hj
    obtain ⟨w, hw, hwg⟩ := fi23_conj_of_fix g.2 hg2 hg1 (hx j hj).1 hx2 hx1 hgj
    refine isConj_iff.mpr ⟨⟨w, hw⟩, Subtype.ext ?_⟩
    simp only [coe_mul, coe_inv, hxW j hj]
    exact hwg
  refine yCensus17_of_roots (k := 3) hN hidx xW (fun _ => T.subgroupOf fi23P) (fun i hi => ?_)
    (fun a _ ha2 ha1 => ?_) (fun i hi b hb hb2 hb1 hbx => ?_)
  ·
    obtain ⟨-, -, -, -, hTC⟩ := hx i hi
    refine CFSG.ABGLocalTools.isSylowOf_of_card ?_ ?_
    · intro b hb
      rw [mem_subgroupOf] at hb
      rw [mem_centralizer_singleton_iff]
      apply Subtype.ext
      simp only [coe_mul, hxW i hi]
      exact (mem_centralizer_singleton_iff.mp (hTC hb))
    · rw [Nat.card_congr (subgroupOfEquivOfLe hTP).toEquiv, hcard,
        CFSG.ComponentClassification.RankTwoSporadic.card_centralizer_subtype, hxW i hi]
      congr 1
      refine (factorization_two_eq (m := 15600091832325) ?_ ?_ (by decide)).symm
      · rw [← hcard]
        exact Subgroup.card_dvd_of_le (le_inf hTP hTC)
      · rw [show (2 : ℕ) ^ 18 * 15600091832325 = 4089470473293004800 by norm_num, ← card_fi23P]
        exact Subgroup.card_dvd_of_le inf_le_left
  ·
    have ha2' : (a : Equiv.Perm (Fin 31671)) ^ 2 = 1 := by rw [← coe_pow, ha2, coe_one]
    have ha1' : (a : Equiv.Perm (Fin 31671)) ≠ 1 := fun h1 => ha1 (Subtype.ext h1)
    have h0 : fixP (x 0) = 3511 := (hx 0 (by norm_num)).2.2.2.1
    have h1 : fixP (x 1) = 695 := (hx 1 (by norm_num)).2.2.2.1
    have h2 : fixP (x 2) = 183 := (hx 2 (by norm_num)).2.2.2.1
    rcases fi23_fixP_cases a.2 ha2' ha1' with h | h | h
    · exact ⟨0, by norm_num, hconj a ha2' ha1' 0 (by norm_num) (h.trans h0.symm)⟩
    · exact ⟨1, by norm_num, hconj a ha2' ha1' 1 (by norm_num) (h.trans h1.symm)⟩
    · exact ⟨2, by norm_num, hconj a ha2' ha1' 2 (by norm_num) (h.trans h2.symm)⟩
  ·
    obtain ⟨-, hx2, -, -, hTC⟩ := hx i hi
    have hbT : (b : Equiv.Perm (Fin 31671)) ∈ T := by rwa [mem_subgroupOf] at hb
    have hb2' : (b : Equiv.Perm (Fin 31671)) ^ 2 = 1 := by rw [← coe_pow, hb2, coe_one]
    have hb1' : (b : Equiv.Perm (Fin 31671)) ≠ 1 := fun h1 => hb1 (Subtype.ext h1)
    have hbx' : (b : Equiv.Perm (Fin 31671)) ≠ x i := by
      rw [← hxW i hi]
      exact fun h1 => hbx (Subtype.ext h1)
    rcases hw i hi b hbT hb2' hb1' hbx' with hM | ⟨j, hji, hj | hj⟩
    · left
      have hXmap : (fi23P.subgroupOf fi23P).map fi23P.subtype = fi23P := by
        rw [subgroupOf_map_subtype, inf_idem]
      have hEmap : (closure ({xW i, b} : Set ↥fi23P)).map fi23P.subtype =
          closure {x i, (b : Equiv.Perm (Fin 31671))} := by
        rw [MonoidHom.map_closure, Set.image_pair]
        simp only [coe_subtype, hxW i hi]
      rw [← monoW_map_iff fi23P.subtype fi23P.subtype_injective, hXmap, hEmap]
      exact hM
    · exact Or.inr ⟨j, hji, Or.inl (hconj b hb2' hb1' j (by omega) hj)⟩
    · have hcomm : x i * b = b * x i := (mem_centralizer_singleton_iff.mp (hTC hbT)).symm
      have hxb2 : ((xW i * b : ↥fi23P) : Equiv.Perm (Fin 31671)) ^ 2 = 1 := by
        rw [coe_mul, hxW i hi, sq, show x i * b * (x i * b) = x i * x i * (b * b) by
          rw [mul_assoc, ← mul_assoc (b : Equiv.Perm (Fin 31671)), ← hcomm]; group]
        rw [← sq, hx2, ← sq, hb2', one_mul]
      have hxb1 : ((xW i * b : ↥fi23P) : Equiv.Perm (Fin 31671)) ≠ 1 := by
        rw [coe_mul, hxW i hi]
        intro h1
        apply hbx'
        have hxinv : (x i)⁻¹ = x i := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hx2)
        rw [← hxinv]
        exact eq_inv_of_mul_eq_one_right h1
      have e : ((xW i * b : ↥fi23P) : Equiv.Perm (Fin 31671)) = x i * b := by
        rw [coe_mul, hxW i hi]
      refine Or.inr ⟨j, hji, Or.inr (hconj _ hxb2 hxb1 j (by omega) ?_)⟩
      rw [e]
      exact hj

theorem sporadicCaseOdd_Fi23
    (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three) :
    SporadicCaseOdd .Fi23 := by
  have hX : fi23P.subgroupOf fi23P = ⊤ := subgroupOf_self _
  refine sporadicCaseOdd_of_yCensus17 h32 h33 fi23AutModel (by rw [hX]; exact le_top) ?_
    (fi23_yCensus17_of_facts fi23_facts)
  rw [hX]
  exact yCensus_top_le_top

end CFSG.ComponentClassification.RankTwoSporadic.Fi23
