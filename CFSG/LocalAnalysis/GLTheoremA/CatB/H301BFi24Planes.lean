module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Fi24
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi24TwoB
public import Certificates.Certificate15027
public import Certificates.Certificate101705
import CFSG.RankThree.Native.ChainCentralizer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.FischerOddCore (fi24K card_fi24K)
open CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime
open CFSG.LocalAnalysis.GLTheoremA.H1017 (k_hside k_A_mem k_G_mem)
open CFSG.LocalAnalysis.GLTheoremA.H1017.Fi24RankNative (kRA iotas)
open CFSG.LocalAnalysis.GLTheoremA.H1017.Fi24Side (iotaP side_conj iotaP_mem iotaP_injective
  rep_iotas card_fix_eq)
open CFSG.LocalAnalysis.GLTheoremA.H1017.Fi22TwistNative (commAtN)
open CFSG.LocalAnalysis.GLTheoremA.H301B.Fi24PlanesNative
open CFSG.RankThree.Native (rep_of_validA)

open CFSG.RankThree.Native in
private theorem commA_eq_commAtN (n : ℕ) (p x : Array ℕ) : commA n p x = commAtN n p x := by
  rw [commA, eqA, commAtN, Bool.eq_iff_iff, allLt_iff, allLt_iff]
  refine forall_congr' fun i => imp_congr_right fun hi => ?_
  rw [compA_get hi, compA_get hi]

open CFSG.RankThree.Native in
private theorem commAtN_iff {n : ℕ} {p x : Array ℕ} {P X : Equiv.Perm (Fin n)} (hp : Rep n p P)
    (hx : Rep n x X) : commAtN n p x = true ↔ P * X = X * P := by
  rw [← commA_eq_commAtN]
  exact commA_iff hp hx

local notation "ιA" => iotaP 504 (kRA ())
local notation "patN" => fi24PlRows fi24NCert.pts (iotas 504 (kRA ()))

private theorem card_pat (r : Array Bool) :
    (Finset.univ.filter fun i : Fin 243 => r[i.val]! = true).card = fi24PlCnt r := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact card_fix_eq _ (fun i : Fin 243 => r[i.val]!) fun _ => Iff.rfl

private theorem fi24PlRows_get {P I : Array (Array ℕ)} {s : ℕ} (hs : s < P.size) :
    (fi24PlRows P I)[s]! = fi24PlRow I P[s]! := by
  rw [fi24PlRows, getElem!_pos (P.map (fi24PlRow I)) s (by simpa using hs), Array.getElem_map,
    getElem!_pos P s hs]

private theorem fi24PlRow_get {I : Array (Array ℕ)} {p : Array ℕ} {i : ℕ} (hi : i < I.size) :
    (fi24PlRow I p)[i]! = commAtN 504 p I[i]! := by
  rw [fi24PlRow, getElem!_pos (I.map (commAtN 504 p)) i (by simpa using hi), Array.getElem_map,
    getElem!_pos I i hi]

section Patterns


private theorem exists_conj_iota {E : Subgroup (Equiv.Perm (Fin 504))} (hEK : E ≤ fi24K)
    (hE : IsElemAbelian 3 E) (hc : Nat.card E = 243) :
    ∃ g ∈ fi24K, ∀ y, y ∈ E ↔ ∃ i < 243, g⁻¹ * y * g = ιA i := by
  haveI : Finite fi24K := Nat.finite_of_card_ne_zero (by rw [card_fi24K]; norm_num)
  have hc' : Nat.card (E.subgroupOf fi24K) = 3 ^ 5 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv, hc]
    norm_num
  obtain ⟨g, hg⟩ := (side_conj (m := 2) fi24K k_hside (fun k hk => k_A_mem hk)
    (fun l hl => k_G_mem hl) (by norm_num) (by rw [card_fi24K]; norm_num) (Or.inl (by norm_num))
    (E.subgroupOf fi24K) (hE.subgroupOf fi24K)).2 hc'
  refine ⟨g, g.2, fun y => ⟨fun hy => ?_, fun ⟨i, hi, hy⟩ => ?_⟩⟩
  · obtain ⟨i, hi, h⟩ := (hg ⟨y, hEK hy⟩).1 (Subgroup.mem_subgroupOf.2 hy)
    exact ⟨i, hi, by simpa using h⟩
  · have hy' : y = g * ιA i * (g : Equiv.Perm (Fin 504))⁻¹ := by
      rw [← hy]
      group
    have hyK : y ∈ fi24K := hy' ▸ fi24K.mul_mem (fi24K.mul_mem g.2
      (iotaP_mem fi24K (fun k hk => k_A_mem hk) i)) (fi24K.inv_mem g.2)
    exact Subgroup.mem_subgroupOf.1 ((hg ⟨y, hyK⟩).2 ⟨i, hi, by simpa using hy⟩)

private theorem pat_iff (hN : fi24NOK = true) {s i : ℕ} (hs : s < 4096) (hi : i < 243) :
    (patN[s]!)[i]! = true ↔
      permOfArr 504 fi24NCert.pts[s]! * ιA i = ιA i * permOfArr 504 fi24NCert.pts[s]! := by
  have hs' : s < fi24NCert.pts.size := by rw [(fi24NOK_facts hN).2.1]; exact hs
  have hI : i < (iotas 504 (kRA ())).size := by rw [iotas, Array.size_ofFn]; exact hi
  rw [fi24PlRows_get hs', fi24PlRow_get hI]
  exact commAtN_iff (rep_of_validA ((fi24N_spec hN).2.2 s hs')) (rep_iotas k_hside hi)

end Patterns

section Bound


private theorem card_le_four {E H C : Subgroup (Equiv.Perm (Fin 504))} (hEK : E ≤ fi24K)
    (hE : IsElemAbelian 3 E) (hc : Nat.card E = 243) (hHE : H ≤ E)
    (hH : Nat.card H * 3 = Nat.card E) (hCN : C ≤ fi24N)
    (hCH : C ≤ Subgroup.centralizer (H : Set (Equiv.Perm (Fin 504)))) : Nat.card C ≤ 4 := by
  classical
  have hK := Certificates.certificate15027
  have hN := (fi24TwoBKCheck_parts hK).2.1
  have hsz := (fi24NOK_facts hN).2.1
  obtain ⟨g, hgK, hg⟩ := exists_conj_iota hEK hE hc
  have hcert : ∀ t < 4096, eqA 504 fi24NCert.pts[t]! (idA 504) = true ∨
      fi24PlCnt patN[t]! < 81 ∨
      (fi24PlCnt patN[t]! = 81 ∧ fi24PlSame fi24NCert.pts patN (idA 504) patN[t]! ≤ 4) :=
    fun t ht => by
      have h : fi24PlCheck fi24NCert.pts patN (idA 504) = true :=
        Certificates.certificate101705
      rw [fi24PlCheck] at h
      simpa only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
        or_assoc] using allLt_spec h ht
  have hH81 : Nat.card H = 81 := by omega
  set S := Finset.univ.filter fun i : Fin 243 => g * ιA i * g⁻¹ ∈ H with hS
  have hSmem : ∀ i, i ∈ S ↔ g * ιA i * g⁻¹ ∈ H := fun i => by
    rw [hS, Finset.mem_filter]
    exact and_iff_right (Finset.mem_univ i)
  have hScard : S.card = 81 := by
    rw [← Nat.card_eq_finsetCard, ← hH81]
    refine Nat.card_congr (Equiv.ofBijective (fun i => ⟨g * ιA i.1 * g⁻¹, (hSmem _).1 i.2⟩)
      ⟨fun i j hij => ?_, fun h => ?_⟩)
    · have e : ιA i.1 = ιA j.1 := by simpa using congrArg Subtype.val hij
      exact Subtype.ext (Fin.ext (iotaP_injective k_hside i.1.2 j.1.2 e))
    · obtain ⟨i, hi, hgi⟩ := (hg h).1 (hHE h.2)
      have e : g * ιA i * g⁻¹ = h := by
        rw [← hgi]
        group
      exact ⟨⟨⟨i, hi⟩, (hSmem _).2 (e ▸ h.2)⟩, Subtype.ext e⟩
  have hidx : ∀ x : C, ∃ s : Fin 4096, permOfArr 504 fi24NCert.pts[s.val]! = g⁻¹ * x * g :=
    fun x => by
      have hx := fi24N_normal_K hK g⁻¹ (fi24K.inv_mem hgK) x (hCN x.2)
      rw [inv_inv] at hx
      obtain ⟨s, hs, e⟩ := ((fi24N_spec hN).1 _).1 hx
      exact ⟨⟨s, lt_of_lt_of_eq hs hsz⟩, e⟩
  choose f hf using hidx
  have hfinj : Function.Injective f := fun x y hxy => by
    have e : g⁻¹ * (x : Equiv.Perm (Fin 504)) * g = g⁻¹ * y * g := by
      rw [← hf x, ← hf y, hxy]
    exact Subtype.ext (by simpa using e)
  have hrep : ∀ x : C, Rep 504 fi24NCert.pts[(f x).val]! (g⁻¹ * x * g) := fun x => by
    rw [← hf x]
    exact rep_of_validA ((fi24N_spec hN).2.2 _ (lt_of_lt_of_eq (f x).2 hsz.symm))
  have hpat : ∀ x : C, (x : Equiv.Perm (Fin 504)) ≠ 1 →
      (∀ i : Fin 243, (patN[(f x).val]!)[i.val]! = true ↔ i ∈ S) ∧
        fi24PlSame fi24NCert.pts patN (idA 504) patN[(f x).val]! ≤ 4 := fun x hx1 => by
    have hsub : S ⊆ Finset.univ.filter fun i : Fin 243 => (patN[(f x).val]!)[i.val]! = true :=
      fun i hi => by
        have hcomm := Subgroup.mem_centralizer_iff.1 (hCH x.2) _ ((hSmem i).1 hi)
        refine Finset.mem_filter.2 ⟨Finset.mem_univ _, (pat_iff hN (f x).2 i.2).2 ?_⟩
        rw [hf x]
        calc g⁻¹ * x * g * ιA i = g⁻¹ * (x * (g * ιA i * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * ιA i * g⁻¹) * x) * g := by rw [← hcomm]
          _ = ιA i * (g⁻¹ * x * g) := by group
    have hne : eqA 504 fi24NCert.pts[(f x).val]! (idA 504) ≠ true := fun h => by
      have e := (eqA_iff (hrep x) rep_idA).1 h
      exact hx1 (by
        calc (x : Equiv.Perm (Fin 504)) = g * (g⁻¹ * x * g) * g⁻¹ := by group
          _ = 1 := by rw [e]; group)
    have hcnt := card_pat patN[(f x).val]!
    have hle := Finset.card_le_card hsub
    rcases (hcert _ (f x).2).resolve_left hne with hlt | ⟨h81, h4⟩
    · omega
    · have heq := Finset.eq_of_subset_of_card_le hsub (by omega)
      refine ⟨fun i => ?_, h4⟩
      rw [heq, Finset.mem_filter]
      exact (and_iff_right (Finset.mem_univ i)).symm
  by_cases hC1 : C = ⊥
  · rw [hC1, Subgroup.card_bot]
    norm_num
  obtain ⟨x₀, hx₀⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hC1
  have hx₀' : (x₀ : Equiv.Perm (Fin 504)) ≠ 1 := fun h => hx₀ (Subtype.ext h)
  have hmem : ∀ x : C, (eqA 504 fi24NCert.pts[(f x).val]! (idA 504) ||
      allLt 243 fun i => (patN[(f x).val]!)[i]! == (patN[(f x₀).val]!)[i]!) = true := fun x => by
    by_cases hx1 : (x : Equiv.Perm (Fin 504)) = 1
    · refine Bool.or_eq_true_iff.2 (Or.inl ((eqA_iff (hrep x) rep_idA).2 ?_))
      rw [hx1]
      group
    · refine Bool.or_eq_true_iff.2 (Or.inr (allLt_iff.2 fun i hi => beq_iff_eq.2 ?_))
      exact Bool.eq_iff_iff.2 (((hpat x hx1).1 ⟨i, hi⟩).trans ((hpat x₀ hx₀').1 ⟨i, hi⟩).symm)
  calc Nat.card C ≤ Nat.card {s : Fin 4096 // (eqA 504 fi24NCert.pts[s.val]! (idA 504) ||
        allLt 243 fun i => (patN[s.val]!)[i]! == (patN[(f x₀).val]!)[i]!) = true} :=
        Nat.card_le_card_of_injective (fun x => ⟨f x, hmem x⟩) fun x y h =>
          hfinj (congrArg Subtype.val h)
    _ = fi24PlSame fi24NCert.pts patN (idA 504) patN[(f x₀).val]! :=
        card_fix_eq _ _ fun _ => Iff.rfl
    _ ≤ 4 := (hpat x₀ hx₀').2

theorem card_fi24N_inf_centralizer_le {E H : Subgroup (Equiv.Perm (Fin 504))} (hEK : E ≤ fi24K)
    (hE : IsElemAbelian 3 E) (hc : Nat.card E = 243) (hHE : H ≤ E)
    (hH : Nat.card H * 3 = Nat.card E) :
    Nat.card ↥(fi24N ⊓ Subgroup.centralizer (H : Set (Equiv.Perm (Fin 504)))) ≤ 4 :=
  card_le_four hEK hE hc hHE hH inf_le_left inf_le_right

end Bound

end CFSG.LocalAnalysis.GLTheoremA.H301B

end
