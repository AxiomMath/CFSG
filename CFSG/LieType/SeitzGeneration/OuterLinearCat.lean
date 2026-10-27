module

public import CFSG.LieType.SeitzGeneration.OuterLinearMain
public import CFSG.LieType.SeitzGeneration.OuterLinearTwo
public import CFSG.LieType.SeitzGeneration.RankVacuity

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial

theorem planeGen_outer_A (hpair : SubfieldPairSLLt) {m : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A m q).Valid) (hm : 2 ≤ m) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ≠ q.p) (hlift : ¬ (p ∣ q.card - 1 ∧ p ∣ m + 1))
    {E : Subgroup (MulAut (Cat ⟨.A m q, hv⟩))} (hE : IsElemAbelian p E)
    (hc : Nat.card E = p ^ 2) (hout : ¬ InnerPlane ⟨.A m q, hv⟩ p E) (hs : NarrowScope p E) :
    PlaneGen E := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  let e : Cat ⟨.A m q, hv⟩ ≃* LinearFlag.projectiveSL (m + 1) (GaloisField q.p q.exponent) :=
    (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL m q hv).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL (m + 1) _)
  have hcardF : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  have hKq : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card _ _ q.exponent_pos.ne'
  have hcop : Nat.Coprime p (Nat.gcd (m + 1) (Nat.card (GaloisField q.p q.exponent) - 1)) := by
    refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hd => hlift ⟨?_, ?_⟩
    · rw [← hcardF]
      exact hd.trans (Nat.gcd_dvd_right _ _)
    · exact hd.trans (Nat.gcd_dvd_left _ _)
  exact planeGen_of_outer_model e (planeGen_projectiveSL_outer hpair q.prime_p q.exponent_pos hKq
    (by omega) hp hp2 hpq hcop (isElemAbelian_map_congr e hE) ((card_map_congr e E).trans hc)
    (not_le_range_conj_map_congr e hout) (hs.map_congr e))


theorem seitzOuter_linear (hpair : SubfieldPairSLLt) :
    SeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ NarrowScope p E ∧ IsLinearIndex d.1 ∧
      ¬ (p = 3 ∧ ∃ q, d.1 = .A 2 q ∧ 3 ∣ q.card - 1) := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, hs, ⟨m, q, hd⟩, hexc⟩
  subst hd
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hm1 : 1 ≤ m := hrange.1
  have hpq : p ≠ q.p := by simpa using hpd
  rcases (by omega : m = 1 ∨ 2 ≤ m) with rfl | hm
  · exact planeGen_outer_A1 hv hp hp2 hex hE hc hout
  · by_cases hlift : p ∣ q.card - 1 ∧ p ∣ m + 1
    · exfalso
      rcases (by omega : m = 2 ∨ 3 ≤ m) with rfl | hm3
      · have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hlift.2
        exact hexc ⟨hp3, q, rfl, hp3 ▸ hlift.1⟩
      · have hm4 : 4 ≤ m := by
          by_contra hlt
          have h3 : m = 3 := by omega
          subst h3
          exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
            (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 from hlift.2)))
        exact not_rankLE2_linear hv hp hlift.1 hm4 hs.1
    · exact planeGen_outer_A hpair hv hm hp hp2 hpq hlift hE hc hout hs

end CFSG.LieType.SeitzGeneration
