module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCheck

public section

namespace CFSG.ComponentClassification.RankTwoL3Four.HypII

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic CFSG.ABGLocalTools
open CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

variable {n : ℕ} {P R : Subgroup (Equiv.Perm (Fin n))} {testP : Array ℕ → Bool} {ps : List ℕ}
  {fuel : ℕ} {sGens : Array (Array ℕ)} {roots : Array ℕ} {nodes : Array Node}
  {regs : Array (Array ℕ)} {k m : ℕ}

theorem yCensusII_of_check_regs (hPR : P ≤ R) (hN : (P.subgroupOf R).Normal)
    (hps : ∀ p ∈ ps, p < n) (htest : ∀ a g, Rep n a g → (testP a = true ↔ g ∈ P))
    (hregs : ∀ r < regs.size, ∃ g ∈ R, Rep n regs[r]! g)
    (hc : censusOK n ps fuel testP testP false true false sGens roots nodes = true)
    (hgen : (allLt sGens.size fun j =>
      (List.range regs.size).any fun r => eqA n sGens[j]! regs[r]!) = true)
    (hsize : (enumBfs n sGens ps fuel).pts.size = 2 ^ k)
    (hcard : Nat.card R = 2 ^ k * m) (hm : Odd m) :
    YCensus (P.subgroupOf R) (· ≤ P.subgroupOf R) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmap : (P.subgroupOf R).map R.subtype = P := by
    rw [subgroupOf_map_subtype, inf_eq_left.mpr hPR]
  have hc' := hc
  simp only [censusOK, Bool.and_eq_true] at hc'
  obtain ⟨⟨hS, -⟩, -⟩ := hc'
  set S' := closure (permsA n sGens)
  have hS'le : S' ≤ R.subtype.range := by
    rw [closure_le, range_subtype]
    rintro _ ⟨j, hj, rfl⟩
    have hr := rep_of_validA (enumOK_gens_valid hS hj)
    have h := allLt_spec hgen hj
    rw [List.any_eq_true] at h
    obtain ⟨r, hr', he⟩ := h
    obtain ⟨g, hgR, hg⟩ := hregs r (List.mem_range.mp hr')
    show permOfArr n sGens[j]! ∈ R
    rw [eq_of_eqA hr hg he]
    exact hgR
  obtain ⟨-, hS'card, -⟩ := enumOK_spec hps hS
  set S := S'.comap R.subtype
  have hSmap : S.map R.subtype = S' := map_comap_eq_self hS'le
  have hScard : Nat.card S = 2 ^ k := by
    rw [← card_map_of_injective R.subtype_injective, hSmap, hS'card, hsize]
  have hSsyl : IsSylowOf 2 S ⊤ := by
    rw [isSylowOf_iff, relIndex_top_right]
    refine ⟨le_top, IsPGroup.of_card hScard, fun h2 => ?_⟩
    have h1 := S.card_mul_index
    rw [hScard, hcard] at h1
    have hidx : S.index = m := Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) k) h1
    rw [hidx] at h2
    exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h2)
  have hin : ∀ a, validA n a = true → testP a = true →
      permOfArr n a ∈ (P.subgroupOf R).map R.subtype := fun a hv ha => by
    rw [hmap]
    exact (htest _ _ (rep_of_validA hv)).1 ha
  have hout : ∀ a, validA n a = true → permOfArr n a ∈ (P.subgroupOf R).map R.subtype →
      testP a = true := fun a hv ha => by
    rw [hmap] at ha
    exact (htest _ _ (rep_of_validA hv)).2 ha
  refine yCensus_of_le_sylow hN hSsyl (fun E w hle x hx => ?_) fun E hES hE hE4 hnot => ?_
  · have hx' : w * x * w⁻¹ ∈ P.subgroupOf R := hle ⟨x, hx, rfl⟩
    have := hN.conj_mem _ hx' w⁻¹
    simpa [mul_assoc] using this
  · have hES' : E.map R.subtype ≤ S' := hSmap ▸ map_mono hES
    have hw := census_of_censusOK hps hin hout hc hES' (isElemAbelian_map hE R.subtype)
      (by rwa [card_map_of_injective R.subtype_injective])
    rcases hw with hw | ⟨h, -⟩ | ⟨-, hw⟩ | ⟨h, -⟩
    · exact (yWitness_map_iff _ R.subtype_injective _ _).mp hw
    · exact absurd h (by decide)
    · exact absurd ((map_le_map_iff_of_injective R.subtype_injective).mp hw) hnot
    · exact absurd h (by decide)

end CFSG.ComponentClassification.RankTwoL3Four.HypII
