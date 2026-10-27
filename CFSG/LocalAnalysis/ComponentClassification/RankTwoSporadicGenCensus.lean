module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSLP
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicStandard17U
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM24Tests

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Cert

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic CFSG.ABGLocalTools
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

variable {n : ℕ} {H : Subgroup (Equiv.Perm (Fin n))} {gens : Array (Array ℕ)}
  {ps : List ℕ} {fuel : ℕ} {prog : List (ℕ × ℕ)} {d : CensusData} {allowU : Bool} {k m : ℕ}

theorem witness_top_of_check (hH : closure (permsA n gens) = H) (hps : ∀ p ∈ ps, p < n)
    (hslp : slpOK n gens prog = true)
    (hc : censusOK n ps fuel (inRegs n ps (slpRegs n gens prog)
      (regIndex n ps (slpRegs n gens prog))) M24.allA true false allowU d.sGens d.roots d.nodes =
      true)
    (hgen : (allLt d.sGens.size fun j => inRegs n ps (slpRegs n gens prog)
      (regIndex n ps (slpRegs n gens prog)) d.sGens[j]!) = true)
    (hsize : (enumBfs n d.sGens ps fuel).pts.size = 2 ^ k)
    (hcard : Nat.card H = 2 ^ k * m) (hm : Odd m) :
    ∃ S : Subgroup ↥H, IsSylowOf 2 S ⊤ ∧ ∀ E ≤ S, IsElemAbelian 2 E → 4 ≤ Nat.card E →
      YWitness (⊤ : Subgroup ↥H) E ∨ PWitness (⊤ : Subgroup ↥H) E ∨
        (allowU = true ∧ UWitness (⊤ : Subgroup ↥H) E) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set regs := slpRegs n gens prog
  set idx := regIndex n ps regs
  have hmem : ∀ a, validA n a = true → inRegs n ps regs idx a = true → permOfArr n a ∈ H :=
    fun a hv ha => hH ▸ mem_closure_of_inRegs hslp hv ha
  have hmap : (⊤ : Subgroup ↥H).map H.subtype = H := by
    rw [← MonoidHom.range_eq_map]
    exact range_subtype H
  have hc' := hc
  simp only [censusOK, Bool.and_eq_true] at hc'
  obtain ⟨⟨hS, -⟩, -⟩ := hc'
  set S' := closure (permsA n d.sGens)
  have hS'le : S' ≤ H.subtype.range := by
    rw [closure_le]
    rintro _ ⟨j, hj, rfl⟩
    exact ⟨⟨_, hmem _ (enumOK_gens_valid hS hj) (allLt_spec hgen hj)⟩, rfl⟩
  obtain ⟨-, hS'card, -⟩ := enumOK_spec hps hS
  set S := S'.comap H.subtype
  have hSmap : S.map H.subtype = S' := map_comap_eq_self hS'le
  have hScard : Nat.card S = 2 ^ k := by
    rw [← card_map_of_injective H.subtype_injective, hSmap, hS'card, hsize]
  refine ⟨S, ?_, fun E hES hE hE4 => ?_⟩
  · rw [isSylowOf_iff, relIndex_top_right]
    refine ⟨le_top, IsPGroup.of_card hScard, fun h2 => ?_⟩
    have h1 := S.card_mul_index
    rw [hScard, hcard] at h1
    have hidx : S.index = m := by
      have hpos : 0 < 2 ^ k := pow_pos (by norm_num) k
      exact Nat.eq_of_mul_eq_mul_left hpos h1
    rw [hidx] at h2
    exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h2)
  · have hin : ∀ a, validA n a = true → inRegs n ps regs idx a = true →
        permOfArr n a ∈ (⊤ : Subgroup ↥H).map H.subtype := fun a hv ha => by
      rw [hmap]
      exact hmem a hv ha
    have hout : ∀ a, validA n a = true → permOfArr n a ∈ (⊤ : Subgroup ↥H).map H.subtype →
        M24.allA a = true := fun _ _ _ => rfl
    have hES' : E.map H.subtype ≤ S' := hSmap ▸ map_mono hES
    have hw := census_of_censusOK hps hin hout hc hES' (isElemAbelian_map hE H.subtype)
      (by rwa [card_map_of_injective H.subtype_injective])
    rcases hw with hw | hw | ⟨h, -⟩ | hw
    · exact Or.inl ((yWitness_map_iff _ H.subtype_injective _ _).mp hw)
    · exact Or.inr (Or.inl ((pWitness_map_iff _ H.subtype_injective _ _).mp hw.2))
    · exact absurd h (by decide)
    · exact Or.inr (Or.inr ⟨hw.1, (uWitness_map_iff _ H.subtype_injective _ _).mp hw.2⟩)

theorem yCensus17U_top_of_check (hH : closure (permsA n gens) = H) (hps : ∀ p ∈ ps, p < n)
    (hslp : slpOK n gens prog = true)
    (hc : censusOK n ps fuel (inRegs n ps (slpRegs n gens prog)
      (regIndex n ps (slpRegs n gens prog))) M24.allA true false allowU d.sGens d.roots d.nodes =
      true)
    (hgen : (allLt d.sGens.size fun j => inRegs n ps (slpRegs n gens prog)
      (regIndex n ps (slpRegs n gens prog)) d.sGens[j]!) = true)
    (hsize : (enumBfs n d.sGens ps fuel).pts.size = 2 ^ k)
    (hcard : Nat.card H = 2 ^ k * m) (hm : Odd m) :
    YCensus17U (⊤ : Subgroup ↥H) (fun _ => False) := by
  obtain ⟨S, hS, hw⟩ := witness_top_of_check hH hps hslp hc hgen hsize hcard hm
  refine yCensus17U_of_le_sylow inferInstance hS (fun _ _ h => h) fun E hES hE hE4 _ => ?_
  rcases hw E hES hE hE4 with h | h | ⟨-, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem yCensus17_top_of_check (hH : closure (permsA n gens) = H) (hps : ∀ p ∈ ps, p < n)
    (hslp : slpOK n gens prog = true)
    (hc : censusOK n ps fuel (inRegs n ps (slpRegs n gens prog)
      (regIndex n ps (slpRegs n gens prog))) M24.allA true false false d.sGens d.roots d.nodes =
      true)
    (hgen : (allLt d.sGens.size fun j => inRegs n ps (slpRegs n gens prog)
      (regIndex n ps (slpRegs n gens prog)) d.sGens[j]!) = true)
    (hsize : (enumBfs n d.sGens ps fuel).pts.size = 2 ^ k)
    (hcard : Nat.card H = 2 ^ k * m) (hm : Odd m) :
    YCensus17 (⊤ : Subgroup ↥H) (fun _ => False) := by
  obtain ⟨S, hS, hw⟩ := witness_top_of_check hH hps hslp hc hgen hsize hcard hm
  refine yCensus17_of_le_sylow inferInstance hS (fun _ _ h => h) fun E hES hE hE4 _ => ?_
  rcases hw E hES hE hE4 with h | h | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h (by decide)

theorem yCensus_top_le_top {W : Type*} [Group W] :
    YCensus (⊤ : Subgroup W) (· ≤ (⊤ : Subgroup W)) :=
  fun _ _ _ h => absurd le_top h

end CFSG.ComponentClassification.RankTwoSporadic.Cert
