module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicConjW

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Cert

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic CFSG.ABGLocalTools
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer

variable {n : ℕ} {P R : Subgroup (Equiv.Perm (Fin n))} {ps : List ℕ} {inX outX inW : Array ℕ → Bool}
  {allowPW allowInX : Bool} {d : ConjData} {e0 : Array (Array ℕ)} {m : ℕ}

theorem witness_pair_conjW_of (hPR : P ≤ R) (hN : (P.subgroupOf R).Normal)
    (hps : ∀ p ∈ ps, p < n)
    (hin : ∀ a, validA n a = true → inX a = true → permOfArr n a ∈ P)
    (hout : ∀ a, validA n a = true → permOfArr n a ∈ P → outX a = true)
    (hinW : ∀ a, validA n a = true → inW a = true → permOfArr n a ∈ R)
    (hc : conjCensusOKW n ps inX outX inW allowPW allowInX false d e0 = true)
    (hgen : d.xs.all inW = true)
    (hcard : Nat.card R = 2 ^ d.xs.length * m) (hm : Odd m) :
    ∃ S : Subgroup ↥R, IsSylowOf 2 S ⊤ ∧ ∀ E ≤ S, IsElemAbelian 2 E → 4 ≤ Nat.card E →
      YWitness (P.subgroupOf R) E ∨ (allowPW = true ∧ PWitness (P.subgroupOf R) E) ∨
        (allowInX = true ∧ E ≤ P.subgroupOf R) ∨ ExcClass R (closure (permsA n e0)) E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmap : (P.subgroupOf R).map R.subtype = P := by
    rw [subgroupOf_map_subtype, inf_eq_left.mpr hPR]
  have hc' := hc
  simp only [conjCensusOKW, Bool.and_eq_true] at hc'
  obtain ⟨hxv, -, -⟩ := pc_of_pcOK hc'.1.1.1.1.1
  set S' := pcSub n d.xs
  have hS'R : S' ≤ R := by
    refine (closure_le R).2 fun _ hx => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
    exact hinW _ (hxv a ha) (List.all_eq_true.1 hgen a ha)
  have hS'le : S' ≤ R.subtype.range := by rwa [range_subtype]
  have hconjP : ∀ r ∈ R, ∀ x ∈ P, r * x * r⁻¹ ∈ P := by
    intro r hr x hx
    have := hN.conj_mem ⟨x, hPR hx⟩ (by rwa [mem_subgroupOf]) ⟨r, hr⟩
    rwa [mem_subgroupOf] at this
  have hSX : ∀ s ∈ S', ((P.subgroupOf R).map R.subtype).map (MulAut.conj s).toMonoidHom =
      (P.subgroupOf R).map R.subtype := by
    intro s hs
    rw [hmap]
    refine le_antisymm ?_ fun x hx => ⟨s⁻¹ * x * s, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact hconjP s (hS'R hs) x hx
    · have := hconjP s⁻¹ (R.inv_mem (hS'R hs)) x hx
      rwa [inv_inv] at this
    · simp [MulAut.conj_apply, mul_assoc]
  have hin' : ∀ a, validA n a = true → inX a = true →
      permOfArr n a ∈ (P.subgroupOf R).map R.subtype := fun a hv ha => by
    rw [hmap]
    exact hin a hv ha
  have hout' : ∀ a, validA n a = true → permOfArr n a ∈ (P.subgroupOf R).map R.subtype →
      outX a = true := fun a hv ha => by
    rw [hmap] at ha
    exact hout a hv ha
  obtain ⟨hS'card, hw⟩ := census_of_conjCensusOKW hps hin' hout' hinW hS'R hSX hc
  set S := S'.comap R.subtype
  have hSmap : S.map R.subtype = S' := map_comap_eq_self hS'le
  have hScard : Nat.card S = 2 ^ d.xs.length := by
    rw [← card_map_of_injective R.subtype_injective, hSmap, hS'card]
  refine ⟨S, ?_, fun E hES hE hE4 => ?_⟩
  · rw [isSylowOf_iff, relIndex_top_right]
    refine ⟨le_top, IsPGroup.of_card hScard, fun h2 => ?_⟩
    have h1 := S.card_mul_index
    rw [hScard, hcard] at h1
    have hidx : S.index = m := Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) _) h1
    rw [hidx] at h2
    exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h2)
  · have hES' : E.map R.subtype ≤ S' := hSmap ▸ map_mono hES
    rcases hw _ hES' (isElemAbelian_map hE R.subtype)
        (by rwa [card_map_of_injective R.subtype_injective]) with
      (hw | hw | hw | ⟨h, -⟩) | ⟨w, hwR, heq⟩
    · exact Or.inl ((yWitness_map_iff _ R.subtype_injective _ _).mp hw)
    · exact Or.inr (Or.inl ⟨hw.1, (pWitness_map_iff _ R.subtype_injective _ _).mp hw.2⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hw.1, (map_le_map_iff_of_injective R.subtype_injective).mp
        hw.2⟩))
    · exact absurd h (by decide)
    · exact Or.inr (Or.inr (Or.inr ⟨w, hwR, heq⟩))

theorem yCensus_pair_conjW_of {testP : Array ℕ → Bool} {u : Array ℕ}
    {uR : Equiv.Perm (Fin n)} (hPR : P ≤ R) (hN : (P.subgroupOf R).Normal)
    (hps : ∀ p ∈ ps, p < n) (htest : ∀ a g, Rep n a g → (testP a = true ↔ g ∈ P))
    (hu : Rep n u uR) (huR : uR ∈ R)
    (hX : ∀ a, validA n a = true → inX a = true → testP a = true)
    (hW : ∀ a, validA n a = true → inW a = true → (testP a || testP (compA n u a)) = true)
    (hc : conjCensusOKW n ps inX (fun _ => true) inW false false false d #[] = true)
    (hgen : d.xs.all inW = true)
    (hcard : Nat.card R = 2 ^ d.xs.length * m) (hm : Odd m) :
    YCensus (P.subgroupOf R) (fun _ => False) := by
  have hinW : ∀ a, validA n a = true → inW a = true → permOfArr n a ∈ R := by
    intro a hv h
    have hr := rep_of_validA hv
    have h' := hW a hv h
    simp only [Bool.or_eq_true] at h'
    rcases h' with h' | h'
    · exact hPR ((htest _ _ hr).1 h')
    · have h'' := (htest _ _ (rep_compA hu hr)).1 h'
      have : permOfArr n a = uR⁻¹ * (uR * permOfArr n a) := by group
      rw [this]
      exact mul_mem (inv_mem huR) (hPR h'')
  obtain ⟨S, hS, hw⟩ := witness_pair_conjW_of hPR hN hps
    (fun a hv h => (htest _ _ (rep_of_validA hv)).1 (hX a hv h)) (fun _ _ _ => rfl) hinW hc hgen
    hcard hm
  refine yCensus_of_le_sylow hN hS (fun E w h => h) fun E hES hE hE4 _ => ?_
  rcases hw E hES hE hE4 with h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨w, -, heq⟩
  · exact h
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exfalso
    have hbot : closure (permsA n (#[] : Array (Array ℕ))) = ⊥ := by
      rw [closure_eq_bot_iff]
      rintro _ ⟨j, hj, -⟩
      exact absurd hj (by simp)
    rw [hbot, Subgroup.map_bot] at heq
    have hEbot : E = ⊥ := by
      rw [← map_eq_bot_iff_of_injective E R.subtype_injective, heq]
    rw [hEbot, card_bot] at hE4
    omega

end CFSG.ComponentClassification.RankTwoSporadic.Cert
