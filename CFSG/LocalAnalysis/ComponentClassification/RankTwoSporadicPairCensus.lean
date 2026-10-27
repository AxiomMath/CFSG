module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCheck
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicStandard17U

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Cert

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic CFSG.ABGLocalTools
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

section Model

variable {G : Type*} [Group G]

theorem autModel_of_conj {P R : Subgroup G} (hPR : P ≤ R) {X₀ : Type*} [Group X₀]
    (eP : ↥P ≃* X₀) (e : ↥R ≃* MulAut ↥P)
    (he : ∀ (x : ↥R) (p : ↥P), ((e x p : ↥P) : G) = (x : G) * p * (x : G)⁻¹) :
    AutModel X₀ ↥R (P.subgroupOf R) where
  normal := by
    refine ⟨fun y hy x => ?_⟩
    rw [mem_subgroupOf] at hy ⊢
    have := he x ⟨y, hy⟩
    simp only [coe_mul, coe_inv]
    rw [← this]
    exact (e x ⟨y, hy⟩).2
  centralizer_eq_bot := by
    rw [eq_bot_iff]
    intro x hx
    rw [mem_bot]
    apply e.injective
    rw [map_one]
    ext p
    have hxp := mem_centralizer_iff.mp hx ⟨p, hPR p.2⟩ (by
      rw [SetLike.mem_coe, mem_subgroupOf]
      exact p.2)
    have h1 := he x p
    have h2 : (x : G) * p * (x : G)⁻¹ = p := by
      have := congrArg Subtype.val hxp
      simp only [coe_mul] at this
      rw [← this]
      group
    rw [h1, h2]
    rfl
  nonempty_mulEquiv := ⟨(subgroupOfEquivOfLe hPR).trans eP⟩
  exists_conj α := by
    set ψ := subgroupOfEquivOfLe hPR
    refine ⟨e.symm (MulAut.congr ψ α), fun y => ?_⟩
    have h1 := he (e.symm (MulAut.congr ψ α)) (ψ y)
    rw [MulEquiv.apply_symm_apply] at h1
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1
    apply Subtype.ext
    simp only [coe_mul, coe_inv]
    exact h1

theorem autModel_of_allInner {P : Subgroup G} {X₀ : Type*} [Group X₀] (eP : ↥P ≃* X₀)
    (hc : center ↥P = ⊥) (hi : ∀ α : MulAut ↥P, ∃ g : ↥P, α = MulAut.conj g) :
    AutModel X₀ ↥P (P.subgroupOf P) := by
  have hinj : Function.Injective (MulAut.conj : ↥P →* MulAut ↥P) := by
    intro x y hxy
    have hmem : y⁻¹ * x ∈ center ↥P := by
      rw [mem_center_iff]
      intro g
      have h := congrArg (fun φ : MulAut ↥P => φ g) hxy
      simp only [MulAut.conj_apply] at h
      calc g * (y⁻¹ * x) = y⁻¹ * (y * g * y⁻¹) * y * y⁻¹ * x := by group
        _ = y⁻¹ * (x * g * x⁻¹) * y * y⁻¹ * x := by rw [h]
        _ = y⁻¹ * x * g := by group
    rw [hc, mem_bot] at hmem
    calc x = y * (y⁻¹ * x) := by group
      _ = y := by rw [hmem, mul_one]
  have hsurj : Function.Surjective (MulAut.conj : ↥P →* MulAut ↥P) := fun α => by
    obtain ⟨g, hg⟩ := hi α
    exact ⟨g, hg.symm⟩
  let e : ↥P ≃* MulAut ↥P :=
    MulEquiv.ofBijective (MulAut.conj : ↥P →* MulAut ↥P) ⟨hinj, hsurj⟩
  refine autModel_of_conj le_rfl eP e fun x p => ?_
  change ((MulAut.conj x p : ↥P) : G) = (x : G) * p * (x : G)⁻¹
  rw [MulAut.conj_apply]
  simp only [coe_mul, coe_inv]

theorem commutator_le_of_index_two {H : Subgroup G} (h : H.index = 2) :
    ⁅(⊤ : Subgroup G), ⊤⁆ ≤ H := by
  rw [commutator_le]
  intro a _ b _
  rw [commutatorElement_def, mul_mem_iff_of_index_two h, mul_mem_iff_of_index_two h,
    mul_mem_iff_of_index_two h, inv_mem_iff, inv_mem_iff]
  tauto

end Model

variable {n : ℕ} {P R : Subgroup (Equiv.Perm (Fin n))} {testP : Array ℕ → Bool} {ps : List ℕ}
  {fuel : ℕ} {allowPW allowInX allowU : Bool} {sGens : Array (Array ℕ)} {roots : Array ℕ}
  {nodes : Array Node} {u : Array ℕ} {uR : Equiv.Perm (Fin n)} {k m : ℕ}

theorem witness_pair_of_check (hPR : P ≤ R) (hps : ∀ p ∈ ps, p < n)
    (htest : ∀ a g, Rep n a g → (testP a = true ↔ g ∈ P)) (hu : Rep n u uR) (huR : uR ∈ R)
    (hc : censusOK n ps fuel testP testP allowPW allowInX allowU sGens roots nodes = true)
    (hgen : (allLt sGens.size fun j => testP sGens[j]! || testP (compA n u sGens[j]!)) = true)
    (hsize : (enumBfs n sGens ps fuel).pts.size = 2 ^ k)
    (hcard : Nat.card R = 2 ^ k * m) (hm : Odd m) :
    ∃ S : Subgroup ↥R, IsSylowOf 2 S ⊤ ∧ ∀ E ≤ S, IsElemAbelian 2 E → 4 ≤ Nat.card E →
      YWitness (P.subgroupOf R) E ∨ (allowPW = true ∧ PWitness (P.subgroupOf R) E) ∨
        (allowInX = true ∧ E ≤ P.subgroupOf R) ∨
        (allowU = true ∧ UWitness (P.subgroupOf R) E) := by
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
    have hv := enumOK_gens_valid hS hj
    have hr := rep_of_validA hv
    have h := allLt_spec hgen hj
    simp only [Bool.or_eq_true] at h
    show permOfArr n sGens[j]! ∈ R
    rcases h with h | h
    · exact hPR ((htest _ _ hr).1 h)
    · have h' := (htest _ _ (rep_compA hu hr)).1 h
      have : permOfArr n sGens[j]! = uR⁻¹ * (uR * permOfArr n sGens[j]!) := by group
      rw [this]
      exact mul_mem (inv_mem huR) (hPR h')
  obtain ⟨-, hS'card, -⟩ := enumOK_spec hps hS
  set S := S'.comap R.subtype
  have hSmap : S.map R.subtype = S' := map_comap_eq_self hS'le
  have hScard : Nat.card S = 2 ^ k := by
    rw [← card_map_of_injective R.subtype_injective, hSmap, hS'card, hsize]
  refine ⟨S, ?_, fun E hES hE hE4 => ?_⟩
  · rw [isSylowOf_iff, relIndex_top_right]
    refine ⟨le_top, IsPGroup.of_card hScard, fun h2 => ?_⟩
    have h1 := S.card_mul_index
    rw [hScard, hcard] at h1
    have hidx : S.index = m := Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) k) h1
    rw [hidx] at h2
    exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h2)
  · have hin : ∀ a, validA n a = true → testP a = true →
        permOfArr n a ∈ (P.subgroupOf R).map R.subtype := fun a hv ha => by
      rw [hmap]
      exact (htest _ _ (rep_of_validA hv)).1 ha
    have hout : ∀ a, validA n a = true → permOfArr n a ∈ (P.subgroupOf R).map R.subtype →
        testP a = true := fun a hv ha => by
      rw [hmap] at ha
      exact (htest _ _ (rep_of_validA hv)).2 ha
    have hES' : E.map R.subtype ≤ S' := hSmap ▸ map_mono hES
    have hw := census_of_censusOK hps hin hout hc hES' (isElemAbelian_map hE R.subtype)
      (by rwa [card_map_of_injective R.subtype_injective])
    rcases hw with hw | hw | hw | hw
    · exact Or.inl ((yWitness_map_iff _ R.subtype_injective _ _).mp hw)
    · exact Or.inr (Or.inl ⟨hw.1, (pWitness_map_iff _ R.subtype_injective _ _).mp hw.2⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hw.1, (map_le_map_iff_of_injective R.subtype_injective).mp
        hw.2⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hw.1, (uWitness_map_iff _ R.subtype_injective _ _).mp
        hw.2⟩))

theorem yCensus_pair_of_check (hPR : P ≤ R) (hN : (P.subgroupOf R).Normal)
    (hps : ∀ p ∈ ps, p < n) (htest : ∀ a g, Rep n a g → (testP a = true ↔ g ∈ P))
    (hu : Rep n u uR) (huR : uR ∈ R)
    (hc : censusOK n ps fuel testP testP false false false sGens roots nodes = true)
    (hgen : (allLt sGens.size fun j => testP sGens[j]! || testP (compA n u sGens[j]!)) = true)
    (hsize : (enumBfs n sGens ps fuel).pts.size = 2 ^ k)
    (hcard : Nat.card R = 2 ^ k * m) (hm : Odd m) :
    YCensus (P.subgroupOf R) (fun _ => False) := by
  obtain ⟨S, hS, hw⟩ := witness_pair_of_check hPR hps htest hu huR hc hgen hsize hcard hm
  refine yCensus_of_le_sylow hN hS (fun _ _ h => h) fun E hES hE hE4 _ => ?_
  rcases hw E hES hE hE4 with h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact h
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)

theorem yCensusII_pair_of_check (hPR : P ≤ R) (hN : (P.subgroupOf R).Normal)
    (hps : ∀ p ∈ ps, p < n) (htest : ∀ a g, Rep n a g → (testP a = true ↔ g ∈ P))
    (hu : Rep n u uR) (huR : uR ∈ R)
    (hc : censusOK n ps fuel testP testP false true false sGens roots nodes = true)
    (hgen : (allLt sGens.size fun j => testP sGens[j]! || testP (compA n u sGens[j]!)) = true)
    (hsize : (enumBfs n sGens ps fuel).pts.size = 2 ^ k)
    (hcard : Nat.card R = 2 ^ k * m) (hm : Odd m) :
    YCensus (P.subgroupOf R) (· ≤ P.subgroupOf R) := by
  obtain ⟨S, hS, hw⟩ := witness_pair_of_check hPR hps htest hu huR hc hgen hsize hcard hm
  refine yCensus_of_le_sylow hN hS (fun E w hle x hx => ?_) fun E hES hE hE4 hnot => ?_
  · have hx' : w * x * w⁻¹ ∈ P.subgroupOf R := hle ⟨x, hx, rfl⟩
    have := hN.conj_mem _ hx' w⁻¹
    simpa [mul_assoc] using this
  · rcases hw E hES hE hE4 with h | ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h (by decide)
    · exact absurd h hnot
    · exact absurd h (by decide)

theorem yCensus17_pair_of_check (hPR : P ≤ R) (hN : (P.subgroupOf R).Normal)
    (hps : ∀ p ∈ ps, p < n) (htest : ∀ a g, Rep n a g → (testP a = true ↔ g ∈ P))
    (hu : Rep n u uR) (huR : uR ∈ R)
    (hc : censusOK n ps fuel testP testP true false false sGens roots nodes = true)
    (hgen : (allLt sGens.size fun j => testP sGens[j]! || testP (compA n u sGens[j]!)) = true)
    (hsize : (enumBfs n sGens ps fuel).pts.size = 2 ^ k)
    (hcard : Nat.card R = 2 ^ k * m) (hm : Odd m) :
    YCensus17 (P.subgroupOf R) (fun _ => False) := by
  obtain ⟨S, hS, hw⟩ := witness_pair_of_check hPR hps htest hu huR hc hgen hsize hcard hm
  refine yCensus17_of_le_sylow hN hS (fun _ _ h => h) fun E hES hE hE4 _ => ?_
  rcases hw E hES hE hE4 with h | ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h (by decide)
  · exact absurd h (by decide)

theorem yCensus17U_pair_of_check (hPR : P ≤ R) (hN : (P.subgroupOf R).Normal)
    (hps : ∀ p ∈ ps, p < n) (htest : ∀ a g, Rep n a g → (testP a = true ↔ g ∈ P))
    (hu : Rep n u uR) (huR : uR ∈ R)
    (hc : censusOK n ps fuel testP testP true false true sGens roots nodes = true)
    (hgen : (allLt sGens.size fun j => testP sGens[j]! || testP (compA n u sGens[j]!)) = true)
    (hsize : (enumBfs n sGens ps fuel).pts.size = 2 ^ k)
    (hcard : Nat.card R = 2 ^ k * m) (hm : Odd m) :
    YCensus17U (P.subgroupOf R) (fun _ => False) := by
  obtain ⟨S, hS, hw⟩ := witness_pair_of_check hPR hps htest hu huR hc hgen hsize hcard hm
  refine yCensus17U_of_le_sylow hN hS (fun _ _ h => h) fun E hES hE hE4 _ => ?_
  rcases hw E hES hE hE4 with h | ⟨-, h⟩ | ⟨h, -⟩ | ⟨-, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact absurd h (by decide)
  · exact Or.inr (Or.inr h)

end CFSG.ComponentClassification.RankTwoSporadic.Cert
