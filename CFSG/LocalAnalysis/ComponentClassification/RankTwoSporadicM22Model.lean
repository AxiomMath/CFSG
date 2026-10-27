module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM22Tests
public import CFSG.Monster.B.TwoA.Fischer.M22Aut

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.M22

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.ABGLocalTools
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Monster.Code CFSG.Monster.B.TwoA

theorem m22AutModel :
    AutModel (Blueprint.NativeSporadic.Carrier .M22) ↥Ppair P0in where
  normal := P0in_normal
  centralizer_eq_bot := centralizer_P0
  nonempty_mulEquiv := ⟨P0inEquiv⟩
  exists_conj α := by
    obtain ⟨w, hw⟩ := (Fischer.catalog_M22_full_automorphism_order.2.2.2.1).2
      (MulAut.congr P0inEquiv α)
    have hwα : MulAut.conjNormal (H := P0in) w = α := by
      apply (MulAut.congr P0inEquiv).injective
      rw [← hw]
      rfl
    refine ⟨w, fun x => ?_⟩
    rw [← hwα, MulAut.conjNormal_apply]

theorem m22_commutator_le : ⁅(⊤ : Subgroup ↥Ppair), ⊤⁆ ≤ P0in := by
  rw [commutator_le]
  intro a _ b _
  rw [commutatorElement_def, mul_mem_iff_of_index_two index_P0in,
    mul_mem_iff_of_index_two index_P0in, mul_mem_iff_of_index_two index_P0in, inv_mem_iff,
    inv_mem_iff]
  tauto

@[expose] def iota : ↥Ppair →* Equiv.Perm (Fin 24) := AutPerm.subtype.comp Ppair.subtype

theorem iota_injective : Function.Injective iota := fun _ _ h =>
  Subtype.ext (Subtype.ext h)

theorem mem_map_iota_P0in_iff {p : Equiv.Perm (Fin 24)} :
    p ∈ P0in.map iota ↔ p ∈ AutPerm ∧ p 0 = 0 ∧ p 1 = 1 := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [SetLike.mem_coe, P0in, mem_subgroupOf, mem_P0_iff] at hq
    exact ⟨(q : AutPerm).2, hq⟩
  · rintro ⟨hp, h0, h1⟩
    refine ⟨⟨⟨p, hp⟩, mem_Ppair_of_fix ⟨p, hp⟩ h0 h1⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, P0in, mem_subgroupOf, mem_P0_iff]
    exact ⟨h0, h1⟩

theorem entries_of_validA {a : Array ℕ} (hv : validA 24 a = true) :
    a[0]! = ((permOfArr 24 a 0 : Fin 24) : ℕ) ∧ a[1]! = ((permOfArr 24 a 1 : Fin 24) : ℕ) :=
  ⟨rep_of_validA hv 0, rep_of_validA hv 1⟩

theorem m22_hin (a : Array ℕ) (hv : validA 24 a = true) (h : m22InX a = true) :
    permOfArr 24 a ∈ P0in.map iota := by
  simp only [m22InX, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨ha, h0⟩, h1⟩ := h
  obtain ⟨e0, e1⟩ := entries_of_validA hv
  refine mem_map_iota_P0in_iff.2 ⟨mem_AutPerm_of_autA ha, Fin.ext ?_, Fin.ext ?_⟩
  · rw [← e0, h0]
    rfl
  · rw [← e1, h1]
    rfl

theorem m22_hout (a : Array ℕ) (hv : validA 24 a = true) (h : permOfArr 24 a ∈ P0in.map iota) :
    m22OutX a = true := by
  obtain ⟨-, h0, h1⟩ := mem_map_iota_P0in_iff.1 h
  obtain ⟨e0, e1⟩ := entries_of_validA hv
  simp only [m22OutX, Bool.and_eq_true, beq_iff_eq]
  refine ⟨?_, ?_⟩
  · rw [e0, h0]
    rfl
  · rw [e1, h1]
    rfl

theorem mem_range_of_pairA {a : Array ℕ} (h : pairA a = true) : permOfArr 24 a ∈ iota.range := by
  simp only [pairA, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨ha, h01⟩ := h
  have hv : validA 24 a = true := by
    simp only [autA, Bool.and_eq_true] at ha
    exact ha.1.1
  have hp := mem_AutPerm_of_autA ha
  obtain ⟨e0, e1⟩ := entries_of_validA hv
  have hP : (⟨permOfArr 24 a, hp⟩ : AutPerm) ∈ Ppair := by
    rw [mem_Ppair_iff]
    change (permOfArr 24 a 0 = 0 ∧ permOfArr 24 a 1 = 1) ∨
      (permOfArr 24 a 0 = 1 ∧ permOfArr 24 a 1 = 0)
    rcases h01 with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · exact .inl ⟨Fin.ext (by rw [← e0, h0]; rfl), Fin.ext (by rw [← e1, h1]; rfl)⟩
    · exact .inr ⟨Fin.ext (by rw [← e0, h0]; rfl), Fin.ext (by rw [← e1, h1]; rfl)⟩
  exact ⟨⟨⟨permOfArr 24 a, hp⟩, hP⟩, rfl⟩

theorem census_of_m22Check {allowPW allowInX : Bool} {s : String}
    (h : m22Check allowPW allowInX s = true) :
    ∃ S : Subgroup ↥Ppair, IsSylowOf 2 S ⊤ ∧ ∀ E ≤ S, IsElemAbelian 2 E → 4 ≤ Nat.card E →
      YWitness P0in E ∨ (allowPW = true ∧ PWitness P0in E) ∨ (allowInX = true ∧ E ≤ P0in) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  simp only [m22Check, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hc, hgen⟩, hsize⟩ := h
  set d := decodeCert 24 s
  have hc' := hc
  simp only [censusOK, Bool.and_eq_true] at hc'
  obtain ⟨⟨hS, -⟩, -⟩ := hc'
  set S' := closure (permsA 24 d.sGens)
  have hS'le : S' ≤ iota.range := by
    rw [closure_le]
    rintro _ ⟨k, hk, rfl⟩
    exact mem_range_of_pairA (allLt_spec hgen hk)
  obtain ⟨-, hS'card, -⟩ := enumOK_spec m22PS_lt hS
  set S := S'.comap iota
  have hSmap : S.map iota = S' := map_comap_eq_self hS'le
  have hScard : Nat.card S = 256 := by
    rw [← card_map_of_injective iota_injective, hSmap, hS'card, hsize]
  refine ⟨S, ?_, fun E hES hE hE4 => ?_⟩
  · rw [isSylowOf_iff, relIndex_top_right]
    refine ⟨le_top, IsPGroup.of_card (n := 8) (by rw [hScard]; norm_num), ?_⟩
    have h1 := S.card_mul_index
    rw [hScard, natCard_Ppair] at h1
    omega
  · have hES' : E.map iota ≤ S' := hSmap ▸ map_mono hES
    have hw := census_of_censusOK m22PS_lt m22_hin m22_hout hc hES'
      (isElemAbelian_map hE iota) (by rwa [card_map_of_injective iota_injective])
    rcases hw with hw | hw | hw | ⟨h, -⟩
    · exact Or.inl ((yWitness_map_iff iota iota_injective _ _).mp hw)
    · exact Or.inr (Or.inl ⟨hw.1, (pWitness_map_iff iota iota_injective _ _).mp hw.2⟩)
    · exact Or.inr (Or.inr ⟨hw.1, (map_le_map_iff_of_injective iota_injective).mp hw.2⟩)
    · exact absurd h (by decide)

theorem m22_yCensusII {s : String} (h : m22Check false true s = true) :
    YCensus P0in (· ≤ P0in) := by
  obtain ⟨S, hS, hcen⟩ := census_of_m22Check h
  refine yCensus_of_le_sylow P0in_normal hS (fun E w hle x hx => ?_)
    fun E hES hE hE4 hnot => ?_
  · have hx' : w * x * w⁻¹ ∈ P0in := hle ⟨x, hx, rfl⟩
    have := P0in_normal.conj_mem _ hx' w⁻¹
    simpa [mul_assoc] using this
  · rcases hcen E hES hE hE4 with hY | ⟨h, -⟩ | ⟨-, h⟩
    · exact hY
    · exact absurd h (by decide)
    · exact absurd h hnot

theorem m22_yCensus17 {s : String} (h : m22Check true false s = true) :
    YCensus17 P0in (fun _ => False) := by
  obtain ⟨S, hS, hcen⟩ := census_of_m22Check h
  refine yCensus17_of_le_sylow P0in_normal hS (fun _ _ h => h) fun E hES hE hE4 _ => ?_
  rcases hcen E hES hE hE4 with hY | ⟨-, h⟩ | ⟨h, -⟩
  · exact Or.inl hY
  · exact Or.inr h
  · exact absurd h (by decide)

end CFSG.ComponentClassification.RankTwoSporadic.M22
