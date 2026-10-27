module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM22Model
public import CFSG.Certificates.Kernel.Census.ToMain

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.M22

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.ABGLocalTools
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Monster.Code CFSG.Monster.B.TwoA CFSG.KC.Census

@[expose] noncomputable def m22CheckW (allowPW allowInX : Bool) (sG roots : Array ℕ)
    (nodes : Array NodeP) (cS : ArrCertP) (wcs : Array (Array ArrCertP)) (xg xs : Array ℕ)
    (xw : List (List ℕ)) : Bool :=
  (allLt (xg.map (unpackP 24 5)).size fun k =>
      validK 24 (xg.map (unpackP 24 5))[k]! && m22InX (xg.map (unpackP 24 5))[k]!) &&
    xsOK 24 (xg.map (unpackP 24 5)) (xs.map (unpackP 24 5)) xw &&
    censusOKW 24 m22PS (inXL 24 (xs.map (unpackP 24 5))) m22OutX allowPW allowInX false
      (sG.map (unpackP 24 5)) roots (nodes.map (NodeP.toMain 24 5)) (cS.toMain 24 5)
      (wcs.map fun cs => cs.map (ArrCertP.toMain 24 5)) &&
    (allLt (sG.map (unpackP 24 5)).size fun k => pairA (sG.map (unpackP 24 5))[k]!) &&
    (cS.toMain 24 5).pts.size == 256

theorem census_of_m22CheckW {allowPW allowInX : Bool}
    {sG roots : Array ℕ} {nodes : Array NodeP} {cS : ArrCertP} {wcs : Array (Array ArrCertP)}
    {xg xs : Array ℕ} {xw : List (List ℕ)}
    (h : m22CheckW allowPW allowInX sG roots nodes cS wcs xg xs xw = true) :
    ∃ S : Subgroup ↥Ppair, IsSylowOf 2 S ⊤ ∧ ∀ E ≤ S, IsElemAbelian 2 E → 4 ≤ Nat.card E →
      YWitness P0in E ∨ (allowPW = true ∧ PWitness P0in E) ∨ (allowInX = true ∧ E ≤ P0in) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  simp only [m22CheckW, validK_eq, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hxg, hxs⟩, hc⟩, hgen⟩, hsize⟩ := h
  set G := xg.map (unpackP 24 5)
  have hGv : (allLt G.size fun k => validA 24 G[k]!) = true := by
    rw [allLt_iff]
    intro k hk
    have := allLt_spec hxg hk
    simp only [Bool.and_eq_true] at this
    exact this.1
  have hGX : closure (permsA 24 G) ≤ P0in.map iota := by
    rw [closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have := allLt_spec hxg hk
    simp only [Bool.and_eq_true] at this
    exact m22_hin _ this.1 this.2
  have hin : ∀ a, validA 24 a = true → inXL 24 (xs.map (unpackP 24 5)) a = true →
      permOfArr 24 a ∈ P0in.map iota :=
    fun a hv ha => hGX (mem_closure_of_inXL hGv hxs hv ha)
  set sGens := sG.map (unpackP 24 5)
  have hc' := hc
  simp only [censusOKW, Bool.and_eq_true] at hc'
  obtain ⟨⟨hS, -⟩, -⟩ := hc'
  replace hS := enumOK_of_enumOKK hS
  set S' := closure (permsA 24 sGens)
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
    have hw := census_of_censusOKW m22PS_lt hin m22_hout hc hES'
      (isElemAbelian_map hE iota) (by rwa [card_map_of_injective iota_injective])
    rcases hw with hw | hw | hw | ⟨h, -⟩
    · exact Or.inl ((yWitness_map_iff iota iota_injective _ _).mp hw)
    · exact Or.inr (Or.inl ⟨hw.1, (pWitness_map_iff iota iota_injective _ _).mp hw.2⟩)
    · exact Or.inr (Or.inr ⟨hw.1, (map_le_map_iff_of_injective iota_injective).mp hw.2⟩)
    · exact absurd h (by decide)

theorem m22_yCensusIIW {sG roots : Array ℕ} {nodes : Array NodeP}
    {cS : ArrCertP} {wcs : Array (Array ArrCertP)} {xg xs : Array ℕ} {xw : List (List ℕ)}
    (h : m22CheckW false true sG roots nodes cS wcs xg xs xw = true) :
    YCensus P0in (· ≤ P0in) := by
  obtain ⟨S, hS, hcen⟩ := census_of_m22CheckW h
  refine yCensus_of_le_sylow P0in_normal hS (fun E w hle x hx => ?_)
    fun E hES hE hE4 hnot => ?_
  · have hx' : w * x * w⁻¹ ∈ P0in := hle ⟨x, hx, rfl⟩
    have := P0in_normal.conj_mem _ hx' w⁻¹
    simpa [mul_assoc] using this
  · rcases hcen E hES hE hE4 with hY | ⟨h, -⟩ | ⟨-, h⟩
    · exact hY
    · exact absurd h (by decide)
    · exact absurd h hnot

theorem m22_yCensus17W {sG roots : Array ℕ} {nodes : Array NodeP}
    {cS : ArrCertP} {wcs : Array (Array ArrCertP)} {xg xs : Array ℕ} {xw : List (List ℕ)}
    (h : m22CheckW true false sG roots nodes cS wcs xg xs xw = true) :
    YCensus17 P0in (fun _ => False) := by
  obtain ⟨S, hS, hcen⟩ := census_of_m22CheckW h
  refine yCensus17_of_le_sylow P0in_normal hS (fun _ _ h => h) fun E hES hE hE4 _ => ?_
  rcases hcen E hES hE hE4 with hY | ⟨-, h⟩ | ⟨h, -⟩
  · exact Or.inl hY
  · exact Or.inr h
  · exact absurd h (by decide)

@[expose] noncomputable def m22CheckW2 (allowPW allowInX : Bool) (sG roots : Array ℕ)
    (nodes : Array NodeP) (cS : ArrCertP) (wcs : Array (Array ArrCertP)) (pfs : Array PerfWP)
    (xg xs : Array ℕ) (xw : List (List ℕ)) : Bool :=
  (allLt (xg.map (unpackP 24 5)).size fun k =>
      validK 24 (xg.map (unpackP 24 5))[k]! && m22InX (xg.map (unpackP 24 5))[k]!) &&
    xsOK 24 (xg.map (unpackP 24 5)) (xs.map (unpackP 24 5)) xw &&
    censusOKW2 24 m22PS (inXL 24 (xs.map (unpackP 24 5))) m22OutX allowPW allowInX false
      (sG.map (unpackP 24 5)) roots (nodes.map (NodeP.toMain 24 5)) (cS.toMain 24 5)
      (wcs.map fun cs => cs.map (ArrCertP.toMain 24 5)) (pfs.map PerfWP.toMain) &&
    (allLt (sG.map (unpackP 24 5)).size fun k => pairA (sG.map (unpackP 24 5))[k]!) &&
    (cS.toMain 24 5).pts.size == 256

theorem census_of_m22CheckW2 {allowPW allowInX : Bool}
    {sG roots : Array ℕ} {nodes : Array NodeP} {cS : ArrCertP} {wcs : Array (Array ArrCertP)}
    {pfs : Array PerfWP} {xg xs : Array ℕ} {xw : List (List ℕ)}
    (h : m22CheckW2 allowPW allowInX sG roots nodes cS wcs pfs xg xs xw = true) :
    ∃ S : Subgroup ↥Ppair, IsSylowOf 2 S ⊤ ∧ ∀ E ≤ S, IsElemAbelian 2 E → 4 ≤ Nat.card E →
      YWitness P0in E ∨ (allowPW = true ∧ PWitness P0in E) ∨ (allowInX = true ∧ E ≤ P0in) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  simp only [m22CheckW2, validK_eq, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hxg, hxs⟩, hc⟩, hgen⟩, hsize⟩ := h
  set G := xg.map (unpackP 24 5)
  have hGv : (allLt G.size fun k => validA 24 G[k]!) = true := by
    rw [allLt_iff]
    intro k hk
    have := allLt_spec hxg hk
    simp only [Bool.and_eq_true] at this
    exact this.1
  have hGX : closure (permsA 24 G) ≤ P0in.map iota := by
    rw [closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have := allLt_spec hxg hk
    simp only [Bool.and_eq_true] at this
    exact m22_hin _ this.1 this.2
  have hin : ∀ a, validA 24 a = true → inXL 24 (xs.map (unpackP 24 5)) a = true →
      permOfArr 24 a ∈ P0in.map iota :=
    fun a hv ha => hGX (mem_closure_of_inXL hGv hxs hv ha)
  set sGens := sG.map (unpackP 24 5)
  have hc' := hc
  simp only [censusOKW2, Bool.and_eq_true] at hc'
  obtain ⟨⟨hS, -⟩, -⟩ := hc'
  replace hS := enumOK_of_enumOKK hS
  set S' := closure (permsA 24 sGens)
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
    have hw := census_of_censusOKW2 m22PS_lt hin m22_hout hc hES'
      (isElemAbelian_map hE iota) (by rwa [card_map_of_injective iota_injective])
    rcases hw with hw | hw | hw | ⟨h, -⟩
    · exact Or.inl ((yWitness_map_iff iota iota_injective _ _).mp hw)
    · exact Or.inr (Or.inl ⟨hw.1, (pWitness_map_iff iota iota_injective _ _).mp hw.2⟩)
    · exact Or.inr (Or.inr ⟨hw.1, (map_le_map_iff_of_injective iota_injective).mp hw.2⟩)
    · exact absurd h (by decide)

theorem m22_yCensus17W2 {sG roots : Array ℕ}
    {nodes : Array NodeP} {cS : ArrCertP} {wcs : Array (Array ArrCertP)} {pfs : Array PerfWP}
    {xg xs : Array ℕ} {xw : List (List ℕ)}
    (h : m22CheckW2 true false sG roots nodes cS wcs pfs xg xs xw = true) :
    YCensus17 P0in (fun _ => False) := by
  obtain ⟨S, hS, hcen⟩ := census_of_m22CheckW2 h
  refine yCensus17_of_le_sylow P0in_normal hS (fun _ _ h => h) fun E hES hE hE4 _ => ?_
  rcases hcen E hES hE hE4 with hY | ⟨-, h⟩ | ⟨h, -⟩
  · exact Or.inl hY
  · exact Or.inr h
  · exact absurd h (by decide)

end CFSG.ComponentClassification.RankTwoSporadic.M22
