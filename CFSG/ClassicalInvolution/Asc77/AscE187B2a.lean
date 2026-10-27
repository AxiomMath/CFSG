module

public import CFSG.ClassicalInvolution.Asc77.AscE187All
public import CFSG.ClassicalInvolution.Asc77.AscE187Basic

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem exists_conj_of_isSylow2In {P Y U : Subgroup G} (hP : IsSylow2In P Y) (hU : IsPGroup 2 U)
    (hUY : U ≤ Y) : ∃ y ∈ Y, U ≤ conjSub y P := by
  have hUp : IsPGroup 2 (U.subgroupOf Y) := hU.comap_subtype
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow hUp
  obtain ⟨y, hy⟩ := exists_conjSub_eq_of_sylow (G := ↥Y) (sylowOfIsSylow2In hP) Q
  refine ⟨y, y.2, fun x hx => ?_⟩
  have hxQ : (⟨x, hUY hx⟩ : ↥Y) ∈ (Q : Subgroup ↥Y) :=
    hQ (by simpa [Subgroup.mem_subgroupOf] using hx)
  rw [← hy, mem_conjSub_iff] at hxQ
  rw [mem_conjSub_iff]
  have h3 := Subgroup.mem_subgroupOf.mp hxQ
  simpa using h3

theorem MinCex.exists_config_sylow (c : MinCex p f Ω K S R W H)
    {K' R' X : Subgroup G} (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K) (hR' : R' ∈ RSet Ω)
    (hR'K' : R' ≤ K') (hR'S : R' ≤ (S : Subgroup G)) (hRX : R ⊔ R' ≤ X) :
    ∃ (S' : Sylow 2 G) (W' : Subgroup G), MinCex p f Ω K S' R W' H ∧ R ⊔ R' ≤ (S' : Subgroup G) ∧
      IsSylow2In ((S' : Subgroup G) ⊓ X) X := by
  have hp : p ≠ 2 := c.stand.odd
  have hq : 5 ≤ p ^ f := c.stand.five
  have hΩ : HypOmegaMod p f Ω := c.stand.hyp
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  have hRR' : IsPGroup 2 ↥(R ⊔ R') := S.isPGroup'.to_le (sup_le hRS hR'S)
  obtain ⟨P, hP, hRRP⟩ := IsSylow2In.exists_ge hRR' hRX
  obtain ⟨S', hPS'⟩ := IsPGroup.exists_le_sylow hP.2.1
  have hSyl : IsSylow2In ((S' : Subgroup G) ⊓ X) X := by
    have hle : P ≤ (S' : Subgroup G) ⊓ X := le_inf hPS' hP.1
    have hp2 : IsPGroup 2 ↥((S' : Subgroup G) ⊓ X) := S'.isPGroup'.to_le inf_le_left
    have heq := hP.eq_of_le hp2 inf_le_right hle
    rw [heq]
    exact hP
  obtain ⟨W', hW', hW'S', hW'n⟩ := WSet.exists_normalized_sylow hp hq hΩ S'
  have hRS' : R ≤ (S' : Subgroup G) := le_sup_left.trans (hRRP.trans hPS')
  have hR'S' : R' ≤ (S' : Subgroup G) := le_sup_right.trans (hRRP.trans hPS')
  exact ⟨S', W', c.of_sylow hRS' hK' hne hR' hR'K' hR'S' hW' hW'S' hW'n,
    sup_le hRS' hR'S', hSyl⟩

theorem MinCex.exists_config_sylow_centralizer (c : MinCex p f Ω K S R W H) {z : G}
    (hz : IsUniqueInvolution K z) :
    ∃ (S' : Sylow 2 G) (W' : Subgroup G), MinCex p f Ω K S' R W' H ∧
      IsSylow2In ((S' : Subgroup G) ⊓ Subgroup.centralizer ({z} : Set G))
        (Subgroup.centralizer ({z} : Set G)) := by
  have hp : p ≠ 2 := c.stand.odd
  have hq : 5 ≤ p ^ f := c.stand.five
  have hΩ : HypOmegaMod p f Ω := c.stand.hyp
  obtain ⟨K', hK'tw, hne, R', hR', hR'K', hR'S⟩ := c.stand.twin
  obtain ⟨-, hRK, -⟩ := c.stand.hR
  have hz' : IsUniqueInvolution K' z := by
    obtain ⟨-, z', hz'K, hz'K'⟩ := hK'tw
    have := hz.eq hz'K
    rwa [← this] at hz'K'
  have hKC : K ≤ Subgroup.centralizer ({z} : Set G) := fun x hx => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hz.commute_of_mem hx).symm
  have hK'C : K' ≤ Subgroup.centralizer ({z} : Set G) := fun x hx => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hz'.commute_of_mem hx).symm
  obtain ⟨S', W', c', -, hSyl⟩ := c.exists_config_sylow hK'tw hne hR' hR'K' hR'S
    (X := Subgroup.centralizer ({z} : Set G)) (sup_le (hRK.trans hKC) (hR'K'.trans hK'C))
  exact ⟨S', W', c', hSyl⟩

theorem MinCex.rename (h : E187Hyps p f) (c : MinCex p f Ω K S R W H)
    {K' R' K'' R'' : Subgroup G} (hK' : K' ∈ twinSet Ω K) (hR' : R' ∈ RSet Ω) (hR'K' : R' ≤ K')
    (hR'S : R' ≤ (S : Subgroup G)) (hK'' : K'' ∈ twinSet Ω K) (hne : K'' ≠ K')
    (hR'' : R'' ∈ RSet Ω) (hR''K'' : R'' ≤ K'') (hR''S : R'' ≤ (S : Subgroup G)) :
    MinCex p f Ω K' S R' W H := by
  have hp : p ≠ 2 := c.stand.odd
  have hΩ : HypOmegaMod p f Ω := c.stand.hyp
  obtain ⟨hK'Ω, z', hz'K, hz'K'⟩ := hK'
  obtain ⟨hK''Ω, z'', hz''K, hz''K''⟩ := hK''
  have hz : z'' = z' := hz''K.eq hz'K
  have hK''tw : K'' ∈ twinSet Ω K' := ⟨hK''Ω, z', hz'K', hz ▸ hz''K''⟩
  have hK'S : K' ∈ dstarComp Ω K := mem_dstarComp_of_twin hp hΩ c.stand.mem ⟨hK'Ω, z', hz'K, hz'K'⟩
  have hcomp : ∀ J ∈ dstarComp Ω K', J ∈ dstarComp Ω K := fun J hJ =>
    Relation.ReflTransGen.trans hK'S hJ
  obtain ⟨hWW, hWS, hWn⟩ := c.stand.hW
  have hcent' : CentralizersSylowPairs Ω K' H := c.hyp.cent.of_twin ⟨hK'Ω, z', hz'K, hz'K'⟩
  have hh₂ := c.hyp.trans K' hK'S
  refine
    { stand :=
        { odd := c.stand.odd
          five := c.stand.five
          hyp := c.stand.hyp
          below := c.stand.below
          mem := hK'Ω
          aEmpty := aEmpty_forall_of_transitive hΩ.conjInvariant
            (e18_3 p f h.l67 G Ω K S R W H c) c.stand.aEmpty K' hK'Ω
          twin := ⟨K'', hK''tw, hne, R'', hR'', hR''K'', hR''S⟩
          hR := ⟨hR', hR'K', hR'S⟩
          hW := ⟨hWW, hWS, hWn⟩ }
      hyp := ⟨fun J hJ => ?_, hcent'⟩
      proper := c.proper
      minimal := c.minimal }
  obtain ⟨h₁, hh₁H, hh₁⟩ := c.hyp.trans J (hcomp J hJ)
  obtain ⟨h₂, hh₂H, hh₂'⟩ := hh₂
  refine ⟨h₁ * h₂⁻¹, H.mul_mem hh₁H (H.inv_mem hh₂H), ?_⟩
  rw [conjSub_mul, ← hh₁, ← hh₂', conjSub_inv_conjSub]

end CFSG.ClassicalInvolution.Asc77
