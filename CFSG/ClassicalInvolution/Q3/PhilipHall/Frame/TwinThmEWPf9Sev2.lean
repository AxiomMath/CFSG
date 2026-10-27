module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEW189a
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf9Sev1
public import CFSG.ClassicalInvolution.Asc77.AscE187B2d
public import CFSG.ClassicalInvolution.Asc77.AscE187P1d

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
open scoped commutatorElement

namespace TwinThmEW
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

section
variable [PrintedQuotOdd] [PrintedQuotCent] [PrintedHull]

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCexQ8.of_sylow (c : MinCexQ8 Ω K S R W H) {S' : Sylow 2 G} {W' : Subgroup G}
    (hRS' : R ≤ (S' : Subgroup G)) {K' R' : Subgroup G} (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K)
    (hR' : R' ∈ RSet Ω) (hR'K' : R' ≤ K') (hR'S' : R' ≤ (S' : Subgroup G))
    (hW' : W' ∈ WSet Ω) (hW'S' : W' ≤ (S' : Subgroup G))
    (hW'n : ∀ s ∈ (S' : Subgroup G), conjSub s W' = W') (hCW' : CentPairs Ω (S' : Subgroup G) W' H) :
    MinCexQ8 Ω K S' R W' H where
  stand :=
    { hyp := c.stand.hyp
      cls := c.stand.cls
      q8 := c.stand.q8
      two := c.stand.two
      ih := c.stand.ih
      mem := c.stand.mem
      aEmpty := c.stand.aEmpty
      twin := ⟨K', hK', hne, R', hR', hR'K', hR'S'⟩
      hR := ⟨c.stand.hR.1, c.stand.hR.2.1, hRS'⟩
      hW := ⟨hW', hW'S', hW'n⟩ }
  hyp := ⟨c.hyp.trans, hCW'⟩
  proper := c.proper
  minimal := c.minimal
end

section
variable [PrintedQuotOdd] [PrintedQuotCent] [PrintedHull]

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCexQ8.centralizer_le_H' (h4 : E18_4CQ8) (c : MinCexQ8 Ω K S R W H)
    {K' R' : Subgroup G} (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K)
    (hR' : R' ∈ RSet Ω) (hR'K' : R' ≤ K') (hR'S : R' ≤ (S : Subgroup G)) {A : Subgroup G}
    (_hA : IsPGroup 2 A) (hAcyc : (∃ w : G, w ≠ 1 ∧ w * w = 1 ∧ A = Subgroup.zpowers w))
    (hRA : R ⊔ R' ≤ Subgroup.centralizer (A : Set G))
    (hX : Subgroup.centralizer (A : Set G) ≠ ⊤) : Subgroup.centralizer (A : Set G) ≤ H := by
  obtain ⟨w, hw1, hw2, rfl⟩ := hAcyc
  rw [centralizer_zpowers_eq_singleton] at hRA hX ⊢
  have hRS := c.stand.hR.2.2
  exact h4 G Ω K S R W H c K' hK' hne R' hR' hR'K' (S.isPGroup'.to_le (sup_le hRS hR'S)) w hw1 hw2
    hRA hX
end

section
variable [PrintedQuotOdd] [PrintedQuotCent] [PrintedHull]

open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCexQ8.part1_core (h : E18_6Q8) (h4 : E18_4CQ8)
    (c : MinCexQ8 Ω K S R W H) {z : G} (hz : IsUniqueInvolution K z) (hzW : z ∈ W)
    (hP : ∀ x : G, x * z * x⁻¹ ∈ H → x ∈ H) {a g t : G} (ha2 : a * a = 1)
    (haH : Subgroup.centralizer ({a} : Set G) ≤ H) (hgH : g ∉ H) (hat : t = g * a * g⁻¹)
    (htS : t ∈ (S : Subgroup G))
    (hCS : ∀ x ∈ (S : Subgroup G), t * x = x * t → x ∈ conjSub g (S : Subgroup G)) : False := by
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  have hA : EtaAbelian Ω := etaAbelian_of_gen hΩ
  have c₁ := c.conj g
  obtain ⟨K', hK'tw, hne, R', hR', hR'K', hR'S⟩ := c.stand.twin
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  exact E187C.part1_core_of (g := g) (K' := K') (R' := R') hΩ.conjInvariant (c.sylow_le hA)
    (fun S₁ X hX Y hY hXS hYS hXY => Q3T8.Asc77.l6_7_proved G Ω hΩ S₁ X hX Y hY hXS hYS hXY)
    (fun hz₁ hR₁ hR₁K₁ hR₁S hβ hT hTS =>
      centralizes_conj_of_mem_RSet h hΩ hz₁ hR₁ hR₁K₁ hR₁S hβ hT hTS)
    (fun hw1 => c.centralizer_ne_top h hw1)
    (fun hK₁tw hne₁ hR₁' hR₁'K hR₁'S w hw1 hw2 hA2 hsup hXne =>
      c₁.centralizer_le_H' h4 hK₁tw hne₁ hR₁' hR₁'K (by rw [coe_conjSylow]; exact hR₁'S) hA2
        ⟨w, hw1, hw2, rfl⟩ hsup hXne)
    (Sec6Gen.isQuatSub_of_mem_RSet hΩ hRR) c.stand.mem hRR hRK hRS hK'tw hne hR' hR'K' hR'S hz hzW hP
    ha2 haH hgH hat htS hCS
    (fun s hs => c₁.stand.hW.2.2 s (by rw [coe_conjSylow]; exact hs))
    (by obtain ⟨η, -, -, -, habel, -⟩ := c₁.exists_eta hA; exact habel)
    (fun ht2 hnc => c.exists_delta h hz hzW ht2 htS hnc)

end

section
variable [PrintedQuotOdd] [PrintedQuotCent] [PrintedHull]

open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCexQ8.part1 (h : E18_6Q8) (h4 : E18_4CQ8)
    (c : MinCexQ8 Ω K S R W H) {z : G} (hz : IsUniqueInvolution K z) (hzW : z ∈ W)
    (hP : ∀ x : G, x * z * x⁻¹ ∈ H → x ∈ H) {a g : G} (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (haH : Subgroup.centralizer ({a} : Set G) ≤ H) (hgt : g * a * g⁻¹ ∈ H) :
    ∃ h' ∈ H, h' * a * h'⁻¹ = g * a * g⁻¹ := by
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  have hA : EtaAbelian Ω := etaAbelian_of_gen hΩ
  exact E187C.part1_of (c.sylow_le hA)
    (fun ha2 haH hgH hat htS hCS => c.part1_core h h4 hz hzW hP ha2 haH hgH hat htS hCS) ha2 ha1
    haH hgt

end

section
variable [PrintedQuotOdd] [PrintedQuotCent] [PrintedHull]

open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCexQ8.exists_config_sylow (c : MinCexQ8 Ω K S R W H)
    {K' R' X : Subgroup G} (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K) (hR' : R' ∈ RSet Ω)
    (hR'K' : R' ≤ K') (hR'S : R' ≤ (S : Subgroup G)) (hRX : R ⊔ R' ≤ X) :
    ∃ (S' : Sylow 2 G) (W' : Subgroup G), MinCexQ8 Ω K S' R W' H ∧ R ⊔ R' ≤ (S' : Subgroup G) ∧
      IsSylow2In ((S' : Subgroup G) ⊓ X) X := by
  have hΩ : HypOmegaGen Ω := c.stand.hyp
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
  have hRS' : R ≤ (S' : Subgroup G) := le_sup_left.trans (hRRP.trans hPS')
  have hR'S' : R' ≤ (S' : Subgroup G) := le_sup_right.trans (hRRP.trans hPS')
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ c.stand.mem
  obtain ⟨x, -, -, hW', hW'S', hW'n, hCW'⟩ := exists_W_of_sylow hΩ c.stand.mem c.hyp.trans hz
    (c.centralizer_le hz) hRR hRK hRS c.stand.hW.1 c.stand.hW.2.1 c.stand.hW.2.2 c.hyp.cent hRR
    hRK hRS'
  exact ⟨S', conjSub x W, c.of_sylow hRS' hK' hne hR' hR'K' hR'S' hW' hW'S' hW'n hCW',
    sup_le hRS' hR'S', hSyl⟩

theorem MinCexQ8.exists_config_sylow_centralizer (c : MinCexQ8 Ω K S R W H) {z : G}
    (hz : IsUniqueInvolution K z) :
    ∃ (S' : Sylow 2 G) (W' : Subgroup G), MinCexQ8 Ω K S' R W' H ∧
      IsSylow2In ((S' : Subgroup G) ⊓ Subgroup.centralizer ({z} : Set G))
        (Subgroup.centralizer ({z} : Set G)) := by
  have hΩ : HypOmegaGen Ω := c.stand.hyp
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

theorem MinCexQ8.rename (h : E18_6Q8) (c : MinCexQ8 Ω K S R W H)
    {K' R' K'' R'' : Subgroup G} (hK' : K' ∈ twinSet Ω K) (hR' : R' ∈ RSet Ω) (hR'K' : R' ≤ K')
    (hR'S : R' ≤ (S : Subgroup G)) (hK'' : K'' ∈ twinSet Ω K) (hne : K'' ≠ K')
    (hR'' : R'' ∈ RSet Ω) (hR''K'' : R'' ≤ K'') (hR''S : R'' ≤ (S : Subgroup G)) :
    MinCexQ8 Ω K' S R' W H := by
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  obtain ⟨hK'Ω, z', hz'K, hz'K'⟩ := hK'
  obtain ⟨hK''Ω, z'', hz''K, hz''K''⟩ := hK''
  have hz : z'' = z' := hz''K.eq hz'K
  have hK''tw : K'' ∈ twinSet Ω K' := ⟨hK''Ω, z', hz'K', hz ▸ hz''K''⟩
  have hK'S : K' ∈ dstarComp Ω K := mem_dstarComp_of_twin_gen hΩ c.stand.mem ⟨hK'Ω, z', hz'K, hz'K'⟩
  have hcomp : ∀ J ∈ dstarComp Ω K', J ∈ dstarComp Ω K := fun J hJ =>
    Relation.ReflTransGen.trans hK'S hJ
  obtain ⟨hWW, hWS, hWn⟩ := c.stand.hW
  have hh₂ := c.hyp.trans K' hK'S
  refine
    { stand :=
        { hyp := c.stand.hyp
          cls := c.stand.cls
          q8 := c.stand.q8
          two := c.stand.two
          ih := c.stand.ih
          mem := hK'Ω
          aEmpty := aEmpty_forall_of_transitive hΩ.conjInvariant
            (e18_3Q8 G Ω K S R W H c) c.stand.aEmpty K' hK'Ω
          twin := ⟨K'', hK''tw, hne, R'', hR'', hR''K'', hR''S⟩
          hR := ⟨hR', hR'K', hR'S⟩
          hW := ⟨hWW, hWS, hWn⟩ }
      hyp := ⟨fun J hJ => ?_, c.hyp.cent⟩
      proper := c.proper
      minimal := c.minimal }
  obtain ⟨h₁, hh₁H, hh₁⟩ := c.hyp.trans J (hcomp J hJ)
  obtain ⟨h₂, hh₂H, hh₂'⟩ := hh₂
  refine ⟨h₁ * h₂⁻¹, H.mul_mem hh₁H (H.inv_mem hh₂H), ?_⟩
  rw [conjSub_mul, ← hh₁, ← hh₂', conjSub_inv_conjSub]
end

section
variable [PrintedQuotOdd] [PrintedQuotCent] [PrintedHull]

open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem commutes_inf_S (h : E18_6Q8) (hΩ : HypOmegaGen Ω)
    {S : Sylow 2 G} {M₁ M₂ R₁ R₂ : Subgroup G} (hM₁ : M₁ ∈ Ω) (hM₂ : M₂ ∈ Ω) (hne : M₁ ≠ M₂)
    (hR₁ : R₁ ∈ RSet Ω) (hR₁M : R₁ ≤ M₁) (hR₁S : R₁ ≤ (S : Subgroup G)) (hR₂ : R₂ ∈ RSet Ω)
    (hR₂M : R₂ ≤ M₂) (hR₂S : R₂ ≤ (S : Subgroup G)) :
    Commutes (M₁ ⊓ (S : Subgroup G)) (M₂ ⊓ (S : Subgroup G)) := by
  rw [inf_S_eq_of_mem_RSet hΩ hM₁ hR₁ hR₁M hR₁S, inf_S_eq_of_mem_RSet hΩ hM₂ hR₂ hR₂M hR₂S]
  have hR₂2 : IsPGroup 2 R₁ := by
    obtain ⟨J, -, -, h2, -⟩ := mem_RSet_iff.mp hR₁
    exact h2
  have hRne : R₁ ≠ R₂ := by
    intro hR
    have := hΩ.card_le_two_of_le_inf hM₁ hM₂ hne hR₂2 hR₁M (hR ▸ hR₂M)
    have h8 := hΩ.eight_le_of_mem_RSet hR₁
    omega
  exact Q3T8.Asc77.l6_7_proved G Ω hΩ S R₁ hR₁ R₂ hR₂ hR₁S hR₂S hRne
end

section
variable [PrintedQuotOdd] [PrintedQuotCent] [PrintedHull]

open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCexQ8.exists_two_twins (h : E18_6Q8) (c : MinCexQ8 Ω K S R W H) {z g t : G}
    (hz : IsUniqueInvolution K z) (hzW : z ∈ W) (hzH : Subgroup.centralizer ({z} : Set G) ≤ H)
    (hSylz : IsSylow2In ((S : Subgroup G) ⊓ Subgroup.centralizer ({z} : Set G))
      (Subgroup.centralizer ({z} : Set G)))
    (hg : g ∉ H) (ht : t = g * z * g⁻¹) (htS : t ∈ (S : Subgroup G)) (hnc : ¬ t * z = z * t)
    {K' : Subgroup G} :
    ∃ (B : Subgroup G) (b : G) (g' : G), B ≤ (S : Subgroup G) ∧
      B ≤ Subgroup.centralizer ({t} : Set G) ∧ IsUniqueInvolution B b ∧ 8 ≤ Nat.card B ∧
      b = z * (t * z * t⁻¹) ∧ b ∈ W ∧ Subgroup.centralizer ({b} : Set G) ≤ H ∧
      t = g' * z * g'⁻¹ ∧ g' ∉ H ∧ (∀ β ∈ B, g'⁻¹ * β * g' ∈ (S : Subgroup G)) ∧
      ∃ β₃ ∈ B, ∃ β₄ ∈ B, conjSub (g'⁻¹ * β₃ * g') K ≠ conjSub (g'⁻¹ * β₄ * g') K ∧
        conjSub (g'⁻¹ * β₃ * g') K ≠ K ∧ conjSub (g'⁻¹ * β₃ * g') K ≠ K' ∧
        conjSub (g'⁻¹ * β₄ * g') K ≠ K ∧ conjSub (g'⁻¹ * β₄ * g') K ≠ K' := by
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  have hA : EtaAbelian Ω := etaAbelian_of_gen hΩ
  have hM : EtaMeet Ω := etaMeet_of_gen hΩ
  exact E187C.exists_two_twins_of hΩ.conjInvariant (fun hQ => hΩ.eight_le_of_mem_RSet hQ)
    (fun hg' => c.hbad_of_conj hA hM hz hg') c.stand.mem hz hzH hSylz hg ht htS hnc
    (fun ht2 hnc => c.exists_delta h hz hzW ht2 htS hnc)

end

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
