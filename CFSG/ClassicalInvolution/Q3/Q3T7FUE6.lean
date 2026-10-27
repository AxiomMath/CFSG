module

public import CFSG.ClassicalInvolution.Q3.Q3T7FUE5
public import CFSG.ClassicalInvolution.Asc77.AscE187P1d
public import CFSG.ClassicalInvolution.Asc77.AscE187B2f

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.T7FU

variable {MT : CFSG.ClassicalInvolution.Uniform.MemberType}
open CFSG.ClassicalInvolution.Q3.Q3T7M (omegaNbr_subset_kPerp_of_twin mem_kPerp_of_twin
  omegaStarDiff_subset_of_twin l6_3 le_of_sq_mem_of_oddGen odd_mem_of_mem_sup_central
      oddGen_conjSub)
open CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
    (HypOmegaMod L6_2 l6_2 L6_7 l6_7_proved L6_10 l6_10_proved
  L6_11 l6_11_proved L6_9 l6_9_proved)

section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCex.part1_core (h : E187Hyps) (h6 : E18_6At MT G) (h4 : E187E4CAt MT G)
    (c : MinCex MT Ω K S R W H) {z : G} (hz : IsUniqueInvolution K z) (hzW : z ∈ W)
    (hP : ∀ x : G, x * z * x⁻¹ ∈ H → x ∈ H) {a g t : G} (ha2 : a * a = 1)
    (haH : Subgroup.centralizer ({a} : Set G) ≤ H) (hgH : g ∉ H) (hat : t = g * a * g⁻¹)
    (htS : t ∈ (S : Subgroup G))
    (hCS : ∀ x ∈ (S : Subgroup G), t * x = x * t → x ∈ conjSub g (S : Subgroup G)) : False := by
  have hΩ : HM MT Ω := c.stand.hyp
  have hA : EtaAbelian Ω := h.etaAbelian hΩ
  have c₁ := c.conj g
  obtain ⟨K', hK'tw, hne, R', hR', hR'K', hR'S⟩ := c.stand.twin
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  exact E187C.part1_core_of (g := g) (K' := K') (R' := R') hΩ.conjInvariant (c.sylow_le hA)
    (fun S₁ X hX Y hY hXS hYS hXY => h.l67 G Ω hΩ S₁ X hX Y hY hXS hYS hXY)
    (fun hz₁ hR₁ hR₁K₁ hR₁S hβ hT hTS =>
      centralizes_conj_of_mem_RSet h hΩ hz₁ hR₁ hR₁K₁ hR₁S hβ hT hTS)
    (fun hw1 => c.centralizer_ne_top h6 hw1)
    (fun hK₁tw hne₁ hR₁' hR₁'K hR₁'S w hw1 hw2 hA2 hsup hXne =>
      c₁.centralizer_le_H h4 hK₁tw hne₁ hR₁' hR₁'K (by rw [coe_conjSylow]; exact hR₁'S) hA2
        ⟨w, hw1, hw2, rfl⟩ hsup hXne)
    (hΩ.isQuatSub_of_mem_RSet hRR) c.stand.mem hRR hRK hRS hK'tw hne hR' hR'K' hR'S hz hzW hP
    ha2 haH hgH hat htS hCS
    (fun s hs => c₁.stand.hW.2.2 s (by rw [coe_conjSylow]; exact hs))
    (by obtain ⟨η, -, -, -, habel, -⟩ := c₁.exists_eta hA; exact habel)
    (fun ht2 hnc => c.exists_delta h hz hzW ht2 htS hnc)

end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCex.part1 (h : E187Hyps) (h6 : E18_6At MT G) (h4 : E187E4CAt MT G)
    (c : MinCex MT Ω K S R W H) {z : G} (hz : IsUniqueInvolution K z) (hzW : z ∈ W)
    (hP : ∀ x : G, x * z * x⁻¹ ∈ H → x ∈ H) {a g : G} (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (haH : Subgroup.centralizer ({a} : Set G) ≤ H) (hgt : g * a * g⁻¹ ∈ H) :
    ∃ h' ∈ H, h' * a * h'⁻¹ = g * a * g⁻¹ := by
  have hΩ : HM MT Ω := c.stand.hyp
  have hA : EtaAbelian Ω := h.etaAbelian hΩ
  exact E187C.part1_of (c.sylow_le hA)
    (fun ha2 haH hgH hat htS hCS => c.part1_core h h6 h4 hz hzW hP ha2 haH hgH hat htS hCS) ha2 ha1
    haH hgt

end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCex.rename (h : E187Hyps) (c : MinCex MT Ω K S R W H)
    {K' R' K'' R'' : Subgroup G} (hK' : K' ∈ twinSet Ω K) (hR' : R' ∈ RSet Ω) (hR'K' : R' ≤ K')
    (hR'S : R' ≤ (S : Subgroup G)) (hK'' : K'' ∈ twinSet Ω K) (hne : K'' ≠ K')
    (hR'' : R'' ∈ RSet Ω) (hR''K'' : R'' ≤ K'') (hR''S : R'' ≤ (S : Subgroup G)) :
    MinCex MT Ω K' S R' W H := by
  have hΩ : HM MT Ω := c.stand.hyp
  obtain ⟨hK'Ω, z', hz'K, hz'K'⟩ := hK'
  obtain ⟨hK''Ω, z'', hz''K, hz''K''⟩ := hK''
  have hz : z'' = z' := hz''K.eq hz'K
  have hK''tw : K'' ∈ twinSet Ω K' := ⟨hK''Ω, z', hz'K', hz ▸ hz''K''⟩
  have hK'S : K' ∈ dstarComp Ω K := mem_dstarComp_of_twin hΩ c.stand.mem ⟨hK'Ω, z', hz'K, hz'K'⟩
  have hcomp : ∀ J ∈ dstarComp Ω K', J ∈ dstarComp Ω K := fun J hJ =>
    Relation.ReflTransGen.trans hK'S hJ
  obtain ⟨hWW, hWS, hWn⟩ := c.stand.hW
  have hcent' : CentralizersSylowPairs Ω K' H := c.hyp.cent.of_twin ⟨hK'Ω, z', hz'K, hz'K'⟩
  have hh₂ := c.hyp.trans K' hK'S
  refine
    { stand :=
        { hyp := c.stand.hyp
          mem := hK'Ω
          aEmpty := aEmpty_forall_of_transitive hΩ.conjInvariant
            (e18_3 h.l67 G Ω K S R W H c) c.stand.aEmpty K' hK'Ω
          twin := ⟨K'', hK''tw, hne, R'', hR'', hR''K'', hR''S⟩
          hR := ⟨hR', hR'K', hR'S⟩
          hW := ⟨hWW, hWS, hWn⟩ }
      hyp := ⟨fun J hJ => ?_, hcent'⟩
      proper := c.proper }
  obtain ⟨h₁, hh₁H, hh₁⟩ := c.hyp.trans J (hcomp J hJ)
  obtain ⟨h₂, hh₂H, hh₂'⟩ := hh₂
  refine ⟨h₁ * h₂⁻¹, H.mul_mem hh₁H (H.inv_mem hh₂H), ?_⟩
  rw [conjSub_mul, ← hh₁, ← hh₂', conjSub_inv_conjSub]

end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem commutes_inf_S (h : E187Hyps) (hΩ : HM MT Ω)
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
  exact h.l67 G Ω hΩ S R₁ hR₁ R₂ hR₂ hR₁S hR₂S hRne

end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCex.exists_two_twins (h : E187Hyps) (c : MinCex MT Ω K S R W H) {z g t : G}
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
  have hΩ : HM MT Ω := c.stand.hyp
  have hA : EtaAbelian Ω := h.etaAbelian hΩ
  have hM : EtaMeet Ω := h.etaMeet hΩ
  exact E187C.exists_two_twins_of hΩ.conjInvariant (fun hQ => hΩ.eight_le_of_mem_RSet hQ)
    (fun hg' => c.hbad_of_conj hA hM hz hg') c.stand.mem hz hzH hSylz hg ht htS hnc
    (fun ht2 hnc => c.exists_delta h hz hzW ht2 htS hnc)

end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCex.goodFour_of_noncommute (h : E187Hyps) (h6 : E18_6At MT G) (h4 : E187E4CAt MT G)
    (c : MinCex MT Ω K S R W H) {z g t : G} (hz : IsUniqueInvolution K z) (hzW : z ∈ W)
    (hzH : Subgroup.centralizer ({z} : Set G) ≤ H)
    (hSylz : IsSylow2In ((S : Subgroup G) ⊓ Subgroup.centralizer ({z} : Set G))
      (Subgroup.centralizer ({z} : Set G)))
    (hg : g ∉ H) (ht : t = g * z * g⁻¹) (htS : t ∈ (S : Subgroup G)) (hnc : ¬ t * z = z * t) :
    GoodFour H t := by
  classical
  have hΩ : HM MT Ω := c.stand.hyp
  have hA : EtaAbelian Ω := h.etaAbelian hΩ
  have hM : EtaMeet Ω := h.etaMeet hΩ
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  obtain ⟨-, hWS, hWn⟩ := c.stand.hW
  obtain ⟨K', hK'tw, hne, R', hR', hR'K', hR'S⟩ := c.stand.twin
  obtain ⟨d₁, d₂, h₁, h₂, h₃, h₄, -, -⟩ := E187C.goodFour_of_noncommute_of (K' := K') (R' := R') (z := z) (g := g) (t := t) hΩ.conjInvariant
    (fun M₁ M₂ R₁ R₂ hM₁ hM₂ hne hR₁ hR₁M hR₁S hR₂ hR₂M hR₂S =>
      commutes_inf_S h hΩ hM₁ hM₂ hne hR₁ hR₁M hR₁S hR₂ hR₂M hR₂S)
    (fun hM' hR₀ hR₀M hR₀S => by
      obtain ⟨-, u, hu, hu4⟩ := c.exists_order_four_of_inf_W hA hM hM' hR₀ hR₀M hR₀S
      exact ⟨u, hu, hu4⟩)
    (inf_S_eq_of_mem_RSet hΩ c.stand.mem hRR hRK hRS) (hΩ.isQuatSub_of_mem_RSet hRR)
    (fun hx1 => c.centralizer_ne_top h6 hx1)
    (fun hK₃tw hK₄tw hne43 hR₃ hR₃K hR₃S hR₄ hR₄K hR₄S hK₄tw' x hx1 hx2 hA2 hsup hXne =>
      (c.rename h hK₃tw hR₃ hR₃K hR₃S hK₄tw hne43 hR₄ hR₄K hR₄S).centralizer_le_H h4 hK₄tw'
        hne43 hR₄ hR₄K hR₄S hA2 ⟨x, hx1, hx2, rfl⟩ hsup hXne)
    c.stand.mem hRR hRK hRS hWS hWn hK'tw hne hR' hR'K' hR'S hz ht htS hnc
    (c.exists_two_twins h hz hzW hzH hSylz hg ht htS hnc (K' := K'))
  exact ⟨d₁, d₂, h₁, h₂, h₃, h₄⟩

end Asc77
end
end CFSG.ClassicalInvolution.T7FU
