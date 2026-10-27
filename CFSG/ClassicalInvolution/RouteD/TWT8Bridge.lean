module

public import CFSG.ClassicalInvolution.RouteD.TWT8Spin
public import CFSG.ClassicalInvolution.RouteD.TWEB6Layer
public import CFSG.ClassicalInvolution.RouteD.TwinYStatements
public import CFSG.ClassicalInvolution.RouteD.TypeDLocal
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedDLocal
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.RouteD.TWT8

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.TWE.B6
open CFSG.LieType.Universal.Spin
open CFSG.ClassicalInvolution.Generic (Commutes)

set_option linter.unusedSectionVars false

section Group

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.ClassicalInvolution.RouteD.TwinY

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {u : G}


theorem exists_bridge_members_typed (hp2 : p ≠ 2) (hΩ : InClass p f Ω) (hex : ExactMembers Ω)
    (hP1 : LocalOddCentral Ω {u}) {t : StatedLieTag} {n : ℕ} (hG2 : t ≠ .G2)
    (hD4 : t ≠ .trialityD4) (hshape : LocalShapeT p f 0 t n Ω u) (hY : YData p f t n)
    (hF : OrthFacts (fundamentalSubgroups t (modelUniv t n p f Fact.out).D) (GaloisField p f))
    (hperf : ∀ R ∈ fundamentalSubgroups t (modelUniv t n p f Fact.out).D, ⁅R, R⁆ = R)
    (hpair : ∀ {R₀ R₁ : Subgroup (modelUniv t n p f Fact.out).K},
      R₀ ∈ fundamentalSubgroups t (modelUniv t n p f Fact.out).D →
      R₁ ∈ fundamentalSubgroups t (modelUniv t n p f Fact.out).D →
      ModelAdj (Subgroup.center (modelUniv t n p f Fact.out).K) R₀ R₁ →
      (∃ W, LinearBlockStandardPair (GaloisField p f) W R₀ R₁) →
      ∃ T₁ ∈ fundamentalSubgroups t (modelUniv t n p f Fact.out).D,
        ∃ T₂ ∈ fundamentalSubgroups t (modelUniv t n p f Fact.out).D,
          Commutes T₁ R₀ ∧ Commutes T₁ R₁ ∧ Commutes T₂ R₀ ∧ Commutes T₂ R₁ ∧ T₁ ≠ T₂ ∧
          ¬ Commutes T₁ T₂ ∧ ∀ r, InvOf T₂ r → ∀ y ∈ T₁, r * y * r⁻¹ ∈ T₁)
    {K β : Subgroup G} {z s : G}
    (hK : K ∈ centralizingMembers Ω {u}) (hβ : β ∈ centralizingMembers Ω {u})
    (hz : IsClassicalMember p f K z) (hs : IsClassicalMember p f β s)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β) :
    ∃ N₁ ∈ centralizingMembers Ω {u}, ∃ N₂ ∈ centralizingMembers Ω {u},
      Commutes K N₁ ∧ Commutes β N₁ ∧ Commutes K N₂ ∧ Commutes β N₂ ∧ ¬ Commutes N₁ N₂ ∧
      N₁ ≠ N₂ ∧ ∃ n₂, IsClassicalMember p f N₂ n₂ ∧ conjSub n₂ N₁ = N₁ := by
  classical
  obtain ⟨e⟩ := Layer0.of_shape hΩ hex hG2 hD4 hshape
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  obtain ⟨R₀, hR₀, hKR⟩ := e.mem K hK
  obtain ⟨R₁, hR₁, hβR⟩ := e.mem β hβ
  obtain ⟨W, hW⟩ := hKβ
  have hadjR : ModelAdj (Subgroup.center (modelUniv t n p f Fact.out).K) R₀ R₁ :=
    e.modelAdj hY hΩ hP1 hK hβ hR₀ hR₁ hKR hβR hz hs (ne_of_linearBlockStandardPair hW)
      (not_commutes_of_linearBlockStandardPair hW)
      (standardPair_involutions_commute h2 hW hz.mem hs.mem hz.orderOf_eq_two hs.orderOf_eq_two)
      (conjSub_eq_of_standardPair h2 hW hs.mem hs.orderOf_eq_two)
  obtain ⟨W', hW'⟩ := e.pair_to_model hF hP1 hK hβ hR₀ hR₁ hKR hβR hW
  obtain ⟨T₁, hT₁, T₂, hT₂, c10, c11, c20, c21, hne, hnc, hnorm⟩ :=
    hpair hR₀ hR₁ hadjR ⟨W', hW'⟩
  obtain ⟨N₁, hN₁, hN₁T⟩ := e.comp T₁ hT₁
  obtain ⟨N₂, hN₂, hN₂T⟩ := e.comp T₂ hT₂
  obtain ⟨n₂, hn₂⟩ := hΩ.classical N₂ hN₂.1
  have hwx : n₂ ∈ locLayer Ω u := le_centralizingLayer hN₂ hn₂.mem
  obtain ⟨r, hr, hrφ⟩ := e.exists_involution hY hN₂ hT₂ hN₂T hn₂
  have hrr : r⁻¹ = r := by
    refine inv_eq_of_mul_eq_one_right ?_
    have := pow_orderOf_eq_one r
    rwa [hr.2, pow_two] at this
  have hT₁r : T₁.map (MulAut.conj r).toMonoidHom = T₁ := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact hnorm r hr y hy
    · intro y hy
      refine ⟨r⁻¹ * y * r, ?_, ?_⟩
      · have := hnorm r hr y hy
        rw [hrr] at this ⊢
        exact this
      · show r * (r⁻¹ * y * r) * r⁻¹ = y
        group
  have hcomp : (MulAut.conj (e.φ r)).toMonoidHom.comp e.φ =
      e.φ.comp (MulAut.conj r).toMonoidHom := by
    ext y
    simp [MulAut.conj_apply, map_mul, map_inv]
  have hnu : n₂ * u * n₂⁻¹ = u := by
    have := Subgroup.mem_centralizer_singleton_iff.mp (hN₂.2 hn₂.mem)
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  have hmemc : conjSub n₂ N₁ ∈ centralizingMembers Ω {u} := by
    have := centralizingMembers_conj hΩ.conjInvariant n₂ u
    rw [hnu] at this
    rw [this]
    exact ⟨N₁, hN₁, rfl⟩
  have key : locImg Ω u (conjSub n₂ N₁) = locImg Ω u N₁ := by
    rw [locImg_conjSub_layer (Ω := Ω) (x := u) N₁ ⟨n₂, hwx⟩, hN₁T, Subgroup.map_map]
    have hφr : locMk Ω u ⟨n₂, hwx⟩ = e.φ r := hrφ.symm
    rw [hφr, hcomp, ← Subgroup.map_map, hT₁r]
  refine ⟨N₁, hN₁, N₂, hN₂, ?_, ?_, ?_, ?_, ?_, ?_, n₂, hn₂, locImg_injOn hΩ hP1 hmemc hN₁ key⟩
  · exact commutes_symm ((e.commutes_iff hY hΩ hP1 hN₁ hK hT₁ hN₁T hKR).mpr c10)
  · exact commutes_symm ((e.commutes_iff hY hΩ hP1 hN₁ hβ hT₁ hN₁T hβR).mpr c11)
  · exact commutes_symm ((e.commutes_iff hY hΩ hP1 hN₂ hK hT₂ hN₂T hKR).mpr c20)
  · exact commutes_symm ((e.commutes_iff hY hΩ hP1 hN₂ hβ hT₂ hN₂T hβR).mpr c21)
  · exact fun h => hnc ((e.commutes_iff hY hΩ hP1 hN₁ hN₂ hT₁ hN₁T hN₂T).mp h)
  · intro h
    exact hne (CFSG.ClassicalInvolution.ModelFacts.eq_of_map_eq_of_isPerfect e.φ e.ker_le
      (hperf T₁ hT₁) (hperf T₂ hT₂) (by rw [← hN₁T, ← hN₂T, h]))

theorem twinYModel_minus_five_of_mod (h : p ^ f % 4 = 1) :
    twinYModel (p ^ f) .POmegaMinus 5 = (.POmegaMinus, 6) := by
  simp [twinYModel, h]

theorem twinYModel_minus_five_of_ne (h : ¬ p ^ f % 4 = 1) :
    twinYModel (p ^ f) .POmegaMinus 5 = (.POmegaPlus, 6) := by
  simp [twinYModel, h]

theorem exists_bridge_members_td5 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) (hP1 : LocalOddCentral Ω {u})
    (hshape : LocalShapeT p f 0 (twinYModel (p ^ f) .POmegaMinus 5).1
      (twinYModel (p ^ f) .POmegaMinus 5).2 Ω u) {K β : Subgroup G} {z s : G}
    (hK : K ∈ centralizingMembers Ω {u}) (hβ : β ∈ centralizingMembers Ω {u})
    (hz : IsClassicalMember p f K z) (hs : IsClassicalMember p f β s)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β) :
    ∃ N₁ ∈ centralizingMembers Ω {u}, ∃ N₂ ∈ centralizingMembers Ω {u},
      Commutes K N₁ ∧ Commutes β N₁ ∧ Commutes K N₂ ∧ Commutes β N₂ ∧ ¬ Commutes N₁ N₂ ∧
      N₁ ≠ N₂ ∧ ∃ n₂, IsClassicalMember p f N₂ n₂ ∧ conjSub n₂ N₁ = N₁ := by
  classical
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · subst h
      simp at hq
    · exact h
  have : Invertible (2 : GaloisField p f) :=
    invertibleOfNonzero (CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2)
  by_cases h4 : p ^ f % 4 = 1
  · rw [twinYModel_minus_five_of_mod h4] at hshape
    have hadm : StatedLieAdmissible .POmegaMinus 6 p f := ⟨Fact.out, hf1, by norm_num⟩
    have cq := Exotic.centralQuot_minus hp2 hq hadm
    exact exists_bridge_members_typed (t := .POmegaMinus) (n := 6) hp2 hΩ hex hP1 (by decide)
      (by decide) hshape (yData_minus (by norm_num) hp2 hadm (by omega))
      (orthFacts_minus (m := 6) hp2 (by norm_num) hq) (fun R hR => cq.perf R hR)
      (fun h0 h1 hadj hlin => exists_bridge_spin_minus hp2 hq h0 h1 hadj hlin) hK hβ hz hs hKβ
  · rw [twinYModel_minus_five_of_ne h4] at hshape
    have hadm : StatedLieAdmissible .POmegaPlus 6 p f := ⟨Fact.out, hf1, by norm_num⟩
    have cq := centralQuot_plus (m := 6) hp2 (by norm_num) (by norm_num) hq
    exact exists_bridge_members_typed (t := .POmegaPlus) (n := 6) hp2 hΩ hex hP1 (by decide)
      (by decide) hshape (yData_plus (by norm_num) hadm (by omega))
      (orthFacts_plus (m := 6) hp2 (by norm_num) hq) (fun R hR => cq.perf R hR)
      (fun h0 h1 hadj hlin => exists_bridge_spin_plus hp2 hq h0 h1 hadj hlin) hK hβ hz hs hKβ

end Group

end CFSG.ClassicalInvolution.RouteD.TWT8
