module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitO2Phi
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitO2W
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitO2E8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitTight
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf9Lie
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitE4Conn

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Uniform

namespace TwinDisc

namespace ExitU

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem members (hS : Q8Section X Φ) (htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L)
    {K : Subgroup X} (hK : K ∈ Φ) {z : X} (hz : IsUniqueInvolution K z)
    (hodd : oddCoreImg (Subgroup.centralizer ({z} : Set X)) = ⊥) :
    ∀ J ∈ Φ, IsPGroup 2 J ∧ Nonempty (↥J ≃* QuaternionGroup 2) := by
  intro J hJ
  obtain ⟨g, rfl⟩ := htrans K hK J hJ
  have h2K : IsPGroup 2 K := isPGroup_of_oddCent hS.hyp hK hz hodd (hS.two K hK)
  have h2J : IsPGroup 2 (conjSub g K) := h2K.map (MulAut.conj g).toMonoidHom
  refine ⟨h2J, ?_⟩
  have hKS : IsSylow2In (conjSub g K) (conjSub g K) :=
    ⟨le_rfl, h2J, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
  exact hS.q8 _ hJ _ hKS

theorem q8Fam_of_q8Section (hS : Q8Section X Φ)
    (htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L) {K : Subgroup X} (hK : K ∈ Φ) {z : X}
    (hz : IsUniqueInvolution K z) (hodd : oddCoreImg (Subgroup.centralizer ({z} : Set X)) = ⊥)
    (hO2 : TightInO2 z) : ExitO2.Q8Fam X Φ where
  hyp := hS.hyp
  two := fun J hJ => (members hS htrans hK hz hodd J hJ).1
  q8 := fun J hJ => (members hS htrans hK hz hodd J hJ).2
  aEmpty := hS.aEmpty
  gen := by
    have := hS.gen
    unfold omegaGen at this
    exact this
  trans := htrans
  oddFree := hS.oddFree
  inO2 := by
    intro L hL u hu
    obtain ⟨g, rfl⟩ := htrans K hK L hL
    obtain ⟨P, hPn, hP2, hzP⟩ := hO2
    refine ⟨P, hPn, hP2, ?_⟩
    have hgu : g * z * g⁻¹ = u := (hz.conj g).eq hu
    rw [← hgu]
    exact hPn.conj_mem z hzP g

theorem exitSec_dstarConnected (hmodel : ExitE4.E4ModelDStar) (hS : Q8Section X Φ)
    (htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L)
    (hedge : ∃ M ∈ Φ, ∃ N : Subgroup X, N ∈ omegaNbr Φ M) {K : Subgroup X} (hK : K ∈ Φ)
    {z : X} (hz : IsUniqueInvolution K z)
    (hodd : oddCoreImg (Subgroup.centralizer ({z} : Set X)) = ⊥) (hno : ¬ TightInO2 z)
    {W : Subgroup X} (hKW : K ≤ W) (hWs : IsSubnormal W ⊤)
    (hex : Thm4Twin.F2.ExitSec W K hKW z hz) : T3.DStarConnected Φ := by
  have hmem := members hS htrans hK hz hodd
  have h2 : ∀ J ∈ Φ, IsPGroup 2 J := fun J hJ => (hmem J hJ).1
  have hq8 : ∀ J ∈ Φ, Nonempty (↥J ≃* QuaternionGroup 2) := fun J hJ => (hmem J hJ).2
  rcases hex with hE | ⟨S, hnoW, hex⟩
  · exact ExitE4.dstarConnected_of_twinE4 hmodel hS.hyp h2 hq8 hS.gen htrans hK hz hno hKW hWs hE
  · have hWtop : W = ⊤ := ExitE4.eq_top_of_subnormal hS.gen htrans hK hWs rfl hKW
    have hΦ : Φ = CoreAssembly.conjClass K := by
      ext J
      constructor
      · intro hJ
        exact htrans K hK J hJ
      · rintro ⟨g, rfl⟩
        exact hS.hyp.conjInvariant g K hK
    have hedge' : ¬ TightEdgeless (K.subgroupOf W) := by
      subst hWtop
      obtain ⟨K₀, hK₀, J, hJ⟩ := hedge
      have h2R : IsPGroup 2 ↥(K.subgroupOf (⊤ : Subgroup X)) := (h2 K hK).comap_subtype
      unfold TightEdgeless
      rw [tightCore_eq_self_of_isPGroup h2R]
      exact ExitE4.not_dEdgeless_top (h2 K hK) hΦ hK₀ hJ
    rcases hex with h | ⟨h, -⟩ | ⟨h, -⟩ | h
    · exact absurd h hnoW
    · exact absurd h hedge'
    · exact absurd h hedge'
    · exact ExitE4.dstarConnected_of_twinE4 hmodel hS.hyp h2 hq8 hS.gen htrans hK hz hno hKW hWs
        (TightE4.twinE4 h)

theorem ae5_of_o2 {n : ℕ} (hD : TC.Thin.ThmDAbsBelow 3 n) (hlt : Nat.card X < n)
    (hS : Q8Section X Φ) (htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L)
    {K : Subgroup X} (hK : K ∈ Φ) {z : X} (hz : IsUniqueInvolution K z)
    (hodd : oddCoreImg (Subgroup.centralizer ({z} : Set X)) = ⊥) (hO2 : TightInO2 z)
    (hdisc : ¬ T3.DStarConnected Φ) : Nonempty (TC.Thin.AEIdent Φ 5) := by
  have F := q8Fam_of_q8Section hS htrans hK hz hodd hO2
  rcases F.thmDConcl hD hlt with h1 | ⟨W, hW⟩ | ⟨E, hE⟩ | I64 | ⟨m, hm, ⟨I⟩⟩ | I29
  · exact absurd (fun K₁ hK₁ J hJ => by
      rw [h1 K₁ hK₁ J hJ]; exact Relation.ReflTransGen.refl) hdisc
  · exact absurd (ExitO2.fam_dstarConnected_of_wSet F hW) hdisc
  · exact absurd (ExitO2.fam_dstarConnected_of_e8 F hE) hdisc
  · obtain ⟨I⟩ := I64
    exact absurd (ExitO2.fam_dstarConnected_of_e64 F I) hdisc
  · rcases Nat.lt_or_ge m 6 with h6 | h6
    · obtain rfl : m = 5 := by omega
      exact ⟨I⟩
    · exact absurd (ExitO2.fam_dstarConnected_of_aeIdent F h6 I) hdisc
  · obtain ⟨I⟩ := I29
    exact absurd (ExitO2.fam_dstarConnected_of_e29 F I) hdisc

theorem noExit_or_ae5 {n : ℕ} (hmodel : ExitE4.E4ModelDStar) (hD : TC.Thin.ThmDAbsBelow 3 n)
    (hlt : Nat.card X < n) (hS : Q8Section X Φ)
    (htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L)
    (hedge : ∃ M ∈ Φ, ∃ N : Subgroup X, N ∈ omegaNbr Φ M)
    (hodd : ∀ K ∈ Φ, ∀ z : X, IsUniqueInvolution K z →
      oddCoreImg (Subgroup.centralizer ({z} : Set X)) = ⊥)
    (hdisc : ¬ T3.DStarConnected Φ) :
    NoExit X Φ ∨ ((∃ K ∈ Φ, ∃ z : X, IsUniqueInvolution K z ∧ TightInO2 z) ∧
      Nonempty (TC.Thin.AEIdent Φ 5)) := by
  by_cases hO2 : ∃ K ∈ Φ, ∃ z : X, IsUniqueInvolution K z ∧ TightInO2 z
  · obtain ⟨K, hK, z, hz, hO⟩ := hO2
    exact Or.inr ⟨⟨K, hK, z, hz, hO⟩, ae5_of_o2 hD hlt hS htrans hK hz (hodd K hK z hz) hO hdisc⟩
  · left
    push Not at hO2
    intro K hK z hz
    refine ⟨hodd K hK z hz, hO2 K hK z hz, ?_⟩
    intro W hKW hWs _ hex
    exact hdisc (exitSec_dstarConnected hmodel hS htrans hedge hK hz (hodd K hK z hz)
      (hO2 K hK z hz) hKW hWs hex)

end ExitU

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
