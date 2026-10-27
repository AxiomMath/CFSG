module

public import CFSG.GH74.Generic.BProg.B3.S3Sec29C5
public import CFSG.GH74.GLS.C3.Layer1.Th2HYPump

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.Generic.S45
  CFSG.GH74.Generic.BProg CFSG.GH74.Generic.BProg.B3 CFSG.Blueprint CFSG.ABGLocalTools
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
  CFSG.GH74.GLS.C3.Layer1 CFSG.ComponentClassification
open scoped commutatorElement

namespace S3Sec29Cw

variable {G : Type} [Group G] [Finite G]

section Mu

variable {x y : G} {K A B Q D J : Subgroup G}

open C3.Layer1 in
theorem exists_Mu (h : Ctx29w G x K A B Q y y D J) {u : G} (hu : u ∈ Q) (hu2 : orderOf u = 2) :
    ∃ M Λ : Subgroup G, PumpUpLT 2 x K u M ∧ PumpCalc.IsLam x u K Λ ∧ x ∈ normalizer (M : Set G) ∧
      Nonempty (kBar M ≃* kBar K) ∧ PumpCalc.bar u Λ = PumpCalc.bar u M ∧ y ∈ Λ ∧ y ∈ M := by
  have hILo : IsILo 2 x K := h.circ.1.1.1
  have hterm : IsTwoTerminal x K := h.circ.1.2.2
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := h.circ.1.1.1.2.2
  have huC : u ∈ CxK x K := h.Q_syl.le hu
  have hR3 : ∀ w : G, orderOf w = 2 → 3 ≤ pRank 2 ↥(centralizer ({w} : Set G)) := by
    have h3 : 3 ≤ pRank 2 G := by
      rw [pRank_two_eq_twoRank]
      exact h.hyp.rank
    exact fun w hw => TwoThin.rankThreeCentralizers G h.hyp.simple h.hyp.nonab h3 w hw
  obtain ⟨M, hlt⟩ := PumpRigid.exists_pumpUpLT hILo hu2 huC (hR3 u hu2)
  obtain ⟨Λ, hΛ⟩ := PumpCalc.exists_isLam hu2 hK huC.2
  obtain ⟨hxM, ⟨e₁⟩⟩ := hterm.2.1 u M hlt
  have hMc : IsPCompIn 2 (centralizer ({u} : Set G)) M := hlt.2.1.2.2
  have hΛM : PumpCalc.bar u Λ ≤ PumpCalc.bar u M := PumpCalc.bar_le_of_stable hlt hΛ hxM
  have hΛeq : PumpCalc.bar u Λ = PumpCalc.bar u M := Th2.HY.bar_lam_eq hΛ hMc hΛM e₁
  have hyK : y ∈ K := (Subgroup.mem_inf.1 h.y_mem).2
  have hyΛ : y ∈ Λ := by
    refine hΛ.twoElt y (Subgroup.mem_inf.2 ⟨hyK, ?_⟩) ⟨1, ?_⟩
    · exact Subgroup.mem_centralizer_singleton_iff.2 (y_comm_Q h hu).symm
    · have := pow_orderOf_eq_one y
      rw [h.y_ord] at this
      simpa using this
  refine ⟨M, Λ, hlt, hΛ, hxM, ⟨e₁⟩, hΛeq, hyΛ, ?_⟩
  have hyC : y ∈ centralizer ({u} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 (y_comm_Q h hu).symm
  have hmem : TwoThin.barMk ↥(centralizer ({u} : Set G)) ⟨y, hyC⟩ ∈
      (M.subgroupOf (centralizer ({u} : Set G))).map (TwoThin.barMk ↥(centralizer ({u} : Set G))) := by
    have h1 : TwoThin.barMk ↥(centralizer ({u} : Set G)) ⟨y, hyC⟩ ∈ PumpCalc.bar u Λ :=
      ⟨⟨y, hyC⟩, Subgroup.mem_subgroupOf.2 hyΛ, rfl⟩
    rw [hΛeq] at h1
    exact h1
  have hy2 : (⟨y, hyC⟩ : ↥(centralizer ({u} : Set G))) ^ (2 ^ 1) = 1 := by
    apply Subtype.ext
    have := pow_orderOf_eq_one y
    rw [h.y_ord] at this
    simpa using this
  exact Subgroup.mem_subgroupOf.1 (mem_of_two_pow_eq_one_of_map_mem
    hMc.2 hy2 hmem)

end Mu

end S3Sec29Cw

end CFSG.GH74.Generic.BProg.B3
