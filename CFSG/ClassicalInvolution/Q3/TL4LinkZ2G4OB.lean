module

public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2G4OA
public import CFSG.ClassicalInvolution.RouteD.ExoticSingleWitt
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofOrthGeom
public import CFSG.ClassicalInvolution.Asc77.AscT8X4
public import CFSG.ClassicalInvolution.Asc77.AscT8YA3
public import CFSG.ClassicalInvolution.AschTight.S1916F2a
public import CFSG.ClassicalInvolution.AschTight.S19BCSW
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.InnerOvergroup
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520Core
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Reduction
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm1RTwin
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm7RCore
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPair
public import CFSG.ClassicalInvolution.Q3.Q3AMDBStmt
public import CFSG.ClassicalInvolution.Q3.Q3T6BSymEx
public import CFSG.ClassicalInvolution.Q3.Q3T6DCfg
public import CFSG.ClassicalInvolution.Q3.Q3T6DPart1
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenSDEnd
public import CFSG.ClassicalInvolution.Q3.Q3T8B10
public import CFSG.ClassicalInvolution.Q3.Q3T8P26T01
public import CFSG.ClassicalInvolution.Q3.Q3T8P26T02
public import CFSG.ClassicalInvolution.Q3.Q3T8P26TH01
public import CFSG.ClassicalInvolution.Q3.Q3TIYOAMain
public import CFSG.ClassicalInvolution.Q3.TL3S8Gold
public import CFSG.ClassicalInvolution.Q3.TL3S8Sd
public import CFSG.ClassicalInvolution.Q3.TL4Conn26Ex
public import CFSG.ClassicalInvolution.Q3.TL4Conn26GAl
public import CFSG.ClassicalInvolution.Q3.TL4Conn274M
public import CFSG.ClassicalInvolution.Q3.TL4E3S3
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM1RC
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM3
public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2G4Red
public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2L2DefsB
public import CFSG.ClassicalInvolution.Q3.TL4OddConv
public import CFSG.ClassicalInvolution.Q3.TL4OddFrThird
public import CFSG.ClassicalInvolution.Q3.TL4OddMu4
public import CFSG.ClassicalInvolution.Q3.TL4SepSub
public import CFSG.ClassicalInvolution.Q3.TL4VtxFree
public import CFSG.ClassicalInvolution.SmallCases.NobqFinal
public import CFSG.Foundations
public import CFSG.Goldschmidt.Steps.G310Core2
public import CFSG.Goldschmidt.Steps.G37Core
public import CFSG.Goldschmidt75.TheoremB
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingCore
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingEscape
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingInherit
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingOddQuotient
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingThreeOne
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.Permutation.BurnsideSchur
public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedScalar
public import CFSG.Timmesfeld.Moufang.Three

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Z2W.G4

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.RankThree.Classical2
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3.TL4.OrthQ8 CFSG.ClassicalInvolution.Q3.TL4.E3S3O.OM3 QuadraticMap
open scoped MatrixGroups

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {S : Type} [Group S]

theorem exists_mem_eq_one' [Finite K] [FiniteDimensional K V] (hK : Nat.card K = 3)
    {P : Submodule K V} (hP : PolarNondegOn Q P) (h2 : 2 ≤ Module.finrank K P) :
    ∃ v ∈ P, Q v = 1 := by
  have hodd : Odd (Nat.card K) := by rw [hK]; decide
  have : Invertible (2 : K) := invertibleOfNonzero (OrthQ8.two_ne_zero' hK)
  obtain ⟨v, hv, hQv⟩ := CFSG.ClassicalInvolution.ModelFacts.exists_mem_eq_unit hodd
    (QuadraticMap.nondegenerate_polar_iff.mp (nondegenerate_polarBilin_restrict hP)) h2 1
  exact ⟨v, hv, by rwa [Units.val_one] at hQv⟩

theorem exists_regular_orth' [FiniteDimensional K V] (h2 : (2 : K) ≠ 0) {P : Submodule K V}
    (hP : PolarNondegOn Q P) {v : V} (hvP : v ∈ P) (hv : Q v ≠ 0) :
    ∃ P' : Submodule K V, (∀ x, x ∈ P' ↔ x ∈ P ∧ polar Q v x = 0) ∧ PolarNondegOn Q P' ∧
      Module.finrank K P ≤ Module.finrank K P' + 1 := by
  have hvv : polar Q v v = 2 * Q v := by rw [polar_self_eq_two_mul]
  have hvv0 : polar Q v v ≠ 0 := by rw [hvv]; exact mul_ne_zero h2 hv
  let φ : P →ₗ[K] K := (polarBilin Q v).domRestrict P
  let P' : Submodule K V := (LinearMap.ker φ).map P.subtype
  have hmem : ∀ x, x ∈ P' ↔ x ∈ P ∧ polar Q v x = 0 := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hx, hx'⟩
      exact ⟨⟨x, hx⟩, hx', rfl⟩
  refine ⟨P', hmem, ?_, ?_⟩
  · intro x hx hxy
    have hxP := ((hmem x).mp hx).1
    have hxv : polar Q v x = 0 := ((hmem x).mp hx).2
    apply hP x hxP
    intro y hy
    have hy' : y - (polar Q y v / polar Q v v) • v ∈ P' := by
      rw [hmem]
      refine ⟨P.sub_mem hy (P.smul_mem _ hvP), ?_⟩
      rw [polar_sub_right, polar_smul_right_eq, polar_comm Q v y]
      field_simp
      ring
    have h1 := hxy _ hy'
    have h3 : y = (y - (polar Q y v / polar Q v v) • v) + (polar Q y v / polar Q v v) • v := by
      abel
    rw [h3, polar_add_right, h1, polar_smul_right_eq, polar_comm Q x v, hxv]
    ring
  · have hr := LinearMap.finrank_range_add_finrank_ker φ
    have h1 : Module.finrank K (LinearMap.range φ) ≤ 1 := by
      calc Module.finrank K (LinearMap.range φ) ≤ Module.finrank K K := Submodule.finrank_le _
        _ = 1 := Module.finrank_self K
    have h4 : Module.finrank K P' = Module.finrank K (LinearMap.ker φ) :=
      LinearEquiv.finrank_eq
        ((LinearMap.ker φ).equivMapOfInjective P.subtype P.injective_subtype).symm
    omega

section Anti

variable {g : V ≃ₗ[K] V}

theorem polar_anti (hgQ : ∀ v, Q (g v) = -1 * Q v) (u v : V) :
    polar Q (g u) (g v) = -polar Q u v := by
  rw [polar, polar, ← map_add, hgQ, hgQ, hgQ]
  ring

theorem polar_self_anti (h2 : (2 : K) ≠ 0) (hgQ : ∀ v, Q (g v) = -1 * Q v)
    (hg2 : ∀ v, g (g v) = v) (v : V) : polar Q v (g v) = 0 := by
  have h1 := polar_anti hgQ v (g v)
  rw [hg2, polar_comm] at h1
  exact (mul_eq_zero.mp (show (2 : K) * polar Q v (g v) = 0 by linear_combination h1)).resolve_left
    h2

noncomputable def antiPair [Finite K] (hK : Nat.card K = 3) (hgQ : ∀ v, Q (g v) = -1 * Q v)
    (hg2 : ∀ v, g (g v) = v) {v : V} (hv : Q v = 1) : HypPair Q where
  e := v + g v
  f := v - g v
  Q_e := by
    rw [QuadraticMap.map_add Q v (g v), hgQ, hv, polar_self_anti (OrthQ8.two_ne_zero' hK) hgQ hg2]
    ring
  Q_f := by
    rw [sub_eq_add_neg, QuadraticMap.map_add Q v (-g v), QuadraticMap.map_neg, hgQ, hv,
      polar_neg_right,
      polar_self_anti (OrthQ8.two_ne_zero' hK) hgQ hg2]
    ring
  polar_ef := by
    have h3 := OrthQ8.three_eq_zero hK
    rw [polar_add_left, polar_sub_right, polar_sub_right, polar_self_eq_two_mul,
      polar_self_eq_two_mul, hgQ, hv, polar_self_anti (OrthQ8.two_ne_zero' hK) hgQ hg2,
      polar_comm Q (g v) v, polar_self_anti (OrthQ8.two_ne_zero' hK) hgQ hg2]
    linear_combination h3

theorem exists_two_pairs_perp [Finite K] [FiniteDimensional K V] (hK : Nat.card K = 3)
    (hQ : (polarBilin Q).Nondegenerate) {F : Frame Q} (hn : 8 ≤ Module.finrank K V)
    (hgQ : ∀ v, Q (g v) = -1 * Q v) (hg2 : ∀ v, g (g v) = v)
    (hgF : ∀ v ∈ F.perp, g v ∈ F.perp) :
    ∃ P₁ P₂ : HypPair Q, P₁.Orth P₂ ∧ (P₁.e ∈ F.perp ∧ P₁.f ∈ F.perp) ∧
      (P₂.e ∈ F.perp ∧ P₂.f ∈ F.perp) := by
  have h2 : (2 : K) ≠ 0 := OrthQ8.two_ne_zero' hK
  have hPn : PolarNondegOn Q F.perp := CFSG.ClassicalInvolution.ModelFacts.polarNondegOn_perp hQ F
  have hdim := CFSG.ClassicalInvolution.ModelFacts.finrank_perp_add_four F
  obtain ⟨v, hvP, hQv⟩ := exists_mem_eq_one' hK hPn (by omega)
  obtain ⟨P₁', hP₁, hP₁n, hP₁d⟩ := exists_regular_orth' h2 hPn hvP (by rw [hQv]; exact one_ne_zero)
  have hgv : Q (g v) ≠ 0 := by
    rw [hgQ, hQv, mul_one]
    exact neg_ne_zero.mpr one_ne_zero
  obtain ⟨P₂', hP₂, hP₂n, hP₂d⟩ :=
    exists_regular_orth' h2 hP₁n ((hP₁ _).mpr ⟨hgF v hvP, polar_self_anti h2 hgQ hg2 v⟩) hgv
  obtain ⟨w, hwP₂, hQw⟩ := exists_mem_eq_one' hK hP₂n (by omega)
  obtain ⟨hwP₁, hw₁⟩ := (hP₂ w).mp hwP₂
  obtain ⟨hwP, hw₀⟩ := (hP₁ w).mp hwP₁
  have o1 : polar Q v w = 0 := hw₀
  have o2 : polar Q (g v) w = 0 := hw₁
  have o3 : polar Q v (g w) = 0 := by
    have h1 := polar_anti hgQ (g v) w
    rw [hg2, o2, neg_zero] at h1
    exact h1
  have o4 : polar Q (g v) (g w) = 0 := by rw [polar_anti hgQ, o1, neg_zero]
  refine ⟨antiPair hK hgQ hg2 hQv, antiPair hK hgQ hg2 hQw, ⟨?_, ?_, ?_, ?_⟩,
    ⟨F.perp.add_mem hvP (hgF v hvP), F.perp.sub_mem hvP (hgF v hvP)⟩,
    ⟨F.perp.add_mem hwP (hgF w hwP), F.perp.sub_mem hwP (hgF w hwP)⟩⟩
  · show polar Q (v + g v) (w + g w) = 0
    rw [polar_add_left, polar_add_right, polar_add_right, o1, o2, o3, o4]
    ring
  · show polar Q (v + g v) (w - g w) = 0
    rw [polar_add_left, polar_sub_right, polar_sub_right, o1, o2, o3, o4]
    ring
  · show polar Q (v - g v) (w + g w) = 0
    rw [polar_sub_left, polar_add_right, polar_add_right, o1, o2, o3, o4]
    ring
  · show polar Q (v - g v) (w - g w) = 0
    rw [polar_sub_left, polar_sub_right, polar_sub_right, o1, o2, o3, o4]
    ring

end Anti

theorem orth_of_mem_perp (F : Frame Q) {P : HypPair Q} (he : P.e ∈ F.perp) (hf : P.f ∈ F.perp) :
    F.P.Orth P ∧ F.P'.Orth P := by
  obtain ⟨a1, a2, a3, a4⟩ :=
    (CFSG.ClassicalInvolution.RouteD.Exotic.mem_perp_iff_four F).mp he
  obtain ⟨b1, b2, b3, b4⟩ :=
    (CFSG.ClassicalInvolution.RouteD.Exotic.mem_perp_iff_four F).mp hf
  exact ⟨⟨by rw [polar_comm]; exact a1, by rw [polar_comm]; exact b1, by rw [polar_comm]; exact a2,
    by rw [polar_comm]; exact b2⟩, ⟨by rw [polar_comm]; exact a3, by rw [polar_comm]; exact b3,
    by rw [polar_comm]; exact a4, by rw [polar_comm]; exact b4⟩⟩

theorem four_pairs_of_orth {P₀ P₁ P₂ P₃ : HypPair Q} (h01 : P₀.Orth P₁) (h02 : P₀.Orth P₂)
    (h03 : P₀.Orth P₃) (h12 : P₁.Orth P₂) (h13 : P₁.Orth P₃) (h23 : P₂.Orth P₃) :
    ∀ i j : Fin 4, i ≠ j → (![P₀, P₁, P₂, P₃] i).Orth (![P₀, P₁, P₂, P₃] j) := by
  have s : ∀ {A B : HypPair Q}, A.Orth B → B.Orth A := fun h =>
    ⟨by rw [polar_comm]; exact h.ee, by rw [polar_comm]; exact h.fe,
      by rw [polar_comm]; exact h.ef, by rw [polar_comm]; exact h.ff⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> first
    | exact absurd rfl hij
    | assumption
    | exact s ‹_›
    | simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.cons_val_succ, Matrix.tail_cons]
      first | assumption | exact s ‹_›

theorem false_of_sPHyp_induced' [Finite K] [FiniteDimensional K V] (hK : Nat.card K = 3)
    (hQ : (polarBilin Q).Nondegenerate) (hn : 7 ≤ Module.finrank K V)
    (htype : Odd (Module.finrank K V) ∨ (8 ≤ Module.finrank K V ∧
      ∀ P : Fin 4 → HypPair Q, (∀ i j, i ≠ j → (P i).Orth (P j)) → False))
    {θ : ↥(orthDerived Q) →* S} (hθ : Function.Surjective θ)
    (hker : θ.ker = (scalars K V).subgroupOf (orthDerived Q))
    {A B : Subgroup S} {r : S} {x : MulAut S} (h : SPHyp A B r x) {g : V ≃ₗ[K] V}
    (hx : InducedBy θ g x) {μ c : K} (hμ0 : μ ≠ 0) (hμ : ∀ v, Q (g v) = μ * Q v)
    (hc : ∀ v, g (g v) = c • v) : False := by
  obtain ⟨F, hAF, -⟩ := exists_frame_of_quatTwinDatum hK hQ hn θ hθ hker h.quat
  subst hAF
  have h2 := two_ne_zero' hK
  obtain ⟨q, hq, hqB⟩ := h.twin
  rcases twin_cases hK hQ hn θ hθ hker h.quat rfl hq (hqB ▸ h.ne) with hswap | ⟨F', hF', hneg⟩
  · rw [hqB] at hswap
    obtain ⟨hμ1, hc1⟩ := mu_eq_neg_one_of_swap hK hQ (by omega) hker hx h.fixA
      (hswap ▸ h.normB) (hswap ▸ h.cB) hμ0 hμ hc
    rw [hμ1] at hμ
    rcases htype with hodd | ⟨h8, hW⟩
    · exact false_of_odd_of_neg hK hQ hμ hodd
    · have hFg := commute_La_of_fix hK hQ (by omega) hker hx h.fixA
      have hg2 : ∀ v, g (g v) = v := fun v => by rw [hc, hc1, one_smul]
      have hgF : ∀ v ∈ F.perp, g v ∈ F.perp := fun v hv =>
        Frame.map_mem_perp h2 (hFg (-1) (neg_one_mem_commutator hK)) hv
      obtain ⟨P₁, P₂, h12, ⟨h1e, h1f⟩, ⟨h2e, h2f⟩⟩ := exists_two_pairs_perp hK hQ h8 hμ hg2 hgF
      obtain ⟨a1, b1⟩ := orth_of_mem_perp F h1e h1f
      obtain ⟨a2, b2⟩ := orth_of_mem_perp F h2e h2f
      exact hW _ (four_pairs_of_orth F.orth a1 a2 b1 b2 h12)
  · have h8 := finrank_eq_eight_of_neg h2 hneg
    rcases htype with hodd | ⟨-, hW⟩
    · rw [h8] at hodd
      exact absurd hodd (by decide)
    · have hle : F'.span ≤ F.perp := (span_eq_perp_of_neg h2 hneg).le
      obtain ⟨o1, o2, o3, o4⟩ :=
        CFSG.ClassicalInvolution.RouteD.Exotic.orth_pairs_of_span_le_perp hle
      exact hW _ (four_pairs_of_orth F.orth o1 o2 o3 o4 F'.orth)

theorem false_of_sPHyp_orth' [Finite K] [FiniteDimensional K V] (hK : Nat.card K = 3)
    (hQ : (polarBilin Q).Nondegenerate) (hn : 7 ≤ Module.finrank K V)
    (htype : Odd (Module.finrank K V) ∨ (8 ≤ Module.finrank K V ∧
      ∀ P : Fin 4 → HypPair Q, (∀ i j, i ≠ j → (P i).Orth (P j)) → False))
    {θ : ↥(orthDerived Q) →* S} (hθ : Function.Surjective θ)
    (hker : θ.ker = (scalars K V).subgroupOf (orthDerived Q))
    {A B : Subgroup S} {r : S} {x : MulAut S} (h : SPHyp A B r x) : False := by
  obtain ⟨β, g, μ, hμ0, hμ, hg, ⟨c, hc⟩, hact⟩ :=
    E3S3O.exists_similarity_of_involutive hK hQ hn θ hθ hker x h.sq
  exact false_of_sPHyp_induced' hK hQ hn htype hθ hker (h.map β) ⟨hg, hact⟩ hμ0 hμ hc

end CFSG.ClassicalInvolution.Q3.TL4.Z2W.G4
