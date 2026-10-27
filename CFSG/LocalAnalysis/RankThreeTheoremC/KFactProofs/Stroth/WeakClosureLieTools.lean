module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureCases
public import CFSG.RankThree.PartOne.CTP.StrongPNoncentral
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureTools
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureVacuous
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerActionN1Common
import CFSG.LocalAnalysis.SectionRank.DerivedQuotient
import CFSG.LocalAnalysis.PreuniquenessRankFour.Helpers

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Open CFSG.RankThree.PartOne.StrongP

section Nonabelian

variable {K : Type} [Group K] [Finite K] {p : ℕ}

theorem WCOn.of_noncomm_pSubgroup [Fact p.Prime] {Q : Subgroup K} (hQ : IsPGroup p Q) {x y : K}
    (hx : x ∈ Q) (hy : y ∈ Q) (hxy : x * y ≠ y * x) : WCOn p K :=
  WCOn.of_not_isMulCommutative fun P =>
    InnerAction.not_isMulCommutative_of_noncomm_pSubgroup hQ hx hy hxy P.isPGroup' P.not_dvd_index

theorem WCOn.of_hom_noncomm [Fact p.Prime] {G : Type*} [Group G] (φ : G →* K) {Q : Subgroup G}
    (hQ : IsPGroup p Q) (hker : ∀ g ∈ Q, φ g = 1 → g = 1) {x y : G} (hx : x ∈ Q) (hy : y ∈ Q)
    (hxy : x * y ≠ y * x) : WCOn p K := by
  refine WCOn.of_noncomm_pSubgroup (Q := Q.map φ) (hQ.map φ) (x := φ x) (y := φ y)
    (Subgroup.mem_map_of_mem φ hx) (Subgroup.mem_map_of_mem φ hy) fun h => hxy ?_
  have h1 : φ (x * y * (y * x)⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [h]
    exact mul_inv_cancel _
  have h2 := hker _ (Q.mul_mem (Q.mul_mem hx hy) (Q.inv_mem (Q.mul_mem hy hx))) h1
  rwa [mul_inv_eq_one] at h2

theorem WCOn.of_pRank_top_le_one [Fact p.Prime] (h : CFSG.Open.pRank p (⊤ : Subgroup K) ≤ 1) :
    WCOn p K := by
  intro P _ hrank
  exfalso
  have := CFSG.PreuniquenessRankFour.Helpers.pRank_mono p Fact.out
    (le_top : (P : Subgroup K) ≤ ⊤)
  omega

end Nonabelian

section Projective

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F] {p : ℕ}

@[expose] def NonscalarPPair (p : ℕ) (H : Subgroup (GL ι F)) : Prop :=
  ∃ x y : GL ι F, x ∈ H ∧ y ∈ H ∧ IsPGroup p (Subgroup.closure ({x, y} : Set (GL ι F))) ∧
    (x * y)⁻¹ * (y * x) ∉ CFSG.Open.StatedScalars ι F

theorem NonscalarPPair.mono {H H' : Subgroup (GL ι F)} (hH : H ≤ H') (h : NonscalarPPair p H) :
    NonscalarPPair p H' := by
  obtain ⟨x, y, hx, hy, hP, hnc⟩ := h
  exact ⟨x, y, hH hx, hH hy, hP, hnc⟩

theorem NonscalarPPair.conj {H H' : Subgroup (GL ι F)} (P : GL ι F)
    (hH : ∀ g ∈ H, P * g * P⁻¹ ∈ H') (h : NonscalarPPair p H) : NonscalarPPair p H' := by
  obtain ⟨x, y, hx, hy, hP, hnc⟩ := h
  refine ⟨P * x * P⁻¹, P * y * P⁻¹, hH x hx, hH y hy, ?_, ?_⟩
  · have hmap : Subgroup.closure ({P * x * P⁻¹, P * y * P⁻¹} : Set (GL ι F)) =
        (Subgroup.closure ({x, y} : Set (GL ι F))).map (MulAut.conj P).toMonoidHom := by
      rw [MonoidHom.map_closure, Set.image_pair]; rfl
    rw [hmap]
    exact hP.map _
  · intro hs
    apply hnc
    have e : (P * x * P⁻¹ * (P * y * P⁻¹))⁻¹ * (P * y * P⁻¹ * (P * x * P⁻¹)) =
        P * ((x * y)⁻¹ * (y * x)) * P⁻¹ := by group
    rw [e] at hs
    have := (inferInstance : (CFSG.Open.StatedScalars ι F).Normal).conj_mem _ hs P⁻¹
    simpa [mul_assoc] using this

theorem NonscalarPPair.of_noncentralPair {H : Subgroup (GL ι F)} (h : NoncentralPair p H) :
    NonscalarPPair p H := by
  obtain ⟨x, y, hx, hy, -, -, hP, hnc⟩ := h
  exact ⟨x, y, hx, hy, hP, hnc⟩

theorem NonscalarPPair.of_unitri [Nonempty ι] [Fact p.Prime] [CharP F p] {H : Subgroup (GL ι F)}
    {r : ι → ℕ} {m : ℕ} (hr : ∀ i, r i < m) {x y : GL ι F} (hx : x ∈ H) (hy : y ∈ H)
    (hxu : IsUnitri r x) (hyu : IsUnitri r y) (hxy : x * y ≠ y * x) : NonscalarPPair p H := by
  refine ⟨x, y, hx, hy, ?_, ?_⟩
  · intro g
    obtain ⟨k, hk⟩ : ∃ k : ℕ, g.1 ^ (p ^ k) = 1 :=
      ⟨m, closure_pair_pow_eq_one p hr hxu hyu g.1 g.2⟩
    exact ⟨k, Subtype.ext hk⟩
  · intro hs
    obtain ⟨c, hc⟩ := hs
    have hxy_u : IsUnitri r (x * y) := hxu.mul hyu
    have hyx_u : IsUnitri r (y * x) := hyu.mul hxu
    have hscal : (y * x : GL ι F) = (x * y) * Matrix.GeneralLinearGroup.scalar ι c := by
      rw [hc]; group
    have hmat : ((y * x : GL ι F) : Matrix ι ι F) = (c : F) • ((x * y : GL ι F) : Matrix ι ι F) := by
      rw [hscal, Units.val_mul]
      ext i j
      simp [Matrix.GeneralLinearGroup.scalar, Matrix.mul_diagonal, mul_comm]
    obtain ⟨i⟩ := ‹Nonempty ι›
    have hd := congrFun (congrFun hmat i) i
    rw [hyx_u.diag i, Matrix.smul_apply, hxy_u.diag i, smul_eq_mul, mul_one] at hd
    have hc1 : (c : F) = 1 := hd.symm
    apply hxy
    have hc1' : c = 1 := Units.ext hc1
    rw [hc1'] at hscal
    have h2 : y * x = x * y := by simpa using hscal
    exact h2.symm

theorem NonscalarPPair.wcOn_statedProj [Fact p.Prime] [Finite F] {H : Subgroup (GL ι F)}
    (h : NonscalarPPair p H) : WCOn p (CFSG.Open.StatedProj H) := by
  obtain ⟨x, y, hx, hy, hP, hnc⟩ := h
  let π : H →* CFSG.Open.StatedProj H :=
    QuotientGroup.mk' ((CFSG.Open.StatedScalars ι F).subgroupOf H)
  let G : Subgroup H := Subgroup.closure ({⟨x, hx⟩, ⟨y, hy⟩} : Set H)
  have hmap1 : G.map H.subtype = Subgroup.closure ({x, y} : Set (GL ι F)) := by
    rw [MonoidHom.map_closure, Set.image_pair]; rfl
  have hG : IsPGroup p G := by
    intro g
    obtain ⟨k, hk⟩ := hP ⟨(g : H), by rw [← hmap1]; exact ⟨g, g.2, rfl⟩⟩
    refine ⟨k, Subtype.ext (H.subtype_injective ?_)⟩
    have := congrArg (fun z : Subgroup.closure ({x, y} : Set (GL ι F)) => (z : GL ι F)) hk
    simpa using this
  refine WCOn.of_noncomm_pSubgroup (Q := G.map π) (hG.map π) (x := π ⟨x, hx⟩) (y := π ⟨y, hy⟩)
    (Subgroup.mem_map_of_mem π (Subgroup.subset_closure (Set.mem_insert _ _)))
    (Subgroup.mem_map_of_mem π (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))) ?_
  intro hc
  apply hnc
  have h1 : π (⟨x, hx⟩ * ⟨y, hy⟩) = π (⟨y, hy⟩ * ⟨x, hx⟩) := by
    rw [map_mul, map_mul]; exact hc
  simp only [π, QuotientGroup.mk'_apply] at h1
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
  simpa using h1

theorem NonscalarPPair.wcOn [Fact p.Prime] [Finite F] {H : Subgroup (GL ι F)} {K : Type}
    [Group K] [Finite K] (e : K ≃* CFSG.Open.StatedProj H) (h : NonscalarPPair p H) :
    WCOn p K := by
  haveI : Finite (CFSG.Open.StatedProj H) := Finite.of_equiv K e.toEquiv
  exact WCOn.of_mulEquiv e h.wcOn_statedProj

end Projective

section Lines

variable {K : Type} [Group K] [Finite K] {p : ℕ}

@[expose] def NormalizerMovesLines (p : ℕ) {K : Type} [Group K] (P : Subgroup K) : Prop :=
  ∀ A : Subgroup K, A ≤ P → Nat.card A = p →
    ∃ n ∈ Subgroup.normalizer (P : Set K), A.map (MulAut.conj n).toMonoidHom ≠ A

theorem WCOn.of_normalizerMovesLines [Fact p.Prime] (P₀ : Sylow p K)
    (h : IsMulCommutative (P₀ : Subgroup K) → 2 ≤ CFSG.Open.pRank p (P₀ : Subgroup K) →
      NormalizerMovesLines p (P₀ : Subgroup K)) : WCOn p K := by
  refine WCOn.of_sylow P₀ fun hab hrank A hAP hA => ?_
  obtain ⟨n, hn, hne⟩ := h hab hrank A hAP hA
  refine ⟨n, ?_, hne⟩
  rintro _ ⟨a, ha, rfl⟩
  exact (Subgroup.mem_normalizer_iff.1 hn a).1 (hAP ha)

@[expose] def IrreducibleOnOmega1 (p : ℕ) {K : Type} [Group K] (P : Subgroup K) : Prop :=
  ∀ V : Subgroup K, V ≤ P → (∀ x ∈ V, x ^ p = 1) →
    (∀ n ∈ Subgroup.normalizer (P : Set K), V.map (MulAut.conj n).toMonoidHom = V) →
    V = ⊥ ∨ ∀ x ∈ P, x ^ p = 1 → x ∈ V

theorem NormalizerMovesLines.of_irreducibleOnOmega1 [Fact p.Prime] {P : Subgroup K}
    (hrank : 2 ≤ CFSG.Open.pRank p P) (h : IrreducibleOnOmega1 p P) :
    NormalizerMovesLines p P := by
  intro A hAP hA
  by_contra hcon
  push Not at hcon
  have hexp : ∀ x ∈ A, x ^ p = 1 := by
    intro x hx
    have := pow_card_eq_one' (G := A) (x := ⟨x, hx⟩)
    rw [hA] at this
    exact congrArg Subtype.val this
  rcases h A hAP hexp hcon with hbot | hall
  · rw [hbot, Subgroup.card_bot] at hA
    exact (Fact.out : p.Prime).one_lt.ne hA
  · obtain ⟨E, hEP, hE, hEcard⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank
      (p := p) (H := P) (k := 2) hrank
    have hEA : E ≤ A := fun x hx => hall x (hEP hx) (hE.2 x hx)
    have h1 : Nat.card E ≤ Nat.card A := Subgroup.card_le_of_le hEA
    rw [hEcard, hA] at h1
    have hp2 := (Fact.out : p.Prime).two_le
    nlinarith

end Lines

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
