module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154LinCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Open CFSG.Assembly CFSG.LieType.SemisimpleCentralizers.Held
open CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup exists_glaPComponent_map_fixSubgroup)
open scoped commutatorElement MatrixGroups

theorem exists_linPsl {K : Type} [Field K] [Finite K] (h2 : (2 : K) = 0) {d : ℕ} (hd : 1 ≤ d)
    (A : GL (Fin d) K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (u : MulAut (LargeEvenProj (StatedSL d K)))
    (hu : ∀ h h' : ↥(StatedSL d K), (h' : GL (Fin d) K) = A * (h : GL (Fin d) K) * A⁻¹ →
      u (LargeEvenProjMk (StatedSL d K) h) = LargeEvenProjMk (StatedSL d K) h')
    (hpow : u ^ p = 1)
    (J : Subgroup (LargeEvenProj (StatedSL d K)))
    (hJ : GLAPComponent p (fixSubgroup u) J) :
    ∃ (d₁ : ℕ) (D₁ : Type) (_ : Field D₁) (_ : Finite D₁) (ι : GL (Fin d₁) D₁ →* GL (Fin d) K)
      (ιSL : ↥(StatedSL d₁ D₁) →* ↥(StatedSL d K)),
      (2 : D₁) = 0 ∧ 2 ≤ d₁ ∧ (d₁ ≠ 2 ∨ Nat.card D₁ ≠ 2) ∧ (d₁ ≠ 2 ∨ Nat.card D₁ ≠ 3) ∧
      Function.Injective ι ∧ (∀ m : ↥(StatedSL d₁ D₁), (ιSL m : GL (Fin d) K) = ι (m : GL (Fin d₁) D₁)) ∧
      J = ιSL.range.map (LargeEvenProjMk (StatedSL d K)) ∧
      ∃ E : Matrix (Fin d) (Fin d) K, E ≠ 0 ∧ ∀ c : K, ∃ t ∈ StatedSL d₁ D₁,
        ((ι t : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 + c • E := by
  obtain ⟨c, hc⟩ := isScalar_of_pow_trivial h2 A p u hu hpow
  have hodd : Odd (orderOf A) := odd_orderOf_of_pow_scalar h2 hd A (hp.odd_of_ne_two hp2) hc
  have hord : ((orderOf A : ℕ) : K) ≠ 0 := cast_orderOf_ne_zero_of_odd h2 A hodd
  obtain ⟨M, hM, hMJ⟩ := exists_glaPComponent_map_fixSubgroup (LargeEvenProjMk (StatedSL d K))
    ker_projMk_le_center (conjSL A) u (fun k => (hu k (conjSL A k) rfl).symm)
    (QuotientGroup.mk_surjective) hp hJ
  have hMinj : Function.Injective (StatedSL d K).subtype := Subtype.val_injective
  have hM' : GLAPComponent p (Subgroup.centralizer ({A} : Set (GL (Fin d) K)) ⊓ CFSG.Open.StatedSL d K)
      (M.map (StatedSL d K).subtype) := by
    rw [← map_fixSubgroup_conjSL A]
    exact (CFSG.LocalAnalysis.GLTheoremA.Y10F.glaPComponent_map_iff hp hMinj).mpr hM
  obtain ⟨d₁, D₁, hF, hFin, ι, h2', hd₁, h22, h23, hιinj, hMι, E, hE, hT⟩ := exists_linComp h2 A hord hM'
  have hrange : ∀ m : ↥(StatedSL d₁ D₁), ι (m : GL (Fin d₁) D₁) ∈ StatedSL d K := by
    intro m
    have hm : ι (m : GL (Fin d₁) D₁) ∈ M.map (StatedSL d K).subtype := by
      rw [hMι]
      exact Subgroup.mem_map_of_mem ι m.2
    obtain ⟨x, -, hx⟩ := Subgroup.mem_map.1 hm
    rw [← hx]
    exact x.2
  let ιSL : ↥(StatedSL d₁ D₁) →* ↥(StatedSL d K) :=
    MonoidHom.codRestrict (ι.comp (StatedSL d₁ D₁).subtype) (StatedSL d K) hrange
  have hιSL : ∀ m : ↥(StatedSL d₁ D₁), (ιSL m : GL (Fin d) K) = ι (m : GL (Fin d₁) D₁) := fun m => rfl
  have hRange : ιSL.range = M := by
    ext x
    constructor
    · rintro ⟨m, rfl⟩
      have hm : (ιSL m : GL (Fin d) K) ∈ M.map (StatedSL d K).subtype := by
        rw [hMι, hιSL]
        exact Subgroup.mem_map_of_mem ι m.2
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hm
      have : y = ιSL m := Subtype.ext hyx
      rw [← this]
      exact hy
    · intro hx
      have hx' : (x : GL (Fin d) K) ∈ (StatedSL d₁ D₁).map ι := by
        rw [← hMι]
        exact Subgroup.mem_map_of_mem _ hx
      obtain ⟨m, hm, hmx⟩ := Subgroup.mem_map.1 hx'
      exact ⟨⟨m, hm⟩, Subtype.ext (by rw [hιSL]; exact hmx)⟩
  exact ⟨d₁, D₁, hF, hFin, ι, ιSL, h2', hd₁, h22, h23, hιinj, hιSL, by rw [hRange, hMJ], E, hE, hT⟩

end CFSG.LocalAnalysis.GLTheoremA.K155X
