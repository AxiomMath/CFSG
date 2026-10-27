module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualTypeBWEichler
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualLeviSingular
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualTypeBWFix
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualTypeBWLift

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Module Subgroup CFSG.Assembly.LowTwoRank
open CFSG.Quasithin (perfectCore)
open LinearPilot (autFixSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus regular_coordinateQuadPlus)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (isometryConjugationHom)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem fixSpace_le_compl (hn : 3 ≤ n) (hQ : ∃ v, coordinateQuadPlus n K v ≠ 0)
    (s : matrixIsometries (coordinateQuadPlus n K)) (hss : s * s = 1) (hq4 : 4 ≤ Nat.card K)
    (U C : Submodule K (Fin (2 * n) → K)) (hUW : U ≤ LinearMap.range (sNil s.val))
    (hQU : ∀ u ∈ U, coordinateQuadPlus n K u = 0) (hCK : C ≤ LinearMap.ker (sNil s.val))
    (hdisj : U ⊓ C = ⊥) (hsup : U ⊔ C = LinearMap.ker (sNil s.val)) (hU0 : U ≠ ⊥)
    {y₀ : Fin (2 * n) → K} (hy₀ : y₀ ∈ C) (hQy₀ : coordinateQuadPlus n K y₀ = 1)
    (htor : ∀ u ∈ U, u ≠ 0 → ∀ a : Kˣ,
      ∃ x ∈ perfectCore (autFixSubgroup (isometryConjugationHom _ s)),
        projLift hQ x u = (a : K) • u ∧ ∀ c ∈ C, projLift hQ x c = c)
    {v : Fin (2 * n) → K}
    (hv : ∀ x ∈ perfectCore (autFixSubgroup (isometryConjugationHom _ s)), projLift hQ x v = v) :
    v ∈ C := by
  have hNN : ∀ v, sNil s.val (sNil s.val v) = 0 := sNil_sNil (congrArg Subtype.val hss)
  by_cases hvW : v ∈ LinearMap.range (sNil s.val)
  · obtain ⟨u, c, hc, huc⟩ :=
      exists_decomp_of_mem_ker (sNil s.val) hsup (range_le_ker _ hNN hvW)
    by_cases hu0 : (u : Fin (2 * n) → K) = 0
    · rw [huc, hu0, zero_add]
      exact hc
    · exfalso
      obtain ⟨a, ha⟩ := exists_unit_ne_one (K := K) hq4
      obtain ⟨x, hx, hxu, hxc⟩ := htor u u.2 hu0 a
      have e := hv x hx
      rw [huc, map_add, hxu, hxc c hc] at e
      have h2 : ((a : K) - 1) • (u : Fin (2 * n) → K) = 0 := by
        rw [sub_smul, one_smul]
        exact sub_eq_zero.mpr (add_right_cancel e)
      rcases smul_eq_zero.mp h2 with h | h
      · exact ha (Units.ext (sub_eq_zero.mp h))
      · exact hu0 h
  · exfalso
    obtain ⟨r, hr, -, -, hrv⟩ :=
      exists_core_move hn hQ s hss hq4 U C hUW hQU hCK hdisj hsup hU0 hy₀ hQy₀ htor hvW
    apply hrv
    rw [hv r hr, sub_self]
    exact C.zero_mem

theorem mapsTo_wallSing_of_core (hn : 3 ≤ n) (hQ : ∃ v, coordinateQuadPlus n K v ≠ 0)
    (s : matrixIsometries (coordinateQuadPlus n K)) (hss : s * s = 1) (hq4 : 4 ≤ Nat.card K)
    (U C : Submodule K (Fin (2 * n) → K)) (hUW : U ≤ LinearMap.range (sNil s.val))
    (hQU : ∀ u ∈ U, coordinateQuadPlus n K u = 0) (hCK : C ≤ LinearMap.ker (sNil s.val))
    (hdisj : U ⊓ C = ⊥) (hsup : U ⊔ C = LinearMap.ker (sNil s.val)) (hU0 : U ≠ ⊥)
    {y₀ : Fin (2 * n) → K} (hy₀ : y₀ ∈ C) (hQy₀ : coordinateQuadPlus n K y₀ = 1)
    (htor : ∀ u ∈ U, u ≠ 0 → ∀ a : Kˣ,
      ∃ x ∈ perfectCore (autFixSubgroup (isometryConjugationHom _ s)),
        projLift hQ x u = (a : K) • u ∧ ∀ c ∈ C, projLift hQ x c = c)
    (W₀ : Submodule K (Fin (2 * n) → K))
    (hW₀ : ∀ v, v ∈ W₀ ↔ v ∈ LinearMap.range (sNil s.val) ∧ coordinateQuadPlus n K v = 0)
    (N₁ N₂ : Subgroup ↥(perfectCore (autFixSubgroup (isometryConjugationHom _ s))))
    [N₁.Normal] [N₂.Normal] (hR : IsPGroup 2 ↥(N₁ ⊓ N₂))
    (hN₁ : ∀ M : Subgroup ↥(perfectCore (autFixSubgroup (isometryConjugationHom _ s))),
      M.Normal → IsPGroup 2 M → M ≤ N₁)
    (hN₂ : ∀ M : Subgroup ↥(perfectCore (autFixSubgroup (isometryConjugationHom _ s))),
      M.Normal → IsPGroup 2 M → M ≤ N₂)
    (hN₁W : ∀ x : ↥(perfectCore (autFixSubgroup (isometryConjugationHom _ s))),
      (∀ w ∈ LinearMap.range (sNil s.val),
        projLift hQ (x : matrixProjectiveDerived (coordinateQuadPlus n K)) w = w) → x ∈ N₁)
    (hN₂K : ∀ x : ↥(perfectCore (autFixSubgroup (isometryConjugationHom _ s))),
      (∀ v ∈ LinearMap.ker (sNil s.val),
        projLift hQ (x : matrixProjectiveDerived (coordinateQuadPlus n K)) v - v ∈
          LinearMap.range (sNil s.val)) → x ∈ N₂)
    (hRW₀ : ∀ r ∈ N₁ ⊓ N₂, ∀ w ∈ W₀,
      ∀ x ∈ perfectCore (autFixSubgroup (isometryConjugationHom _ s)),
        projLift hQ x (projLift hQ ((r : ↥(perfectCore (autFixSubgroup
          (isometryConjugationHom _ s)))) : matrixProjectiveDerived (coordinateQuadPlus n K)) w -
            w) = projLift hQ ((r : ↥(perfectCore (autFixSubgroup
              (isometryConjugationHom _ s)))) : matrixProjectiveDerived (coordinateQuadPlus n K))
                w - w)
    (g : similarityPairs (coordinateQuadPlus n K))
    (hgX : ∀ x ∈ perfectCore (autFixSubgroup (isometryConjugationHom _ s)),
      matrixProjectiveConjugationHom _ g x ∈ perfectCore (autFixSubgroup
        (isometryConjugationHom _ s))) :
    ∀ w ∈ W₀, coordinateSemilinearMap g.val w ∈ W₀ := by
  intro w hw
  have hS : ∀ v, (∀ r ∈ N₁ ⊓ N₂ ⊓ ⊤,
      ∀ x ∈ perfectCore (autFixSubgroup (isometryConjugationHom _ s)),
        projLift hQ x (projLift hQ ((r : ↥(perfectCore (autFixSubgroup
          (isometryConjugationHom _ s)))) : matrixProjectiveDerived (coordinateQuadPlus n K)) v -
            v) = projLift hQ ((r : ↥(perfectCore (autFixSubgroup
              (isometryConjugationHom _ s)))) : matrixProjectiveDerived (coordinateQuadPlus n K))
                v - v) → v ∈ LinearMap.range (sNil s.val) := by
    intro v hv
    by_contra hvW
    obtain ⟨r, hr, hrW, hrK, hrv⟩ :=
      exists_core_move hn hQ s hss hq4 U C hUW hQU hCK hdisj hsup hU0 hy₀ hQy₀ htor hvW
    have hr₁ : (⟨r, hr⟩ : ↥(perfectCore (autFixSubgroup (isometryConjugationHom _ s)))) ∈ N₁ :=
      hN₁W _ hrW
    have hr₂ : (⟨r, hr⟩ : ↥(perfectCore (autFixSubgroup (isometryConjugationHom _ s)))) ∈ N₂ :=
      hN₂K _ hrK
    exact hrv (fixSpace_le_compl hn hQ s hss hq4 U C hUW hQU hCK hdisj hsup hU0 hy₀ hQy₀ htor
      (hv ⟨r, hr⟩ ⟨⟨hr₁, hr₂⟩, Subgroup.mem_top _⟩))
  have hN : ∀ N' ∈ ({N₁, N₂, ⊤} :
      Set (Subgroup ↥(perfectCore (autFixSubgroup (isometryConjugationHom _ s))))),
      ∀ M : Subgroup ↥(perfectCore (autFixSubgroup (isometryConjugationHom _ s))),
        M.Normal → IsPGroup 2 M → M ≤ N' := by
    intro N' hN' M hM hMp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hN'
    rcases hN' with rfl | rfl | rfl
    · exact hN₁ M hM hMp
    · exact hN₂ M hM hMp
    · exact le_top
  have hR' : IsPGroup 2 ↥(N₁ ⊓ N₂ ⊓ ⊤) := by rwa [inf_top_eq]
  have hRn : (N₁ ⊓ N₂ ⊓ ⊤).Normal := by
    rw [inf_top_eq]
    infer_instance
  have hwS := mapsTo_relFixSpace_of_core hQ g hgX N₁ N₂ ⊤ hN hR' hRn (v := w)
    fun r hr x hx => hRW₀ r (by rwa [inf_top_eq] at hr) w hw x hx
  rw [hW₀] at hw ⊢
  exact ⟨hS _ hwS, map_coordinateSemilinearMap_eq_zero g hw.2⟩

end CFSG.SeitzReduction.OmegaPilot
