module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXFam
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXUntw

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.DX

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.T263
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)


theorem modelSel_adjointGroup {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K = 2) (hK4 : 4 ≤ Nat.card K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K ^ 2 - 1) : ModelSel p ↥(adjointGroup τ K) := by
  intro r hrp hr1 P hPr hP2 hP1
  have hfix := CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup_conj r
  have hβp : (MulAut.conj r) ^ p = 1 := by rw [← map_pow, hrp, map_one]
  have hβ1 : MulAut.conj r ≠ 1 := by
    intro h
    refine hr1 (Subgroup.mem_bot.1 ?_)
    rw [← center_adjointGroup_eq_bot (τ := τ) (K := K), Subgroup.mem_center_iff]
    intro g
    have h1 := congrArg (fun f : MulAut ↥(adjointGroup τ K) => f g) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    rwa [mul_inv_eq_iff_eq_mul, eq_comm] at h1
  have hβmem : MulAut.conj r ∈ innAutDerived ↥(adjointGroup τ K) :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_le_innAutDerived _ ⟨r, rfl⟩
  have := exists_comp_of_two_adjointGroup hτ hK2 hK4 hp hp2 hpq (MulAut.conj r) hβmem hβp hβ1 P
    (hfix ▸ hPr) hP2 hP1
  rwa [hfix] at this

private theorem exists_modelSel_untw_cat {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {c : TauCeti.PrimePower → TauCeti.LieTypeIndex}
    (hB : CFSG.TauCetiBridge.Even.UntwistedBridgeAll τ c) (q : TauCeti.PrimePower)
    (hv : (c q).Valid) (hq2 : q.p = 2) (hq4 : 4 ≤ q.card) (hpq : p ∣ q.card ^ 2 - 1)
    {X : Type} [Group X] (e : X ≃* (TauCeti.CFSGIndex.lie ⟨c q, hv⟩).Group) :
    ∃ (T : Type) (_ : Group T) (_ : Finite T), Nonempty (X ≃* T) ∧ ModelSel p T := by
  obtain ⟨K, _, _, hK, hKc, ⟨φ⟩⟩ :=
    CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup hB q hv
  have hK2 : ringChar K = 2 := by rw [ringChar.eq K q.p, hq2]
  exact ⟨↥(adjointGroup τ K), inferInstance, inferInstance, ⟨e.trans φ⟩,
    modelSel_adjointGroup hτ hK2 (hK ▸ hq4) hp hp2 (hK ▸ hpq)⟩

theorem exists_modelSel_excEasy {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Type} [Group X]
    (h : catalogIs X (t263GExcEasy p)) :
    ∃ (T : Type) (_ : Group T) (_ : Finite T), Nonempty (X ≃* T) ∧ ModelSel p T := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d with
    | E7 q =>
      obtain ⟨hq2, hq4, hpq⟩ := hi
      exact exists_modelSel_untw_cat hp hp2 (by simp)
        CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 q hv hq2 hq4 hpq e
    | E8 q =>
      obtain ⟨hq2, hq4, hpq⟩ := hi
      exact exists_modelSel_untw_cat hp hp2 (by simp)
        CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 q hv hq2 hq4 hpq e
    | F4 q =>
      obtain ⟨hq2, hq4, hpq⟩ := hi
      exact exists_modelSel_untw_cat hp hp2 (by simp)
        CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 q hv hq2 hq4 hpq e
    | G2 q =>
      obtain ⟨hq2, hq4, hpq⟩ := hi
      exact exists_modelSel_untw_cat hp hp2 (by simp)
        CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv hq2 hq4 hpq e
    | _ => exact hi.elim
  | _ => exact hi.elim

end CFSG.LocalAnalysis.GLTheoremA.T263.DX
