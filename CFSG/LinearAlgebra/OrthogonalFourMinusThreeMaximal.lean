module

public import CFSG.LinearAlgebra.OrthogonalFourMinusThreeDeleted
public import CFSG.RankThree.Classical.OddQuadraticFrame

noncomputable section
public section
open TauCeti
open QuadraticMap
namespace CFSG.LinearAlgebra.OrthogonalFourMinusThree

open CFSG

set_option linter.style.haveILetI false

def diagW : Fin 4 → ZMod 3 := fun i => if i = 3 then 2 else 1

def diagMinusForm : QuadraticForm (ZMod 3) (Fin 4 → ZMod 3) :=
  QuadraticMap.weightedSumSquares (ZMod 3) diagW

private lemma zmod3_cases (x : ZMod 3) : x = 0 ∨ x = 1 ∨ x = 2 := by
  revert x
  decide

private lemma diagAll_has_isotropic_plane :
    ∃ W : Submodule (ZMod 3) (Fin 4 → ZMod 3),
      Module.finrank (ZMod 3) W = 2 ∧
        ∀ x ∈ W, QuadraticMap.weightedSumSquares (ZMod 3) (fun _ => (1 : ZMod 3)) x = 0 := by
  let u : Fin 4 → ZMod 3 := ![1, 1, 1, 0]
  let v : Fin 4 → ZMod 3 := ![1, 2, 0, 1]
  have hli : LinearIndependent (ZMod 3) ![u, v] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h2 := congrArg (fun x : Fin 4 → ZMod 3 => x 2) hst
    have h3 := congrArg (fun x : Fin 4 → ZMod 3 => x 3) hst
    simp [u, v] at h2 h3
    exact ⟨h2, h3⟩
  let W : Submodule (ZMod 3) (Fin 4 → ZMod 3) :=
    Submodule.span (ZMod 3) {u, v}
  refine ⟨W, ?_, ?_⟩
  · have hspan : Submodule.span (ZMod 3) {u, v} =
        Submodule.span (ZMod 3) (Set.range ![u, v]) := by
      congr 1
      ext x
      simp [or_comm]
    rw [show W = Submodule.span (ZMod 3) {u, v} from rfl, hspan,
      finrank_span_eq_card hli, Fintype.card_fin]
  · intro x hx
    rw [show W = Submodule.span (ZMod 3) {u, v} from rfl] at hx
    rcases (Submodule.mem_span_pair.mp hx) with ⟨a, c, hac⟩
    rw [← hac]
    rcases zmod3_cases a with rfl | rfl | rfl <;>
      rcases zmod3_cases c with rfl | rfl | rfl <;>
      decide

lemma exists_isometry_diagMinus_of_minus
    {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : Module.finrank (ZMod 3) V = 4)
    (hminus : ¬ ∃ U : Submodule (ZMod 3) V,
      Module.finrank (ZMod 3) U = 2 ∧ ∀ u ∈ U, Q u = 0) :
    Nonempty (Q.IsometryEquiv diagMinusForm) := by
  have hK : Odd (Nat.card (ZMod 3)) := by
    rw [Nat.card_zmod]
    decide
  obtain ⟨b, hborth, hbnorm, hblast⟩ :=
    CFSG.RankThree.Classical.exists_orthogonal_basis_quad_eq (K := ZMod 3) (V := V)
      hK (d := Module.finrank (ZMod 3) V) rfl (by omega) Q hQ (a := 1) one_ne_zero
  haveI : Invertible (2 : ZMod 3) := invertibleOfNonzero (by decide)
  have hborth' : (QuadraticMap.associated Q).IsOrthoᵢ b := by
    rw [LinearMap.isOrthoᵢ_def]
    intro i j hij
    change (QuadraticMap.associated Q) (b i) (b j) = 0
    rw [QuadraticMap.associated_apply (S := ZMod 3), QuadraticMap.map_add Q (b i) (b j),
      hborth i j hij]
    simp
  let w : Fin (Module.finrank (ZMod 3) V) → ZMod 3 := fun i => Q (b i)
  let he : Q.IsometryEquiv (QuadraticMap.weightedSumSquares (ZMod 3) w) :=
    QuadraticForm.isometryEquivWeightedSumSquares Q b hborth'
  let idx : Fin 4 ≃ Fin (Module.finrank (ZMod 3) V) := finCongr hd.symm
  let w4 : Fin 4 → ZMod 3 := w ∘ idx
  have he4 : Q.IsometryEquiv (QuadraticMap.weightedSumSquares (ZMod 3) w4) :=
    he.trans (QuadraticForm.isometryEquivWeightedSumSquaresReindex w idx)
  have hidx0 : idx 0 = ⟨0, by omega⟩ := by
    ext
    simp [idx, finCongr]
  have hidx1 : idx 1 = ⟨1, by omega⟩ := by
    ext
    simp [idx, finCongr]
  have hidx2 : idx 2 = ⟨2, by omega⟩ := by
    ext
    simp [idx, finCongr]
  have hidx3 : idx 3 = ⟨Module.finrank (ZMod 3) V - 1, by omega⟩ := by
    ext
    simp [idx, finCongr]
    omega
  have hw0 : w4 0 = 1 := by
    dsimp [w4, w]
    rw [hidx0]
    exact hbnorm _ (by change (0 : ℕ) + 1 < Module.finrank (ZMod 3) V; omega)
  have hw1 : w4 1 = 1 := by
    dsimp [w4, w]
    rw [hidx1]
    exact hbnorm _ (by change (1 : ℕ) + 1 < Module.finrank (ZMod 3) V; omega)
  have hw2 : w4 2 = 1 := by
    dsimp [w4, w]
    rw [hidx2]
    exact hbnorm _ (by change (2 : ℕ) + 1 < Module.finrank (ZMod 3) V; omega)
  have hw3ne : w4 3 ≠ 0 := by
    dsimp [w4, w]
    rw [hidx3]
    exact hblast
  have hw3 : w4 3 = 2 := by
    rcases zmod3_cases (w4 3) with h | h | h
    · exact (hw3ne h).elim
    · exfalso
      have hw4all : w4 = fun _ => (1 : ZMod 3) := by
        funext i
        fin_cases i
        · simpa using hw0
        · simpa using hw1
        · simpa using hw2
        · simpa using h
      let heAll : Q.IsometryEquiv
          (QuadraticMap.weightedSumSquares (ZMod 3) (fun _ => (1 : ZMod 3))) :=
        he4.trans (QuadraticForm.weightedSumSquaresCongr hw4all)
      obtain ⟨W, hWrank, hWzero⟩ := diagAll_has_isotropic_plane
      let U : Submodule (ZMod 3) V :=
        W.map (heAll.symm.toLinearEquiv.toLinearMap : (Fin 4 → ZMod 3) →ₗ[ZMod 3] V)
      have hUrank : Module.finrank (ZMod 3) U = 2 := by
        dsimp [U]
        rw [LinearEquiv.finrank_map_eq, hWrank]
      have hUzero : ∀ u ∈ U, Q u = 0 := by
        intro u hu
        rcases Submodule.mem_map.mp hu with ⟨x, hx, rfl⟩
        exact (heAll.symm.map_app x).trans (hWzero x hx)
      exact hminus ⟨U, hUrank, hUzero⟩
    · exact h
  have hw4 : w4 = diagW := by
    funext i
    fin_cases i <;> simp [diagW, hw0, hw1, hw2, hw3]
  exact ⟨he4.trans (QuadraticForm.weightedSumSquaresCongr hw4)⟩


lemma exists_isometry_qDeleted_diagMinus :
    Nonempty (qDeleted.IsometryEquiv diagMinusForm) :=
  exists_isometry_diagMinus_of_minus qDeleted
    polarBilin_qDeleted_nondegenerate finrank_deleted
    not_exists_isotropic_plane_qDeleted

lemma exists_isometry_qDeleted_of_minus
    {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : Module.finrank (ZMod 3) V = 4)
    (hminus : ¬ ∃ U : Submodule (ZMod 3) V,
      Module.finrank (ZMod 3) U = 2 ∧ ∀ u ∈ U, Q u = 0) :
    Nonempty (Q.IsometryEquiv qDeleted) := by
  obtain ⟨eQ⟩ := exists_isometry_diagMinus_of_minus Q hQ hd hminus
  obtain ⟨eD⟩ := exists_isometry_qDeleted_diagMinus
  exact ⟨eQ.trans eD.symm⟩

lemma orthogonalGroup_smul_eq
    {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V) {d : ZMod 3} (hd : d ≠ 0) :
    TauCeti.QuadraticMap.orthogonalGroup (d • Q) =
      TauCeti.QuadraticMap.orthogonalGroup Q := by
  ext g
  simp only [TauCeti.QuadraticMap.mem_orthogonalGroup_iff, QuadraticMap.smul_apply, smul_eq_mul]
  exact forall_congr' fun x => mul_right_inj' hd

lemma exists_pointed_isometry_qDeleted_of_map_eq_two
    {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : Module.finrank (ZMod 3) V = 4)
    (hminus : ¬ ∃ U : Submodule (ZMod 3) V,
      Module.finrank (ZMod 3) U = 2 ∧ ∀ u ∈ U, Q u = 0)
    {v : V} (hv2 : Q v = 2) :
    ∃ e : Q.IsometryEquiv qDeleted, e v = vDeleted := by
  obtain ⟨e0⟩ := exists_isometry_qDeleted_of_minus Q hQ hd hminus
  have hnorm : qDeleted (e0 v) = qDeleted vDeleted := by
    rw [e0.map_app, hv2, qDeleted_vDeleted]
  haveI : NeZero (2 : ZMod 3) := ⟨by decide⟩
  obtain ⟨aIso, hIsoV⟩ :=
    QuadraticMap.exists_isometryEquiv_apply_eq_of_map_eq (Q := qDeleted) hnorm
      qDeleted_vDeleted_ne_zero
  exact ⟨e0.trans aIso, by simpa using hIsoV⟩

lemma orthogonalGroup_eq_top_of_pointed_isometry
    {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V)
    {H : Subgroup (V ≃ₗ[ZMod 3] V)} {v : V}
    (e : Q.IsometryEquiv qDeleted) (hev : e v = vDeleted)
    (hHO : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hstab : ∀ a ∈ TauCeti.QuadraticMap.orthogonalGroup Q, a v = v → a ∈ H)
    (hmove : ∃ g ∈ H, g v ∉ Submodule.span (ZMod 3) {v}) :
    H = TauCeti.QuadraticMap.orthogonalGroup Q := by
  let eO : TauCeti.QuadraticMap.orthogonalGroup Q ≃*
      TauCeti.QuadraticMap.orthogonalGroup qDeleted :=
    QuadraticMap.orthogonalGroupCongr e
  let H' : Subgroup (TauCeti.QuadraticMap.orthogonalGroup qDeleted) :=
    (H.subgroupOf (TauCeti.QuadraticMap.orthogonalGroup Q)).map eO
  have hstab' : ∀ a : TauCeti.QuadraticMap.orthogonalGroup qDeleted,
      ((a : TauCeti.QuadraticMap.orthogonalGroup qDeleted) :
        DeletedSpace ≃ₗ[ZMod 3] DeletedSpace) vDeleted = vDeleted → a ∈ H' := by
    intro a ha
    have ha' : ((a : TauCeti.QuadraticMap.orthogonalGroup qDeleted) :
        DeletedSpace ≃ₗ[ZMod 3] DeletedSpace) (e v) = e v := by
      simpa [hev] using ha
    let b : TauCeti.QuadraticMap.orthogonalGroup Q := eO.symm a
    have hbH : b.1 ∈ H := by
      apply hstab b.1 b.2
      have hb : e.toLinearEquiv (b.1 v) = e.toLinearEquiv v := by
        calc
          e.toLinearEquiv (b.1 v) =
              ((eO b : TauCeti.QuadraticMap.orthogonalGroup qDeleted) :
                DeletedSpace ≃ₗ[ZMod 3] DeletedSpace) (e v) := by
                rw [QuadraticMap.coe_orthogonalGroupCongr_apply]
                simp [b]
          _ = e v := by
                rw [show eO b = a by simp [b]]
                exact ha'
      exact e.toLinearEquiv.injective hb
    exact Subgroup.mem_map.mpr ⟨b, hbH, by simp [b]⟩
  obtain ⟨h, hhH, hmove⟩ := hmove
  let hO : TauCeti.QuadraticMap.orthogonalGroup Q := ⟨h, hHO hhH⟩
  let h' : TauCeti.QuadraticMap.orthogonalGroup qDeleted := eO hO
  have hh'H : h' ∈ H' := Subgroup.mem_map.mpr ⟨hO, hhH, rfl⟩
  have hmove_e : ((h' : TauCeti.QuadraticMap.orthogonalGroup qDeleted) :
        DeletedSpace ≃ₗ[ZMod 3] DeletedSpace) (e v) ∉
          Submodule.span (ZMod 3) {e v} := by
    intro hspan
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hspan
    have hh : e.toLinearEquiv (h v) = e.toLinearEquiv (c • v) := by
      calc
        e.toLinearEquiv (h v) =
            ((eO hO : TauCeti.QuadraticMap.orthogonalGroup qDeleted) :
              DeletedSpace ≃ₗ[ZMod 3] DeletedSpace) (e v) := by
              rw [QuadraticMap.coe_orthogonalGroupCongr_apply]
              simp [hO]
        _ = c • e v := hc.symm
        _ = e.toLinearEquiv (c • v) := by
              simp
    have hvc : h v = c • v := e.toLinearEquiv.injective hh
    exact hmove ((Submodule.mem_span_singleton).mpr ⟨c, hvc.symm⟩)
  have hmove' : ((h' : TauCeti.QuadraticMap.orthogonalGroup qDeleted) :
        DeletedSpace ≃ₗ[ZMod 3] DeletedSpace) vDeleted ∉
          Submodule.span (ZMod 3) {vDeleted} := by
    intro hspan
    exact hmove_e (by simpa [hev] using hspan)
  have hH'top : H' = ⊤ :=
    deletedOrthogonalGroup_eq_top_of_stabilizer_le hstab' ⟨h', hh'H, hmove'⟩
  refine le_antisymm hHO ?_
  intro a ha
  let aO : TauCeti.QuadraticMap.orthogonalGroup Q := ⟨a, ha⟩
  have ha' : eO aO ∈ H' := by
    rw [hH'top]
    exact Subgroup.mem_top (eO aO)
  rcases Subgroup.mem_map.mp ha' with ⟨b, hbH, hba⟩
  have hba' : b = aO := eO.injective hba
  rw [hba'] at hbH
  exact hbH

theorem orthogonalGroup_eq_top_of_stabilizer_le
    {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : Module.finrank (ZMod 3) V = 4)
    (hminus : ¬ ∃ U : Submodule (ZMod 3) V,
      Module.finrank (ZMod 3) U = 2 ∧ ∀ u ∈ U, Q u = 0)
    {H : Subgroup (V ≃ₗ[ZMod 3] V)} {v : V}
    (hv : Q v ≠ 0)
    (hHO : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hstab : ∀ a ∈ TauCeti.QuadraticMap.orthogonalGroup Q, a v = v → a ∈ H)
    (hmove : ∃ g ∈ H, g v ∉ Submodule.span (ZMod 3) {v}) :
    H = TauCeti.QuadraticMap.orthogonalGroup Q := by
  let c : ZMod 3 := 2 * (Q v)⁻¹
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero (by decide) (inv_ne_zero hv)
  have hcQ : c * Q v = 2 := by
    dsimp [c]
    field_simp
  have hQ' : (QuadraticMap.polarBilin (c • Q)).Nondegenerate := by
    have hp : QuadraticMap.polarBilin (c • Q) = c • QuadraticMap.polarBilin Q := by
      ext x y
      simp [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_smul]
    rw [hp]
    refine ⟨?_, ?_⟩
    · intro x hx
      apply hQ.1 x
      intro y
      exact (smul_eq_zero.mp (hx y)).resolve_left hc
    · intro y hy
      apply hQ.2 y
      intro x
      exact (smul_eq_zero.mp (hy x)).resolve_left hc
  have hminus' : ¬ ∃ U : Submodule (ZMod 3) V,
      Module.finrank (ZMod 3) U = 2 ∧ ∀ u ∈ U, (c • Q) u = 0 := by
    rintro ⟨U, hU, hU0⟩
    exact hminus ⟨U, hU, fun u hu => (smul_eq_zero.mp (hU0 u hu)).resolve_left hc⟩
  have hQ'v : (c • Q) v = 2 := by
    simpa [QuadraticMap.smul_apply, smul_eq_mul] using hcQ
  obtain ⟨e, hev⟩ :=
    exists_pointed_isometry_qDeleted_of_map_eq_two (c • Q) hQ' hd hminus' hQ'v
  have hOeq : TauCeti.QuadraticMap.orthogonalGroup (c • Q) =
      TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthogonalGroup_smul_eq Q hc
  have hHO' : H ≤ TauCeti.QuadraticMap.orthogonalGroup (c • Q) := by
    intro a ha
    rw [hOeq]
    exact hHO ha
  have hstab' : ∀ a ∈ TauCeti.QuadraticMap.orthogonalGroup (c • Q),
      a v = v → a ∈ H := by
    intro a ha hav
    have haQ : a ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
      simpa [hOeq] using ha
    exact hstab a haQ hav
  have htop :=
    orthogonalGroup_eq_top_of_pointed_isometry (c • Q) e hev hHO' hstab' hmove
  rw [htop, hOeq]

end CFSG.LinearAlgebra.OrthogonalFourMinusThree
