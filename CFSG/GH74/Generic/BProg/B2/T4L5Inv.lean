module

public import CFSG.GH74.Generic.BProg.B2.T4L5Count
public import CFSG.GH74.Generic.BProg.B2.WeakSigGen

public section

namespace CFSG.GH74.Generic.BProg.B2.T4.L5Inv

open Matrix L5Count
open scoped Classical

variable {F : Type} [Field F]

@[expose] noncomputable def permGL5 : Equiv.Perm (Fin 5) →* GL (Fin 5) F :=
  (Matrix.permMatrixHom (n := Fin 5) (R := F)).toHomUnits

theorem coe_permGL5 (σ : Equiv.Perm (Fin 5)) :
    ((permGL5 σ : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) = σ⁻¹.permMatrix F := rfl

theorem coe_permGL5_inv (σ : Equiv.Perm (Fin 5)) :
    (((permGL5 σ)⁻¹ : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) = σ.permMatrix F := by
  rw [← map_inv, coe_permGL5, inv_inv]

theorem permGL5_conj_diagonal (σ : Equiv.Perm (Fin 5)) (v : Fin 5 → F) :
    ((permGL5 σ : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) * Matrix.diagonal v *
        (((permGL5 σ)⁻¹ : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) =
      Matrix.diagonal (v ∘ σ.symm) := by
  rw [coe_permGL5, coe_permGL5_inv]
  have h1 : (σ⁻¹.permMatrix F) * Matrix.diagonal v =
      (Matrix.diagonal v).submatrix (σ⁻¹ : Equiv.Perm (Fin 5)) id :=
    PEquiv.toMatrix_toPEquiv_mul _ _
  have h2 : ((Matrix.diagonal v).submatrix (σ⁻¹ : Equiv.Perm (Fin 5)) id) * σ.permMatrix F =
      ((Matrix.diagonal v).submatrix (σ⁻¹ : Equiv.Perm (Fin 5)) id).submatrix id σ.symm :=
    PEquiv.mul_toMatrix_toPEquiv _ _
  rw [h1, h2]
  ext k l
  simp only [Matrix.submatrix_apply, id_eq, Matrix.diagonal_apply, Function.comp_apply]
  by_cases hkl : k = l
  · subst hkl
    simp [Equiv.Perm.inv_def]
  · have : σ⁻¹ k ≠ σ.symm l := by
      intro h'
      apply hkl
      have : σ.symm k = σ.symm l := by rw [← Equiv.Perm.inv_def]; exact h'
      exact σ.symm.injective this
    simp [hkl]

theorem exists_perm_of_negCount {ε η : Fin 5 → F} (hε : ∀ i, ε i * ε i = 1) (hη : ∀ i, η i * η i = 1)
    (h : negCount ε = negCount η) : ∃ σ : Equiv.Perm (Fin 5), ∀ i, η i = ε (σ.symm i) := by
  have hc : Fintype.card {i // ε i = -1} = Fintype.card {i // η i = -1} := by
    rw [Fintype.card_subtype, Fintype.card_subtype]
    exact h
  let e : {i // ε i = -1} ≃ {i // η i = -1} := Fintype.equivOfCardEq hc
  refine ⟨e.extendSubtype, fun i => ?_⟩
  set j := e.extendSubtype.symm i with hj
  have hij : e.extendSubtype j = i := by rw [hj, Equiv.apply_symm_apply]
  by_cases hjm : ε j = -1
  · have := e.extendSubtype_mem j hjm
    rw [hij] at this
    rw [this, hjm]
  · have hni := e.extendSubtype_not_mem j hjm
    rw [hij] at hni
    rcases eq_one_or_neg_one (hη i) with h1 | h1
    · rcases eq_one_or_neg_one (hε j) with h2 | h2
      · rw [h1, h2]
      · exact absurd h2 hjm
    · exact absurd h1 hni

theorem mul_apply_self_of_isDiag {X : Matrix (Fin 5) (Fin 5) F} (hX : X.IsDiag)
    (Y : Matrix (Fin 5) (Fin 5) F) (i : Fin 5) : (X * Y) i i = X i i * Y i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    rw [hX (Ne.symm hk), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem det_of_isDiag {X : Matrix (Fin 5) (Fin 5) F} (hX : X.IsDiag) : X.det = ∏ i, X i i := by
  conv_lhs => rw [← hX.diagonal_diag]
  rw [Matrix.det_diagonal]
  rfl

theorem commute_of_isDiag {X Y : Matrix (Fin 5) (Fin 5) F} (hX : X.IsDiag) (hY : Y.IsDiag) :
    X * Y = Y * X := by
  rw [← hX.diagonal_diag, ← hY.diagonal_diag, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

section Conj

theorem exists_conj_of_diag (S N : Subgroup (GL (Fin 5) F))
    (hNS : ∀ n ∈ N, (n : Matrix (Fin 5) (Fin 5) F).det = 1 → n ∈ S)
    (hperm : ∀ σ : Equiv.Perm (Fin 5), permGL5 σ ∈ N)
    (hadj : ∀ n ∈ N, ∃ δ ∈ N, (δ : Matrix (Fin 5) (Fin 5) F).IsDiag ∧
      (n : Matrix (Fin 5) (Fin 5) F).det * (δ : Matrix (Fin 5) (Fin 5) F).det = 1)
    {x y B C : GL (Fin 5) F} (hBN : B ∈ N) (hCN : C ∈ N)
    (hx : ((B⁻¹ * x * B : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F).IsDiag)
    (hy : ((C⁻¹ * y * C : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F).IsDiag)
    (hxsq : ∀ i, ((B⁻¹ * x * B : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) i i *
      ((B⁻¹ * x * B : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) i i = 1)
    (hysq : ∀ i, ((C⁻¹ * y * C : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) i i *
      ((C⁻¹ * y * C : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) i i = 1)
    (hw : negCount (fun i => ((B⁻¹ * x * B : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) i i) =
      negCount (fun i => ((C⁻¹ * y * C : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) i i)) :
    ∃ g ∈ S, g * x * g⁻¹ = y := by
  classical
  obtain ⟨σ, hσ⟩ := exists_perm_of_negCount hxsq hysq hw
  set g : GL (Fin 5) F := C * permGL5 σ * B⁻¹ with hg
  have hgN : g ∈ N := N.mul_mem (N.mul_mem hCN (hperm σ)) (N.inv_mem hBN)
  have hkey : (permGL5 σ * (B⁻¹ * x * B) * (permGL5 σ)⁻¹ : GL (Fin 5) F) = C⁻¹ * y * C := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, ← hx.diagonal_diag, permGL5_conj_diagonal, ← hy.diagonal_diag]
    congr 1
    funext i
    exact (hσ i).symm
  have hgconj : g * x * g⁻¹ = y := by
    have : g * x * g⁻¹ = C * (permGL5 σ * (B⁻¹ * x * B) * (permGL5 σ)⁻¹) * C⁻¹ := by
      rw [hg]
      group
    rw [this, hkey]
    group
  obtain ⟨δ, hδN, hδdiag, hδdet⟩ := hadj g hgN
  set c : GL (Fin 5) F := B * δ * B⁻¹ with hc
  have hcN : c ∈ N := N.mul_mem (N.mul_mem hBN hδN) (N.inv_mem hBN)
  have hcx : c * x = x * c := by
    have h1 : δ * (B⁻¹ * x * B) = (B⁻¹ * x * B) * δ := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul]
      exact commute_of_isDiag hδdiag hx
    calc c * x = B * (δ * (B⁻¹ * x * B)) * B⁻¹ := by rw [hc]; group
      _ = B * ((B⁻¹ * x * B) * δ) * B⁻¹ := by rw [h1]
      _ = x * c := by rw [hc]; group
  set g' : GL (Fin 5) F := g * c with hg'
  have hg'N : g' ∈ N := N.mul_mem hgN hcN
  have hcdet : (c : Matrix (Fin 5) (Fin 5) F).det = (δ : Matrix (Fin 5) (Fin 5) F).det := by
    have hBB : (B : Matrix (Fin 5) (Fin 5) F).det *
        ((B⁻¹ : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F).det = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
    have e1 : (c : Matrix (Fin 5) (Fin 5) F) = (B : Matrix (Fin 5) (Fin 5) F) *
        (δ : Matrix (Fin 5) (Fin 5) F) * ((B⁻¹ : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) := by
      rw [hc, Units.val_mul, Units.val_mul]
    rw [e1, Matrix.det_mul, Matrix.det_mul]
    calc (B : Matrix (Fin 5) (Fin 5) F).det * (δ : Matrix (Fin 5) (Fin 5) F).det *
          ((B⁻¹ : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F).det
        = (δ : Matrix (Fin 5) (Fin 5) F).det * ((B : Matrix (Fin 5) (Fin 5) F).det *
          ((B⁻¹ : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F).det) := by ring
      _ = (δ : Matrix (Fin 5) (Fin 5) F).det := by rw [hBB, mul_one]
  have hg'det : (g' : Matrix (Fin 5) (Fin 5) F).det = 1 := by
    have e1 : (g' : Matrix (Fin 5) (Fin 5) F) = (g : Matrix (Fin 5) (Fin 5) F) *
        (c : Matrix (Fin 5) (Fin 5) F) := by rw [hg', Units.val_mul]
    rw [e1, Matrix.det_mul, hcdet, hδdet]
  refine ⟨g', hNS g' hg'N hg'det, ?_⟩
  calc g' * x * g'⁻¹ = g * (c * x) * c⁻¹ * g⁻¹ := by rw [hg']; group
    _ = g * (x * c) * c⁻¹ * g⁻¹ := by rw [hcx]
    _ = g * x * g⁻¹ := by group
    _ = y := hgconj

end Conj

section Generic

variable {P : Type} [Group P] [Finite P]

theorem exists_conj_mem_of_model (h2 : (2 : F) ≠ 0) (S N : Subgroup (GL (Fin 5) F))
    (hdetS : ∀ s ∈ S, (s : Matrix (Fin 5) (Fin 5) F).det = 1)
    (hNS : ∀ n ∈ N, (n : Matrix (Fin 5) (Fin 5) F).det = 1 → n ∈ S)
    (hperm : ∀ σ : Equiv.Perm (Fin 5), permGL5 σ ∈ N)
    (hadj : ∀ n ∈ N, ∃ δ ∈ N, (δ : Matrix (Fin 5) (Fin 5) F).IsDiag ∧
      (n : Matrix (Fin 5) (Fin 5) F).det * (δ : Matrix (Fin 5) (Fin 5) F).det = 1)
    (π : ↥S →* P)
    (hlift : ∀ D : Subgroup P, CFSG.IsElementaryAbelian 2 ↥D → ∃ (B : GL (Fin 5) F) (ρ : ↥D →* ↥S),
      B ∈ N ∧ (∀ d, π (ρ d) = d) ∧
        ∀ d, ((B⁻¹ * ((ρ d : ↥S) : GL (Fin 5) F) * B : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F).IsDiag)
    (E : Subgroup P) (hEab : CFSG.IsElementaryAbelian 2 ↥E) (hE8 : Nat.card ↥E = 8)
    (v : P) (hv : v * v = 1) (hv1 : v ≠ 1) : ∃ g : P, g * v * g⁻¹ ∈ E := by
  classical
  have : Fintype ↥E := Fintype.ofFinite _
  obtain ⟨B, ρ, hBN, hρπ, hρd⟩ := hlift E hEab
  have hDv : CFSG.IsElementaryAbelian 2 ↥(Subgroup.zpowers v) := by
    refine WeakSigGen.isElementaryAbelian_of_forall ?_ ?_
    · intro a ha b hb
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact (Commute.zpow_zpow_self v i j).eq
    · intro a ha
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      rw [← _root_.zpow_add, ← two_mul, _root_.zpow_mul, show v ^ (2 : ℤ) = 1 by rw [zpow_two, hv],
        _root_.one_zpow]
  obtain ⟨B', ρ', hB'N, hρ'π, hρ'd⟩ := hlift _ hDv
  set v₀ : ↥(Subgroup.zpowers v) := ⟨v, Subgroup.mem_zpowers v⟩ with hv₀
  set vt : GL (Fin 5) F := ((ρ' v₀ : ↥S) : GL (Fin 5) F) with hvt
  have hρsq : ∀ e : ↥E, ((ρ e : ↥S) : GL (Fin 5) F) * ((ρ e : ↥S) : GL (Fin 5) F) = 1 := by
    intro e
    have h1 : e * e = 1 := WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hEab e
    have h := congrArg (fun z => ((ρ z : ↥S) : GL (Fin 5) F)) h1
    simpa only [map_mul, map_one, Subgroup.coe_mul, Subgroup.coe_one] using h
  have hvsq : vt * vt = 1 := by
    have h1 : v₀ * v₀ = 1 := WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hDv v₀
    have h := congrArg (fun z => ((ρ' z : ↥S) : GL (Fin 5) F)) h1
    simpa only [map_mul, map_one, Subgroup.coe_mul, Subgroup.coe_one] using h
  let D : ↥E → Matrix (Fin 5) (Fin 5) F := fun e =>
    ((B⁻¹ * ((ρ e : ↥S) : GL (Fin 5) F) * B : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)
  have hDmul : ∀ e f, D (e * f) = D e * D f := by
    intro e f
    simp only [D, map_mul, Subgroup.coe_mul]
    rw [← Units.val_mul]
    congr 1
    group
  have hD1 : ∀ e, D e * D e = 1 := by
    intro e
    rw [← hDmul, WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hEab e]
    simp [D]
  let ε : ↥E → Fin 5 → F := fun e i => D e i i
  have hεmul : ∀ e f i, ε (e * f) i = ε e i * ε f i := by
    intro e f i
    simp only [ε]
    rw [hDmul, mul_apply_self_of_isDiag (hρd e)]
  have hεsq : ∀ e i, ε e i * ε e i = 1 := by
    intro e i
    have h := congrArg (fun X : Matrix (Fin 5) (Fin 5) F => X i i) (hD1 e)
    rw [mul_apply_self_of_isDiag (hρd e), Matrix.one_apply_eq] at h
    exact h
  have hεinj : ∀ e, (∀ i, ε e i = 1) → e = 1 := by
    intro e he
    have hDe : D e = 1 := by
      have hdd : Matrix.diagonal (Matrix.diag (D e)) = D e := (hρd e).diagonal_diag
      have : Matrix.diag (D e) = fun _ => (1 : F) := funext he
      rw [← hdd, this, Matrix.diagonal_one]
    have hρe : ((ρ e : ↥S) : GL (Fin 5) F) = 1 := by
      have h1 : (B⁻¹ * ((ρ e : ↥S) : GL (Fin 5) F) * B : GL (Fin 5) F) = 1 := Units.ext hDe
      have : ((ρ e : ↥S) : GL (Fin 5) F) = B * (B⁻¹ * ((ρ e : ↥S) : GL (Fin 5) F) * B) * B⁻¹ := by
        group
      rw [this, h1]
      group
    have hρe' : ρ e = 1 := Subtype.ext hρe
    have := hρπ e
    rw [hρe', map_one] at this
    exact Subtype.ext this.symm
  have hεdet : ∀ e, ∏ i, ε e i = 1 := by
    intro e
    rw [show (∏ i, ε e i) = (D e).det from (det_of_isDiag (hρd e)).symm]
    simp only [D, Units.val_mul, Matrix.det_mul]
    rw [hdetS _ (ρ e).2, mul_one, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.det_one]
  have hcardE : Fintype.card ↥E = 8 := by rw [Fintype.card_eq_nat_card, hE8]
  obtain ⟨⟨e₂, he₂⟩, ⟨e₄, he₄⟩⟩ := exists_negCount_two_four h2 hcardE ε hεmul hεsq hεinj hεdet
  set D' : Matrix (Fin 5) (Fin 5) F := ((B'⁻¹ * vt * B' : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)
    with hD'
  have hD'diag : D'.IsDiag := hρ'd v₀
  let η : Fin 5 → F := fun i => D' i i
  have hD'1 : D' * D' = 1 := by
    rw [hD', ← Units.val_mul]
    have : (B'⁻¹ * vt * B') * (B'⁻¹ * vt * B') = B'⁻¹ * (vt * vt) * B' := by group
    rw [this, hvsq]
    simp
  have hηsq : ∀ i, η i * η i = 1 := by
    intro i
    have h := congrArg (fun X : Matrix (Fin 5) (Fin 5) F => X i i) hD'1
    rw [mul_apply_self_of_isDiag hD'diag, Matrix.one_apply_eq] at h
    exact h
  have hηdet : ∏ i, η i = 1 := by
    rw [show (∏ i, η i) = D'.det from (det_of_isDiag hD'diag).symm, hD']
    simp only [Units.val_mul, Matrix.det_mul]
    rw [hdetS _ (ρ' v₀).2, mul_one, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.det_one]
  have hη24 : negCount η = 2 ∨ negCount η = 4 := by
    have hev := even_negCount h2 hηsq hηdet
    have hle := negCount_le η
    have h0 : negCount η ≠ 0 := by
      intro h0
      apply hv1
      have hη1 := eq_one_of_negCount_eq_zero hηsq h0
      have hD'e : D' = 1 := by
        rw [← hD'diag.diagonal_diag]
        have : Matrix.diag D' = fun _ => (1 : F) := funext hη1
        rw [this, Matrix.diagonal_one]
      have hvt1 : vt = 1 := by
        have h1 : (B'⁻¹ * vt * B' : GL (Fin 5) F) = 1 := Units.ext hD'e
        have : vt = B' * (B'⁻¹ * vt * B') * B'⁻¹ := by group
        rw [this, h1]
        group
      have hρ'1 : ρ' v₀ = 1 := Subtype.ext hvt1
      have := hρ'π v₀
      rw [hρ'1, map_one] at this
      exact this.symm
    obtain ⟨k, hk⟩ := hev
    omega
  obtain ⟨e, he⟩ : ∃ e : ↥E, negCount (ε e) = negCount η := by
    rcases hη24 with h | h
    · exact ⟨e₂, by rw [he₂, h]⟩
    · exact ⟨e₄, by rw [he₄, h]⟩
  obtain ⟨σ, hσ⟩ := exists_perm_of_negCount (hεsq e) hηsq he
  set ρe : GL (Fin 5) F := ((ρ e : ↥S) : GL (Fin 5) F) with hρe
  set g : GL (Fin 5) F := B' * permGL5 σ * B⁻¹ with hg
  have hgN : g ∈ N := N.mul_mem (N.mul_mem hB'N (hperm σ)) (N.inv_mem hBN)
  have hkey : (permGL5 σ * (B⁻¹ * ρe * B) * (permGL5 σ)⁻¹ : GL (Fin 5) F) = B'⁻¹ * vt * B' := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    have hDe : ((B⁻¹ * ρe * B : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) =
        Matrix.diagonal (ε e) := ((hρd e).diagonal_diag).symm
    rw [hDe, permGL5_conj_diagonal, ← hD', ← hD'diag.diagonal_diag]
    congr 1
    funext i
    exact (hσ i).symm
  have hgconj : g * ρe * g⁻¹ = vt := by
    have : g * ρe * g⁻¹ = B' * (permGL5 σ * (B⁻¹ * ρe * B) * (permGL5 σ)⁻¹) * B'⁻¹ := by
      rw [hg]
      group
    rw [this, hkey]
    group
  obtain ⟨δ, hδN, hδdiag, hδdet⟩ := hadj g hgN
  set c : GL (Fin 5) F := B * δ * B⁻¹ with hc
  have hcN : c ∈ N := N.mul_mem (N.mul_mem hBN hδN) (N.inv_mem hBN)
  have hcρ : c * ρe = ρe * c := by
    have h1 : δ * (B⁻¹ * ρe * B) = (B⁻¹ * ρe * B) * δ := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul]
      exact commute_of_isDiag hδdiag (hρd e)
    calc c * ρe = B * (δ * (B⁻¹ * ρe * B)) * B⁻¹ := by rw [hc]; group
      _ = B * ((B⁻¹ * ρe * B) * δ) * B⁻¹ := by rw [h1]
      _ = ρe * c := by rw [hc]; group
  set g' : GL (Fin 5) F := g * c with hg'
  have hg'N : g' ∈ N := N.mul_mem hgN hcN
  have hcdet : (c : Matrix (Fin 5) (Fin 5) F).det = (δ : Matrix (Fin 5) (Fin 5) F).det := by
    have hBB : (B : Matrix (Fin 5) (Fin 5) F).det *
        ((B⁻¹ : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F).det = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
    have e1 : (c : Matrix (Fin 5) (Fin 5) F) = (B : Matrix (Fin 5) (Fin 5) F) *
        (δ : Matrix (Fin 5) (Fin 5) F) * ((B⁻¹ : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) := by
      rw [hc, Units.val_mul, Units.val_mul]
    rw [e1, Matrix.det_mul, Matrix.det_mul]
    calc (B : Matrix (Fin 5) (Fin 5) F).det * (δ : Matrix (Fin 5) (Fin 5) F).det *
          ((B⁻¹ : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F).det
        = (δ : Matrix (Fin 5) (Fin 5) F).det * ((B : Matrix (Fin 5) (Fin 5) F).det *
          ((B⁻¹ : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F).det) := by ring
      _ = (δ : Matrix (Fin 5) (Fin 5) F).det := by rw [hBB, mul_one]
  have hg'det : (g' : Matrix (Fin 5) (Fin 5) F).det = 1 := by
    have e1 : (g' : Matrix (Fin 5) (Fin 5) F) = (g : Matrix (Fin 5) (Fin 5) F) *
        (c : Matrix (Fin 5) (Fin 5) F) := by rw [hg', Units.val_mul]
    rw [e1, Matrix.det_mul, hcdet, hδdet]
  have hg'S : g' ∈ S := hNS g' hg'N hg'det
  have hg'conj : g' * ρe * g'⁻¹ = vt := by
    calc g' * ρe * g'⁻¹ = g * (c * ρe) * c⁻¹ * g⁻¹ := by rw [hg']; group
      _ = g * (ρe * c) * c⁻¹ * g⁻¹ := by rw [hcρ]
      _ = g * ρe * g⁻¹ := by group
      _ = vt := hgconj
  set h : P := π ⟨g', hg'S⟩ with hh
  have hS : (⟨g', hg'S⟩ : ↥S) * ρ e * (⟨g', hg'S⟩ : ↥S)⁻¹ = ρ' v₀ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hg'conj
  have hP : h * (e : P) * h⁻¹ = v := by
    have := congrArg π hS
    rw [map_mul, map_mul, map_inv, hρπ e, hρ'π v₀] at this
    exact this
  refine ⟨h⁻¹, ?_⟩
  have : h⁻¹ * v * h⁻¹⁻¹ = (e : P) := by
    rw [← hP]
    group
  rw [this]
  exact e.2

end Generic

section Std

@[expose] def stdSign (k : ℕ) : Fin 5 → F := fun i => if i.val < k then -1 else 1

theorem stdSign_sq (k : ℕ) (i : Fin 5) : stdSign (F := F) k i * stdSign k i = 1 := by
  unfold stdSign
  split_ifs <;> simp

@[expose] def sgnGL (ε : Fin 5 → F) (hε : ∀ i, ε i * ε i = 1) : GL (Fin 5) F where
  val := Matrix.diagonal ε
  inv := Matrix.diagonal ε
  val_inv := by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; exact hε i
  inv_val := by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; exact hε i

theorem coe_sgnGL (ε : Fin 5 → F) (hε : ∀ i, ε i * ε i = 1) :
    ((sgnGL ε hε : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) = Matrix.diagonal ε := rfl

theorem negCount_stdSign (h2 : (2 : F) ≠ 0) {k : ℕ} (hk : k ≤ 5) : negCount (stdSign (F := F) k) = k := by
  unfold negCount stdSign
  have hne : (1 : F) ≠ -1 := fun h => neg_one_ne_one h2 h.symm
  have : (Finset.univ.filter fun i : Fin 5 => (if i.val < k then (-1 : F) else 1) = -1) =
      Finset.univ.filter fun i : Fin 5 => i.val < k := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs with h
    · exact ⟨fun _ => h, fun _ => rfl⟩
    · exact ⟨fun h' => absurd h' hne, fun h' => absurd h' h⟩
  rw [this]
  interval_cases k <;> decide

variable {P : Type} [Group P]

theorem exists_conj_std_of_model (h2 : (2 : F) ≠ 0) (S N : Subgroup (GL (Fin 5) F))
    (hdetS : ∀ s ∈ S, (s : Matrix (Fin 5) (Fin 5) F).det = 1)
    (hNS : ∀ n ∈ N, (n : Matrix (Fin 5) (Fin 5) F).det = 1 → n ∈ S)
    (hperm : ∀ σ : Equiv.Perm (Fin 5), permGL5 σ ∈ N)
    (hadj : ∀ n ∈ N, ∃ δ ∈ N, (δ : Matrix (Fin 5) (Fin 5) F).IsDiag ∧
      (n : Matrix (Fin 5) (Fin 5) F).det * (δ : Matrix (Fin 5) (Fin 5) F).det = 1)
    (π : ↥S →* P)
    (hlift : ∀ D : Subgroup P, CFSG.IsElementaryAbelian 2 ↥D → ∃ (B : GL (Fin 5) F) (ρ : ↥D →* ↥S),
      B ∈ N ∧ (∀ d, π (ρ d) = d) ∧
        ∀ d, ((B⁻¹ * ((ρ d : ↥S) : GL (Fin 5) F) * B : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F).IsDiag)
    (hstd : ∀ k, k = 2 ∨ k = 4 → sgnGL (stdSign (F := F) k) (stdSign_sq k) ∈ S)
    (v : P) (hv : v * v = 1) (hv1 : v ≠ 1) :
    ∃ k, ∃ hk : k = 2 ∨ k = 4, ∃ g : P,
      g * v * g⁻¹ = π ⟨sgnGL (stdSign (F := F) k) (stdSign_sq k), hstd k hk⟩ := by
  classical
  have hDv : CFSG.IsElementaryAbelian 2 ↥(Subgroup.zpowers v) := by
    refine WeakSigGen.isElementaryAbelian_of_forall ?_ ?_
    · intro a ha b hb
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact (Commute.zpow_zpow_self v i j).eq
    · intro a ha
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      rw [← _root_.zpow_add, ← two_mul, _root_.zpow_mul, show v ^ (2 : ℤ) = 1 by rw [zpow_two, hv],
        _root_.one_zpow]
  obtain ⟨B', ρ', hB'N, hρ'π, hρ'd⟩ := hlift _ hDv
  set v₀ : ↥(Subgroup.zpowers v) := ⟨v, Subgroup.mem_zpowers v⟩ with hv₀
  set vt : GL (Fin 5) F := ((ρ' v₀ : ↥S) : GL (Fin 5) F) with hvt
  have hvsq : vt * vt = 1 := by
    have h1 : v₀ * v₀ = 1 := WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hDv v₀
    have h := congrArg (fun z => ((ρ' z : ↥S) : GL (Fin 5) F)) h1
    simpa only [map_mul, map_one, Subgroup.coe_mul, Subgroup.coe_one] using h
  set D' : Matrix (Fin 5) (Fin 5) F := ((B'⁻¹ * vt * B' : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)
    with hD'
  have hD'diag : D'.IsDiag := hρ'd v₀
  have hD'1 : D' * D' = 1 := by
    rw [hD', ← Units.val_mul]
    have : (B'⁻¹ * vt * B') * (B'⁻¹ * vt * B') = B'⁻¹ * (vt * vt) * B' := by group
    rw [this, hvsq]
    simp
  have hηsq : ∀ i, D' i i * D' i i = 1 := by
    intro i
    have h := congrArg (fun X : Matrix (Fin 5) (Fin 5) F => X i i) hD'1
    rw [mul_apply_self_of_isDiag hD'diag, Matrix.one_apply_eq] at h
    exact h
  have hηdet : ∏ i, D' i i = 1 := by
    rw [show (∏ i, D' i i) = D'.det from (det_of_isDiag hD'diag).symm, hD']
    simp only [Units.val_mul, Matrix.det_mul]
    rw [hdetS _ (ρ' v₀).2, mul_one, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.det_one]
  have hη24 : negCount (fun i => D' i i) = 2 ∨ negCount (fun i => D' i i) = 4 := by
    have hev := even_negCount h2 hηsq hηdet
    have hle := negCount_le (fun i => D' i i)
    have h0 : negCount (fun i => D' i i) ≠ 0 := by
      intro h0
      apply hv1
      have hη1 := eq_one_of_negCount_eq_zero hηsq h0
      have hD'e : D' = 1 := by
        rw [← hD'diag.diagonal_diag]
        have : Matrix.diag D' = fun _ => (1 : F) := funext hη1
        rw [this, Matrix.diagonal_one]
      have hvt1 : vt = 1 := by
        have h1 : (B'⁻¹ * vt * B' : GL (Fin 5) F) = 1 := Units.ext hD'e
        have : vt = B' * (B'⁻¹ * vt * B') * B'⁻¹ := by group
        rw [this, h1]
        group
      have hρ'1 : ρ' v₀ = 1 := Subtype.ext hvt1
      have := hρ'π v₀
      rw [hρ'1, map_one] at this
      exact this.symm
    obtain ⟨k, hk⟩ := hev
    omega
  set k := negCount (fun i => D' i i) with hkdef
  refine ⟨k, hη24, ?_⟩
  set x : GL (Fin 5) F := sgnGL (stdSign (F := F) k) (stdSign_sq k) with hx
  have hk5 : k ≤ 5 := by rcases hη24 with h | h <;> omega
  have hxd : ((1⁻¹ * x * 1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F).IsDiag := by
    rw [inv_one, one_mul, mul_one, hx, coe_sgnGL]
    exact Matrix.isDiag_diagonal _
  have hxsq : ∀ i, ((1⁻¹ * x * 1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) i i *
      ((1⁻¹ * x * 1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) i i = 1 := by
    intro i
    rw [inv_one, one_mul, mul_one, hx, coe_sgnGL, Matrix.diagonal_apply_eq]
    exact stdSign_sq k i
  have hw : negCount (fun i => ((1⁻¹ * x * 1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) i i) =
      negCount (fun i => ((B'⁻¹ * vt * B' : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) i i) := by
    have e1 : (fun i => ((1⁻¹ * x * 1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) i i) = stdSign k := by
      funext i
      rw [inv_one, one_mul, mul_one, hx, coe_sgnGL, Matrix.diagonal_apply_eq]
    rw [e1, negCount_stdSign h2 hk5]
  obtain ⟨g, hgS, hg⟩ := exists_conj_of_diag S N hNS hperm hadj (N.one_mem) hB'N hxd hD'diag hxsq hηsq hw
  refine ⟨(π ⟨g, hgS⟩)⁻¹, ?_⟩
  have hS : (⟨g, hgS⟩ : ↥S) * ⟨x, hstd k hη24⟩ * (⟨g, hgS⟩ : ↥S)⁻¹ = ρ' v₀ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hg
  have h' : π ⟨g, hgS⟩ * π ⟨x, hstd k hη24⟩ * (π ⟨g, hgS⟩)⁻¹ = v := by
    rw [← map_mul, ← map_inv, ← map_mul, hS]
    exact hρ'π v₀
  rw [← h']
  group
  rfl

end Std

end CFSG.GH74.Generic.BProg.B2.T4.L5Inv
