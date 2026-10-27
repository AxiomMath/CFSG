module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RUA6Def
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A6Aut
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21GenA6
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_16FactsSix

public section

namespace CFSG.EvenSporadicStandard.Fin76b.A6X

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts CFSG.QuasithinUnique.DoubleA3

set_option maxRecDepth 100000 in
theorem invol_fix_check : Core.autL.all (fun c =>
    Core.cmul c c != Core.cid || c == Core.cid || 5 ≤ (Core.cpslList c).length) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cent_d_check : Core.autL.all (fun c =>
    !(Core.dLit.all fun d => Core.cmul c d == Core.cmul d c) || Core.cmul c c == Core.cid) =
      true := by
  decide +kernel

theorem five_le_card_cent {α : P10} (hα : α ∈ A6Models.autA6) (h2 : α * α = 1) (hne : α ≠ 1) :
    5 ≤ Nat.card ↥(A6Models.psl29 ⊓ Subgroup.centralizer ({α} : Set P10)) := by
  have hall := List.all_eq_true.1 invol_fix_check
  have h1 := hall (code α) (code_mem_autL hα)
  have e1 : (Core.cmul (code α) (code α) != Core.cid) = false := by
    rw [← code_mul, h2, code_one]
    simp
  have e2 : (code α == Core.cid) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    rw [← code_one]
    intro hc
    exact hne (code_injective hc)
  rw [e1, e2] at h1
  simp only [Bool.false_or, decide_eq_true_eq] at h1
  rw [card_psl29_centralizer]
  exact h1

theorem sq_of_cent_D {c : P10} (hc : c ∈ A6Models.autA6)
    (h : ∀ d ∈ P0 ⊓ A6Models.psl29, c * d = d * c) : c * c = 1 := by
  have hall := List.all_eq_true.1 cent_d_check
  have h1 := hall (code c) (code_mem_autL hc)
  have hd : (Core.dLit.all fun d => Core.cmul (code c) d == Core.cmul d (code c)) = true := by
    rw [List.all_eq_true]
    intro d hd
    obtain ⟨d', hd'0, rfl⟩ := Out21.A6.surj_D d hd
    have := h d' hd'0
    rw [beq_iff_eq, ← code_mul, ← code_mul, this]
  rw [hd] at h1
  simp only [Bool.not_true, Bool.false_or, beq_iff_eq] at h1
  apply code_injective
  rw [code_mul, h1, code_one]

theorem fix_invol {ζ : MulAut (alternatingGroup (Fin 6))} (h2 : ζ * ζ = 1) (h1 : ζ ≠ 1) :
    5 ≤ Nat.card ↥(fixSub ζ) := by
  obtain ⟨ψ, -⟩ := exists_psl_equiv
  let φ : alternatingGroup (Fin 6) ≃* ↥A6Models.psl29 := ψ.symm
  obtain ⟨b, hbA, hb⟩ := exists_aut_model φ ζ
  have hζζ : ∀ k, ζ (ζ k) = k := fun k => by
    have := congrArg (fun f : MulAut (alternatingGroup (Fin 6)) => f k) h2
    simpa using this
  have hb2 : b * b = 1 := by
    have hc : b * b ∈ A6Models.autA6 := A6Models.autA6.mul_mem hbA hbA
    refine centralizer_psl29 hc fun x hx => ?_
    set k := φ.symm ⟨x, hx⟩ with hkdef
    have hk : ((φ k : ↥A6Models.psl29) : P10) = x := by simp [hkdef]
    have h1' := hb k
    have h2' := hb (ζ k)
    rw [hζζ k, h1', hk] at h2'
    calc b * b * x = (b * (b * x * b⁻¹) * b⁻¹) * (b * b) := by group
      _ = x * (b * b) := by rw [← h2']
  have hb1 : b ≠ 1 := by
    intro hb1
    apply h1
    refine MulEquiv.ext fun k => ?_
    apply φ.injective
    apply Subtype.ext
    rw [hb k, hb1]
    simp
  have h5 := five_le_card_cent hbA hb2 hb1
  let f : alternatingGroup (Fin 6) →* P10 := A6Models.psl29.subtype.comp φ.toMonoidHom
  have hfinj : Function.Injective f := Subtype.val_injective.comp φ.injective
  have hmap : (fixSub ζ).map f = A6Models.psl29 ⊓ Subgroup.centralizer ({b} : Set P10) := by
    ext y
    constructor
    · rintro ⟨k, hk, rfl⟩
      refine ⟨(φ k).2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      have h := hb k
      rw [mem_fixSub.1 hk] at h
      show ((φ k : ↥A6Models.psl29) : P10) * b = b * ((φ k : ↥A6Models.psl29) : P10)
      calc ((φ k : ↥A6Models.psl29) : P10) * b
          = (b * ((φ k : ↥A6Models.psl29) : P10) * b⁻¹) * b := by rw [← h]
        _ = b * ((φ k : ↥A6Models.psl29) : P10) := by group
    · rintro ⟨hy, hyc⟩
      refine ⟨φ.symm ⟨y, hy⟩, mem_fixSub.2 ?_, by simp [f]⟩
      apply φ.injective
      apply Subtype.ext
      rw [hb (φ.symm ⟨y, hy⟩)]
      have hk : ((φ (φ.symm ⟨y, hy⟩) : ↥A6Models.psl29) : P10) = y := by simp
      rw [hk]
      have := Subgroup.mem_centralizer_singleton_iff.1 hyc
      calc b * y * b⁻¹ = (y * b) * b⁻¹ := by rw [this]
        _ = y := by group
  rw [← Subgroup.card_map_of_injective hfinj, hmap]
  exact h5

theorem fix_sq_A {γ : MulAut (alternatingGroup (Fin 6))} {Q : Subgroup (alternatingGroup (Fin 6))}
    (hQ : Nat.card ↥Q = 8) (hfix : ∀ q ∈ Q, γ q = q) : γ * γ = 1 := by
  obtain ⟨ψ, -⟩ := exists_psl_equiv
  let φ : alternatingGroup (Fin 6) ≃* ↥A6Models.psl29 := ψ.symm
  obtain ⟨b, hbA, hb⟩ := exists_aut_model φ γ
  let f : alternatingGroup (Fin 6) →* P10 := A6Models.psl29.subtype.comp φ.toMonoidHom
  have hfinj : Function.Injective f := Subtype.val_injective.comp φ.injective
  set Q'' : Subgroup P10 := Q.map f with hQ''
  have hQ''card : Nat.card ↥Q'' = 8 := by
    rw [hQ'', Subgroup.card_map_of_injective hfinj]
    exact hQ
  have hQ''le : Q'' ≤ A6Models.psl29 := by
    rintro _ ⟨q, -, rfl⟩
    exact (φ q).2
  have hbcomm : ∀ y ∈ Q'', b * y = y * b := by
    rintro _ ⟨q, hq, rfl⟩
    have h := hb q
    rw [hfix q hq] at h
    show b * ((φ q : ↥A6Models.psl29) : P10) = ((φ q : ↥A6Models.psl29) : P10) * b
    calc b * ((φ q : ↥A6Models.psl29) : P10)
        = (b * ((φ q : ↥A6Models.psl29) : P10) * b⁻¹) * b := by group
      _ = ((φ q : ↥A6Models.psl29) : P10) * b := by rw [← h]
  obtain ⟨g, hg, hgQ⟩ := Unc25K1.Six.exists_conj_of_card_eight (G := P10) (H := A6Models.psl29)
    (P := P0 ⊓ A6Models.psl29) (Q := Q'') inf_le_right hQ''le Out21.A6.card_D hQ''card card_psl29
  have hgA : g ∈ A6Models.autA6 := psl29_le_autA6 hg
  have hb' : g⁻¹ * b * g ∈ A6Models.autA6 :=
    A6Models.autA6.mul_mem (A6Models.autA6.mul_mem (A6Models.autA6.inv_mem hgA) hbA) hgA
  have hcD : ∀ d ∈ P0 ⊓ A6Models.psl29, (g⁻¹ * b * g) * d = d * (g⁻¹ * b * g) := by
    intro d hd
    have hmem : g * d * g⁻¹ ∈ Q'' := by
      rw [hgQ]
      exact ⟨d, hd, by simp [MulAut.conj_apply]⟩
    have h := hbcomm _ hmem
    calc g⁻¹ * b * g * d = g⁻¹ * (b * (g * d * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * d * g⁻¹) * b) * g := by rw [h]
      _ = d * (g⁻¹ * b * g) := by group
  have hsq' := sq_of_cent_D hb' hcD
  have hb2 : b * b = 1 := by
    calc b * b = g * ((g⁻¹ * b * g) * (g⁻¹ * b * g)) * g⁻¹ := by group
      _ = 1 := by rw [hsq']; group
  refine MulEquiv.ext fun k => ?_
  apply φ.injective
  apply Subtype.ext
  rw [MulAut.mul_apply, hb, hb]
  show _ = ((φ k : ↥A6Models.psl29) : P10)
  calc b * (b * ((φ k : ↥A6Models.psl29) : P10) * b⁻¹) * b⁻¹
      = (b * b) * ((φ k : ↥A6Models.psl29) : P10) * (b * b)⁻¹ := by group
    _ = _ := by rw [hb2]; group

end CFSG.EvenSporadicStandard.Fin76b.A6X
