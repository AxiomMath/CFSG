module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25V1

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25R.AE5X

open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open Certificates.AE117 Certificates.AE5Sq Certificates.AE5X
open CFSG.ClassicalInvolution.Q8P.Asc77.P25R.AE5Sq (finAll_iff mem_alphas card_of_mem_alphas ord4Pi_iff
  mkQ_mem_aeModel)

@[expose] def IsI18 (p q : Lab) (x : AEQ 5) : Prop :=
  (∃ m ∈ memL p, ∃ m' ∈ memL q, mkQ 5 (m * m') = x) ∧ x ≠ 1 ∧ x * x = 1 ∧ x ≠ mkQ 5 (zW p)

@[expose] def NormGen (p q : Lab) (u : AEQ 5) : Prop :=
  ∀ g ∈ memL p ++ memL q, ∃ m ∈ memL p, ∃ m' ∈ memL q, u * mkQ 5 g * u⁻¹ = mkQ 5 (m * m')

theorem inV_iff (x : Wr 5) : inV x = true ↔ InV (mkQ 5 x) := by
  simp only [inV, decide_eq_true_eq]
  exact Iff.rfl

theorem mem_prodL {p q : Lab} {y : Wr 5} : y ∈ prodL p q ↔ ∃ m ∈ memL p, ∃ m' ∈ memL q, m * m' = y := by
  simp [prodL, List.mem_flatMap, List.mem_map]

theorem inv18With_iff {p q : Lab} {x : Wr 5} :
    inv18With (prodL p q) (zW p) x = true ↔ IsI18 p q (mkQ 5 x) := by
  simp only [inv18With, IsI18, Bool.and_eq_true, List.any_eq_true, Bool.not_eq_true',
    TL4.Mdl117.eqPi_iff, mem_prodL]
  have h1 : inPi x = false ↔ mkQ 5 x ≠ 1 := by
    rw [Bool.eq_false_iff, Ne, TL4.Mdl117.inPi_iff]
  have h2 : inPi (x * x) = true ↔ mkQ 5 x * mkQ 5 x = 1 := by
    rw [TL4.Mdl117.inPi_iff, map_mul]
  have h3 : eqPi x (zW p) = false ↔ mkQ 5 x ≠ mkQ 5 (zW p) := by
    rw [Bool.eq_false_iff, Ne, TL4.Mdl117.eqPi_iff]
  rw [h1, h2, h3]
  constructor
  · rintro ⟨⟨⟨⟨y, ⟨m, hm, m', hm', rfl⟩, hxy⟩, hx1⟩, hx2⟩, hx3⟩
    exact ⟨⟨m, hm, m', hm', hxy.symm⟩, hx1, hx2, hx3⟩
  · rintro ⟨⟨m, hm, m', hm', hxy⟩, hx1, hx2, hx3⟩
    exact ⟨⟨⟨⟨m * m', ⟨m, hm, m', hm', rfl⟩, hxy.symm⟩, hx1⟩, hx2⟩, hx3⟩

theorem mem_L18 {p q : Lab} {x : Wr 5} : x ∈ L18 p q ↔ x ∈ prodL p q ∧ IsI18 p q (mkQ 5 x) := by
  simp only [L18, List.mem_filter, inv18With_iff]

theorem exists_L18 {p q : Lab} {x : AEQ 5} (hx : IsI18 p q x) : ∃ x' ∈ L18 p q, mkQ 5 x' = x := by
  obtain ⟨⟨m, hm, m', hm', hmm'⟩, hx1, hx2, hx3⟩ := hx
  refine ⟨m * m', mem_L18.2 ⟨mem_prodL.2 ⟨m, hm, m', hm', rfl⟩, ?_⟩, hmm'⟩
  rw [hmm']
  exact ⟨⟨m, hm, m', hm', hmm'⟩, hx1, hx2, hx3⟩

theorem chkA1_spec {p q : Lab} (h : chkA1 p q = true) :
    (∃ x, IsI18 p q x ∧ InV x) ∧ (∃ x, IsI18 p q x ∧ ¬ InV x) := by
  simp only [chkA1, Bool.and_eq_true, List.any_eq_true] at h
  obtain ⟨⟨x, hx, hxv⟩, ⟨y, hy, hyv⟩⟩ := h
  refine ⟨⟨mkQ 5 x, (mem_L18.1 hx).2, (inV_iff x).1 hxv⟩, ⟨mkQ 5 y, (mem_L18.1 hy).2, ?_⟩⟩
  rw [Bool.not_eq_true'] at hyv
  intro hv
  have := (inV_iff y).2 hv
  rw [hyv] at this
  exact absurd this (by simp)

theorem aeModel_of_isAE {w : Wr 5} (h : isAE w = true) : mkQ 5 w ∈ TL4.aeModel 5 := by
  simp only [isAE, Bool.and_eq_true, decide_eq_true_eq] at h
  refine mkQ_mem_aeModel ?_ ?_
  · simp only [evenFin5, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h.1
  · simp only [a5Fin, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h.2

theorem normGen_of_normG {p q : Lab} {w : Wr 5} (h : normG p q w = true) : NormGen p q (mkQ 5 w) := by
  intro g hg
  simp only [normG, List.all_eq_true, List.any_eq_true] at h
  obtain ⟨y, hy, hyg⟩ := h g hg
  obtain ⟨m, hm, m', hm', rfl⟩ := mem_prodL.1 hy
  refine ⟨m, hm, m', hm', ?_⟩
  have := (TL4.Mdl117.eqPi_iff _ _).1 hyg
  simpa [map_mul, map_inv] using this

theorem normG_of_normGen {p q : Lab} {w : Wr 5} (h : NormGen p q (mkQ 5 w)) : normG p q w = true := by
  simp only [normG, List.all_eq_true, List.any_eq_true]
  intro g hg
  obtain ⟨m, hm, m', hm', hmm'⟩ := h g hg
  refine ⟨m * m', mem_prodL.2 ⟨m, hm, m', hm', rfl⟩, ?_⟩
  rw [TL4.Mdl117.eqPi_iff]
  simpa [map_mul, map_inv] using hmm'

theorem chkA2_spec {p q : Lab} (h : chkA2 p q = true) (v : Bool) :
    ∃ x₀, IsI18 p q x₀ ∧ (InV x₀ ↔ v = true) ∧ ∀ x', IsI18 p q x' → (InV x' ↔ v = true) →
      ∃ u ∈ TL4.aeModel 5, NormGen p q u ∧ u * mkQ 5 (zW p) * u⁻¹ = mkQ 5 (zW p) ∧
        u * x₀ * u⁻¹ = x' := by
  simp only [chkA2, List.all_eq_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
    Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
  have hv : v ∈ [true, false] := by cases v <;> simp
  obtain ⟨x₀, hx₀L, ⟨hx₀v, hall⟩⟩ := h v hv
  refine ⟨mkQ 5 x₀, (mem_L18.1 hx₀L).2, ?_, ?_⟩
  · rw [← inV_iff, hx₀v]
  · intro x' hx' hx'v
    obtain ⟨x'', hx''L, rfl⟩ := exists_L18 hx'
    have hv'' : inV x'' = v := by
      cases v
      · rw [Bool.eq_false_iff, Ne, inV_iff]
        intro hh
        exact absurd (hx'v.1 hh) (by simp)
      · exact (inV_iff x'').2 (hx'v.2 rfl)
    rcases hall x'' hx''L with hne | ⟨w, hw, hwe⟩
    · exact absurd hv'' hne
    · simp only [nrm, Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true] at hw
      obtain ⟨⟨hAE, hz⟩, hN⟩ := hw
      refine ⟨mkQ 5 w, aeModel_of_isAE hAE, normGen_of_normG hN, ?_, ?_⟩
      · have := (TL4.Mdl117.eqPi_iff _ _).1 hz
        simpa [map_mul, map_inv] using this
      · have := (TL4.Mdl117.eqPi_iff _ _).1 hwe
        simpa [map_mul, map_inv] using this

theorem chkA3_spec {p q : Lab} (h : chkA3 p q = true) :
    ∃ u ∈ TL4.aeModel 5, ∃ s : AEQ 5, s = u * mkQ 5 (zW p) * u⁻¹ ∧
      (∀ m ∈ memL p, ∃ m' ∈ memL q, s * mkQ 5 m * s⁻¹ = mkQ 5 m') ∧
      (∀ m' ∈ memL q, ∃ m ∈ memL p, s * mkQ 5 m' * s⁻¹ = mkQ 5 m) ∧ s ≠ mkQ 5 (zW p) ∧
      (∃ l ∈ labs, ∃ m ∈ memL l, mkQ 5 m * mkQ 5 m ≠ 1 ∧
        mkQ 5 m * mkQ 5 m * (mkQ 5 m * mkQ 5 m) = 1 ∧
        s * mkQ 5 (zW p) * mkQ 5 m = mkQ 5 m * (s * mkQ 5 (zW p))) ∧
      ∀ c : AEQ 5, c * mkQ 5 (zW p) * c⁻¹ ≠ s * mkQ 5 (zW p) := by
  simp only [chkA3, decide_eq_true_eq] at h
  obtain ⟨w, -, hw⟩ := h
  simp only [swapOK, Bool.and_eq_true] at hw
  obtain ⟨⟨⟨⟨⟨hAE, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := hw
  have hs : mkQ 5 (w * zW p * w⁻¹) = mkQ 5 w * mkQ 5 (zW p) * (mkQ 5 w)⁻¹ := by
    simp [map_mul, map_inv]
  refine ⟨mkQ 5 w, aeModel_of_isAE hAE, mkQ 5 (w * zW p * w⁻¹), hs, ?_, ?_, ?_, ?_, ?_⟩
  · intro m hm
    obtain ⟨m', hm', he⟩ := List.any_eq_true.1 (List.all_eq_true.1 h1 m hm)
    refine ⟨m', hm', ?_⟩
    have := (TL4.Mdl117.eqPi_iff _ _).1 he
    simpa [map_mul, map_inv] using this
  · intro m' hm'
    obtain ⟨m, hm, he⟩ := List.any_eq_true.1 (List.all_eq_true.1 h2 m' hm')
    refine ⟨m, hm, ?_⟩
    have := (TL4.Mdl117.eqPi_iff _ _).1 he
    simpa [map_mul, map_inv] using this
  · intro he
    rw [Bool.not_eq_true'] at h3
    have := (TL4.Mdl117.eqPi_iff _ _).2 he
    rw [this] at h3
    exact absurd h3 (by simp)
  · obtain ⟨l, hl, hm⟩ := List.any_eq_true.1 h4
    obtain ⟨m, hm, hm'⟩ := List.any_eq_true.1 hm
    rw [Bool.and_eq_true] at hm'
    obtain ⟨ho, he⟩ := hm'
    refine ⟨l, hl, m, hm, ?_⟩
    obtain ⟨o1, o2⟩ := (ord4Pi_iff m).1 ho
    refine ⟨o1, o2, ?_⟩
    have := (TL4.Mdl117.eqPi_iff _ _).1 he
    simpa [map_mul, map_inv] using this
  · intro c hc
    obtain ⟨c', rfl⟩ := QuotientGroup.mk_surjective c
    have := finAll_iff.1 h5 c' (Finset.mem_univ c')
    rw [Bool.not_eq_true'] at this
    have h6 : eqPi (c' * zW p * c'⁻¹) (w * zW p * w⁻¹ * zW p) = true := by
      rw [TL4.Mdl117.eqPi_iff]
      simpa [map_mul, map_inv] using hc
    rw [h6] at this
    exact absurd this (by simp)

theorem chkA5_spec {p q : Lab} (h : chkA5 p q = true) (c : AEQ 5)
    (hc2a : c * c * mkQ 5 (a0 ()) = mkQ 5 (a0 ()) * (c * c))
    (hc2b : c * c * mkQ 5 (b0 ()) = mkQ 5 (b0 ()) * (c * c)) (hN : NormGen p q c)
    (hexc : ∀ l ∈ labs, ∀ m ∈ memL l, mkQ 5 m * mkQ 5 m ≠ 1 →
      mkQ 5 m * mkQ 5 m * (mkQ 5 m * mkQ 5 m) = 1 → c * mkQ 5 m * c⁻¹ ≠ mkQ 5 m) :
    (∃ x, IsI18 p q x ∧ InV x ∧ c * x * c⁻¹ ≠ x) ∧ (∃ x, IsI18 p q x ∧ ¬ InV x ∧ c * x * c⁻¹ ≠ x) := by
  obtain ⟨c', rfl⟩ := QuotientGroup.mk_surjective c
  have hc := finAll_iff.1 h c' (Finset.mem_univ c')
  have e1 : eqPi (c' * c' * a0 ()) (a0 () * (c' * c')) = true := by
    rw [TL4.Mdl117.eqPi_iff]; simpa [map_mul] using hc2a
  have e2 : eqPi (c' * c' * b0 ()) (b0 () * (c' * c')) = true := by
    rw [TL4.Mdl117.eqPi_iff]; simpa [map_mul] using hc2b
  have e3 : normG p q c' = true := normG_of_normGen hN
  have e4 : excOK c' = true := by
    simp only [excOK, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true']
    intro l hl m hm
    by_cases ho : ord4Pi m = true
    · right
      rw [Bool.eq_false_iff, Ne, TL4.Mdl117.eqPi_iff]
      obtain ⟨o1, o2⟩ := (ord4Pi_iff m).1 ho
      simpa [map_mul, map_inv] using hexc l hl m hm o1 o2
    · left
      simpa using ho
  rw [e1, e2, e3, e4] at hc
  simp only [Bool.and_self, Bool.not_true, Bool.false_or, Bool.and_eq_true, List.any_eq_true,
    Bool.not_eq_true'] at hc
  obtain ⟨⟨x, hx, hxv, hxe⟩, ⟨y, hy, hyv, hye⟩⟩ := hc
  refine ⟨⟨mkQ 5 x, (mem_L18.1 hx).2, (inV_iff x).1 hxv, ?_⟩, ⟨mkQ 5 y, (mem_L18.1 hy).2, ?_, ?_⟩⟩
  · intro he
    have h2 : eqPi (c' * x * c'⁻¹) x = true := by
      rw [TL4.Mdl117.eqPi_iff]; simpa [map_mul, map_inv] using he
    rw [hxe] at h2
    exact absurd h2 (by simp)
  · intro hv
    have := (inV_iff y).2 hv
    rw [hyv] at this
    exact absurd this (by simp)
  · intro he
    have h2 : eqPi (c' * y * c'⁻¹) y = true := by
      rw [TL4.Mdl117.eqPi_iff]; simpa [map_mul, map_inv] using he
    rw [hye] at h2
    exact absurd h2 (by simp)

theorem twin_of_comm {α α' : Finset (Fin 5)} (hα : α.card = 4) (hα' : α'.card = 4) {b b' : Bool}
    (hc : ∀ x ∈ memBar α hα b, ∀ y ∈ memBar α' hα' b', x * y = y * x) :
    twin (α, b) (α', b') = true := by
  simp only [twin, List.all_eq_true]
  intro m hm m' hm'
  rw [TL4.Mdl117.eqPi_iff, map_mul, map_mul]
  exact hc _ ((TL4.Mdl117.mem_memBar_iff α hα b _).2 ⟨m, hm, rfl⟩) _
    ((TL4.Mdl117.mem_memBar_iff α' hα' b' _).2 ⟨m', hm', rfl⟩)

section Facts


theorem twin_facts {α α' : Finset (Fin 5)} (hα : α.card = 4) (hα' : α'.card = 4) {b b' : Bool}
    (hc : ∀ x ∈ memBar α hα b, ∀ y ∈ memBar α' hα' b', x * y = y * x) :
    chkA1 (α, b) (α', b') = true ∧ chkA2 (α, b) (α', b') = true ∧ chkA3 (α, b) (α', b') = true ∧
      chkA5 (α, b) (α', b') = true := by
  have h := check_parts.2.2.2.2 _ (mem_labs hα b) _ (mem_labs hα' b') (twin_of_comm hα hα' hc)
  simp only [chkTwin, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h5⟩

end Facts

theorem NormGen.mem_sup {α α' : Finset (Fin 5)} {hα : α.card = 4} {hα' : α'.card = 4} {b b' : Bool}
    {u : AEQ 5} (hu : NormGen (α, b) (α', b') u) :
    ∀ x ∈ memBar α hα b ⊔ memBar α' hα' b', u * x * u⁻¹ ∈ memBar α hα b ⊔ memBar α' hα' b' := by
  set H := memBar α hα b ⊔ memBar α' hα' b' with hH
  have hmem : ∀ g ∈ memL (α, b) ++ memL (α', b'), u * mkQ 5 g * u⁻¹ ∈ H := by
    intro g hg
    obtain ⟨m, hm, m', hm', he⟩ := hu g hg
    rw [he, map_mul]
    exact Subgroup.mul_mem_sup ((TL4.Mdl117.mem_memBar_iff α hα b _).2 ⟨m, hm, rfl⟩)
      ((TL4.Mdl117.mem_memBar_iff α' hα' b' _).2 ⟨m', hm', rfl⟩)
  have h1 : memBar α hα b ≤ H.comap (MulAut.conj u).toMonoidHom := by
    intro x hx
    obtain ⟨m, hm, rfl⟩ := (TL4.Mdl117.mem_memBar_iff α hα b x).1 hx
    simpa only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
      hmem m (List.mem_append_left _ hm)
  have h2 : memBar α' hα' b' ≤ H.comap (MulAut.conj u).toMonoidHom := by
    intro x hx
    obtain ⟨m, hm, rfl⟩ := (TL4.Mdl117.mem_memBar_iff α' hα' b' x).1 hx
    simpa only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
      hmem m (List.mem_append_right _ hm)
  intro x hx
  have := sup_le h1 h2 hx
  simpa only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using this

end CFSG.ClassicalInvolution.Q8P.Asc77.P25R.AE5X
