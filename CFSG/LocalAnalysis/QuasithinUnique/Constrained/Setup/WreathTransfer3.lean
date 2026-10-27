module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathTransfer2

public section

namespace CFSG.QuasithinUnique.Setup.Wreath

open scoped Pointwise commutatorElement
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Campbell

section Finite

variable {H : Type*} [Group H] [Finite H] {R M V W F : Subgroup H} {r : ℕ} {I : Fin r → Subgroup H}
  {Pm : Subgroup (Equiv.Perm (Fin r))} (h : WreathHyp R M V W F I Pm)

namespace WreathHyp

include h

omit [Finite H] in
theorem card_map_rho_mul (A : Subgroup H) :
    Nat.card (A.map h.rho) * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set H)) = Nat.card A := by
  have := card_map_mul_card_inf_ker h.rho A
  rwa [h.ker_rho_eq_centralizer_V] at this

omit [Finite H] in
theorem card_fixV_map_rho (A : Subgroup H) :
    Nat.card ↥(@fixV ↥W h.cg (A.map h.rho)) =
      Nat.card ↥(W ⊓ Subgroup.centralizer (A : Set H)) := by
  let _ := h.cg
  have hmap : (@fixV ↥W h.cg (A.map h.rho)).map W.subtype =
      W ⊓ Subgroup.centralizer (A : Set H) := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w.2, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
      have := congrArg (fun u : ↥W => (u : H)) (hw (h.rho a) ⟨a, ha, rfl⟩)
      simp only [h.rho_apply] at this
      show a * (w : H) = (w : H) * a
      calc a * (w : H) = (a * (w : H) * a⁻¹) * a := by group
        _ = (w : H) * a := by rw [this]
    · rintro ⟨hzW, hzc⟩
      refine ⟨⟨z, hzW⟩, ?_, rfl⟩
      rintro _ ⟨a, ha, rfl⟩
      apply Subtype.ext
      rw [h.rho_apply]
      have := Subgroup.mem_centralizer_iff.mp hzc a ha
      calc a * z * a⁻¹ = z * a * a⁻¹ := by rw [this]
        _ = z := by group
  rw [← hmap]
  exact (Subgroup.card_map_of_injective W.subtype_injective).symm

theorem card_W_mul_le {K : Subgroup H} (hK : K ≤ V) :
    Nat.card W * Nat.card K ≤ Nat.card V * Nat.card ↥(W ⊓ K) := by
  have hc : ∀ x ∈ W, ∀ y ∈ K, x * y = y * x := fun x hx y hy =>
    (isElemAbelian_iff.mp h.V_elem).1 x (h.W_le hx) y (hK hy)
  have h1 := card_sup_mul_card_inf hc
  have h2 : Nat.card ↥(W ⊔ K) ≤ Nat.card V :=
    Subgroup.card_le_of_le (sup_le h.W_le hK)
  rw [← h1]
  exact Nat.mul_le_mul_right _ h2

theorem maxElem_structure {t : ∀ i, MulAut ↥(planesIn W I i)}
    (ht : @IsCoordProduct ↥W h.cg (Fin r) (planesIn W I) h.T0 Finset.univ t)
    {A : Subgroup H} (hA : IsMaxElemAbelian R A) :
    (A ⊓ Subgroup.centralizer (V : Set H)).relIndex A =
        (V ⊓ Subgroup.centralizer (A : Set H)).relIndex V ∧
      ∃ J : Finset (Fin r), @IsCoordProduct ↥W h.cg (Fin r) (planesIn W I) (A.map h.rho) J t := by
  let _ := h.cg
  have hAR : A ≤ R := hA.1
  have hAel : CFSG.Open.IsElemAbelian 2 A := hA.2.1
  have hAρ : CFSG.Quasithin.IsElemAbelian2 (A.map h.rho) := by
    obtain ⟨hc, hp⟩ := isElemAbelian_iff.mp hAel
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hc a ha b hb]
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hp a ha, map_one]
  have hAp : ∀ a ∈ A.map h.rho, ∀ i, ∃ j, a • planesIn W I i = planesIn W I j := by
    rintro _ ⟨a, ha, rfl⟩ i
    obtain ⟨σ, -, hσ⟩ := h.image_le' a
    exact ⟨σ i, hσ i⟩
  obtain ⟨hn1, hn2, -, -, -⟩ := binary_plane_wreath_offenders h.planeFamily hAp hAρ
  set K : Subgroup H := V ⊓ Subgroup.centralizer (A : Set H) with hK
  have hKV : K ≤ V := inf_le_left
  obtain ⟨-, hact⟩ := action_inequality hA h.V_le_R h.V_elem
  have hρc := h.card_map_rho_mul A
  have hW4 := h.card_W_mul_le hKV
  have hWK : W ⊓ K = W ⊓ Subgroup.centralizer (A : Set H) := by
    rw [hK, ← inf_assoc, inf_eq_left.mpr h.W_le]
  rw [hWK] at hW4
  have hfix := h.card_fixV_map_rho A
  rw [hfix] at hn1
  have hv : 0 < Nat.card V := Nat.card_pos
  have hw : 0 < Nat.card W := Nat.card_pos
  have hc : 0 < Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set H)) := Nat.card_pos
  have hρa : 0 < Nat.card (A.map h.rho) := Nat.card_pos
  have hk : 0 < Nat.card K := Nat.card_pos
  set v := Nat.card V
  set w := Nat.card W
  set a := Nat.card A
  set c := Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set H))
  set ρa := Nat.card (A.map h.rho)
  set k := Nat.card K
  set m := Nat.card ↥(W ⊓ Subgroup.centralizer (A : Set H))
  have h1 : v ≤ ρa * k := by
    have : v * c ≤ (ρa * k) * c := by
      calc v * c ≤ a * k := hact
        _ = (ρa * c) * k := by rw [hρc]
        _ = (ρa * k) * c := by ring
    exact Nat.le_of_mul_le_mul_right this hc
  have h2 : v * w ≤ (ρa * k) * w := Nat.mul_le_mul_right w h1
  have h3 : (ρa * k) * w ≤ v * (ρa * m) := by
    calc (ρa * k) * w = ρa * (w * k) := by ring
      _ ≤ ρa * (v * m) := Nat.mul_le_mul_left ρa hW4
      _ = v * (ρa * m) := by ring
  have h4 : v * (ρa * m) ≤ v * w := Nat.mul_le_mul_left v hn1
  have e1 : v * w = v * (ρa * m) := le_antisymm (h2.trans h3) h4
  have e2 : (ρa * k) * w = v * w := le_antisymm (h3.trans h4) h2
  have hw_eq : ρa * m = w := (Nat.eq_of_mul_eq_mul_left hv e1).symm
  have hv_eq : ρa * k = v := Nat.eq_of_mul_eq_mul_right hw e2
  refine ⟨?_, ?_⟩
  · have r1 := Subgroup.relIndex_mul_card (A ⊓ Subgroup.centralizer (V : Set H)) A
    have r2 := Subgroup.relIndex_mul_card K V
    rw [inf_of_le_left inf_le_left] at r1
    rw [inf_of_le_left hKV] at r2
    have q1 : (A ⊓ Subgroup.centralizer (V : Set H)).relIndex A = ρa := by
      refine Nat.eq_of_mul_eq_mul_right hc ?_
      rw [r1]
      exact hρc.symm
    have q2 : K.relIndex V = ρa := by
      refine Nat.eq_of_mul_eq_mul_right hk ?_
      rw [r2]
      exact hv_eq.symm
    rw [q1]
    exact q2.symm
  · by_cases hbot : A.map h.rho = ⊥
    · refine ⟨∅, ?_, fun g => ?_⟩
      · intro i hi
        exact absurd hi (Finset.notMem_empty i)
      · rw [hbot, Subgroup.mem_bot]
        constructor
        · rintro rfl
          intro i
          left
          intro x
          rfl
        · intro hg
          exact eq_one_of_coordCond_empty h.planeFamily hg
    · have heq : Nat.card ↥(A.map h.rho) * Nat.card ↥(@fixV ↥W h.cg (A.map h.rho)) =
          Nat.card ↥W := by
        rw [hfix]
        exact hw_eq
      obtain ⟨J, t', -, hC⟩ := ((hn2 hbot).mp heq)
      refine ⟨J, hC.congr_family fun i hi => ?_⟩
      obtain ⟨b, hbA, hbx⟩ := hC.exists_block h.planeFamily hi
      have hbT : b ∈ h.T0 := ⟨Subgroup.map_mono hAR hbA, hC.le_baseGp hbA⟩
      rcases (ht.mem_iff b).mp hbT i with hid | ⟨-, hbt⟩
      · exfalso
        apply (hC.invol i hi).1
        refine MulEquiv.ext fun x => Subtype.ext ?_
        have := hid x
        rw [hbx x] at this
        exact this
      · refine MulEquiv.ext fun x => Subtype.ext ?_
        have := hbt x
        rw [hbx x] at this
        exact this.symm

end WreathHyp

end Finite

end CFSG.QuasithinUnique.Setup.Wreath
