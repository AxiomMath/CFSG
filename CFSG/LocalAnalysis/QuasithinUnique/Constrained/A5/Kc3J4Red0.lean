module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Frame
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4PlanBase
public import CFSG.Sporadic.J4.QT2LocFiveProofBase

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT
  CFSG.Sporadic.J4.QT2

@[expose] def FpfAt {Y : Type} [Group Y] (W : Subgroup Y) (y : Y) : Prop :=
  Nat.card W = 16 ∧ (∀ a ∈ W, ∀ b ∈ W, a * b = b * a) ∧ (∀ a ∈ W, a * a = 1) ∧
    y ∈ Subgroup.normalizer (W : Set Y) ∧ orderOf y = 5 ∧ ∀ v ∈ W, y * v = v * y → v = 1

@[expose] def FpfX0 (W : Subgroup ↥J) : Prop := FpfAt W fiveElt

@[expose] noncomputable def pentSubAt {Y : Type} [Group Y] (x v : Y) : Subgroup Y :=
  Subgroup.closure {v, x * v * x⁻¹, x ^ 2 * v * (x ^ 2)⁻¹, x ^ 3 * v * (x ^ 3)⁻¹}

@[expose] noncomputable def pentSub (v : ↥J) : Subgroup ↥J := pentSubAt fiveElt v

@[expose] def PentCand (p : Row) (v : ↥J) : Prop :=
  p ∈ Pts ∧ v ≠ 1 ∧ v * v = 1 ∧ RIn p v ∧ fiveElt • p ≠ p ∧
    ∀ k : ℕ, v • (fiveElt ^ k • p) = fiveElt ^ k • p

theorem fpfAt_map_cm {Y : Type} [Group Y] (m : Y) {W : Subgroup Y} {y : Y} (h : FpfAt W y) :
    FpfAt (W.map (cm m)) (cm m y) := by
  obtain ⟨hc, hab, hsq, hx, hx5, hfpf⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (cm_injective m)]
    exact hc
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    show m * a * m⁻¹ * (m * b * m⁻¹) = m * b * m⁻¹ * (m * a * m⁻¹)
    calc m * a * m⁻¹ * (m * b * m⁻¹) = m * (a * b) * m⁻¹ := by group
      _ = m * (b * a) * m⁻¹ := by rw [hab a ha b hb]
      _ = m * b * m⁻¹ * (m * a * m⁻¹) := by group
  · rintro _ ⟨a, ha, rfl⟩
    show m * a * m⁻¹ * (m * a * m⁻¹) = 1
    calc m * a * m⁻¹ * (m * a * m⁻¹) = m * (a * a) * m⁻¹ := by group
      _ = 1 := by rw [hsq a ha]; group
  · have e := normalizer_map_equiv_eq (MulAut.conj m) W
    change cm m y ∈ Subgroup.normalizer ((W.map (MulAut.conj m).toMonoidHom : Subgroup Y) :
      Set Y)
    rw [e]
    exact ⟨y, hx, rfl⟩
  · have h5 := (MulAut.conj m).orderOf_eq y
    rw [MulAut.conj_apply] at h5
    rw [cm_apply, h5]
    exact hx5
  · rintro _ ⟨v, hv, rfl⟩ hcomm
    have h1 : y * v = v * y := by
      have : m * y * m⁻¹ * (m * v * m⁻¹) = m * v * m⁻¹ * (m * y * m⁻¹) := hcomm
      have h2 : m * (y * v) * m⁻¹ = m * (v * y) * m⁻¹ := by
        calc m * (y * v) * m⁻¹ = m * y * m⁻¹ * (m * v * m⁻¹) := by group
          _ = m * v * m⁻¹ * (m * y * m⁻¹) := this
          _ = m * (v * y) * m⁻¹ := by group
      simpa using h2
    have := hfpf v hv h1
    rw [this]
    simp [cm_apply]

theorem smul_conj_fix' {Y X : Type*} [Group Y] [MulAction Y X] (k v : Y) {r : X}
    (h : v • (k • r) = k • r) : (k⁻¹ * v * k) • r = r := by
  calc (k⁻¹ * v * k) • r = k⁻¹ • (v • (k • r)) := by rw [mul_smul, mul_smul]
    _ = k⁻¹ • (k • r) := by rw [h]
    _ = r := inv_smul_smul k r

theorem map_cm_pentSubAt {Y : Type} [Group Y] {x k : Y} (v : Y) (hk : k * x = x * k) :
    (pentSubAt x v).map (cm k) = pentSubAt x (k * v * k⁻¹) := by
  have key : ∀ y : Y, k * y = y * k → cm k (y * v * y⁻¹) = y * (k * v * k⁻¹) * y⁻¹ := by
    intro y h
    have hky : k * y * k⁻¹ = y := by rw [h, mul_inv_cancel_right]
    rw [cm_apply]
    calc k * (y * v * y⁻¹) * k⁻¹ = (k * y * k⁻¹) * (k * v * k⁻¹) * (k * y * k⁻¹)⁻¹ := by group
      _ = y * (k * v * k⁻¹) * y⁻¹ := by rw [hky]
  have hkC : Commute k x := hk
  have h2 : k * x ^ 2 = x ^ 2 * k := (hkC.pow_right 2).eq
  have h3 : k * x ^ 3 = x ^ 3 * k := (hkC.pow_right 3).eq
  unfold pentSubAt
  rw [MonoidHom.map_closure]
  simp only [Set.image_insert_eq, Set.image_singleton]
  rw [key _ hk, key _ h2, key _ h3, cm_apply]

theorem map_cm_pentSub {k : ↥J} (hk : k * fiveElt = fiveElt * k) (v : ↥J) :
    (pentSub v).map (cm k) = pentSub (k * v * k⁻¹) :=
  map_cm_pentSubAt (Y := ↥J) (x := fiveElt) (k := k) v hk

theorem pow_mul_comm_of_comm {Y : Type} [Group Y] {x k : Y} (j : ℕ) (hk : k * x = x * k) :
    x ^ j * k = k * x ^ j := by
  have hkC : Commute k x := hk
  have hC : Commute (x ^ j) k := hkC.symm.pow_left j
  exact hC.eq

theorem pentCand_conj {p q : Row} {v k : ↥J} (hk : k * fiveElt = fiveElt * k) (hpq : p = k • q)
    (h : PentCand p v) : PentCand q (k⁻¹ * v * k) := by
  obtain ⟨hp, hv1, hsq, hR, hxp, hfix⟩ := h
  have hv'k : k * (k⁻¹ * v * k) * k⁻¹ = v := by group
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hq' : q = k⁻¹ • p := by rw [hpq, inv_smul_smul]
    rw [hq']
    exact smul_mem_pts hp
  · intro h1
    apply hv1
    rw [← hv'k, h1]
    group
  · calc k⁻¹ * v * k * (k⁻¹ * v * k) = k⁻¹ * (v * v) * k := by group
      _ = 1 := by rw [hsq]; group
  · have : RIn (k • q) (k * (k⁻¹ * v * k) * k⁻¹) := by rw [← hpq, hv'k]; exact hR
    exact (RIn_conj k q _).1 this
  · intro h1
    apply hxp
    rw [hpq]
    calc fiveElt • (k • q) = (fiveElt * k) • q := (mul_smul _ _ _).symm
      _ = (k * fiveElt) • q := by rw [hk]
      _ = k • (fiveElt • q) := mul_smul _ _ _
      _ = k • q := by rw [h1]
  · intro j
    apply smul_conj_fix' k v
    have hjk : fiveElt ^ j * k = k * fiveElt ^ j :=
      pow_mul_comm_of_comm (Y := ↥J) (x := fiveElt) (k := k) j hk
    have hc : fiveElt ^ j • (k • q) = k • (fiveElt ^ j • q) := by
      rw [← mul_smul, ← mul_smul, hjk]
    have := hfix j
    rw [hpq, hc] at this
    exact this

theorem verdict_of_two_cases (lH lN : List (Subgroup ↥J))
    (hH : ∀ V : Subgroup ↥J, FpfV V → HasCommonFixedPt V →
      ∃ V' ∈ lH, ∃ g : ↥J, V = V'.map (cm g))
    (hN : ∀ V : Subgroup ↥J, FpfV V → ¬ HasCommonFixedPt V →
      ∃ V' ∈ lN, ∃ g : ↥J, V = V'.map (cm g))
    (hd : ∀ V' ∈ lH ++ lN, ClassRad V' ∨ NoNonHBlockAt Hj V') : J4VVerdict := by
  refine verdict_of_list (lH ++ lN) (fun V hV => ?_) hd
  by_cases h : HasCommonFixedPt V
  · obtain ⟨V', hV', g, hg⟩ := hH V hV h
    exact ⟨V', List.mem_append_left _ hV', g, hg⟩
  · obtain ⟨V', hV', g, hg⟩ := hN V hV h
    exact ⟨V', List.mem_append_right _ hV', g, hg⟩

end CFSG.QuasithinUnique.A5
