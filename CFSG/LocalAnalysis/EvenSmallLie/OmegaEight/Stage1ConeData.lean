module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Orbit
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Act

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage1

open Subgroup Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar

theorem cone_snd_lt (ε : Eps) : (coneX ε).2 < 64 ∧ (coneXi ε).2 < 64 ∧ (coneY ε).2 < 64 ∧
    (coneYi ε).2 < 64 := by
  cases ε <;> decide

theorem coneCheck_spec (ε : Eps) :
    (∀ v < 64, qfB ε (affB (coneX ε) v) = qfB ε v ∧ qfB ε (affB (coneY ε) v) = qfB ε v ∧
      affB (coneXi ε) (affB (coneX ε) v) = v ∧ affB (coneX ε) (affB (coneXi ε) v) = v ∧
      affB (coneYi ε) (affB (coneY ε) v) = v ∧ affB (coneY ε) (affB (coneYi ε) v) = v) ∧
    (∀ j < 6, coneComm ε (2 ^ j) = (coneC ε).getD j 0) ∧ coneComm ε 0 = 0 ∧
      dickC (coneC ε) = true := by
  have h := (checks ε).2.2.2.2
  simp only [coneCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨fun v hv => by
    obtain ⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩ := h1 v hv
    exact ⟨a1, a2, a3, a4, a5, a6⟩, h2, h3, h4⟩

@[expose] def coneXP (ε : Eps) : Equiv.Perm V6 :=
  affPerm (coneX ε) (coneXi ε) (cone_snd_lt ε).1 (cone_snd_lt ε).2.1
    (fun v hv => ((coneCheck_spec ε).1 v hv).2.2.1)
    (fun v hv => ((coneCheck_spec ε).1 v hv).2.2.2.1)

@[expose] def coneYP (ε : Eps) : Equiv.Perm V6 :=
  affPerm (coneY ε) (coneYi ε) (cone_snd_lt ε).2.2.1 (cone_snd_lt ε).2.2.2
    (fun v hv => ((coneCheck_spec ε).1 v hv).2.2.2.2.1)
    (fun v hv => ((coneCheck_spec ε).1 v hv).2.2.2.2.2)

theorem coneXP_mem (ε : Eps) : coneXP ε ∈ affGroup ε :=
  affPerm_mem fun v hv => ((coneCheck_spec ε).1 v hv).1

theorem coneYP_mem (ε : Eps) : coneYP ε ∈ affGroup ε :=
  affPerm_mem fun v hv => ((coneCheck_spec ε).1 v hv).2.1

@[expose] def coneCommP (ε : Eps) : Equiv.Perm V6 :=
  coneXP ε * coneYP ε * (coneXP ε)⁻¹ * (coneYP ε)⁻¹

theorem coneComm_apply (ε : Eps) (v : V6) :
    coneCommP ε v = toVec 6 (coneComm ε (vecBits v)) := by
  obtain ⟨hx, hxi, hy, hyi⟩ := cone_snd_lt ε
  simp only [coneCommP, Equiv.Perm.mul_apply, coneXP, coneYP, affPerm_apply, affPerm_inv_apply]
  rw [vecBits_toVec (affB_lt _ hyi _), vecBits_toVec (affB_lt _ hxi _),
    vecBits_toVec (affB_lt _ hy _)]
  rfl

theorem coneComm_zero (ε : Eps) : coneCommP ε 0 = 0 := by
  rw [coneComm_apply, vecBits_zero, (coneCheck_spec ε).2.2.1, ← vecBits_zero, toVec_vecBits]

theorem colsF_coneComm (ε : Eps) : colsF (coneCommP ε) = coneC ε := by
  have hlen : (coneC ε).length = 6 := by cases ε <;> rfl
  apply List.ext_getElem (by rw [colsF_length, hlen])
  intro j hj _
  rw [colsF_length] at hj
  have h1 := colsF_getD (coneCommP ε) hj
  rw [List.getD_eq_getElem _ _ (by rw [colsF_length]; exact hj)] at h1
  have hj64 : 2 ^ j < 64 :=
    calc 2 ^ j < 2 ^ 6 := Nat.pow_lt_pow_right (by norm_num) hj
      _ = 64 := rfl
  have hc64 : coneComm ε (2 ^ j) < 64 := affB_lt _ (cone_snd_lt ε).1 _
  rw [h1, coneComm_apply, basisVec, vecBits_toVec hj64, vecBits_toVec hc64,
    (coneCheck_spec ε).2.1 j hj, List.getD_eq_getElem _ 0 (hlen ▸ hj)]

theorem dickCheck_spec (ε : Eps) {C : List ℕ} (hC : C ∈ oCols ε) (hd : dickC C = false)
    {i : ℕ} (hi : i < 6) : dickC (C.map (bmulVec 6 6 (genRows ε i))) = false ∧
      dickC (C.map (bmulVec 6 6 (genInvRows ε i))) = false := by
  have h := (checks ε).2.2.2.1
  simp only [dickCheck, List.all_eq_true, Bool.or_eq_true, List.mem_range, Bool.and_eq_true,
    Bool.not_eq_true'] at h
  exact ((h C hC).resolve_left (by simp [hd])) i hi

theorem colsF_mulVec (A : Array ℕ) (f : V6 → V6) :
    colsF (fun v => toMat 6 6 A *ᵥ f v) = (colsF f).map (bmulVec 6 6 A) := by
  simp [colsF, vecBits_mulVec]

theorem dickC_id : dickC (colsF id) = false := by
  have : colsF id = [1, 2, 4, 8, 16, 32] := by
    simp only [colsF, id]
    simp [List.range_succ, vecBits_basisVec]
  rw [this]
  decide

variable {G : Type*} [Group G]

namespace RadicalData

variable {ε : Eps} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G} {p : Fin 6 → G}
  (hR : RadicalData ε L U Q P a ψ p)
include hR

theorem lin_p_inv (i : Fin 6) (w : V6) : lin ψ (p i)⁻¹ w = genInvMat ε i *ᵥ w := by
  have h1 : lin ψ (p i) (lin ψ (p i)⁻¹ w) = lin ψ (p i) (genInvMat ε i *ᵥ w) := by
    rw [hR.lin_inv (hR.p_mem_normalizer i), hR.lin_p, mulVec_mulVec, genMat_mul_genInvMat,
      one_mulVec]
  have hinj : Function.Injective (lin ψ (p i)) := fun x y h => by
    rw [← hR.lin_inv' (hR.p_mem_normalizer i) x, h, hR.lin_inv' (hR.p_mem_normalizer i)]
  exact hinj h1

theorem closure_le_P : closure ((Q : Set G) ∪ Set.range p) ≤ P := by
  rw [closure_le]
  rintro x (hx | ⟨i, rfl⟩)
  · exact hR.U_le_P (hR.Q_le_U hx)
  · exact hR.p_mem i

theorem colsF_lin_mem_oCols {x : G} (hx : x ∈ P) : colsF (lin ψ x) ∈ oCols ε :=
  colsOf_mem_oCols (σ := hR.linHom ⟨x, hR.P_le_normalizer hx⟩)
    ⟨hR.linHom_mem_linGroup _, fun v => hR.qfV_lin hx v⟩

theorem dickC_colsF_lin {x : G} (hx : x ∈ P) : dickC (colsF (lin ψ x)) = false := by
  have hxP := hR.P_le hx
  induction hxP using closure_induction_left with
  | one =>
    have : lin ψ 1 = id := funext hR.lin_one
    rw [this]
    exact dickC_id
  | mul_left s hs y hy ih =>
    have hyP : y ∈ P := hR.closure_le_P hy
    have hsP : s ∈ P := hR.closure_le_P (subset_closure hs)
    rcases hs with hs | ⟨i, rfl⟩
    · have : lin ψ (s * y) = lin ψ y := funext fun v => by
        rw [hR.lin_mul (le_normalizer hs) (hR.P_le_normalizer hyP), hR.lin_of_mem_Q hs]
      rw [this]
      exact ih hyP
    · have : lin ψ (p i * y) = fun v => toMat 6 6 (genRows ε i) *ᵥ lin ψ y v := funext fun v => by
        rw [hR.lin_mul (hR.p_mem_normalizer i) (hR.P_le_normalizer hyP), hR.lin_p]
        rfl
      rw [this, colsF_mulVec]
      exact (dickCheck_spec ε (hR.colsF_lin_mem_oCols hyP) (ih hyP) i.isLt).1
  | inv_mul_cancel s hs y hy ih =>
    have hyP : y ∈ P := hR.closure_le_P hy
    rcases hs with hs | ⟨i, rfl⟩
    · have : lin ψ (s⁻¹ * y) = lin ψ y := funext fun v => by
        rw [hR.lin_mul (le_normalizer (inv_mem hs)) (hR.P_le_normalizer hyP),
          hR.lin_of_mem_Q (inv_mem hs)]
      rw [this]
      exact ih hyP
    · have : lin ψ ((p i)⁻¹ * y) = fun v => toMat 6 6 (genInvRows ε i) *ᵥ lin ψ y v :=
        funext fun v => by
          rw [hR.lin_mul (inv_mem (hR.p_mem_normalizer i)) (hR.P_le_normalizer hyP),
            hR.lin_p_inv]
          rfl
      rw [this, colsF_mulVec]
      exact (dickCheck_spec ε (hR.colsF_lin_mem_oCols hyP) (ih hyP) i.isLt).2

end RadicalData

end CFSG.EvenSmallLie.OmegaEight.Stage1
