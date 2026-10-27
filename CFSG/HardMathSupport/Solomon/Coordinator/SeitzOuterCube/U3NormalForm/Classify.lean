module

public import CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.Rank2GUClassify
public import CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three.NormalFormAux

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.U3NF

open scoped MatrixGroups
open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartTwo.KFacts
open CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner
open CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.RankTwoGU
open CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three (nonabelian_heisenberg_any)

section Closure

variable {K : Type} [Field K]

theorem mem_closure_of_mem_closure_sc {U : Subgroup (GL (Fin 3) K)} {G : Set (GL (Fin 3) K)}
    (hG : G ⊆ U) {w : GL (Fin 3) K} (hw : w ∈ Subgroup.closure (↑(sc K) ∪ G)) (hwU : w ∈ U) :
    w ∈ Subgroup.closure (G ∪ ↑(sc K ⊓ U)) := by
  have hn := sc_normal K
  rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.mem_sup_of_normal_left] at hw
  obtain ⟨s, hs, t, ht, rfl⟩ := hw
  have htU : t ∈ U := (Subgroup.closure_le U).2 hG ht
  have hsU : s ∈ U := by
    have := U.mul_mem hwU (U.inv_mem htU)
    rwa [mul_inv_cancel_right] at this
  exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inr ⟨hs, hsU⟩))
    (Subgroup.closure_mono Set.subset_union_left ht)

end Closure

section Heis

variable {p f : ℕ} {K : Type} [Field K]

theorem nonabelian_case_any (h : UnitaryFieldData p f K) (h3 : 3 ∣ p ^ f + 1)
    (A : Subgroup (GL (Fin 3) K)) (hA : A ≤ unitaryIsom3 h)
    (hS : sc K ⊓ unitaryIsom3 h ≤ A) (hcube : ∀ x ∈ A, x ^ 3 ∈ sc K)
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y * x⁻¹ * y⁻¹ ∈ sc K)
    (hrank : Nat.card (A ⧸ (sc K).subgroupOf A) = 9)
    {x₀ z₀ : GL (Fin 3) K} (hx₀ : x₀ ∈ A) (hz₀ : z₀ ∈ A) (hne : x₀ * z₀ ≠ z₀ * x₀) :
    ∃ g ∈ unitaryIsom3 h, ∃ (lam ω : Kˣ), IsPrimitiveRoot (ω : K) 3 ∧
      diagGL K 1 ω (ω ^ 2) ∈ unitaryIsom3 h ∧ monomGL K lam ∈ unitaryIsom3 h ∧
      A.map (MulAut.conj g).toMonoidHom =
        heisenbergThree K lam ω ⊓ unitaryIsom3 h := by
  have := h.finite
  have h3K := three_dvd_card_sub_one h h3
  have hσ := isUnitaryInvolution_invol h
  have hF3 := hF3_of_dvd h h3
  have hS' : sc K ≤ A ⊔ sc K := le_sup_right
  have hAA' : A ≤ A ⊔ sc K := le_sup_left
  have hcube' := sup_cube hcube
  have hcomm' := sup_comm hcomm
  have hidx' := sup_index hrank
  obtain ⟨g, lam, ω, hω, hH⟩ := nonabelian_heisenberg_any h3K (A ⊔ sc K) hS' hcube' hcomm'
    hidx' (hAA' hx₀) (hAA' hz₀) hne
  have hω3 : ω ^ 3 = 1 := Units.ext (by simpa using hω.pow_eq_one)
  have hdH : diagGL K 1 ω (ω ^ 2) ∈ heisenbergThree K lam ω :=
    Subgroup.subset_closure (by simp)
  have hmH : monomGL K lam ∈ heisenbergThree K lam ω := Subgroup.subset_closure (by simp)
  have hback : ∀ z ∈ heisenbergThree K lam ω, g⁻¹ * z * g ∈ A ⊔ sc K := by
    intro z hz
    rw [← hH] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    have : g⁻¹ * (MulAut.conj g).toMonoidHom x * g = x := by
      show g⁻¹ * (g * x * g⁻¹) * g = x
      group
    rw [this]
    exact hx
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : GL (Fin 3) K, y₀ = g⁻¹ * diagGL K 1 ω (ω ^ 2) * g := ⟨_, rfl⟩
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : GL (Fin 3) K, w₀ = g⁻¹ * monomGL K lam * g := ⟨_, rfl⟩
  have hy₀A : y₀ ∈ A ⊔ sc K := hy₀ ▸ hback _ hdH
  have hw₀A : w₀ ∈ A ⊔ sc K := hw₀ ▸ hback _ hmH
  have hy₀3 : y₀ ^ 3 = 1 := by
    have : y₀ ^ 3 = g⁻¹ * (diagGL K 1 ω (ω ^ 2)) ^ 3 * g := by
      rw [hy₀]; simpa using conj_pow (a := g⁻¹) (b := diagGL K 1 ω (ω ^ 2)) (i := 3)
    rw [this, diagHeis_cube hω3, mul_one, inv_mul_cancel]
  have hw₀3 : w₀ ^ 3 = scal lam := by
    have : w₀ ^ 3 = g⁻¹ * (monomGL K lam) ^ 3 * g := by
      rw [hw₀]; simpa using conj_pow (a := g⁻¹) (b := monomGL K lam) (i := 3)
    rw [this, monom_cube, mul_assoc, ← scal_comm lam g, inv_mul_cancel_left]
  have hyw : y₀ * w₀ = scal ω * (w₀ * y₀) := by
    have e1 : y₀ * w₀ = g⁻¹ * (diagGL K 1 ω (ω ^ 2) * monomGL K lam) * g := by
      rw [hy₀, hw₀]; group
    have e2 : w₀ * y₀ = g⁻¹ * (monomGL K lam * diagGL K 1 ω (ω ^ 2)) * g := by
      rw [hy₀, hw₀]; group
    rw [e1, e2, diag_monom lam ω hω3, ← mul_assoc g⁻¹, scal_comm ω g⁻¹]
    simp only [mul_assoc]
  obtain ⟨a_y, ha_y, c_y, hy_eq⟩ := mem_sup_sc.mp hy₀A
  obtain ⟨w₁, hw₁A, c_w, hw_eq⟩ := mem_sup_sc.mp hw₀A
  have hy₀U : y₀ ∈ unitaryIsom3 h := by
    rw [hy_eq]
    refine mul_scal_mem_of_cube h h3 (hA ha_y) c_y ?_
    rw [← hy_eq, hy₀3]
    exact one_mem _
  have hw₁U : w₁ ∈ unitaryIsom3 h := hA hw₁A
  have hyw₁ : y₀ * w₁ = scal ω * (w₁ * y₀) := by
    have e := hyw
    rw [hw_eq] at e
    have e1 : y₀ * (w₁ * scal c_w) = y₀ * w₁ * scal c_w := by rw [mul_assoc]
    have e2 : scal ω * (w₁ * scal c_w * y₀) = scal ω * (w₁ * y₀) * scal c_w := by
      rw [mul_assoc w₁, ← scal_comm c_w y₀, ← mul_assoc, ← mul_assoc, mul_assoc (scal ω)]
    rw [e1, e2] at e
    exact mul_right_cancel e
  obtain ⟨b, hb⟩ : ∃ b : Kˣ, b = lam * (c_w⁻¹) ^ 3 := ⟨_, rfl⟩
  have hw₁3 : w₁ ^ 3 = scal b := by
    have e : w₁ = w₀ * scal c_w⁻¹ := by
      rw [hw_eq, mul_assoc, ← scal_mul, mul_inv_cancel, scal_one, mul_one]
    have hcom : Commute w₀ (scal c_w⁻¹) := scal_comm c_w⁻¹ w₀
    rw [e, hcom.mul_pow, hw₀3, ← scal_pow, ← scal_mul, hb]
  obtain ⟨v, hvdef⟩ : ∃ v : Fin 3 → K,
      v = ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ (Pi.single 0 1 : Fin 3 → K) :=
    ⟨_, rfl⟩
  have hgv : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v = Pi.single 0 1 := by
    rw [hvdef, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  have hv : v ≠ 0 := by
    intro h0
    rw [h0, mulVec_zero] at hgv
    have := congrFun hgv 0
    simp at this
  have hyv : (y₀ : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v := by
    rw [hy₀, Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec, hgv,
      diagHeis_fix, hvdef]
  have hy_m : conjTr (invol h) (y₀ : Matrix (Fin 3) (Fin 3) K) * (y₀ : Matrix (Fin 3) (Fin 3) K)
      = 1 := (mem_unitaryIsom3_iff h).mp hy₀U
  have hw_m : conjTr (invol h) (w₁ : Matrix (Fin 3) (Fin 3) K) * (w₁ : Matrix (Fin 3) (Fin 3) K)
      = 1 := (mem_unitaryIsom3_iff h).mp hw₁U
  have hyw_m : (y₀ : Matrix (Fin 3) (Fin 3) K) * (w₁ : Matrix (Fin 3) (Fin 3) K) =
      Matrix.scalar (Fin 3) (ω : K) * ((w₁ : Matrix (Fin 3) (Fin 3) K) *
        (y₀ : Matrix (Fin 3) (Fin 3) K)) := by
    have := congrArg Units.val hyw₁
    simpa [Units.val_mul, coe_scal] using this
  have hw3_m : (w₁ : Matrix (Fin 3) (Fin 3) K) ^ 3 = Matrix.scalar (Fin 3) (b : K) := by
    rw [← Units.val_pow_eq_pow_val, hw₁3, coe_scal]
  obtain ⟨M, hMu, hMy, hMw⟩ := exists_unitary_normal_form hσ hF3 hω hy_m hw_m hyw_m hw3_m hv hyv
  let gM : GL (Fin 3) K := ⟨M, conjTr (invol h) M, mul_eq_one_comm.mp hMu, hMu⟩
  have hgM : gM ∈ unitaryIsom3 h := (mem_unitaryIsom3_iff h).mpr hMu
  have hgy : y₀ * gM = gM * diagGL K 1 ω (ω ^ 2) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_diagHeis]
    exact hMy
  have hgw : w₁ * gM = gM * monomGL K b := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_monomGL]
    exact hMw
  have hg'y : gM⁻¹ * y₀ * gM = diagGL K 1 ω (ω ^ 2) := by
    rw [mul_assoc, hgy, inv_mul_cancel_left]
  have hg'w : gM⁻¹ * w₁ * gM = monomGL K b := by
    rw [mul_assoc, hgw, inv_mul_cancel_left]
  have hconj : ∀ z : GL (Fin 3) K, (MulAut.conj gM⁻¹).toMonoidHom z = gM⁻¹ * z * gM := by
    intro z
    show gM⁻¹ * z * gM⁻¹⁻¹ = _
    rw [inv_inv]
  have hge : heisenbergThree K b ω ≤ (A ⊔ sc K).map (MulAut.conj gM⁻¹).toMonoidHom := by
    rw [heisenbergThree, Subgroup.closure_le]
    rintro z (hz | hz)
    · refine ⟨z, hS' hz, ?_⟩
      obtain ⟨c, rfl⟩ := mem_sc_iff.mp hz
      rw [hconj, scal_comm c, inv_mul_cancel_right]
    · rcases hz with rfl | rfl
      · exact ⟨w₁, hAA' hw₁A, by rw [hconj, hg'w]⟩
      · exact ⟨y₀, hy₀A, by rw [hconj, hg'y]⟩
  have hle : (A ⊔ sc K).map (MulAut.conj gM⁻¹).toMonoidHom ≤ heisenbergThree K b ω := by
    rintro _ ⟨x, hx, rfl⟩
    have hz : g * x * g⁻¹ ∈ heisenbergThree K lam ω := by
      rw [← hH]; exact ⟨x, hx, rfl⟩
    have hmain : ∀ z ∈ heisenbergThree K lam ω,
        (gM⁻¹ * g⁻¹) * z * (gM⁻¹ * g⁻¹)⁻¹ ∈ heisenbergThree K b ω := by
      intro z hz
      induction hz using Subgroup.closure_induction with
      | mem z hz =>
        rcases hz with hz | hz
        · obtain ⟨c, rfl⟩ := mem_sc_iff.mp hz
          rw [conj_scal]
          exact Subgroup.subset_closure (Or.inl (scal_mem_sc c))
        · rcases hz with rfl | rfl
          · have e : (gM⁻¹ * g⁻¹) * monomGL K lam * (gM⁻¹ * g⁻¹)⁻¹ = monomGL K b * scal c_w := by
              calc (gM⁻¹ * g⁻¹) * monomGL K lam * (gM⁻¹ * g⁻¹)⁻¹
                  = gM⁻¹ * (g⁻¹ * monomGL K lam * g) * gM := by group
                _ = gM⁻¹ * (w₁ * scal c_w) * gM := by rw [← hw₀, hw_eq]
                _ = (gM⁻¹ * w₁ * gM) * scal c_w := by
                    simp only [mul_assoc]
                    rw [← scal_comm c_w gM]
                _ = monomGL K b * scal c_w := by rw [hg'w]
            rw [e]
            exact (heisenbergThree K b ω).mul_mem (Subgroup.subset_closure (by simp))
              (Subgroup.subset_closure (Or.inl (scal_mem_sc _)))
          · have e : (gM⁻¹ * g⁻¹) * diagGL K 1 ω (ω ^ 2) * (gM⁻¹ * g⁻¹)⁻¹ =
                diagGL K 1 ω (ω ^ 2) := by
              calc (gM⁻¹ * g⁻¹) * diagGL K 1 ω (ω ^ 2) * (gM⁻¹ * g⁻¹)⁻¹
                  = gM⁻¹ * (g⁻¹ * diagGL K 1 ω (ω ^ 2) * g) * gM := by group
                _ = gM⁻¹ * y₀ * gM := by rw [hy₀]
                _ = _ := hg'y
            rw [e]
            exact Subgroup.subset_closure (by simp)
      | one => simp
      | mul a c _ _ ha hc =>
        have : (gM⁻¹ * g⁻¹) * (a * c) * (gM⁻¹ * g⁻¹)⁻¹ =
            ((gM⁻¹ * g⁻¹) * a * (gM⁻¹ * g⁻¹)⁻¹) * ((gM⁻¹ * g⁻¹) * c * (gM⁻¹ * g⁻¹)⁻¹) := by
          group
        rw [this]
        exact (heisenbergThree K b ω).mul_mem ha hc
      | inv a _ ha =>
        have : (gM⁻¹ * g⁻¹) * a⁻¹ * (gM⁻¹ * g⁻¹)⁻¹ =
            ((gM⁻¹ * g⁻¹) * a * (gM⁻¹ * g⁻¹)⁻¹)⁻¹ := by
          group
        rw [this]
        exact (heisenbergThree K b ω).inv_mem ha
    have := hmain _ hz
    rw [hconj]
    convert this using 1
    group
  have hmap : (A ⊔ sc K).map (MulAut.conj gM⁻¹).toMonoidHom = heisenbergThree K b ω :=
    le_antisymm hle hge
  refine ⟨gM⁻¹, inv_mem hgM, b, ω, hω, ?_, ?_, ?_⟩
  · rw [← hg'y]
    exact (unitaryIsom3 h).mul_mem
      ((unitaryIsom3 h).mul_mem ((unitaryIsom3 h).inv_mem hgM) hy₀U) hgM
  · rw [← hg'w]
    exact (unitaryIsom3 h).mul_mem
      ((unitaryIsom3 h).mul_mem ((unitaryIsom3 h).inv_mem hgM) hw₁U) hgM
  ext z
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨hle ⟨a, hAA' ha, rfl⟩, ?_⟩
    rw [hconj]
    exact (unitaryIsom3 h).mul_mem ((unitaryIsom3 h).mul_mem ((unitaryIsom3 h).inv_mem hgM)
      (hA ha)) hgM
  · rintro ⟨hzH, hzU⟩
    obtain ⟨a, haA', rfl⟩ := hge hzH
    refine ⟨a, ?_, rfl⟩
    apply mem_of_mem_sup_unitary h hA hS haA'
    rw [hconj] at hzU
    have : a = gM * (gM⁻¹ * a * gM) * gM⁻¹ := by group
    rw [this]
    exact (unitaryIsom3 h).mul_mem ((unitaryIsom3 h).mul_mem hgM hzU)
      ((unitaryIsom3 h).inv_mem hgM)

end Heis

theorem pgu3_rank_two_classify_any {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (h3 : 3 ∣ p ^ f + 1) (A : Subgroup (GL (Fin 3) K)) (hA : A ≤ unitaryIsom3 h)
    (hS : sc K ⊓ unitaryIsom3 h ≤ A) (hcube : ∀ x ∈ A, x ^ 3 ∈ sc K)
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y * x⁻¹ * y⁻¹ ∈ sc K)
    (hrank : Nat.card (A ⧸ (sc K).subgroupOf A) = 9) :
    (∃ g ∈ unitaryIsom3 h, A.map (MulAut.conj g).toMonoidHom ≤ torusThree K) ∨
    (∃ g ∈ unitaryIsom3 h, ∃ (lam ω : Kˣ), IsPrimitiveRoot (ω : K) 3 ∧
      diagGL K 1 ω (ω ^ 2) ∈ unitaryIsom3 h ∧ monomGL K lam ∈ unitaryIsom3 h ∧
      A.map (MulAut.conj g).toMonoidHom =
        Subgroup.closure ({monomGL K lam, diagGL K 1 ω (ω ^ 2)} ∪ ↑(sc K ⊓ unitaryIsom3 h))) := by
  by_cases habel : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x
  · exact Or.inl (abelian_case h h3 A hA hcube habel hrank)
  · push Not at habel
    obtain ⟨x₀, hx₀, z₀, hz₀, hne⟩ := habel
    obtain ⟨g, hg, lam, ω, hω, hD, hX, hmap⟩ :=
      nonabelian_case_any h h3 A hA hS hcube hcomm hrank hx₀ hz₀ hne
    refine Or.inr ⟨g, hg, lam, ω, hω, hD, hX, ?_⟩
    rw [hmap]
    have hGU : ({monomGL K lam, diagGL K 1 ω (ω ^ 2)} : Set (GL (Fin 3) K)) ⊆ unitaryIsom3 h := by
      rintro _ (rfl | rfl)
      · exact hX
      · exact hD
    apply le_antisymm
    · rintro w ⟨hw, hwU⟩
      refine mem_closure_of_mem_closure_sc hGU ?_ hwU
      rw [heisenbergThree] at hw
      refine (Subgroup.closure_mono ?_) hw
      rintro z (hz | hz)
      · exact Or.inl hz
      · exact Or.inr hz
    · rw [Subgroup.closure_le]
      rintro z (hz | ⟨hzs, hzU⟩)
      · exact ⟨Subgroup.subset_closure (Or.inr hz), hGU hz⟩
      · exact ⟨Subgroup.subset_closure (Or.inl hzs), hzU⟩

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.U3NF
