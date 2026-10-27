module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveOmeX
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveZetMain

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix
open CFSG.LocalAnalysis.ComponentInitial (LinearFlag.unitriangular)

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F]
variable {N W₁ W₂ S₀ : Subgroup G} {p : G → SpecialLinearGroup (Fin 4) F} {b : G → Fin 4 → F}

theorem IsFieldModuleData.seitzLeviX_eq_leviPre (h : IsFieldModuleData N W₁ S₀ p b)
    (hF : Nat.card F = 4) (hW₂S₀ : W₂ ≤ S₀) (hS₀W₂ : S₀ ≤ normalizer (W₂ : Set G))
    (hW₂c : Nat.card W₂ = 2 ^ 8) (hZ : Nat.card (W₁ ⊓ W₂ : Subgroup G) ≤ 4)
    (hXN : seitzLeviX W₁ W₂ ≤ N)
    (hP3 : CFSG.Quasithin.perfectCore (N ⊓ normalizer ((W₁ ⊔ W₂ : Subgroup G) : Set G)) ≤
      normalizer (W₂ : Set G)) :
    seitzLeviX W₁ W₂ = h.leviPre := by
  have hXp : ⁅seitzLeviX W₁ W₂, seitzLeviX W₁ W₂⁆ = seitzLeviX W₁ W₂ :=
    CFSG.Quasithin.perfectCore_perfect _
  have hYp := h.commutator_leviPre hF
  refine le_antisymm (fun x hx => ?_) ?_
  ·
    have hXZ : ∀ y ∈ seitzLeviX W₁ W₂, ∀ z ∈ W₁ ⊓ W₂, y * z * y⁻¹ ∈ W₁ ⊓ W₂ :=
      fun y hy z hz => mem_inf.2
        ⟨(mem_normalizer_iff.1 (seitzLeviX_le_normalizer_left W₁ W₂ hy) z).1 (mem_inf.1 hz).1,
          (mem_normalizer_iff.1 (seitzLeviX_le_normalizer_right W₁ W₂ hy) z).1
            (mem_inf.1 hz).2⟩
    have hrow : ∀ y ∈ seitzLeviX W₁ W₂, ∀ j : Fin 3,
        (p y : Matrix (Fin 4) (Fin 4) F) (Fin.last 3) j.castSucc = 0 :=
      fun y hy => h.lastRow_of_conj hF hW₂S₀ hS₀W₂ hW₂c hZ (hXN hy) (hXZ y hy)
    let χ : seitzLeviX W₁ W₂ →* F :=
      { toFun := fun y => (p y : Matrix (Fin 4) (Fin 4) F) (Fin.last 3) (Fin.last 3)
        map_one' := by
          change (p 1 : Matrix (Fin 4) (Fin 4) F) (Fin.last 3) (Fin.last 3) = 1
          rw [h.map_one, Matrix.SpecialLinearGroup.coe_one, one_apply_eq]
        map_mul' := fun y z => by
          change (p (y * z : G) : Matrix (Fin 4) (Fin 4) F) (Fin.last 3) (Fin.last 3) = _
          rw [h.map_mul _ (hXN y.2) _ (hXN z.2), Matrix.SpecialLinearGroup.coe_mul,
            mul_apply_last_last (hrow y y.2)] }
    have hχ := congrArg Units.val (eq_one_of_commutator_eq_self hXp χ.toHomUnits ⟨x, hx⟩)
    exact ⟨hXN hx, hrow x hx, hχ⟩
  · refine CFSG.Quasithin.le_perfectCore_of_perfect (le_inf (fun y hy => h.le_normalizer hy.1)
      ?_) hYp
    refine le_trans ?_ hP3
    refine CFSG.Quasithin.le_perfectCore_of_perfect (le_inf (fun y hy => hy.1) ?_) hYp
    refine le_normalizer_of_forall_conj_mem fun y hy g hg => ?_
    have hgN : g ∈ N := (sup_le h.wOne_le (hW₂S₀.trans h.sZero_le)) hg
    have hgc := (h.mem_sup_iff hF hW₂S₀ hS₀W₂ hW₂c hZ hgN).1 hg
    have hygN : y * g * y⁻¹ ∈ N := mul_mem (mul_mem hy.1 hgN) (inv_mem hy.1)
    rw [h.mem_sup_iff hF hW₂S₀ hS₀W₂ hW₂c hZ hygN, h.map_mul _ (mul_mem hy.1 hgN) _ (inv_mem hy.1),
      h.map_mul _ hy.1 _ hgN, h.map_inv hy.1]
    exact isColRadical_conj hy.2 hgc

theorem exists_leviData_of_fieldModule [CharP F 2] (hF : Nat.card F = 4)
    (h : IsFieldModuleData N W₁ S₀ p b) (hW₂S₀ : W₂ ≤ S₀) (hS₀W₂ : S₀ ≤ normalizer (W₂ : Set G))
    (hW₂c : Nat.card W₂ = 2 ^ 8) (hZ : Nat.card (W₁ ⊓ W₂ : Subgroup G) ≤ 4)
    (hXN : seitzLeviX W₁ W₂ ≤ N)
    (hP3 : CFSG.Quasithin.perfectCore (N ⊓ normalizer ((W₁ ⊔ W₂ : Subgroup G) : Set G)) ≤
      normalizer (W₂ : Set G))
    {t : G} {σ : F →+* F} (hσ : ∀ x, σ x = x ^ 2) {c : SpecialLinearGroup (Fin 4) F}
    (hpt : ∀ x ∈ N, t * x * t⁻¹ ∈ N → (p (t * x * t⁻¹) : Matrix (Fin 4) (Fin 4) F) =
      (c : Matrix (Fin 4) (Fin 4) F) * (p x : Matrix (Fin 4) (Fin 4) F).map σ *
        ((c⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))
    (hbt : ∀ w ∈ W₁, b (t * w * t⁻¹) =
      (fun k => σ (b w k)) ᵥ* ((c⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))
    (htW₁ : ∀ w ∈ W₁, t * w * t⁻¹ ∈ W₁) (htW₂ : ∀ w ∈ W₂, t * w * t⁻¹ ∈ W₂) :
    ∃ φ : seitzLeviX W₁ W₂ →* SpecialLinearGroup (Fin 3) F,
      Function.Surjective φ ∧
      (∀ x, φ x = 1 ↔ (x : G) ∈ W₁ ⊔ W₂) ∧
      S₀ ≤ seitzLeviX W₁ W₂ ∧
      (∃ B : GL (Fin 3) F, ∀ x : seitzLeviX W₁ W₂, ∀ hx : t * x * t⁻¹ ∈ seitzLeviX W₁ W₂,
        ((φ ⟨t * x * t⁻¹, hx⟩ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
          (B : Matrix (Fin 3) (Fin 3) F) *
            (φ x : Matrix (Fin 3) (Fin 3) F).map (frobenius F 2) *
              ((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) ∧
      (∃ μ₁ : G → Fin 3 → F,
        (∀ w ∈ W₁, ∀ w' ∈ W₁, μ₁ (w * w') = μ₁ w + μ₁ w') ∧ (∀ v, ∃ w ∈ W₁, μ₁ w = v) ∧
        (∀ w ∈ W₁, μ₁ w = 0 ↔ w ∈ W₂) ∧
        ∀ x : seitzLeviX W₁ W₂, ∀ w ∈ W₁,
          μ₁ ((x : G) * w * (x : G)⁻¹) =
            (((φ x)⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ μ₁ w) ∧
      (∃ μ₂ : G → Fin 3 → F,
        (∀ w ∈ W₂, ∀ w' ∈ W₂, μ₂ (w * w') = μ₂ w + μ₂ w') ∧
        (∀ w ∈ W₂, μ₂ w = 0 ↔ w ∈ W₁) ∧
        ∀ x : seitzLeviX W₁ W₂, ∀ w ∈ W₂,
          μ₂ ((x : G) * w * (x : G)⁻¹) =
            ((φ x : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ μ₂ w) := by
  have hXY := h.seitzLeviX_eq_leviPre hF hW₂S₀ hS₀W₂ hW₂c hZ hXN hP3
  have hXQ : ∀ x ∈ seitzLeviX W₁ W₂, x ∈ N ∧ p x ∈ leviQ F := fun x hx => by
    rw [hXY] at hx
    exact hx
  have hW₂N : W₂ ≤ N := hW₂S₀.trans h.sZero_le
  have hcol := fun {w : G} (hw : w ∈ W₂) => h.isColRadical hF hW₂S₀ hS₀W₂ hZ hw
  obtain ⟨-, -, hall⟩ := h.wTwo_count hF hW₂S₀ hS₀W₂ hW₂c hZ
  let φ : seitzLeviX W₁ W₂ →* SpecialLinearGroup (Fin 3) F :=
    { toFun := fun x => ⟨(p x : Matrix (Fin 4) (Fin 4) F).submatrix Fin.castSucc Fin.castSucc,
        det_leviBlock (hXQ x x.2).2⟩
      map_one' := Subtype.ext (by
        change (p 1 : Matrix (Fin 4) (Fin 4) F).submatrix Fin.castSucc Fin.castSucc = 1
        rw [h.map_one, Matrix.SpecialLinearGroup.coe_one, submatrix_castSucc_one])
      map_mul' := fun x y => Subtype.ext (by
        change (p (x * y : G) : Matrix (Fin 4) (Fin 4) F).submatrix Fin.castSucc Fin.castSucc =
          (p x : Matrix (Fin 4) (Fin 4) F).submatrix Fin.castSucc Fin.castSucc *
            (p y : Matrix (Fin 4) (Fin 4) F).submatrix Fin.castSucc Fin.castSucc
        rw [h.map_mul _ (hXQ x x.2).1 _ (hXQ y y.2).1]
        exact leviBlock_mul (hXQ y y.2).2) }
  have hφ : ∀ x : seitzLeviX W₁ W₂, ((φ x : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = (p x : Matrix (Fin 4) (Fin 4) F).submatrix Fin.castSucc
        Fin.castSucc := fun x => rfl
  refine ⟨φ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro A
    obtain ⟨y, hyN, hy⟩ := h.surj (leviEmbed F A)
    have hyX : y ∈ seitzLeviX W₁ W₂ := by
      rw [hXY]
      exact ⟨hyN, hy ▸ leviEmbed_mem_leviQ A⟩
    refine ⟨⟨y, hyX⟩, Subtype.ext ?_⟩
    rw [hφ]
    change (p y : Matrix (Fin 4) (Fin 4) F).submatrix Fin.castSucc Fin.castSucc = _
    rw [hy, leviBlock_leviEmbed]
  ·
    intro x
    rw [h.mem_sup_iff hF hW₂S₀ hS₀W₂ hW₂c hZ (hXQ x x.2).1]
    constructor
    · intro hx1
      refine isColRadical_of_mem_leviQ (hXQ x x.2).2 ?_
      rw [← hφ, hx1, Matrix.SpecialLinearGroup.coe_one]
    · intro hxc
      apply Subtype.ext
      rw [hφ, Matrix.SpecialLinearGroup.coe_one]
      ext i j
      rw [submatrix_apply, hxc.1, one_apply, one_apply]
      simp only [Fin.castSucc_inj]
  ·
    intro s hs
    rw [hXY]
    exact ⟨h.sZero_le hs, mem_leviQ_of_mem_unitriangular
      ((h.mem_sZero_iff s (h.sZero_le hs)).1 hs)⟩
  ·
    have htZ : ∀ z ∈ W₁ ⊓ W₂, t * z * t⁻¹ ∈ W₁ ⊓ W₂ := fun z hz =>
      mem_inf.2 ⟨htW₁ z (mem_inf.1 hz).1, htW₂ z (mem_inf.1 hz).2⟩
    have hc := h.lastRow_of_twist hF hW₂S₀ hS₀W₂ hW₂c hZ hbt htZ
    have hc' := (lastRow_of_mul_eq_one (M := (c : Matrix (Fin 4) (Fin 4) F))
      (N := ((c⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))
      (by rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one]) hc).1
    let B : GL (Fin 3) F :=
      { val := (c : Matrix (Fin 4) (Fin 4) F).submatrix Fin.castSucc Fin.castSucc
        inv := ((c⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).submatrix
          Fin.castSucc Fin.castSucc
        val_inv := by
          rw [← submatrix_castSucc_mul_of_lastRow hc', ← Matrix.SpecialLinearGroup.coe_mul,
            mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, submatrix_castSucc_one]
        inv_val := by
          rw [← submatrix_castSucc_mul_of_lastRow hc, ← Matrix.SpecialLinearGroup.coe_mul,
            inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, submatrix_castSucc_one] }
    refine ⟨B, fun x hx => ?_⟩
    have hσx : ∀ j : Fin 3, ((p x : Matrix (Fin 4) (Fin 4) F).map σ) (Fin.last 3) j.castSucc =
        0 := fun j => by rw [Matrix.map_apply, (hXQ x x.2).2.1 j, map_zero]
    rw [hφ, hφ]
    change (p (t * x * t⁻¹) : Matrix (Fin 4) (Fin 4) F).submatrix Fin.castSucc Fin.castSucc = _
    rw [hpt x (hXQ x x.2).1 (hXQ _ hx).1, submatrix_castSucc_mul_of_lastRow hc',
      submatrix_castSucc_mul_of_lastRow hσx, Matrix.submatrix_map]
    have hfr : ((p x : Matrix (Fin 4) (Fin 4) F).submatrix Fin.castSucc Fin.castSucc).map σ =
        ((p x : Matrix (Fin 4) (Fin 4) F).submatrix Fin.castSucc Fin.castSucc).map
          (frobenius F 2) := by
      ext i j
      rw [Matrix.map_apply, Matrix.map_apply, hσ, frobenius_def]
    rw [hfr]
    rfl
  ·
    refine ⟨fun g j => b g j.castSucc, fun w hw w' hw' => ?_, fun v => ?_, fun w hw => ?_,
      fun x w hw => ?_⟩
    · funext j
      change b (w * w') j.castSucc = b w j.castSucc + b w' j.castSucc
      rw [h.add w hw w' hw']
      rfl
    · obtain ⟨w, hw, hbw⟩ := h.surjB (Fin.snoc (α := fun _ => F) v 0)
      refine ⟨w, hw, funext fun j => ?_⟩
      change b w j.castSucc = v j
      rw [hbw, Fin.snoc_castSucc]
    · constructor
      · intro h0
        have hbw : b w = Pi.single (Fin.last 3) (b w (Fin.last 3)) := by
          funext k
          induction k using Fin.lastCases with
          | last => rw [Pi.single_eq_same]
          | cast j =>
            rw [Pi.single_eq_of_ne (M := fun _ : Fin 4 => F) (Fin.castSucc_lt_last j).ne]
            exact congrFun h0 j
        obtain ⟨z, hz, hbz⟩ := hall (b w (Fin.last 3))
        rw [← h.inj z (mem_inf.1 hz).1 w hw (hbz.trans hbw.symm)]
        exact (mem_inf.1 hz).2
      · intro hw₂
        funext j
        exact h.apply_castSucc_eq_zero hF hS₀W₂ hZ (mem_inf.2 ⟨hw, hw₂⟩) j
    · have hxN := (hXQ x x.2).1
      have hxi : (x : G)⁻¹ ∈ seitzLeviX W₁ W₂ := inv_mem x.2
      have hinvrow : ∀ j : Fin 3, (((p x)⁻¹ : SpecialLinearGroup (Fin 4) F) :
          Matrix (Fin 4) (Fin 4) F) (Fin.last 3) j.castSucc = 0 := by
        rw [← h.map_inv hxN]
        exact (hXQ _ hxi).2.1
      have h1 := vecMul_castSucc_of_lastRow hinvrow (b w)
      have h2 : ((p x)⁻¹ : SpecialLinearGroup (Fin 4) F) = p ((x : G)⁻¹) := (h.map_inv hxN).symm
      change (fun j : Fin 3 => b ((x : G) * w * (x : G)⁻¹) j.castSucc) = _
      rw [h.act _ hxN _ hw, h1, Matrix.mulVec_transpose, ← map_inv φ x, hφ x⁻¹,
        Subgroup.coe_inv, ← h2]
  ·
    refine ⟨fun g => colRadVec (p g : Matrix (Fin 4) (Fin 4) F), fun w hw w' hw' => ?_,
      fun w hw => ?_, fun x w hw => ?_⟩
    · change colRadVec (p (w * w') : Matrix (Fin 4) (Fin 4) F) = _
      rw [h.map_mul _ (hW₂N hw) _ (hW₂N hw'), Matrix.SpecialLinearGroup.coe_mul,
        ((hcol hw).mul (hcol hw')).2]
    · change colRadVec (p w : Matrix (Fin 4) (Fin 4) F) = 0 ↔ _
      rw [← h.eq_one_iff _ (hW₂N hw)]
      constructor
      · intro h0
        exact Subtype.ext ((hcol hw).eq_one h0)
      · intro h1
        rw [h1, Matrix.SpecialLinearGroup.coe_one, colRadVec_one]
    · have hxN := (hXQ x x.2).1
      have hxw : (x : G) * w * (x : G)⁻¹ ∈ W₂ :=
        (mem_normalizer_iff.1 (seitzLeviX_le_normalizer_right W₁ W₂ x.2) w).1 hw
      change colRadVec (p ((x : G) * w * (x : G)⁻¹) : Matrix (Fin 4) (Fin 4) F) = _
      rw [hφ]
      refine colRadVec_eq_mulVec_of_mul_eq (hXQ x x.2).2.2 (hcol hw) (hcol hxw) ?_
      rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul,
        ← h.map_mul _ hxN _ (hW₂N hw), ← h.map_mul _ (hW₂N hxw) _ hxN]
      congr 2
      group

end CFSG.SeitzReduction.LinearPilot
