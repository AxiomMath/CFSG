module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1016M3Co1Act

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017.H1016M3.Co1Sylow

open CFSG.Sporadic.Co1Schreier CFSG.HardMathSupport.Timmesfeld.SporadicBalance
open CFSG.Monster.B.Pinned (rowsMat)
open CFSG.HardMathSupport.Foote.E27.OrbitF3 (rowsMat_lidD)
open scoped Matrix

private theorem card_fix_le (M : Matrix (Fin 6) (Fin 6) (ZMod 3))
    (v : ZMod 3 → ZMod 3 → ZMod 3 → Fin 6 → ZMod 3)
    (hv : ∀ x y z x' y' z', v x y z - v x' y' z' = v (x - x') (y - y') (z - z'))
    (h : ∀ x y z, M *ᵥ v x y z = v x y z → x = 0 ∧ y = 0 ∧ z = 0) :
    Nat.card {b : Fin 6 → ZMod 3 // M *ᵥ b = b} ≤ 27 := by
  have hinj : Function.Injective fun p : {b : Fin 6 → ZMod 3 // M *ᵥ b = b} ×
      (ZMod 3 × ZMod 3 × ZMod 3) => p.1.1 + v p.2.1 p.2.2.1 p.2.2.2 := by
    rintro ⟨⟨b, hb⟩, x, y, z⟩ ⟨⟨b', hb'⟩, x', y', z'⟩ hbb
    change b + v x y z = b' + v x' y' z' at hbb
    have hd : b - b' = v (x' - x) (y' - y) (z' - z) := by
      rw [← hv]
      exact sub_eq_sub_iff_add_eq_add.2 (hbb.trans (add_comm _ _))
    have hfix : M *ᵥ v (x' - x) (y' - y) (z' - z) = v (x' - x) (y' - y) (z' - z) := by
      rw [← hd, Matrix.mulVec_sub, hb, hb']
    obtain ⟨h1, h2, h3⟩ := h _ _ _ hfix
    rw [sub_eq_zero] at h1 h2 h3
    subst h1 h2 h3
    obtain rfl := add_right_cancel hbb
    rfl
  have hc := Nat.card_le_card_of_injective _ hinj
  simp only [Nat.card_prod, Nat.card_fun, Nat.card_zmod, Nat.card_fin, Nat.reducePow,
    Nat.reduceMul] at hc
  omega

section Rho


private theorem exists_acts' (x : ↥Co1T.Qg) :
    ∃ M, Acts ((x : ↥GA) : GL24) M ∧ M ∈ s0Rows.map (rowsMat 3 6) := by
  obtain ⟨Y, hY, h⟩ := exists_acts x.2
  exact ⟨_, h, List.mem_map_of_mem hY⟩

private noncomputable def rhoM (x : ↥Co1T.Qg) : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  (exists_acts' x).choose

private theorem acts_rhoM (x : ↥Co1T.Qg) : Acts ((x : ↥GA) : GL24) (rhoM x) :=
  (exists_acts' x).choose_spec.1

private theorem rhoM_mem (x : ↥Co1T.Qg) : rhoM x ∈ s0Rows.map (rowsMat 3 6) :=
  (exists_acts' x).choose_spec.2

private noncomputable def rhoHom : ↥Co1T.Qg →* Matrix (Fin 6) (Fin 6) (ZMod 3) where
  toFun := rhoM
  map_one' := acts_unique (acts_rhoM 1) acts_one
  map_mul' x y := acts_unique (acts_rhoM (x * y)) (acts_mul (acts_rhoM x) (acts_rhoM y))

noncomputable def rho : ↥Co1T.Qg →* (Matrix (Fin 6) (Fin 6) (ZMod 3))ˣ :=
  rhoHom.toHomUnits

private theorem rho_val (x : ↥Co1T.Qg) :
    ((rho x : (Matrix (Fin 6) (Fin 6) (ZMod 3))ˣ) : Matrix (Fin 6) (Fin 6) (ZMod 3)) = rhoM x :=
  MonoidHom.coe_toHomUnits _ _

private theorem rho_eq_of_acts {x : ↥Co1T.Qg} {M : Matrix (Fin 6) (Fin 6) (ZMod 3)}
    (h : Acts ((x : ↥GA) : GL24) M) :
    ((rho x : (Matrix (Fin 6) (Fin 6) (ZMod 3))ˣ) : Matrix (Fin 6) (Fin 6) (ZMod 3)) = M :=
  (rho_val x).trans (acts_unique (acts_rhoM x) h)

theorem rho_eq_one {x : ↥Co1T.Qg} (hx : ((x : ↥GA) : GL24) ∈ ElemThree.E) : rho x = 1 :=
  Units.ext ((rho_eq_of_acts (acts_of_mem_E hx)).trans Units.val_one.symm)

private theorem rho_wG {w : List ℕ} (hw : w ∈ Co1T.Data.qGenWords) :
    ((rho ⟨Co1T.wG w, wG_mem_Qg hw⟩ : (Matrix (Fin 6) (Fin 6) (ZMod 3))ˣ) :
      Matrix (Fin 6) (Fin 6) (ZMod 3)) = rowsMat 3 6 (wordRows w) :=
  rho_eq_of_acts (acts_wG (words_check w hw).1)

theorem rho_range_noncomm : ¬ ∀ u v : ↥rho.range, u * v = v * u := by
  intro h
  obtain ⟨w₁, hw₁, w₂, hw₂, e₁, e₂⟩ := m_words_check
  have h12 := congrArg (fun u : ↥rho.range =>
      ((u : (Matrix (Fin 6) (Fin 6) (ZMod 3))ˣ) : Matrix (Fin 6) (Fin 6) (ZMod 3)))
    (h ⟨rho ⟨Co1T.wG w₁, wG_mem_Qg hw₁⟩, MonoidHom.mem_range.2 ⟨_, rfl⟩⟩
      ⟨rho ⟨Co1T.wG w₂, wG_mem_Qg hw₂⟩, MonoidHom.mem_range.2 ⟨_, rfl⟩⟩)
  simp only [Subgroup.coe_mul, Units.val_mul, rho_wG hw₁, rho_wG hw₂, e₁, e₂] at h12
  exact m_noncomm h12

theorem card_rho_range_le : Nat.card rho.range ≤ 27 := by
  classical
  have hmem : ∀ u : ↥rho.range, ((u : (Matrix (Fin 6) (Fin 6) (ZMod 3))ˣ) :
      Matrix (Fin 6) (Fin 6) (ZMod 3)) ∈ (s0Rows.map (rowsMat 3 6)).toFinset := by
    rintro ⟨_, x, rfl⟩
    show ((rho x : (Matrix (Fin 6) (Fin 6) (ZMod 3))ˣ) : Matrix (Fin 6) (Fin 6) (ZMod 3)) ∈ _
    rw [List.mem_toFinset, rho_val]
    exact rhoM_mem x
  have hinj : Function.Injective fun u : ↥rho.range =>
      (⟨_, hmem u⟩ : ↥(s0Rows.map (rowsMat 3 6)).toFinset) := fun u v h =>
    Subtype.ext (Units.ext (congrArg Subtype.val h))
  calc Nat.card rho.range ≤ Nat.card ↥(s0Rows.map (rowsMat 3 6)).toFinset :=
        Nat.card_le_card_of_injective _ hinj
    _ = (s0Rows.map (rowsMat 3 6)).toFinset.card := Nat.card_eq_finsetCard _
    _ ≤ (s0Rows.map (rowsMat 3 6)).length := List.toFinset_card_le _
    _ = 27 := by rw [List.length_map, s0_check.2]

theorem rho_mulVec_eExp {x : ↥Co1T.Qg} {e : GL24} (he : e ∈ ElemThree.E)
    (hc : ((x : ↥GA) : GL24) * e = e * ((x : ↥GA) : GL24)) :
    ((rho x : (Matrix (Fin 6) (Fin 6) (ZMod 3))ˣ) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ
      eExp ⟨e, he⟩ = eExp ⟨e, he⟩ := by
  rw [rho_val]
  apply eProd_injective
  rw [← acts_rhoM x, eProd_eExp]
  show ((x : ↥GA) : GL24) * e * ((x : ↥GA) : GL24)⁻¹ = e
  rw [hc, mul_inv_cancel_right]

theorem card_fix_rho_le {x : ↥Co1T.Qg} (hx : rho x ≠ 1) :
    Nat.card {b : Fin 6 → ZMod 3 //
      ((rho x : (Matrix (Fin 6) (Fin 6) (ZMod 3))ˣ) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ b = b} ≤
      27 := by
  rw [rho_val]
  obtain ⟨Y, hY, hYx⟩ := List.mem_map.1 (rhoM_mem x)
  rcases fix_check Y hY with h | h | h
  · refine absurd (Units.ext ?_) hx
    rw [rho_val, Units.val_one, ← hYx, h, rowsMat_lidD]
  · exact card_fix_le _ vA vA_sub (by rw [← hYx]; exact h)
  · exact card_fix_le _ vB vB_sub (by rw [← hYx]; exact h)

end Rho

end CFSG.LocalAnalysis.GLTheoremA.H1017.H1016M3.Co1Sylow
