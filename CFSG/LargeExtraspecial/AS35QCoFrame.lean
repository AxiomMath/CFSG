module

public import CFSG.LargeExtraspecial.AS35QCoLin

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35QCo

open Module CFSG.RankThree.OrthogonalInvolutions

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def IsIsom (q : QuadraticForm (ZMod 2) V) (g : V ≃ₗ[ZMod 2] V) : Prop :=
  ∀ v, q (g v) = q v

structure Frame (q : QuadraticForm (ZMod 2) V) where
  Y₁ : V ≃ₗ[ZMod 2] V
  Y₂ : V ≃ₗ[ZMod 2] V
  Y₃ : V ≃ₗ[ZMod 2] V
  S₁ : V ≃ₗ[ZMod 2] V
  S₂ : V ≃ₗ[ZMod 2] V
  S₃ : V ≃ₗ[ZMod 2] V
  P₁₂ : V ≃ₗ[ZMod 2] V
  P₂₃ : V ≃ₗ[ZMod 2] V
  X : V ≃ₗ[ZMod 2] V
  iY₁ : IsIsom q Y₁
  iY₂ : IsIsom q Y₂
  iY₃ : IsIsom q Y₃
  iS₁ : IsIsom q S₁
  iX : IsIsom q X
  y₁ : Y₁ ^ 3 = 1
  y₂ : Y₂ ^ 3 = 1
  y₃ : Y₃ ^ 3 = 1
  s₁ : S₁ * S₁ = 1
  s₂ : S₂ * S₂ = 1
  s₃ : S₃ * S₃ = 1
  sy₁ : S₁ * Y₁ * S₁ = Y₁ * Y₁
  sy₂ : S₂ * Y₂ * S₂ = Y₂ * Y₂
  sy₃ : S₃ * Y₃ * S₃ = Y₃ * Y₃
  y₁₂ : Y₁ * Y₂ = Y₂ * Y₁
  y₁₃ : Y₁ * Y₃ = Y₃ * Y₁
  y₂₃ : Y₂ * Y₃ = Y₃ * Y₂
  s₁y₂ : S₁ * Y₂ = Y₂ * S₁
  s₁y₃ : S₁ * Y₃ = Y₃ * S₁
  s₂y₁ : S₂ * Y₁ = Y₁ * S₂
  s₂y₃ : S₂ * Y₃ = Y₃ * S₂
  s₃y₁ : S₃ * Y₁ = Y₁ * S₃
  s₃y₂ : S₃ * Y₂ = Y₂ * S₃
  s₁₂ : S₁ * S₂ = S₂ * S₁
  s₁₃ : S₁ * S₃ = S₃ * S₁
  p₁₂y₁ : P₁₂ * Y₁ = Y₂ * P₁₂
  p₁₂y₂ : P₁₂ * Y₂ = Y₁ * P₁₂
  p₁₂y₃ : P₁₂ * Y₃ = Y₃ * P₁₂
  p₁₂s₁ : P₁₂ * S₁ = S₂ * P₁₂
  p₂₃y₁ : P₂₃ * Y₁ = Y₁ * P₂₃
  p₂₃y₂ : P₂₃ * Y₂ = Y₃ * P₂₃
  p₂₃y₃ : P₂₃ * Y₃ = Y₂ * P₂₃
  p₂₃s₁ : P₂₃ * S₁ = S₁ * P₂₃
  x₅ : X ^ 5 = 1
  xy₁ : X * Y₁ = Y₁ * X
  xs₁ : X * S₁ = S₁ * X

namespace Frame

variable [FiniteDimensional (ZMod 2) V] {q : QuadraticForm (ZMod 2) V} (F : Frame q)

omit [FiniteDimensional (ZMod 2) V] in
theorem conj_eq {P g h : V ≃ₗ[ZMod 2] V} (e : P * g = h * P) : P * g * P⁻¹ = h := by
  rw [e, mul_assoc, mul_inv_cancel, mul_one]

omit [FiniteDimensional (ZMod 2) V] in
theorem commSpace_eq_map {P g h : V ≃ₗ[ZMod 2] V} (e : P * g = h * P) :
    commSpace h = (commSpace g).map (P : V →ₗ[ZMod 2] V) := by
  rw [← conj_eq e, commSpace_conj]

omit [FiniteDimensional (ZMod 2) V] in
theorem fixSpace_eq_map {P g h : V ≃ₗ[ZMod 2] V} (e : P * g = h * P) :
    fixSpace h = (fixSpace g).map (P : V →ₗ[ZMod 2] V) := by
  rw [← conj_eq e, fixSpace_conj]

omit [FiniteDimensional (ZMod 2) V] in
theorem apply_mem_commSpace_conj {P g h : V ≃ₗ[ZMod 2] V} (e : P * g = h * P) {v : V}
    (hv : v ∈ commSpace g) : P v ∈ commSpace h := by
  rw [commSpace_eq_map e]
  exact ⟨v, hv, rfl⟩

omit [FiniteDimensional (ZMod 2) V] in
theorem apply_mem_fixSpace_conj {P g h : V ≃ₗ[ZMod 2] V} (e : P * g = h * P) {v : V}
    (hv : v ∈ fixSpace g) : P v ∈ fixSpace h := by
  rw [fixSpace_eq_map e]
  exact ⟨v, hv, rfl⟩

omit [FiniteDimensional (ZMod 2) V] in
theorem finrank_commSpace_eq {P g h : V ≃ₗ[ZMod 2] V} (e : P * g = h * P) :
    finrank (ZMod 2) (commSpace h) = finrank (ZMod 2) (commSpace g) := by
  rw [commSpace_eq_map e, finrank_map_equiv]

omit [FiniteDimensional (ZMod 2) V] in
theorem s_mul_y {S Y : V ≃ₗ[ZMod 2] V} (hs : S * S = 1) (hsy : S * Y * S = Y * Y) :
    S * Y = Y * Y * S := by
  calc S * Y = S * Y * S * S := by rw [mul_assoc (S * Y), hs, mul_one]
    _ = Y * Y * S := by rw [hsy]

omit [FiniteDimensional (ZMod 2) V] in
theorem commSpace_sq {Y : V ≃ₗ[ZMod 2] V} (hY : Y ^ 3 = 1) : commSpace (Y * Y) = commSpace Y := by
  have : Y * Y = Y⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_three', hY]
  rw [this, commSpace_inv]

omit [FiniteDimensional (ZMod 2) V] in
theorem fixSpace_sq {Y : V ≃ₗ[ZMod 2] V} (hY : Y ^ 3 = 1) : fixSpace (Y * Y) = fixSpace Y := by
  have : Y * Y = Y⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_three', hY]
  rw [this, fixSpace_inv]

omit [FiniteDimensional (ZMod 2) V] in
theorem apply_mem_commSpace_of_inv {S Y : V ≃ₗ[ZMod 2] V} (hY : Y ^ 3 = 1)
    (e : S * Y = Y * Y * S) {v : V} (hv : v ∈ commSpace Y) : S v ∈ commSpace Y := by
  rw [← commSpace_sq hY]
  exact apply_mem_commSpace_conj e hv

omit [FiniteDimensional (ZMod 2) V] in
theorem apply_mem_fixSpace_of_inv {S Y : V ≃ₗ[ZMod 2] V} (hY : Y ^ 3 = 1)
    (e : S * Y = Y * Y * S) {v : V} (hv : v ∈ fixSpace Y) : S v ∈ fixSpace Y := by
  rw [← fixSpace_sq hY]
  exact apply_mem_fixSpace_conj e hv

omit [FiniteDimensional (ZMod 2) V] in
theorem odd_five : Odd 5 := ⟨2, rfl⟩

omit [FiniteDimensional (ZMod 2) V] in
theorem odd_three : Odd 3 := ⟨1, rfl⟩

omit [FiniteDimensional (ZMod 2) V] in
theorem fixSpace_eq_top_iff {g : V ≃ₗ[ZMod 2] V} : fixSpace g = ⊤ ↔ g = 1 := by
  constructor
  · intro h
    ext v
    have : v ∈ fixSpace g := h ▸ Submodule.mem_top
    exact mem_fixSpace.mp this
  · rintro rfl
    rw [eq_top_iff]
    intro v _
    exact mem_fixSpace.mpr rfl

theorem finrank_fixSpace_X (hV : finrank (ZMod 2) V = 8) (hX : F.X ≠ 1)
    (hfix : fixSpace F.X ≠ ⊥) : finrank (ZMod 2) (fixSpace F.X) = 4 := by
  have h := mod_four_of_pow_five F.x₅ (W := ⊤) (fun w _ => Submodule.mem_top)
  rw [finrank_top, hV, top_inf_eq] at h
  have hle : finrank (ZMod 2) (fixSpace F.X) ≤ 8 := hV ▸ Submodule.finrank_le _
  have hne0 : finrank (ZMod 2) (fixSpace F.X) ≠ 0 := fun h0 =>
    hfix (Submodule.finrank_eq_zero.mp h0)
  have hne8 : finrank (ZMod 2) (fixSpace F.X) ≠ 8 := fun h8 =>
    hX (fixSpace_eq_top_iff.mp (Submodule.eq_top_of_finrank_eq (by rw [h8, hV])))
  omega

theorem eq_of_le_commSpace_X (hV : finrank (ZMod 2) V = 8) (hX : F.X ≠ 1)
    (hfix : fixSpace F.X ≠ ⊥) {U : Submodule (ZMod 2) V} (hU : U ≤ commSpace F.X)
    (hUX : ∀ u ∈ U, F.X u ∈ U) (hU0 : U ≠ ⊥) : U = commSpace F.X := by
  have hc : finrank (ZMod 2) (commSpace F.X) = 4 := by
    have := finrank_commSpace_add_finrank_fixSpace F.X
    rw [F.finrank_fixSpace_X hV hX hfix, hV] at this
    omega
  have hfree : U ⊓ fixSpace F.X = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    have : v ∈ fixSpace F.X ⊓ commSpace F.X :=
      Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp hv).2, hU (Submodule.mem_inf.mp hv).1⟩
    rwa [fixSpace_inf_commSpace odd_five F.x₅] at this
  have h := mod_four_of_pow_five F.x₅ hUX
  rw [hfree, finrank_bot] at h
  have hle : finrank (ZMod 2) U ≤ 4 := hc ▸ Submodule.finrank_mono hU
  have hpos : finrank (ZMod 2) U ≠ 0 := fun h0 => hU0 (Submodule.finrank_eq_zero.mp h0)
  exact Submodule.eq_of_le_of_finrank_eq hU (by omega)


theorem commSpace_X_le (hV : finrank (ZMod 2) V = 8) (hX : F.X ≠ 1)
    (hfix : fixSpace F.X ≠ ⊥) : commSpace F.X ≤ fixSpace F.Y₁ ⊓ fixSpace F.S₁ := by
  let U := commSpace F.X
  have hUS : ∀ u ∈ U, F.S₁ u ∈ U := fun u hu => apply_mem_commSpace F.xs₁.symm hu
  have hUY : ∀ u ∈ U, F.Y₁ u ∈ U := fun u hu => apply_mem_commSpace F.xy₁.symm hu
  have hUX : ∀ u ∈ U, F.X u ∈ U := fun u hu => apply_mem_commSpace rfl hu
  have hc : finrank (ZMod 2) (commSpace F.X) = 4 := by
    have := finrank_commSpace_add_finrank_fixSpace F.X
    rw [F.finrank_fixSpace_X hV hX hfix, hV] at this
    omega
  have hS : ∀ u ∈ U, F.S₁ u = u := by
    have hKX : ∀ u ∈ U ⊓ fixSpace F.S₁, F.X u ∈ U ⊓ fixSpace F.S₁ := fun u hu =>
      Submodule.mem_inf.mpr ⟨hUX u (Submodule.mem_inf.mp hu).1,
        apply_mem_fixSpace F.xs₁ (Submodule.mem_inf.mp hu).2⟩
    by_cases hK : U ⊓ fixSpace F.S₁ = ⊥
    · intro u hu
      have hmem : F.S₁ u - u ∈ U ⊓ fixSpace F.S₁ := by
        refine Submodule.mem_inf.mpr ⟨U.sub_mem (hUS u hu) hu, mem_fixSpace.mpr ?_⟩
        rw [map_sub, ← LinearEquiv.mul_apply, F.s₁, one_apply', ← neg_sub, neg_eq_self']
      rw [hK, Submodule.mem_bot, sub_eq_zero] at hmem
      exact hmem
    · have hKU := F.eq_of_le_commSpace_X hV hX hfix inf_le_left hKX hK
      intro u hu
      have hu' : u ∈ commSpace F.X ⊓ fixSpace F.S₁ := by rw [hKU]; exact hu
      exact mem_fixSpace.mp (Submodule.mem_inf.mp hu').2
  have hY : ∀ u ∈ U, F.Y₁ u = u := by
    have hKX : ∀ u ∈ U ⊓ fixSpace F.Y₁, F.X u ∈ U ⊓ fixSpace F.Y₁ := fun u hu =>
      Submodule.mem_inf.mpr ⟨hUX u (Submodule.mem_inf.mp hu).1,
        apply_mem_fixSpace F.xy₁ (Submodule.mem_inf.mp hu).2⟩
    by_cases hK : U ⊓ fixSpace F.Y₁ = ⊥
    · exfalso
      have hU0 : commSpace F.X = ⊥ := by
        rw [eq_bot_iff]
        intro u hu
        have e1 : F.S₁ (F.Y₁ (F.S₁ u)) = F.Y₁ (F.Y₁ u) := by
          rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, F.sy₁, LinearEquiv.mul_apply]
        rw [hS u hu, hS _ (hUY u hu)] at e1
        have e2 : u = F.Y₁ u := F.Y₁.injective e1
        have hmem : u ∈ U ⊓ fixSpace F.Y₁ := Submodule.mem_inf.mpr ⟨hu, mem_fixSpace.mpr e2.symm⟩
        rwa [hK] at hmem
      rw [hU0, finrank_bot] at hc
      exact absurd hc (by norm_num)
    · have hKU := F.eq_of_le_commSpace_X hV hX hfix inf_le_left hKX hK
      intro u hu
      have hu' : u ∈ commSpace F.X ⊓ fixSpace F.Y₁ := by rw [hKU]; exact hu
      exact mem_fixSpace.mp (Submodule.mem_inf.mp hu').2
  intro u hu
  exact Submodule.mem_inf.mpr ⟨mem_fixSpace.mpr (hY u hu), mem_fixSpace.mpr (hS u hu)⟩

theorem commSpace_le_fixSpace_X (hq : q.polarBilin.Nondegenerate) (hV : finrank (ZMod 2) V = 8)
    (hX : F.X ≠ 1) (hfix : fixSpace F.X ≠ ⊥) :
    commSpace F.Y₁ ≤ fixSpace F.X ∧ commSpace F.S₁ ≤ fixSpace F.X :=
  ⟨commSpace_le_fixSpace_swap hq F.iX F.iY₁ ((F.commSpace_X_le hV hX hfix).trans inf_le_left),
    commSpace_le_fixSpace_swap hq F.iX F.iS₁ ((F.commSpace_X_le hV hX hfix).trans inf_le_right)⟩


omit [FiniteDimensional (ZMod 2) V] in
theorem commSpace_inf_fixSpace {Y : V ≃ₗ[ZMod 2] V} (hY : Y ^ 3 = 1) :
    commSpace Y ⊓ fixSpace Y = ⊥ := by
  rw [inf_comm]
  exact fixSpace_inf_commSpace odd_three hY

omit [FiniteDimensional (ZMod 2) V] in
theorem inf_fixSpace_of_le_commSpace {Y : V ≃ₗ[ZMod 2] V} (hY : Y ^ 3 = 1)
    {U : Submodule (ZMod 2) V} (hU : U ≤ commSpace Y) : U ⊓ fixSpace Y = ⊥ :=
  eq_bot_iff.mpr fun v hv => by
    have : v ∈ commSpace Y ⊓ fixSpace Y :=
      Submodule.mem_inf.mpr ⟨hU (Submodule.mem_inf.mp hv).1, (Submodule.mem_inf.mp hv).2⟩
    rwa [commSpace_inf_fixSpace hY] at this

omit [FiniteDimensional (ZMod 2) V] in
theorem finrank_commSpace_Y₂ : finrank (ZMod 2) (commSpace F.Y₂) =
    finrank (ZMod 2) (commSpace F.Y₁) := finrank_commSpace_eq F.p₁₂y₁

omit [FiniteDimensional (ZMod 2) V] in
theorem finrank_commSpace_Y₃ : finrank (ZMod 2) (commSpace F.Y₃) =
    finrank (ZMod 2) (commSpace F.Y₁) := by
  rw [finrank_commSpace_eq F.p₂₃y₂, finrank_commSpace_Y₂]

theorem finrank_W₁₂ :
    finrank (ZMod 2) ↥(commSpace F.Y₁ ⊓ commSpace F.Y₂) =
      2 * finrank (ZMod 2) ↥((commSpace F.Y₁ ⊓ commSpace F.Y₂) ⊓ fixSpace (F.Y₁ * F.Y₂)) ∧
      Even (finrank (ZMod 2) ↥((commSpace F.Y₁ ⊓ commSpace F.Y₂) ⊓ fixSpace (F.Y₁ * F.Y₂))) := by
  apply finrank_split F.y₁ F.y₂ F.y₁₂
  · intro u hu
    exact Submodule.mem_inf.mpr ⟨apply_mem_commSpace rfl (Submodule.mem_inf.mp hu).1,
      apply_mem_commSpace F.y₁₂ (Submodule.mem_inf.mp hu).2⟩
  · intro u hu
    exact Submodule.mem_inf.mpr ⟨apply_mem_commSpace F.y₁₂.symm (Submodule.mem_inf.mp hu).1,
      apply_mem_commSpace rfl (Submodule.mem_inf.mp hu).2⟩
  · exact inf_fixSpace_of_le_commSpace F.y₁ inf_le_left
  · exact inf_fixSpace_of_le_commSpace F.y₂ inf_le_right
  · exact F.s₂y₁
  · exact s_mul_y F.s₂ F.sy₂
  · exact F.s₂
  · intro u hu
    exact Submodule.mem_inf.mpr ⟨apply_mem_commSpace F.s₂y₁ (Submodule.mem_inf.mp hu).1,
      apply_mem_commSpace_of_inv F.y₂ (s_mul_y F.s₂ F.sy₂) (Submodule.mem_inf.mp hu).2⟩

omit [FiniteDimensional (ZMod 2) V] in
theorem map_inf_equiv (P : V ≃ₗ[ZMod 2] V) (U W : Submodule (ZMod 2) V) :
    (U ⊓ W).map (P : V →ₗ[ZMod 2] V) =
      U.map (P : V →ₗ[ZMod 2] V) ⊓ W.map (P : V →ₗ[ZMod 2] V) :=
  Submodule.map_inf _ P.injective

omit [FiniteDimensional (ZMod 2) V] in
theorem W₁₃_eq : commSpace F.Y₁ ⊓ commSpace F.Y₃ =
    (commSpace F.Y₁ ⊓ commSpace F.Y₂).map (F.P₂₃ : V →ₗ[ZMod 2] V) := by
  rw [map_inf_equiv, ← commSpace_eq_map F.p₂₃y₁, ← commSpace_eq_map F.p₂₃y₂]

omit [FiniteDimensional (ZMod 2) V] in
theorem W₂₃_eq : commSpace F.Y₂ ⊓ commSpace F.Y₃ =
    (commSpace F.Y₁ ⊓ commSpace F.Y₃).map (F.P₁₂ : V →ₗ[ZMod 2] V) := by
  rw [map_inf_equiv, ← commSpace_eq_map F.p₁₂y₁, ← commSpace_eq_map F.p₁₂y₃]

omit [FiniteDimensional (ZMod 2) V] in
theorem le_fixSpace_of_W₁₂ (h : commSpace F.Y₁ ⊓ commSpace F.Y₂ = ⊥) :
    commSpace F.Y₁ ≤ fixSpace F.Y₂ ⊓ fixSpace F.Y₃ ∧
      commSpace F.Y₂ ≤ fixSpace F.Y₁ ⊓ fixSpace F.Y₃ ∧
        commSpace F.Y₃ ≤ fixSpace F.Y₁ ⊓ fixSpace F.Y₂ := by
  have h13 : commSpace F.Y₁ ⊓ commSpace F.Y₃ = ⊥ := by rw [F.W₁₃_eq, h, Submodule.map_bot]
  have h23 : commSpace F.Y₂ ⊓ commSpace F.Y₃ = ⊥ := by rw [F.W₂₃_eq, h13, Submodule.map_bot]
  have key : ∀ {A B : V ≃ₗ[ZMod 2] V}, A ^ 3 = 1 → B * A = A * B →
      commSpace B ⊓ commSpace A = ⊥ → commSpace B ≤ fixSpace A := fun hA hBA hBA' =>
    le_fixSpace_of_inf_commSpace hA (fun u hu => apply_mem_commSpace hBA.symm hu) hBA'
  refine ⟨le_inf (key F.y₂ F.y₁₂ h) (key F.y₃ F.y₁₃ h13), le_inf ?_ (key F.y₃ F.y₂₃ h23),
    le_inf ?_ ?_⟩
  · exact key F.y₁ F.y₁₂.symm (by rw [inf_comm]; exact h)
  · exact key F.y₁ F.y₁₃.symm (by rw [inf_comm]; exact h13)
  · exact key F.y₂ F.y₂₃.symm (by rw [inf_comm]; exact h23)


omit [FiniteDimensional (ZMod 2) V] in
theorem mul_comm_of {A B C : V ≃ₗ[ZMod 2] V} (hAB : A * C = C * A) (hBC : B * C = C * B) :
    A * B * C = C * (A * B) := by
  rw [mul_assoc, hBC, ← mul_assoc, hAB, mul_assoc]

theorem natural (hq : q.polarBilin.Nondegenerate) (hV : finrank (ZMod 2) V = 8)
    (hY : F.Y₁ ≠ 1) (hX : F.X ≠ 1) (hfix : fixSpace F.X ≠ ⊥) :
    finrank (ZMod 2) (commSpace F.Y₁) = 2 ∧ commSpace F.Y₁ ⊓ commSpace F.Y₂ = ⊥ := by
  have hc4 : finrank (ZMod 2) (commSpace F.Y₁) ≤ 4 :=
    (Submodule.finrank_mono (F.commSpace_le_fixSpace_X hq hV hX hfix).1).trans
      (F.finrank_fixSpace_X hV hX hfix).le
  have hceven : Even (finrank (ZMod 2) (commSpace F.Y₁)) :=
    even_finrank_of_free F.y₁ (fun u hu => apply_mem_commSpace rfl hu)
      (commSpace_inf_fixSpace F.y₁)
  have hc0 := one_le_finrank_commSpace hY
  obtain ⟨hW, hWeven⟩ := F.finrank_W₁₂
  have hWle : finrank (ZMod 2) ↥(commSpace F.Y₁ ⊓ commSpace F.Y₂) ≤
      finrank (ZMod 2) (commSpace F.Y₁) := Submodule.finrank_mono inf_le_left
  by_cases hW0 : commSpace F.Y₁ ⊓ commSpace F.Y₂ = ⊥
  · refine ⟨?_, hW0⟩
    obtain ⟨h1, h2, h3⟩ := F.le_fixSpace_of_W₁₂ hW0
    have h12 := finrank_sup_of_inf_eq_bot hW0
    have h123 : (commSpace F.Y₁ ⊔ commSpace F.Y₂) ⊓ commSpace F.Y₃ = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      obtain ⟨hv12, hv3⟩ := Submodule.mem_inf.mp hv
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv12
      have hb1 : b ∈ fixSpace F.Y₁ := (Submodule.mem_inf.mp (h2 hb)).1
      have hv1 : a + b ∈ fixSpace F.Y₁ := (Submodule.mem_inf.mp (h3 hv3)).1
      have ha1 : a ∈ fixSpace F.Y₁ := by
        have := (fixSpace F.Y₁).sub_mem hv1 hb1
        rwa [add_sub_cancel_right] at this
      have ha0 : a = 0 := by
        have : a ∈ commSpace F.Y₁ ⊓ fixSpace F.Y₁ := Submodule.mem_inf.mpr ⟨ha, ha1⟩
        rwa [commSpace_inf_fixSpace F.y₁, Submodule.mem_bot] at this
      rw [ha0, zero_add] at hv3 ⊢
      have : b ∈ commSpace F.Y₂ ⊓ fixSpace F.Y₂ :=
        Submodule.mem_inf.mpr ⟨hb, (Submodule.mem_inf.mp (h3 hv3)).2⟩
      rwa [commSpace_inf_fixSpace F.y₂, Submodule.mem_bot] at this
    have h3sum := finrank_sup_of_inf_eq_bot h123
    rw [h12, F.finrank_commSpace_Y₂, F.finrank_commSpace_Y₃] at h3sum
    have hle : finrank (ZMod 2) ↥(commSpace F.Y₁ ⊔ commSpace F.Y₂ ⊔ commSpace F.Y₃) ≤ 8 :=
      hV ▸ Submodule.finrank_le _
    obtain ⟨k, hk⟩ := hceven
    omega
  · exfalso
    have hpos : 0 < finrank (ZMod 2) ↥(commSpace F.Y₁ ⊓ commSpace F.Y₂) := by
      rw [Nat.pos_iff_ne_zero]
      exact fun h => hW0 (Submodule.finrank_eq_zero.mp h)
    obtain ⟨d, hd⟩ := hWeven
    have hW4 : finrank (ZMod 2) ↥(commSpace F.Y₁ ⊓ commSpace F.Y₂) = 4 := by omega
    have hc : finrank (ZMod 2) (commSpace F.Y₁) = 4 := by omega
    have e1 : commSpace F.Y₁ ⊓ commSpace F.Y₂ = commSpace F.Y₁ :=
      Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [hW4, hc])
    have e2 : commSpace F.Y₁ ⊓ commSpace F.Y₂ = commSpace F.Y₂ :=
      Submodule.eq_of_le_of_finrank_eq inf_le_right (by rw [hW4, F.finrank_commSpace_Y₂, hc])
    have e3 : commSpace F.Y₁ ⊓ commSpace F.Y₃ = commSpace F.Y₃ := by
      apply Submodule.eq_of_le_of_finrank_eq inf_le_right
      rw [F.W₁₃_eq, finrank_map_equiv, hW4, F.finrank_commSpace_Y₃, hc]
    have e4 : commSpace F.Y₁ ⊓ commSpace F.Y₃ = commSpace F.Y₁ := by
      apply Submodule.eq_of_le_of_finrank_eq inf_le_left
      rw [F.W₁₃_eq, finrank_map_equiv, hW4, hc]
    have h12 : commSpace F.Y₂ = commSpace F.Y₁ := e2.symm.trans e1
    have h13 : commSpace F.Y₃ = commSpace F.Y₁ := e3.symm.trans e4
    set A := commSpace F.Y₁ ⊓ fixSpace (F.Y₁ * F.Y₂) with hA
    have hAdim : finrank (ZMod 2) A = 2 := by
      have := hd
      rw [e1] at hW
      rw [hA]
      omega
    obtain ⟨h2, h2even⟩ := finrank_split (U := A) F.y₁ F.y₃ F.y₁₃
      (fun u hu => Submodule.mem_inf.mpr ⟨apply_mem_commSpace rfl (Submodule.mem_inf.mp hu).1,
        apply_mem_fixSpace (mul_comm_of rfl F.y₁₂.symm).symm (Submodule.mem_inf.mp hu).2⟩)
      (fun u hu => Submodule.mem_inf.mpr
        ⟨apply_mem_commSpace F.y₁₃.symm (Submodule.mem_inf.mp hu).1,
          apply_mem_fixSpace (mul_comm_of F.y₁₃ F.y₂₃).symm (Submodule.mem_inf.mp hu).2⟩)
      (inf_fixSpace_of_le_commSpace F.y₁ inf_le_left)
      (inf_fixSpace_of_le_commSpace F.y₃ (inf_le_left.trans h13.ge))
      F.s₃y₁ (s_mul_y F.s₃ F.sy₃) F.s₃
      (fun u hu => Submodule.mem_inf.mpr
        ⟨apply_mem_commSpace F.s₃y₁ (Submodule.mem_inf.mp hu).1,
          apply_mem_fixSpace (mul_comm_of F.s₃y₁.symm F.s₃y₂.symm).symm
            (Submodule.mem_inf.mp hu).2⟩)
    obtain ⟨k, hk⟩ := h2even
    omega

omit [FiniteDimensional (ZMod 2) V] in
theorem eq_of_finrank_eq_one {W : Submodule (ZMod 2) V} (hW : finrank (ZMod 2) W = 1)
    {a b : V} (ha : a ∈ W) (hb : b ∈ W) (ha0 : a ≠ 0) (hb0 : b ≠ 0) : a = b := by
  have hb' : (⟨b, hb⟩ : W) ≠ 0 := fun h => hb0 (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨b, hb⟩ : W) hb').mp hW ⟨a, ha⟩
  have hc' : c • b = a := congrArg Subtype.val hc
  have hc1 : c = 1 := by
    have h01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases h01 c with rfl | rfl
    · rw [zero_smul] at hc'; exact absurd hc'.symm ha0
    · rfl
  rw [← hc', hc1, one_smul]

end Frame

end CFSG.LargeExtraspecial.AS35QCo
