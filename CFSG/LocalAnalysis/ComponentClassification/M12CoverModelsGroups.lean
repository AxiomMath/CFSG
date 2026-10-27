module

public import Certificates.Certificate11001

public section

namespace CFSG.ComponentClassification.M12Cover.InternalSylow

open CFSG.ComponentClassification.CentralCover

theorem center_of_check {G : Type*} [Group G] {N : ℕ} (hN : 9 ≤ N)
    {mul : Fin N → Fin N → Fin N} {mulN : ℕ → ℕ → ℕ} (hmul : ∀ x y, (mul x y : ℕ) = mulN x y)
    {enc : Fin N ≃ G} (h : IsTableModel mul enc) (hc : centerCheckN N mulN = true) (z : Fin N) :
    enc z ∈ Subgroup.center G ↔ isCentralLabel z = true := by
  rw [IsTableModel.mem_center_iff h z]
  have hz := all_range hc z.2
  unfold isCentralLabel
  split_ifs at hz with hl
  · refine ⟨fun _ => hl, fun _ x => Fin.ext ?_⟩
    rw [hmul, hmul]
    exact Nat.eq_of_beq_eq_true (all_range hz x.2)
  · refine ⟨fun hcomm => ?_, fun h' => absurd h' hl⟩
    obtain ⟨x, hx, hne⟩ := List.any_eq_true.1 hz
    have hx' : x < N := by
      rw [List.mem_range] at hx
      omega
    have := congrArg Fin.val (hcomm ⟨x, hx'⟩)
    rw [hmul, hmul] at this
    simp [this] at hne

theorem rootCount_two_of_table {G : Type*} [Group G] {N : ℕ} {mul : Fin N → Fin N → Fin N}
    {mulN : ℕ → ℕ → ℕ} (hmul : ∀ x y, (mul x y : ℕ) = mulN x y) {enc : Fin N ≃ G}
    (h : IsTableModel mul enc) (z : Fin N) :
    rootCount 2 (enc z) = (List.range N).countP fun x => mulN x x == z := by
  rw [IsTableModel.rootCount_two h, ← card_fin_subtype_eq_countP]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
  rw [Fin.ext_iff, hmul, beq_iff_eq]

theorem rootCount_four_of_table {G : Type*} [Group G] {N : ℕ} {mul : Fin N → Fin N → Fin N}
    {mulN : ℕ → ℕ → ℕ} (hmul : ∀ x y, (mul x y : ℕ) = mulN x y) {enc : Fin N ≃ G}
    (h : IsTableModel mul enc) (z : Fin N) :
    rootCount 4 (enc z) = (List.range N).countP fun x => mulN (mulN x x) (mulN x x) == z := by
  rw [IsTableModel.rootCount_four h, ← card_fin_subtype_eq_countP]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
  rw [Fin.ext_iff, hmul, hmul, beq_iff_eq]

theorem card_center_of_check {G : Type*} [Group G] {N : ℕ} {enc : Fin N ≃ G}
    (hc : ∀ z : Fin N, enc z ∈ Subgroup.center G ↔ isCentralLabel z = true) :
    Nat.card (Subgroup.center G) = (List.range N).countP isCentralLabel := by
  rw [← card_fin_subtype_eq_countP]
  exact (Nat.card_congr (enc.subtypeEquiv fun z => (hc z).symm)).symm

theorem isElementaryAbelian_center_of {G : Type*} [Group G]
    (h : ∀ w ∈ Subgroup.center G, w ^ 2 = 1) : IsElementaryAbelian 2 (Subgroup.center G) where
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun w =>
    Subtype.ext (by simpa using h w w.2)

theorem star_val (x y : Fin 128) : (star x y : ℕ) = starN x y := rfl

theorem centerCheck_R : centerCheckN 128 starN = true :=
  Certificates.certificate11001.1

theorem mem_center_R (w : R) :
    w ∈ Subgroup.center R ↔ w = encR 0 ∨ w = encR 27 ∨ w = encR 64 ∨ w = encR 91 := by
  obtain ⟨z, rfl⟩ := encR.surjective w
  rw [center_of_check (by norm_num) star_val isTableModel_star centerCheck_R z,
    encR.injective.eq_iff, encR.injective.eq_iff, encR.injective.eq_iff, encR.injective.eq_iff]
  unfold isCentralLabel
  simp only [Bool.or_eq_true, beq_iff_eq, Fin.ext_iff, or_assoc]
  exact Iff.rfl

theorem rootCounts_R_check :
    ((List.range 128).countP fun x => starN x x == 27) = 0 ∧
    ((List.range 128).countP fun x => starN (starN x x) (starN x x) == 27) = 0 ∧
    ((List.range 128).countP fun x => starN x x == 64) = 24 ∧
    ((List.range 128).countP fun x => starN (starN x x) (starN x x) == 64) = 0 ∧
    ((List.range 128).countP fun x => starN x x == 91) = 24 ∧
    ((List.range 128).countP fun x => starN (starN x x) (starN x x) == 91) = 32 ∧
    starN 27 27 = 0 ∧ starN 64 64 = 0 ∧ starN 91 91 = 0 ∧
    (List.range 128).countP isCentralLabel = 4 :=
  Certificates.certificate11001.2.1

theorem rootCounts_R :
    (rootCount 2 (encR 27), rootCount 4 (encR 27)) = (0, 0) ∧
    (rootCount 2 (encR 64), rootCount 4 (encR 64)) = (24, 0) ∧
    (rootCount 2 (encR 91), rootCount 4 (encR 91)) = (24, 32) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := rootCounts_R_check
  simp only [rootCount_two_of_table star_val isTableModel_star,
    rootCount_four_of_table star_val isTableModel_star]
  exact ⟨Prod.ext h1 h2, Prod.ext h3 h4, Prod.ext h5 h6⟩

theorem sq_encR {z : Fin 128} (hz : starN z z = 0) : encR z ^ 2 = 1 := by
  rw [sq, ← isTableModel_star, ← encR_zero]
  exact congrArg encR (Fin.ext hz)

theorem center_R_elementary :
    IsElementaryAbelian 2 (Subgroup.center R) ∧ Nat.card (Subgroup.center R) = 4 := by
  obtain ⟨-, -, -, -, -, -, h27, h64, h91, hc⟩ := rootCounts_R_check
  refine ⟨isElementaryAbelian_center_of fun w hw => ?_, ?_⟩
  · rcases (mem_center_R w).1 hw with rfl | rfl | rfl | rfl
    · rw [encR_zero, one_pow]
    · exact sq_encR h27
    · exact sq_encR h64
    · exact sq_encR h91
  · rw [card_center_of_check (center_of_check (by norm_num) star_val isTableModel_star
      centerCheck_R), hc]

theorem encR_ne_one {z : Fin 128} (hz : z ≠ 0) : encR z ≠ 1 := by
  rw [← encR_zero]
  exact fun h => hz (encR.injective h)

theorem aut_fixes_center_R (φ : MulAut R) : ∀ w ∈ Subgroup.center R, φ w = w := by
  obtain ⟨h27, h64, h91⟩ := rootCounts_R
  refine aut_fixes_center (z₁ := encR 27) (z₂ := encR 64) (z₃ := encR 91)
    (fun w => by rw [mem_center_R, encR_zero]) (encR_ne_one (by decide))
    (encR_ne_one (by decide)) (encR_ne_one (by decide)) ?_ ?_ ?_ φ
  · rw [h27, h64]; decide
  · rw [h27, h91]; decide
  · rw [h64, h91]; decide

@[expose] noncomputable def zε (ε : ZMod 2) : R := if ε = 1 then ⟨1, 1⟩ else 1

theorem twistHyp (ε : ZMod 2) : TwistHyp tau (zε ε) where
  invol := tau_tau
  comm x := by
    unfold zε
    split_ifs
    · exact (Subgroup.mem_center_iff.1 (CocycleExtension.mk_one_mem_center 1) x).symm
    · rw [one_mul, mul_one]
  fix := by
    unfold zε
    split_ifs
    · exact tau_z
    · exact map_one tau

instance instFactTwistHyp (ε : ZMod 2) : Fact (TwistHyp tau (zε ε)) := ⟨twistHyp ε⟩

abbrev T (ε : ZMod 2) : Type := TwistExt tau (zε ε)

theorem card_T (ε : ZMod 2) : Nat.card (T ε) = 256 := by
  rw [TwistExt.card, card_R]

theorem t_mul_t (ε : ZMod 2) :
    (TwistExt.t : T ε) * TwistExt.t = TwistExt.inl (if ε = 1 then ⟨1, 1⟩ else 1) :=
  TwistExt.t_mul_t

theorem t_conj (ε : ZMod 2) (x : R) :
    (TwistExt.t : T ε) * TwistExt.inl x * TwistExt.t⁻¹ = TwistExt.inl (tau x) :=
  TwistExt.t_conj x

theorem tmulN_lt (ε X Y : ℕ) : tmulN ε X Y < 256 := by
  have := starN_lt (starN (X % 128) (if (X / 128) % 2 = 1 then tauN lamIdx (Y % 128) else Y % 128))
    (zN (ε * (X / 128) * (Y / 128)))
  have := Nat.mod_lt (X / 128 + Y / 128) (show 0 < 2 by norm_num)
  unfold tmulN
  omega

@[expose] def tmul (ε : ℕ) (X Y : Fin 256) : Fin 256 := ⟨tmulN ε X Y, tmulN_lt ε X Y⟩

theorem tmul_val (ε : ℕ) (X Y : Fin 256) : (tmul ε X Y : ℕ) = tmulN ε X Y := rfl

@[expose] noncomputable def encTFun (ε : ZMod 2) (X : ℕ) : T ε :=
  ⟨encR ⟨X % 128, Nat.mod_lt _ (by norm_num)⟩, ((X / 128 : ℕ) : ZMod 2)⟩

@[expose] noncomputable def encT (ε : ZMod 2) : Fin 256 ≃ T ε where
  toFun X := encTFun ε X
  invFun a := ⟨encR.symm a.x + 128 * a.e.val, by
    have := (encR.symm a.x).2; have := a.e.val_lt; omega⟩
  left_inv X := by
    apply Fin.ext
    have hX := X.2
    simp only [encTFun, Equiv.symm_apply_apply, ZMod.val_natCast]
    omega
  right_inv a := by
    have h1 := (encR.symm a.x).2
    have h2 := a.e.val_lt
    refine TwistExt.ext ?_ ?_
    · simp only [encTFun]
      rw [show ((⟨((encR.symm a.x : ℕ) + 128 * a.e.val) % 128, Nat.mod_lt _ (by norm_num)⟩ :
        Fin 128)) = encR.symm a.x from Fin.ext (by simp only; omega), Equiv.apply_symm_apply]
    · simp only [encTFun]
      rw [show ((encR.symm a.x : ℕ) + 128 * a.e.val) / 128 = a.e.val by omega,
        ZMod.natCast_zmod_val]

theorem encT_apply (ε : ZMod 2) (X : Fin 256) : encT ε X = encTFun ε X := rfl

theorem encTFun_mk (ε : ZMod 2) (x : Fin 128) (e : ℕ) :
    encTFun ε (x + 128 * e) = ⟨encR x, (e : ZMod 2)⟩ := by
  have hx := x.2
  refine TwistExt.ext ?_ ?_
  · exact congrArg encR (Fin.ext (by simp only; omega))
  · exact congrArg (fun n : ℕ => (n : ZMod 2)) (by omega)

theorem encR_zN (ε : ZMod 2) (e d : ℕ) (he : e < 2) (hd : d < 2) :
    encR ⟨zN (ε.val * e * d), by unfold zN; split_ifs <;> norm_num⟩ =
      TwistExt.zpow2 (zε ε) ((e : ZMod 2) * (d : ZMod 2)) := by
  have h0 : (0 : ZMod 2).val = 0 := rfl
  have h1 : (1 : ZMod 2).val = 1 := rfl
  rcases zmod2_cases ε with rfl | rfl <;> interval_cases e <;> interval_cases d <;>
    simp [zN, zε, TwistExt.zpow2, encR_zero, encR_64, h0, h1]

theorem encR_twist (e : ℕ) (he : e < 2) (y : Fin 128) :
    encR ⟨if e % 2 = 1 then tauN lamIdx y else y, by split_ifs; exacts [tauN_lt _ _, y.2]⟩ =
      TwistExt.twist tau (e : ZMod 2) (encR y) := by
  interval_cases e
  · simp [TwistExt.twist]
  · simp only [Nat.one_mod, ↓reduceIte, Nat.cast_one, TwistExt.twist]
    rw [← encR_tauF]
    rfl

theorem isTableModel_tmul (ε : ZMod 2) : IsTableModel (tmul ε.val) (encT ε) := by
  intro X Y
  have hX := X.2
  have hY := Y.2
  have he : (X : ℕ) / 128 < 2 := by omega
  have hd : (Y : ℕ) / 128 < 2 := by omega
  have hx : (X : ℕ) % 128 < 128 := Nat.mod_lt _ (by norm_num)
  have hy : (Y : ℕ) % 128 < 128 := Nat.mod_lt _ (by norm_num)
  have hX' : encT ε X = ⟨encR ⟨X % 128, hx⟩, (((X : ℕ) / 128 : ℕ) : ZMod 2)⟩ := rfl
  have hY' : encT ε Y = ⟨encR ⟨Y % 128, hy⟩, (((Y : ℕ) / 128 : ℕ) : ZMod 2)⟩ := rfl
  rw [hX', hY', encT_apply]
  simp only [tmul, tmulN]
  rw [encTFun_mk ε ⟨_, starN_lt _ _⟩]
  refine TwistExt.ext ?_ ?_
  · simp only [TwistExt.mul_def]
    rw [← encR_twist _ he ⟨_, hy⟩, ← encR_zN ε _ _ he hd, ← isTableModel_star,
      ← isTableModel_star]
    rfl
  · simp only [TwistExt.mul_def]
    rw [← Nat.cast_add]
    exact zmod2_eq_of_mod (Nat.mod_mod _ _)

theorem centerCheck_T (ε : ZMod 2) : centerCheckN 256 (tmulN ε.val) = true :=
  Certificates.certificate11001.2.2.1 ε

theorem mem_center_T (ε : ZMod 2) (w : T ε) :
    w ∈ Subgroup.center (T ε) ↔
      w = encT ε 0 ∨ w = encT ε 27 ∨ w = encT ε 64 ∨ w = encT ε 91 := by
  obtain ⟨z, rfl⟩ := (encT ε).surjective w
  rw [center_of_check (by norm_num) (tmul_val _) (isTableModel_tmul ε) (centerCheck_T ε) z,
    (encT ε).injective.eq_iff, (encT ε).injective.eq_iff, (encT ε).injective.eq_iff,
    (encT ε).injective.eq_iff]
  unfold isCentralLabel
  simp only [Bool.or_eq_true, beq_iff_eq, Fin.ext_iff, or_assoc]
  exact Iff.rfl

theorem rootCounts_T0_check :
    ((List.range 256).countP fun x => tmulN 0 x x == 27) = 0 ∧
    ((List.range 256).countP fun x => tmulN 0 (tmulN 0 x x) (tmulN 0 x x) == 27) = 0 ∧
    ((List.range 256).countP fun x => tmulN 0 x x == 64) = 24 ∧
    ((List.range 256).countP fun x => tmulN 0 (tmulN 0 x x) (tmulN 0 x x) == 64) = 32 ∧
    ((List.range 256).countP fun x => tmulN 0 x x == 91) = 40 ∧
    ((List.range 256).countP fun x => tmulN 0 (tmulN 0 x x) (tmulN 0 x x) == 91) = 32 :=
  Certificates.certificate11001.2.2.2.1

theorem rootCounts_T1_check :
    ((List.range 256).countP fun x => tmulN 1 x x == 27) = 16 ∧
    ((List.range 256).countP fun x => tmulN 1 (tmulN 1 x x) (tmulN 1 x x) == 27) = 0 ∧
    ((List.range 256).countP fun x => tmulN 1 x x == 64) = 40 ∧
    ((List.range 256).countP fun x => tmulN 1 (tmulN 1 x x) (tmulN 1 x x) == 64) = 32 ∧
    ((List.range 256).countP fun x => tmulN 1 x x == 91) = 24 ∧
    ((List.range 256).countP fun x => tmulN 1 (tmulN 1 x x) (tmulN 1 x x) == 91) = 32 :=
  Certificates.certificate11001.2.2.2.2.1

theorem squares_T_check (ε : ZMod 2) :
    tmulN ε.val 27 27 = 0 ∧ tmulN ε.val 64 64 = 0 ∧ tmulN ε.val 91 91 = 0 ∧
    (List.range 256).countP isCentralLabel = 4 :=
  Certificates.certificate11001.2.2.2.2.2 ε

theorem rootCounts_T0 :
    (rootCount 2 (encT 0 27), rootCount 4 (encT 0 27)) = (0, 0) ∧
    (rootCount 2 (encT 0 64), rootCount 4 (encT 0 64)) = (24, 32) ∧
    (rootCount 2 (encT 0 91), rootCount 4 (encT 0 91)) = (40, 32) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := rootCounts_T0_check
  simp only [rootCount_two_of_table (tmul_val _) (isTableModel_tmul 0),
    rootCount_four_of_table (tmul_val _) (isTableModel_tmul 0)]
  exact ⟨Prod.ext h1 h2, Prod.ext h3 h4, Prod.ext h5 h6⟩

theorem rootCounts_T1 :
    (rootCount 2 (encT 1 27), rootCount 4 (encT 1 27)) = (16, 0) ∧
    (rootCount 2 (encT 1 64), rootCount 4 (encT 1 64)) = (40, 32) ∧
    (rootCount 2 (encT 1 91), rootCount 4 (encT 1 91)) = (24, 32) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := rootCounts_T1_check
  simp only [rootCount_two_of_table (tmul_val _) (isTableModel_tmul 1),
    rootCount_four_of_table (tmul_val _) (isTableModel_tmul 1)]
  exact ⟨Prod.ext h1 h2, Prod.ext h3 h4, Prod.ext h5 h6⟩

theorem encT_zero (ε : ZMod 2) : encT ε 0 = 1 := by
  rw [encT_apply, show ((0 : Fin 256) : ℕ) = (0 : Fin 128) + 128 * 0 from rfl, encTFun_mk,
    encR_zero]
  rfl

theorem encT_inl (ε : ZMod 2) (x : Fin 128) :
    encT ε ⟨x, by have := x.2; omega⟩ = TwistExt.inl (encR x) := by
  rw [encT_apply, show ((⟨x, _⟩ : Fin 256) : ℕ) = x + 128 * 0 by simp, encTFun_mk]
  rfl

theorem encT_ne_one (ε : ZMod 2) {z : Fin 256} (hz : z ≠ 0) : encT ε z ≠ 1 := by
  rw [← encT_zero ε]
  exact fun h => hz ((encT ε).injective h)

theorem sq_encT (ε : ZMod 2) {z : Fin 256} (hz : tmulN ε.val z z = 0) : encT ε z ^ 2 = 1 := by
  rw [sq, ← isTableModel_tmul ε, ← encT_zero ε]
  exact congrArg (encT ε) (Fin.ext hz)

theorem center_T_elementary (ε : ZMod 2) :
    IsElementaryAbelian 2 (Subgroup.center (T ε)) ∧ Nat.card (Subgroup.center (T ε)) = 4 := by
  obtain ⟨h27, h64, h91, hc⟩ := squares_T_check ε
  refine ⟨isElementaryAbelian_center_of fun w hw => ?_, ?_⟩
  · rcases (mem_center_T ε w).1 hw with rfl | rfl | rfl | rfl
    · rw [encT_zero, one_pow]
    · exact sq_encT ε h27
    · exact sq_encT ε h64
    · exact sq_encT ε h91
  · rw [card_center_of_check (center_of_check (by norm_num) (tmul_val _) (isTableModel_tmul ε)
      (centerCheck_T ε)), hc]

theorem aut_fixes_center_T0 (φ : MulAut (T 0)) : ∀ w ∈ Subgroup.center (T 0), φ w = w := by
  obtain ⟨h27, h64, h91⟩ := rootCounts_T0
  refine aut_fixes_center (z₁ := encT 0 27) (z₂ := encT 0 64) (z₃ := encT 0 91)
    (fun w => by rw [mem_center_T, encT_zero])
    (encT_ne_one _ (by decide)) (encT_ne_one _ (by decide)) (encT_ne_one _ (by decide)) ?_ ?_ ?_ φ
  · rw [h27, h64]; decide
  · rw [h27, h91]; decide
  · rw [h64, h91]; decide

theorem aut_fixes_center_T1 (φ : MulAut (T 1)) : ∀ w ∈ Subgroup.center (T 1), φ w = w := by
  obtain ⟨h27, h64, h91⟩ := rootCounts_T1
  refine aut_fixes_center (z₁ := encT 1 27) (z₂ := encT 1 64) (z₃ := encT 1 91)
    (fun w => by rw [mem_center_T, encT_zero])
    (encT_ne_one _ (by decide)) (encT_ne_one _ (by decide)) (encT_ne_one _ (by decide)) ?_ ?_ ?_ φ
  · rw [h27, h64]; decide
  · rw [h27, h91]; decide
  · rw [h64, h91]; decide

theorem aut_fixes_center_T (ε : ZMod 2) (φ : MulAut (T ε)) :
    ∀ w ∈ Subgroup.center (T ε), φ w = w := by
  fin_cases ε
  exacts [aut_fixes_center_T0 φ, aut_fixes_center_T1 φ]

end CFSG.ComponentClassification.M12Cover.InternalSylow
