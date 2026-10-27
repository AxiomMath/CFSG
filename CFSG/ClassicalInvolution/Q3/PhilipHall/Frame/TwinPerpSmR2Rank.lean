module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5GL2

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.R2

open Matrix CFSG.ClassicalInvolution.Q3.TA3

@[expose] def RankLeTwo (G : Type*) [Group G] : Prop :=
  ∀ x y z : G, x ^ 2 = 1 → y ^ 2 = 1 → z ^ 2 = 1 → x * y = y * x → x * z = z * x →
    y * z = z * y → x = 1 ∨ y = 1 ∨ z = 1 ∨ x = y ∨ x = z ∨ y = z ∨ x * y = z

theorem RankLeTwo.of_injective {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (h : RankLeTwo H) : RankLeTwo G := by
  intro x y z hx hy hz hxy hxz hyz
  have e : ∀ {a : G}, a ^ 2 = 1 → f a ^ 2 = 1 := fun ha => by rw [← map_pow, ha, map_one]
  have c : ∀ {a b : G}, a * b = b * a → f a * f b = f b * f a := fun hab => by
    rw [← map_mul, ← map_mul, hab]
  have i1 : ∀ {a : G}, f a = 1 → a = 1 := fun ha => hf (ha.trans (map_one f).symm)
  rcases h (f x) (f y) (f z) (e hx) (e hy) (e hz) (c hxy) (c hxz) (c hyz) with
    h1 | h1 | h1 | h1 | h1 | h1 | h1
  · exact Or.inl (i1 h1)
  · exact Or.inr (Or.inl (i1 h1))
  · exact Or.inr (Or.inr (Or.inl (i1 h1)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (hf h1))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hf h1)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hf h1))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hf (by rw [map_mul]; exact h1)))))))

theorem sq_mul_eq_one {G : Type*} [Group G] {u v : G} (hu : u ^ 2 = 1) (hv : v ^ 2 = 1)
    (huv : u * v = v * u) : (u * v) ^ 2 = 1 := by
  rw [pow_two] at hu hv ⊢
  calc u * v * (u * v) = u * (v * u) * v := by group
    _ = u * (u * v) * v := by rw [huv]
    _ = (u * u) * (v * v) := by group
    _ = 1 := by rw [hu, hv, one_mul]

theorem rankLeTwo_of_pred {G : Type*} [Group G] (P : G → Prop)
    (hP : ∀ u v : G, u ^ 2 = 1 → v ^ 2 = 1 → u * v = v * u → ¬ P u → ¬ P v → P (u * v))
    (hE : ∀ u v : G, u ^ 2 = 1 → v ^ 2 = 1 → u * v = v * u → P u → P v →
      u = 1 ∨ v = 1 ∨ u = v) : RankLeTwo G := by
  intro x y z hx hy hz hxy hxz hyz
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨hx1, hy1, hz1, hxy', hxz', hyz', hxyz⟩ := hcon
  have hx' : x * x = 1 := by rw [← pow_two]; exact hx
  have hy' : y * y = 1 := by rw [← pow_two]; exact hy
  have hz' : z * z = 1 := by rw [← pow_two]; exact hz
  have sxy := sq_mul_eq_one hx hy hxy
  have sxz := sq_mul_eq_one hx hz hxz
  have syz := sq_mul_eq_one hy hz hyz
  have c1 : x * (y * z) = y * z * x := by
    rw [← mul_assoc, hxy, mul_assoc, hxz, ← mul_assoc]
  have c2 : y * (x * z) = x * z * y := by
    rw [← mul_assoc, ← hxy, mul_assoc, hyz, ← mul_assoc]
  have c3 : x * y * z = z * (x * y) := by
    rw [mul_assoc, hyz, ← mul_assoc, hxz, mul_assoc]
  have c4 : x * y * (x * z) = x * z * (x * y) := by
    calc x * y * (x * z) = x * (y * x) * z := by group
      _ = x * (x * y) * z := by rw [hxy]
      _ = (x * x) * (y * z) := by group
      _ = (x * x) * (z * y) := by rw [hyz]
      _ = x * (x * z) * y := by group
      _ = x * (z * x) * y := by rw [hxz]
      _ = x * z * (x * y) := by group
  have n1 : y * z ≠ 1 := fun h => hyz' (by
    calc y = y * (z * z) := by rw [hz', mul_one]
      _ = (y * z) * z := by group
      _ = z := by rw [h, one_mul])
  have n2 : x * z ≠ 1 := fun h => hxz' (by
    calc x = x * (z * z) := by rw [hz', mul_one]
      _ = (x * z) * z := by group
      _ = z := by rw [h, one_mul])
  have n3 : x * y ≠ 1 := fun h => hxy' (by
    calc x = x * (y * y) := by rw [hy', mul_one]
      _ = (x * y) * y := by group
      _ = y := by rw [h, one_mul])
  have n4 : x ≠ y * z := fun h => hxyz (by
    rw [h]
    calc y * z * y = y * (z * y) := by group
      _ = y * (y * z) := by rw [hyz]
      _ = (y * y) * z := by group
      _ = z := by rw [hy', one_mul])
  have n5 : y ≠ x * z := fun h => hxyz (by
    rw [h, ← mul_assoc, hx', one_mul])
  have n6 : x * y ≠ x * z := fun h => hyz' (mul_left_cancel h)
  by_cases px : P x <;> by_cases py : P y <;> by_cases pz : P z
  · rcases hE x y hx hy hxy px py with h | h | h
    exacts [hx1 h, hy1 h, hxy' h]
  · rcases hE x y hx hy hxy px py with h | h | h
    exacts [hx1 h, hy1 h, hxy' h]
  · rcases hE x z hx hz hxz px pz with h | h | h
    exacts [hx1 h, hz1 h, hxz' h]
  · rcases hE x (y * z) hx syz c1 px (hP y z hy hz hyz py pz) with h | h | h
    exacts [hx1 h, n1 h, n4 h]
  · rcases hE y z hy hz hyz py pz with h | h | h
    exacts [hy1 h, hz1 h, hyz' h]
  · rcases hE y (x * z) hy sxz c2 py (hP x z hx hz hxz px pz) with h | h | h
    exacts [hy1 h, n2 h, n5 h]
  · rcases hE (x * y) z sxy hz c3 (hP x y hx hy hxy px py) pz with h | h | h
    exacts [n3 h, hz1 h, hxyz h]
  · rcases hE (x * y) (x * z) sxy sxz c4 (hP x y hx hy hxy px py) (hP x z hx hz hxz px pz) with
      h | h | h
    exacts [n3 h, n2 h, n6 h]

theorem eq_of_sq_eq_one_of_isCyclic {C : Type*} [Group C] [Finite C] [IsCyclic C] {u v : C}
    (hu : u ^ 2 = 1) (hv : v ^ 2 = 1) : u = 1 ∨ v = 1 ∨ u = v := by
  by_cases hu1 : u = 1
  · exact Or.inl hu1
  by_cases hv1 : v = 1
  · exact Or.inr (Or.inl hv1)
  refine Or.inr (Or.inr ?_)
  have hou : orderOf u = 2 := orderOf_eq_prime hu hu1
  have hov : orderOf v = 2 := orderOf_eq_prime hv hv1
  have hz : Subgroup.zpowers u = Subgroup.zpowers v :=
    (IsCyclic.subgroup_eq_iff_card_eq).mpr (by rw [Nat.card_zpowers, Nat.card_zpowers, hou, hov])
  have hvu : v ∈ Subgroup.zpowers u := hz ▸ Subgroup.mem_zpowers v
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hvu
  rw [← zpow_mod_orderOf, hou] at hk
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_zero] at hk
    exact absurd hk.symm hv1
  · rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_one] at hk
    exact hk

theorem eq_of_mem_of_card_dvd_two {G : Type*} [Group G] {H : Subgroup G} (hH : Nat.card H ∣ 2)
    {u v : G} (hu : u ∈ H) (hv : v ∈ H) : u = 1 ∨ v = 1 ∨ u = v := by
  rcases (Nat.dvd_prime Nat.prime_two).mp hH with h1 | h2
  · have hbot : H = ⊥ := Subgroup.card_eq_one.mp h1
    rw [hbot, Subgroup.mem_bot] at hu
    exact Or.inl hu
  · by_cases hu1 : u = 1
    · exact Or.inl hu1
    by_cases hv1 : v = 1
    · exact Or.inr (Or.inl hv1)
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : H)).mp h2
    have h1 : (⟨u, hu⟩ : H) = y := hy _ fun h => hu1 (congrArg Subtype.val h)
    have h2 : (⟨v, hv⟩ : H) = y := hy _ fun h => hv1 (congrArg Subtype.val h)
    exact Or.inr (Or.inr (congrArg Subtype.val (h1.trans h2.symm)))

theorem r_mem_zpowers_r_one {m : ℕ} [NeZero m] (i : ZMod m) :
    DihedralGroup.r i ∈ Subgroup.zpowers (DihedralGroup.r (1 : ZMod m)) := by
  rw [Subgroup.mem_zpowers_iff]
  exact ⟨(i.val : ℤ), by rw [zpow_natCast, DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]⟩

theorem rankLeTwo_dihedral (m : ℕ) [NeZero m] : RankLeTwo (DihedralGroup m) := by
  refine rankLeTwo_of_pred (fun x => x ∈ Subgroup.zpowers (DihedralGroup.r (1 : ZMod m)))
    ?_ ?_
  · intro u v _ _ _ hu hv
    cases u with
    | r i => exact absurd (r_mem_zpowers_r_one i) hu
    | sr i =>
      cases v with
      | r j => exact absurd (r_mem_zpowers_r_one j) hv
      | sr j =>
        show DihedralGroup.sr i * DihedralGroup.sr j ∈ _
        rw [DihedralGroup.sr_mul_sr]
        exact r_mem_zpowers_r_one _
  · intro u v hu hv _ hu' hv'
    have hu2 : (⟨u, hu'⟩ : Subgroup.zpowers (DihedralGroup.r (1 : ZMod m))) ^ 2 = 1 :=
      Subtype.ext (by simpa using hu)
    have hv2 : (⟨v, hv'⟩ : Subgroup.zpowers (DihedralGroup.r (1 : ZMod m))) ^ 2 = 1 :=
      Subtype.ext (by simpa using hv)
    rcases eq_of_sq_eq_one_of_isCyclic hu2 hv2 with h | h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (Or.inl (congrArg Subtype.val h))
    · exact Or.inr (Or.inr (congrArg Subtype.val h))

theorem gl2_eq_one_or_neg_one {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) {A : GL (Fin 2) F}
    (hA : A * A = 1) (hdet : GeneralLinearGroup.det A = 1) : A = 1 ∨ A = -1 := by
  have hM : (A : Matrix (Fin 2) (Fin 2) F) * A = 1 := by
    have := congrArg (fun B : GL (Fin 2) F => (B : Matrix (Fin 2) (Fin 2) F)) hA
    simpa using this
  have hd : (A : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    have := congrArg (fun u : Fˣ => (u : F)) hdet
    simpa [GeneralLinearGroup.val_det_apply] using this
  set M := (A : Matrix (Fin 2) (Fin 2) F) with hMdef
  have e00 := congrFun (congrFun hM 0) 0
  have e01 := congrFun (congrFun hM 0) 1
  have e10 := congrFun (congrFun hM 1) 0
  have e11 := congrFun (congrFun hM 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq, Matrix.one_apply_ne, ne_eq,
    Fin.zero_eta, Fin.isValue, zero_ne_one, not_false_eq_true, one_ne_zero] at e00 e01 e10 e11
  rw [Matrix.det_fin_two] at hd
  have hs : (M 0 0 + M 1 1) ^ 2 = 2 * 2 := by linear_combination e00 + e11 + 2 * hd
  have hne : M 0 0 + M 1 1 ≠ 0 := by
    intro h0
    rw [h0] at hs
    exact mul_ne_zero h2 h2 (by rw [← hs]; ring)
  have hb : M 0 1 = 0 := by
    have : M 0 1 * (M 0 0 + M 1 1) = 0 := by linear_combination e01
    exact (mul_eq_zero.mp this).resolve_right hne
  have hc : M 1 0 = 0 := by
    have : M 1 0 * (M 0 0 + M 1 1) = 0 := by linear_combination e10
    exact (mul_eq_zero.mp this).resolve_right hne
  have had : M 0 0 * M 1 1 = 1 := by rw [hb, zero_mul, sub_zero] at hd; exact hd
  have ha2 : M 0 0 * M 0 0 = 1 := by rw [hb, zero_mul, add_zero] at e00; exact e00
  have hda : M 1 1 = M 0 0 := by
    calc M 1 1 = M 1 1 * (M 0 0 * M 0 0) := by rw [ha2, mul_one]
      _ = (M 0 0 * M 1 1) * M 0 0 := by ring
      _ = M 0 0 := by rw [had, one_mul]
  rcases mul_self_eq_one_iff.mp ha2 with h | h
  · left
    ext i j
    fin_cases i <;> fin_cases j <;> simp [← hMdef, h, hda, hb, hc]
  · right
    ext i j
    fin_cases i <;> fin_cases j <;> simp [← hMdef, h, hda, hb, hc]

theorem rankLeTwo_gl2 {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) : RankLeTwo (GL (Fin 2) F) := by
  have hdet2 : ∀ A : GL (Fin 2) F, A ^ 2 = 1 →
      GeneralLinearGroup.det A = 1 ∨ GeneralLinearGroup.det A = -1 := by
    intro A hA
    have h1 : (GeneralLinearGroup.det A : F) * GeneralLinearGroup.det A = 1 := by
      have := congrArg (fun B : GL (Fin 2) F => ((GeneralLinearGroup.det B : Fˣ) : F)) hA
      simpa [pow_two] using this
    rcases mul_self_eq_one_iff.mp h1 with h | h
    · exact Or.inl (Units.ext h)
    · exact Or.inr (Units.ext (by rw [h, Units.val_neg, Units.val_one]))
  refine rankLeTwo_of_pred (fun A => GeneralLinearGroup.det A = 1) ?_ ?_
  · intro u v hu hv _ hu1 hv1
    show GeneralLinearGroup.det (u * v) = 1
    rw [map_mul, (hdet2 u hu).resolve_left hu1, (hdet2 v hv).resolve_left hv1, neg_mul_neg,
      one_mul]
  · intro u v hu hv _ hu1 hv1
    rw [pow_two] at hu hv
    rcases gl2_eq_one_or_neg_one h2 hu hu1 with h | h
    · exact Or.inl h
    rcases gl2_eq_one_or_neg_one h2 hv hv1 with h' | h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr (h.trans h'.symm))

theorem rankLeTwo_range_of_cubeKer {F : Type} [Field F] (h2 : (2 : F) ≠ 0)
    {H : Subgroup (GL (Fin 2) F)} {X : Type} [Group X] {π : H →* X} (hk : Q5GL2.CubeKer π) :
    RankLeTwo ↥π.range := by
  have hlift : ∀ x : ↥π.range, x ^ 2 = 1 → ∃ A : H, A ^ 2 = 1 ∧ π A = x := by
    intro x hx
    obtain ⟨B, hB⟩ := x.2
    have hx' : (x : X) ^ 2 = 1 := by
      have := congrArg Subtype.val hx
      simpa using this
    refine ⟨B ^ 3, ?_, ?_⟩
    · have h1 : π (B ^ 2) = 1 := by rw [map_pow, hB, hx']
      obtain ⟨ω, hω, hBω⟩ := hk (B ^ 2) h1
      apply Subtype.ext
      have e : ((B ^ 3) ^ 2 : H) = (B ^ 2) ^ 3 := by rw [← pow_mul, ← pow_mul]
      rw [e, Subgroup.coe_pow, hBω, ← map_pow, hω, map_one, Subgroup.coe_one]
    · rw [map_pow, hB, pow_succ, hx', one_mul]
  have hcomm : ∀ A B : H, A ^ 2 = 1 → B ^ 2 = 1 → π A * π B = π B * π A → A * B = B * A := by
    intro A B _ hB hAB
    have h1 : π (A * B * A⁻¹ * B⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hAB]
      group
    obtain ⟨ω, hω, hc⟩ := hk _ h1
    set s : GL (Fin 2) F := GeneralLinearGroup.scalar (Fin 2) ω with hs
    set a : GL (Fin 2) F := (A : GL (Fin 2) F) with ha
    set b : GL (Fin 2) F := (B : GL (Fin 2) F) with hb
    have hc' : a * b * a⁻¹ * b⁻¹ = s := by rw [ha, hb, ← hc]; simp
    have hbb : b * b = 1 := by
      have := congrArg Subtype.val hB
      simpa [pow_two] using this
    have hsb : s * b = b * s := Q5GL2.scalar_mul_comm ω b
    have hab : a * b = s * (b * a) := by
      calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
        _ = s * (b * a) := by rw [hc']
    have habb : a * (b * b) = s * s * ((b * b) * a) := by
      calc a * (b * b) = (a * b) * b := by group
        _ = (s * (b * a)) * b := by rw [hab]
        _ = s * (b * (a * b)) := by group
        _ = s * (b * (s * (b * a))) := by rw [hab]
        _ = s * ((b * s) * (b * a)) := by group
        _ = s * ((s * b) * (b * a)) := by rw [hsb]
        _ = s * s * ((b * b) * a) := by group
    rw [hbb, mul_one, one_mul] at habb
    have hss : s * s = 1 := by
      have := congrArg (fun g => g * a⁻¹) habb
      simpa using this.symm
    have hs3 : s ^ 3 = 1 := by rw [hs, ← map_pow, hω, map_one]
    have hs1 : s = 1 := by
      calc s = s ^ 3 * (s * s)⁻¹ := by group
        _ = 1 := by rw [hs3, hss, inv_one, one_mul]
    apply Subtype.ext
    show a * b = b * a
    rw [hab, hs1, one_mul]
  intro x y z hx hy hz hxy hxz hyz
  obtain ⟨A, hA, hAx⟩ := hlift x hx
  obtain ⟨B, hB, hBy⟩ := hlift y hy
  obtain ⟨C, hC, hCz⟩ := hlift z hz
  have cv : ∀ {u v : ↥π.range}, u * v = v * u → (u : X) * v = v * u := fun h => by
    have := congrArg Subtype.val h
    simpa using this
  have hAB := hcomm A B hA hB (by rw [hAx, hBy]; exact cv hxy)
  have hAC := hcomm A C hA hC (by rw [hAx, hCz]; exact cv hxz)
  have hBC := hcomm B C hB hC (by rw [hBy, hCz]; exact cv hyz)
  have sq : ∀ {D : H}, D ^ 2 = 1 → (D : GL (Fin 2) F) ^ 2 = 1 := fun hD => by
    rw [← Subgroup.coe_pow, hD, Subgroup.coe_one]
  have cm : ∀ {D E : H}, D * E = E * D → (D : GL (Fin 2) F) * E = E * D := fun hDE => by
    rw [← Subgroup.coe_mul, hDE, Subgroup.coe_mul]
  have ext1 : ∀ {D : H} {u : ↥π.range}, π D = u → (D : GL (Fin 2) F) = 1 → u = 1 := by
    intro D u hD h1
    apply Subtype.ext
    rw [← hD, show D = 1 from Subtype.ext h1, map_one, Subgroup.coe_one]
  have ext2 : ∀ {D E : H} {u v : ↥π.range}, π D = u → π E = v →
      (D : GL (Fin 2) F) = E → u = v := by
    intro D E u v hD hE h1
    apply Subtype.ext
    rw [← hD, ← hE, show D = E from Subtype.ext h1]
  rcases rankLeTwo_gl2 h2 A B C (sq hA) (sq hB) (sq hC) (cm hAB) (cm hAC) (cm hBC) with
    h | h | h | h | h | h | h
  · exact Or.inl (ext1 hAx h)
  · exact Or.inr (Or.inl (ext1 hBy h))
  · exact Or.inr (Or.inr (Or.inl (ext1 hCz h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (ext2 hAx hBy h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ext2 hAx hCz h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ext2 hBy hCz h))))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))))
    apply Subtype.ext
    rw [Subgroup.coe_mul, ← hAx, ← hBy, ← hCz, ← map_mul, show A * B = C from Subtype.ext
      (by rw [Subgroup.coe_mul]; exact h)]

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.R2
