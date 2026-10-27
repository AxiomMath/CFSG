module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3E

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

local notation "actΓ" => CFSG.RankThree.PartOne.U5K.Hyp.act

theorem mul_mat_sSU_apply (A : Matrix (HypIndex 2 1) (HypIndex 2 1) K) (i j : HypIndex 2 1) :
    (A * mat (sSU h)) i j = A i (σs j) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (σs j) (fun w _ hw => by
      rw [mat_sSU, ite_eq_right (fun e => hw (by rw [← e, σs_σs])), mul_zero]) (by simp),
    mat_sSU, σs_σs, ite_eq_left rfl, mul_one]

theorem mat_sSU_mul_apply (A : Matrix (HypIndex 2 1) (HypIndex 2 1) K) (i j : HypIndex 2 1) :
    (mat (sSU h) * A) i j = A (σs i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (σs i) (fun w _ hw => by
      rw [mat_sSU, ite_eq_right (fun e => hw e.symm), zero_mul]) (by simp),
    mat_sSU, ite_eq_left rfl, one_mul]

theorem exists_eq_innM_of_act_N₂ {x : Gam h} (hcol : ∀ a, a ≠ ιe₁ → lmat x a ιe₁ = 0)
    (hrow : ∀ b, b ≠ ιf₁ → lmat x ιf₁ b = 0)
    (hN : ∀ n ∈ N₂sub h, n ∈ hypUnitriangular h 2 1 → ∃ v ∈ A₂sub h, actΓ h x n = v * n)
    (hs : ∃ v ∈ A₂sub h, actΓ h x (sSU h) = v * sSU h) {k : ℕ} (hk : Phi h x ^ 2 ^ k = 1) :
    ∃ u ∈ A₂sub h, Phi h x = innM h u := by
  have := h.charP
  have hσ := right_eq_one_of_act_N₂ hcol hrow hN
  have hmap : ∀ g : hypSU h 2 1, (mat g).map x.1.right = mat g := by
    intro g
    rw [hσ]
    ext a b
    rfl
  set A := lmat x with hAdef
  have key : ∀ n ∈ N₂sub h, (∃ v ∈ A₂sub h, actΓ h x n = v * n) → ∀ i j : HypIndex 2 1,
      i ≠ ιe₁ → i ≠ ιf₁ → j ≠ ιf₁ → (A * mat n) i j = (mat n * A) i j := by
    rintro n hn ⟨v, hv, hvn⟩ i j hi1 hi2 hj
    have hrel := lmat_mul_map x n
    rw [hmap, hvn, mat_mul, Matrix.mul_assoc] at hrel
    rw [hrel, A₂sub_mul_apply hv _ hi1 hi2]
    have : (mat n * A) ιf₁ j = 0 := by
      rw [Matrix.mul_apply, Finset.sum_eq_single ιf₁ (fun k _ hk => by
        rw [(N₂sub_rows hn k).2, one_apply_ne (Ne.symm hk), zero_mul]) (by simp),
        (N₂sub_rows hn _).2, one_apply_eq, one_mul, hrow j hj]
    rw [this, mul_zero, add_zero]
  obtain ⟨n₁, hn₁, hn₁e⟩ := exists_rootI₆ h (map_one h.bar)
  have hn₁N := patSub_sI₆_le_N₂sub hn₁
  obtain ⟨hn₁U, -, a2, a3, a4, a5, a6, a7, a8, -⟩ := mem_patSub_sI₆.1 hn₁
  obtain ⟨⟨-, d2, d3, -, d5⟩, ⟨l1, l2, l3, -, l5, l6, -, l8, l9, l10⟩⟩ := U_entries hn₁U
  have k1 := key n₁ hn₁N (hN n₁ hn₁N hn₁U) ιe₂ ιz (by decide) (by decide) (by decide)
  have k2 := key n₁ hn₁N (hN n₁ hn₁N hn₁U) ιz ιf₂ (by decide) (by decide) (by decide)
  have k3 := key n₁ hn₁N (hN n₁ hn₁N hn₁U) ιf₂ ιf₂ (by decide) (by decide) (by decide)
  simp only [Matrix.mul_apply, sum_hypIndex_two, a2, a3, a4, a5, a6, a7, a8, d2, d3, d5, l1, l2,
    l3, l5, l6, l8, l9, l10, hn₁e, mul_zero, zero_mul, mul_one, one_mul, add_zero,
    zero_add] at k1 k2 k3
  have hfz : A ιf₂ ιz = 0 := by linear_combination k1.symm
  have hze : A ιz ιe₂ = 0 := by linear_combination k2
  have hfe : A ιf₂ ιe₂ = 0 := by linear_combination k3
  have hez : A ιe₂ ιe₂ = A ιz ιz := by
    obtain ⟨c, hc⟩ := trace_surj (hK := h) (a := 1 * h.bar 1)
      (by rw [map_mul, h.bar_bar, mul_comm])
    obtain ⟨n, hn, hnu, hnc⟩ := exists_rootI₂ h hc
    have hnN := patSub_sI₂_le_N₂sub hn
    obtain ⟨hnU, -, -, b3, -, -, b6, -⟩ := mem_patSub_sI₂.1 hn
    obtain ⟨⟨-, e2, e3, -, -⟩, ⟨m1, -, -, -, -, -, -, m8, m9, -⟩⟩ := U_entries hnU
    have k := key n hnN (hN n hnN hnU) ιe₂ ιz (by decide) (by decide) (by decide)
    simp only [Matrix.mul_apply, sum_hypIndex_two, b3, b6, e2, e3, m1, m8, m9, hnu, hnc, hfz,
      mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add] at k
    linear_combination k
  have ks := key (sSU h) sSU_mem_N₂sub hs
  have s1 := ks ιe₂ ιe₂ (by decide) (by decide) (by decide)
  have s2 := ks ιe₂ ιz (by decide) (by decide) (by decide)
  have s3 := ks ιz ιe₂ (by decide) (by decide) (by decide)
  have s4 := ks ιf₂ ιe₂ (by decide) (by decide) (by decide)
  have σe : σs ιe₂ = ιf₂ := by decide
  have σz : σs ιz = ιz := by decide
  have σf : σs ιf₂ = ιe₂ := by decide
  rw [mul_mat_sSU_apply, mat_sSU_mul_apply] at s1 s2 s3 s4
  simp only [σe, σz, σf] at s1 s2 s3 s4
  have hef : A ιe₂ ιf₂ = 0 := by rw [s1, hfe]
  have hezz : A ιe₂ ιz = 0 := by rw [s2, hfz]
  have hzf : A ιz ιf₂ = 0 := by rw [s3, hze]
  have hff : A ιf₂ ιf₂ = A ιz ιz := by rw [s4, hez]
  have hcolN : ∀ N : ℕ, ∀ b, (A ^ N) b ιe₁ =
      (1 : Matrix (HypIndex 2 1) (HypIndex 2 1) K) b ιe₁ * A ιe₁ ιe₁ ^ N := by
    intro N
    induction N with
    | zero => intro b; simp
    | succ N ih =>
      intro b
      rw [pow_succ, Matrix.mul_apply, Finset.sum_eq_single ιe₁ (fun w _ hw => by
        rw [hcol w hw, mul_zero]) (by simp), ih, pow_succ, mul_assoc]
  have hzN : ∀ N : ℕ, (A ^ N) ιz ιz = A ιz ιz ^ N := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [pow_succ, Matrix.mul_apply, sum_hypIndex_two, hcolN, ih, one_apply_ne (by decide),
        hezz, hrow ιz (by decide), hfz, pow_succ]
      ring
  have hker : Phi h (x ^ 2 ^ k) = 1 := by rw [map_pow, hk]
  obtain ⟨-, c₀, hc₀⟩ := Phi_eq_one_iff.1 hker
  have hleft : (x ^ 2 ^ k).1.left = x.1.left ^ 2 ^ k := by
    rw [Subgroup.coe_pow]
    exact (left_pow_of_right_one hσ _).1
  rw [hleft] at hc₀
  have hAN : ∀ a, (A ^ 2 ^ k) a a = c₀ := by
    intro a
    have e := congrArg (fun B : GL (HypIndex 2 1) K =>
      (B : Matrix (HypIndex 2 1) (HypIndex 2 1) K) a a) hc₀
    show (lmat x ^ 2 ^ k) a a = c₀
    simpa only [lmat, Units.val_pow_eq_pow_val, GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.diagonal_apply_eq] using e
  have hl0 : A ιe₁ ιe₁ ≠ 0 := lmat_e₁e₁_ne_zero hcol
  have hlμ : A ιe₁ ιe₁ = A ιz ιz := by
    have e1 := hAN ιe₁
    rw [hcolN, one_apply_eq, one_mul] at e1
    have e2 := hAN ιz
    rw [hzN] at e2
    have e : (A ιe₁ ιe₁ - A ιz ιz) ^ 2 ^ k = 0 := by rw [sub_pow_char_pow, e1, e2, sub_self]
    exact sub_eq_zero.1 (pow_eq_zero_iff (by positivity) |>.1 e)
  have hA : ∀ a ∈ A₂sub h, ∃ z ∈ ZPsub h, actΓ h x a = z * a := by
    intro a ha
    set b := actΓ h x a with hb
    have hbA : b ∈ A₂sub h := act_mem_A₂sub hcol hrow ha
    have hrel : A * mat a = mat b * A := by
      have := lmat_mul_map x a
      rwa [hmap] at this
    obtain ⟨-, ⟨d22, l32, l42, l52⟩, ⟨u23, d33, l43, l53⟩, ⟨u25, u35, l45, d55⟩, -, -⟩ :=
      A₂sub_entries ha
    obtain ⟨b11, -, -, -, -, -⟩ := A₂sub_entries hbA
    have r1 := congrFun (congrFun hrel ιe₁) ιe₂
    have r2 := congrFun (congrFun hrel ιe₁) ιz
    have r3 := congrFun (congrFun hrel ιe₁) ιf₂
    simp only [Matrix.mul_apply, sum_hypIndex_two, d22, l32, l42, l52, u23, d33, l43, l53, u25,
      u35, l45, d55, b11, hze, hfe, hezz, hfz, hef, hzf, hrow ιe₂ (by decide),
      hrow ιz (by decide), hrow ιf₂ (by decide), hff, hez, mul_zero, mul_one,
      one_mul, add_zero] at r1 r2 r3
    have q1 : mat b ιe₁ ιe₂ = mat a ιe₁ ιe₂ :=
      mul_left_cancel₀ hl0 (by linear_combination -r1 + mat b ιe₁ ιe₂ * hlμ)
    have q2 : mat b ιe₁ ιz = mat a ιe₁ ιz :=
      mul_left_cancel₀ hl0 (by linear_combination -r2 + mat b ιe₁ ιz * hlμ)
    have q3 : mat b ιe₁ ιf₂ = mat a ιe₁ ιf₂ :=
      mul_left_cancel₀ hl0 (by linear_combination -r3 + mat b ιe₁ ιf₂ * hlμ)
    have hza : b * a⁻¹ ∈ A₂sub h := mul_mem hbA (inv_mem ha)
    obtain ⟨p1, p2, p3, -⟩ := A₂_mul hbA (inv_mem ha)
    obtain ⟨i1, i2, i3⟩ := A₂_inv_mul ha (one_mem _)
    rw [mul_one, mat_one, one_apply_ne (by decide), add_zero] at i1
    rw [mul_one, mat_one, one_apply_ne (by decide), add_zero] at i2
    rw [mul_one, mat_one, one_apply_ne (by decide), add_zero] at i3
    refine ⟨b * a⁻¹, mem_ZPsub_of_A₂ hza ?_ ?_ ?_, (inv_mul_cancel_right b a).symm⟩
    · rw [p1, q1, i1, CharTwo.add_self_eq_zero]
    · rw [p2, q2, i2, CharTwo.add_self_eq_zero]
    · rw [p3, q3, i3, CharTwo.add_self_eq_zero]
  exact exists_eq_innM_of_fixes_A₂ hcol hrow hA

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem Hyp.mem_B₂_of_commutator_N₂_mem_A₂ (hd : d.Hyp) {c : G}
    (hc : c ∈ normalizer (d.B₂ : Set G) ⊓ centralizer ({d.t} : Set G))
    (hcN : ∀ n ∈ d.N₂, c * n * c⁻¹ * n⁻¹ ∈ d.A₂) {k : ℕ} (hk : c ^ 2 ^ k = 1) :
    c ∈ d.B₂ := by
  obtain ⟨hcB, hct⟩ := Subgroup.mem_inf.1 hc
  have hcL := hd.centralizer_le_normalizer hct
  have hcZ : c ∈ normalizer (d.ZtP : Set G) := by
    rw [← hd.centerIn_B₂]
    exact mem_normalizer_centerIn hcB
  obtain ⟨y, hy⟩ := Phi_surjective h (d.act ⟨c, hcL⟩)
  obtain ⟨hcol, hrow⟩ := hd.lift_flag hcZ hcL hy
  have hN : ∀ n ∈ N₂sub h, n ∈ hypUnitriangular h 2 1 →
      ∃ v ∈ A₂sub h, actΓ h y n = v * n := by
    intro n hn hnU
    obtain ⟨v, hv, hve⟩ := hcN _ ⟨n, hn, rfl⟩
    refine ⟨v, hv, ?_⟩
    have e : d.η (actΓ h y n) = d.η (v * n) := by
      rw [← d.conj_η_eq hcL hy, map_mul, hve]
      group
    obtain ⟨k₁, hk₁⟩ := exists_pow_eq_one_of_mem_U hnU
    obtain ⟨k₂, hk₂⟩ := exists_pow_eq_one_of_mem_U (mul_mem (A₂sub_le_U hv) hnU)
    refine hd.eq_of_η_eq_of_two e (k := k₁ + k₂) ?_ ?_
    · rw [← act_pow, pow_add, pow_mul, hk₁, one_pow, CFSG.RankThree.PartOne.U5K.Hyp.act_one]
    · rw [pow_add, mul_comm, pow_mul, hk₂, one_pow]
  have hs : ∃ v ∈ A₂sub h, actΓ h y (sSU h) = v * sSU h := by
    obtain ⟨v, hv, hve⟩ := hcN _ ⟨sSU h, sSU_mem_N₂sub, rfl⟩
    refine ⟨v, hv, ?_⟩
    have e : d.η (actΓ h y (sSU h)) = d.η (v * sSU h) := by
      rw [← d.conj_η_eq hcL hy, map_mul, hve]
      group
    have hsinv : (sSU h)⁻¹ = sSU h := inv_eq_of_mul_eq_one_right sSU_mul_self
    have hvs : (v * sSU h) ^ 2 ∈ A₂sub h := by
      have e2 : (v * sSU h) ^ 2 = v * (sSU h * v * (sSU h)⁻¹) := by
        rw [hsinv, pow_two, mul_assoc, mul_assoc]
      rw [e2]
      exact mul_mem hv (conj_N₂sub_mem_A₂sub sSU_mem_N₂sub hv)
    obtain ⟨k₂, hk₂⟩ := exists_pow_eq_one_of_mem_U (A₂sub_le_U hvs)
    refine hd.eq_of_η_eq_of_two e (k := k₂ + 1) ?_ ?_
    · rw [← act_pow, pow_succ, mul_comm, pow_mul, sq, sSU_mul_self, one_pow,
        CFSG.RankThree.PartOne.U5K.Hyp.act_one]
    · rw [pow_succ, mul_comm, pow_mul, hk₂]
  have hk' : Phi h y ^ 2 ^ k = 1 := by
    rw [hy, ← map_pow]
    have e : (⟨c, hcL⟩ : normalizer (d.L : Set G)) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using hk)
    rw [e, map_one]
  obtain ⟨u, hu, hPhi⟩ := exists_eq_innM_of_act_N₂ hcol hrow hN hs hk'
  have hact : d.act ⟨c, hcL⟩ = d.act ⟨d.η u, le_normalizer (d.η_mem u)⟩ := by
    rw [← hy, hPhi, d.act_η]
  have hηN : d.η u ∈ normalizer (d.L : Set G) := le_normalizer (d.η_mem u)
  have hmem : (d.η u)⁻¹ * c ∈ normalizer (d.L : Set G) := mul_mem (inv_mem hηN) hcL
  have huc : (d.η u)⁻¹ * c ∈ centralizer (d.L : Set G) := by
    refine (d.act_eq_one_iff ⟨(d.η u)⁻¹ * c, hmem⟩).1 ?_
    have e : (⟨(d.η u)⁻¹ * c, hmem⟩ : normalizer (d.L : Set G)) =
        (⟨d.η u, hηN⟩ : normalizer (d.L : Set G))⁻¹ * ⟨c, hcL⟩ := rfl
    rw [e, map_mul, map_inv, hact, inv_mul_cancel]
  have hut : (d.η u)⁻¹ * c ∈ zpowers d.t := by
    rw [← hd.sec3_1'.1]
    have hηC : (d.η u)⁻¹ * c ∈ centralizer ({d.t} : Set G) :=
      mul_mem (inv_mem (hd.L_le_centralizer (d.η_mem u))) hct
    exact Subgroup.mem_inf.2 ⟨huc, hηC⟩
  rw [show c = d.η u * ((d.η u)⁻¹ * c) by group]
  exact mul_mem (mem_sup_right ⟨u, hu, rfl⟩) (mem_sup_left hut)

end Data

end CFSG.LocalAnalysis.EvenBN.U5
