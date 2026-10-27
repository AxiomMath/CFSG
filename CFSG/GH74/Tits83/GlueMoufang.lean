module

public import CFSG.GH74.Tits83.GlueMoves

public section

namespace CFSG.GH74.Tits83

open CFSG.GH74.BNPair

open scoped commutatorElement Pointwise

universe u

variable {X : Type u} [Group X]

theorem not_mem_Uminus_mul_B_of_ne_one (D : RankTwoSystem X 8) (m : D.N)
    (hm : (m : D.Weyl) ≠ 1) : (m : X) ∉ D.Vm * (D.B : Set X) := by
  rintro ⟨u, hu, b, hb, hm_eq⟩
  let xU : X := ((liftZero D)⁻¹ : X) * u * (((liftZero D)⁻¹ : X))⁻¹
  have hxU : xU ∈ D.U := conj_liftZero_inv_Uminus (D := D) ((D.mem_Vm_iff).1 hu)
  have hxUB : xU ∈ D.B := D.U_le_B hxU
  have hu_eq : u = ((liftZero D : D.N) : X) * xU * (((liftZero D : D.N) : X))⁻¹ := by
    simp only [xU]
    group
  have hprod : ((liftZero D)⁻¹ : X) * (m : X) =
      xU * ((liftZero D)⁻¹ : X) * b := by
    rw [← hm_eq, hu_eq]
    group
  have hdc_zero : ((liftZero D)⁻¹ : X) * (m : X) ∈ dc D.B D.N D.w₀ := by
    refine (mem_dc_of_lift (w := D.w₀) (n := (liftZero D)⁻¹)
      (liftZero_inv_mk D)).2 ⟨xU, hxUB, b, hb, hprod⟩
  have hN : (((liftZero D)⁻¹ * m : D.N) : X) ∈
      dc D.B D.N (((liftZero D)⁻¹ * m : D.N) : D.Weyl) :=
    coe_mem_dc (B := D.B) (N := D.N) _
  have hmk : (((liftZero D)⁻¹ * m : D.N) : D.Weyl) = D.w₀ * (m : D.Weyl) := by
    rw [QuotientGroup.mk_mul, liftZero_inv_mk]
  have hdc_mid : ((liftZero D)⁻¹ : X) * (m : X) ∈
      dc D.B D.N (D.w₀ * (m : D.Weyl)) := by
    have h := hN
    rw [hmk] at h
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h
  have hne : D.w₀ * (m : D.Weyl) ≠ D.w₀ := by
    intro h
    apply hm
    have := congrArg (fun z => D.w₀⁻¹ * z) h
    simpa [← mul_assoc, w₀_mul_self D] using this
  exact (Set.disjoint_left.1 (D.isTits.pairwise_disjoint_dc hne)) hdc_mid hdc_zero

theorem not_mem_Uminus_mul_B (D : RankTwoSystem X 8) :
    ((liftOne D : D.N) : X) ∉ D.Vm * (D.B : Set X) := by
  refine not_mem_Uminus_mul_B_of_ne_one D (liftOne D) ?_
  rw [liftOne_mk]
  exact D.isTits.gen_ne_one (s := D.w₁) (by simp)

theorem not_mem_Uminus_mul_B_liftTwo (D : RankTwoSystem X 8) :
    ((liftTwo D : D.N) : X) ∉ D.Vm * (D.B : Set X) := by
  refine not_mem_Uminus_mul_B_of_ne_one D (liftTwo D) ?_
  rw [liftTwo_mk]
  exact D.isTits.gen_ne_one (s := D.w₂) (by simp)

theorem lemmaA (D : RankTwoSystem X 8) {g : X}
    (hg : g ∈ chainProd D.root ((intList 2 8).map Neg.neg)) (hP : g ∈ D.P₁) : g = 1 := by
  have hgVm : g ∈ D.Vm := Vminus_subset_Vm (by simpa [Vminus] using hg)
  rcases (mem_parabolic_single_iff D.isTits
    (s := D.w₁) (by simp)).1 hP with hB | hdc
  · exact D.eq_one_of_mem_U_Vm hB hgVm
  · obtain ⟨b, hb, x, hx, hg_eq⟩ :=
      D.dc_panel_w₁ (liftOne D) (liftOne_mk D) hdc
    have hxB : x ∈ D.B := D.root_le_B (by norm_num) (by norm_num) hx
    have hact := D.actsPos_lift₁ (liftOne D) (liftOne_mk D)
    have hx0 : x ∈ D.root (Rt 8 0) := by
      rw [Rt_of_lt (by norm_num) (by norm_num)]
      simpa using hx
    have hx' : ((liftOne D : D.N) : X) * x * (((liftOne D : D.N) : X))⁻¹ ∈ D.Vm := by
      have h1 := hact 0 x hx0
      change _ ∈ D.root (Rt 8 (8 - 0)) at h1
      have e : Rt 8 (8 - 0) = -1 := by
        rw [Rt_of_ge (by norm_num) (by norm_num)]
        norm_num
      rw [e] at h1
      exact D.root_le_V D.coe_Vm (by norm_num) (by norm_num) h1
    have hg₂ : ((liftOne D : D.N) : X) * g * (((liftOne D : D.N) : X))⁻¹ ∈ D.Vm :=
      Vminus_subset_Vm (conj_liftOne_Vminus (D := D) (by simpa [Vminus] using hg))
    have hbx : b * (((liftOne D : D.N) : X) * x * (((liftOne D : D.N) : X))⁻¹) =
        (((liftOne D : D.N) : X))⁻¹ * (((liftOne D : D.N) : X) * g *
          (((liftOne D : D.N) : X))⁻¹) := by
      calc b * (((liftOne D : D.N) : X) * x * (((liftOne D : D.N) : X))⁻¹)
          = (b * ((liftOne D : D.N) : X) * x) * (((liftOne D : D.N) : X))⁻¹ := by group
        _ = g * (((liftOne D : D.N) : X))⁻¹ := by rw [← hg_eq]
        _ = (((liftOne D : D.N) : X))⁻¹ * (((liftOne D : D.N) : X) * g *
              (((liftOne D : D.N) : X))⁻¹) := by group
    have hm1_eq : ((liftOne D : D.N) : X) =
        (((liftOne D : D.N) : X) * g * (((liftOne D : D.N) : X))⁻¹) *
          ((((liftOne D : D.N) : X) * x * (((liftOne D : D.N) : X))⁻¹)⁻¹) * b⁻¹ := by
      have := congrArg (fun z => ((liftOne D : D.N) : X) * z *
        ((((liftOne D : D.N) : X) * x * (((liftOne D : D.N) : X))⁻¹)⁻¹) * b⁻¹) hbx
      simpa [mul_assoc] using this
    exfalso
    refine (not_mem_Uminus_mul_B D) ⟨_, D.Vm.mul_mem hg₂ (D.Vm.inv_mem hx'),
      b⁻¹, D.B.inv_mem hb, hm1_eq.symm⟩

theorem conj_liftOne_inv_V {D : RankTwoSystem X 8} {x : X} (hx : x ∈ V D) :
    ((liftOne D)⁻¹ : X) * x * (((liftOne D)⁻¹ : X))⁻¹ ∈ V D := by
  obtain ⟨W, hWc, -, -, -⟩ := D.roots.subgroup 2 8 (by norm_num) (by norm_num) (by norm_num)
  unfold V at hx
  have hact := D.actsPos_lift₁ ((liftOne D)⁻¹) (liftOne_inv_mk D)
  have hconj := chainProd_conj_mem D.root W (((liftOne D)⁻¹ : D.N) : X) (intList 2 8)
    (fun k hk y hy => ?_) x hx
  · rw [← SetLike.mem_coe, hWc] at hconj
    exact hconj
  · obtain ⟨hk1, hk2⟩ := mem_intList_iff.1 hk
    have hy' : y ∈ D.root (Rt 8 (k - 1)) := by
      rwa [Rt_pos_idx (by omega) (by omega)]
    have h1 := hact (k - 1) y hy'
    change _ ∈ D.root (Rt 8 (8 - (k - 1))) at h1
    have e : Rt 8 (8 - (k - 1)) = 10 - k := by
      rw [show 8 - (k - 1) = 9 - k by ring, Rt_of_lt (by omega) (by omega)]
      ring
    rw [e] at h1
    have hmem := mem_chainProd_of_mem D.root (l := intList 2 8)
      (mem_intList_iff.2 ⟨by omega, by omega⟩) h1
    rw [← SetLike.mem_coe, hWc]
    exact hmem

theorem conj_liftZero_X1 {D : RankTwoSystem X 8} {x : X} (hx : x ∈ D.root 1) :
    ((liftZero D : D.N) : X) * x * (((liftZero D : D.N) : X))⁻¹ ∈ D.root (-1) := by
  have hm : ((liftZero D : D.N) : D.Weyl) = altWord D.w₁ D.w₂ 8 := by
    simpa [RankTwoSystem.w₀] using liftZero_mk D
  have hact : D.ActsPos ((liftZero D : D.N) : X) (fun q => q - 8) := by
    simpa [tauA_eight] using D.actsPos_altWord₁ 8 (liftZero D) hm
  have hx0 : x ∈ D.root (Rt 8 0) := by
    rw [Rt_of_lt (by norm_num) (by norm_num)]
    simpa using hx
  have h1 := hact 0 x hx0
  change _ ∈ D.root (Rt 8 (0 - 8)) at h1
  have e : Rt 8 (0 - 8) = -1 := by
    rw [show (0 : ℤ) - 8 = -8 by ring, Rt_of_neg (by norm_num) (by norm_num)]
    norm_num
  rwa [e] at h1

theorem conj_liftZero_Xminus1 {D : RankTwoSystem X 8} {x : X} (hx : x ∈ D.root (-1)) :
    ((liftZero D : D.N) : X) * x * (((liftZero D : D.N) : X))⁻¹ ∈ D.root 1 := by
  have hm : ((liftZero D : D.N) : D.Weyl) = altWord D.w₁ D.w₂ 8 := by
    simpa [RankTwoSystem.w₀] using liftZero_mk D
  have hact : D.ActsPos ((liftZero D : D.N) : X) (fun q => q - 8) := by
    simpa [tauA_eight] using D.actsPos_altWord₁ 8 (liftZero D) hm
  have hx8 : x ∈ D.root (Rt 8 8) := by
    have e : Rt 8 8 = -1 := by
      rw [Rt_of_ge (by norm_num) (by norm_num)]
      norm_num
    rwa [e]
  have h1 := hact 8 x hx8
  change _ ∈ D.root (Rt 8 (8 - 8)) at h1
  have e : Rt 8 (8 - 8) = 1 := by
    rw [show (8 : ℤ) - 8 = 0 by ring, Rt_of_lt (by norm_num) (by norm_num)]
    norm_num
  rwa [e] at h1

theorem Xminus1_le_P1 (D : RankTwoSystem X 8) : D.root (-1) ≤ D.P₁ := by
  intro x hx
  have haction := D.roots.action₁ (liftOne D) (liftOne_mk D)
  have hxconj : x ∈ conjBy ((liftOne D : D.N) : X) (D.root 1) := by
    rw [haction.1]
    exact hx
  have ha : ((liftOne D : D.N) : X) * x * (((liftOne D : D.N) : X))⁻¹ ∈ D.root 1 :=
    (mem_conjBy_iff).1 hxconj
  have haP : ((liftOne D : D.N) : X) * x * (((liftOne D : D.N) : X))⁻¹ ∈ D.P₁ :=
    (mem_parabolic_single_iff D.isTits (s := D.w₁) (by simp)).2
      (Or.inl (D.root_le_B (by norm_num) (by norm_num) ha))
  have hm1P : ((liftOne D : D.N) : X) ∈ D.P₁ :=
    (mem_parabolic_single_iff D.isTits (s := D.w₁) (by simp)).2
      (Or.inr (by rw [← liftOne_mk D]; exact coe_mem_dc (B := D.B) (N := D.N) (liftOne D)))
  have h := D.P₁.mul_mem (D.P₁.mul_mem (D.P₁.inv_mem hm1P) haP) hm1P
  simpa [mul_assoc] using h

theorem lemmaB (D : RankTwoSystem X 8) {y : X} (hy : y ∈ D.root (-1)) (hy1 : y ≠ 1) :
    ∃ v ∈ D.root 1, ∃ w ∈ D.root 1, ∃ m : D.N, (m : X) = v * y * w ∧ (m : D.Weyl) = D.w₁ := by
  have hyP : y ∈ D.P₁ := Xminus1_le_P1 D hy
  have hyVm : y ∈ D.Vm := D.root_le_V D.coe_Vm (by norm_num) (by norm_num) hy
  have hyB : y ∉ D.B := fun hb => hy1 (D.eq_one_of_mem_U_Vm hb hyVm)
  have hy_dc : y ∈ dc D.B D.N D.w₁ := by
    rcases (mem_parabolic_single_iff D.isTits (s := D.w₁) (by simp)).1 hyP with hB | hdc
    · exact absurd hB hyB
    · exact hdc
  obtain ⟨b, hb, x, hx, hy_eq⟩ := D.dc_panel_w₁ (liftOne D) (liftOne_mk D) hy_dc
  have hb' : b ∈ ((D.B ⊓ D.N : Subgroup X) : Set X) * (D.U : Set X) := by
    rw [← D.isSplit.2]
    exact hb
  obtain ⟨h, hh, u, hu, hb_eq⟩ := Set.mem_mul.1 hb'
  have hh' : h ∈ D.B ⊓ D.N := hh
  obtain ⟨a, ha, c, hc, hu_eq⟩ := D.U_decomp (i := 1) (by norm_num) u hu
  have ha1 : a ∈ D.root 1 := by
    simpa [intList, chainProd] using ha
  have hcV : c ∈ V D := hc
  have hx0 : h * a * h⁻¹ ∈ D.root 1 := H_conj_X1 (D := D) hh' ha1
  let mN : D.N := ⟨h, (Subgroup.mem_inf.1 hh').2⟩ * liftOne D
  have hh1 : ((⟨h, (Subgroup.mem_inf.1 hh').2⟩ : D.N) : D.Weyl) = 1 :=
    (mk_eq_one_iff (B := D.B) (N := D.N)).2 (Subgroup.mem_inf.1 hh').1
  have hmN : (mN : D.Weyl) = D.w₁ := by
    dsimp [mN]
    rw [hh1, one_mul, liftOne_mk]
  let v' : X := (((liftOne D)⁻¹ : D.N) : X) * c * ((((liftOne D)⁻¹ : D.N) : X))⁻¹
  have hv' : v' ∈ V D := conj_liftOne_inv_V (D := D) hcV
  have hy_decomp : y = (h * a * h⁻¹) * (mN : X) * v' * x := by
    rw [hy_eq, ← hb_eq, hu_eq]
    dsimp [mN, v']
    group
  have hweylN : (((liftZero D * mN⁻¹ * (liftZero D)⁻¹ : D.N) : D.Weyl)) = D.w₁ := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, liftZero_mk, hmN,
      liftZero_inv_mk D, inv_eq_of_mul_eq_one_right (D.rank2.dih.mul_self_a),
      w₀_comm_w₁, mul_assoc, w₀_mul_self, mul_one]
  have hNterm : ((liftZero D : D.N) : X) * (mN : X)⁻¹ * (((liftZero D : D.N) : X))⁻¹ ∈ D.P₁ := by
    have hmem : (((liftZero D * mN⁻¹ * (liftZero D)⁻¹ : D.N) : X)) ∈ dc D.B D.N D.w₁ := by
      have := coe_mem_dc (B := D.B) (N := D.N) (liftZero D * mN⁻¹ * (liftZero D)⁻¹)
      rwa [hweylN] at this
    have hX : ((liftZero D : D.N) : X) * (mN : X)⁻¹ * (((liftZero D : D.N) : X))⁻¹ ∈
        dc D.B D.N D.w₁ := by
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hmem
    exact (mem_parabolic_single_iff D.isTits (s := D.w₁) (by simp)).2 (Or.inr hX)
  have hx0term : ((liftZero D : D.N) : X) * (h * a * h⁻¹)⁻¹ *
      (((liftZero D : D.N) : X))⁻¹ ∈ D.P₁ :=
    Xminus1_le_P1 D (conj_liftZero_X1 (D := D) ((D.root 1).inv_mem hx0))
  have hyterm : ((liftZero D : D.N) : X) * y * (((liftZero D : D.N) : X))⁻¹ ∈ D.P₁ :=
    (mem_parabolic_single_iff D.isTits (s := D.w₁) (by simp)).2
      (Or.inl (D.root_le_B (by norm_num) (by norm_num)
        (conj_liftZero_Xminus1 (D := D) hy)))
  have hxterm : ((liftZero D : D.N) : X) * x⁻¹ * (((liftZero D : D.N) : X))⁻¹ ∈ D.P₁ :=
    Xminus1_le_P1 D (conj_liftZero_X1 (D := D) ((D.root 1).inv_mem hx))
  have hv'P : ((liftZero D : D.N) : X) * v' * (((liftZero D : D.N) : X))⁻¹ ∈ D.P₁ := by
    have hv'eq : v' = (mN : X)⁻¹ * (h * a * h⁻¹)⁻¹ * y * x⁻¹ := by
      rw [hy_decomp]
      dsimp [v']
      group
    have hfac : ((liftZero D : D.N) : X) * v' * (((liftZero D : D.N) : X))⁻¹ =
        (((liftZero D : D.N) : X) * (mN : X)⁻¹ * (((liftZero D : D.N) : X))⁻¹) *
        (((liftZero D : D.N) : X) * (h * a * h⁻¹)⁻¹ * (((liftZero D : D.N) : X))⁻¹) *
        (((liftZero D : D.N) : X) * y * (((liftZero D : D.N) : X))⁻¹) *
        (((liftZero D : D.N) : X) * x⁻¹ * (((liftZero D : D.N) : X))⁻¹) := by
      rw [hv'eq]
      group
    rw [hfac]
    exact D.P₁.mul_mem (D.P₁.mul_mem (D.P₁.mul_mem hNterm hx0term) hyterm) hxterm
  have hv'Vminus : ((liftZero D : D.N) : X) * v' * (((liftZero D : D.N) : X))⁻¹ ∈ Vminus D :=
    conj_liftZero_V (D := D) hv'
  have hzero : ((liftZero D : D.N) : X) * v' * (((liftZero D : D.N) : X))⁻¹ = 1 :=
    lemmaA D (by simpa [Vminus] using hv'Vminus) hv'P
  have hv'1 : v' = 1 := by
    have := congrArg (fun z => (((liftZero D : D.N) : X))⁻¹ * z *
      (((liftZero D : D.N) : X))) hzero
    simpa [mul_assoc] using this
  refine ⟨(h * a * h⁻¹)⁻¹, (D.root 1).inv_mem hx0, x⁻¹, (D.root 1).inv_mem hx, mN, ?_, hmN⟩
  rw [hy_decomp, hv'1]
  group

@[expose] def Vtwo (D : RankTwoSystem X 8) : Set X :=
  chainProd D.root (intList 1 7)

@[expose] def VminusTwo (D : RankTwoSystem X 8) : Set X :=
  chainProd D.root ((intList 1 7).map Neg.neg)

@[expose] noncomputable def VminusTwoSub (D : RankTwoSystem X 8) : Subgroup X :=
  Classical.choose (D.chainProd_good_plist (k := 6) (by norm_num) 8).1

theorem coe_VminusTwoSub (D : RankTwoSystem X 8) :
    (VminusTwoSub D : Set X) = chainProd D.root ((plist 8 6).map (Rt 8)) :=
  Classical.choose_spec (D.chainProd_good_plist (k := 6) (by norm_num) 8).1

theorem plist_eight_map_Rt :
    (plist 8 6).map (Rt 8) = (intList 1 7).map Neg.neg := by
  apply List.ext_getElem
  · simp [plist, intList]
  · intro t h1 h2
    simp only [plist, intList, List.length_map, List.length_range, List.getElem_map,
      List.getElem_range] at h1 h2 ⊢
    have ht : t < 7 := by simpa using h1
    rw [Rt_of_ge (by omega) (by omega)]
    ring

theorem coe_VminusTwoSub' (D : RankTwoSystem X 8) :
    (VminusTwoSub D : Set X) = VminusTwo D := by
  rw [coe_VminusTwoSub, plist_eight_map_Rt]
  rfl

theorem VminusTwo_subset_Vm {D : RankTwoSystem X 8} {x : X} (hx : x ∈ VminusTwo D) :
    x ∈ D.Vm := by
  unfold VminusTwo at hx
  rw [D.mem_Vm_iff, ← D.coe_Vm]
  refine chainProd_subset D.root D.Vm _ (fun k hk => ?_) hx
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hk
  obtain ⟨hj1, hj2⟩ := mem_intList_iff.1 hj
  exact D.root_le_V D.coe_Vm (by omega) (by omega)

theorem conj_liftTwo_inv_V {D : RankTwoSystem X 8} {x : X} (hx : x ∈ Vtwo D) :
    ((liftTwo D)⁻¹ : X) * x * (((liftTwo D)⁻¹ : X))⁻¹ ∈ Vtwo D := by
  obtain ⟨W, hWc, -, -, -⟩ := D.roots.subgroup 1 7 (by norm_num) (by norm_num) (by norm_num)
  unfold Vtwo at hx
  have hact := D.actsPos_lift₂ ((liftTwo D)⁻¹) (liftTwo_inv_mk D)
  have hconj := chainProd_conj_mem D.root W (((liftTwo D)⁻¹ : D.N) : X) (intList 1 7)
    (fun k hk y hy => ?_) x hx
  · rw [← SetLike.mem_coe, hWc] at hconj
    exact hconj
  · obtain ⟨hk1, hk2⟩ := mem_intList_iff.1 hk
    have hy' : y ∈ D.root (Rt 8 (k - 1)) := by
      rwa [Rt_pos_idx (by omega) (by omega)]
    have h1 := hact (k - 1) y hy'
    change _ ∈ D.root (Rt 8 (6 - (k - 1))) at h1
    have e : Rt 8 (6 - (k - 1)) = 8 - k := by
      rw [show 6 - (k - 1) = 7 - k by ring, Rt_of_lt (by omega) (by omega)]
      ring
    rw [e] at h1
    have hmem := mem_chainProd_of_mem D.root (l := intList 1 7)
      (mem_intList_iff.2 ⟨by omega, by omega⟩) h1
    rw [← SetLike.mem_coe, hWc]
    exact hmem

theorem conj_liftTwo_Vminus {D : RankTwoSystem X 8} {x : X} (hx : x ∈ VminusTwo D) :
    ((liftTwo D : D.N) : X) * x * (((liftTwo D : D.N) : X))⁻¹ ∈ VminusTwo D := by
  have hact := D.actsPos_lift₂ (liftTwo D) (liftTwo_mk D)
  rw [← coe_VminusTwoSub'] at hx ⊢
  rw [coe_VminusTwoSub] at hx ⊢
  have hx' : x ∈ chainProd (fun q => D.root (Rt 8 q)) (plist 8 6) := by
    rwa [← chainProd_comp]
  have hconj := chainProd_conj_mem (fun q => D.root (Rt 8 q)) (VminusTwoSub D)
    ((liftTwo D : D.N) : X) (plist 8 6) (fun q hq y hy => ?_) x hx'
  · change _ ∈ (VminusTwoSub D : Set X) at hconj
    rw [coe_VminusTwoSub, chainProd_comp] at hconj
    exact hconj
  · have hq' := mem_plist_iff.1 hq
    have h1 := hact q y hy
    change _ ∈ D.root (Rt 8 (6 - q)) at h1
    have e : Rt 8 (6 - q) = Rt 8 (22 - q) := by
      rw [← Rt_add_mul 8 (6 - q) 1]
      congr 1
      ring
    rw [e] at h1
    change _ ∈ (VminusTwoSub D : Set X)
    rw [coe_VminusTwoSub]
    refine mem_chainProd_of_mem D.root (List.mem_map.2 ⟨22 - q, ?_, rfl⟩) h1
    rw [mem_plist_iff]
    omega

theorem conj_liftZero_Vtwo {D : RankTwoSystem X 8} {x : X} (hx : x ∈ Vtwo D) :
    ((liftZero D : D.N) : X) * x * (((liftZero D : D.N) : X))⁻¹ ∈ VminusTwo D := by
  have hm : ((liftZero D : D.N) : D.Weyl) = altWord D.w₁ D.w₂ 8 := by
    simpa [RankTwoSystem.w₀] using liftZero_mk D
  have hact : D.ActsPos ((liftZero D : D.N) : X) (fun q => q - 8) := by
    simpa [tauA_eight] using D.actsPos_altWord₁ 8 (liftZero D) hm
  unfold Vtwo at hx
  rw [← coe_VminusTwoSub']
  rw [coe_VminusTwoSub]
  have hconj := chainProd_conj_mem D.root (VminusTwoSub D) ((liftZero D : D.N) : X)
    (intList 1 7) (fun k hk y hy => ?_) x hx
  · change _ ∈ (VminusTwoSub D : Set X) at hconj
    rw [coe_VminusTwoSub, chainProd_comp] at hconj
    exact hconj
  · obtain ⟨hk1, hk2⟩ := mem_intList_iff.1 hk
    have hy' : y ∈ D.root (Rt 8 (k - 1)) := by
      rwa [Rt_pos_idx (by omega) (by omega)]
    have h1 := hact (k - 1) y hy'
    change _ ∈ D.root (Rt 8 (k - 1 - 8)) at h1
    have e : Rt 8 (k - 1 - 8) = Rt 8 (k + 7) := by
      rw [← Rt_add_mul 8 (k - 1 - 8) 1]
      congr 1
      ring
    rw [e] at h1
    change _ ∈ (VminusTwoSub D : Set X)
    rw [coe_VminusTwoSub]
    refine mem_chainProd_of_mem D.root (List.mem_map.2 ⟨k + 7, ?_, rfl⟩) h1
    rw [mem_plist_iff]
    omega

theorem Xminus8_le_P2 (D : RankTwoSystem X 8) : D.root (-8) ≤ D.P₂ := by
  intro x hx
  have haction := D.roots.action₂ (liftTwo D) (liftTwo_mk D)
  have hxconj : x ∈ conjBy ((liftTwo D : D.N) : X) (D.root 8) := by
    change x ∈ conjBy ((liftTwo D : D.N) : X) (D.root ((8 : ℕ) : ℤ))
    rw [haction.1]
    simpa using hx
  have ha : ((liftTwo D : D.N) : X) * x * (((liftTwo D : D.N) : X))⁻¹ ∈ D.root 8 :=
    (mem_conjBy_iff).1 hxconj
  have haP : ((liftTwo D : D.N) : X) * x * (((liftTwo D : D.N) : X))⁻¹ ∈ D.P₂ :=
    (mem_parabolic_single_iff D.isTits (s := D.w₂) (by simp)).2
      (Or.inl (D.root_le_B (by norm_num) (by norm_num) ha))
  have hm2P : ((liftTwo D : D.N) : X) ∈ D.P₂ :=
    (mem_parabolic_single_iff D.isTits (s := D.w₂) (by simp)).2
      (Or.inr (by rw [← liftTwo_mk D]; exact coe_mem_dc (B := D.B) (N := D.N) (liftTwo D)))
  have h := D.P₂.mul_mem (D.P₂.mul_mem (D.P₂.inv_mem hm2P) haP) hm2P
  simpa [mul_assoc] using h

theorem lemmaA₂ (D : RankTwoSystem X 8) {g : X}
    (hg : g ∈ VminusTwo D) (hP : g ∈ D.P₂) : g = 1 := by
  have hgVm : g ∈ D.Vm := VminusTwo_subset_Vm hg
  rcases (mem_parabolic_single_iff D.isTits
    (s := D.w₂) (by simp)).1 hP with hB | hdc
  · exact D.eq_one_of_mem_U_Vm hB hgVm
  · obtain ⟨b, hb, x, hx, hg_eq⟩ :=
      D.dc_panel_w₂ (liftTwo D) (liftTwo_mk D) hdc
    have hxB : x ∈ D.B := D.root_le_B (by norm_num) (by norm_num) hx
    have hact := D.actsPos_lift₂ (liftTwo D) (liftTwo_mk D)
    have hx7 : x ∈ D.root (Rt 8 7) := by
      rw [Rt_of_lt (by norm_num) (by norm_num)]
      simpa using hx
    have hx' : ((liftTwo D : D.N) : X) * x * (((liftTwo D : D.N) : X))⁻¹ ∈ D.Vm := by
      have h1 := hact 7 x hx7
      change _ ∈ D.root (Rt 8 (6 - 7)) at h1
      have e : Rt 8 (6 - 7) = -8 := by
        rw [show (6 : ℤ) - 7 = -1 by ring, Rt_of_neg (by norm_num) (by norm_num)]
        norm_num
      rw [e] at h1
      exact D.root_le_V D.coe_Vm (by norm_num) (by norm_num) h1
    have hg₂ : ((liftTwo D : D.N) : X) * g * (((liftTwo D : D.N) : X))⁻¹ ∈ D.Vm :=
      VminusTwo_subset_Vm (conj_liftTwo_Vminus (D := D) hg)
    have hbx : b * (((liftTwo D : D.N) : X) * x * (((liftTwo D : D.N) : X))⁻¹) =
        (((liftTwo D : D.N) : X))⁻¹ * (((liftTwo D : D.N) : X) * g *
          (((liftTwo D : D.N) : X))⁻¹) := by
      calc b * (((liftTwo D : D.N) : X) * x * (((liftTwo D : D.N) : X))⁻¹)
          = (b * ((liftTwo D : D.N) : X) * x) * (((liftTwo D : D.N) : X))⁻¹ := by group
        _ = g * (((liftTwo D : D.N) : X))⁻¹ := by rw [← hg_eq]
        _ = (((liftTwo D : D.N) : X))⁻¹ * (((liftTwo D : D.N) : X) * g *
              (((liftTwo D : D.N) : X))⁻¹) := by group
    have hm2_eq : ((liftTwo D : D.N) : X) =
        (((liftTwo D : D.N) : X) * g * (((liftTwo D : D.N) : X))⁻¹) *
          ((((liftTwo D : D.N) : X) * x * (((liftTwo D : D.N) : X))⁻¹)⁻¹) * b⁻¹ := by
      have := congrArg (fun z => ((liftTwo D : D.N) : X) * z *
        ((((liftTwo D : D.N) : X) * x * (((liftTwo D : D.N) : X))⁻¹)⁻¹) * b⁻¹) hbx
      simpa [mul_assoc] using this
    exfalso
    refine (not_mem_Uminus_mul_B_liftTwo D) ⟨_, D.Vm.mul_mem hg₂ (D.Vm.inv_mem hx'),
      b⁻¹, D.B.inv_mem hb, hm2_eq.symm⟩

theorem conj_liftZero_X8 {D : RankTwoSystem X 8} {x : X} (hx : x ∈ D.root 8) :
    ((liftZero D : D.N) : X) * x * (((liftZero D : D.N) : X))⁻¹ ∈ D.root (-8) := by
  have hm : ((liftZero D : D.N) : D.Weyl) = altWord D.w₁ D.w₂ 8 := by
    simpa [RankTwoSystem.w₀] using liftZero_mk D
  have hact : D.ActsPos ((liftZero D : D.N) : X) (fun q => q - 8) := by
    simpa [tauA_eight] using D.actsPos_altWord₁ 8 (liftZero D) hm
  have hx7 : x ∈ D.root (Rt 8 7) := by
    rw [Rt_of_lt (by norm_num) (by norm_num)]
    simpa using hx
  have h1 := hact 7 x hx7
  change _ ∈ D.root (Rt 8 (7 - 8)) at h1
  have e : Rt 8 (7 - 8) = -8 := by
    rw [show (7 : ℤ) - 8 = -1 by ring, Rt_of_neg (by norm_num) (by norm_num)]
    norm_num
  rwa [e] at h1

theorem conj_liftZero_Xminus8 {D : RankTwoSystem X 8} {x : X} (hx : x ∈ D.root (-8)) :
    ((liftZero D : D.N) : X) * x * (((liftZero D : D.N) : X))⁻¹ ∈ D.root 8 := by
  have hm : ((liftZero D : D.N) : D.Weyl) = altWord D.w₁ D.w₂ 8 := by
    simpa [RankTwoSystem.w₀] using liftZero_mk D
  have hact : D.ActsPos ((liftZero D : D.N) : X) (fun q => q - 8) := by
    simpa [tauA_eight] using D.actsPos_altWord₁ 8 (liftZero D) hm
  have hx15 : x ∈ D.root (Rt 8 15) := by
    have e : Rt 8 15 = -8 := by
      rw [Rt_of_ge (by norm_num) (by norm_num)]
      norm_num
    rwa [e]
  have h1 := hact 15 x hx15
  change _ ∈ D.root (Rt 8 (15 - 8)) at h1
  have e : Rt 8 (15 - 8) = 8 := by
    rw [show (15 : ℤ) - 8 = 7 by ring, Rt_of_lt (by norm_num) (by norm_num)]
    norm_num
  rwa [e] at h1

theorem H_conj_X8 {D : RankTwoSystem X 8} {h : X} (hh : h ∈ D.B ⊓ D.N) {x : X}
    (hx : x ∈ D.root 8) : h * x * h⁻¹ ∈ D.root 8 :=
  D.roots.invariant 8 ⟨by norm_num, by norm_num⟩ h hh x hx

theorem conj_root8_Vtwo {D : RankTwoSystem X 8} {a : X} (ha : a ∈ D.root 8) {c : X}
    (hc : c ∈ Vtwo D) : a * c * a⁻¹ ∈ Vtwo D := by
  obtain ⟨W, hWc, -, -, hWn⟩ := D.roots.subgroup 1 7 (by norm_num) (by norm_num) (by norm_num)
  unfold Vtwo at hc
  have hconj := chainProd_conj_mem D.root W a (intList 1 7)
    (fun k hk y hy => ?_) c hc
  · rw [← SetLike.mem_coe, hWc] at hconj
    exact hconj
  · obtain ⟨hk1, hk2⟩ := mem_intList_iff.1 hk
    have hyW : y ∈ W := by
      rw [← SetLike.mem_coe, hWc]
      exact mem_chainProd_of_mem D.root (mem_intList_iff.2 ⟨hk1, hk2⟩) hy
    exact hWn (by norm_num) a ha y hyW

theorem lemmaB₂ (D : RankTwoSystem X 8) {y : X} (hy : y ∈ D.root (-8)) (hy1 : y ≠ 1) :
    ∃ v ∈ D.root 8, ∃ w ∈ D.root 8, ∃ m : D.N, (m : X) = v * y * w ∧ (m : D.Weyl) = D.w₂ := by
  have hyP : y ∈ D.P₂ := Xminus8_le_P2 D hy
  have hyVm : y ∈ D.Vm := D.root_le_V D.coe_Vm (by norm_num) (by norm_num) hy
  have hyB : y ∉ D.B := fun hb => hy1 (D.eq_one_of_mem_U_Vm hb hyVm)
  have hy_dc : y ∈ dc D.B D.N D.w₂ := by
    rcases (mem_parabolic_single_iff D.isTits (s := D.w₂) (by simp)).1 hyP with hB | hdc
    · exact absurd hB hyB
    · exact hdc
  obtain ⟨b, hb, x, hx, hy_eq⟩ := D.dc_panel_w₂ (liftTwo D) (liftTwo_mk D) hy_dc
  have hb' : b ∈ ((D.B ⊓ D.N : Subgroup X) : Set X) * (D.U : Set X) := by
    rw [← D.isSplit.2]
    exact hb
  obtain ⟨h, hh, u, hu, hb_eq⟩ := Set.mem_mul.1 hb'
  have hh' : h ∈ D.B ⊓ D.N := hh
  obtain ⟨c, hc, a, ha, hu_eq⟩ := D.U_decomp' (i := 1) (by norm_num) u hu
  have ha8 : a ∈ D.root 8 := by
    simpa [intList, chainProd] using ha
  have hcV : c ∈ Vtwo D := hc
  let c' : X := a⁻¹ * c * a
  have hc' : c' ∈ Vtwo D := by
    simpa [c'] using conj_root8_Vtwo (D := D) ((D.root 8).inv_mem ha8) hcV
  have hu_eq' : u = a * c' := by
    rw [hu_eq]
    dsimp [c']
    group
  have hx0 : h * a * h⁻¹ ∈ D.root 8 := H_conj_X8 (D := D) hh' ha8
  let mN : D.N := ⟨h, (Subgroup.mem_inf.1 hh').2⟩ * liftTwo D
  have hh1 : ((⟨h, (Subgroup.mem_inf.1 hh').2⟩ : D.N) : D.Weyl) = 1 :=
    (mk_eq_one_iff (B := D.B) (N := D.N)).2 (Subgroup.mem_inf.1 hh').1
  have hmN : (mN : D.Weyl) = D.w₂ := by
    dsimp [mN]
    rw [hh1, one_mul, liftTwo_mk]
  let v' : X := (((liftTwo D)⁻¹ : D.N) : X) * c' * ((((liftTwo D)⁻¹ : D.N) : X))⁻¹
  have hv' : v' ∈ Vtwo D := conj_liftTwo_inv_V (D := D) hc'
  have hy_decomp : y = (h * a * h⁻¹) * (mN : X) * v' * x := by
    rw [hy_eq, ← hb_eq, hu_eq']
    dsimp [mN, v']
    group
  have hweylN : (((liftZero D * mN⁻¹ * (liftZero D)⁻¹ : D.N) : D.Weyl)) = D.w₂ := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, liftZero_mk, hmN,
      liftZero_inv_mk D, inv_eq_of_mul_eq_one_right (D.rank2.dih.mul_self_b),
      w₀_comm_w₂, mul_assoc, w₀_mul_self, mul_one]
  have hNterm : ((liftZero D : D.N) : X) * (mN : X)⁻¹ * (((liftZero D : D.N) : X))⁻¹ ∈ D.P₂ := by
    have hmem : (((liftZero D * mN⁻¹ * (liftZero D)⁻¹ : D.N) : X)) ∈ dc D.B D.N D.w₂ := by
      have := coe_mem_dc (B := D.B) (N := D.N) (liftZero D * mN⁻¹ * (liftZero D)⁻¹)
      rwa [hweylN] at this
    have hX : ((liftZero D : D.N) : X) * (mN : X)⁻¹ * (((liftZero D : D.N) : X))⁻¹ ∈
        dc D.B D.N D.w₂ := by
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hmem
    exact (mem_parabolic_single_iff D.isTits (s := D.w₂) (by simp)).2 (Or.inr hX)
  have hx0term : ((liftZero D : D.N) : X) * (h * a * h⁻¹)⁻¹ *
      (((liftZero D : D.N) : X))⁻¹ ∈ D.P₂ :=
    Xminus8_le_P2 D (conj_liftZero_X8 (D := D) ((D.root 8).inv_mem hx0))
  have hyterm : ((liftZero D : D.N) : X) * y * (((liftZero D : D.N) : X))⁻¹ ∈ D.P₂ :=
    (mem_parabolic_single_iff D.isTits (s := D.w₂) (by simp)).2
      (Or.inl (D.root_le_B (by norm_num) (by norm_num)
        (conj_liftZero_Xminus8 (D := D) hy)))
  have hxterm : ((liftZero D : D.N) : X) * x⁻¹ * (((liftZero D : D.N) : X))⁻¹ ∈ D.P₂ :=
    Xminus8_le_P2 D (conj_liftZero_X8 (D := D) ((D.root 8).inv_mem hx))
  have hv'P : ((liftZero D : D.N) : X) * v' * (((liftZero D : D.N) : X))⁻¹ ∈ D.P₂ := by
    have hv'eq : v' = (mN : X)⁻¹ * (h * a * h⁻¹)⁻¹ * y * x⁻¹ := by
      rw [hy_decomp]
      dsimp [v']
      group
    have hfac : ((liftZero D : D.N) : X) * v' * (((liftZero D : D.N) : X))⁻¹ =
        (((liftZero D : D.N) : X) * (mN : X)⁻¹ * (((liftZero D : D.N) : X))⁻¹) *
        (((liftZero D : D.N) : X) * (h * a * h⁻¹)⁻¹ * (((liftZero D : D.N) : X))⁻¹) *
        (((liftZero D : D.N) : X) * y * (((liftZero D : D.N) : X))⁻¹) *
        (((liftZero D : D.N) : X) * x⁻¹ * (((liftZero D : D.N) : X))⁻¹) := by
      rw [hv'eq]
      group
    rw [hfac]
    exact D.P₂.mul_mem (D.P₂.mul_mem (D.P₂.mul_mem hNterm hx0term) hyterm) hxterm
  have hv'Vminus : ((liftZero D : D.N) : X) * v' * (((liftZero D : D.N) : X))⁻¹ ∈ VminusTwo D :=
    conj_liftZero_Vtwo (D := D) hv'
  have hzero : ((liftZero D : D.N) : X) * v' * (((liftZero D : D.N) : X))⁻¹ = 1 :=
    lemmaA₂ D hv'Vminus hv'P
  have hv'1 : v' = 1 := by
    have := congrArg (fun z => (((liftZero D : D.N) : X))⁻¹ * z *
      (((liftZero D : D.N) : X))) hzero
    simpa [mul_assoc] using this
  refine ⟨(h * a * h⁻¹)⁻¹, (D.root 8).inv_mem hx0, x⁻¹, (D.root 8).inv_mem hx, mN, ?_, hmN⟩
  rw [hy_decomp, hv'1]
  group

theorem moufang_nine (D : RankTwoSystem X 8) {y : X} (hy : y ∈ ofRankTwoU D 9) (hy1 : y ≠ 1) :
    ∃ v ∈ ofRankTwoU D 17, ∃ w ∈ ofRankTwoU D 17, ∀ j : ℤ,
      (ofRankTwoU D j).map (MulAut.conj (v * y * w)).toMonoidHom = ofRankTwoU D (26 - j) := by
  have e9 : ofRankTwoU D 9 = D.root (-1) := by
    unfold ofRankTwoU
    norm_num [Rt]
  have hy' : y ∈ D.root (-1) := by rwa [e9] at hy
  obtain ⟨v, hv, w, hw, m, hm_eq, hm_w⟩ := lemmaB D hy' hy1
  have e17 : ofRankTwoU D 17 = D.root 1 := by
    unfold ofRankTwoU
    norm_num [Rt]
  have hvU : v ∈ ofRankTwoU D 17 := by rwa [e17]
  have hwU : w ∈ ofRankTwoU D 17 := by rwa [e17]
  have hmoves : MovesU D ((m : D.N) : X) (fun j => 10 - j) := moves_of_liftOne D m hm_w
  have hmoves' : MovesU D (v * y * w) (fun j => 10 - j) := by
    rwa [hm_eq] at hmoves
  refine ⟨v, hvU, w, hwU, fun j => ?_⟩
  have h := hmoves' j
  rw [show (fun j : ℤ => 10 - j) j = (26 - j) + 16 * (-1) by ring,
    ofRankTwoU_add_mul] at h
  exact h

theorem moufang_sixteen (D : RankTwoSystem X 8) {y : X} (hy : y ∈ ofRankTwoU D 16)
    (hy1 : y ≠ 1) :
    ∃ v ∈ ofRankTwoU D 24, ∃ w ∈ ofRankTwoU D 24, ∀ j : ℤ,
      (ofRankTwoU D j).map (MulAut.conj (v * y * w)).toMonoidHom = ofRankTwoU D (40 - j) := by
  have e16 : ofRankTwoU D 16 = D.root (-8) := by
    unfold ofRankTwoU
    norm_num [Rt]
  have hy' : y ∈ D.root (-8) := by rwa [e16] at hy
  obtain ⟨v, hv, w, hw, m, hm_eq, hm_w⟩ := lemmaB₂ D hy' hy1
  have e24 : ofRankTwoU D 24 = D.root 8 := by
    unfold ofRankTwoU
    norm_num [Rt]
  have hvU : v ∈ ofRankTwoU D 24 := by rwa [e24]
  have hwU : w ∈ ofRankTwoU D 24 := by rwa [e24]
  have hmoves : MovesU D ((m : D.N) : X) (fun j => 8 - j) := moves_of_liftTwo D m hm_w
  have hmoves' : MovesU D (v * y * w) (fun j => 8 - j) := by
    rwa [hm_eq] at hmoves
  refine ⟨v, hvU, w, hwU, fun j => ?_⟩
  have h := hmoves' j
  rw [show (fun j : ℤ => 8 - j) j = (40 - j) + 16 * (-2) by ring,
    ofRankTwoU_add_mul] at h
  exact h

theorem moufang_ofRankTwo (D : RankTwoSystem X 8) :
    ∀ i : ℤ, ∀ u ∈ ofRankTwoU D i, u ≠ 1 → ∃ v ∈ ofRankTwoU D (i + 8),
      ∃ w ∈ ofRankTwoU D (i + 8), ∀ j : ℤ,
        (ofRankTwoU D j).map (MulAut.conj (v * u * w)).toMonoidHom =
          ofRankTwoU D (2 * i + 8 - j) := by
  intro i u hu hu1
  rcases Int.even_or_odd' i with ⟨k, hk | hk⟩
  ·
    let c : ℤ := 2 * (k - 8)
    have hc : i = 16 + c := by rw [hk]; dsimp [c]; ring
    obtain ⟨g, hg⟩ := exists_moves_shift D (k - 8)
    have hg' : MovesU D g⁻¹ (· - c) := by
      have := MovesU.inv_shift hg
      simpa [c] using this
    have hu' : g⁻¹ * u * g ∈ ofRankTwoU D 16 := by
      have h := MovesU.conj_mem hg' hu
      rw [show i - c = 16 by omega] at h
      simpa [inv_inv] using h
    have hu1' : g⁻¹ * u * g ≠ 1 := by
      intro h
      apply hu1
      calc u = g * (g⁻¹ * u * g) * g⁻¹ := by group
        _ = 1 := by rw [h]; group
    obtain ⟨v₀, hv₀, w₀, hw₀, hm₀⟩ := moufang_sixteen D hu' hu1'
    refine ⟨g * v₀ * g⁻¹, ?_, g * w₀ * g⁻¹, ?_, fun j => ?_⟩
    · have h := MovesU.conj_mem hg hv₀
      rwa [show 24 + c = i + 8 by omega] at h
    · have h := MovesU.conj_mem hg hw₀
      rwa [show 24 + c = i + 8 by omega] at h
    · have hu_eq : g * (g⁻¹ * u * g) * g⁻¹ = u := by group
      have hmoves := MovesU.mul (MovesU.mul hg hm₀) hg'
      have hfun : (fun j => (fun x => x + c) ((fun x => 40 - x) ((fun x => x - c) j))) =
          fun j => 2 * i + 8 - j := by
        funext j
        rw [hc]
        dsimp [c]
        ring
      change MovesU D (g * (v₀ * (g⁻¹ * u * g) * w₀) * g⁻¹)
        (fun j => (fun x => x + c) ((fun x => 40 - x) ((fun x => x - c) j))) at hmoves
      rw [hfun] at hmoves
      have heq : g * (v₀ * (g⁻¹ * u * g) * w₀) * g⁻¹ =
          (g * v₀ * g⁻¹) * u * (g * w₀ * g⁻¹) := by
        rw [← hu_eq]
        group
      rw [heq] at hmoves
      exact hmoves j
  ·
    let c : ℤ := 2 * (k - 4)
    have hc : i = 9 + c := by rw [hk]; dsimp [c]; ring
    obtain ⟨g, hg⟩ := exists_moves_shift D (k - 4)
    have hg' : MovesU D g⁻¹ (· - c) := by
      have := MovesU.inv_shift hg
      simpa [c] using this
    have hu' : g⁻¹ * u * g ∈ ofRankTwoU D 9 := by
      have h := MovesU.conj_mem hg' hu
      rw [show i - c = 9 by omega] at h
      simpa [inv_inv] using h
    have hu1' : g⁻¹ * u * g ≠ 1 := by
      intro h
      apply hu1
      calc u = g * (g⁻¹ * u * g) * g⁻¹ := by group
        _ = 1 := by rw [h]; group
    obtain ⟨v₀, hv₀, w₀, hw₀, hm₀⟩ := moufang_nine D hu' hu1'
    refine ⟨g * v₀ * g⁻¹, ?_, g * w₀ * g⁻¹, ?_, fun j => ?_⟩
    · have h := MovesU.conj_mem hg hv₀
      rwa [show 17 + c = i + 8 by omega] at h
    · have h := MovesU.conj_mem hg hw₀
      rwa [show 17 + c = i + 8 by omega] at h
    · have hu_eq : g * (g⁻¹ * u * g) * g⁻¹ = u := by group
      have hmoves := MovesU.mul (MovesU.mul hg hm₀) hg'
      have hfun : (fun j => (fun x => x + c) ((fun x => 26 - x) ((fun x => x - c) j))) =
          fun j => 2 * i + 8 - j := by
        funext j
        rw [hc]
        dsimp [c]
        ring
      change MovesU D (g * (v₀ * (g⁻¹ * u * g) * w₀) * g⁻¹)
        (fun j => (fun x => x + c) ((fun x => 26 - x) ((fun x => x - c) j))) at hmoves
      rw [hfun] at hmoves
      have heq : g * (v₀ * (g⁻¹ * u * g) * w₀) * g⁻¹ =
          (g * v₀ * g⁻¹) * u * (g * w₀ * g⁻¹) := by
        rw [← hu_eq]
        group
      rw [heq] at hmoves
      exact hmoves j

end CFSG.GH74.Tits83

end
