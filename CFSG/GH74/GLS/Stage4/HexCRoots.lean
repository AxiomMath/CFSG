module

public import CFSG.GH74.GLS.Stage4.HexWeights
public import CFSG.GH74.GLS.Stage4.HexCScalar

public noncomputable section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

variable {G : Type} [Group G] {H : Subgroup G} {r₁ r₂ : G} {U : Subgroup G}
  {root : ℤ → Subgroup G}

theorem prod_single_six {x : G} {a : ℤ} (h1 : 1 ≤ a) (h6 : a ≤ 6) :
    ((intList 1 ((6 : ℕ) : ℤ)).map fun k => if k = a then x else (1 : G)).prod = x := by
  have hl : intList 1 ((6 : ℕ) : ℤ) = [1, 2, 3, 4, 5, 6] := by decide
  rw [hl]
  interval_cases a <;> simp

theorem pos_inter_six (R : RGD2 6 H r₁ r₂ U root) {a b : ℤ} (ha1 : 1 ≤ a) (ha6 : a ≤ 6)
    (hb1 : 1 ≤ b) (hb6 : b ≤ 6) {x : G} (hxa : x ∈ root a) (hxb : x ∈ root b) (hx : x ≠ 1) :
    a = b := by
  by_contra hne
  apply hx
  have key := R.unique (fun k => if k = a then x else 1) (fun k => if k = b then x else 1)
    (fun k hk => by
      have := mem_intList_iff.1 hk
      by_cases hka : k = a
      · subst hka; simpa using hxa
      · simp [hka])
    (fun k hk => by
      have := mem_intList_iff.1 hk
      by_cases hkb : k = b
      · subst hkb; simpa using hxb
      · simp [hkb])
    (by rw [prod_single_six ha1 ha6, prod_single_six hb1 hb6]) a
    (mem_intList_iff.2 ⟨ha1, by exact_mod_cast ha6⟩)
  simpa [hne] using key

theorem pos_neg_inter_six (R : RGD2 6 H r₁ r₂ U root) {a b : ℤ} (ha1 : 1 ≤ a) (ha6 : a ≤ 6)
    (hb1 : 1 ≤ b) (hb6 : b ≤ 6) {x : G} (hxa : x ∈ root a) (hxb : x ∈ root (-b)) : x = 1 :=
  R.meet_one x (Subgroup.mem_sup_right (RGD2.root_le_U R ha1 (by exact_mod_cast ha6) hxa))
    (mem_negGen_of_mem hb1 (by exact_mod_cast hb6) hxb)

theorem Rt6_eq_pos {q b : ℤ} (hb1 : 1 ≤ b) (hb6 : b ≤ 6) : Rt 6 q = b ↔ q % 12 = b - 1 := by
  unfold Rt
  simp only [Nat.cast_ofNat]
  constructor <;> intro h <;> split_ifs at * <;> omega

theorem Rt6_eq_neg {q b : ℤ} (hb1 : 1 ≤ b) (hb6 : b ≤ 6) : Rt 6 q = -b ↔ q % 12 = b + 5 := by
  unfold Rt
  simp only [Nat.cast_ofNat]
  constructor <;> intro h <;> split_ifs at * <;> omega

theorem exists_antipodal (R : RGD2 6 H r₁ r₂ U root) :
    ∃ w : G, ∀ a : ℤ, IsRoot 6 a → ∀ x ∈ root a, w * x * w⁻¹ ∈ root (-a) := by
  refine ⟨r₁ * (r₂ * (r₁ * (r₂ * (r₁ * r₂)))), fun a ha x hx => ?_⟩
  have h12 := (R.actsPos_r₁).mul ((R.actsPos_r₂).mul ((R.actsPos_r₁).mul
    ((R.actsPos_r₂).mul ((R.actsPos_r₁).mul R.actsPos_r₂))))
  obtain ⟨q, hq⟩ : ∃ q : ℤ, Rt 6 q = a := by
    rcases lt_or_gt_of_ne ha.1 with hneg | hpos
    · refine ⟨-a + 5, ?_⟩
      have := ha.2
      rw [Rt_of_ge (by omega) (by omega)]
      ring
    · refine ⟨a - 1, ?_⟩
      have := ha.2
      rw [Rt_of_lt (by omega) (by omega)]
      ring
  have h := h12 q x (hq ▸ hx)
  have e : ((6 : ℕ) : ℤ) - (((6 : ℕ) : ℤ) - 2 - (((6 : ℕ) : ℤ) - (((6 : ℕ) : ℤ) - 2 -
      (((6 : ℕ) : ℤ) - (((6 : ℕ) : ℤ) - 2 - q))))) = q + ((6 : ℕ) : ℤ) := by ring
  simp only [e] at h
  rw [Rt_add_n (by norm_num : 0 < 6), hq] at h
  exact h

theorem root_inter_six (R : RGD2 6 H r₁ r₂ U root) {a b : ℤ} (ha : IsRoot 6 a) (hb : IsRoot 6 b)
    {x : G} (hxa : x ∈ root a) (hxb : x ∈ root b) (hx : x ≠ 1) : a = b := by
  obtain ⟨w, hw⟩ := exists_antipodal R
  have ha' := ha.2
  have hb' := hb.2
  rcases lt_or_gt_of_ne ha.1 with han | hap <;> rcases lt_or_gt_of_ne hb.1 with hbn | hbp
  · have h1 := hw a ha x hxa
    have h2 := hw b hb x hxb
    have hne : w * x * w⁻¹ ≠ 1 := by
      intro h; apply hx
      have := congrArg (fun y => w⁻¹ * y * w) h
      simpa [mul_assoc] using this
    have := pos_inter_six R (by omega) (by omega) (by omega) (by omega) h1 h2 hne
    omega
  · exfalso; apply hx
    exact pos_neg_inter_six R (a := b) (b := -a) (by omega) (by omega) (by omega) (by omega) hxb
      (by simpa using hxa)
  · exfalso; apply hx
    exact pos_neg_inter_six R (a := a) (b := -b) (by omega) (by omega) (by omega) (by omega) hxa
      (by simpa using hxb)
  · exact pos_inter_six R (by omega) (by omega) (by omega) (by omega) hxa hxb hx

theorem actsPos_eq_of_conj (R : RGD2 6 H r₁ r₂ U root) {m : G} {f : ℤ → ℤ}
    (hf : ActsPos 6 root m f) {q b : ℤ} (hb : IsRoot 6 b) {x : G} (hx : x ∈ root (Rt 6 q))
    (hx1 : x ≠ 1) (hxb : m * x * m⁻¹ ∈ root b) : Rt 6 (f q) = b := by
  have h1 := hf q x hx
  have hne : m * x * m⁻¹ ≠ 1 := by
    intro h; apply hx1
    have := congrArg (fun y => m⁻¹ * y * m) h
    simpa [mul_assoc] using this
  exact root_inter_six R (Rt_isRoot (by norm_num) _) hb h1 hxb hne

structure SL2Pos (H N : Subgroup G) (root : ℤ → Subgroup G) (i : ℤ) extends RankOneAt H root i where
  hW : toRankOneAt.φ (sl2W toRankOneAt.F) ∈ N

theorem sl2Pos_of_sl2At {N : Subgroup G} {i : ℤ} (h : SL2At H N root i) :
    Nonempty (SL2Pos H N root i) := by
  obtain ⟨F, _, _, -, φ, hφ, hU, hL, hD, hW⟩ := h
  exact ⟨{ F := F, φ := φ, inj := hφ, hU := hU, hL := hL, hD := hD, hW := hW }⟩

@[expose] noncomputable def SL2Pos.conj {N : Subgroup G} {i j : ℤ} (E : SL2Pos H N root i) (m : G)
    (hmN : m ∈ N) (hm : ∀ h ∈ H, m * h * m⁻¹ ∈ H) (hU : ∀ x, x ∈ root i ↔ m * x * m⁻¹ ∈ root j)
    (hL : ∀ x, x ∈ root (-i) ↔ m * x * m⁻¹ ∈ root (-j)) : SL2Pos H N root j where
  F := E.F
  field := E.field
  finite := E.finite
  φ := (MulAut.conj m).toMonoidHom.comp E.φ
  inj := (MulAut.conj m).injective.comp E.inj
  hU x := by
    constructor
    · intro hx
      have h1 : m⁻¹ * x * m⁻¹⁻¹ ∈ root i := by
        rw [hU]
        simpa [mul_assoc] using hx
      obtain ⟨c, hc⟩ := (E.hU _).1 h1
      refine ⟨c, ?_⟩
      show m * E.φ (sl2U c) * m⁻¹ = x
      rw [hc]
      group
    · rintro ⟨c, rfl⟩
      exact (hU _).1 ((E.hU _).2 ⟨c, rfl⟩)
  hL x := by
    constructor
    · intro hx
      have h1 : m⁻¹ * x * m⁻¹⁻¹ ∈ root (-i) := by
        rw [hL]
        simpa [mul_assoc] using hx
      obtain ⟨c, hc⟩ := (E.hL _).1 h1
      refine ⟨c, ?_⟩
      show m * E.φ (sl2L c) * m⁻¹ = x
      rw [hc]
      group
    · rintro ⟨c, rfl⟩
      exact (hL _).1 ((E.hL _).2 ⟨c, rfl⟩)
  hD t := hm _ (E.hD t)
  hW := N.mul_mem (N.mul_mem hmN E.hW) (N.inv_mem hmN)

theorem sl2Pos_U_mem {N : Subgroup G} {i : ℤ} (E : SL2Pos H N root i) (c : E.F) :
    E.φ (sl2U c) ∈ root i := (E.hU _).2 ⟨c, rfl⟩

theorem sl2Pos_L_mem {N : Subgroup G} {i : ℤ} (E : SL2Pos H N root i) (c : E.F) :
    E.φ (sl2L c) ∈ root (-i) := (E.hL _).2 ⟨c, rfl⟩

theorem sl2Pos_U_ne_one {N : Subgroup G} {i : ℤ} (E : SL2Pos H N root i) :
    E.φ (sl2U (1 : E.F)) ≠ 1 := by
  intro h
  have h1 : E.φ (sl2U (1 : E.F)) = E.φ (sl2U 0) := by rw [h, sl2U_zero, map_one]
  exact one_ne_zero (sl2U_injective (E.inj h1))

theorem actsPos_weylFour (R : RGD2 6 H r₁ r₂ U root) (E : SL2Pos H R.N root 4)
    (hO : ∀ a ∈ root 1 ⊔ root (-1), ∀ b ∈ root 4 ⊔ root (-4), a * b = b * a) :
    ActsPos 6 root (E.φ (sl2W E.F)) (fun q => -q) := by
  classical
  set n := E.φ (sl2W E.F) with hn_def
  have hn : n ∈ R.N := E.hW
  obtain ⟨f, g, hf, hg, hactf, hactg⟩ := R.goodAct_of_mem_N hn
  have hn4 : n ∈ root 4 ⊔ root (-4) := by
    rw [hn_def, sl2W_eq_sl2Wc]
    simp only [sl2Wc, map_mul]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left (sl2Pos_U_mem E _))
      (Subgroup.mem_sup_right (sl2Pos_L_mem E _))) (Subgroup.mem_sup_left (sl2Pos_U_mem E _))
  obtain ⟨x, hx, hx1⟩ : ∃ x ∈ root 1, x ≠ 1 := by
    have h := R.ne_bot 1 (isRoot_of_pos_le (by norm_num) (by norm_num))
    obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h
    exact ⟨x, hx, fun h' => hx1 (Subtype.ext h')⟩
  have hxfix : n * x * n⁻¹ = x := by
    have := hO x (Subgroup.mem_sup_left hx) n hn4
    rw [mul_inv_eq_iff_eq_mul]; exact this.symm
  have hy : E.φ (sl2U (1 : E.F)) ∈ root 4 := sl2Pos_U_mem E 1
  have hyn : n * E.φ (sl2U (1 : E.F)) * n⁻¹ = E.φ (sl2L (-1)) := by
    rw [mul_inv_eq_iff_eq_mul, hn_def, ← map_mul, ← map_mul, sl2W_mul_sl2U]
  have hyn' : n * E.φ (sl2U (1 : E.F)) * n⁻¹ ∈ root (-4) := hyn ▸ sl2Pos_L_mem E (-1)
  have hRt0 : Rt 6 0 = 1 := (Rt6_eq_pos (q := 0) (by norm_num) (by norm_num)).2 (by norm_num)
  have hRt3 : Rt 6 3 = 4 := (Rt6_eq_pos (q := 3) (by norm_num) (by norm_num)).2 (by norm_num)
  have hx' : x ∈ root (Rt 6 0) := by rw [hRt0]; exact hx
  have hxn : n * x * n⁻¹ ∈ root 1 := by rw [hxfix]; exact hx
  have hy' : E.φ (sl2U (1 : E.F)) ∈ root (Rt 6 3) := by rw [hRt3]; exact hy
  have h0 := actsPos_eq_of_conj R hactf (q := 0) (b := 1) ⟨by norm_num, by norm_num⟩
    hx' hx1 hxn
  have h3 := actsPos_eq_of_conj R hactf (q := 3) (b := -4) ⟨by norm_num, by norm_num⟩
    hy' (sl2Pos_U_ne_one E) hyn'
  rw [Rt6_eq_pos (by norm_num) (by norm_num)] at h0
  rw [Rt6_eq_neg (by norm_num) (by norm_num)] at h3
  rcases hf with ⟨c, hc⟩ | ⟨c, hc⟩
  · exfalso
    rw [hc] at h0 h3
    omega
  · have hq : ∀ q, Rt 6 (f q) = Rt 6 (-q) := fun q => by
      apply Rt_congr
      rw [hc q]
      rw [hc 0] at h0
      simp only [Nat.cast_ofNat]
      omega
    intro q z hz
    have := hactf q z hz
    rwa [hq q] at this

theorem actsPos_conj_r12 (R : RGD2 6 H r₁ r₂ U root) {n : G}
    (hn : ActsPos 6 root n (fun q => -q)) :
    ActsPos 6 root ((r₁ * r₂) * n * (r₁ * r₂)⁻¹) (fun q => 4 - q) := by
  have h1 := R.actsPos_r₁
  have h2 := R.actsPos_r₂
  have h1i := R.actsPos_inv_of_sq R.sq₁ h1
  have h2i := R.actsPos_inv_of_sq R.sq₂ h2
  have hm := h1.mul h2
  have hmi := h2i.mul h1i
  have h := (hm.mul hn).mul hmi
  rw [← mul_inv_rev] at h
  intro q x hx
  have := h q x hx
  have e : ((6 : ℕ) : ℤ) - (((6 : ℕ) : ℤ) - 2 - (-(((6 : ℕ) : ℤ) - 2 - (((6 : ℕ) : ℤ) - q)))) =
      4 - q := by push_cast; ring
  simp only [e] at this
  exact this

theorem r12_conj_H (R : RGD2 6 H r₁ r₂ U root) : ∀ h ∈ H, (r₁ * r₂) * h * (r₁ * r₂)⁻¹ ∈ H := by
  intro h hh
  have := R.conj_H₁ _ (R.conj_H₂ h hh)
  have e : (r₁ * r₂) * h * (r₁ * r₂)⁻¹ = r₁ * (r₂ * h * r₂⁻¹) * r₁⁻¹ := by group
  rw [e]; exact this

theorem mem_iff_r12 (R : RGD2 6 H r₁ r₂ U root) (x : G) :
    x ∈ root 4 ↔ (r₁ * r₂) * x * (r₁ * r₂)⁻¹ ∈ root 6 := by
  have h2 := RGD2.mem_iff_r₂ R (i := 4) (by norm_num) (by norm_num) x
  have h1 := RGD2.mem_iff_r₁ R (i := 2) (by norm_num) (by norm_num) (r₂ * x * r₂⁻¹)
  norm_num at h2 h1
  have e : r₁ * (r₂ * x * r₂⁻¹) * r₁⁻¹ = (r₁ * r₂) * x * (r₁ * r₂)⁻¹ := by group
  rw [e] at h1
  exact h2.trans h1

theorem mem_iff_r12_neg (R : RGD2 6 H r₁ r₂ U root) (x : G) :
    x ∈ root (-4) ↔ (r₁ * r₂) * x * (r₁ * r₂)⁻¹ ∈ root (-6) := by
  have h2 := RGD2.mem_iff_r₂_neg R (i := 4) (by norm_num) (by norm_num) x
  have h1 := RGD2.mem_iff_r₁_neg R (i := 2) (by norm_num) (by norm_num) (r₂ * x * r₂⁻¹)
  norm_num at h2 h1
  have e : r₁ * (r₂ * x * r₂⁻¹) * r₁⁻¹ = (r₁ * r₂) * x * (r₁ * r₂)⁻¹ := by group
  rw [e] at h1
  exact h2.trans h1

theorem natPair_long (R : RGD2 6 H r₁ r₂ U root) (E : SL2Pos H R.N root 4)
    (hO : ∀ a ∈ root 1 ⊔ root (-1), ∀ b ∈ root 4 ⊔ root (-4), a * b = b * a)
    (hc24 : ∀ x ∈ root 2, ∀ y ∈ root 4, x * y = y * x)
    (hc46 : ∀ x ∈ root 4, ∀ y ∈ root 6, x * y = y * x)
    (hc26 : ∀ x ∈ root 2, ∀ y ∈ root 6, ⁅x, y⁆ ∈ root 4)
    (hab4 : ∀ x ∈ root 4, ∀ y ∈ root 4, x * y = y * x)
    (hab2 : ∀ x ∈ root 2, ∀ y ∈ root 2, x * y = y * x) :
    NatPair ((MulAut.conj (r₁ * r₂)).toMonoidHom.comp E.φ) (root 4) (root 2) := by
  classical
  set m := r₁ * r₂ with hm
  set φ₆ : SL2 E.F →* G := (MulAut.conj m).toMonoidHom.comp E.φ with hφ₆
  have hφ₆_apply : ∀ g, φ₆ g = m * E.φ g * m⁻¹ := fun g => by
    show (MulAut.conj m) (E.φ g) = _
    rw [MulAut.conj_apply]
  have hU6 : ∀ c, φ₆ (sl2U c) ∈ root 6 := fun c => by
    rw [hφ₆_apply]; exact (mem_iff_r12 R _).1 (sl2Pos_U_mem E c)
  have hL6 : ∀ c, φ₆ (sl2L c) ∈ root (-6) := fun c => by
    rw [hφ₆_apply]; exact (mem_iff_r12_neg R _).1 (sl2Pos_L_mem E c)
  have hn4 := actsPos_weylFour R E hO
  have hn6 : ActsPos 6 root (φ₆ (sl2W E.F)) (fun q => 4 - q) := by
    rw [hφ₆_apply]; exact actsPos_conj_r12 R hn4
  have h62 : conjBy r₂⁻¹ (root (-6)) = root 6 := by simpa using R.act₂.2.1
  have hr2neg : ∀ z ∈ root (-6), r₂ * z * r₂⁻¹ ∈ root 6 := fun z hz =>
    (mem_iff_conj_of_conjBy h62 z).1 hz
  have h22 : ∀ b ∈ root 2, r₂ * b * r₂⁻¹ ∈ root 4 := fun b hb => by
    have := (RGD2.mem_iff_r₂ R (i := 2) (by norm_num) (by norm_num) b).1 hb
    norm_num at this; exact this
  have h24 : ∀ a ∈ root 4, r₂ * a * r₂⁻¹ ∈ root 2 := fun a ha => by
    have := (RGD2.mem_iff_r₂ R (i := 4) (by norm_num) (by norm_num) a).1 ha
    norm_num at this; exact this
  have h22' : ∀ w : G, r₂ * w * r₂⁻¹ ∈ root 4 → w ∈ root 2 := fun w hw => by
    have := (RGD2.mem_iff_r₂ R (i := 2) (by norm_num) (by norm_num) w).2
    norm_num at this; exact this hw
  have hlB : ∀ (c : E.F), ∀ b ∈ root 2, φ₆ (sl2L c) * b * (φ₆ (sl2L c))⁻¹ = b := by
    intro c b hb
    have hz' := hr2neg _ (hL6 c)
    have hb' := h22 b hb
    have hcomm := hc46 _ hb' _ hz'
    have h : r₂ * (φ₆ (sl2L c) * b * (φ₆ (sl2L c))⁻¹) * r₂⁻¹ = r₂ * b * r₂⁻¹ := by
      calc r₂ * (φ₆ (sl2L c) * b * (φ₆ (sl2L c))⁻¹) * r₂⁻¹
          = (r₂ * φ₆ (sl2L c) * r₂⁻¹) * (r₂ * b * r₂⁻¹) * (r₂ * φ₆ (sl2L c) * r₂⁻¹)⁻¹ := by group
        _ = r₂ * b * r₂⁻¹ := by rw [← hcomm]; group
    have := congrArg (fun y => r₂⁻¹ * y * r₂) h
    simpa [mul_assoc] using this
  have huA : ∀ (c : E.F), ∀ a ∈ root 4, φ₆ (sl2U c) * a * (φ₆ (sl2U c))⁻¹ = a := by
    intro c a ha
    have := hc46 a ha _ (hU6 c)
    calc φ₆ (sl2U c) * a * (φ₆ (sl2U c))⁻¹ = (a * φ₆ (sl2U c)) * (φ₆ (sl2U c))⁻¹ := by
          rw [← this]
      _ = a := by group
  have hW6 : φ₆ (sl2W E.F) = φ₆ (sl2U 1) * φ₆ (sl2L (-1)) * φ₆ (sl2U 1) := by
    rw [sl2W_eq_sl2Wc]
    simp only [sl2Wc, map_mul, inv_one]
  refine
    { commA := hab4
      commB := hab2
      commAB := fun a ha b hb => (hc24 b hb a ha).symm
      uA := huA
      lB := hlB
      uB := ?_
      lA := ?_
      ndU := ?_
      ndL := ?_ }
  · intro c b hb
    have h := hc26 b hb _ (hU6 c)
    have e : φ₆ (sl2U c) * b * (φ₆ (sl2U c))⁻¹ * b⁻¹ = (⁅b, φ₆ (sl2U c)⁆)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]; exact (root 4).inv_mem h
  · intro c a ha
    have hz' := hr2neg _ (hL6 c)
    have ha' := h24 a ha
    have h := hc26 _ ha' _ hz'
    have e : r₂ * (φ₆ (sl2L c) * a * (φ₆ (sl2L c))⁻¹ * a⁻¹) * r₂⁻¹ =
        (⁅r₂ * a * r₂⁻¹, r₂ * φ₆ (sl2L c) * r₂⁻¹⁆)⁻¹ := by
      simp only [commutatorElement_def]; group
    exact h22' _ (by rw [e]; exact (root 4).inv_mem h)
  · intro b hb hfix
    by_contra hb1
    have hbu : b * φ₆ (sl2U 1) = φ₆ (sl2U 1) * b := by
      have := congrArg (fun y => y * φ₆ (sl2U 1)) hfix
      simpa [mul_assoc] using this.symm
    have hbz : b * φ₆ (sl2L (-1)) = φ₆ (sl2L (-1)) * b := by
      have := hlB (-1) b hb
      have h2 := congrArg (fun y => y * φ₆ (sl2L (-1))) this
      simpa [mul_assoc] using h2.symm
    have hfixn : φ₆ (sl2W E.F) * b * (φ₆ (sl2W E.F))⁻¹ = b := by
      rw [mul_inv_eq_iff_eq_mul, hW6]
      calc φ₆ (sl2U 1) * φ₆ (sl2L (-1)) * φ₆ (sl2U 1) * b
          = φ₆ (sl2U 1) * φ₆ (sl2L (-1)) * (φ₆ (sl2U 1) * b) := by group
        _ = φ₆ (sl2U 1) * φ₆ (sl2L (-1)) * (b * φ₆ (sl2U 1)) := by rw [hbu]
        _ = φ₆ (sl2U 1) * (φ₆ (sl2L (-1)) * b) * φ₆ (sl2U 1) := by group
        _ = φ₆ (sl2U 1) * (b * φ₆ (sl2L (-1))) * φ₆ (sl2U 1) := by rw [hbz]
        _ = (φ₆ (sl2U 1) * b) * φ₆ (sl2L (-1)) * φ₆ (sl2U 1) := by group
        _ = (b * φ₆ (sl2U 1)) * φ₆ (sl2L (-1)) * φ₆ (sl2U 1) := by rw [hbu]
        _ = b * (φ₆ (sl2U 1) * φ₆ (sl2L (-1)) * φ₆ (sl2U 1)) := by group
    have hRt1 : Rt 6 1 = 2 := (Rt6_eq_pos (q := 1) (by norm_num) (by norm_num)).2 (by norm_num)
    have hb' : b ∈ root (Rt 6 1) := by rw [hRt1]; exact hb
    have hbn : φ₆ (sl2W E.F) * b * (φ₆ (sl2W E.F))⁻¹ ∈ root 2 := by rw [hfixn]; exact hb
    have := actsPos_eq_of_conj R hn6 (q := 1) (b := 2) ⟨by norm_num, by norm_num⟩ hb' hb1 hbn
    rw [Rt6_eq_pos (by norm_num) (by norm_num)] at this
    omega
  · intro a ha hfix
    by_contra ha1
    have hau : a * φ₆ (sl2U 1) = φ₆ (sl2U 1) * a := hc46 a ha _ (hU6 1)
    have haz : a * φ₆ (sl2L (-1)) = φ₆ (sl2L (-1)) * a := by
      have h1 : φ₆ (sl2L (-1)) = (φ₆ (sl2L 1))⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← map_mul, ← sl2L_add]; simp [sl2L_zero]
      have h2 : a * φ₆ (sl2L 1) = φ₆ (sl2L 1) * a := by
        have := congrArg (fun y => y * φ₆ (sl2L 1)) hfix
        simpa [mul_assoc] using this.symm
      rw [h1]
      have := congrArg (fun y => (φ₆ (sl2L 1))⁻¹ * y * (φ₆ (sl2L 1))⁻¹) h2
      simpa [mul_assoc] using this.symm
    have hfixn : φ₆ (sl2W E.F) * a * (φ₆ (sl2W E.F))⁻¹ = a := by
      rw [mul_inv_eq_iff_eq_mul, hW6]
      calc φ₆ (sl2U 1) * φ₆ (sl2L (-1)) * φ₆ (sl2U 1) * a
          = φ₆ (sl2U 1) * φ₆ (sl2L (-1)) * (φ₆ (sl2U 1) * a) := by group
        _ = φ₆ (sl2U 1) * φ₆ (sl2L (-1)) * (a * φ₆ (sl2U 1)) := by rw [hau]
        _ = φ₆ (sl2U 1) * (φ₆ (sl2L (-1)) * a) * φ₆ (sl2U 1) := by group
        _ = φ₆ (sl2U 1) * (a * φ₆ (sl2L (-1))) * φ₆ (sl2U 1) := by rw [haz]
        _ = (φ₆ (sl2U 1) * a) * φ₆ (sl2L (-1)) * φ₆ (sl2U 1) := by group
        _ = (a * φ₆ (sl2U 1)) * φ₆ (sl2L (-1)) * φ₆ (sl2U 1) := by rw [hau]
        _ = a * (φ₆ (sl2U 1) * φ₆ (sl2L (-1)) * φ₆ (sl2U 1)) := by group
    have hRt3 : Rt 6 3 = 4 := (Rt6_eq_pos (q := 3) (by norm_num) (by norm_num)).2 (by norm_num)
    have ha' : a ∈ root (Rt 6 3) := by rw [hRt3]; exact ha
    have han : φ₆ (sl2W E.F) * a * (φ₆ (sl2W E.F))⁻¹ ∈ root 4 := by rw [hfixn]; exact ha
    have := actsPos_eq_of_conj R hn6 (q := 3) (b := 4) ⟨by norm_num, by norm_num⟩ ha' ha1 han
    rw [Rt6_eq_pos (by norm_num) (by norm_num)] at this
    omega

@[expose] noncomputable def phi6 {F : Type*} [Field F] (r₁ r₂ : G) (φ : SL2 F →* G) : SL2 F →* G :=
  (MulAut.conj (r₁ * r₂)).toMonoidHom.comp φ

theorem phi6_apply {F : Type*} [Field F] (r₁ r₂ : G) (φ : SL2 F →* G) (g : SL2 F) :
    phi6 r₁ r₂ φ g = (r₁ * r₂) * φ g * (r₁ * r₂)⁻¹ := by
  show (MulAut.conj (r₁ * r₂)) (φ g) = _
  rw [MulAut.conj_apply]

theorem two_ne_zero_of_odd_card {F : Type*} [Field F] [Finite F] (h : Odd (Nat.card F)) :
    (2 : F) ≠ 0 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  apply Ring.two_ne_zero
  intro h2
  have := (FiniteField.even_card_iff_char_two (F := F)).1 h2
  rw [Nat.card_eq_fintype_card] at h
  obtain ⟨k, hk⟩ := h
  omega

theorem long_coords (R : RGD2 6 H r₁ r₂ U root) (E : SL2Pos H R.N root 4)
    (hodd : Odd (Nat.card E.F))
    (hO : ∀ a ∈ root 1 ⊔ root (-1), ∀ b ∈ root 4 ⊔ root (-4), a * b = b * a)
    (hc24 : ∀ x ∈ root 2, ∀ y ∈ root 4, x * y = y * x)
    (hc46 : ∀ x ∈ root 4, ∀ y ∈ root 6, x * y = y * x)
    (hc26 : ∀ x ∈ root 2, ∀ y ∈ root 6, ⁅x, y⁆ ∈ root 4)
    (hab4 : ∀ x ∈ root 4, ∀ y ∈ root 4, x * y = y * x)
    (hab2 : ∀ x ∈ root 2, ∀ y ∈ root 2, x * y = y * x) :
    ∃ x₂ x₄ : E.F → G, (∀ c d, x₂ (c + d) = x₂ c * x₂ d) ∧ Function.Injective x₂ ∧
      (∀ d, x₂ d ∈ root 2) ∧ (∀ b ∈ root 2, ∃ d, x₂ d = b) ∧
      (∀ c d, x₄ (c + d) = x₄ c * x₄ d) ∧ Function.Injective x₄ ∧
      (∀ d, x₄ d ∈ root 4) ∧ (∀ b ∈ root 4, ∃ d, x₄ d = b) ∧
      (∀ c d, ⁅phi6 r₁ r₂ E.φ (sl2U c), x₂ d⁆ = x₄ (c * d)) ∧
      (∀ (t : E.Fˣ) d, phi6 r₁ r₂ E.φ (sl2D t) * x₂ d * (phi6 r₁ r₂ E.φ (sl2D t))⁻¹ =
        x₂ ((t : E.F)⁻¹ * d)) ∧
      (∀ (t : E.Fˣ) d, phi6 r₁ r₂ E.φ (sl2D t) * x₄ d * (phi6 r₁ r₂ E.φ (sl2D t))⁻¹ =
        x₄ ((t : E.F) * d)) := by
  classical
  have hnp := natPair_long R E hO hc24 hc46 hc26 hab4 hab2
  have hr₂N : r₂ ∈ R.N := Subgroup.subset_closure (Or.inr (Or.inr rfl))
  have hU2 : ∀ x, x ∈ root 4 ↔ r₂ * x * r₂⁻¹ ∈ root 2 := fun x => by
    have := RGD2.mem_iff_r₂ R (i := 4) (by norm_num) (by norm_num) x
    norm_num at this; exact this
  have hL2 : ∀ x, x ∈ root (-4) ↔ r₂ * x * r₂⁻¹ ∈ root (-2) := fun x => by
    have := RGD2.mem_iff_r₂_neg R (i := 4) (by norm_num) (by norm_num) x
    norm_num at this; exact this
  set φ₂ : SL2 E.F →* G := (MulAut.conj r₂).toMonoidHom.comp E.φ with hφ₂
  have hφ₂U : ∀ x, x ∈ root 2 ↔ ∃ c : E.F, φ₂ (sl2U c) = x :=
    (E.conj r₂ hr₂N R.conj_H₂ hU2 hL2).hU
  have hφ₂L : ∀ x, x ∈ root (-2) ↔ ∃ c : E.F, φ₂ (sl2L c) = x :=
    (E.conj r₂ hr₂N R.conj_H₂ hU2 hL2).hL
  have hφ₂D : ∀ t : E.Fˣ, φ₂ (sl2D t) ∈ H := fun t => R.conj_H₂ _ (E.hD t)
  have hφ₂inj : Function.Injective φ₂ := (MulAut.conj r₂).injective.comp E.inj
  have hF2 : (2 : E.F) ≠ 0 := two_ne_zero_of_odd_card hodd
  have hD6 : ∀ t : E.Fˣ, phi6 r₁ r₂ E.φ (sl2D t) ∈ H := fun t => by
    rw [phi6_apply]; exact r12_conj_H R _ (E.hD t)
  have hscal : ∀ t : E.Fˣ, ∃ a : E.F, ∀ y : E.F,
      phi6 r₁ r₂ E.φ (sl2D t) * φ₂ (sl2U y) * (phi6 r₁ r₂ E.φ (sl2D t))⁻¹ =
        φ₂ (sl2U (a * y)) := by
    intro t
    have hU' : ∀ c : E.F, ∃ d : E.F, phi6 r₁ r₂ E.φ (sl2D t) * φ₂ (sl2U c) *
        (phi6 r₁ r₂ E.φ (sl2D t))⁻¹ = φ₂ (sl2U d) := fun c => by
      have := R.invariant 2 (isRoot_of_pos_le (by norm_num) (by norm_num)) _ (hD6 t) _
        ((hφ₂U _).2 ⟨c, rfl⟩)
      obtain ⟨d, hd⟩ := (hφ₂U _).1 this
      exact ⟨d, hd.symm⟩
    have hL' : ∀ c : E.F, ∃ d : E.F, phi6 r₁ r₂ E.φ (sl2D t) * φ₂ (sl2L c) *
        (phi6 r₁ r₂ E.φ (sl2D t))⁻¹ = φ₂ (sl2L d) := fun c => by
      have := R.invariant (-2) ⟨by norm_num, by norm_num⟩ _ (hD6 t) _ ((hφ₂L _).2 ⟨c, rfl⟩)
      obtain ⟨d, hd⟩ := (hφ₂L _).1 this
      exact ⟨d, hd.symm⟩
    obtain ⟨a, -, ha, -⟩ := exists_scalar_of_normalizes hF2 φ₂ hφ₂inj R.comm_H hφ₂D (hD6 t) hU' hL'
    exact ⟨a, ha⟩
  choose a ha using hscal
  obtain ⟨x₂, x₄, h2add, h2inj, h2mem, h2surj, h4add, h4inj, h4mem, h4surj, hrel, hw2, hw4⟩ :=
    hnp.exists_coords (xB := fun y => φ₂ (sl2U y))
      (fun y y' => by rw [sl2U_add, map_mul]) (fun y y' h => sl2U_injective (hφ₂inj h))
      (fun y => (hφ₂U _).2 ⟨y, rfl⟩) (fun b hb => (hφ₂U b).1 hb) a ha rfl E.toRankOneAt.card_root
  exact ⟨x₂, x₄, h2add, h2inj, h2mem, h2surj, h4add, h4inj, h4mem, h4surj, hrel, hw2, hw4⟩

end CFSG.GH74.GLS.Stage4.Hex
