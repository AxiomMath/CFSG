module

public import CFSG.GH74.GLS.Stage2.Final.ModelCenAb
public import CFSG.GH74.GLS.Stage2.Final.ModelSylow

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelBlock

open CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Matrix Subgroup

variable {F : Type} [Field F]

theorem mkP_diag_eq_iff {M : ModelData F} {a b a' b' : GL (Fin 2) F} (h : diagGL a b ∈ M.K4)
    (h' : diagGL a' b' ∈ M.K4) :
    mkP M ⟨diagGL a b, h⟩ = mkP M ⟨diagGL a' b', h'⟩ ↔
      ∃ c : Fˣ, a' = sc2 c * a ∧ b' = sc2 c * b := by
  rw [mkP_eq_iff]
  constructor
  · rintro ⟨c, hc⟩
    have h1 : diagGL a⁻¹ b⁻¹ * diagGL a' b' = diagGL (sc2 c) (sc2 c) := by
      rw [← diagGL_inv]
      rw [← scalar4_eq]
      exact hc
    rw [diagGL_mul] at h1
    obtain ⟨h2, h3⟩ := diagGL_inj h1
    refine ⟨c, ?_, ?_⟩
    · rw [inv_mul_eq_iff_eq_mul] at h2
      rw [h2]; exact (sc2_comm c a).symm
    · rw [inv_mul_eq_iff_eq_mul] at h3
      rw [h3]; exact (sc2_comm c b).symm
  · rintro ⟨c, h1, h2⟩
    refine ⟨c, ?_⟩
    show (diagGL a b)⁻¹ * diagGL a' b' = _
    rw [scalar4_eq, diagGL_inv, diagGL_mul, h1, h2, sc2_comm c a, sc2_comm c b,
      inv_mul_cancel_left, inv_mul_cancel_left]

theorem dRefl_inv : (dRefl F)⁻¹ = dRefl F := inv_eq_of_mul_eq_one_right dRefl_mul_self

theorem dRefl_not_scalar (h2 : (2 : F) ≠ 0) (c : Fˣ) : dRefl F ≠ sc2 c := by
  intro h
  have h00 := congrArg (fun u : GL (Fin 2) F => (u : Matrix (Fin 2) (Fin 2) F) 0 0) h
  have h11 := congrArg (fun u : GL (Fin 2) F => (u : Matrix (Fin 2) (Fin 2) F) 1 1) h
  simp [coe_dRefl, sc2, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h00 h11
  apply h2
  linear_combination h00 - h11

theorem dRefl_ne_one (h2 : (2 : F) ≠ 0) : dRefl F ≠ 1 := fun h =>
  dRefl_not_scalar h2 1 (by rw [h, sc2_one])

theorem dRefl_ne_neg_one (h2 : (2 : F) ≠ 0) : dRefl F ≠ -1 := fun h =>
  dRefl_not_scalar h2 (-1) (by rw [h, sc2_neg_one])

theorem neg_dRefl_ne_one (h2 : (2 : F) ≠ 0) : -dRefl F ≠ 1 := fun h =>
  dRefl_ne_neg_one h2 (neg_eq_iff_eq_neg.1 h)

theorem isConj_yP_of_ConjMod {M : ModelData F} {g : GL (Fin 4) F} (hg : g ∈ M.K4)
    (h : ConjMod M g (xyGL F)) : IsConj (yP M) (mkP M ⟨g, hg⟩) := by
  have := isConj_of_ConjMod hg M.xyGL_mem_K4 h
  have e : (⟨xyGL F, M.xyGL_mem_K4⟩ : ↥M.K4) = M.xyK := rfl
  rw [e, mkP_xyK] at this
  exact this.symm

theorem tP_mul_dP (M : ModelData F) {a : GL (Fin 2) F} (ha : a ∈ M.U2) :
    tP M * dP M a ha = mkP M ⟨swapGL F * diagGL a a⁻¹,
      M.K4.mul_mem M.swapGL_mem_K4 (diag_inv_mem_K4 M ha)⟩ := by
  rw [tP, dP, ← map_mul]
  rfl

theorem tP_conj_dP (M : ModelData F) {a : GL (Fin 2) F} (ha : a ∈ M.U2) :
    tP M * dP M a ha * (tP M)⁻¹ = (dP M a ha)⁻¹ := by
  have key : (M.wK * (⟨diagGL a a⁻¹, diag_inv_mem_K4 M ha⟩ : ↥M.K4) * M.wK⁻¹ : ↥M.K4) =
      (⟨diagGL a a⁻¹, diag_inv_mem_K4 M ha⟩ : ↥M.K4)⁻¹ := by
    apply Subtype.ext
    show swapGL F * diagGL a a⁻¹ * (swapGL F)⁻¹ = (diagGL a a⁻¹)⁻¹
    rw [swapGL_mul_diagGL_mul_inv, diagGL_inv, inv_inv]
  calc tP M * dP M a ha * (tP M)⁻¹
      = mkP M (M.wK * (⟨diagGL a a⁻¹, diag_inv_mem_K4 M ha⟩ : ↥M.K4) * M.wK⁻¹) := by
        simp only [tP, dP, map_mul, map_inv]
    _ = mkP M ((⟨diagGL a a⁻¹, diag_inv_mem_K4 M ha⟩ : ↥M.K4)⁻¹) := by rw [key]
    _ = (dP M a ha)⁻¹ := by simp only [dP, map_inv]

theorem dP_mul_self {M : ModelData F} {a : GL (Fin 2) F} (ha : a ∈ M.U2) (h : a * a = 1) :
    dP M a ha * dP M a ha = 1 := by
  have key : (⟨diagGL a a⁻¹, diag_inv_mem_K4 M ha⟩ : ↥M.K4) *
      (⟨diagGL a a⁻¹, diag_inv_mem_K4 M ha⟩ : ↥M.K4) = 1 := by
    apply Subtype.ext
    show diagGL a a⁻¹ * diagGL a a⁻¹ = 1
    rw [diagGL_mul, h, ← _root_.mul_inv_rev, h, inv_one, diagGL_one]
  rw [dP, ← map_mul, key, map_one]

theorem dP_pow_four {M : ModelData F} {a : GL (Fin 2) F} (ha : a ∈ M.U2) (h : a ^ 4 = 1) :
    dP M a ha ^ 4 = 1 := by
  have key : (⟨diagGL a a⁻¹, diag_inv_mem_K4 M ha⟩ : ↥M.K4) ^ 4 = 1 := by
    apply Subtype.ext
    show (diagGL a a⁻¹) ^ 4 = 1
    rw [diagGL_pow, h, inv_pow, h, inv_one, diagGL_one]
  rw [dP, ← map_pow, key, map_one]

theorem mem_normalizer_zpowers {G : Type*} [Group G] {g x : G} (hg : g * x * g⁻¹ = x⁻¹)
    (hg2 : g * g = 1) : g ∈ Subgroup.normalizer (zpowers x : Set G) := by
  have hgi : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg2
  have hconj : ∀ k ∈ zpowers x, g * k * g⁻¹ ∈ zpowers x := by
    intro k hk
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    have : g * x ^ n * g⁻¹ = (g * x * g⁻¹) ^ n := (conj_zpow).symm
    rw [this, hg, _root_.inv_zpow']
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) _
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh; exact hconj h hh
  · intro hh
    have := hconj _ hh
    have e : g * (g * h * g⁻¹) * g⁻¹ = h := by rw [hgi]; calc g * (g * h * g) * g = (g * g) * h * (g * g) := by group
      _ = h := by rw [hg2]; group
    rw [e] at this
    exact this

theorem iota_mul_eq_mkP_diag (M : ModelData F) (x y : ↥M.H2)
    (hxy : diagGL (x : GL (Fin 2) F) (y : GL (Fin 2) F) ∈ M.K4) :
    iota1 M x * iota2 M y = mkP M ⟨diagGL x y, hxy⟩ := by
  rw [iota1_apply, iota2_apply, ← map_mul]
  congr 1
  apply Subtype.ext
  show blkL F (x : GL (Fin 2) F) * blkR F (y : GL (Fin 2) F) = diagGL (x : GL (Fin 2) F) y
  rw [← diagGL_eq_blkL_mul_blkR]

theorem diagGL_mem_K4_of_H2 (M : ModelData F) (x y : ↥M.H2) :
    diagGL (x : GL (Fin 2) F) (y : GL (Fin 2) F) ∈ M.K4 :=
  M.diagGL_mem_K4_iff.2 ⟨((M.mem_H2 _).1 x.2).1, ((M.mem_H2 _).1 y.2).1, by
    rw [((M.mem_H2 _).1 x.2).2, ((M.mem_H2 _).1 y.2).2, one_mul]⟩

theorem dP_not_mem_E (M : ModelData F) {a₀ : GL (Fin 2) F} (ha₀ : a₀ ∈ M.U2)
    (hdet : ∀ s : Fˣ, sc4 s ∈ M.K4 → (a₀ : Matrix (Fin 2) (Fin 2) F).det ≠ (s : F) ^ 2) :
    dP M a₀ ha₀ ∉ K1 M ⊔ K2 M := by
  intro hb'
  obtain ⟨x, y, hxy⟩ := (mem_E_iff M).1 hb'
  have hxyK := diagGL_mem_K4_of_H2 M x y
  have heq : mkP M ⟨diagGL a₀ a₀⁻¹, diag_inv_mem_K4 M ha₀⟩ = mkP M ⟨diagGL x y, hxyK⟩ := by
    rw [← iota_mul_eq_mkP_diag M x y hxyK]
    exact hxy
  obtain ⟨c, h1, h2'⟩ := (mkP_diag_eq_iff _ _).1 heq
  have hdx : ((x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := ((M.mem_H2 _).1 x.2).2
  rw [h1, Units.val_mul, Matrix.det_mul, det_sc2] at hdx
  have hsc : sc4 c ∈ M.K4 := by
    have e : sc4 c = diagGL x y * (diagGL a₀ a₀⁻¹)⁻¹ := by
      rw [show (sc4 c : GL (Fin 4) F) = diagGL (sc2 c) (sc2 c) from scalar4_eq c, h1, h2',
        diagGL_inv, diagGL_mul, mul_inv_cancel_right, mul_inv_cancel_right]
    rw [e]
    exact M.K4.mul_mem hxyK (M.K4.inv_mem (diag_inv_mem_K4 M ha₀))
  have hsc' : sc4 c⁻¹ ∈ M.K4 := by rw [map_inv]; exact M.K4.inv_mem hsc
  apply hdet c⁻¹ hsc'
  have hc0 : (c : F) ≠ 0 := c.ne_zero
  rw [Units.val_inv_eq_inv_val, inv_pow]
  field_simp
  linear_combination hdx

theorem dRefl_neg_mem {M : ModelData F} (hd : dRefl F ∈ M.U2) : -dRefl F ∈ M.U2 := by
  have := M.U2.mul_mem M.neg_mem hd
  simpa using this

open CFSG.GH74.GLS.LU.Local in
theorem exists_luSylow [Finite F] {M : ModelData F} (hG : GoodModel M) (hF : LUFacts M)
    {a₀ : GL (Fin 2) F} (ha₀ : a₀ ∈ M.U2) (ha₀4 : a₀ ^ 4 = 1)
    (hdet : ∀ s : Fˣ, sc4 s ∈ M.K4 → (a₀ : Matrix (Fin 2) (Fin 2) F).det ≠ (s : F) ^ 2)
    (hd : dRefl F ∈ M.U2)
    (hu : dP M (dRefl F) hd ∈ zpowers (dP M a₀ ha₀) ⊔ zpowers (tP M))
    {o : ℕ} (ho : Odd o) (hidx : ((K1 M ⊔ K2 M).subgroupOf (Cg M)).index = 4 * o)
    (hcs : ∀ s ∈ BSsub M, (∃ i : ℕ, s ^ 2 ^ i = 1) → s = 1 ∨ s = yP M) :
    ∃ S : Sylow 2 (PG M), (S : Subgroup (PG M)) ≤ Cg M ∧
      LUSyl (PG M) (yP M) S (K1 M) (K2 M) (tP M) (dP M (dRefl F) hd) ∧
      ∀ s ∈ (S : Subgroup (PG M)), ∃ k ∈ (S : Subgroup (PG M)) ⊓ (K1 M ⊔ K2 M),
        s = k ∨ s = k * tP M ∨ s = k * dP M a₀ ha₀ ∨ s = k * (tP M * dP M a₀ ha₀) := by
  classical
  have h2 := hG.two_ne_zero
  have hCodd : Odd (Cg M).index := by rw [index_C]; exact hG.odd_index
  have hEn := layer_normal_Cg M h2 hG.qs
  have hEC := E_le_Cg M
  have hb4 : dP M a₀ ha₀ ^ 4 = 1 := dP_pow_four ha₀ ha₀4
  have hbord : ∃ i : ℕ, dP M a₀ ha₀ ^ 2 ^ i = 1 := ⟨2, by simpa using hb4⟩
  have hord : ∃ i : ℕ, tP M ^ 2 ^ i = 1 := ⟨1, by simpa [pow_two] using tP_sq M⟩
  have hzb : IsPGroup 2 ↥(zpowers (dP M a₀ ha₀)) := by
    obtain ⟨j, hj⟩ := ModelSylowQ.card_zpowers_two_pow hbord
    exact IsPGroup.of_card hj
  have hza : IsPGroup 2 ↥(zpowers (tP M)) := by
    obtain ⟨j, hj⟩ := ModelSylowQ.card_zpowers_two_pow hord
    exact IsPGroup.of_card hj
  have hnorm : zpowers (tP M) ≤ Subgroup.normalizer (zpowers (dP M a₀ ha₀) : Set (PG M)) := by
    rw [Subgroup.zpowers_le]
    exact mem_normalizer_zpowers (tP_conj_dP M ha₀) (tP_sq M)
  have hW : IsPGroup 2 ↥(zpowers (dP M a₀ ha₀) ⊔ zpowers (tP M)) :=
    hzb.to_sup_of_normal_left' hza hnorm
  have haW : tP M ∈ zpowers (dP M a₀ ha₀) ⊔ zpowers (tP M) :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hbW : dP M a₀ ha₀ ∈ zpowers (dP M a₀ ha₀) ⊔ zpowers (tP M) :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hWC : zpowers (dP M a₀ ha₀) ⊔ zpowers (tP M) ≤ Cg M :=
    sup_le (Subgroup.zpowers_le.2 (dP_mem_Cg M ha₀)) (Subgroup.zpowers_le.2 (tP_mem_Cg M))
  have haE : tP M ∉ K1 M ⊔ K2 M := tP_not_mem_E M h2
  have hbE : dP M a₀ ha₀ ∉ K1 M ⊔ K2 M := dP_not_mem_E M ha₀ hdet
  have habE : tP M * dP M a₀ ha₀ ∉ K1 M ⊔ K2 M := tP_mul_not_mem_E M h2 (dP_mem_C0 M ha₀)
  have ha2 : tP M * tP M ∈ K1 M ⊔ K2 M := by rw [tP_sq]; exact Subgroup.one_mem _
  obtain ⟨S, hSC, haS, hbS, hcard, hdec⟩ := exists_sylow_le_quot4 (Cg M) (K1 M ⊔ K2 M) hCodd hEC
    hEn ho hidx hW haW hbW hWC ha2 haE hbE habE
  refine ⟨S, hSC, ?_, hdec⟩
  have hzcen : CenterIs (S : Subgroup (PG M)) (yP M) := sylow_center_of_le_Cg hG S hSC
  have hWS : zpowers (dP M a₀ ha₀) ⊔ zpowers (tP M) ≤ (S : Subgroup (PG M)) :=
    sup_le (Subgroup.zpowers_le.2 hbS) (Subgroup.zpowers_le.2 haS)
  have hu2 : dP M (dRefl F) hd * dP M (dRefl F) hd = 1 := dP_mul_self hd dRefl_mul_self
  have hu1 : dP M (dRefl F) hd ≠ 1 := by
    intro h
    have h' : mkP M ⟨diagGL (dRefl F) (dRefl F)⁻¹, diag_inv_mem_K4 M hd⟩ =
        mkP M ⟨diagGL 1 1, by rw [diagGL_one]; exact M.K4.one_mem⟩ := by
      rw [show (⟨diagGL 1 1, by rw [diagGL_one]; exact M.K4.one_mem⟩ : ↥M.K4) = 1 from
        Subtype.ext diagGL_one, map_one]
      exact h
    obtain ⟨c, h1, -⟩ := (mkP_diag_eq_iff _ _).1 h'
    apply dRefl_not_scalar h2 c⁻¹
    rw [← sc2_inv]
    have h1' : sc2 c * dRefl F = 1 := h1.symm
    exact eq_inv_of_mul_eq_one_right h1'
  have ht : IsConj (yP M) (tP M) := by
    obtain ⟨k, hk, hkc⟩ := hF.w_conj
    exact isConj_yP_of_ConjMod M.swapGL_mem_K4 (ConjMod.of_conj hk hkc)
  refine ⟨orderOf_yP M h2, (centerIs_iff _ _).2 hzcen, haS, ht, tP_swap M, hWS hu,
    orderOf_eq_prime (by rw [sq]; exact hu2) hu1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hcard,
    LUCenAb.mono le_top (luCenAb_K1 hG)⟩
  ·
    intro h
    have h' : mkP M ⟨diagGL (dRefl F) (dRefl F)⁻¹, diag_inv_mem_K4 M hd⟩ =
        mkP M ⟨diagGL (-1) 1, M.yGL_mem_K4⟩ := h
    obtain ⟨c, -, h2'⟩ := (mkP_diag_eq_iff _ _).1 h'
    apply dRefl_not_scalar h2 c⁻¹
    rw [← sc2_inv]
    rw [dRefl_inv] at h2'
    exact eq_inv_of_mul_eq_one_right h2'.symm
  ·
    obtain ⟨k, hk, hkc⟩ := hF.perm_conj
    exact isConj_yP_of_ConjMod (diag_inv_mem_K4 M hd)
      (ConjMod.of_conj hk (by rw [dRefl_inv]; exact hkc))
  ·
    have hnd : -dRefl F ∈ M.U2 := dRefl_neg_mem hd
    have hmem : diagGL (-dRefl F) (dRefl F) ∈ M.K4 := by
      have := M.K4.mul_mem (diag_inv_mem_K4 M hd) M.yGL_mem_K4
      have e : diagGL (dRefl F) (dRefl F)⁻¹ * yGL F = diagGL (-dRefl F) (dRefl F) := by
        rw [yGL, diagGL_mul, dRefl_inv, mul_neg, mul_one]
      rwa [e] at this
    have hprod : dP M (dRefl F) hd * yP M = mkP M ⟨diagGL (-dRefl F) (dRefl F), hmem⟩ := by
      rw [dP, ← map_mul]
      congr 1
      apply Subtype.ext
      show diagGL (dRefl F) (dRefl F)⁻¹ * yGL F = diagGL (-dRefl F) (dRefl F)
      rw [yGL, diagGL_mul, dRefl_inv, mul_neg, mul_one]
    rw [hprod]
    refine isConj_yP_of_ConjMod hmem (D_refl hF hnd hd ?_ dRefl_mul_self (neg_dRefl_ne_one h2) ?_
      (dRefl_ne_one h2) (dRefl_ne_neg_one h2))
    · rw [neg_mul_neg]; exact dRefl_mul_self
    · intro h
      exact dRefl_ne_one h2 (neg_inj.1 h)
  ·
    exact normalizer_K1_of_C0 M h2 (dP_mem_C0 M hd)
  ·
    have h := tP_conj_dP M hd
    have hinv : (dP M (dRefl F) hd)⁻¹ = dP M (dRefl F) hd := inv_eq_of_mul_eq_one_right hu2
    rw [hinv, mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  ·
    intro s hs hsn
    obtain ⟨k, hk, hcases⟩ := hdec s hs
    have hkE : k ∈ K1 M ⊔ K2 M := hk.2
    have hkC0 : k ∈ C0 M := E_le_C0 M hkE
    have hk' : k⁻¹ ∈ (S : Subgroup (PG M)) ⊓ (K1 M ⊔ K2 M) :=
      ⟨S.inv_mem hk.1, (K1 M ⊔ K2 M).inv_mem hkE⟩
    refine ⟨k⁻¹, hk', ?_⟩
    rcases hcases with h | h | h | h
    · exfalso
      apply hsn
      rw [h]
      exact normalizer_K1_of_C0 M h2 hkC0
    · rw [h, ← mul_assoc, inv_mul_cancel, one_mul]
      exact ht
    · exfalso
      apply hsn
      rw [h]
      exact normalizer_K1_of_C0 M h2 ((C0 M).mul_mem hkC0 (dP_mem_C0 M ha₀))
    · rw [h, ← mul_assoc, inv_mul_cancel, one_mul, tP_mul_dP M ha₀]
      exact isConj_yP_of_ConjMod _ (W_one hF ha₀)
  ·
    intro s hs hcomm
    have hsC : s ∈ Cg M := hSC hs
    obtain ⟨p, hp⟩ := blockScalar_of_cent_E hG hsC hcomm
    have hsB : s ∈ BSsub M := ⟨p, hp⟩
    have hs2 : ∃ i : ℕ, s ^ 2 ^ i = 1 := by
      obtain ⟨i, hi⟩ := S.isPGroup' ⟨s, hs⟩
      exact ⟨i, by have := congrArg Subtype.val hi; simpa using this⟩
    rcases hcs s hsB hs2 with rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

end CFSG.GH74.GLS.Stage2.Final.ModelBlock
