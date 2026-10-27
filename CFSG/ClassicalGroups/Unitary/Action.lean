module

public import CFSG.ClassicalGroups.Unitary.Transitivity

public section

namespace CFSG.ClassicalGroups.Unitary

open Matrix CFSG.LieType.Universal.Unitary CFSG.Assembly.LowTwoRank
open scoped LinearAlgebra.Projectivization

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

variable (σ) in
@[expose] def IsIsoPt (x : ℙ K (Fin n → K)) : Prop := herm σ x.rep x.rep = 0

theorem isIsoPt_mk {v : Fin n → K} (hv : v ≠ 0) :
    IsIsoPt σ (Projectivization.mk K v hv) ↔ herm σ v v = 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep K v hv
  rw [IsIsoPt, ← ha, Units.smul_def, herm_smul_left, herm_smul_right]
  have h0 : σ (a : K) ≠ 0 := (map_ne_zero σ).mpr a.ne_zero
  constructor
  · intro h
    exact (mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_left h0)).resolve_left a.ne_zero
  · intro h
    rw [h, mul_zero, mul_zero]

variable (σ n) in
@[expose] def isoPts : SubMulAction (SUid σ n) (ℙ K (Fin n → K)) where
  carrier := {x | IsIsoPt σ x}
  smul_mem' g x hx := by
    induction x using Projectivization.ind with
    | h v hv =>
      change IsIsoPt σ (Projectivization.mk K (g • v) ((smul_ne_zero_iff_ne g).mpr hv))
      rw [isIsoPt_mk, herm_smul_smul]
      exact (isIsoPt_mk hv).mp hx

@[expose] def pt (v : Fin n → K) (hv : v ≠ 0) (hiso : herm σ v v = 0) : isoPts σ n :=
  ⟨Projectivization.mk K v hv, (isIsoPt_mk hv).mpr hiso⟩

theorem isoPts_ind {P : isoPts σ n → Prop}
    (h : ∀ (v : Fin n → K) (hv : v ≠ 0) (hiso : herm σ v v = 0), P (pt v hv hiso)) :
    ∀ x, P x := by
  rintro ⟨x, hx⟩
  induction x using Projectivization.ind with
  | h v hv => exact h v hv ((isIsoPt_mk hv).mp hx)

theorem smul_pt (g : SUid σ n) {v : Fin n → K} (hv : v ≠ 0) (hiso : herm σ v v = 0) :
    g • pt v hv hiso = pt (g • v) ((smul_ne_zero_iff_ne g).mpr hv)
      (by rw [herm_smul_smul]; exact hiso) :=
  rfl

theorem pt_eq_pt_iff {v w : Fin n → K} (hv : v ≠ 0) (hw : w ≠ 0) (hv' : herm σ v v = 0)
    (hw' : herm σ w w = 0) : pt v hv hv' = pt w hw hw' ↔ ∃ c : K, c • w = v := by
  rw [← Projectivization.mk_eq_mk_iff' K v w hv hw]
  exact Subtype.ext_iff

theorem pt_eq_pt_of_smul {v w : Fin n → K} (hv : v ≠ 0) (hw : w ≠ 0) (hv' : herm σ v v = 0)
    (hw' : herm σ w w = 0) (c : K) (h : v = c • w) : pt v hv hv' = pt w hw hw' :=
  (pt_eq_pt_iff hv hw hv' hw').mpr ⟨c, h.symm⟩

theorem isPretransitive_isoPts (hσ : IsUnitaryInvolution σ) (hn : 3 ≤ n) :
    MulAction.IsPretransitive (SUid σ n) (isoPts σ n) := by
  refine ⟨fun x y => ?_⟩
  induction x using isoPts_ind with
  | h v hv hiso =>
  induction y using isoPts_ind with
  | h w hw hiso' =>
  obtain ⟨t, -, ht⟩ := exists_mem_T_smul_eq_of_iso hσ hn hv hiso hw hiso'
  refine ⟨t, ?_⟩
  rw [smul_pt]
  exact pt_eq_pt_of_smul _ _ _ _ 1 (by rw [ht, one_smul])

theorem smul_eq_of_mem_scalars {g : SUid σ n}
    (hg : g ∈ (StatedScalars (Fin n) K).subgroupOf (SUid σ n)) (x : isoPts σ n) : g • x = x := by
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hg
  obtain ⟨u, hu⟩ := hg
  induction x using isoPts_ind with
  | h v hv hiso =>
  rw [smul_pt]
  refine pt_eq_pt_of_smul _ _ _ _ (u : K) ?_
  rw [smul_def, ← hu, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  ext k
  simp [Matrix.mulVec_diagonal]

theorem mem_scalars_of_smul_eq (hσ : IsUnitaryInvolution σ) (hn : 3 ≤ n) {g : SUid σ n}
    (hg : ∀ x : isoPts σ n, g • x = x) :
    g ∈ (StatedScalars (Fin n) K).subgroupOf (SUid σ n) := by
  obtain ⟨W⟩ := hσ.nonempty_wittData
  obtain ⟨M, hMdef⟩ : ∃ M, M = ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := ⟨_, rfl⟩
  have hev : ∀ (i j : Fin n), i ≠ j → ∀ t : K, σ t * t = -1 →
      ∃ c : K, ∀ k, M k i + M k j * t = c * (Pi.single i 1 + Pi.single j t : Fin n → K) k := by
    intro i j hij t ht
    have hv0 : (Pi.single i 1 + Pi.single j t : Fin n → K) ≠ 0 := by
      intro h
      have := congrFun h i
      simp [Pi.single_eq_of_ne hij] at this
    have hiso : herm σ (Pi.single i 1 + Pi.single j t : Fin n → K)
        (Pi.single i 1 + Pi.single j t) = 0 := by
      rw [herm_single_add_single hij, ht]; ring
    have h := hg (pt _ hv0 hiso)
    rw [smul_pt, pt_eq_pt_iff] at h
    obtain ⟨c, hc⟩ := h
    refine ⟨c, fun k => ?_⟩
    have hmv : (M *ᵥ (Pi.single i 1 + Pi.single j t)) k = M k i + M k j * t := by
      simp [mulVec_add, mul_comm]
    have := congrFun hc k
    rw [smul_def, ← hMdef, hmv] at this
    simp only [Pi.smul_apply, smul_eq_mul] at this
    linear_combination -this
  have hu0 := W.u_ne_zero
  have huω : W.u - W.u * W.ω ≠ 0 := by
    rw [show W.u - W.u * W.ω = W.u * (1 - W.ω) by ring]
    exact mul_ne_zero hu0 W.one_sub_ω_ne_zero
  have hNuω : σ (W.u * W.ω) * (W.u * W.ω) = -1 := by
    rw [map_mul, show σ W.u * σ W.ω * (W.u * W.ω) = (σ W.u * W.u) * (σ W.ω * W.ω) by ring,
      W.hu, W.hω]
    ring
  have hoff : ∀ k j : Fin n, k ≠ j → M k j = 0 := by
    intro k j hkj
    obtain ⟨i, hij, hik⟩ := Fin.exists_ne_and_ne_of_two_lt j k (by omega)
    obtain ⟨c₁, hc₁⟩ := hev i j hij W.u W.hu
    obtain ⟨c₂, hc₂⟩ := hev i j hij (W.u * W.ω) hNuω
    have h1 := hc₁ k
    have h2 := hc₂ k
    simp only [Pi.add_apply, Pi.single_eq_of_ne hik.symm, Pi.single_eq_of_ne hkj, add_zero,
      mul_zero] at h1 h2
    have h3 : M k j * (W.u - W.u * W.ω) = 0 := by linear_combination h1 - h2
    exact (mul_eq_zero.mp h3).resolve_right huω
  have hdiag : ∀ i j : Fin n, i ≠ j → M j j = M i i := by
    intro i j hij
    obtain ⟨c, hc⟩ := hev i j hij W.u W.hu
    have h1 := hc i
    have h2 := hc j
    simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij.symm,
      Pi.single_eq_of_ne hij, add_zero, zero_add, mul_one] at h1 h2
    rw [hoff i j hij, zero_mul, add_zero] at h1
    rw [hoff j i hij.symm, zero_add] at h2
    have h3 : (M j j - M i i) * W.u = 0 := by linear_combination h2 - W.u * h1
    exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right hu0)
  set i₀ : Fin n := ⟨0, by omega⟩
  have hM : M = Matrix.scalar (Fin n) (M i₀ i₀) := by
    ext i j
    rw [Matrix.scalar_apply]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq]
      by_cases hi : i = i₀
      · rw [hi]
      · exact hdiag i₀ i (Ne.symm hi)
    · rw [Matrix.diagonal_apply_ne _ hij, hoff i j hij]
  have hdet : M.det = 1 := by rw [hMdef]; exact ((mem_SUid_iff σ).mp g.2).1
  have hd0 : M i₀ i₀ ≠ 0 := by
    intro h
    have : Nonempty (Fin n) := ⟨i₀⟩
    rw [hM, h, map_zero, Matrix.det_zero] at hdet
    exact zero_ne_one hdet
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]
  refine ⟨Units.mk0 _ hd0, ?_⟩
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0, ← hMdef]
  exact hM.symm

theorem exists_fix_smul_eq (hσ : IsUnitaryInvolution σ) {a b b' : Fin n → K}
    (ha : herm σ a a = 0) (hb : herm σ b b = 0) (hb' : herm σ b' b' = 0)
    (hab : herm σ a b ≠ 0) (hab' : herm σ a b' ≠ 0) :
    ∃ g : SUid σ n, g • a = a ∧ g • b = (herm σ a b / herm σ a b') • b' := by
  set b₁ := (herm σ a b)⁻¹ • b with hb₁
  set b₂ := (herm σ a b')⁻¹ • b' with hb₂
  have hab₁ : herm σ a b₁ = 1 := by rw [hb₁, herm_smul_right, inv_mul_cancel₀ hab]
  have hab₂ : herm σ a b₂ = 1 := by rw [hb₂, herm_smul_right, inv_mul_cancel₀ hab']
  have hb₁a : herm σ b₁ a = 1 := by rw [herm_conj σ hσ.invol, hab₁, map_one]
  have hb₂a : herm σ b₂ a = 1 := by rw [herm_conj σ hσ.invol, hab₂, map_one]
  have hb₁b₁ : herm σ b₁ b₁ = 0 := by rw [hb₁, herm_smul_left, herm_smul_right, hb]; ring
  have hb₂b₂ : herm σ b₂ b₂ = 0 := by rw [hb₂, herm_smul_left, herm_smul_right, hb']; ring
  set c := herm σ b₁ b₂ with hc
  have hb₂b₁ : herm σ b₂ b₁ = σ c := herm_conj σ hσ.invol b₁ b₂
  set y := b₂ - b₁ - c • a with hy
  have hay : herm σ a y = 0 := by rw [hy]; simp [hab₁, hab₂, ha]
  have hyb₁ : herm σ y b₁ = 0 := by rw [hy]; simp [hb₂b₁, hb₁b₁, hab₁]
  have hcy : c + σ c = -herm σ y y := by
    rw [hy]
    simp only [herm_sub_left, herm_sub_right, herm_smul_left, herm_smul_right, hb₂b₂, hb₁b₁,
      hb₂b₁, ← hc, hb₂a, hb₁a, hab₁, hab₂, ha]
    ring
  set E := eichler hσ.invol ha hay hcy with hE
  have hEb₁ : E • b₁ = b₂ := by
    rw [hE, eichler_smul, hab₁, hyb₁, one_smul, zero_smul, sub_zero, hy]
    abel
  refine ⟨E, eichler_smul_self hσ.invol ha hay hcy, ?_⟩
  have hb1 : b = herm σ a b • b₁ := by rw [hb₁, smul_smul, mul_inv_cancel₀ hab, one_smul]
  conv_lhs => rw [hb1]
  rw [smul_comm, hEb₁, hb₂, smul_smul, div_eq_mul_inv]

theorem exists_fix_herm_ne_zero (hσ : IsUnitaryInvolution σ) {a b : Fin n → K} (ha0 : a ≠ 0)
    (ha : herm σ a a = 0) (hb : herm σ b b = 0) (hab : herm σ a b = 0)
    (hba : ∀ c : K, b ≠ c • a) : ∃ g : SUid σ n, g • a = a ∧ herm σ b (g • b) ≠ 0 := by
  obtain ⟨d, hd, had, hbd⟩ := exists_iso_perp hσ ha0 ha hb hab hba
  obtain ⟨τ, hτ0, hτ⟩ := hσ.exists_traceZero
  have hda : herm σ d a = 0 := herm_eq_zero_comm σ hσ.invol had
  refine ⟨tv hσ.invol hd hτ, ?_, ?_⟩
  · rw [tv_smul, hda, mul_zero, zero_smul, add_zero]
  · rw [tv_smul, herm_add_right, herm_smul_right, hb, zero_add, herm_conj σ hσ.invol b d]
    exact mul_ne_zero (mul_ne_zero hτ0 ((map_ne_zero σ).mpr hbd)) hbd

section Blocks

variable {B : Set (isoPts σ n)}

theorem smul_mem_of_isBlock (hB : MulAction.IsBlock (SUid σ n) B) {x y : isoPts σ n}
    (hx : x ∈ B) (hy : y ∈ B) {g : SUid σ n} (hg : g • x = x) : g • y ∈ B := by
  have h := hB.smul_eq_of_mem hx (by rwa [hg])
  rw [← h]
  exact Set.smul_mem_smul_set hy

theorem mem_of_isBlock_opp (hσ : IsUnitaryInvolution σ) (hB : MulAction.IsBlock (SUid σ n) B)
    {a b c : Fin n → K} (ha0 : a ≠ 0) (ha : herm σ a a = 0) (hb0 : b ≠ 0)
    (hb : herm σ b b = 0) (hc0 : c ≠ 0) (hc : herm σ c c = 0) (haB : pt a ha0 ha ∈ B)
    (hbB : pt b hb0 hb ∈ B) (hab : herm σ a b ≠ 0) (hac : herm σ a c ≠ 0) :
    pt c hc0 hc ∈ B := by
  obtain ⟨g, hga, hgb⟩ := exists_fix_smul_eq hσ ha hb hc hab hac
  have hg : g • pt a ha0 ha = pt a ha0 ha := by
    rw [smul_pt]
    exact pt_eq_pt_of_smul _ _ _ _ 1 (by rw [hga, one_smul])
  have := smul_mem_of_isBlock hB haB hbB hg
  rw [smul_pt] at this
  rwa [pt_eq_pt_of_smul _ hc0 _ hc _ hgb] at this

theorem eq_univ_of_isBlock_opp (hσ : IsUnitaryInvolution σ)
    (hB : MulAction.IsBlock (SUid σ n) B) {a b : Fin n → K} (ha0 : a ≠ 0) (ha : herm σ a a = 0)
    (hb0 : b ≠ 0) (hb : herm σ b b = 0) (haB : pt a ha0 ha ∈ B) (hbB : pt b hb0 hb ∈ B)
    (hab : herm σ a b ≠ 0) : B = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  induction x using isoPts_ind with
  | h c hc0 hc =>
  by_cases hac : herm σ a c ≠ 0
  · exact mem_of_isBlock_opp hσ hB ha0 ha hb0 hb hc0 hc haB hbB hab hac
  push Not at hac
  obtain ⟨d, hd, had, hcd⟩ := exists_cno hσ ha0 ha hc0
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact had (herm_zero_right σ a)
  have hdB := mem_of_isBlock_opp hσ hB ha0 ha hb0 hb hd0 hd haB hbB hab had
  have hda : herm σ d a ≠ 0 := by
    rw [herm_conj σ hσ.invol]
    exact (map_ne_zero σ).mpr had
  have hdc : herm σ d c ≠ 0 := by
    rw [herm_conj σ hσ.invol]
    exact (map_ne_zero σ).mpr hcd
  exact mem_of_isBlock_opp hσ hB hd0 hd ha0 ha hc0 hc hdB haB hda hdc

end Blocks

theorem isPreprimitive_isoPts (hσ : IsUnitaryInvolution σ) (hn : 3 ≤ n) :
    MulAction.IsPreprimitive (SUid σ n) (isoPts σ n) := by
  have := isPretransitive_isoPts hσ hn
  obtain ⟨W⟩ := hσ.nonempty_wittData
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  set a₀ := W.hypA m with ha₀def
  have ha₀ : herm σ a₀ a₀ = 0 := W.herm_hypA_hypA
  have ha₀0 : a₀ ≠ 0 := W.hypA_ne_zero
  apply MulAction.IsPreprimitive.of_isTrivialBlock_base (pt a₀ ha₀0 ha₀)
  intro B hL₀ hB
  by_cases hsub : B.Subsingleton
  · exact Or.inl hsub
  right
  obtain ⟨M, hMB, hML⟩ : ∃ M ∈ B, M ≠ pt a₀ ha₀0 ha₀ := by
    by_contra hcon
    push Not at hcon
    exact hsub fun x hx y hy => by rw [hcon x hx, hcon y hy]
  induction M using isoPts_ind with
  | h b hb0 hb =>
  by_cases hab : herm σ a₀ b = 0
  · have hba : ∀ c : K, b ≠ c • a₀ := by
      intro c hc
      exact hML (pt_eq_pt_of_smul _ _ _ _ c hc)
    obtain ⟨g, hga, hgb⟩ := exists_fix_herm_ne_zero hσ ha₀0 ha₀ hb hab hba
    have hg : g • pt a₀ ha₀0 ha₀ = pt a₀ ha₀0 ha₀ := by
      rw [smul_pt]
      exact pt_eq_pt_of_smul _ _ _ _ 1 (by rw [hga, one_smul])
    have hgB := smul_mem_of_isBlock hB hL₀ hMB hg
    rw [smul_pt] at hgB
    exact eq_univ_of_isBlock_opp hσ hB hb0 hb _ _ hMB hgB hgb
  · exact eq_univ_of_isBlock_opp hσ hB ha₀0 ha₀ hb0 hb hL₀ hMB hab

end CFSG.ClassicalGroups.Unitary
