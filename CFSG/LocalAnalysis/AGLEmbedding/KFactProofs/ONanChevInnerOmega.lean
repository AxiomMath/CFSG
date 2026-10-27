module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerBits
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerOrbit
public import CFSG.ClassicalGroups.Orthogonal.Simple
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.LieType.Universal.Spin QuadraticMap Matrix CFSG.ClassicalGroups.Orthogonal
  CFSG.Assembly.LowTwoRank

section Instances

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def Om8 : Subgroup (GL ι8 (ZMod 2)) := StatedOmega (StatedQuadPlus 4 (ZMod 2))

theorem Om8_eq : Om8 = (elementaryGroup (quadPlus 4 (ZMod 2))).map
    (toLinEquiv ι8 (ZMod 2)).symm.toMonoidHom :=
  statedOmega_quadPlus_eq_map (by norm_num)

theorem mem_Om8_iff (g : GL ι8 (ZMod 2)) :
    g ∈ Om8 ↔ toLinEquiv ι8 (ZMod 2) g ∈ elementaryGroup (quadPlus 4 (ZMod 2)) := by
  rw [Om8_eq, Subgroup.mem_map_equiv]
  rfl

theorem eichGL_mem (u w : V8) : eichGL u w ∈ Om8 := by
  rw [mem_Om8_iff]
  unfold eichGL
  rw [MulEquiv.apply_symm_apply]
  exact eichler_mem_elementaryGroup _ u w

theorem conj_eichGL {g : GL ι8 (ZMod 2)} (hg : g ∈ Om8) (u w : V8) :
    g * eichGL u w * g⁻¹ = eichGL ((g : Matrix ι8 ι8 (ZMod 2)) *ᵥ u)
      ((g : Matrix ι8 ι8 (ZMod 2)) *ᵥ w) := by
  have hgo : toLinEquiv ι8 (ZMod 2) g ∈ TauCeti.QuadraticMap.orthogonalGroup
      (quadPlus 4 (ZMod 2)) :=
    elementaryGroup_le_orthogonalGroup _ ((mem_Om8_iff g).1 hg)
  apply (toLinEquiv ι8 (ZMod 2)).injective
  rw [map_mul, map_mul, map_inv]
  unfold eichGL
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, eichler_conj hgo]
  rfl

@[expose] noncomputable def eg (pc : ℕ) : Om8 :=
  ⟨eichGL (bv (pc % 256)) (bv (pc / 256 % 256)), eichGL_mem _ _⟩

@[expose] def actPair (a : ℕ → ℕ) (pc : ℕ) : ℕ := a (pc % 256) + 256 * a (pc / 256 % 256)

theorem conj_eg (g : Om8) {pc : ℕ} :
    g * eg pc * g⁻¹ = eg (actPair (actG (g : GL ι8 (ZMod 2))) pc) := by
  apply Subtype.ext
  have h1 := actG_lt (g : GL ι8 (ZMod 2)) (pc % 256)
  have h2 := actG_lt (g : GL ι8 (ZMod 2)) (pc / 256 % 256)
  have e1 : actPair (actG (g : GL ι8 (ZMod 2))) pc % 256 =
      actG (g : GL ι8 (ZMod 2)) (pc % 256) := by unfold actPair; omega
  have e2 : actPair (actG (g : GL ι8 (ZMod 2))) pc / 256 % 256 =
      actG (g : GL ι8 (ZMod 2)) (pc / 256 % 256) := by unfold actPair; omega
  show (g : GL ι8 (ZMod 2)) * eichGL _ _ * (g : GL ι8 (ZMod 2))⁻¹ = eichGL _ _
  rw [conj_eichGL g.2, e1, e2]
  unfold actG
  rw [bv_bc, bv_bc]

@[expose] def canon (pc : ℕ) : ℕ :=
  pc % 256 + 256 * min (pc / 256 % 256) (addB (pc / 256 % 256) (pc % 256))

theorem eg_add_self (pc : ℕ) :
    eg (pc % 256 + 256 * addB (pc / 256 % 256) (pc % 256)) = eg pc := by
  apply Subtype.ext
  have hu : pc % 256 < 256 := Nat.mod_lt _ (by norm_num)
  have hw : addB (pc / 256 % 256) (pc % 256) < 256 := addB_lt _ _
  have e1 : (pc % 256 + 256 * addB (pc / 256 % 256) (pc % 256)) % 256 = pc % 256 := by omega
  have e2 : (pc % 256 + 256 * addB (pc / 256 % 256) (pc % 256)) / 256 % 256 =
      addB (pc / 256 % 256) (pc % 256) := by omega
  show eichGL (bv ((pc % 256 + 256 * addB (pc / 256 % 256) (pc % 256)) % 256))
      (bv ((pc % 256 + 256 * addB (pc / 256 % 256) (pc % 256)) / 256 % 256)) =
    eichGL (bv (pc % 256)) (bv (pc / 256 % 256))
  rw [e1, e2]
  have hwc : pc / 256 % 256 < 256 := Nat.mod_lt _ (by norm_num)
  have hadd : bv (addB (pc / 256 % 256) (pc % 256)) =
      bv (pc / 256 % 256) + bv (pc % 256) := by
    apply bc_injective
    rw [bc_bv hw, bc_add, bc_bv hwc, bc_bv hu]
  rw [hadd]
  unfold eichGL
  congr 1
  by_cases hQ : quadPlus 4 (ZMod 2) (bv (pc % 256)) = 0
  · simpa using eichler_add_smul_self (Q := quadPlus 4 (ZMod 2)) hQ (bv (pc / 256 % 256)) 1
  · rw [eichler_of_map_ne_zero hQ, eichler_of_map_ne_zero hQ]

theorem eg_canon (pc : ℕ) : eg (canon pc) = eg pc := by
  unfold canon
  rcases le_total (pc / 256 % 256) (addB (pc / 256 % 256) (pc % 256)) with h | h
  · rw [min_eq_left h]
    apply Subtype.ext
    have hu : pc % 256 < 256 := Nat.mod_lt _ (by norm_num)
    have hw : pc / 256 % 256 < 256 := Nat.mod_lt _ (by norm_num)
    have e1 : (pc % 256 + 256 * (pc / 256 % 256)) % 256 = pc % 256 := by omega
    have e2 : (pc % 256 + 256 * (pc / 256 % 256)) / 256 % 256 = pc / 256 % 256 := by omega
    show eichGL (bv ((pc % 256 + 256 * (pc / 256 % 256)) % 256))
      (bv ((pc % 256 + 256 * (pc / 256 % 256)) / 256 % 256)) =
        eichGL (bv (pc % 256)) (bv (pc / 256 % 256))
    rw [e1, e2]
  · rw [min_eq_right h]
    exact eg_add_self pc

@[expose] noncomputable def welt (ps : List (ℕ × ℕ)) : Om8 :=
  (ps.map fun p => eg (p.1 + 256 * p.2)).prod

@[expose] def wact (ps : List (ℕ × ℕ)) (c : ℕ) : ℕ := ps.foldr (fun p c => eAct p.1 p.2 c) c

theorem eAct_lt (u w c : ℕ) (hc : c < 256) : eAct u w c < 256 := by
  unfold eAct
  by_cases h : Qb u = 0 ∧ Bb u w = 0
  · simp only [h, and_self, ↓reduceIte]
    exact addB_lt _ _
  · simp only [h, ↓reduceIte]
    exact hc

theorem wact_lt (ps : List (ℕ × ℕ)) {c : ℕ} (hc : c < 256) : wact ps c < 256 := by
  induction ps with
  | nil => exact hc
  | cons p ps ih => exact eAct_lt _ _ _ ih

theorem actG_eg {u w c : ℕ} (hu : u < 256) (hw : w < 256) (hc : c < 256) :
    actG ((eg (u + 256 * w) : Om8) : GL ι8 (ZMod 2)) c = eAct u w c := by
  have e1 : (u + 256 * w) % 256 = u := by omega
  have e2 : (u + 256 * w) / 256 % 256 = w := by omega
  show actG (eichGL (bv ((u + 256 * w) % 256)) (bv ((u + 256 * w) / 256 % 256))) c = _
  rw [e1, e2, actG_eichGL _ _ hc, bc_bv hu, bc_bv hw]

theorem actG_welt (ps : List (ℕ × ℕ)) (hps : ∀ p ∈ ps, p.1 < 256 ∧ p.2 < 256) {c : ℕ}
    (hc : c < 256) : actG ((welt ps : Om8) : GL ι8 (ZMod 2)) c = wact ps c := by
  induction ps with
  | nil =>
    show actG 1 c = c
    exact actG_one hc
  | cons p ps ih =>
    have hp := hps p (List.mem_cons_self)
    have hrest : ∀ q ∈ ps, q.1 < 256 ∧ q.2 < 256 := fun q hq => hps q (List.mem_cons_of_mem _ hq)
    have hlt : wact ps c < 256 := wact_lt ps hc
    show actG ((eg (p.1 + 256 * p.2) : Om8) * (welt ps : Om8) : Om8) c = _
    rw [Subgroup.coe_mul, actG_mul, ih hrest, actG_eg hp.1 hp.2 hlt]
    rfl


theorem er_of_bfs (M : Subgroup Om8) (words : List (List (ℕ × ℕ)))
    (hw : ∀ ps ∈ words, welt ps ∈ M) (hlt : ∀ ps ∈ words, ∀ p ∈ ps, p.1 < 256 ∧ p.2 < 256)
    {start : ℕ} (hstart : eg start ∈ M) (steps : List (ℕ × ℕ)) {mask : ℕ}
    (hmask : bfsAux (fun k pc => canon (actPair (wact (words.getD k [])) pc)) steps
      (1 <<< start) = some mask) : ∀ c, mask.testBit c = true → eg c ∈ M := by
  refine bfsAux_sound (R := fun c => eg c ∈ M) _ ?_ steps _ mask ?_ hmask
  · intro k c hc
    have hpsw : welt (words.getD k []) ∈ M ∧
        ∀ p ∈ words.getD k [], p.1 < 256 ∧ p.2 < 256 := by
      by_cases hk : k < words.length
      · have hmem : words.getD k [] ∈ words := by
          rw [List.getD_eq_getElem _ _ hk]
          exact List.getElem_mem hk
        exact ⟨hw _ hmem, hlt _ hmem⟩
      · rw [List.getD_eq_default _ _ (not_lt.1 hk)]
        exact ⟨by simp [welt], by simp⟩
    have hconj := M.mul_mem (M.mul_mem hpsw.1 hc) (M.inv_mem hpsw.1)
    rw [conj_eg] at hconj
    have e : actPair (actG ((welt (words.getD k []) : Om8) : GL ι8 (ZMod 2))) c =
        actPair (wact (words.getD k [])) c := by
      unfold actPair
      rw [actG_welt _ hpsw.2 (Nat.mod_lt _ (by norm_num)),
        actG_welt _ hpsw.2 (Nat.mod_lt _ (by norm_num))]
    rw [e] at hconj
    show eg (canon _) ∈ M
    rw [eg_canon]
    exact hconj
  · intro c hc
    rw [Nat.one_shiftLeft, Nat.testBit_two_pow] at hc
    have : start = c := by simpa using hc
    rw [← this]
    exact hstart

theorem om8_top_of_eichler (M : Subgroup Om8)
    (h : ∀ u w : V8, (⟨eichGL u w, eichGL_mem u w⟩ : Om8) ∈ M) : M = ⊤ := by
  rw [eq_top_iff]
  intro g _
  set N : Subgroup (V8 ≃ₗ[ZMod 2] V8) :=
    (M.map Om8.subtype).map (toLinEquiv ι8 (ZMod 2)).toMonoidHom with hN
  have hle : elementaryGroup (quadPlus 4 (ZMod 2)) ≤ N := by
    apply elementaryGroup_le_of_eichler_mem
    intro u w _ _
    refine Subgroup.mem_map.2 ⟨eichGL u w, Subgroup.mem_map.2 ⟨⟨eichGL u w, eichGL_mem u w⟩,
      h u w, rfl⟩, ?_⟩
    unfold eichGL
    exact MulEquiv.apply_symm_apply _ _
  obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.1 (hle ((mem_Om8_iff g.1).1 g.2))
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hx
  have : m = g := Subtype.ext ((toLinEquiv ι8 (ZMod 2)).injective hxg)
  rwa [← this]


theorem quad_zero_iff (v : V8) : quadPlus 4 (ZMod 2) v = 0 ↔ Qb (bc v) = 0 := by
  rw [quad_quadPlus, cast2_eq_zero_iff]
  have := Qb_lt (bc v)
  omega

theorem polar_zero_iff (v w : V8) : polar (quadPlus 4 (ZMod 2)) v w = 0 ↔ Bb (bc v) (bc w) = 0 := by
  rw [polar_bc, cast2_eq_zero_iff]
  have := Bb_lt (bc v) (bc w)
  omega

theorem quad_one_iff (v : V8) : quadPlus 4 (ZMod 2) v = 1 ↔ Qb (bc v) = 1 := by
  have h2 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  have := Qb_lt (bc v)
  have h0 := quad_zero_iff v
  rcases h2 (quadPlus 4 (ZMod 2) v) with h | h
  · rw [h]
    constructor
    · intro h'
      exact absurd h' (by decide)
    · intro h'
      have := h0.1 h
      omega
  · rw [h]
    constructor
    · intro _
      by_contra hne
      have : Qb (bc v) = 0 := by omega
      have := h0.2 this
      rw [h] at this
      exact absurd this (by decide)
    · intro _
      rfl

@[expose] def EAllOk (mask : ℕ) (zl : List ℕ) : Prop :=
  (∀ u < 256, Qb u = 0 → u ≠ 0 → ∀ w < 256, Bb u w = 0 → Qb w = 1 →
    mask.testBit (canon (u + 256 * w)) = true) ∧
  (∀ u < 256, Qb u = 0 → u ≠ 0 → ∀ w < 256, Bb u w = 0 → Qb w = 0 →
    ∃ z ∈ zl, z < 256 ∧ Bb u z = 0 ∧ Qb z = 1 ∧ Bb w z = 0)

set_option synthInstance.maxSize 20000 in
instance (mask : ℕ) (zl : List ℕ) : Decidable (EAllOk mask zl) := by
  unfold EAllOk
  infer_instance

@[expose] def eAllCheck (mask : ℕ) (zl : List ℕ) : Bool :=
  (List.range 256).all (fun u =>
    !(Qb u == 0) || (u == 0) ||
    (List.range 256).all (fun w => !(Qb w == 1) || !(Bb u w == 0) ||
      mask.testBit (canon (u + 256 * w)))) &&
  (List.range 256).all (fun u =>
    !(Qb u == 0) || (u == 0) ||
    (List.range 256).all (fun w => !(Qb w == 0) || !(Bb u w == 0) ||
      zl.any (fun z => decide (z < 256) && Bb u z == 0 && Qb z == 1 && Bb w z == 0)))

theorem eAllOk_of_check {mask : ℕ} {zl : List ℕ} (h : eAllCheck mask zl = true) :
    EAllOk mask zl := by
  unfold eAllCheck at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', beq_eq_false_iff_ne, beq_iff_eq, ne_eq, List.any_eq_true,
    Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun u hu hq hu0 w hw hb hq1 => ?_, fun u hu hq hu0 w hw hb hq0 => ?_⟩
  · rcases h1 u hu with (h | h) | h
    · exact absurd hq h
    · exact absurd h hu0
    · rcases h w hw with (h | h) | h
      · exact absurd hq1 h
      · exact absurd hb h
      · exact h
  · rcases h2 u hu with (h | h) | h
    · exact absurd hq h
    · exact absurd h hu0
    · rcases h w hw with (h | h) | h
      · exact absurd hq0 h
      · exact absurd hb h
      · obtain ⟨z, hz, ⟨⟨hz1, hz2⟩, hz3⟩, hz4⟩ := h
        exact ⟨z, hz, hz1, hz2, hz3, hz4⟩

theorem all_eichler_mem (M : Subgroup Om8) {mask : ℕ} {zl : List ℕ}
    (hM : ∀ c, mask.testBit c = true → eg c ∈ M) (hok : EAllOk mask zl) :
    ∀ u w : V8, (⟨eichGL u w, eichGL_mem u w⟩ : Om8) ∈ M := by
  have type1 : ∀ u w : V8, bc u ≠ 0 → quadPlus 4 (ZMod 2) u = 0 →
      polar (quadPlus 4 (ZMod 2)) u w = 0 → quadPlus 4 (ZMod 2) w = 1 →
      (⟨eichGL u w, eichGL_mem u w⟩ : Om8) ∈ M := by
    intro u w hbc hu hw hq
    have h1 := hok.1 (bc u) (bc_lt u) ((quad_zero_iff u).1 hu) hbc (bc w) (bc_lt w)
      ((polar_zero_iff u w).1 hw) ((quad_one_iff w).1 hq)
    have h2 := hM _ h1
    rw [eg_canon] at h2
    have e : (⟨eichGL u w, eichGL_mem u w⟩ : Om8) = eg (bc u + 256 * bc w) := by
      apply Subtype.ext
      have hu' := bc_lt u
      have hw' := bc_lt w
      have e1 : (bc u + 256 * bc w) % 256 = bc u := by omega
      have e2 : (bc u + 256 * bc w) / 256 % 256 = bc w := by omega
      show eichGL u w = eichGL (bv ((bc u + 256 * bc w) % 256))
        (bv ((bc u + 256 * bc w) / 256 % 256))
      rw [e1, e2, bv_bc, bv_bc]
    rw [e]
    exact h2
  intro u w
  by_cases hu0 : u = 0
  · subst hu0
    have : eichGL (0 : V8) w = 1 := by
      unfold eichGL
      rw [eichler_zero_left, map_one]
    have e : (⟨eichGL 0 w, eichGL_mem 0 w⟩ : Om8) = 1 := Subtype.ext this
    rw [e]
    exact M.one_mem
  have hbc : bc u ≠ 0 := fun h' => hu0 (bc_injective (h'.trans bc_zero.symm))
  by_cases h : quadPlus 4 (ZMod 2) u = 0 ∧ polar (quadPlus 4 (ZMod 2)) u w = 0
  · by_cases hq : quadPlus 4 (ZMod 2) w = 1
    · exact type1 u w hbc h.1 h.2 hq
    · have hq0 : quadPlus 4 (ZMod 2) w = 0 := by
        rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (quadPlus 4 (ZMod 2) w) with h' | h'
        · exact h'
        · exact absurd h' hq
      obtain ⟨z, hz, hz256, hz1, hz2, hz3⟩ := hok.2 (bc u) (bc_lt u) ((quad_zero_iff u).1 h.1)
        hbc (bc w) (bc_lt w) ((polar_zero_iff u w).1 h.2) ((quad_zero_iff w).1 hq0)
      set zv : V8 := bv z with hzvdef
      have hbz : bc zv = z := bc_bv hz256
      have hQz : quadPlus 4 (ZMod 2) zv = 1 := (quad_one_iff zv).2 (by rw [hbz]; exact hz2)
      have hPuz : polar (quadPlus 4 (ZMod 2)) u zv = 0 :=
        (polar_zero_iff u zv).2 (by rw [hbz]; exact hz1)
      have hPwz : polar (quadPlus 4 (ZMod 2)) w zv = 0 :=
        (polar_zero_iff w zv).2 (by rw [hbz]; exact hz3)
      have hQwz : quadPlus 4 (ZMod 2) (w + zv) = 1 := by
        rw [QuadraticMap.map_add (quadPlus 4 (ZMod 2)) w zv, hq0, hQz, hPwz]
        decide
      have hPuwz : polar (quadPlus 4 (ZMod 2)) u (w + zv) = 0 := by
        rw [polar_add_right, h.2, hPuz, add_zero]
      have hprod : eichGL u w = eichGL u (w + zv) * eichGL u zv := by
        unfold eichGL
        rw [← map_mul, eichler_mul hPuwz hPuz, add_assoc, CharTwo.add_self_eq_zero, add_zero]
      have e : (⟨eichGL u w, eichGL_mem u w⟩ : Om8) =
          ⟨eichGL u (w + zv), eichGL_mem u (w + zv)⟩ * ⟨eichGL u zv, eichGL_mem u zv⟩ :=
        Subtype.ext hprod
      rw [e]
      exact M.mul_mem (type1 u _ hbc h.1 hPuwz hQwz) (type1 u _ hbc h.1 hPuz hQz)
  · have : eichGL u w = 1 := by
      unfold eichGL
      rw [eichler_of_not h, map_one]
    rw [show (⟨eichGL u w, eichGL_mem u w⟩ : Om8) = 1 from Subtype.ext this]
    exact M.one_mem

end Instances

end CFSG.AGLEmbedding
