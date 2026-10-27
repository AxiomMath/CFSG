module

public import CFSG.Certificates.Kernel.GGToral.PkSplitWalk

public section

namespace CFSG.KC.GGToral

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.StandardType CFSG.StandardType.StepTwoToralCert

@[expose] noncomputable def six (d0 d1 d2 d3 d4 d5 : ℕ) : ℕ :=
  d0 + ((d1 <<< 16) + ((d2 <<< 32) + ((d3 <<< 48) + ((d4 <<< 64) + (d5 <<< 80)))))

theorem lanes_six {d0 d1 d2 d3 d4 d5 : ℕ} (h0 : d0 < 65536) (h1 : d1 < 65536) (h2 : d2 < 65536)
    (h3 : d3 < 65536) (h4 : d4 < 65536) (h5 : d5 < 65536) :
    lane (six d0 d1 d2 d3 d4 d5) 0 = d0 ∧ lane (six d0 d1 d2 d3 d4 d5) 1 = d1 ∧
      lane (six d0 d1 d2 d3 d4 d5) 2 = d2 ∧ lane (six d0 d1 d2 d3 d4 d5) 3 = d3 ∧
      lane (six d0 d1 d2 d3 d4 d5) 4 = d4 ∧ lane (six d0 d1 d2 d3 d4 d5) 5 = d5 ∧
      six d0 d1 d2 d3 d4 d5 < 2 ^ 96 := by
  have hv : six d0 d1 d2 d3 d4 d5 = d0 + 65536 * (d1 + 65536 * (d2 + 65536 * (d3 +
      65536 * (d4 + 65536 * d5)))) := by
    unfold six
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
    norm_num
    ring
  rw [hv, lane_eq, lane_eq, lane_eq, lane_eq, lane_eq, lane_eq]
  norm_num
  omega

theorem twPt_eq_six (p x : ℕ) : twPt p x = six (Nat.mod x p) (Nat.mod (Nat.div x p) p)
    (Nat.mod (Nat.div x (Nat.mul p p)) p) (Nat.mod (Nat.div x (Nat.mul p (Nat.mul p p))) p)
    (Nat.mod (Nat.div x (Nat.mul p p)) p) (Nat.mod x p) := rfl

theorem gRev_eq_six (v : ℕ) : gRev v = six (lane v 5) (lane v 3) (lane v 2) (lane v 1) (lane v 4)
    (lane v 0) := rfl

@[expose] noncomputable def twLoop (p N : ℕ) (acc : List ℕ) : List ℕ :=
  Nat.rec (motive := fun _ => List ℕ → List ℕ) (fun acc => acc)
    (fun i ih => fun acc => ih (Bool.rec (motive := fun _ => List ℕ) (twPt p i :: acc) acc
      (Nat.beq i 0))) N acc

theorem twV_eq (p : ℕ) : twV p = twLoop p (Nat.mul p (Nat.mul p (Nat.mul p p))) [] := rfl

theorem twLoop_mono (p : ℕ) : ∀ (N : ℕ) {acc : List ℕ} {x : ℕ}, x ∈ acc → x ∈ twLoop p N acc
  | 0, _, _, h => h
  | N + 1, acc, x, h => by
    change x ∈ twLoop p N (Bool.rec (motive := fun _ => List ℕ) (twPt p N :: acc) acc
      (Nat.beq N 0))
    apply twLoop_mono p N
    cases Nat.beq N 0
    · exact List.mem_cons_of_mem _ h
    · exact h

theorem twLoop_complete (p : ℕ) : ∀ (N : ℕ) (acc : List ℕ) {i : ℕ}, i < N → i ≠ 0 →
    twPt p i ∈ twLoop p N acc
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | N + 1, acc, i, h, h0 => by
    change _ ∈ twLoop p N (Bool.rec (motive := fun _ => List ℕ) (twPt p N :: acc) acc
      (Nat.beq N 0))
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | rfl
    · exact twLoop_complete p N _ h h0
    · apply twLoop_mono
      cases hb : Nat.beq i 0 with
      | true => exact absurd (Nat.eq_of_beq_eq_true hb) h0
      | false => exact List.mem_cons_self

theorem dig_mod {p a y : ℕ} (ha : a < p) : (a + p * y) % p = a := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]

theorem dig_div {p a y : ℕ} (ha : a < p) : (a + p * y) / p = y := by
  have hp : 0 < p := by omega
  rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt ha, zero_add]

theorem dig_lt {p q a y : ℕ} (ha : a < p) (hy : y < q) : a + p * y < p * q := by
  have h1 : p * (y + 1) ≤ p * q := Nat.mul_le_mul_left p (by omega)
  rw [mul_add, mul_one] at h1
  omega

theorem e6Gamma_0 : e6Gamma ⟨0, by decide⟩ = ⟨5, by decide⟩ := by decide

theorem e6Gamma_1 : e6Gamma ⟨1, by decide⟩ = ⟨1, by decide⟩ := by decide

theorem e6Gamma_2 : e6Gamma ⟨2, by decide⟩ = ⟨4, by decide⟩ := by decide

theorem e6Gamma_3 : e6Gamma ⟨3, by decide⟩ = ⟨3, by decide⟩ := by decide

theorem e6Gamma_4 : e6Gamma ⟨4, by decide⟩ = ⟨2, by decide⟩ := by decide

theorem e6Gamma_5 : e6Gamma ⟨5, by decide⟩ = ⟨0, by decide⟩ := by decide

theorem twPt_lanes {p : ℕ} (hp0 : 0 < p) (hp16 : p ≤ 16) (x : ℕ) :
    lane (twPt p x) 0 = x % p ∧ lane (twPt p x) 1 = x / p % p ∧
      lane (twPt p x) 2 = x / (p * p) % p ∧ lane (twPt p x) 3 = x / (p * (p * p)) % p ∧
      lane (twPt p x) 4 = x / (p * p) % p ∧ lane (twPt p x) 5 = x % p ∧ twPt p x < 2 ^ 96 := by
  have hm : ∀ y, y % p < 65536 := fun y => by have := Nat.mod_lt y hp0; omega
  rw [twPt_eq_six]
  exact lanes_six (hm x) (hm (x / p)) (hm (x / (p * p))) (hm (x / (p * (p * p))))
    (hm (x / (p * p))) (hm x)

theorem twPt_digits {p c0 c1 c2 c3 : ℕ} (hp0 : 0 < p) (hp16 : p ≤ 16) (l0 : c0 < p) (l1 : c1 < p)
    (l2 : c2 < p) (l3 : c3 < p) : ∃ x, x < Nat.mul p (Nat.mul p (Nat.mul p p)) ∧
      (x = 0 → c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0) ∧
      lane (twPt p x) 0 = c0 ∧ lane (twPt p x) 1 = c1 ∧ lane (twPt p x) 2 = c2 ∧
      lane (twPt p x) 3 = c3 ∧ lane (twPt p x) 4 = c2 ∧ lane (twPt p x) 5 = c0 ∧
      twPt p x < 2 ^ 96 := by
  obtain ⟨k0, k1, k2, k3, k4, k5, k96⟩ := twPt_lanes hp0 hp16 (c0 + p * (c1 + p * (c2 + p * c3)))
  have d1 : (c0 + p * (c1 + p * (c2 + p * c3))) / p % p = c1 := by rw [dig_div l0, dig_mod l1]
  have d2 : (c0 + p * (c1 + p * (c2 + p * c3))) / (p * p) % p = c2 := by
    rw [← Nat.div_div_eq_div_mul, dig_div l0, dig_div l1, dig_mod l2]
  have d3 : (c0 + p * (c1 + p * (c2 + p * c3))) / (p * (p * p)) % p = c3 := by
    rw [← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, dig_div l0, dig_div l1,
      dig_div l2, Nat.mod_eq_of_lt l3]
  rw [dig_mod l0] at k0 k5
  rw [d1] at k1
  rw [d2] at k2 k4
  rw [d3] at k3
  refine ⟨_, dig_lt l0 (dig_lt l1 (dig_lt l2 l3)), fun h0 => ?_, k0, k1, k2, k3, k4, k5, k96⟩
  have e1 : p * (c1 + p * (c2 + p * c3)) = 0 := by omega
  have e1' := (Nat.mul_eq_zero.mp e1).resolve_left (by omega)
  have e2 : p * (c2 + p * c3) = 0 := by omega
  have e2' := (Nat.mul_eq_zero.mp e2).resolve_left (by omega)
  have e3 : p * c3 = 0 := by omega
  have e3' := (Nat.mul_eq_zero.mp e3).resolve_left (by omega)
  omega

theorem twV_complete {p : ℕ} {H : Hd} (h : tagHdOK .E6 p 1 H = true)
    {b : Fin Tag.E6.rank → ZMod p} (hb : b ∈ fixedSub p e6Gamma) (hb0 : b ≠ 0) :
    ∃ a ∈ twV p, red H a = true ∧ vecZ p Tag.E6.rank a = b := by
  obtain ⟨-, -, hn, hpp, hp3, hp16, -⟩ := tagHdOK_basic h
  have hp0 : 0 < p := by omega
  have : NeZero p := ⟨by omega⟩
  have hfix : ∀ i, b (e6Gamma i) = b i := hb
  have h50 : b ⟨5, by decide⟩ = b ⟨0, by decide⟩ := by
    have := hfix ⟨0, by decide⟩
    rwa [e6Gamma_0] at this
  have h42 : b ⟨4, by decide⟩ = b ⟨2, by decide⟩ := by
    have := hfix ⟨2, by decide⟩
    rwa [e6Gamma_2] at this
  have hcast : ∀ i : Fin Tag.E6.rank, (((b i).val : ℕ) : ZMod p) = b i := fun i =>
    ZMod.natCast_zmod_val _
  obtain ⟨x, hxlt, hx0, k0, k1, k2, k3, k4, k5, k96⟩ := twPt_digits hp0 (by omega)
    (ZMod.val_lt (b ⟨0, by decide⟩)) (ZMod.val_lt (b ⟨1, by decide⟩))
    (ZMod.val_lt (b ⟨2, by decide⟩)) (ZMod.val_lt (b ⟨3, by decide⟩))
  have hx0' : x ≠ 0 := by
    intro h0
    apply hb0
    obtain ⟨e0, e1, e2, e3⟩ := hx0 h0
    have z0 : b ⟨0, by decide⟩ = 0 := (ZMod.val_eq_zero _).mp e0
    have z1 : b ⟨1, by decide⟩ = 0 := (ZMod.val_eq_zero _).mp e1
    have z2 : b ⟨2, by decide⟩ = 0 := (ZMod.val_eq_zero _).mp e2
    have z3 : b ⟨3, by decide⟩ = 0 := (ZMod.val_eq_zero _).mp e3
    funext i
    obtain ⟨i, hi⟩ := i
    change i < 6 at hi
    interval_cases i
    · exact z0
    · exact z1
    · exact z2
    · exact z3
    · exact h42.trans z2
    · exact h50.trans z0
  refine ⟨twPt p x, ?_, ?_, ?_⟩
  · rw [twV_eq]
    exact twLoop_complete p _ [] hxlt hx0'
  · have hlanes : ∀ j < H.n, lane (twPt p x) j < H.p := by
      intro j hj
      rw [hn] at hj
      rw [hpp]
      change j < 6 at hj
      interval_cases j
      · rw [k0]; exact ZMod.val_lt _
      · rw [k1]; exact ZMod.val_lt _
      · rw [k2]; exact ZMod.val_lt _
      · rw [k3]; exact ZMod.val_lt _
      · rw [k4]; exact ZMod.val_lt _
      · rw [k5]; exact ZMod.val_lt _
    unfold red
    rw [Nat.beq_eq, modL_eq_packN]
    rw [packN_congr (g := lane (twPt p x)) fun j hj => Nat.mod_eq_of_lt (hlanes j hj)]
    refine (eq_packN_lane ?_).symm
    rw [hn]
    exact k96
  · funext i
    obtain ⟨i, hi⟩ := i
    change ((lane (twPt p x) i : ℕ) : ZMod p) = _
    change i < 6 at hi
    interval_cases i
    · rw [k0, hcast]
    · rw [k1, hcast]
    · rw [k2, hcast]
    · rw [k3, hcast]
    · rw [k4, hcast]
      exact h42.symm
    · rw [k5, hcast]
      exact h50.symm

theorem tagHdOK_gam {τ : Tag} {p : ℕ} {H : Hd} (h : tagHdOK τ p 1 H = true) :
    ∀ r < H.np, lane H.gam r < H.np ∧ row H.rrev (lane H.gam r) = gRev (row H.rrev r) := by
  intro r hr
  unfold tagHdOK at h
  simp only [andB_eq_true, orB_eq_true] at h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hg⟩ := h
  rcases hg with h0 | ⟨-, hall⟩
  · exact absurd h0 (by decide)
  have hrr := allN_eq_true.mp hall r hr
  rw [andB_eq_true] at hrr
  exact ⟨Nat.blt_eq.mp hrr.1, Nat.eq_of_beq_eq_true hrr.2⟩

theorem rowZ_gam {p : ℕ} {H : Hd} (h : tagHdOK .E6 p 1 H = true) {r : ℕ} (hr : r < H.np) :
    lane H.gam r < H.np ∧ rowZ .E6 H (lane H.gam r) = latPerm e6Gamma (rowZ .E6 H r) := by
  obtain ⟨-, -, hn, -⟩ := tagHdOK_basic h
  obtain ⟨h1, h2⟩ := tagHdOK_gam h r hr
  refine ⟨h1, ?_⟩
  obtain ⟨g0, g1, g2, g3, g4, g5, -⟩ := lanes_six (lane_lt (row H.rrev r) 5)
    (lane_lt (row H.rrev r) 3) (lane_lt (row H.rrev r) 2) (lane_lt (row H.rrev r) 1)
    (lane_lt (row H.rrev r) 4) (lane_lt (row H.rrev r) 0)
  rw [gRev_eq_six] at h2
  have hc : ∀ j : ℕ, rtC H (lane H.gam r) j = lane (six (lane (row H.rrev r) 5)
      (lane (row H.rrev r) 3) (lane (row H.rrev r) 2) (lane (row H.rrev r) 1)
      (lane (row H.rrev r) 4) (lane (row H.rrev r) 0)) (Nat.sub 5 j) := by
    intro j
    unfold rtC
    rw [h2, hn]
    rfl
  have hc' : ∀ j : ℕ, rtC H r j = lane (row H.rrev r) (Nat.sub 5 j) := by
    intro j
    unfold rtC
    rw [hn]
    rfl
  have key : ∀ j : Fin Tag.E6.rank, rtC H (lane H.gam r) j = rtC H r (e6Gamma j) := by
    intro j
    rw [hc, hc']
    obtain ⟨j, hj⟩ := j
    change j < 6 at hj
    interval_cases j
    · rw [e6Gamma_0]
      exact g5
    · rw [e6Gamma_1]
      exact g4
    · rw [e6Gamma_2]
      exact g3
    · rw [e6Gamma_3]
      exact g2
    · rw [e6Gamma_4]
      exact g1
    · rw [e6Gamma_5]
      exact g0
  funext j
  change ((rtC H (lane H.gam r) j : ℕ) : ℤ) = ((rtC H r (e6Gamma.symm j) : ℕ) : ℤ)
  rw [e6Gamma_symm, key]

theorem e6Gamma_e6Gamma (i : Fin Tag.E6.rank) : e6Gamma (e6Gamma i) = i := by
  revert i
  decide

theorem symmetrizedCartan_e6Gamma (i j : Fin Tag.E6.rank) :
    Tag.E6.symmetrizedCartan (e6Gamma i) (e6Gamma j) = Tag.E6.symmetrizedCartan i j := by
  have hτ : tgOK Tag.E6 = true := by decide
  have hd : ∀ i : Fin Tag.E6.rank, lane (tgDiag Tag.E6) (e6Gamma i) = lane (tgDiag Tag.E6) i := by
    decide
  rw [symmetrizedCartan_eq_lit hτ, symmetrizedCartan_eq_lit hτ, tcW_e6Gamma_cartan, hd]

theorem latGram_e6Gamma (α β : Fin Tag.E6.rank → ℤ) :
    latGram Tag.E6.symmetrizedCartan (latPerm e6Gamma α) (latPerm e6Gamma β) =
      latGram Tag.E6.symmetrizedCartan α β := by
  unfold latGram latPerm
  refine Fintype.sum_equiv e6Gamma.symm _ _ fun i => ?_
  refine Fintype.sum_equiv e6Gamma.symm _ _ fun j => ?_
  rw [← symmetrizedCartan_e6Gamma (e6Gamma.symm i) (e6Gamma.symm j), e6Gamma_symm, e6Gamma_symm,
    e6Gamma_e6Gamma, e6Gamma_e6Gamma]

theorem latPerm_neg {N : ℕ} (π : Equiv.Perm (Fin N)) (α : Fin N → ℤ) :
    latPerm π (-α) = -latPerm π α := rfl

theorem latChar_e6Gamma {p : ℕ} {b : Fin Tag.E6.rank → ZMod p} (hb : b ∈ fixedSub p e6Gamma)
    (α : Fin Tag.E6.rank → ℤ) : latChar p b (latPerm e6Gamma α) = latChar p b α := by
  have hfix : ∀ i, b (e6Gamma i) = b i := hb
  unfold latChar latPerm
  refine Fintype.sum_equiv e6Gamma.symm _ _ fun i => ?_
  rw [e6Gamma_symm, hfix]

section Comp


theorem latLinked_e6Gamma {p : ℕ} {b : Fin Tag.E6.rank → ZMod p} (hb : b ∈ fixedSub p e6Gamma)
    (hR : ∀ α, IsRoot .E6 α → IsRoot .E6 (latPerm e6Gamma α)) {x y : Fin Tag.E6.rank → ℤ}
    (h : latLinked Tag.E6.symmetrizedCartan (latPhi {α | IsRoot .E6 α} p b) x y) :
    latLinked Tag.E6.symmetrizedCartan (latPhi {α | IsRoot .E6 α} p b) (latPerm e6Gamma x)
      (latPerm e6Gamma y) := by
  induction h with
  | rel x y h =>
    refine Relation.EqvGen.rel _ _ ⟨⟨hR _ h.1.1, ?_⟩, ⟨hR _ h.2.1.1, ?_⟩, ?_⟩
    · rw [latChar_e6Gamma hb]
      exact h.1.2
    · rw [latChar_e6Gamma hb]
      exact h.2.1.2
    · rw [latGram_e6Gamma]
      exact h.2.2
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

theorem latLinked_e6Gamma_iff {p : ℕ} {b : Fin Tag.E6.rank → ZMod p}
    (hb : b ∈ fixedSub p e6Gamma) (hR : ∀ α, IsRoot .E6 α → IsRoot .E6 (latPerm e6Gamma α))
    (x y : Fin Tag.E6.rank → ℤ) :
    latLinked Tag.E6.symmetrizedCartan (latPhi {α | IsRoot .E6 α} p b) (latPerm e6Gamma x) y ↔
      latLinked Tag.E6.symmetrizedCartan (latPhi {α | IsRoot .E6 α} p b) x
        (latPerm e6Gamma y) := by
  constructor
  · intro h
    have := latLinked_e6Gamma hb hR h
    rwa [latPerm_e6Gamma_involutive] at this
  · intro h
    have := latLinked_e6Gamma hb hR h
    rwa [latPerm_e6Gamma_involutive] at this

end Comp

theorem rootsOf_append (τ : Tag) (H : Hd) (l1 l2 : List ℕ) :
    rootsOf τ H (l1 ++ l2) = rootsOf τ H l1 ∪ rootsOf τ H l2 := by
  ext β
  simp only [rootsOf, Set.mem_setOf_eq, Set.mem_union, List.mem_append]
  constructor
  · rintro ⟨r, hr | hr, h⟩
    · exact Or.inl ⟨r, hr, h⟩
    · exact Or.inr ⟨r, hr, h⟩
  · rintro (⟨r, hr, h⟩ | ⟨r, hr, h⟩)
    · exact ⟨r, Or.inl hr, h⟩
    · exact ⟨r, Or.inr hr, h⟩

theorem mem_rootsOf_map_gam {p : ℕ} {H : Hd} (h : tagHdOK .E6 p 1 H = true) {mem : List ℕ}
    (hmem : ∀ r ∈ mem, r < H.np) (β : Fin Tag.E6.rank → ℤ) :
    β ∈ rootsOf .E6 H (mem.map (lane H.gam)) ↔ latPerm e6Gamma β ∈ rootsOf .E6 H mem := by
  have key : ∀ r ∈ mem, ∀ s : Fin Tag.E6.rank → ℤ, (β = s ↔ latPerm e6Gamma β =
      latPerm e6Gamma s) := fun r _ s => ⟨fun h => by rw [h], fun h => by
    rw [← latPerm_e6Gamma_involutive β, h, latPerm_e6Gamma_involutive]⟩
  simp only [rootsOf, Set.mem_setOf_eq, List.mem_map]
  constructor
  · rintro ⟨_, ⟨r, hr, rfl⟩, hβ⟩
    refine ⟨r, hr, ?_⟩
    rw [(rowZ_gam h (hmem r hr)).2] at hβ
    rcases hβ with hβ | hβ
    · exact Or.inl (by rw [hβ, latPerm_e6Gamma_involutive])
    · exact Or.inr (by rw [hβ, latPerm_neg, latPerm_e6Gamma_involutive])
  · rintro ⟨r, hr, hβ⟩
    refine ⟨lane H.gam r, ⟨r, hr, rfl⟩, ?_⟩
    rw [(rowZ_gam h (hmem r hr)).2]
    rcases hβ with hβ | hβ
    · exact Or.inl (by rw [← hβ, latPerm_e6Gamma_involutive])
    · exact Or.inr (by rw [← latPerm_neg, ← hβ, latPerm_e6Gamma_involutive])

theorem trace_mem {p : ℕ} {H : Hd} (h : tagHdOK .E6 p 1 H = true) {r : ℕ} (hr : r < H.np)
    {O : Set (Fin Tag.E6.rank → ℤ)} (hO1 : rowZ .E6 H r ∈ O)
    (hO2 : rowZ .E6 H (lane H.gam r) ∈ O) :
    vecZ p Tag.E6.rank (row H.cor r) + vecZ p Tag.E6.rank (row H.cor (lane H.gam r)) ∈
      (fixedSub p e6Gamma : Set (Fin Tag.E6.rank → ZMod p)) ∩
        latEigenCoroot p Tag.E6.symmetrizedCartan e6Gamma O := by
  obtain ⟨hg, hgr⟩ := rowZ_gam h hr
  set c := latCorootZ Tag.E6.symmetrizedCartan (rowZ .E6 H r) with hc
  have hcg : latCorootZ Tag.E6.symmetrizedCartan (rowZ .E6 H (lane H.gam r)) =
      fun i => c (e6Gamma i) := by
    rw [hgr, hc]
    funext i
    simp only [latCorootZ]
    have h1 : (Pi.single i (1 : ℤ) : Fin Tag.E6.rank → ℤ) =
        latPerm e6Gamma (Pi.single (e6Gamma i) 1) := by
      funext j
      simp only [latPerm, Pi.single_apply, e6Gamma_symm]
      congr 1
      exact propext ⟨fun h => by rw [h], fun h => by
        rw [← e6Gamma_e6Gamma j, h, e6Gamma_e6Gamma]⟩
    rw [h1, latGram_e6Gamma, latGram_e6Gamma]
  have hv : vecZ p Tag.E6.rank (row H.cor r) + vecZ p Tag.E6.rank (row H.cor (lane H.gam r)) =
      fun i => (((c + fun i => c (e6Gamma i)) i : ℤ) : ZMod p) := by
    rw [vecZ_cor h hr, vecZ_cor h hg, hcg]
    funext i
    simp [hc]
  rw [hv]
  refine ⟨fun i => ?_, c + fun i => c (e6Gamma i), Submodule.add_mem _
    (Submodule.subset_span ⟨_, hO1, rfl⟩) (Submodule.subset_span ⟨_, hO2, hcg⟩), fun i => rfl,
    0, Submodule.zero_mem _, ?_⟩
  · simp only [Pi.add_apply, e6Gamma_e6Gamma]
    push_cast
    ring
  · funext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_zero, Pi.zero_apply, e6Gamma_symm,
      e6Gamma_e6Gamma]
    ring

section Vec

variable {τ : Tag} {p mode : ℕ} {H : Hd}

theorem vecZ_modL_lin3 (h : tagHdOK τ p mode H = true) {x y z c : ℕ} (hx : red H x = true)
    (hy : red H y = true) (hz : red H z = true) (hc : c < 16) :
    vecZ p τ.rank (modL H.p H.n (x + c * (y + z))) =
      vecZ p τ.rank x + (c : ZMod p) • (vecZ p τ.rank y + vecZ p τ.rank z) := by
  obtain ⟨-, -, hn, hpp, hp3, hp16, -⟩ := tagHdOK_basic h
  have hpos : 0 < H.p := by omega
  obtain ⟨hxl, hxv⟩ := red_spec hpos hx
  obtain ⟨hyl, hyv⟩ := red_spec hpos hy
  obtain ⟨hzl, hzv⟩ := red_spec hpos hz
  have hpk : x + c * (y + z) = packN H.n (fun j => lane x j + c * (lane y j + lane z j)) := by
    conv_lhs => rw [eq_packN_lane hxl, eq_packN_lane hyl, eq_packN_lane hzl]
    rw [packN_eq_sum, packN_eq_sum, packN_eq_sum, packN_eq_sum, ← Finset.sum_add_distrib,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hb : ∀ j < τ.rank, lane x j + c * (lane y j + lane z j) < 65536 := fun j hj => by
    have h1 := hxv j (by omega)
    have h2 := hyv j (by omega)
    have h3 := hzv j (by omega)
    have h4 : c * (lane y j + lane z j) ≤ 16 * 32 := Nat.mul_le_mul (by omega) (by omega)
    omega
  rw [hpk, hpp, hn]
  funext j
  rw [vecZ_modL_packN hb j]
  simp only [vecZ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

end Vec

theorem combo_spec_twist {p : ℕ} {H : Hd} (h : tagHdOK .E6 p 1 H = true) {a : ℕ}
    (ha : red H a = true) {mem : List ℕ} (hmem : ∀ r ∈ mem, r < H.np)
    {T : Submodule (ZMod p) (Fin Tag.E6.rank → ZMod p)} (hTa : vecZ p Tag.E6.rank a ∈ T)
    (hTc : ∀ r ∈ mem, vecZ p Tag.E6.rank (row H.cor r) +
      vecZ p Tag.E6.rank (row H.cor (lane H.gam r)) ∈ T) :
    ∀ ps, pairsOK H mem ps = true →
      red H (combo H a ps) = true ∧ vecZ p Tag.E6.rank (combo H a ps) ∈ T := by
  obtain ⟨-, hm, -, hpp, hp3, hp16, -⟩ := tagHdOK_basic h
  have hpos : 0 < H.p := by omega
  have htw : tw H = true := by
    rw [tw, hm]
    rfl
  intro ps
  induction ps with
  | nil =>
    refine fun _ => ⟨red_zero H hpos, ?_⟩
    change vecZ p Tag.E6.rank 0 ∈ T
    rw [vecZ_zero]
    exact T.zero_mem
  | cons gc ps ih =>
    intro hps
    have hps' : andB (genValid mem (gc / 256)) (andB (Nat.blt (gc % 256) H.p)
      (pairsOK H mem ps)) = true := hps
    simp only [andB_eq_true, Nat.blt_eq] at hps'
    obtain ⟨hg, hc, hps⟩ := hps'
    obtain ⟨hr, hm⟩ := ih hps
    have e : combo H a (gc :: ps) =
        modL H.p H.n (combo H a ps + (gc % 256) * genOf H a (gc / 256)) := rfl
    refine ⟨by rw [e]; exact red_modL hpos (by omega) _, ?_⟩
    rw [e]
    cases hg0 : Nat.beq (gc / 256) 0
    · have hm' := (genValid_spec hg).resolve_left (Nat.ne_of_beq_eq_false hg0)
      have hgen : genOf H a (gc / 256) =
          row H.cor (gc / 256 - 1) + row H.cor (lane H.gam (gc / 256 - 1)) := by
        unfold genOf
        rw [hg0, htw]
        rfl
      rw [hgen, vecZ_modL_lin3 h hr (red_cor h (hmem _ hm'))
        (red_cor h (rowZ_gam h (hmem _ hm')).1) (by omega)]
      exact T.add_mem hm (T.smul_mem _ (hTc _ hm'))
    · have hgen : genOf H a (gc / 256) = a := by
        unfold genOf
        rw [hg0]
      rw [hgen, ← one_mul (combo H a ps), vecZ_modL_lin h hr ha (by norm_num) (by omega)]
      exact T.add_mem (T.smul_mem _ hm) (T.smul_mem _ hTa)

theorem finrank_fixedSub_le {p : ℕ} [Fact p.Prime] :
    Module.finrank (ZMod p) (fixedSub p e6Gamma) ≤ 4 := by
  have h46 : 4 ≤ Tag.E6.rank := by decide
  have hinj : Function.Injective ((LinearMap.funLeft (ZMod p) (ZMod p)
      (Fin.castLE h46 : Fin 4 → Fin Tag.E6.rank)).comp (fixedSub p e6Gamma).subtype) := by
    rintro ⟨g, hg⟩ ⟨g', hg'⟩ hL
    have hfix : ∀ i, g (e6Gamma i) = g i := hg
    have hfix' : ∀ i, g' (e6Gamma i) = g' i := hg'
    have h0 : ∀ i : Fin 4, g (Fin.castLE h46 i) = g' (Fin.castLE h46 i) := fun i =>
      congrFun hL i
    have h50 := hfix ⟨0, by decide⟩
    have h42 := hfix ⟨2, by decide⟩
    have h50' := hfix' ⟨0, by decide⟩
    have h42' := hfix' ⟨2, by decide⟩
    rw [e6Gamma_0] at h50 h50'
    rw [e6Gamma_2] at h42 h42'
    apply Subtype.ext
    funext i
    obtain ⟨i, hi⟩ := i
    change i < 6 at hi
    change g _ = g' _
    interval_cases i
    · exact h0 0
    · exact h0 1
    · exact h0 2
    · exact h0 3
    · rw [h42, h42']
      exact h0 2
    · rw [h50, h50']
      exact h0 0
  have := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_fin_fun] at this

theorem allKilled_spec_twist {H : Hd} (htw : tw H = true) {v : ℕ} :
    ∀ {mem : List ℕ}, allKilled H mem v = true →
      ∀ r ∈ mem, killed H r v = true ∧ killed H (lane H.gam r) v = true
  | [], _, r, hr => absurd hr (by simp)
  | a :: mem, h, r, hr => by
    change andB (killed H a v) (andB (orB (notB (tw H)) (killed H (lane H.gam a) v))
      (allKilled H mem v)) = true at h
    rw [htw] at h
    simp only [andB_eq_true] at h
    rcases List.mem_cons.mp hr with rfl | hr
    · exact ⟨h.1, h.2.1⟩
    · exact allKilled_spec_twist htw h.2.2 r hr

section Kinds

variable {p : ℕ} {H : Hd}

theorem kind0_twist (hp : p.Prime) (h : tagHdOK .E6 p 1 H = true) {mem : List ℕ}
    (hmem : ∀ r ∈ mem, r < H.np) (h7 : ∀ r < H.np, ∀ j < H.n, rtC H r j ≤ 7)
    {v1 q1 v2 q2 v3 q3 : ℕ} (hk : kerOK H mem v1 q1 v2 q2 v3 q3 = true) :
    3 ≤ Module.finrank (ZMod p)
      ↥(fixedSub p e6Gamma ⊓ annSub p (rootsOf .E6 H (mem ++ mem.map (lane H.gam)))) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hm, hn, -⟩ := tagHdOK_basic h
  have htw : tw H = true := by
    rw [tw, hm]
    rfl
  unfold kerOK kerVec at hk
  simp only [andB_eq_true, notB_eq_true, Nat.blt_eq] at hk
  obtain ⟨⟨hr1, hv1, hk1, hq1, hz1⟩, ⟨hr2, hv2, hk2, hq2, hz2⟩, ⟨hr3, hv3, hk3, hq3, hz3⟩, h21, h31,
    h32⟩ := hk
  have hann : ∀ v, red H v = true → inV H v = true → allKilled H mem v = true →
      vecZ p Tag.E6.rank v ∈ (fixedSub p e6Gamma ⊓ annSub p (rootsOf .E6 H
        (mem ++ mem.map (lane H.gam))) : Submodule (ZMod p) (Fin Tag.E6.rank → ZMod p)) := by
    intro v hv hvV hkv
    refine ⟨(inV_iff_twist h hv).mp hvV, fun β hβ => ?_⟩
    obtain ⟨r, hr, hβ⟩ := hβ
    have hz : latChar p (vecZ p Tag.E6.rank v) (rowZ .E6 H r) = 0 := by
      rcases List.mem_append.mp hr with hr | hr
      · exact (killed_iff h (hmem r hr) (h7 r (hmem r hr)) hv).mp
          (allKilled_spec_twist htw hkv r hr).1
      · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
        have hg := (rowZ_gam h (hmem s hs)).1
        exact (killed_iff h hg (h7 _ hg) hv).mp (allKilled_spec_twist htw hkv s hs).2
    rcases hβ with rfl | rfl
    · exact hz
    · rw [latChar_neg, hz]
      exact neg_zero
  have hne : ∀ {v q : ℕ} (hq : q < H.n), zL H v q = false →
      vecZ p Tag.E6.rank v ⟨q, by omega⟩ ≠ 0 :=
    fun hq hz h0 => Bool.eq_false_iff.mp hz ((vecZ_apply_eq_zero h _ _).mp h0)
  exact three_le_finrank_of_tri (hne hq1 hz1) (hne hq2 hz2) (hne hq3 hz3)
    ((vecZ_apply_eq_zero h _ ⟨q1, by omega⟩).mpr h21)
    ((vecZ_apply_eq_zero h _ ⟨q1, by omega⟩).mpr h31)
    ((vecZ_apply_eq_zero h _ ⟨q2, by omega⟩).mpr h32) (hann _ hr1 hv1 hk1)
    (hann _ hr2 hv2 hk2) (hann _ hr3 hv3 hk3)

@[expose] def spanT (p : ℕ) (H : Hd) (a : ℕ) (mem : List ℕ) :
    Submodule (ZMod p) (Fin Tag.E6.rank → ZMod p) :=
  Submodule.span (ZMod p) (insert (vecZ p Tag.E6.rank a)
    ((fixedSub p e6Gamma : Set (Fin Tag.E6.rank → ZMod p)) ∩
      latEigenCoroot p Tag.E6.symmetrizedCartan e6Gamma
        (rootsOf .E6 H (mem ++ mem.map (lane H.gam)))))

theorem combo_mem_spanT (h : tagHdOK .E6 p 1 H = true) {a : ℕ} (ha : red H a = true)
    {mem : List ℕ} (hmem : ∀ r ∈ mem, r < H.np) (ps : List ℕ) (hps : pairsOK H mem ps = true) :
    red H (combo H a ps) = true ∧ vecZ p Tag.E6.rank (combo H a ps) ∈ spanT p H a mem :=
  combo_spec_twist h ha hmem (Submodule.subset_span (Set.mem_insert _ _))
    (fun r hr => Submodule.subset_span (Set.mem_insert_of_mem _ (trace_mem h (hmem r hr)
      (O := rootsOf .E6 H (mem ++ mem.map (lane H.gam)))
      ⟨r, List.mem_append_left _ hr, Or.inl rfl⟩
      ⟨lane H.gam r, List.mem_append_right _ (List.mem_map_of_mem hr), Or.inl rfl⟩))) ps hps

theorem spanT_le {a : ℕ} {mem : List ℕ} (ha : vecZ p Tag.E6.rank a ∈ fixedSub p e6Gamma) :
    spanT p H a mem ≤ fixedSub p e6Gamma := by
  refine Submodule.span_le.mpr ?_
  rintro x (rfl | ⟨hx, -⟩)
  · exact ha
  · exact hx

theorem kind1_twist (hp : p.Prime) (h : tagHdOK .E6 p 1 H = true) {a : ℕ} (ha : red H a = true)
    (haV : vecZ p Tag.E6.rank a ∈ fixedSub p e6Gamma)
    {mem : List ℕ} (hmem : ∀ r ∈ mem, r < H.np) {R : List (ℕ × ℕ × List ℕ)}
    (hR : RowsOK H a mem [] R) (hlen : dimV H ≤ R.length + 1) :
    ∃ S : Submodule (ZMod p) (Fin Tag.E6.rank → ZMod p), S ≤ fixedSub p e6Gamma ∧
      S ≤ spanT p H a mem ∧
      Module.finrank (ZMod p) (fixedSub p e6Gamma) ≤ Module.finrank (ZMod p) S + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hm, hn, -⟩ := tagHdOK_basic h
  have htw : tw H = true := by
    rw [tw, hm]
    rfl
  obtain ⟨hR1, -, hR3⟩ := rowsOK_tri hR
  have hmemR : ∀ i : Fin R.length, R.getD i (0, 0, []) ∈ R := fun i => by
    rw [List.getD_eq_getElem _ _ i.2]
    exact List.getElem_mem i.2
  let v : Fin R.length → Fin Tag.E6.rank → ZMod p := fun i =>
    vecZ p Tag.E6.rank (R.getD i (0, 0, [])).1
  let c : Fin R.length → Fin Tag.E6.rank := fun i =>
    ⟨(R.getD i (0, 0, [])).2.1, by have := (hR1 _ (hmemR i)).2.2.1; omega⟩
  have hS : Submodule.span (ZMod p) (Set.range v) ≤ spanT p H a mem := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    obtain ⟨h1, h2, -, -⟩ := hR1 _ (hmemR i)
    change vecZ p Tag.E6.rank (R.getD i (0, 0, [])).1 ∈ _
    rw [h1]
    exact (combo_mem_spanT h ha hmem _ h2).2
  refine ⟨Submodule.span (ZMod p) (Set.range v), hS.trans (spanT_le haV), hS, ?_⟩
  have hli := card_le_finrank_of_tri v c
    (fun j h0 => Bool.eq_false_iff.mp (hR1 _ (hmemR j)).2.2.2
      ((vecZ_apply_eq_zero h _ _).mp h0))
    (fun i j hij => (vecZ_apply_eq_zero h _ _).mpr (hR3 i j hij j.2))
    (Submodule.span (ZMod p) (Set.range v)) (fun i => Submodule.subset_span ⟨i, rfl⟩)
  have hd : dimV H = 4 := by
    unfold dimV
    rw [htw]
  have := finrank_fixedSub_le (p := p)
  omega

end Kinds

section LM


@[expose] noncomputable def twMon : Submonoid (WeylGroup Tag.E6) :=
  Submonoid.closure (Set.range twElt)

theorem twWordElt_mem : ∀ w : List ℕ, twWordElt w ∈ twMon
  | [] => Submonoid.one_mem _
  | g :: w => Submonoid.mul_mem _ (twWordElt_mem w) (Submonoid.subset_closure ⟨g, rfl⟩)

theorem commutesPi_twMon {u : WeylGroup Tag.E6} (hu : u ∈ twMon) : CommutesPi e6Gamma u := by
  induction hu using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    exact commutesPi_twElt g
  | one => exact commutesPi_one e6Gamma
  | mul x y _ _ hx hy => exact commutesPi_mul hx hy

theorem closed_twMon {p : ℕ} {M : Set (Fin Tag.E6.rank → ZMod p)}
    (hM : ∀ g, ∀ x ∈ M, cowAct (twElt g) x ∈ M) {u : WeylGroup Tag.E6} (hu : u ∈ twMon) :
    ∀ x ∈ M, cowAct u x ∈ M := by
  induction hu using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    exact hM g
  | one =>
    intro x hx
    rw [cowAct_one]
    exact hx
  | mul x y _ _ hx hy =>
    intro z hz
    rw [cowAct_mul]
    exact hx _ (hy z hz)

theorem mem_of_cowAct_mem {τ : Tag} {p : ℕ} {M : Set (Fin τ.rank → ZMod p)} (hM : M.Finite)
    {u : WeylGroup τ} (hu : ∀ x ∈ M, cowAct u x ∈ M) {t : Fin τ.rank → ZMod p}
    (ht : cowAct u t ∈ M) : t ∈ M := by
  have hinj : Function.Injective (cowAct (p := p) u) := fun x y hxy => by
    rw [← cowAct_inv_cowAct u x, hxy, cowAct_inv_cowAct]
  have hbij := (hM.injOn_iff_bijOn_of_mapsTo (fun x hx => hu x hx)).mp hinj.injOn
  obtain ⟨m, hm, hmt⟩ := hbij.surjOn ht
  rw [← hinj hmt]
  exact hm

theorem lm_planeFree_twist {p : ℕ} {H : Hd} (h : tagHdOK .E6 p 1 H = true) {mask : ℕ}
    (hlm : LMFacts H mask) :
    ∃ ents : List ℕ, (∀ x, red H x = true → (inM H mask x = true ↔ x ∈ ents)) ∧
      (∀ g, ∀ x ∈ vset .E6 p ents, cowAct (twElt g) x ∈ vset .E6 p ents) ∧
      ∃ R, PlaneFree e6Gamma (vset .E6 p ents) R := by
  obtain ⟨-, hm, hn, hpp, hp3, hp16, -⟩ := tagHdOK_basic h
  have hpos : 0 < H.p := by omega
  have hp16' : H.p ≤ 65536 := by omega
  have htw : tw H = true := by
    rw [tw, hm]
    rfl
  obtain ⟨reps, ents, ⟨hmask, hok, hreps, hch⟩, hcl, hnp⟩ := hlm
  have hred : ∀ e ∈ ents, red H e = true := fun e he => ((vecOK_iff _ _).mp (hok e he)).1
  have hin : ∀ x, red H x = true → (inM H mask x = true ↔ x ∈ ents) := fun x hx => by
    rw [hmask]
    exact ⟨mem_of_inM_maskL hpos hred hx, inM_maskL_of_mem H⟩
  have hclose : ∀ e ∈ ents, ∀ g < ngens H, inM H mask (letter H g e) = true := by
    clear hreps hch hnp hok hred hin hmask
    induction ents with
    | nil => exact fun e he => absurd he (by simp)
    | cons v ents ih =>
      intro e he
      obtain ⟨h1, h2⟩ := (andB_eq_true _ _).mp hcl
      rcases List.mem_cons.mp he with rfl | he
      · exact allN_eq_true.mp h1
      · exact ih h2 e he
  have hng : ngens H = 4 := by
    unfold ngens
    rw [htw]
  have hlet : ∀ g, ∀ x ∈ vset .E6 p ents, cowAct (twElt g) x ∈ vset .E6 p ents := by
    rintro g _ ⟨e, he, rfl⟩
    have hmin : twElt g = twElt (min g 3) := by
      unfold twElt
      rw [min_assoc, min_self]
    have hl := hclose e he (min g 3) (by rw [hng]; omega)
    obtain ⟨hv, -⟩ := vecZ_letter_twist h (hred e he) (min g 3)
    refine ⟨letter H (min g 3) e, (hin _ (red_letter hpos hp16' _ _)).mp hl, ?_⟩
    rw [hv, hmin]
  refine ⟨ents, hin, hlet, vset .E6 p reps, twMon, fun u hu => commutesPi_twMon hu, ?_,
    fun u hu e he => closed_twMon hlet hu e he, ?_, ?_⟩
  · rintro _ ⟨r, hr, rfl⟩
    exact ⟨r, hreps r hr, rfl⟩
  · rintro _ ⟨e, he, rfl⟩
    obtain ⟨w, hw⟩ := chainOK_word hpos hp16' hch hred e he
    exact ⟨twWordElt w, twWordElt_mem w, word H w e, hw,
      (vecZ_word_twist h w (hred e he)).1⟩
  · rintro _ ⟨r, hr, rfl⟩ _ ⟨e, he, rfl⟩
    have hr' := hred r (hreps r hr)
    have he' := hred e he
    obtain ⟨t, ht⟩ := hnp r hr e he
    unfold npItem at ht
    cases htp : Nat.blt t H.p
    · rw [htp] at ht
      dsimp only at ht
      simp only [andB_eq_true, notB_eq_true, Nat.blt_eq] at ht
      obtain ⟨hlt, hx0, hxm⟩ := ht
      have hlt' : t < H.p + H.p * H.p := hlt
      change inM H mask (modL H.p H.n ((t - H.p) / H.p * r + (t - H.p) % H.p * e)) = false at hxm
      have hA : (t - H.p) / H.p < 16 := by
        have : (t - H.p) / H.p < H.p := by
          rw [Nat.div_lt_iff_lt_mul hpos]
          rcases Nat.lt_or_ge t H.p with h4 | h4
          · rw [Nat.sub_eq_zero_of_le h4.le]
            exact Nat.mul_pos hpos hpos
          · exact Nat.sub_lt_left_of_lt_add h4 hlt'
        omega
      have hC : (t - H.p) % H.p < 16 := by
        have := Nat.mod_lt (t - H.p) hpos
        omega
      have hv := vecZ_modL_lin h hr' he' hA hC
      refine Or.inr ⟨(((t - H.p) / H.p : ℕ) : ZMod p), (((t - H.p) % H.p : ℕ) : ZMod p), ?_, ?_⟩
      · rw [← hv]
        exact vecZ_ne_zero h (red_modL hpos hp16' _) (Nat.ne_of_beq_eq_false hx0)
      · rw [← hv]
        rintro ⟨e', he'', hee⟩
        have := vecZ_inj h (hred e' he'') (red_modL hpos hp16' _) hee
        have h1 := (hin e' (hred e' he'')).mpr he''
        rw [this] at h1
        rw [h1] at hxm
        exact absurd hxm (by simp)
    · rw [htp] at ht
      have htp' : t < 16 := by
        have := Nat.blt_eq.mp htp
        omega
      have he2 : e = modL H.p H.n (t * r + 0 * r) := by
        rw [zero_mul, add_zero]
        exact Nat.eq_of_beq_eq_true ht
      refine Or.inl ⟨(t : ZMod p), ?_⟩
      rw [he2, vecZ_modL_lin h hr' hr' htp' (by norm_num)]
      simp

end LM

theorem pkTwist_caseFacts {p : ℕ} (hp : p.Prime) {D : List ℕ} (hc : pkCheck [] D = true)
    (hh : pkHead Tag.E6.rootCertificate.roots D = true) (ht : pkTag .E6 p 1 D = true) :
    ∀ b ∈ fixedSub p e6Gamma, b ≠ 0 →
      ∀ O : Set (Fin Tag.E6.rank → ℤ),
        IsCompOrbit Tag.E6.symmetrizedCartan e6Gamma (latPhi {α | IsRoot .E6 α} p b) O →
        CaseFacts p e6Gamma (fixedSub p e6Gamma) b O := by
  intro b hb hb0 O hO
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨H, s, hH, hD⟩ := hdK_spec ht
  have h : tagHdOK .E6 p 1 H = true := hH
  obtain ⟨hτ, hm, hn, hpp, hp3, hp16, hnp, -⟩ := tagHdOK_basic h
  have hpos : 0 < H.p := by omega
  have hp16' : H.p ≤ 65536 := by omega
  have hnp0 : 0 < H.np := by
    rw [hnp]
    decide
  obtain ⟨hroot, hall⟩ := rows_roots hD hnp0 hn hh
  have h7 := rtC_le hD hnp0 hh
  have htw : tw H = true := by
    rw [tw, hm]
    rfl
  obtain ⟨ms, hms, tg, htab, hcase⟩ := pkCheck_walk hD hc
  have hpts : pkPts H [] = twV p := by
    unfold pkPts
    rw [htw, hpp]
  have hnorm : ∀ t ∈ fixedSub p e6Gamma, t ≠ 0 →
      ∃ a ∈ pkPts H [], red H a = true ∧ vecZ p Tag.E6.rank a = t := by
    rw [hpts]
    exact fun t ht ht0 => twV_complete h ht ht0
  obtain ⟨a, ha, hared, rfl⟩ := hnorm b hb hb0
  obtain ⟨phi, hphiOK, cls, hcls, hcov⟩ := hcase a ha
  have hphi1 : phi < 2 ^ H.np ∧ allN H.np (fun r => beqB (memB phi r) (killed H r a)) = true := by
    have := (andB_eq_true _ _).mp hphiOK
    refine ⟨?_, this.2⟩
    have h1 := Nat.blt_eq.mp this.1
    change phi < 1 <<< H.np at h1
    rwa [Nat.shiftLeft_eq, one_mul] at h1
  have hphi : ∀ r < H.np, memB phi r = true ↔
      latChar p (vecZ p Tag.E6.rank a) (rowZ .E6 H r) = 0 := by
    intro r hr
    have hb := allN_eq_true.mp hphi1.2 r hr
    rw [← killed_iff h hr (h7 r hr) hared]
    cases h1 : memB phi r <;> cases h2 : killed H r a <;> rw [h1, h2] at hb <;>
      simp_all [beqB, notB]
  have hphinp : ∀ r, memB phi r = true → r < H.np := by
    intro r hr
    by_contra hge
    have h1 : phi < 2 ^ r := lt_of_lt_of_le hphi1.1 (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [memB_iff, Nat.testBit_eq_false_of_lt h1] at hr
    exact absurd hr (by simp)
  obtain ⟨α, hαΦ, rfl⟩ := hO
  obtain ⟨r0, hr0, hα⟩ := hall α hαΦ.1
  have hr0z : latChar p (vecZ p Tag.E6.rank a) (rowZ .E6 H r0) = 0 := by
    have := hαΦ.2
    rcases hα with rfl | rfl
    · exact this
    · rw [latChar_neg] at this
      exact neg_eq_zero.mp this
  obtain ⟨c, hc, hr0c⟩ := hcov r0 ((hphi r0 hr0).mpr hr0z)
  obtain ⟨hland, hcl, hlk, hkind⟩ := hcls c hc
  have hsub : ∀ r ∈ c.1, memB phi r = true ∧ r < H.np := fun r hr => by
    have h1 := memB_maskOf_of_mem hr
    rw [← hland, memB_land] at h1
    exact ⟨h1.2, hphinp r h1.2⟩
  have hmem : ∀ r ∈ c.1, r < H.np := fun r hr => (hsub r hr).2
  have hcomp := comp_eq_rootsOf h hroot hall hphi hsub hcl hlk hr0c hα
  have hR : ∀ β, IsRoot .E6 β → IsRoot .E6 (latPerm e6Gamma β) := by
    intro β hβ
    obtain ⟨r, hr, hβr | hβr⟩ := hall β hβ
    · rw [hβr, ← (rowZ_gam h hr).2]
      exact hroot _ (rowZ_gam h hr).1
    · rw [hβr, latPerm_neg, ← (rowZ_gam h hr).2]
      exact CFSG.LieType.Chevalley.IsRoot.neg (hroot _ (rowZ_gam h hr).1)
  have hO : {β | ∃ k : ℕ, latLinked Tag.E6.symmetrizedCartan
      (latPhi {α | IsRoot .E6 α} p (vecZ p Tag.E6.rank a)) ((latPerm e6Gamma)^[k] α) β} =
      rootsOf .E6 H (c.1 ++ c.1.map (lane H.gam)) := by
    rw [tcOrbit_eq_union latPerm_e6Gamma_involutive, rootsOf_append, ← hcomp]
    congr 1
    ext β
    rw [Set.mem_setOf_eq, latLinked_e6Gamma_iff hb hR, mem_rootsOf_map_gam h hmem, ← hcomp]
    rfl
  rw [hO]
  rcases hkind with ⟨-, v1, q1, v2, q2, v3, q3, hk⟩ | ⟨-, R, hlen, hR'⟩ | ⟨mask, hmk, hwit⟩
  · exact Or.inl (kind0_twist hp h hmem h7 hk)
  · exact Or.inr (Or.inl (kind1_twist hp h hared hb hmem hR' hlen))
  · refine Or.inr (Or.inr ?_)
    have hlm : LMFacts H mask := by
      rcases hmk with ⟨-, rfl⟩ | ⟨-, k, rfl⟩
      · exact lmFacts_zero H
      · rcases nthM_mem ms k with h0 | h0
        · rw [h0]
          exact lmFacts_zero H
        · exact hms _ h0
    obtain ⟨ents, hin, hlet, Rr, hPF⟩ := lm_planeFree_twist h hlm
    refine ⟨vset .E6 p ents, Rr, hPF, fun t htV ht0 htM => ?_⟩
    obtain ⟨b, hb', hbred, rfl⟩ := hnorm t htV ht0
    have htg : ∃ t' ∈ tg, red H t' = true ∧ ∃ u : WeylGroup Tag.E6, u ∈ twMon ∧
        vecZ p Tag.E6.rank t' = cowAct u (vecZ p Tag.E6.rank b) := by
      rcases htab with rfl | ⟨hall', hw⟩
      · exact ⟨b, hb', hbred, 1, Submonoid.one_mem _, (cowAct_one _).symm⟩
      · obtain ⟨w, hw'⟩ := hw b hb'
        have hT : ∀ v ∈ tg, red H v = true := fun v hv =>
          ((vecOK_iff _ _).mp ((allVec_iff H tg).mp hall' v hv)).1
        obtain ⟨h5, h6⟩ := vecZ_word_twist h w hbred
        exact ⟨word H w b, mem_of_inM_maskL hpos hT h6 hw', h6, twWordElt w, twWordElt_mem w, h5⟩
    obtain ⟨t', ht'tg, ht'red, u, huG, hu⟩ := htg
    have hm' : inM H mask t' = false := by
      cases hmt : inM H mask t'
      · rfl
      · exfalso
        apply htM
        refine mem_of_cowAct_mem (Set.toFinite _) (closed_twMon hlet huG) ?_
        rw [← hu]
        exact ⟨t', (hin t' ht'red).mp hmt, rfl⟩
    obtain ⟨ps, w2, hps, hc0, hw2⟩ := hwit t' ht'tg hm'
    have hcomb := combo_mem_spanT h hared hmem ps hps
    obtain ⟨h8, -⟩ := vecZ_word_twist h w2 hcomb.1
    refine ⟨vecZ p Tag.E6.rank (combo H a ps), hcomb.2, vecZ_ne_zero h hcomb.1 hc0,
      u⁻¹ * twWordElt w2, commutesPi_mul (commutesPi_inv (commutesPi_twMon huG))
        (commutesPi_twWordElt w2), ?_⟩
    rw [cowAct_mul, ← h8, hw2, hu, cowAct_inv_cowAct]

end CFSG.KC.GGToral
