module

public import CFSG.Holt.H78.Sec4Prop49S5c

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General CFSG.Open
open scoped Pointwise

section Union

variable {G : Type} [Group G] [Finite G]

theorem ncard_biUnion_sdiff_one {ι : Type*} [DecidableEq ι] (F : Finset ι)
    (W : ι → Subgroup G) (hW : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → W i ⊓ W j = ⊥) {w : ℕ}
    (hw : ∀ i ∈ F, Nat.card (W i) = w) :
    (⋃ i ∈ F, ((W i : Set G) \ {1})).ncard = F.card * (w - 1) := by
  induction F using Finset.induction_on with
  | empty => simp
  | insert i F hi ih =>
    rw [Finset.set_biUnion_insert, Set.ncard_union_eq ?_ (Set.toFinite _) (Set.toFinite _),
      ih (fun a ha b hb hab => hW a (Finset.mem_insert_of_mem ha) b
        (Finset.mem_insert_of_mem hb) hab) (fun a ha => hw a (Finset.mem_insert_of_mem ha)),
      Set.ncard_sdiff_singleton_of_mem (one_mem (W i)), ← Nat.card_coe_set_eq,
      SetLike.coe_sort_coe, hw i (Finset.mem_insert_self i F), Finset.card_insert_of_notMem hi]
    · ring
    · rw [Set.disjoint_left]
      rintro x ⟨hxi, hx1⟩ hxF
      simp only [Set.mem_iUnion] at hxF
      obtain ⟨j, hj, hxj, -⟩ := hxF
      have hij : i ≠ j := fun h => hi (h ▸ hj)
      have := hW i (Finset.mem_insert_self i F) j (Finset.mem_insert_of_mem hj) hij
      have hx : x ∈ W i ⊓ W j := ⟨hxi, hxj⟩
      rw [this, Subgroup.mem_bot] at hx
      exact hx1 hx

end Union

namespace P49Config

section WLines

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α : Ω} {v : G} {C : P49Config G Ω α v}

namespace P95Data

variable (P : C.P95Data)

@[expose] def Wl (ℓ : Set Ω) : Subgroup G := P.E ⊓ fixingSubgroup G ℓ

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem mem_Wl {ℓ : Set Ω} {e : G} : e ∈ P.Wl ℓ ↔ e ∈ P.E ∧ ∀ y ∈ ℓ, e • y = y := by
  rw [Wl, Subgroup.mem_inf, mem_fixingSubgroup_iff]

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem Wl_line : P.Wl C.line = P.W := rfl

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem conj_mem_Wl {n : G} (hn : n ∈ Subgroup.normalizer (P.E : Set G)) {ℓ : Set Ω} {e : G}
    (he : e ∈ P.Wl ℓ) : n * e * n⁻¹ ∈ P.Wl (n • ℓ) := by
  rw [mem_Wl] at he ⊢
  refine ⟨(Subgroup.mem_normalizer_iff.mp hn e).mp he.1, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  rw [mul_smul, mul_smul, inv_smul_smul, he.2 y hy]

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem map_conj_Wl {n : G} (hn : n ∈ Subgroup.normalizer (P.E : Set G)) (ℓ : Set Ω) :
    (P.Wl ℓ).map (MulAut.conj n).toMonoidHom = P.Wl (n • ℓ) := by
  refine le_antisymm ?_ fun e he => ⟨n⁻¹ * e * n⁻¹⁻¹, ?_, by simp [mul_assoc]⟩
  · rintro _ ⟨e, he, rfl⟩
    exact P.conj_mem_Wl hn he
  · have := P.conj_mem_Wl (inv_mem hn) he
    rwa [inv_smul_smul] at this

theorem card_Wl (h : C.P95) {ℓ : Set Ω} (hℓ : ℓ ∈ linesThrough G C.line α) :
    Nat.card (P.Wl ℓ) = Nat.card P.W := by
  obtain ⟨n, -, hnN, rfl⟩ := P.exists_mem_normalizer_smul_line h hℓ
  rw [← P.map_conj_Wl hnN, Subgroup.card_map_of_injective (MulAut.conj n).injective, Wl_line]

omit [Finite G] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem exists_mem_ne_of_mem_linesThrough {ℓ : Set Ω} (hℓ : ℓ ∈ linesThrough G C.line α) :
    ∃ y ∈ ℓ, y ≠ α := by
  obtain ⟨⟨g, rfl⟩, -⟩ := hℓ
  by_cases hg : g • α = α
  · refine ⟨g • C.β, Set.smul_mem_smul_set C.β_mem_line, fun h1 => C.ne ?_⟩
    exact smul_left_cancel g (hg.trans h1.symm)
  · exact ⟨g • α, Set.smul_mem_smul_set C.α_mem_line, hg⟩

omit [Finite G] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem notMem_Wl {s : G} (hs : s ∈ longInvAt G Ω α) {ℓ : Set Ω}
    (hℓ : ℓ ∈ linesThrough G C.line α) : s ∉ P.Wl ℓ := fun hsW => by
  obtain ⟨y, hy, hyα⟩ := exists_mem_ne_of_mem_linesThrough (C := C) hℓ
  exact hyα (hs.1.2.unique ((P.mem_Wl.mp hsW).2 y hy) hs.2)

theorem two_mul_le_ncard (h : C.P95) (T : P.Torus) :
    (Nat.card C.rootZ - 1) * 2 ≤ {s | s ∈ P.E ∧ s ∈ longInvAt G Ω α}.ncard := by
  have hLs := fun {e : G} (he : e ∈ P.E) => P.E_le_stabilizer_line h he
  set z₀ := C.lineHom ⟨P.t, hLs P.t_mem_E⟩ with hz₀
  have hz₀1 : z₀ ≠ 1 := fun h1 =>
    P.notMem_Wl P.t_mem (line_mem_linesThrough C) ((P.mem_W_iff_lineHom h P.t_mem_E).mpr h1)
  have hz₀Z : z₀ ∈ C.rootZ := P.lineHom_mem_rootZ h P.t_mem_E
  have hu : C.lineHom ⟨P.u, hLs P.u_mem_E⟩ = z₀ := by
    have hv : C.lineHom ⟨P.t * P.u, hLs (mul_mem P.t_mem_E P.u_mem_E)⟩ = 1 := by
      have hvW : P.t * P.u ∈ P.W := (P.mem_W).mpr ⟨mul_mem P.t_mem_E P.u_mem_E, fun y hy => by
        rw [P.mul_eq]
        exact mem_fixSet_zpowers_iff.mp (C.line_subset_fixSet hy)⟩
      exact (P.mem_W_iff_lineHom h (mul_mem P.t_mem_E P.u_mem_E)).mp hvW
    rw [P.lineHom_mul h P.t_mem_E P.u_mem_E] at hv
    rw [eq_inv_of_mul_eq_one_right hv, ← hz₀,
      inv_eq_of_mul_eq_one_right ((C.isNaturalSE C.i).mul_self_eq_one_of_mem_rootCenter hz₀Z)]
  have hk : ∀ z : {z // z ∈ C.rootZ ∧ z ≠ 1}, ∃ k : ℕ, T.d ^ k * z₀ * (T.d ^ k)⁻¹ = z := by
    rintro ⟨z, hz, hz1⟩
    obtain ⟨d', hd'M, hd'a, hd'b, hd'z⟩ :=
      (C.isNaturalSE C.i).exists_conj_eq C.coord_ne hz₀Z hz₀1 hz hz1
    obtain ⟨k, rfl⟩ := T.exists_pow_eq hd'M hd'a hd'b
    exact ⟨k, hd'z⟩
  choose K hK using hk
  have hnk : ∀ k : ℕ, T.n ^ k ∈ Subgroup.normalizer (P.E : Set G) ∧ T.n ^ k ∈ stabilizer G α :=
    fun k => ⟨Subgroup.pow_mem _ T.mem_normalizer k, Subgroup.pow_mem _ T.mem_stabilizer k⟩
  have hconj : ∀ k : ℕ, ∀ {e}, e ∈ P.E → e ∈ longInvAt G Ω α →
      T.n ^ k * e * (T.n ^ k)⁻¹ ∈ P.E ∧ T.n ^ k * e * (T.n ^ k)⁻¹ ∈ longInvAt G Ω α := by
    intro k e he heJ
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hnk k).1 e).mp he, ?_⟩
    have := conj_mem_longInvAt heJ (T.n ^ k)
    rwa [mem_stabilizer_iff.mp (hnk k).2] at this
  set f : {z // z ∈ C.rootZ ∧ z ≠ 1} × Bool → {s | s ∈ P.E ∧ s ∈ longInvAt G Ω α} :=
    fun p => ⟨T.n ^ K p.1 * (if p.2 then P.t else P.u) * (T.n ^ K p.1)⁻¹, by
      cases p.2
      · exact hconj _ P.u_mem_E P.u_mem
      · exact hconj _ P.t_mem_E P.t_mem⟩
  have hact : ∀ p, C.LineActs (f p : G) p.1 := by
    rintro ⟨z, b⟩
    have hb : C.LineActs (if b then P.t else P.u) z₀ := by
      cases b
      · exact hu ▸ C.lineActs_lineHom ⟨P.u, hLs P.u_mem_E⟩
      · exact C.lineActs_lineHom ⟨P.t, hLs P.t_mem_E⟩
    have := ((T.lineActs.pow (K z)).mul hb).mul (T.lineActs.pow (K z)).inv
    rwa [hK z] at this
  have hinj : Function.Injective f := by
    rintro ⟨z, b⟩ ⟨z', b'⟩ hpp
    have e1 := (hact (z, b)).unique (hpp ▸ hact (z', b'))
    have hzz : z = z' := Subtype.ext e1
    subst hzz
    have e2 := congrArg Subtype.val hpp
    simp only [f] at e2
    have e3 := mul_left_cancel (mul_right_cancel e2)
    cases b <;> cases b'
    · rfl
    · exact absurd e3.symm P.t_ne_u
    · exact absurd e3 P.t_ne_u
    · rfl
  have hcard := Nat.card_le_card_of_injective f hinj
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool,
    Nat.card_coe_set_eq] at hcard
  have hdom : Nat.card {z // z ∈ C.rootZ ∧ z ≠ 1} = Nat.card C.rootZ - 1 := by
    have e1 : Nat.card {z // z ∈ C.rootZ ∧ z ≠ 1} =
        ((C.rootZ : Set (Equiv.Perm (C.D.Ψc C.i))) \ {1}).ncard := Nat.card_coe_set_eq _
    have e2 : Nat.card C.rootZ = (C.rootZ : Set (Equiv.Perm (C.D.Ψc C.i))).ncard :=
      Nat.card_coe_set_eq _
    rw [e1, e2, Set.ncard_sdiff_singleton_of_mem (one_mem C.rootZ)]
  rwa [hdom] at hcard

end P95Data

end WLines

section Count

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α : Ω} {v : G} {C : P49Config G Ω α v}

namespace P95Data

variable {P : C.P95Data}

namespace Torus

variable (T : P.Torus)

omit [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem exists_pow_eq_of_mem_zpowers {g : G} (hg : g ∈ Subgroup.zpowers T.n) :
    ∃ k : ℕ, T.n ^ k = g := by
  rw [← SetLike.mem_coe, ← (isOfFinOrder_of_finite T.n).powers_eq_zpowers] at hg
  exact Submonoid.mem_powers_iff _ _ |>.mp hg

theorem pow_comm_mem_V (h : C.P95) (k : ℕ) {e : G} (he : e ∈ P.E) :
    T.n ^ k * e * (T.n ^ k)⁻¹ * e⁻¹ ∈ T.V := by
  induction k with
  | zero => simp
  | succ k ih =>
    have he' : T.n ^ k * e * (T.n ^ k)⁻¹ ∈ P.E :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ T.mem_normalizer k) e).mp he
    have h1 := (T.mem_V h).mpr ⟨_, he', rfl⟩
    have := mul_mem h1 ih
    rwa [show T.n * (T.n ^ k * e * (T.n ^ k)⁻¹) * T.n⁻¹ * (T.n ^ k * e * (T.n ^ k)⁻¹)⁻¹ *
      (T.n ^ k * e * (T.n ^ k)⁻¹ * e⁻¹) = T.n ^ (k + 1) * e * (T.n ^ (k + 1))⁻¹ * e⁻¹ by
        rw [pow_succ']; group] at this

theorem mem_W_of_conj_eq (h : C.P95) {k : ℕ} {x : G} (hx : x ∈ T.V)
    (hxk : T.n ^ k * x * (T.n ^ k)⁻¹ ≠ x) {e : G} (he : e ∈ P.E)
    (hek : T.n ^ k * e * (T.n ^ k)⁻¹ = e) : e ∈ P.W := by
  have hLs := fun {e : G} (he : e ∈ P.E) => P.E_le_stabilizer_line h he
  by_contra heW
  set z := C.lineHom ⟨e, hLs he⟩
  have hz1 : z ≠ 1 := fun h1 => heW ((P.mem_W_iff_lineHom h he).mpr h1)
  have hzZ := P.lineHom_mem_rootZ h he
  have hdk : T.d ^ k * z * (T.d ^ k)⁻¹ = z := by
    have h1 := ((T.lineActs.pow k).mul (C.lineActs_lineHom ⟨e, hLs he⟩)).mul
      (T.lineActs.pow k).inv
    rw [hek] at h1
    exact (C.lineHom_eq h1).symm
  have hall : ∀ z' ∈ C.rootZ, T.d ^ k * z' * (T.d ^ k)⁻¹ = z' := by
    intro z' hz'
    by_cases hz'1 : z' = 1
    · rw [hz'1]; group
    obtain ⟨d', hd'M, hd'a, hd'b, hd'z⟩ :=
      (C.isNaturalSE C.i).exists_conj_eq C.coord_ne hzZ hz1 hz' hz'1
    obtain ⟨j, rfl⟩ := T.exists_pow_eq hd'M hd'a hd'b
    rw [← hd'z]
    have hc : T.d ^ k * T.d ^ j = T.d ^ j * T.d ^ k := ((Commute.refl T.d).pow_pow k j).eq
    calc T.d ^ k * (T.d ^ j * z * (T.d ^ j)⁻¹) * (T.d ^ k)⁻¹
        = (T.d ^ k * T.d ^ j) * z * (T.d ^ k * T.d ^ j)⁻¹ := by group
      _ = (T.d ^ j * T.d ^ k) * z * (T.d ^ j * T.d ^ k)⁻¹ := by rw [hc]
      _ = T.d ^ j * (T.d ^ k * z * (T.d ^ k)⁻¹) * (T.d ^ j)⁻¹ := by group
      _ = T.d ^ j * z * (T.d ^ j)⁻¹ := by rw [hdk]
  refine hxk ?_
  have hxE := T.V_le_E hx
  have hx' : T.n ^ k * x * (T.n ^ k)⁻¹ ∈ T.V := by
    have := mul_mem (T.pow_comm_mem_V h k hxE) hx
    rwa [inv_mul_cancel_right] at this
  have hact := ((T.lineActs.pow k).mul (C.lineActs_lineHom ⟨x, hLs hxE⟩)).mul
    (T.lineActs.pow k).inv
  rw [hall _ (P.lineHom_mem_rootZ h hxE)] at hact
  have hw : (T.n ^ k * x * (T.n ^ k)⁻¹)⁻¹ * x ∈ P.W := (P.mem_W).mpr
    ⟨mul_mem (inv_mem (T.V_le_E hx')) hxE, by
      rintro _ ⟨ψ, rfl⟩
      have := (hact.inv.mul (C.lineActs_lineHom ⟨x, hLs hxE⟩)) ψ
      rwa [inv_mul_cancel, Equiv.Perm.one_apply] at this⟩
  exact inv_mul_eq_one.mp (T.eq_one_of_mem_W h (mul_mem (inv_mem hx') hx) hw)

end Torus

theorem inf_Wl_eq_bot (h : C.P95)
    (hA : ∀ ℓ ∈ linesThrough G C.line α, ℓ ≠ C.line → P.W ⊓ P.Wl ℓ = ⊥) {ℓ ℓ' : Set Ω}
    (hℓ : ℓ ∈ linesThrough G C.line α) (hℓ' : ℓ' ∈ linesThrough G C.line α) (hne : ℓ ≠ ℓ') :
    P.Wl ℓ ⊓ P.Wl ℓ' = ⊥ := by
  obtain ⟨n, hnα, hnN, rfl⟩ := P.exists_mem_normalizer_smul_line h hℓ
  have hℓ'' : n⁻¹ • ℓ' ∈ linesThrough G C.line α := by
    have := smul_mem_linesThrough hℓ' n⁻¹
    rwa [mem_stabilizer_iff.mp (inv_mem hnα)] at this
  have hne' : n⁻¹ • ℓ' ≠ C.line := fun h1 => hne (by rw [← h1, smul_inv_smul])
  rw [eq_bot_iff]
  rintro x ⟨hx, hx'⟩
  have h1 := P.conj_mem_Wl (inv_mem hnN) hx
  have h2 := P.conj_mem_Wl (inv_mem hnN) hx'
  rw [inv_smul_smul] at h1
  have h3 : n⁻¹ * x * n⁻¹⁻¹ ∈ P.W ⊓ P.Wl (n⁻¹ • ℓ') := ⟨h1, h2⟩
  rw [hA _ hℓ'' hne', Subgroup.mem_bot] at h3
  rw [Subgroup.mem_bot]
  calc x = n * (n⁻¹ * x * n⁻¹⁻¹) * n⁻¹ := by group
    _ = 1 := by rw [h3]; group

theorem false_of_forall_conj_eq (h : C.P95) (T : P.Torus)
    (hA' : ∀ ℓ ∈ linesThrough G C.line α, ∀ ℓ' ∈ linesThrough G C.line α, ℓ ≠ ℓ' →
      P.Wl ℓ ⊓ P.Wl ℓ' = ⊥) {ℓ : Set Ω} (hℓ : ℓ ∈ linesThrough G C.line α) (hℓL : ℓ ≠ C.line)
    (hc : ∀ k : ℕ, T.n ^ k • ℓ = ℓ → ∀ x ∈ T.V, T.n ^ k * x * (T.n ^ k)⁻¹ = x) : False := by
  classical
  have hq := (C.isNaturalSE C.i).exists_isBenderAction
  obtain ⟨nq, kq, eq, hA⟩ := hq
  have hqcard : Nat.card C.rootZ = 2 ^ nq := hA.card_rootCenter_seRadical (C.D.coord C.a C.i)
  have hq4 := hA.four_le_q
  have hV := T.card_V h
  obtain ⟨x₀, hx₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    ((Subgroup.one_lt_card_iff_ne_bot T.V).mp (by rw [hV, hqcard]; omega))
  have hk : ∀ y : {y // y ∈ T.V ∧ y ≠ 1}, ∃ k : ℕ, T.n ^ k * x₀ * (T.n ^ k)⁻¹ = y := fun y =>
    T.exists_pow_conj_eq h x₀.2 y.2.1 (fun h1 => hx₀1 (Subtype.ext h1)) y.2.2
  choose K hK using hk
  set f : {y // y ∈ T.V ∧ y ≠ 1} → Set Ω := fun y => T.n ^ K y • ℓ
  have hnL : ∀ k : ℕ, T.n ^ k • C.line = C.line := fun k => (T.lineActs.pow k).smul_line
  have hfline : ∀ y, f y ∈ linesThrough G C.line α := fun y => by
    have := smul_mem_linesThrough hℓ (T.n ^ K y)
    rwa [mem_stabilizer_iff.mp (Subgroup.pow_mem _ T.mem_stabilizer _)] at this
  have hfL : ∀ y, f y ≠ C.line := fun y h1 => hℓL (by
    have := congrArg (fun X => (T.n ^ K y)⁻¹ • X) h1
    simp only [f, inv_smul_smul] at this
    rw [this, inv_smul_eq_iff, hnL])
  have hfinj : Function.Injective f := by
    intro y y' hyy
    have hg : ((T.n ^ K y')⁻¹ * T.n ^ K y) • ℓ = ℓ := by
      rw [mul_smul]
      exact inv_smul_eq_iff.mpr hyy
    obtain ⟨m, hm⟩ := T.exists_pow_eq_of_mem_zpowers (g := (T.n ^ K y')⁻¹ * T.n ^ K y)
      (mul_mem (inv_mem (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _))
        (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _))
    have h1 := hc m (hm ▸ hg) x₀ x₀.2
    rw [hm] at h1
    refine Subtype.ext ?_
    rw [← hK y, ← hK y']
    calc T.n ^ K y * x₀ * (T.n ^ K y)⁻¹
        = T.n ^ K y' * ((T.n ^ K y')⁻¹ * T.n ^ K y * x₀ * ((T.n ^ K y')⁻¹ * T.n ^ K y)⁻¹) *
            (T.n ^ K y')⁻¹ := by group
      _ = T.n ^ K y' * x₀ * (T.n ^ K y')⁻¹ := by rw [h1]
  have : Fintype {y // y ∈ T.V ∧ y ≠ 1} := Fintype.ofFinite _
  set F : Finset (Set Ω) := insert C.line (Finset.univ.image f)
  have hLF : C.line ∉ Finset.univ.image f := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    exact fun y h1 => hfL y h1
  have hFcard : F.card = Nat.card C.rootZ := by
    rw [Finset.card_insert_of_notMem hLF, Finset.card_image_of_injective _ hfinj,
      Finset.card_univ, ← Nat.card_eq_fintype_card]
    have e1 : Nat.card {y // y ∈ T.V ∧ y ≠ 1} = ((T.V : Set G) \ {1}).ncard :=
      Nat.card_coe_set_eq _
    have e2 : Nat.card T.V = (T.V : Set G).ncard := Nat.card_coe_set_eq _
    rw [e1, Set.ncard_sdiff_singleton_of_mem (one_mem T.V), ← e2, hV]
    have := Nat.card_pos (α := C.rootZ)
    omega
  have hFlines : ∀ ℓ' ∈ F, ℓ' ∈ linesThrough G C.line α := by
    intro ℓ' hℓ'
    rcases Finset.mem_insert.mp hℓ' with rfl | hℓ'
    · exact line_mem_linesThrough C
    · obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hℓ'
      exact hfline y
  have hU := ncard_biUnion_sdiff_one F (fun ℓ' => P.Wl ℓ')
    (fun a ha b hb hab => hA' a (hFlines a ha) b (hFlines b hb) hab)
    (fun a ha => P.card_Wl h (hFlines a ha))
  set J₀ := {s | s ∈ P.E ∧ s ∈ longInvAt G Ω α}
  set U := ⋃ ℓ' ∈ F, ((P.Wl ℓ' : Set G) \ {1})
  have hdisj : Disjoint J₀ U := by
    rw [Set.disjoint_left]
    rintro s ⟨-, hs⟩ hsU
    simp only [U, Set.mem_iUnion] at hsU
    obtain ⟨ℓ', hℓ', hsW, -⟩ := hsU
    exact P.notMem_Wl hs (hFlines ℓ' hℓ') hsW
  have hsub : J₀ ∪ U ⊆ (P.E : Set G) \ {1} := by
    rintro s (⟨hsE, hs⟩ | hsU)
    · refine ⟨hsE, fun h1 => ?_⟩
      have h2 := hs.1.1
      rw [Set.mem_singleton_iff.mp h1, orderOf_one] at h2
      exact absurd h2 (by norm_num)
    · simp only [U, Set.mem_iUnion] at hsU
      obtain ⟨ℓ', -, hsW, hs1⟩ := hsU
      exact ⟨(P.mem_Wl.mp hsW).1, hs1⟩
  have hE1 : ((P.E : Set G) \ {1}).ncard = Nat.card P.W * Nat.card C.rootZ - 1 := by
    rw [Set.ncard_sdiff_singleton_of_mem (one_mem P.E),
      show (P.E : Set G).ncard = Nat.card P.E from (Nat.card_coe_set_eq _).symm, P.card_E h]
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), hU, hFcard, hE1] at h1
  have h2 : (Nat.card C.rootZ - 1) * 2 ≤ J₀.ncard := P.two_mul_le_ncard h T
  have hw : 1 ≤ Nat.card P.W := Nat.card_pos
  generalize J₀.ncard = J at h1 h2
  generalize Nat.card C.rootZ = Q at h1 h2 hqcard
  generalize Nat.card P.W = w at h1 hw
  obtain ⟨w, rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
  rw [Nat.add_sub_cancel, add_mul, one_mul, mul_comm Q w] at h1
  omega

theorem Wl_le_V (h : C.P95) (T : P.Torus)
    (hA' : ∀ ℓ ∈ linesThrough G C.line α, ∀ ℓ' ∈ linesThrough G C.line α, ℓ ≠ ℓ' →
      P.Wl ℓ ⊓ P.Wl ℓ' = ⊥) {ℓ : Set Ω} (hℓ : ℓ ∈ linesThrough G C.line α)
    (hℓL : ℓ ≠ C.line) : P.Wl ℓ ≤ T.V := by
  by_cases hc : ∃ k : ℕ, T.n ^ k • ℓ = ℓ ∧ ∃ x ∈ T.V, T.n ^ k * x * (T.n ^ k)⁻¹ ≠ x
  · obtain ⟨k, hkℓ, x, hx, hxk⟩ := hc
    have hbN : T.n ^ k ∈ Subgroup.normalizer (P.E : Set G) :=
      Subgroup.pow_mem _ T.mem_normalizer k
    have hmap : ∀ w : P.Wl ℓ, T.n ^ k * w * (T.n ^ k)⁻¹ * (w : G)⁻¹ ∈ P.Wl ℓ := fun w => by
      have := P.conj_mem_Wl hbN w.2
      rw [hkℓ] at this
      exact mul_mem this (inv_mem w.2)
    set φ : P.Wl ℓ → P.Wl ℓ := fun w => ⟨_, hmap w⟩
    have hφ : Function.Injective φ := by
      intro w w' hww
      have e := congrArg Subtype.val hww
      simp only [φ] at e
      have hfix : T.n ^ k * ((w' : G)⁻¹ * w) * (T.n ^ k)⁻¹ = (w' : G)⁻¹ * w := by
        have e' : T.n ^ k * w * (T.n ^ k)⁻¹ = T.n ^ k * w' * (T.n ^ k)⁻¹ * (w' : G)⁻¹ * w := by
          rw [← e]; group
        calc T.n ^ k * ((w' : G)⁻¹ * w) * (T.n ^ k)⁻¹
            = (T.n ^ k * w' * (T.n ^ k)⁻¹)⁻¹ * (T.n ^ k * w * (T.n ^ k)⁻¹) := by group
          _ = (w' : G)⁻¹ * w := by rw [e']; group
      have hmem : (w' : G)⁻¹ * w ∈ P.Wl ℓ := mul_mem (inv_mem w'.2) w.2
      have hW := T.mem_W_of_conj_eq h hx hxk (P.mem_Wl.mp hmem).1 hfix
      have h1 : (w' : G)⁻¹ * w ∈ P.Wl C.line ⊓ P.Wl ℓ := ⟨hW, hmem⟩
      rw [hA' _ (line_mem_linesThrough C) _ hℓ (Ne.symm hℓL), Subgroup.mem_bot] at h1
      exact (Subtype.ext (inv_mul_eq_one.mp h1)).symm
    intro w hw
    obtain ⟨w', hw'⟩ := (Finite.injective_iff_surjective.mp hφ) ⟨w, hw⟩
    have := T.pow_comm_mem_V h k (P.mem_Wl.mp w'.2).1
    have e : T.n ^ k * w' * (T.n ^ k)⁻¹ * (w' : G)⁻¹ = w := congrArg Subtype.val hw'
    rw [e] at this
    exact this
  · push Not at hc
    exact (P.false_of_forall_conj_eq h T hA' hℓ hℓL hc).elim

theorem exists_ne_inf_ne_bot (h : C.P95) :
    ∃ ℓ ∈ linesThrough G C.line α, ℓ ≠ C.line ∧ P.W ⊓ P.Wl ℓ ≠ ⊥ := by
  classical
  obtain ⟨T⟩ := P.nonempty_torus h
  by_contra hne
  have hA : ∀ ℓ ∈ linesThrough G C.line α, ℓ ≠ C.line → P.W ⊓ P.Wl ℓ = ⊥ :=
    fun ℓ hℓ hℓL => by_contra fun h1 => hne ⟨ℓ, hℓ, hℓL, h1⟩
  have hA' := fun ℓ (hℓ : ℓ ∈ linesThrough G C.line α) ℓ' (hℓ' : ℓ' ∈ linesThrough G C.line α)
    (hne : ℓ ≠ ℓ') => P.inf_Wl_eq_bot h hA hℓ hℓ' hne
  have hi := fun ℓ (hℓ : ℓ ∈ linesThrough G C.line α) (hℓL : ℓ ≠ C.line) =>
    P.Wl_le_V h T hA' hℓ hℓL
  obtain ⟨ℓ₂, hℓ₂, ℓ₃, hℓ₃, hℓ₂L, hℓ₃L, hℓ₂₃⟩ := h.exists_three_lines
  have hLl := line_mem_linesThrough C
  set S : Finset (Set Ω) := (Set.toFinite (linesThrough G C.line α)).toFinset
  have hS : ∀ ℓ, ℓ ∈ S ↔ ℓ ∈ linesThrough G C.line α := fun ℓ => Set.Finite.mem_toFinset _
  set F₁ := S.erase C.line
  set F₂ := F₁.erase ℓ₂
  have hmem₁ : ∀ ℓ, ℓ ∈ F₁ ↔ ℓ ∈ linesThrough G C.line α ∧ ℓ ≠ C.line := fun ℓ => by
    rw [Finset.mem_erase, hS, and_comm]
  have hmem₂ : ∀ ℓ, ℓ ∈ F₂ ↔ ℓ ∈ linesThrough G C.line α ∧ ℓ ≠ C.line ∧ ℓ ≠ ℓ₂ := fun ℓ => by
    rw [Finset.mem_erase, hmem₁]
    tauto
  have hF₁ : F₁.card + 1 = S.card := Finset.card_erase_add_one ((hS _).mpr hLl)
  have hF₂ : F₂.card + 1 = F₁.card := Finset.card_erase_add_one ((hmem₁ _).mpr ⟨hℓ₂, hℓ₂L⟩)
  have hF₂pos : 1 ≤ F₂.card := Finset.card_pos.mpr ⟨ℓ₃, (hmem₂ _).mpr ⟨hℓ₃, hℓ₃L, Ne.symm hℓ₂₃⟩⟩
  have hV := T.card_V h
  have hw2 : 2 ≤ Nat.card P.W := by
    have hv1 : v ≠ 1 := fun h1 => by
      have h2 := C.isTypeL.orderOf_eq_two
      rw [h1, orderOf_one] at h2
      exact absurd h2 (by norm_num)
    have hvW : v ∈ P.W := (P.mem_W).mpr ⟨P.v_mem_E, fun y hy =>
      mem_fixSet_zpowers_iff.mp (C.line_subset_fixSet hy)⟩
    exact (Subgroup.one_lt_card_iff_ne_bot _).mpr
      (Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨v, hvW⟩, fun h1 => hv1 (congrArg Subtype.val h1)⟩)
  have hcardW : ∀ ℓ ∈ linesThrough G C.line α, Nat.card (P.Wl ℓ) = Nat.card P.W :=
    fun ℓ hℓ => P.card_Wl h hℓ
  have hU1 := ncard_biUnion_sdiff_one F₁ P.Wl
    (fun a ha b hb hab => hA' a ((hmem₁ a).mp ha).1 b ((hmem₁ b).mp hb).1 hab)
    (fun a ha => hcardW a ((hmem₁ a).mp ha).1)
  obtain ⟨w₀, hw₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    ((Subgroup.one_lt_card_iff_ne_bot (P.Wl ℓ₂)).mp (by rw [hcardW ℓ₂ hℓ₂]; omega))
  have hw₀V : (w₀ : G) ∈ T.V := hi ℓ₂ hℓ₂ hℓ₂L w₀.2
  have hw₀1' : (w₀ : G) ≠ 1 := fun h1 => hw₀1 (Subtype.ext h1)
  have hsub1 : (T.V : Set G) \ {1} = ⋃ ℓ ∈ F₁, ((P.Wl ℓ : Set G) \ {1}) := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro y ⟨hy, hy1⟩
      obtain ⟨k, hk⟩ := T.exists_pow_conj_eq h hw₀V hy hw₀1' hy1
      have hkℓ : T.n ^ k • ℓ₂ ∈ linesThrough G C.line α := by
        have := smul_mem_linesThrough hℓ₂ (T.n ^ k)
        rwa [mem_stabilizer_iff.mp (Subgroup.pow_mem _ T.mem_stabilizer _)] at this
      have hkL : T.n ^ k • ℓ₂ ≠ C.line := fun h1 => hℓ₂L (by
        rw [← inv_smul_eq_iff.mpr h1.symm, inv_smul_eq_iff, (T.lineActs.pow k).smul_line])
      simp only [Set.mem_iUnion]
      refine ⟨_, (hmem₁ _).mpr ⟨hkℓ, hkL⟩, ?_, hy1⟩
      rw [← hk]
      exact P.conj_mem_Wl (Subgroup.pow_mem _ T.mem_normalizer k) w₀.2
    · intro y hy
      simp only [Set.mem_iUnion] at hy
      obtain ⟨ℓ, hℓ, hyW, hy1⟩ := hy
      exact ⟨hi ℓ ((hmem₁ ℓ).mp hℓ).1 ((hmem₁ ℓ).mp hℓ).2 hyW, hy1⟩
  have hq : Nat.card T.V - 1 = F₁.card * (Nat.card P.W - 1) := by
    rw [← hU1, ← hsub1, Set.ncard_sdiff_singleton_of_mem (one_mem T.V)]
    rfl
  obtain ⟨n₂, hn₂α, hn₂N, hn₂L⟩ := P.exists_mem_normalizer_smul_line h hℓ₂
  set V₂ := T.V.map (MulAut.conj n₂).toMonoidHom
  have hV₂ : Nat.card V₂ = Nat.card T.V :=
    Subgroup.card_map_of_injective (MulAut.conj n₂).injective
  have hW₂ : ∀ ℓ ∈ linesThrough G C.line α, ℓ ≠ ℓ₂ → P.Wl ℓ ≤ V₂ := by
    intro ℓ hℓ hℓℓ₂
    have hℓ' : n₂⁻¹ • ℓ ∈ linesThrough G C.line α := by
      have := smul_mem_linesThrough hℓ n₂⁻¹
      rwa [mem_stabilizer_iff.mp (inv_mem hn₂α)] at this
    have hℓ'L : n₂⁻¹ • ℓ ≠ C.line := fun h1 => hℓℓ₂ (by rw [← hn₂L, ← h1, smul_inv_smul])
    rw [← smul_inv_smul n₂ ℓ, ← P.map_conj_Wl hn₂N]
    exact Subgroup.map_mono (hi _ hℓ' hℓ'L)
  have hU2 := ncard_biUnion_sdiff_one F₂ P.Wl
    (fun a ha b hb hab => hA' a ((hmem₂ a).mp ha).1 b ((hmem₂ b).mp hb).1 hab)
    (fun a ha => hcardW a ((hmem₂ a).mp ha).1)
  have hsub2 : ⋃ ℓ ∈ F₂, ((P.Wl ℓ : Set G) \ {1}) ⊆ ((T.V ⊓ V₂ : Subgroup G) : Set G) \ {1} := by
    intro y hy
    simp only [Set.mem_iUnion] at hy
    obtain ⟨ℓ, hℓ, hyW, hy1⟩ := hy
    obtain ⟨hℓl, hℓL, hℓℓ₂⟩ := (hmem₂ ℓ).mp hℓ
    exact ⟨⟨hi ℓ hℓl hℓL hyW, hW₂ ℓ hℓl hℓℓ₂ hyW⟩, hy1⟩
  have h2 := Set.ncard_le_ncard hsub2 (Set.toFinite _)
  rw [hU2, Set.ncard_sdiff_singleton_of_mem (one_mem _)] at h2
  have hprod : Nat.card (T.V ⊓ V₂ : Subgroup G) * Nat.card P.W ≤ Nat.card V₂ := by
    rw [← Nat.card_prod]
    refine Nat.card_le_card_of_injective
      (fun p => ⟨(p.1 : G) * p.2, mul_mem (p.1.2.2) (hW₂ C.line hLl (Ne.symm hℓ₂L) p.2.2)⟩) ?_
    rintro ⟨a, b⟩ ⟨a', b'⟩ hab
    have e := congrArg Subtype.val hab
    simp only at e
    have h1 : (a' : G)⁻¹ * a = b' * (b : G)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← e, mul_inv_cancel_right]
    have h3 : (a' : G)⁻¹ * a ∈ P.W := h1 ▸ mul_mem b'.2 (inv_mem b.2)
    have h4 := T.eq_one_of_mem_W h (mul_mem (inv_mem a'.2.1) a.2.1) h3
    have haa : a = a' := Subtype.ext (inv_mul_eq_one.mp h4).symm
    subst haa
    have hbb : (b : G) = b' := mul_left_cancel e
    rw [Subtype.ext hbb]
  have hcard_eq : (((T.V ⊓ V₂ : Subgroup G) : Set G)).ncard = Nat.card (T.V ⊓ V₂ : Subgroup G) :=
    (Nat.card_coe_set_eq _).symm
  rw [hcard_eq] at h2
  rw [hV₂] at hprod
  have hVpos : 1 ≤ Nat.card T.V := Nat.card_pos
  have hIpos : 1 ≤ Nat.card (T.V ⊓ V₂ : Subgroup G) := Nat.card_pos
  generalize Nat.card T.V = Q at hq hprod hVpos
  generalize Nat.card (T.V ⊓ V₂ : Subgroup G) = I at h2 hprod hIpos
  generalize Nat.card P.W = w at hq hprod h2 hw2
  generalize F₁.card = f₁ at hq hF₂
  generalize F₂.card = f₂ at h2 hF₂ hF₂pos
  obtain ⟨a, rfl⟩ : ∃ a, w = a + 2 := ⟨w - 2, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, f₂ = m + 1 := ⟨f₂ - 1, by omega⟩
  subst hF₂
  simp only [show a + 2 - 1 = a + 1 by omega] at hq h2
  obtain ⟨Q, rfl⟩ : ∃ Q', Q = Q' + 1 := ⟨Q - 1, by omega⟩
  obtain ⟨I, rfl⟩ : ∃ I', I = I' + 1 := ⟨I - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hq h2
  have h3 := Nat.mul_le_mul_right (a + 2) h2
  have h4 : 0 < (m + 1) * (a + 1) * (a + 1) := by positivity
  nlinarith

end P95Data

end Count

end P49Config

end CFSG.Holt.H78
