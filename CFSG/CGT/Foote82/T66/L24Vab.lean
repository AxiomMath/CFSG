module

public import CFSG.CGT.Foote82.T66.L24Lines
import CFSG.CGT.Foote82.T66.MC2Perm
import CFSG.Quasithin.Background.G11Basic

public section

namespace CFSG.CGT.Foote82.L24

open CFSG.Open CFSG.Quasithin.G11 Equiv Equiv.Perm

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {G : Subgroup (GLV V)} {N : ℕ}

section Trans

variable (φ : ↥G ≃* alternatingGroup (Fin N))

theorem exists_map_list {l l' : List (Fin N)} (hl : l.Nodup) (hl' : l'.Nodup)
    (hlen : l.length = l'.length) (hN : l.length + 2 ≤ N) : ∃ g : ↥G, l.map (pm φ g) = l' := by
  classical
  let x : Fin l.length ↪ Fin N := ⟨l.get, List.nodup_iff_injective_get.1 hl⟩
  let y : Fin l.length ↪ Fin N := ⟨fun i => l'.get (Fin.cast hlen i),
    (List.nodup_iff_injective_get.1 hl').comp (Fin.cast_injective hlen)⟩
  haveI := alternatingGroup.isMultiplyPretransitive (α := Fin N)
  have hk : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin N)) (Fin N) l.length :=
    MulAction.isMultiplyPretransitive_of_le (n := Nat.card (Fin N) - 2)
      (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega) (Nat.sub_le _ _)
  obtain ⟨σ, hσ⟩ := MulAction.isMultiplyPretransitive_iff.1 hk x y
  refine ⟨φ.symm σ, List.ext_getElem (by simp [hlen]) fun i h1 h2 => ?_⟩
  have := congrArg (fun f : Fin l.length ↪ Fin N => f ⟨i, by simpa using h1⟩) hσ
  simp only [Function.Embedding.smul_apply] at this
  rw [List.getElem_map]
  have e : ∀ k, pm φ (φ.symm σ) k = (σ : Perm (Fin N)) k := fun k => by simp [pm]
  rw [e]
  exact this

theorem nodup4 {a b c d : Fin N} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) : [a, b, c, d].Nodup := by
  simp [hab, hac, had, hbc, hbd, hcd]

end Trans

section Uniq

@[expose] def UniqV (U : Submodule (ZMod 2) V) (v : V) : Prop :=
  v ∈ U ∧ v ≠ 0 ∧ ∀ y ∈ U, y = 0 ∨ y = v

theorem UniqV.unique {U : Submodule (ZMod 2) V} {v v' : V} (h : UniqV U v) (h' : UniqV U v') :
    v = v' :=
  ((h.2.2 v' h'.1).resolve_left h'.2.1).symm

theorem UniqV.of_eq {U U' : Submodule (ZMod 2) V} (e : U = U') {v : V} (h : UniqV U v) :
    UniqV U' v := e ▸ h

variable {φ : ↥G ≃* alternatingGroup (Fin N)}

theorem coe_inv_apply (g : ↥G) (y : V) : (g : GLV V) (((g⁻¹ : ↥G) : GLV V) y) = y := by
  simp

theorem uniqV_conj (g : ↥G) {a b c d : Fin N} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) {v : V}
    (hv : UniqV (I4 φ a b c d) v) :
    UniqV (I4 φ (pm φ g a) (pm φ g b) (pm φ g c) (pm φ g d)) ((g : GLV V) v) := by
  have hinj := (pm φ g).injective
  refine ⟨⟨apply_mem_Rg_T3 φ g hab hac hv.1.1, apply_mem_Rg_T3 φ g hab had hv.1.2⟩,
    fun h0 => hv.2.1 (((g : GLV V).map_eq_zero_iff).1 h0), fun y hy => ?_⟩
  have hab' : pm φ g a ≠ pm φ g b := fun e => hab (hinj e)
  have hac' : pm φ g a ≠ pm φ g c := fun e => hac (hinj e)
  have had' : pm φ g a ≠ pm φ g d := fun e => had (hinj e)
  have hinv : ∀ k, pm φ g⁻¹ (pm φ g k) = k := fun k => by
    rw [pm_inv]
    simp
  have hy' : ((g⁻¹ : ↥G) : GLV V) y ∈ I4 φ a b c d := by
    have h1 := apply_mem_Rg_T3 φ g⁻¹ hab' hac' hy.1
    have h2 := apply_mem_Rg_T3 φ g⁻¹ hab' had' hy.2
    rw [hinv, hinv, hinv] at h1
    rw [hinv, hinv, hinv] at h2
    exact ⟨h1, h2⟩
  rcases hv.2.2 _ hy' with h0 | h1
  · left
    rw [← coe_inv_apply g y, h0, map_zero]
  · right
    rw [← coe_inv_apply g y, h1]

theorem I4_swap {a b c d : Fin N} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) : I4 φ b a c d = I4 φ a b c d := by
  rw [I4, I4, Rg_T3_swap φ hab hac hbc, Rg_T3_swap φ hab had hbd]

theorem I4_comm (a b c d : Fin N) : I4 φ a b d c = I4 φ a b c d := by
  rw [I4, I4, inf_comm]

end Uniq

section Lines

variable {φ : ↥G ≃* alternatingGroup (Fin N)} {F : Finset (Fin N)}
  {θ : (Fin N → ZMod 2) →ₗ[ZMod 2] V}

theorem exists_five (hF : 5 ≤ F.card) :
    ∃ f₀ ∈ F, ∃ f₁ ∈ F, ∃ f₂ ∈ F, ∃ f₃ ∈ F, ∃ f₄ ∈ F, [f₀, f₁, f₂, f₃, f₄].Nodup := by
  obtain ⟨f₀, h₀, -⟩ := exists_mem_not_mem_list (S := F) []
      (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨f₁, h₁, n₁⟩ := exists_mem_not_mem_list (S := F) [f₀]
      (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨f₂, h₂, n₂⟩ := exists_mem_not_mem_list (S := F) [f₀, f₁]
      (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨f₃, h₃, n₃⟩ := exists_mem_not_mem_list (S := F) [f₀, f₁, f₂]
      (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨f₄, h₄, n₄⟩ := exists_mem_not_mem_list (S := F) [f₀, f₁, f₂, f₃]
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨f₀, h₀, f₁, h₁, f₂, h₂, f₃, h₃, f₄, h₄, ?_⟩
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or,
    not_false_eq_true] at n₁ n₂ n₃ n₄
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true, not_false_eq_true]
  refine ⟨⟨fun h => n₁ h.symm, fun h => n₂.1 h.symm, fun h => n₃.1 h.symm, fun h => n₄.1 h.symm⟩,
    ⟨fun h => n₂.2 h.symm, fun h => n₃.2.1 h.symm, fun h => n₄.2.1 h.symm⟩,
    ⟨fun h => n₃.2.2 h.symm, fun h => n₄.2.2.1 h.symm⟩, fun h => n₄.2.2.2 h.symm⟩

theorem HeartW.base_one (h : HeartW φ F θ) {f₀ f₁ f₂ f₃ f₄ : Fin N} (h₀ : f₀ ∈ F) (h₁ : f₁ ∈ F)
    (h₂ : f₂ ∈ F) (h₃ : f₃ ∈ F) (h₄ : f₄ ∈ F) (hnd : [f₀, f₁, f₂, f₃, f₄].Nodup) :
    ∃ x, UniqV (I4 φ f₀ f₁ f₂ f₃) x ∧ UniqV (I4 φ f₀ f₁ f₂ f₄) x := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true, not_false_eq_true] at hnd
  obtain ⟨⟨h01, h02, h03, h04⟩, ⟨h12, h13, h14⟩, ⟨h23, h24⟩, h34⟩ := hnd
  obtain ⟨x, hx, hxT, hx0, hxu⟩ :=
    h.exists_vF h₀ h₁ h₂ h₃ h₄ h01 h02 h03 h04 h12 h13 h14 h23 h24 h34
  obtain ⟨x', hx', hxT', hx0', hxu'⟩ :=
    h.exists_vF h₀ h₁ h₂ h₄ h₃ h01 h02 h04 h03 h12 h14 h13 h24 h23 (Ne.symm h34)
  have e : x' = x := eq_of_mem_Rg_T3 h₀ h₁ h₂ h01 h02 h12 hx'.1 hx.1 hxT' hxT
  rw [e] at hx' hxu'
  exact ⟨x, ⟨hx, hx0, hxu⟩, ⟨hx', hx0, hxu'⟩⟩

theorem HeartW.base_add (h : HeartW φ F θ) {f₀ f₁ f₂ f₃ f₄ : Fin N} (h₀ : f₀ ∈ F) (h₁ : f₁ ∈ F)
    (h₂ : f₂ ∈ F) (h₃ : f₃ ∈ F) (h₄ : f₄ ∈ F) (hnd : [f₀, f₁, f₂, f₃, f₄].Nodup) :
    ∃ x₁ x₂ x₃, UniqV (I4 φ f₀ f₁ f₂ f₃) x₁ ∧ UniqV (I4 φ f₁ f₂ f₀ f₃) x₂ ∧
      UniqV (I4 φ f₂ f₀ f₁ f₃) x₃ ∧ x₁ + x₂ = x₃ := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true, not_false_eq_true] at hnd
  obtain ⟨⟨h01, h02, h03, h04⟩, ⟨h12, h13, h14⟩, ⟨h23, h24⟩, h34⟩ := hnd
  obtain ⟨x₁, hx₁, hT₁, h0₁, hu₁⟩ :=
    h.exists_vF h₀ h₁ h₂ h₃ h₄ h01 h02 h03 h04 h12 h13 h14 h23 h24 h34
  obtain ⟨x₂, hx₂, hT₂, h0₂, hu₂⟩ :=
    h.exists_vF h₁ h₂ h₀ h₃ h₄ h12 (Ne.symm h01) h13 h14 (Ne.symm h02) h23 h24 h03 h04 h34
  obtain ⟨x₃, hx₃, hT₃, h0₃, hu₃⟩ :=
    h.exists_vF h₂ h₀ h₁ h₃ h₄ (Ne.symm h02) (Ne.symm h12) h23 h24 h01 h03 h04 h13 h14 h34
  refine ⟨x₁, x₂, x₃, ⟨hx₁, h0₁, hu₁⟩, ⟨hx₂, h0₂, hu₂⟩, ⟨hx₃, h0₃, hu₃⟩, ?_⟩
  have hR₂ : x₂ ∈ Rg (T3 φ f₀ f₁ f₂) := by
    rw [← T3_rotate φ h01 h02 h12]
    exact hx₂.1
  have hR₃ : x₃ ∈ Rg (T3 φ f₀ f₁ f₂) := by
    rw [← T3_rotate φ h01 h02 h12, ← T3_rotate φ h12 (Ne.symm h01) (Ne.symm h02)]
    exact hx₃.1
  refine eq_of_mem_Rg_T3 h₀ h₁ h₂ h01 h02 h12 ((Rg _).add_mem hx₁.1 hR₂) hR₃ ?_ hT₃
  have e : x₁ + x₂ - θ (ev f₂ + ev f₀) =
      (x₁ - θ (ev f₀ + ev f₁)) + (x₂ - θ (ev f₁ + ev f₂)) + θ (ev f₁ + ev f₁) := by
    rw [map_add, map_add, map_add, map_add]
    abel
  rw [e, add_self, map_zero, add_zero]
  exact Submodule.add_mem _ hT₁ hT₂

theorem HeartW.exists_uniqV (h : HeartW φ F θ) (hF : 5 ≤ F.card) (hN : 7 ≤ N) {a b c d : Fin N}
    (hnd : [a, b, c, d].Nodup) : ∃ v, UniqV (I4 φ a b c d) v := by
  obtain ⟨f₀, h₀, f₁, h₁, f₂, h₂, f₃, h₃, f₄, h₄, hf⟩ := exists_five hF
  obtain ⟨x, hx, -⟩ := h.base_one h₀ h₁ h₂ h₃ h₄ hf
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true, not_false_eq_true] at hf
  obtain ⟨⟨h01, h02, h03, -⟩, ⟨h12, h13, -⟩, ⟨h23, -⟩, -⟩ := hf
  obtain ⟨g, hg⟩ := exists_map_list φ (nodup4 h01 h02 h03 h12 h13 h23) hnd rfl
    (by simp only [List.length_cons, List.length_nil]; omega)
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hg
  obtain ⟨ga, gb, gc, gd⟩ := hg
  have := uniqV_conj g h01 h02 h03 hx
  rw [ga, gb, gc, gd] at this
  exact ⟨_, this⟩

theorem HeartW.uniqV_of_uniqV (h : HeartW φ F θ) (hF : 5 ≤ F.card) (hN : 7 ≤ N)
    {a b c d d' : Fin N} (hnd : [a, b, c, d, d'].Nodup) {v : V} (hv : UniqV (I4 φ a b c d) v) :
    UniqV (I4 φ a b c d') v := by
  obtain ⟨f₀, h₀, f₁, h₁, f₂, h₂, f₃, h₃, f₄, h₄, hf⟩ := exists_five hF
  obtain ⟨x, hx, hx'⟩ := h.base_one h₀ h₁ h₂ h₃ h₄ hf
  obtain ⟨g, hg⟩ := exists_map_list φ hf hnd rfl
      (by simp only [List.length_cons, List.length_nil]; omega)
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hg
  obtain ⟨ga, gb, gc, gd, gd'⟩ := hg
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true, not_false_eq_true] at hf
  have t1 := uniqV_conj g hf.1.1 hf.1.2.1 hf.1.2.2.1 hx
  have t2 := uniqV_conj g hf.1.1 hf.1.2.1 hf.1.2.2.2 hx'
  rw [ga, gb, gc, gd] at t1
  rw [ga, gb, gc, gd'] at t2
  rwa [hv.unique t1]

theorem HeartW.add_eq_of_uniqV (h : HeartW φ F θ) (hF : 5 ≤ F.card) (hN : 7 ≤ N)
    {a b c d : Fin N} (hnd : [a, b, c, d].Nodup) {v₁ v₂ v₃ : V} (h₁ : UniqV (I4 φ a b c d) v₁)
    (h₂ : UniqV (I4 φ b c a d) v₂) (h₃ : UniqV (I4 φ c a b d) v₃) : v₁ + v₂ = v₃ := by
  obtain ⟨f₀, hf₀, f₁, hf₁, f₂, hf₂, f₃, hf₃, f₄, hf₄, hf⟩ := exists_five hF
  obtain ⟨x₁, x₂, x₃, hx₁, hx₂, hx₃, hx⟩ := h.base_add hf₀ hf₁ hf₂ hf₃ hf₄ hf
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true, not_false_eq_true] at hf
  obtain ⟨⟨h01, h02, h03, -⟩, ⟨h12, h13, -⟩, ⟨h23, -⟩, -⟩ := hf
  obtain ⟨g, hg⟩ := exists_map_list φ (nodup4 h01 h02 h03 h12 h13 h23) hnd rfl
    (by simp only [List.length_cons, List.length_nil]; omega)
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hg
  obtain ⟨ga, gb, gc, gd⟩ := hg
  have t1 := uniqV_conj g h01 h02 h03 hx₁
  have t2 := uniqV_conj g h12 (Ne.symm h01) h13 hx₂
  have t3 := uniqV_conj g (Ne.symm h02) (Ne.symm h12) h23 hx₃
  rw [ga, gb, gc, gd] at t1 t2 t3
  rw [h₁.unique t1, h₂.unique t2, h₃.unique t3, ← map_add, hx]

end Lines

section Vab

variable (φ : ↥G ≃* alternatingGroup (Fin N))

open Classical in
@[expose] noncomputable def vab (a b : Fin N) : V :=
  if h : ∃ v, ∃ c d, [a, b, c, d].Nodup ∧ UniqV (I4 φ a b c d) v then h.choose else 0

variable {φ} {F : Finset (Fin N)} {θ : (Fin N → ZMod 2) →ₗ[ZMod 2] V}

theorem vab_self (a : Fin N) : vab φ a a = (0 : V) := by
  rw [vab, dif_neg]
  rintro ⟨v, c, d, hnd, -⟩
  simp at hnd

theorem HeartW.uniqV_move (h : HeartW φ F θ) (hF : 5 ≤ F.card) (hN : 7 ≤ N)
    {a b c d d' : Fin N} (hnd : [a, b, c, d].Nodup) (hd'a : d' ≠ a) (hd'b : d' ≠ b)
    (hd'c : d' ≠ c) {v : V} (hv : UniqV (I4 φ a b c d) v) : UniqV (I4 φ a b c d') v := by
  by_cases hdd : d' = d
  · rwa [hdd]
  refine h.uniqV_of_uniqV hF hN ?_ hv
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true, not_false_eq_true] at hnd ⊢
  exact ⟨⟨hnd.1.1, hnd.1.2.1, hnd.1.2.2, Ne.symm hd'a⟩, ⟨hnd.2.1.1, hnd.2.1.2, Ne.symm hd'b⟩,
    ⟨hnd.2.2, Ne.symm hd'c⟩, Ne.symm hdd⟩

theorem HeartW.uniqV_chain (h : HeartW φ F θ) (hF : 5 ≤ F.card) (hN : 7 ≤ N)
    {a b c d c' d' : Fin N} (hnd : [a, b, c, d].Nodup) (hnd' : [a, b, c', d'].Nodup) {v : V}
    (hv : UniqV (I4 φ a b c d) v) : UniqV (I4 φ a b c' d') v := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true, not_false_eq_true] at hnd hnd'
  obtain ⟨⟨hab, hac, had⟩, ⟨hbc, hbd⟩, hcd⟩ := hnd
  obtain ⟨⟨-, hac', had'⟩, ⟨hbc', hbd'⟩, hcd'⟩ := hnd'
  have hsw : UniqV (I4 φ a b d c) v := hv.of_eq (I4_comm a b c d).symm
  by_cases hc'd : c' = d
  · rw [hc'd] at hcd' ⊢
    exact h.uniqV_move hF hN (nodup4 hab had hac hbd hbc (Ne.symm hcd)) (Ne.symm had')
      (Ne.symm hbd') (Ne.symm hcd') hsw
  · have h1 : UniqV (I4 φ a b d c') v :=
      h.uniqV_move hF hN (nodup4 hab had hac hbd hbc (Ne.symm hcd)) (Ne.symm hac')
        (Ne.symm hbc') hc'd hsw
    have h2 : UniqV (I4 φ a b c' d) v := h1.of_eq (I4_comm a b d c').symm
    exact h.uniqV_move hF hN (nodup4 hab hac' had hbc' hbd hc'd) (Ne.symm had') (Ne.symm hbd')
      (Ne.symm hcd') h2

theorem HeartW.uniqV_vab (h : HeartW φ F θ) (hF : 5 ≤ F.card) (hN : 7 ≤ N) {a b c d : Fin N}
    (hnd : [a, b, c, d].Nodup) : UniqV (I4 φ a b c d) (vab φ a b) := by
  have hex : ∃ v, ∃ c d, [a, b, c, d].Nodup ∧ UniqV (I4 φ a b c d) v := by
    obtain ⟨v, hv⟩ := h.exists_uniqV hF hN hnd
    exact ⟨v, c, d, hnd, hv⟩
  rw [vab, dif_pos hex]
  obtain ⟨c₀, d₀, hnd₀, hv₀⟩ := hex.choose_spec
  exact h.uniqV_chain hF hN hnd₀ hnd hv₀

theorem exists_two (hN : 4 ≤ N) (a b : Fin N) :
    ∃ c d : Fin N, c ≠ a ∧ c ≠ b ∧ d ≠ a ∧ d ≠ b ∧ c ≠ d := by
  obtain ⟨c, -, hc⟩ := exists_mem_not_mem_list (S := Finset.univ) [a, b]
    (by simp only [List.length_cons, List.length_nil, Finset.card_univ, Fintype.card_fin]; omega)
  obtain ⟨d, -, hd⟩ := exists_mem_not_mem_list (S := Finset.univ) [a, b, c]
    (by simp only [List.length_cons, List.length_nil, Finset.card_univ, Fintype.card_fin]; omega)
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or,
    not_false_eq_true] at hc hd
  exact ⟨c, d, hc.1, hc.2, hd.1, hd.2.1, fun h => hd.2.2 h.symm⟩

theorem HeartW.vab_ne_zero (h : HeartW φ F θ) (hF : 5 ≤ F.card) (hN : 7 ≤ N) {a b : Fin N}
    (hab : a ≠ b) : vab φ a b ≠ 0 := by
  obtain ⟨c, d, hca, hcb, hda, hdb, hcd⟩ := exists_two (by omega) a b
  exact (h.uniqV_vab hF hN (nodup4 hab (Ne.symm hca) (Ne.symm hda) (Ne.symm hcb)
    (Ne.symm hdb) hcd)).2.1

theorem HeartW.vab_comm (h : HeartW φ F θ) (hF : 5 ≤ F.card) (hN : 7 ≤ N) (a b : Fin N) :
    vab φ a b = vab φ b a := by
  by_cases hab : a = b
  · rw [hab]
  obtain ⟨c, d, hca, hcb, hda, hdb, hcd⟩ := exists_two (by omega) a b
  have h1 := h.uniqV_vab hF hN (nodup4 hab (Ne.symm hca) (Ne.symm hda) (Ne.symm hcb)
    (Ne.symm hdb) hcd)
  have h2 := h.uniqV_vab hF hN (nodup4 (Ne.symm hab) (Ne.symm hcb) (Ne.symm hdb) (Ne.symm hca)
    (Ne.symm hda) hcd)
  rw [I4_swap hab (Ne.symm hca) (Ne.symm hda) (Ne.symm hcb) (Ne.symm hdb)] at h2
  exact h1.unique h2

theorem HeartW.vab_apply (h : HeartW φ F θ) (hF : 5 ≤ F.card) (hN : 7 ≤ N) (g : ↥G)
    (a b : Fin N) : (g : GLV V) (vab φ a b) = vab φ (pm φ g a) (pm φ g b) := by
  by_cases hab : a = b
  · rw [hab, vab_self, vab_self, map_zero]
  obtain ⟨c, d, hca, hcb, hda, hdb, hcd⟩ := exists_two (by omega) a b
  have h1 := uniqV_conj g hab (Ne.symm hca) (Ne.symm hda) (h.uniqV_vab hF hN
    (nodup4 hab (Ne.symm hca) (Ne.symm hda) (Ne.symm hcb) (Ne.symm hdb) hcd))
  have hinj := (pm φ g).injective
  have h2 := h.uniqV_vab hF hN (a := pm φ g a) (b := pm φ g b) (c := pm φ g c) (d := pm φ g d)
    (nodup4 (fun e => hab (hinj e)) (fun e => hca (hinj e).symm) (fun e => hda (hinj e).symm)
      (fun e => hcb (hinj e).symm) (fun e => hdb (hinj e).symm) (fun e => hcd (hinj e)))
  exact h1.unique h2

theorem HeartW.vab_add (h : HeartW φ F θ) (hF : 5 ≤ F.card) (hN : 7 ≤ N) (a b c : Fin N) :
    vab φ a b + vab φ b c = vab φ a c := by
  by_cases hab : a = b
  · rw [hab, vab_self, zero_add]
  by_cases hbc : b = c
  · rw [hbc, vab_self, add_zero]
  by_cases hac : a = c
  · rw [← hac, vab_self, h.vab_comm hF hN b a, add_self_V]
  obtain ⟨d, -, hd⟩ := exists_mem_not_mem_list (S := Finset.univ) [a, b, c]
    (by simp only [List.length_cons, List.length_nil, Finset.card_univ, Fintype.card_fin]; omega)
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or,
    not_false_eq_true] at hd
  obtain ⟨hda, hdb, hdc⟩ := hd
  have h1 := h.uniqV_vab hF hN (nodup4 hab hac (Ne.symm hda) hbc (Ne.symm hdb) (Ne.symm hdc))
  have h2 := h.uniqV_vab hF hN (a := b) (b := c) (c := a) (d := d)
    (nodup4 hbc (Ne.symm hab) (Ne.symm hdb) (Ne.symm hac) (Ne.symm hdc) (Ne.symm hda))
  have h3 := h.uniqV_vab hF hN (a := c) (b := a) (c := b) (d := d)
    (nodup4 (Ne.symm hac) (Ne.symm hbc) (Ne.symm hdc) hab (Ne.symm hda) (Ne.symm hdb))
  rw [h.add_eq_of_uniqV hF hN (nodup4 hab hac (Ne.symm hda) hbc (Ne.symm hdb) (Ne.symm hdc))
    h1 h2 h3, h.vab_comm hF hN c a]

end Vab

section Theta

variable (φ : ↥G ≃* alternatingGroup (Fin N))

@[expose] noncomputable def thetaV (i₀ : Fin N) : (Fin N → ZMod 2) →ₗ[ZMod 2] V where
  toFun y := ∑ k, y k • vab φ k i₀
  map_add' y z := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c y := by simp [Finset.smul_sum, smul_smul]

variable {φ} {F : Finset (Fin N)} {θ : (Fin N → ZMod 2) →ₗ[ZMod 2] V}

theorem thetaV_apply (i₀ : Fin N) (y : Fin N → ZMod 2) :
    thetaV φ i₀ y = ∑ k, y k • vab φ k i₀ := rfl

theorem HeartW.thetaV_ev_add (h : HeartW φ F θ) (hF : 5 ≤ F.card) (hN : 7 ≤ N) (i₀ a b : Fin N) :
    thetaV φ i₀ (ev a + ev b) = vab φ a b := by
  by_cases hab : a = b
  · rw [hab, add_self, map_zero, vab_self]
  rw [map_add, thetaV_apply, thetaV_apply]
  simp only [ev, Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rw [h.vab_comm hF hN b i₀, h.vab_add hF hN]

theorem HeartW.apply_thetaV (h : HeartW φ F θ) (hF : 5 ≤ F.card) (hN : 7 ≤ N) (i₀ : Fin N)
    (g : ↥G) {y : Fin N → ZMod 2} (hy : ∑ k, y k = 0) :
    (g : GLV V) (thetaV φ i₀ y) = thetaV φ i₀ (pa (pm φ g) y) := by
  rw [thetaV_apply, thetaV_apply, map_sum]
  simp_rw [map_smul, h.vab_apply hF hN g]
  simp only [pa_apply]
  conv_rhs => rw [← Equiv.sum_comp (pm φ g)]
  simp only [Perm.inv_def, Equiv.symm_apply_apply]
  have e : ∀ k, vab φ (pm φ g k) (pm φ g i₀) = vab φ (pm φ g k) i₀ + vab φ i₀ (pm φ g i₀) :=
    fun k => (h.vab_add hF hN _ i₀ _).symm
  simp_rw [e, smul_add]
  rw [Finset.sum_add_distrib, ← Finset.sum_smul, hy, zero_smul, add_zero]

end Theta

section Univ

variable {φ : ↥G ≃* alternatingGroup (Fin N)}

theorem AS_univ : AS φ (Finset.univ : Finset (Fin N)) = G := by
  ext x
  rw [mem_AS]
  constructor
  · rintro ⟨g, -, rfl⟩
    exact g.2
  · intro hx
    refine ⟨⟨x, hx⟩, MC2.mem_altOn_iff.2 ⟨pm_mem_alternatingGroup φ _, fun k hk => ?_⟩, rfl⟩
    exact absurd (Finset.mem_coe.2 (Finset.mem_univ k)) hk

theorem commSpace_eq_top_fixedSpace_eq_bot (φ : ↥G ≃* alternatingGroup (Fin N)) (hN : 3 ≤ N)
    (hirr : IsIrr G ⊤) :
    commSpace G ⊤ = ⊤ ∧ fixedSpace G = ⊥ := by
  have h01 : (⟨0, by omega⟩ : Fin N) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have h02 : (⟨0, by omega⟩ : Fin N) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  set σ := cyc (⟨0, by omega⟩ : Fin N) ⟨1, by omega⟩ ⟨2, by omega⟩ with hσ
  have hσA : σ ∈ alternatingGroup (Fin N) := cyc_mem_alternatingGroup h01 h02
  have hσ1 : σ ≠ 1 := by
    intro h1
    have := cyc_apply_left (c := (⟨2, by omega⟩ : Fin N)) h01 (by simp [Fin.ext_iff])
    rw [← hσ, h1, Perm.one_apply] at this
    exact h01 this
  have hg1 : ((el φ σ hσA : ↥G) : GLV V) ≠ 1 := by
    intro h1
    apply hσ1
    rw [← pm_el φ σ hσA, show el φ σ hσA = 1 from Subtype.ext h1, pm_one]
  obtain ⟨v, hv⟩ : ∃ v, ((el φ σ hσA : ↥G) : GLV V) v ≠ v := by
    by_contra hc
    push Not at hc
    exact hg1 (LinearEquiv.ext hc)
  have hG : ∀ k' ∈ G, ∀ k ∈ G, k' * k * k'⁻¹ ∈ G := fun k' hk' k hk =>
    G.mul_mem (G.mul_mem hk' hk) (G.inv_mem hk')
  refine ⟨?_, ?_⟩
  · rcases hirr.eq_bot_or_eq (invariant_commSpace hG (invariant_top G)) le_top with h0 | ht
    · exfalso
      have : ((el φ σ hσA : ↥G) : GLV V) v - v ∈ commSpace G ⊤ :=
        sub_mem_commSpace (el φ σ hσA).2 Submodule.mem_top
      rw [h0, Submodule.mem_bot, sub_eq_zero] at this
      exact hv this
    · exact ht
  · rcases hirr.eq_bot_or_eq (invariant_fixedSpace hG) le_top with h0 | ht
    · exact h0
    · exfalso
      have : v ∈ fixedSpace G := by
        rw [ht]
        exact Submodule.mem_top
      exact hv (this _ (el φ σ hσA).2)

theorem HeartW.heartW_univ {F : Finset (Fin N)} {θ : (Fin N → ZMod 2) →ₗ[ZMod 2] V}
    (h : HeartW φ F θ) (hF : 5 ≤ F.card) (hN : 7 ≤ N) (hirr : IsIrr G ⊤) :
    HeartW φ Finset.univ (thetaV φ ⟨0, by omega⟩) := by
  obtain ⟨htop, hbot⟩ := commSpace_eq_top_fixedSpace_eq_bot φ (by omega) hirr
  have hT : tildeVBot (AS φ (Finset.univ : Finset (Fin N))) = ⊥ := by
    rw [AS_univ, tildeVBot, hbot, bot_inf_eq]
  have hW : commSpace (AS φ (Finset.univ : Finset (Fin N))) ⊤ = ⊤ := by
    rw [AS_univ, htop]
  have hcard : (Finset.univ : Finset (Fin N)).card = N := by simp
  refine heartW_of_pre (by omega) ?_ (commutator_AS φ (by omega)) (fun y _ => by
    rw [hW]; exact Submodule.mem_top) (fun g _ y hy => ?_) ?_
  · show IrrSec _ _ _
    rw [hT, hW, AS_univ]
    exact hirr.2
  · rw [h.apply_thetaV hF hN _ g hy.2, sub_self]
    exact Submodule.zero_mem _
  · have h01 : (⟨0, by omega⟩ : Fin N) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
    refine ⟨ev ⟨0, by omega⟩ + ev ⟨1, by omega⟩,
      ev_add_ev_mem_Ew (Finset.mem_univ _) (Finset.mem_univ _), ?_⟩
    rw [hT, Submodule.mem_bot, h.thetaV_ev_add hF hN]
    exact h.vab_ne_zero hF hN h01

end Univ

end CFSG.CGT.Foote82.L24
