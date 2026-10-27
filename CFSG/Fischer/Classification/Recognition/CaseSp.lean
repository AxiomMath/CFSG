module

public import CFSG.Fischer.Classification.Recognition.SpUBasic
public import CFSG.Fischer.Classification.Skeleton
public import CFSG.Fischer.Classification.Symplectic.OrthoGenSymplectic

public section

namespace CFSG.Fischer.Classification.Recognition.SpU.Sp

open CFSG.Open Matrix

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem add_self_zmod2 (a : ZMod 2) : a + a = 0 := by
  revert a
  decide

theorem add_self_vec {ι : Type} (z : ι → ZMod 2) : z + z = 0 := by
  funext i
  exact add_self_zmod2 (z i)

theorem eq_of_add_eq_zero_zmod2 {a c : ZMod 2} (h : a + c = 0) : a = c := by
  revert a c
  decide

theorem eq_one_of_ne_zero_zmod2 {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  revert a
  decide

variable {ι : Type} [Fintype ι] [DecidableEq ι] {b : LinearMap.BilinForm (ZMod 2) (ι → ZMod 2)}

noncomputable abbrev SpH (b : LinearMap.BilinForm (ZMod 2) (ι → ZMod 2)) :
    Subgroup (GL ι (ZMod 2)) :=
  fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y

noncomputable def act (g : SpH b) (x : ι → ZMod 2) : ι → ZMod 2 :=
  ((g : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ x

theorem act_mul (g h : SpH b) (x : ι → ZMod 2) : act (g * h) x = act g (act h x) := by
  simp only [act, Subgroup.coe_mul, Units.val_mul, Matrix.mulVec_mulVec]

theorem act_one (x : ι → ZMod 2) : act (1 : SpH b) x = x := by
  simp only [act, OneMemClass.coe_one, Units.val_one, Matrix.one_mulVec]

theorem act_add (g : SpH b) (x y : ι → ZMod 2) : act g (x + y) = act g x + act g y :=
  Matrix.mulVec_add _ _ _

theorem act_smul (g : SpH b) (c : ZMod 2) (x : ι → ZMod 2) : act g (c • x) = c • act g x :=
  Matrix.mulVec_smul _ _ _

theorem act_zero (g : SpH b) : act g 0 = 0 := Matrix.mulVec_zero _

theorem act_inv_act (g : SpH b) (x : ι → ZMod 2) : act g⁻¹ (act g x) = x := by
  rw [← act_mul, inv_mul_cancel, act_one]

theorem act_act_inv (g : SpH b) (x : ι → ZMod 2) : act g (act g⁻¹ x) = x := by
  rw [← act_mul, mul_inv_cancel, act_one]

theorem act_ext {g h : SpH b} (e : ∀ x, act g x = act h x) : g = h :=
  Subtype.ext (Units.ext (Matrix.ext_of_mulVec_single fun _ => e _))

theorem b_act_act (g : SpH b) (x y : ι → ZMod 2) : b (act g x) (act g y) = b x y :=
  (mem_fischerMatrixGroup_bilin_iff b g).1 g.2 x y

theorem b_act_left {g : SpH b} {v : ι → ZMod 2} (hg : act g v = v) (x : ι → ZMod 2) :
    b (act g x) v = b x v := by
  conv_lhs => rw [← hg]
  exact b_act_act g x v

omit [Fintype ι] [DecidableEq ι] in
theorem b_symm (halt : ∀ x, b x x = 0) (x y : ι → ZMod 2) : b x y = b y x := by
  have h := halt (x + y)
  simp only [map_add, LinearMap.add_apply, halt x, halt y, zero_add, add_zero] at h
  exact (eq_of_add_eq_zero_zmod2 h).symm

omit [Fintype ι] [DecidableEq ι] in
theorem exists_b_eq_one (halt : ∀ x, b x x = 0) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    {v : ι → ZMod 2} (hv : v ≠ 0) : ∃ y, b y v = 1 := by
  by_contra h
  apply hv
  refine hnd v fun y => ?_
  by_contra hy
  exact h ⟨y, by rw [b_symm halt]; exact eq_one_of_ne_zero_zmod2 hy⟩

noncomputable def QSp (b : LinearMap.BilinForm (ZMod 2) (ι → ZMod 2)) (v : ι → ZMod 2) :
    Subgroup (SpH b) where
  carrier := {g | act g v = v ∧ ∀ y, b y v = 0 → ∃ c : ZMod 2, act g y = y + c • v}
  one_mem' := ⟨act_one v, fun y _ => ⟨0, by rw [act_one, zero_smul, add_zero]⟩⟩
  mul_mem' := by
    rintro g h ⟨hgv, hg⟩ ⟨hhv, hh⟩
    refine ⟨by rw [act_mul, hhv, hgv], fun y hy => ?_⟩
    obtain ⟨c, hc⟩ := hh y hy
    obtain ⟨c', hc'⟩ := hg y hy
    exact ⟨c' + c, by rw [act_mul, hc, act_add, act_smul, hgv, hc', add_smul, add_assoc]⟩
  inv_mem' := by
    rintro g ⟨hgv, hg⟩
    have hv' : act g⁻¹ v = v := by
      conv_lhs => rw [← hgv]
      exact act_inv_act g v
    refine ⟨hv', fun y hy => ?_⟩
    obtain ⟨c, hc⟩ := hg (act g⁻¹ y) (by rw [b_act_left hv', hy])
    rw [act_act_inv] at hc
    refine ⟨c, ?_⟩
    calc act g⁻¹ y = act g⁻¹ y + c • v + c • v := by rw [add_assoc, add_self_vec, add_zero]
      _ = y + c • v := by rw [← hc]

theorem pow_four_eq_one {g : SpH b} {v : ι → ZMod 2} (hgv : act g v = v)
    (hg : ∀ y, b y v = 0 → ∃ c : ZMod 2, act g y = y + c • v) : g ^ 4 = 1 := by
  have h2 : ∀ x, ∃ e : ZMod 2, act g (act g x) = x + e • v := by
    intro x
    have ha : b (act g x + x) v = 0 := by
      rw [map_add, LinearMap.add_apply, b_act_left hgv, add_self_zmod2]
    obtain ⟨e, he⟩ := hg _ ha
    refine ⟨e, ?_⟩
    have hx : act g x = x + (act g x + x) := by
      rw [add_comm x, add_assoc, add_self_vec, add_zero]
    calc act g (act g x) = act g (x + (act g x + x)) := by rw [← hx]
      _ = (x + (act g x + x)) + (act g x + x + e • v) := by rw [act_add, ← hx, he]
      _ = x + e • v + ((act g x + x) + (act g x + x)) := by abel
      _ = x + e • v := by rw [add_self_vec, add_zero]
  refine act_ext fun x => ?_
  obtain ⟨e, he⟩ := h2 x
  have h4 : act (g ^ 4) x = act g (act g (act g (act g x))) := by
    simp only [pow_succ, pow_zero, one_mul, act_mul]
  rw [h4, he, act_add, act_add, act_smul, act_smul, hgv, hgv, he, act_one, add_assoc,
    add_self_vec, add_zero]

section Transvection

variable (halt : ∀ x, b x x = 0)

noncomputable def tr (w : ι → ZMod 2) : SpH b :=
  ⟨sympTransvectionGL b halt w, sympTransvectionGL_mem_fischerMatrixGroup w⟩

theorem act_tr (w x : ι → ZMod 2) : act (tr halt w) x = x + b x w • w :=
  sympTransvectionGL_mulVec w x

theorem act_tr_mul_tr {v w : ι → ZMod 2} (hw : b w v = 0) {y : ι → ZMod 2} (hy : b y v = 0) :
    act (tr halt w * tr halt (w + v)) y = y + b y w • v := by
  have hww : b (w + v) w = 0 := by
    rw [map_add, LinearMap.add_apply, halt w, b_symm halt v w, hw, add_zero]
  rw [act_mul, act_tr, act_tr, map_add, hy, add_zero, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, hww, smul_zero, add_zero]
  calc y + b y w • (w + v) + b y w • w = y + b y w • v + (b y w • w + b y w • w) := by
        rw [smul_add]; abel
    _ = y + b y w • v := by rw [add_self_vec, add_zero]

theorem tr_mul_tr_mem_QSp {v w : ι → ZMod 2} (hw : b w v = 0) :
    tr halt w * tr halt (w + v) ∈ QSp b v := by
  refine ⟨?_, fun y hy => ⟨b y w, act_tr_mul_tr halt hw hy⟩⟩
  have hvv : b v (w + v) = 0 := by
    rw [map_add, b_symm halt v w, hw, halt v, add_zero]
  rw [act_mul, act_tr halt (w + v) v, hvv, zero_smul, add_zero, act_tr, b_symm halt v w, hw,
    zero_smul, add_zero]

end Transvection

section Centralizer

variable (halt : ∀ x, b x x = 0) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
  {t : SpH b} {v : ι → ZMod 2} (hv : v ≠ 0) (ht : ∀ x, act t x = x + b x v • v)

include halt hnd hv ht in
theorem act_eq_of_mem_centralizer {c : SpH b} (hc : c ∈ Subgroup.centralizer {t}) :
    act c v = v := by
  obtain ⟨y₀, hy₀⟩ := exists_b_eq_one halt hnd hv
  have e := congrArg (fun g => act g y₀) (Subgroup.mem_centralizer_singleton_iff.1 hc)
  simp only [act_mul, ht, hy₀, one_smul, act_add] at e
  have e' : act c v = b (act c y₀) v • v := add_left_cancel e
  rcases eq_or_ne (b (act c y₀) v) 0 with h0 | h1
  · exfalso
    apply hv
    rw [h0, zero_smul] at e'
    rw [← act_inv_act c v, e', act_zero]
  · rw [e', eq_one_of_ne_zero_zmod2 h1, one_smul]

include ht in
theorem QSp_le_centralizer : QSp b v ≤ Subgroup.centralizer {t} := by
  rintro g ⟨hgv, -⟩
  refine Subgroup.mem_centralizer_singleton_iff.2 (act_ext fun x => ?_)
  rw [act_mul, act_mul, ht, ht, act_add, act_smul, hgv, b_act_left hgv]

include halt hnd hv ht in
theorem conj_mem_QSp {c g : SpH b} (hc : c ∈ Subgroup.centralizer {t}) (hg : g ∈ QSp b v) :
    c * g * c⁻¹ ∈ QSp b v := by
  have hcv := act_eq_of_mem_centralizer halt hnd hv ht hc
  have hcv' : act c⁻¹ v = v := by
    conv_lhs => rw [← hcv]
    exact act_inv_act c v
  obtain ⟨hgv, hg⟩ := hg
  refine ⟨by rw [act_mul, act_mul, hcv', hgv, hcv], fun y hy => ?_⟩
  obtain ⟨e, he⟩ := hg (act c⁻¹ y) (by rw [b_act_left hcv', hy])
  exact ⟨e, by rw [act_mul, act_mul, he, act_add, act_smul, act_act_inv, hcv]⟩

include halt hnd hv ht in
theorem mem_QSp_of_commute {c : SpH b} (hc : c ∈ Subgroup.centralizer {t})
    (hcQ : ∀ x ∈ QSp b v, c * x = x * c) : c ∈ QSp b v := by
  have hcv := act_eq_of_mem_centralizer halt hnd hv ht hc
  refine ⟨hcv, fun y hy => ?_⟩
  set z := act c y + y with hz
  have hzu : ∀ u, b u v = 0 → b z u = 0 := by
    intro u hu
    have e := congrArg (fun g => act g y) (hcQ _ (tr_mul_tr_mem_QSp halt hu))
    simp only [act_mul] at e
    rw [← act_mul (tr halt u), act_tr_mul_tr halt hu hy, act_add, act_smul, hcv,
      ← act_mul (tr halt u), act_tr_mul_tr halt hu (by rw [b_act_left hcv, hy]),
      add_right_inj] at e
    have e' : b y u = b (act c y) u := smul_left_injective (ZMod 2) hv e
    rw [hz, map_add, LinearMap.add_apply, ← e', add_self_zmod2]
  obtain ⟨y₀, hy₀⟩ := exists_b_eq_one halt hnd hv
  refine ⟨b z y₀, ?_⟩
  have hzv : z + b z y₀ • v = 0 := by
    refine hnd _ fun x => ?_
    have hx : b (x + b x v • y₀) v = 0 := by
      rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hy₀, smul_eq_mul,
        mul_one, add_self_zmod2]
    have h := hzu _ hx
    rw [map_add, map_smul, smul_eq_mul] at h
    rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      b_symm halt v x]
    linear_combination h
  have hz' : z = b z y₀ • v := by
    calc z = z + b z y₀ • v + b z y₀ • v := by rw [add_assoc, add_self_vec, add_zero]
      _ = b z y₀ • v := by rw [hzv, zero_add]
  calc act c y = z + y := by rw [hz, add_assoc, add_self_vec, add_zero]
    _ = y + b z y₀ • v := by
      conv_lhs => rw [hz']
      rw [add_comm]

end Centralizer

theorem not_isComponentOf_centralizer (halt : ∀ x, b x x = 0)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) {t : SpH b}
    (ht : (t : GL ι (ZMod 2)) ∈ fischerTransvections (fun x y => b x y) fun v => v ≠ 0)
    (K : Subgroup (SpH b)) : ¬ IsComponentOf K (Subgroup.centralizer {t}) := by
  intro hK
  obtain ⟨v, hv, htv⟩ := ht
  have ht' : ∀ x, act t x = x + b x v • v := htv
  refine SpU.not_isComponentOf hK (QSp_le_centralizer ht')
    (fun c hc g hg => conj_mem_QSp halt hnd hv ht' hc hg)
    (fun g hg => pow_four_eq_one hg.1 hg.2) fun c hc hcQ => ?_
  have h := mem_QSp_of_commute halt hnd hv ht' hc hcQ
  exact pow_four_eq_one h.1 h.2

end CFSG.Fischer.Classification.Recognition.SpU.Sp

namespace CFSG.Fischer.Classification.Recognition

open CFSG.Open Matrix

theorem not_isComponentOf_case2 {G : Type} [Group G] {D : Set G}
    (hN : ∃ m : ℕ, 2 ≤ m ∧ ∃ b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2),
      (∀ x, b x x = 0) ∧ (∀ x, (∀ y, b x y = 0) → x = 0) ∧
      fischerLinearModel D
        (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y)
        (fischerTransvections (fun x y => b x y) fun v => v ≠ 0))
    {d : G} (hd : d ∈ D) (K : Subgroup G) :
    ¬ IsComponentOf K (Subgroup.centralizer ({d} : Set G)) := by
  intro hK
  obtain ⟨m, -, b, halt, hnd, φ, hφ⟩ := hN
  have h := IsComponentOf.map_mulEquiv φ hK
  rw [map_centralizer_singleton] at h
  exact SpU.Sp.not_isComponentOf_centralizer halt hnd ((hφ d).1 hd) _ h

theorem componentOrder_case2 {G : Type} [Group G] [Finite G] {D : Set G} (_hH : Hyp G D)
    (hN : ∃ m : ℕ, 2 ≤ m ∧ ∃ b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2),
      (∀ x, b x x = 0) ∧ (∀ x, (∀ y, b x y = 0) → x = 0) ∧
      fischerLinearModel D
        (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y)
        (fischerTransvections (fun x y => b x y) fun v => v ≠ 0))
    {d : G} (hd : d ∈ D) {K : Subgroup G}
    (hK : IsComponentOf K (Subgroup.centralizer ({d} : Set G))) :
    Nat.card (K ⧸ Subgroup.center K) ∉ fischerComponentOrders :=
  (not_isComponentOf_case2 hN hd K hK).elim

end CFSG.Fischer.Classification.Recognition
