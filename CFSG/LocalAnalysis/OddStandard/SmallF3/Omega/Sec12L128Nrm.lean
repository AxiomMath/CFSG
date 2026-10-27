module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128SplB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128WrDef

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

abbrev sec128g : Multiplicative (ZMod 2) := Multiplicative.ofAdd 1

theorem sec128_Q_cases (q : Multiplicative (ZMod 2)) : q = 1 ∨ q = sec128g := by
  revert q
  decide

theorem sec128_g_ne_one : sec128g ≠ 1 := by decide

theorem sec128_g_mul_g : sec128g * sec128g = 1 := by decide

structure Sec128Tw {M : Type} [Group M] (ρ : Sec128A5 × Sec128A5 →* MulAut M)
    (V1 V2 : Subgroup M) (τ : MulAut M) : Prop where
  sq : τ * τ = 1
  hA : ∀ a, ∃ b, τ * ρ (a, 1) * τ⁻¹ = ρ (1, b)
  hB : ∀ b, ∃ a, τ * ρ (1, b) * τ⁻¹ = ρ (a, 1)
  nz : ∀ p, τ ≠ ρ p
  sub : V1.map (τ : M ≃* M).toMonoidHom = V2

section General

variable {M : Type} [Group M] {ρ : Sec128A5 × Sec128A5 →* MulAut M} {V1 V2 : Subgroup M}
  {φ1 φ2 : (Fin 5 → ZMod 2) → M} {τ : MulAut M}

theorem Sec128Tw.inv_eq (ht : Sec128Tw ρ V1 V2 τ) : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right ht.sq

theorem Sec128Tw.apply_apply (ht : Sec128Tw ρ V1 V2 τ) (u : M) : τ (τ u) = u :=
  congrArg (fun f : MulAut M => f u) ht.sq

theorem Sec128Tw.mem_of_mem1 (ht : Sec128Tw ρ V1 V2 τ) {u : M} (hu : u ∈ V1) : τ u ∈ V2 := by
  rw [← ht.sub]
  exact ⟨u, hu, rfl⟩

theorem sec128_exists_beta (h : Sec128Spl ρ V1 V2 φ1 φ2) (ht : Sec128Tw ρ V1 V2 τ) :
    ∃ β : Sec128A5 →* Sec128A5, Function.Injective β ∧
      ∀ a, τ * ρ (a, 1) * τ⁻¹ = ρ (1, β a) := by
  choose βf hβ using ht.hA
  have hm : ∀ a b, βf (a * b) = βf a * βf b := by
    intro a b
    have h1 : ρ (1, βf (a * b)) = ρ (1, βf a * βf b) := by
      calc ρ (1, βf (a * b)) = τ * ρ (a * b, 1) * τ⁻¹ := (hβ _).symm
        _ = (τ * ρ (a, 1) * τ⁻¹) * (τ * ρ (b, 1) * τ⁻¹) := by
          rw [show ((a * b : Sec128A5), (1 : Sec128A5)) = (a, 1) * (b, 1) by simp, map_mul]
          group
        _ = ρ (1, βf a) * ρ (1, βf b) := by rw [hβ, hβ]
        _ = ρ (1, βf a * βf b) := by rw [← map_mul]; simp
    exact (Prod.mk.inj (h.inj h1)).2
  have h1 : βf 1 = 1 := by
    have := hm 1 1
    simpa using this
  refine ⟨{ toFun := βf, map_one' := h1, map_mul' := hm }, ?_, hβ⟩
  intro a a' haa
  have h2 : ρ (a, 1) = ρ (a', 1) := by
    have h3 : τ * ρ (a, 1) * τ⁻¹ = τ * ρ (a', 1) * τ⁻¹ := by
      rw [hβ, hβ]
      exact congrArg (fun x => ρ (1, x)) haa
    exact mul_left_cancel (mul_right_cancel h3)
  exact (Prod.mk.inj (h.inj h2)).1

theorem sec128_g_inv : sec128g⁻¹ = sec128g := by decide

@[expose] def sec128Psi' (ρ : Sec128A5 × Sec128A5 →* MulAut M) (β : Sec128A5 →* Sec128A5) :
    Sec128A5 × Sec128A5 →* MulAut M :=
  ρ.comp (MonoidHom.prodMap (MonoidHom.id Sec128A5) β)

theorem sec128Psi'_apply (β : Sec128A5 →* Sec128A5) (a c : Sec128A5) :
    sec128Psi' ρ β (a, c) = ρ (a, β c) := rfl

theorem sec128Psi'_mul (β : Sec128A5 →* Sec128A5) (a c a' c' : Sec128A5) :
    sec128Psi' ρ β (a * a', c * c') = sec128Psi' ρ β (a, c) * sec128Psi' ρ β (a', c') :=
  map_mul (sec128Psi' ρ β) (a, c) (a', c')

theorem sec128_tw_psi (ht : Sec128Tw ρ V1 V2 τ) {β : Sec128A5 →* Sec128A5}
    (hβ : ∀ a, τ * ρ (a, 1) * τ⁻¹ = ρ (1, β a)) (a c : Sec128A5) :
    τ * sec128Psi' ρ β (a, c) = sec128Psi' ρ β (c, a) * τ := by
  have e1 : ρ (a, β c) = ρ (a, 1) * ρ (1, β c) := by rw [← map_mul]; simp
  have e2 : τ * ρ (a, 1) = ρ (1, β a) * τ := by
    calc τ * ρ (a, 1) = (τ * ρ (a, 1) * τ⁻¹) * τ := by group
      _ = ρ (1, β a) * τ := by rw [hβ]
  have e3 : τ * ρ (1, β c) = ρ (c, 1) * τ := by
    rw [← hβ c, ht.inv_eq]
    calc τ * (τ * ρ (c, 1) * τ) = (τ * τ) * ρ (c, 1) * τ := by group
      _ = ρ (c, 1) * τ := by rw [ht.sq, one_mul]
  have e4 : ρ (1, β a) * ρ (c, 1) = ρ (c, β a) := by rw [← map_mul]; simp
  rw [sec128Psi'_apply, sec128Psi'_apply, e1]
  calc τ * (ρ (a, 1) * ρ (1, β c)) = (τ * ρ (a, 1)) * ρ (1, β c) := by group
    _ = ρ (1, β a) * (τ * ρ (1, β c)) := by rw [e2]; group
    _ = ρ (1, β a) * (ρ (c, 1) * τ) := by rw [e3]
    _ = ρ (c, β a) * τ := by rw [← mul_assoc, e4]

theorem sec128_psi_act1 (h : Sec128Spl ρ V1 V2 φ1 φ2) (β : Sec128A5 →* Sec128A5)
    (a c : Sec128A5) {v : Fin 5 → ZMod 2} (hv : IsEvenVec v) :
    sec128Psi' ρ β (a, c) (φ1 v) = φ1 (permVec (a : Equiv.Perm (Fin 5)) v) :=
  h.act1 a (β c) v hv

theorem sec128_psi_act2 (h : Sec128Spl ρ V1 V2 φ1 φ2) (ht : Sec128Tw ρ V1 V2 τ)
    {β : Sec128A5 →* Sec128A5} (hβ : ∀ a, τ * ρ (a, 1) * τ⁻¹ = ρ (1, β a))
    (a c : Sec128A5) {v : Fin 5 → ZMod 2} (hv : IsEvenVec v) :
    sec128Psi' ρ β (a, c) (τ (φ1 v)) = τ (φ1 (permVec (c : Equiv.Perm (Fin 5)) v)) := by
  have e1 : ρ (a, β c) = ρ (a, 1) * ρ (1, β c) := by rw [← map_mul]; simp
  have e2 : ρ (1, β c) = τ * ρ (c, 1) * τ := by rw [← hβ c, ht.inv_eq]
  rw [sec128Psi'_apply, e1, e2]
  show ρ (a, 1) (τ (ρ (c, 1) (τ (τ (φ1 v))))) = _
  rw [ht.apply_apply, h.act1 c 1 v hv]
  exact h.fixed1 (ht.mem_of_mem1 (h.c1.mem _ (sec128_isEven_permVec _ hv))) a

@[expose] def sec128tau (τ : MulAut M) (q : Multiplicative (ZMod 2)) : MulAut M :=
  if q = 1 then 1 else τ

theorem sec128tau_one : sec128tau τ 1 = 1 := by simp [sec128tau]

theorem sec128tau_g : sec128tau τ sec128g = τ := by simp [sec128tau, sec128_g_ne_one]

@[expose] def sec128e0 (ρ : Sec128A5 × Sec128A5 →* MulAut M) (β : Sec128A5 →* Sec128A5)
    (τ : MulAut M) (w : WrZ2 Sec128A5) : MulAut M :=
  sec128Psi' ρ β (w.left 1, w.left sec128g) * sec128tau τ w.right

theorem sec128_wr_left_one (f1 f2 : Multiplicative (ZMod 2) → Sec128A5) :
    ((f1 * fun x => f2 ((1 : Multiplicative (ZMod 2))⁻¹ * x)) 1,
      (f1 * fun x => f2 ((1 : Multiplicative (ZMod 2))⁻¹ * x)) sec128g) =
      (f1 1 * f2 1, f1 sec128g * f2 sec128g) := by
  refine Prod.ext ?_ ?_
  · show f1 1 * f2 ((1 : Multiplicative (ZMod 2))⁻¹ * 1) = f1 1 * f2 1
    rw [mul_one, inv_one]
  · show f1 sec128g * f2 ((1 : Multiplicative (ZMod 2))⁻¹ * sec128g) = f1 sec128g * f2 sec128g
    rw [inv_one, one_mul]

theorem sec128_wr_left_g (f1 f2 : Multiplicative (ZMod 2) → Sec128A5) :
    ((f1 * fun x => f2 (sec128g⁻¹ * x)) 1, (f1 * fun x => f2 (sec128g⁻¹ * x)) sec128g) =
      (f1 1 * f2 sec128g, f1 sec128g * f2 1) := by
  refine Prod.ext ?_ ?_
  · show f1 1 * f2 (sec128g⁻¹ * 1) = f1 1 * f2 sec128g
    rw [mul_one, sec128_g_inv]
  · show f1 sec128g * f2 (sec128g⁻¹ * sec128g) = f1 sec128g * f2 1
    rw [inv_mul_cancel]

theorem sec128e0_mul (ht : Sec128Tw ρ V1 V2 τ) {β : Sec128A5 →* Sec128A5}
    (hβ : ∀ a, τ * ρ (a, 1) * τ⁻¹ = ρ (1, β a)) (w1 w2 : WrZ2 Sec128A5) :
    sec128e0 ρ β τ (w1 * w2) = sec128e0 ρ β τ w1 * sec128e0 ρ β τ w2 := by
  obtain ⟨f1, s1⟩ := w1
  obtain ⟨f2, s2⟩ := w2
  have tw := sec128_tw_psi ht hβ (f2 1) (f2 sec128g)
  have hm1 := sec128Psi'_mul (ρ := ρ) β (f1 1) (f1 sec128g) (f2 1) (f2 sec128g)
  have hm2 := sec128Psi'_mul (ρ := ρ) β (f1 1) (f1 sec128g) (f2 sec128g) (f2 1)
  rcases sec128_Q_cases s1 with rfl | rfl <;> rcases sec128_Q_cases s2 with rfl | rfl
  · show sec128Psi' ρ β ((f1 * fun x => f2 ((1 : Multiplicative (ZMod 2))⁻¹ * x)) 1,
        (f1 * fun x => f2 ((1 : Multiplicative (ZMod 2))⁻¹ * x)) sec128g) *
        sec128tau τ (1 * 1) =
      (sec128Psi' ρ β (f1 1, f1 sec128g) * sec128tau τ 1) *
        (sec128Psi' ρ β (f2 1, f2 sec128g) * sec128tau τ 1)
    rw [sec128_wr_left_one]
    simp only [sec128tau_one, mul_one]
    exact hm1
  · show sec128Psi' ρ β ((f1 * fun x => f2 ((1 : Multiplicative (ZMod 2))⁻¹ * x)) 1,
        (f1 * fun x => f2 ((1 : Multiplicative (ZMod 2))⁻¹ * x)) sec128g) *
        sec128tau τ (1 * sec128g) =
      (sec128Psi' ρ β (f1 1, f1 sec128g) * sec128tau τ 1) *
        (sec128Psi' ρ β (f2 1, f2 sec128g) * sec128tau τ sec128g)
    rw [sec128_wr_left_one]
    simp only [sec128tau_one, sec128tau_g, mul_one, one_mul]
    rw [hm1, mul_assoc]
  · show sec128Psi' ρ β ((f1 * fun x => f2 (sec128g⁻¹ * x)) 1,
        (f1 * fun x => f2 (sec128g⁻¹ * x)) sec128g) * sec128tau τ (sec128g * 1) =
      (sec128Psi' ρ β (f1 1, f1 sec128g) * sec128tau τ sec128g) *
        (sec128Psi' ρ β (f2 1, f2 sec128g) * sec128tau τ 1)
    rw [sec128_wr_left_g]
    simp only [sec128tau_one, sec128tau_g, mul_one]
    calc sec128Psi' ρ β (f1 1 * f2 sec128g, f1 sec128g * f2 1) * τ
        = sec128Psi' ρ β (f1 1, f1 sec128g) * (sec128Psi' ρ β (f2 sec128g, f2 1) * τ) := by
          rw [hm2, mul_assoc]
      _ = sec128Psi' ρ β (f1 1, f1 sec128g) * (τ * sec128Psi' ρ β (f2 1, f2 sec128g)) := by
          rw [tw]
      _ = sec128Psi' ρ β (f1 1, f1 sec128g) * τ * sec128Psi' ρ β (f2 1, f2 sec128g) :=
          (mul_assoc _ _ _).symm
  · show sec128Psi' ρ β ((f1 * fun x => f2 (sec128g⁻¹ * x)) 1,
        (f1 * fun x => f2 (sec128g⁻¹ * x)) sec128g) * sec128tau τ (sec128g * sec128g) =
      (sec128Psi' ρ β (f1 1, f1 sec128g) * sec128tau τ sec128g) *
        (sec128Psi' ρ β (f2 1, f2 sec128g) * sec128tau τ sec128g)
    rw [sec128_wr_left_g]
    simp only [sec128tau_one, sec128tau_g, mul_one, sec128_g_mul_g]
    calc sec128Psi' ρ β (f1 1 * f2 sec128g, f1 sec128g * f2 1)
        = sec128Psi' ρ β (f1 1, f1 sec128g) * sec128Psi' ρ β (f2 sec128g, f2 1) := hm2
      _ = sec128Psi' ρ β (f1 1, f1 sec128g) * (sec128Psi' ρ β (f2 sec128g, f2 1) * (τ * τ)) := by
          rw [ht.sq, mul_one]
      _ = sec128Psi' ρ β (f1 1, f1 sec128g) *
            ((sec128Psi' ρ β (f2 sec128g, f2 1) * τ) * τ) := by rw [mul_assoc]
      _ = sec128Psi' ρ β (f1 1, f1 sec128g) *
            ((τ * sec128Psi' ρ β (f2 1, f2 sec128g)) * τ) := by rw [tw]
      _ = sec128Psi' ρ β (f1 1, f1 sec128g) * τ * (sec128Psi' ρ β (f2 1, f2 sec128g) * τ) := by
          rw [mul_assoc, ← mul_assoc τ, mul_assoc]
          group

@[expose] def sec128E (ht : Sec128Tw ρ V1 V2 τ) {β : Sec128A5 →* Sec128A5}
    (hβ : ∀ a, τ * ρ (a, 1) * τ⁻¹ = ρ (1, β a)) : WrZ2 Sec128A5 →* MulAut M where
  toFun := sec128e0 ρ β τ
  map_one' := by
    show sec128Psi' ρ β ((1 : WrZ2 Sec128A5).left 1, (1 : WrZ2 Sec128A5).left sec128g) *
      sec128tau τ (1 : WrZ2 Sec128A5).right = 1
    rw [show (1 : WrZ2 Sec128A5).right = 1 from rfl, sec128tau_one, mul_one]
    exact map_one (sec128Psi' ρ β)
  map_mul' := sec128e0_mul ht hβ

@[expose] def sec128phi (φ1 : (Fin 5 → ZMod 2) → M) (τ : MulAut M)
    (q : Multiplicative (ZMod 2)) (v : Fin 5 → ZMod 2) : M :=
  if q = 1 then φ1 v else τ (φ1 v)

theorem sec128phi_one (v : Fin 5 → ZMod 2) : sec128phi φ1 τ 1 v = φ1 v := if_pos rfl

theorem sec128phi_g (v : Fin 5 → ZMod 2) : sec128phi φ1 τ sec128g v = τ (φ1 v) :=
  if_neg sec128_g_ne_one

@[expose] def sec128Vq (V1 V2 : Subgroup M) (q : Multiplicative (ZMod 2)) : Subgroup M :=
  if q = 1 then V1 else V2

theorem sec128Vq_one : sec128Vq V1 V2 1 = V1 := if_pos rfl

theorem sec128Vq_g : sec128Vq V1 V2 sec128g = V2 := if_neg sec128_g_ne_one

theorem sec128e0_act (h : Sec128Spl ρ V1 V2 φ1 φ2) (ht : Sec128Tw ρ V1 V2 τ)
    {β : Sec128A5 →* Sec128A5} (hβ : ∀ a, τ * ρ (a, 1) * τ⁻¹ = ρ (1, β a))
    (w : WrZ2 Sec128A5) (q : Multiplicative (ZMod 2)) {v : Fin 5 → ZMod 2} (hv : IsEvenVec v) :
    sec128e0 ρ β τ w (sec128phi φ1 τ q v) =
      sec128phi φ1 τ (w.right * q)
        (permVec ((w.left (w.right * q) : Sec128A5) : Equiv.Perm (Fin 5)) v) := by
  obtain ⟨f, s⟩ := w
  rcases sec128_Q_cases s with rfl | rfl <;> rcases sec128_Q_cases q with rfl | rfl
  · show (sec128Psi' ρ β (f 1, f sec128g) * sec128tau τ 1) (sec128phi φ1 τ 1 v) =
      sec128phi φ1 τ (1 * 1) (permVec ((f (1 * 1) : Sec128A5) : Equiv.Perm (Fin 5)) v)
    rw [sec128tau_one, mul_one, mul_one, sec128phi_one, sec128phi_one]
    exact sec128_psi_act1 h β _ _ hv
  · show (sec128Psi' ρ β (f 1, f sec128g) * sec128tau τ 1) (sec128phi φ1 τ sec128g v) =
      sec128phi φ1 τ (1 * sec128g) (permVec ((f (1 * sec128g) : Sec128A5) : Equiv.Perm (Fin 5)) v)
    rw [sec128tau_one, mul_one, one_mul, sec128phi_g, sec128phi_g]
    exact sec128_psi_act2 h ht hβ _ _ hv
  · show (sec128Psi' ρ β (f 1, f sec128g) * sec128tau τ sec128g) (sec128phi φ1 τ 1 v) =
      sec128phi φ1 τ (sec128g * 1) (permVec ((f (sec128g * 1) : Sec128A5) : Equiv.Perm (Fin 5)) v)
    rw [sec128tau_g, mul_one, sec128phi_one, sec128phi_g]
    exact sec128_psi_act2 h ht hβ _ _ hv
  · show (sec128Psi' ρ β (f 1, f sec128g) * sec128tau τ sec128g) (sec128phi φ1 τ sec128g v) =
      sec128phi φ1 τ (sec128g * sec128g)
        (permVec ((f (sec128g * sec128g) : Sec128A5) : Equiv.Perm (Fin 5)) v)
    rw [sec128tau_g, sec128_g_mul_g, sec128phi_g, sec128phi_one]
    show sec128Psi' ρ β (f 1, f sec128g) (τ (τ (φ1 v))) = _
    rw [ht.apply_apply]
    exact sec128_psi_act1 h β _ _ hv

theorem sec128E_injective (h : Sec128Spl ρ V1 V2 φ1 φ2) (ht : Sec128Tw ρ V1 V2 τ)
    {β : Sec128A5 →* Sec128A5} (hβ : ∀ a, τ * ρ (a, 1) * τ⁻¹ = ρ (1, β a))
    (hβi : Function.Injective β) : Function.Injective (sec128E ht hβ) := by
  rw [injective_iff_map_eq_one]
  intro w hw
  obtain ⟨f, s⟩ := w
  have hw' : sec128Psi' ρ β (f 1, f sec128g) * sec128tau τ s = 1 := hw
  rcases sec128_Q_cases s with rfl | rfl
  · rw [sec128tau_one, mul_one, sec128Psi'_apply] at hw'
    have h1 : ((f 1, β (f sec128g)) : Sec128A5 × Sec128A5) = 1 :=
      h.inj (hw'.trans (map_one ρ).symm)
    have hf1 : f 1 = 1 := congrArg Prod.fst h1
    have hfg : f sec128g = 1 := hβi ((congrArg Prod.snd h1).trans (map_one β).symm)
    refine RegularWreathProduct.ext ?_ rfl
    funext q
    rcases sec128_Q_cases q with rfl | rfl
    · exact hf1
    · exact hfg
  · rw [sec128tau_g, sec128Psi'_apply] at hw'
    have : τ = ρ (f 1, β (f sec128g))⁻¹ := by
      rw [map_inv]
      exact eq_inv_of_mul_eq_one_right hw'
    exact absurd this (ht.nz _)

theorem sec128_coord_g (h : Sec128Spl ρ V1 V2 φ1 φ2) (ht : Sec128Tw ρ V1 V2 τ) :
    Sec128Coord V2 (fun v => τ (φ1 v)) where
  mem v hv := ht.mem_of_mem1 (h.c1.mem v hv)
  mul v w hv hw := by rw [h.c1.mul v w hv hw, map_mul]
  inj v hv h1 := h.c1.inj v hv (τ.injective (h1.trans (map_one τ).symm))
  surj x hx := by
    rw [← ht.sub] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨v, hv, rfl⟩ := h.c1.surj u hu
    exact ⟨v, hv, rfl⟩

end General

theorem sec128_card_wr : Nat.card (WrZ2 Sec128A5) = 7200 := by
  have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_eq_fintype_card]
    rfl
  rw [RegularWreathProduct.card, h2, sec127_card_alt5_type]
  norm_num

theorem sec128_wrAct_of {G : Type} [Group G] {V : Subgroup G} {Y : Subgroup (MulAut ↥V)}
    {ρ : Sec128A5 × Sec128A5 →* MulAut ↥V} {V1 V2 : Subgroup ↥V}
    {φ1 φ2 : (Fin 5 → ZMod 2) → ↥V} (h : Sec128Spl ρ V1 V2 φ1 φ2) {τ : MulAut ↥V}
    (ht : Sec128Tw ρ V1 V2 τ) (hτY : τ ∈ Y) (hρY : ρ.range ≤ Y)
    (hidx : (ρ.range.subgroupOf Y).index = 2) : Sec128WrAct V Y := by
  obtain ⟨β, hβi, hβ⟩ := sec128_exists_beta h ht
  have hEY : ∀ w, sec128E ht hβ w ∈ Y := by
    intro w
    show sec128Psi' ρ β (w.left 1, w.left sec128g) * sec128tau τ w.right ∈ Y
    refine Y.mul_mem (hρY ⟨(w.left 1, β (w.left sec128g)), rfl⟩) ?_
    by_cases hs : w.right = 1
    · rw [hs, sec128tau_one]
      exact Y.one_mem
    · simp only [sec128tau, hs, if_false]
      exact hτY
  let E1 : WrZ2 Sec128A5 →* ↥Y := (sec128E ht hβ).codRestrict Y hEY
  have hE1inj : Function.Injective E1 := fun a b hab =>
    sec128E_injective h ht hβ hβi (congrArg Subtype.val hab)
  have hcardY : Nat.card ↥Y = 7200 := by
    have h1 := Subgroup.card_mul_index (ρ.range.subgroupOf Y)
    rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hρY).toEquiv,
      ← Nat.card_congr (MonoidHom.ofInjective h.inj).toEquiv, Nat.card_prod,
      sec127_card_alt5_type] at h1
    omega
  haveI : Finite ↥Y := Nat.finite_of_card_ne_zero (by rw [hcardY]; norm_num)
  have hE1bij : Function.Bijective E1 :=
    hE1inj.bijective_of_nat_card_le (by rw [hcardY, sec128_card_wr])
  refine ⟨MulEquiv.ofBijective E1 hE1bij, sec128phi φ1 τ, sec128Vq V1 V2, ?_, ?_, ?_, ?_⟩
  · intro q
    rcases sec128_Q_cases q with rfl | rfl
    · rw [sec128Vq_one]
      exact (funext sec128phi_one : sec128phi φ1 τ 1 = φ1) ▸ h.c1
    · rw [sec128Vq_g]
      exact (funext sec128phi_g : sec128phi φ1 τ sec128g = fun v => τ (φ1 v)) ▸
        sec128_coord_g h ht
  · rw [sec128Vq_one, sec128Vq_g]
    exact h.sup
  · rw [sec128Vq_one, sec128Vq_g]
    exact h.inf
  · intro w q v hv
    exact sec128e0_act h ht hβ w q hv

end CFSG.OddStandard.SmallF3.Omega
