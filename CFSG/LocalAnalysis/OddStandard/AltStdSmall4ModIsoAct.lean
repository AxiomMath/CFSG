module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4ModIsoS0
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4ModSplit

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.OddStandard.AltStdSmall4.ModIso

open Subgroup Equiv Matrix
open CFSG.ProperTwoGeneratedCore.BinaryThreeSpace
open scoped Pointwise

section Proj

variable {G : Type} [Group G] {T O : Subgroup G}

@[expose] noncomputable def proj (T O : Subgroup G) (x : G) : G :=
  open Classical in if h : ∃ t ∈ T, t⁻¹ * x ∈ O then h.choose else 1

theorem proj_spec (hTO : T ≤ normalizer (O : Set G)) {x : G} (hx : x ∈ T ⊔ O) :
    proj T O x ∈ T ∧ (proj T O x)⁻¹ * x ∈ O := by
  have h : ∃ t ∈ T, t⁻¹ * x ∈ O := by
    have hm := Subgroup.coe_mul_of_left_le_normalizer_right T O hTO
    have hx' : x ∈ (T : Set G) * (O : Set G) := by
      rw [← hm]
      exact hx
    obtain ⟨t, ht, o, ho, rfl⟩ := Set.mem_mul.1 hx'
    exact ⟨t, ht, by rw [inv_mul_cancel_left]; exact ho⟩
  rw [proj, dif_pos h]
  exact h.choose_spec

theorem proj_eq (hTO : T ≤ normalizer (O : Set G)) (hinf : T ⊓ O = ⊥) {x t : G} (ht : t ∈ T)
    (hto : t⁻¹ * x ∈ O) : proj T O x = t := by
  have hx : x ∈ T ⊔ O := by
    have : x = t * (t⁻¹ * x) := by group
    rw [this]
    exact mul_mem (mem_sup_left ht) (mem_sup_right hto)
  obtain ⟨h1, h2⟩ := proj_spec hTO hx
  have h3 : t⁻¹ * proj T O x ∈ T ⊓ O := by
    refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem ht) h1, ?_⟩
    have : t⁻¹ * proj T O x = (t⁻¹ * x) * ((proj T O x)⁻¹ * x)⁻¹ := by group
    rw [this]
    exact mul_mem hto (inv_mem h2)
  rw [hinf, mem_bot] at h3
  calc proj T O x = t * (t⁻¹ * proj T O x) := by group
    _ = t := by rw [h3, mul_one]

@[expose] noncomputable def act (T O : Subgroup G) (g t : G) : G := proj T O (g * t * g⁻¹)

variable {N : Subgroup G} (hTO : T ≤ normalizer (O : Set G)) (hinf : T ⊓ O = ⊥)
  (hON : ∀ g ∈ N, ∀ o ∈ O, g * o * g⁻¹ ∈ O) (hTN : ∀ g ∈ N, ∀ t ∈ T, g * t * g⁻¹ ∈ T ⊔ O)

include hTO hTN in
theorem act_spec {g t : G} (hg : g ∈ N) (ht : t ∈ T) :
    act T O g t ∈ T ∧ (act T O g t)⁻¹ * (g * t * g⁻¹) ∈ O :=
  proj_spec hTO (hTN g hg t ht)

include hTO hinf in
theorem act_of_mem {g t : G} (h : g * t * g⁻¹ ∈ T) : act T O g t = g * t * g⁻¹ :=
  proj_eq hTO hinf h (by rw [inv_mul_cancel]; exact one_mem _)

include hTO hinf in
theorem act_one {t : G} (ht : t ∈ T) : act T O 1 t = t := by
  rw [act_of_mem hTO hinf (by rw [one_mul, inv_one, mul_one]; exact ht), one_mul, inv_one,
    mul_one]

include hTO hinf hTN in
theorem act_mul {g s t : G} (hg : g ∈ N) (hs : s ∈ T) (ht : t ∈ T) :
    act T O g (s * t) = act T O g s * act T O g t := by
  obtain ⟨hs1, hs2⟩ := act_spec hTO hTN hg hs
  obtain ⟨ht1, ht2⟩ := act_spec hTO hTN hg ht
  refine proj_eq hTO hinf (mul_mem hs1 ht1) ?_
  set s' := act T O g s
  set t' := act T O g t
  have e : (s' * t')⁻¹ * (g * (s * t) * g⁻¹) =
      (t'⁻¹ * (s'⁻¹ * (g * s * g⁻¹)) * t'⁻¹⁻¹) * (t'⁻¹ * (g * t * g⁻¹)) := by group
  rw [e]
  exact mul_mem ((mem_normalizer_iff.1 (hTO (inv_mem ht1)) _).1 hs2) ht2

include hTO hinf hON hTN in
theorem act_comp {g h t : G} (hg : g ∈ N) (hh : h ∈ N) (ht : t ∈ T) :
    act T O (g * h) t = act T O g (act T O h t) := by
  obtain ⟨h1, h2⟩ := act_spec hTO hTN hh ht
  obtain ⟨g1, g2⟩ := act_spec hTO hTN hg h1
  refine proj_eq hTO hinf g1 ?_
  set t₁ := act T O h t
  set t₂ := act T O g t₁
  have e : t₂⁻¹ * (g * h * t * (g * h)⁻¹) =
      (t₂⁻¹ * (g * t₁ * g⁻¹)) * (g * (t₁⁻¹ * (h * t * h⁻¹)) * g⁻¹) := by group
  rw [e]
  exact mul_mem g2 (hON g hg _ h2)

include hTO hinf hON hTN in
theorem act_conj_z {g z t : G} (hg : g ∈ N) (hz : z ∈ N) (hgz : g * z = z * g)
    (hzT : ∀ x ∈ T, z * x * z⁻¹ ∈ T) (ht : t ∈ T) :
    act T O g (z * t * z⁻¹) = z * act T O g t * z⁻¹ := by
  obtain ⟨h1, h2⟩ := act_spec hTO hTN hg ht
  refine proj_eq hTO hinf (hzT _ h1) ?_
  have e : (z * act T O g t * z⁻¹)⁻¹ * (g * (z * t * z⁻¹) * g⁻¹) =
      z * ((act T O g t)⁻¹ * (g * t * g⁻¹)) * z⁻¹ := by
    have hgz' : z⁻¹ * g = g * z⁻¹ := by
      calc z⁻¹ * g = z⁻¹ * (g * z) * z⁻¹ := by group
        _ = z⁻¹ * (z * g) * z⁻¹ := by rw [hgz]
        _ = g * z⁻¹ := by group
    calc (z * act T O g t * z⁻¹)⁻¹ * (g * (z * t * z⁻¹) * g⁻¹)
        = z * (act T O g t)⁻¹ * z⁻¹ * ((g * z) * t * (z⁻¹ * g⁻¹)) := by group
      _ = z * (act T O g t)⁻¹ * z⁻¹ * ((z * g) * t * (g⁻¹ * z⁻¹)) := by
          rw [hgz, show z⁻¹ * g⁻¹ = g⁻¹ * z⁻¹ by
            rw [← _root_.mul_inv_rev, ← _root_.mul_inv_rev, hgz]]
      _ = z * ((act T O g t)⁻¹ * (g * t * g⁻¹)) * z⁻¹ := by group
  rw [e]
  exact hON z hz _ h2

end Proj

section Coords

variable {G : Type} [Group G] {T : Subgroup G}

@[expose] noncomputable def toW (μ : T ≃* Multiplicative (Fin 6 → ZMod 2)) (x : G) :
    Fin 6 → ZMod 2 :=
  open Classical in if h : x ∈ T then Multiplicative.toAdd (μ ⟨x, h⟩) else 0

@[expose] noncomputable def ofW (μ : T ≃* Multiplicative (Fin 6 → ZMod 2))
    (w : Fin 6 → ZMod 2) : G :=
  ((μ.symm (Multiplicative.ofAdd w) : T) : G)

variable (μ : T ≃* Multiplicative (Fin 6 → ZMod 2))

theorem ofW_mem (w : Fin 6 → ZMod 2) : ofW μ w ∈ T := (μ.symm _).2

theorem toW_ofW (w : Fin 6 → ZMod 2) : toW μ (ofW μ w) = w := by
  rw [toW, dif_pos (ofW_mem μ w)]
  show Multiplicative.toAdd (μ (μ.symm (Multiplicative.ofAdd w))) = w
  rw [MulEquiv.apply_symm_apply, toAdd_ofAdd]

theorem ofW_toW {x : G} (hx : x ∈ T) : ofW μ (toW μ x) = x := by
  rw [toW, dif_pos hx, ofW, ofAdd_toAdd, MulEquiv.symm_apply_apply]

theorem ofW_add (v w : Fin 6 → ZMod 2) : ofW μ (v + w) = ofW μ v * ofW μ w := by
  rw [ofW, ofW, ofW, ofAdd_add, map_mul, Subgroup.coe_mul]

theorem ofW_zero : ofW μ 0 = 1 := by
  rw [ofW, ofAdd_zero, map_one, OneMemClass.coe_one]

theorem ofW_injective : Function.Injective (ofW μ) := fun v w h =>
  Multiplicative.ofAdd.injective (μ.symm.injective (Subtype.ext h))

theorem toW_mul {x y : G} (hx : x ∈ T) (hy : y ∈ T) : toW μ (x * y) = toW μ x + toW μ y := by
  apply ofW_injective μ
  rw [ofW_add, ofW_toW μ hx, ofW_toW μ hy, ofW_toW μ (mul_mem hx hy)]

theorem toW_one : toW μ 1 = 0 := by
  apply ofW_injective μ
  rw [ofW_toW μ (one_mem T), ofW_zero]

theorem toW_eq_zero {x : G} (hx : x ∈ T) (h : toW μ x = 0) : x = 1 := by
  rw [← ofW_toW μ hx, h, ofW_zero]

theorem w6_add_self (x : Fin 6 → ZMod 2) : x + x = 0 := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  generalize x i = a
  revert a
  decide

end Coords

structure TCoords {G : Type} [Group G] (z : G) (T : Subgroup G) (κ : GL (Fin 3) (ZMod 2) →* G)
    (E₀ : Subgroup G) (cT : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2) → G) : Prop where
  mem : ∀ v w, cT v w ∈ T
  add : ∀ v w v' w', cT (v + v') (w + w') = cT v w * cT v' w'
  surj : ∀ t ∈ T, ∃ v w, cT v w = t
  inj : ∀ v w, cT v w = 1 → v = 0 ∧ w = 0
  conj_z : ∀ v w, z * cT v w * z⁻¹ = cT (v + w) w
  conj_lin : ∀ (A : GL (Fin 3) (ZMod 2)) (g : G), g ∈ normalizer (T : Set G) →
    (∃ e ∈ E₀, g = e * κ A) → ∀ v w,
      g * cT v w * g⁻¹ = cT ((A : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v)
        ((A : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w)

section Setting

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ}
  {θ : L ≃* alternatingGroup (Fin n)} {z : G} {T : Subgroup G}

theorem conj_mem_oddCoreOf' {H : Subgroup G} {g : G} (hg : g ∈ H) {x : G}
    (hx : x ∈ AltStdSec.oddCoreOf H) : g * x * g⁻¹ ∈ AltStdSec.oddCoreOf H := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹,
    (inferInstance : (CFSG.oddCore ↥H).Normal).conj_mem y hy ⟨g, hg⟩, rfl⟩

theorem exists_mu {hn : 8 ≤ n} (hH : HData θ hn z T) :
    Nonempty (T ≃* Multiplicative (Fin 6 → ZMod 2)) := by
  rcases hH.n0.homo with h | h
  · exact h
  · exfalso
    obtain ⟨e⟩ := h
    set y : Multiplicative (Fin 3 → ZMod 4) := Multiplicative.ofAdd (fun _ => 1)
    have hx := hH.elem _ (e.symm y).2
    have h1 : (e.symm y) ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hx)
    have h2 := congrArg e h1
    rw [map_pow, MulEquiv.apply_symm_apply, map_one] at h2
    have h3 := congrArg (fun x : Multiplicative (Fin 3 → ZMod 4) => Multiplicative.toAdd x 0) h2
    simp only [y, pow_two, toAdd_mul, toAdd_ofAdd, Pi.add_apply, toAdd_one,
      Pi.zero_apply] at h3
    exact absurd h3 (by decide)

variable (c : Config G L Q n θ z) (hH : HData θ c.hn8 z T)

theorem kap_mem_N0 (A : GL (Fin 3) (ZMod 2)) : kap θ c.hn8 A ∈ N0 θ c.hn8 z :=
  N0.mem_N0_of_mem_L c.hn8 c (kap_mem_L θ c.hn8 A) fun i => ⟨_, kap_conj_eps θ c.hn8 A i⟩

abbrev Ocore (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) (z : G) : Subgroup G :=
  AltStdSec.oddCoreOf (N0 θ hn z)

omit [Finite G] in
theorem le_normalizer_of_conj' {H X : Subgroup G} (h : ∀ g ∈ H, ∀ x ∈ X, g * x * g⁻¹ ∈ X) :
    H ≤ normalizer (X : Set G) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro x
  refine ⟨h g hg x, fun hx => ?_⟩
  have := h g⁻¹ (inv_mem hg) _ hx
  rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this

theorem ocore_conj {g o : G} (hg : g ∈ N0 θ c.hn8 z) (ho : o ∈ Ocore θ c.hn8 z) :
    g * o * g⁻¹ ∈ Ocore θ c.hn8 z :=
  conj_mem_oddCoreOf' hg ho

include hH in
theorem T_le_normalizer_ocore : T ≤ normalizer (Ocore θ c.hn8 z : Set G) :=
  le_normalizer_of_conj' fun g hg o ho => ocore_conj c (hH.n0.le hg) ho

include hH in
theorem T_inf_ocore : T ⊓ Ocore θ c.hn8 z = ⊥ := by
  apply inf_eq_bot_of_coprime
  rw [hH.n0.card_eq]
  exact Nat.Coprime.pow_left 6 (coprime_card_oddCoreOf _)

theorem z_mem_N0 : z ∈ N0 θ c.hn8 z :=
  Subgroup.le_normalizer (mem_sup_right (mem_zpowers z))

include hH in
theorem conj_z_mem {x : G} (hx : x ∈ T) : z * x * z⁻¹ ∈ T :=
  (mem_normalizer_iff.1 hH.n0.norm x).1 hx

include hH in
theorem comm_T {a b : G} (ha : a ∈ T) (hb : b ∈ T) : a * b = b * a := by
  have hab := hH.elem _ (mul_mem ha hb)
  have h1 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hab)
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hH.elem a ha)
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hH.elem b hb)
  rw [_root_.mul_inv_rev, ha', hb'] at h1
  exact h1.symm

include hH in
theorem inv_T {a : G} (ha : a ∈ T) : a⁻¹ = a :=
  inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hH.elem a ha)

end Setting

section Rep

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ}
  {θ : L ≃* alternatingGroup (Fin n)} {z : G} {T : Subgroup G}
  (c : Config G L Q n θ z) (hH : HData θ c.hn8 z T) (μ : T ≃* Multiplicative (Fin 6 → ZMod 2))

@[expose] noncomputable def repFun (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) (z : G)
    (μ : T ≃* Multiplicative (Fin 6 → ZMod 2)) (A : GL (Fin 3) (ZMod 2))
    (w : Fin 6 → ZMod 2) : Fin 6 → ZMod 2 :=
  toW μ (act T (Ocore θ hn z) (kap θ hn A) (ofW μ w))

include hH in
theorem act_kap_mem (A : GL (Fin 3) (ZMod 2)) {t : G} (ht : t ∈ T) :
    act T (Ocore θ c.hn8 z) (kap θ c.hn8 A) t ∈ T :=
  (act_spec (T_le_normalizer_ocore c hH) hH.n0.normal (kap_mem_N0 c A) ht).1

include hH in
theorem repFun_add (A : GL (Fin 3) (ZMod 2)) (v w : Fin 6 → ZMod 2) :
    repFun θ c.hn8 z μ A (v + w) = repFun θ c.hn8 z μ A v + repFun θ c.hn8 z μ A w := by
  unfold repFun
  rw [ofW_add, act_mul (T_le_normalizer_ocore c hH) (T_inf_ocore c hH) hH.n0.normal
    (kap_mem_N0 c A) (ofW_mem μ v) (ofW_mem μ w),
    toW_mul μ (act_kap_mem c hH A (ofW_mem μ v)) (act_kap_mem c hH A (ofW_mem μ w))]

include hH in
theorem repFun_zero (A : GL (Fin 3) (ZMod 2)) : repFun θ c.hn8 z μ A 0 = 0 := by
  unfold repFun
  rw [ofW_zero, act_of_mem (T_le_normalizer_ocore c hH) (T_inf_ocore c hH)
    (by rw [mul_one, mul_inv_cancel]; exact one_mem T), mul_one, mul_inv_cancel, toW_one]

include hH in
theorem repFun_one (w : Fin 6 → ZMod 2) : repFun θ c.hn8 z μ 1 w = w := by
  unfold repFun
  rw [map_one, act_one (T_le_normalizer_ocore c hH) (T_inf_ocore c hH) (ofW_mem μ w),
    toW_ofW]

include hH in
theorem repFun_mul (A B : GL (Fin 3) (ZMod 2)) (w : Fin 6 → ZMod 2) :
    repFun θ c.hn8 z μ (A * B) w = repFun θ c.hn8 z μ A (repFun θ c.hn8 z μ B w) := by
  unfold repFun
  rw [map_mul, act_comp (T_le_normalizer_ocore c hH) (T_inf_ocore c hH)
    (fun g hg o ho => ocore_conj c hg ho) hH.n0.normal (kap_mem_N0 c A) (kap_mem_N0 c B)
    (ofW_mem μ w), ofW_toW μ (act_kap_mem c hH B (ofW_mem μ w))]

@[expose] noncomputable def rep :
    Representation (ZMod 2) (GL (Fin 3) (ZMod 2)) (Fin 6 → ZMod 2) where
  toFun A := AddMonoidHom.toZModLinearMap 2
    { toFun := repFun θ c.hn8 z μ A
      map_zero' := repFun_zero c hH μ A
      map_add' := repFun_add c hH μ A }
  map_one' := LinearMap.ext (repFun_one c hH μ)
  map_mul' A B := LinearMap.ext (repFun_mul c hH μ A B)

theorem rep_apply (A : GL (Fin 3) (ZMod 2)) (w : Fin 6 → ZMod 2) :
    rep c hH μ A w = repFun θ c.hn8 z μ A w := rfl

@[expose] noncomputable def iE : (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2) :=
  AddMonoidHom.toZModLinearMap 2
    { toFun := fun v => toW μ (N0.eps θ c.hn8 (bits.symm v))
      map_zero' := by
        show toW μ (N0.eps θ c.hn8 (bits.symm 0)) = 0
        rw [bits_symm_zero, N0.eps_zero, toW_one]
      map_add' := fun v w => by
        show toW μ (N0.eps θ c.hn8 (bits.symm (v + w))) =
          toW μ (N0.eps θ c.hn8 (bits.symm v)) + toW μ (N0.eps θ c.hn8 (bits.symm w))
        rw [bits_symm_add, N0.xr_eq_xor, ← N0.eps_mul, toW_mul μ
          (hH.n0.E_le (N0.eps_mem_E θ c.hn8 _)) (hH.n0.E_le (N0.eps_mem_E θ c.hn8 _))] }

theorem iE_apply (v : Fin 3 → ZMod 2) :
    iE c hH μ v = toW μ (N0.eps θ c.hn8 (bits.symm v)) := rfl

@[expose] noncomputable def iota : (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2) :=
  AddMonoidHom.toZModLinearMap 2
    { toFun := fun w => w + toW μ (z * ofW μ w * z⁻¹)
      map_zero' := by
        show 0 + toW μ (z * ofW μ 0 * z⁻¹) = 0
        rw [ofW_zero, mul_one, mul_inv_cancel, toW_one, add_zero]
      map_add' := fun v w => by
        show v + w + toW μ (z * ofW μ (v + w) * z⁻¹) =
          v + toW μ (z * ofW μ v * z⁻¹) + (w + toW μ (z * ofW μ w * z⁻¹))
        rw [ofW_add, show z * (ofW μ v * ofW μ w) * z⁻¹ =
          (z * ofW μ v * z⁻¹) * (z * ofW μ w * z⁻¹) by group,
          toW_mul μ (conj_z_mem c hH (ofW_mem μ v)) (conj_z_mem c hH (ofW_mem μ w))]
        abel }

theorem iota_apply (w : Fin 6 → ZMod 2) :
    iota c hH μ w = w + toW μ (z * ofW μ w * z⁻¹) := rfl

theorem iota_toW {t : G} (ht : t ∈ T) : iota c hH μ (toW μ t) = toW μ (t * (z * t * z⁻¹)) := by
  rw [iota_apply, ofW_toW μ ht, toW_mul μ ht (conj_z_mem c hH ht)]

include hH in
theorem eps_mem_T (v : Fin 8) : N0.eps θ c.hn8 v ∈ T := hH.n0.E_le (N0.eps_mem_E θ c.hn8 v)

theorem conj_z_eps (v : Fin 8) : z * N0.eps θ c.hn8 v * z⁻¹ = N0.eps θ c.hn8 v := by
  rw [← N0.eps_comm_z c.hn8 c v, mul_inv_cancel_right]

include hH in
theorem exists_tCoords_act : ∃ cT, TCoords z T (kap θ c.hn8) (E θ c.hn8) cT ∧
    ∀ (A : GL (Fin 3) (ZMod 2)) (v w : Fin 3 → ZMod 2),
      act T (Ocore θ c.hn8 z) (kap θ c.hn8 A) (cT v w) =
        cT ((A : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v)
          ((A : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w) := by
  obtain ⟨μ⟩ := exists_mu hH
  have hTO := T_le_normalizer_ocore c hH
  have hinf := T_inf_ocore c hH
  have hi : ∀ (g : GL (Fin 3) (ZMod 2)) (v : Fin 3 → ZMod 2),
      iE c hH μ ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) = rep c hH μ g (iE c hH μ v) := by
    intro g v
    rw [rep_apply, repFun, iE_apply, iE_apply, ofW_toW μ (eps_mem_T c hH _),
      act_of_mem hTO hinf (by rw [kap_conj_eps]; exact eps_mem_T c hH _), kap_conj_eps,
      linPerm8_apply, Equiv.apply_symm_apply]
  have hι : ∀ (g : GL (Fin 3) (ZMod 2)) (w : Fin 6 → ZMod 2),
      iota c hH μ (rep c hH μ g w) = rep c hH μ g (iota c hH μ w) := by
    intro g w
    have ht := ofW_mem μ w
    have ht' := act_kap_mem c hH g ht
    rw [rep_apply, rep_apply, repFun, repFun, iota_toW c hH μ ht', iota_apply,
      ← toW_ofW μ w, ofW_toW μ ht, ← toW_mul μ ht (conj_z_mem c hH ht), ofW_toW μ
      (mul_mem ht (conj_z_mem c hH ht)), act_mul hTO hinf hH.n0.normal (kap_mem_N0 c g) ht
      (conj_z_mem c hH ht), act_conj_z hTO hinf (fun g hg o ho => ocore_conj c hg ho)
      hH.n0.normal (kap_mem_N0 c g) (z_mem_N0 c) (N0.comm_z_of_mem_L c (kap_mem_L θ c.hn8 g))
      (fun x hx => conj_z_mem c hH hx) ht]
  have hinj : Function.Injective (iE c hH μ) := by
    intro v v' h
    rw [iE_apply, iE_apply] at h
    have h1 := congrArg (ofW μ) h
    rw [ofW_toW μ (eps_mem_T c hH _), ofW_toW μ (eps_mem_T c hH _)] at h1
    exact bits.symm.injective (N0.eps_injective θ c.hn8 h1)
  have hcent : ∀ t ∈ T, z * t * z⁻¹ = t → ∃ v : Fin 8, N0.eps θ c.hn8 v = t := by
    intro t ht hzt
    have htC : t ∈ T ⊓ centralizer ({z} : Set G) := by
      refine Subgroup.mem_inf.2 ⟨ht, mem_centralizer_singleton_iff.2 ?_⟩
      calc t * z = z * t * z⁻¹ * z := by rw [hzt]
        _ = z * t := by group
    rw [hH.n0.cent] at htC
    obtain ⟨v, hv⟩ := (N0.mem_E_iff θ c.hn8 t).1 htC
    exact ⟨v, hv.symm⟩
  have hrange_le : ∀ w, iota c hH μ w ∈ LinearMap.range (iE c hH μ) := by
    intro w
    set t := ofW μ w
    have ht : t ∈ T := ofW_mem μ w
    have hu : z * (t * (z * t * z⁻¹)) * z⁻¹ = t * (z * t * z⁻¹) := by
      have hz2 : z⁻¹ = z := z_inv c
      calc z * (t * (z * t * z⁻¹)) * z⁻¹ = (z * t * z⁻¹) * (z * z * t * z⁻¹ * z⁻¹) := by group
        _ = (z * t * z⁻¹) * t := by
          rw [z_mul_self c, one_mul, mul_assoc t, show z⁻¹ * z⁻¹ = 1 by rw [hz2, z_mul_self c],
            mul_one]
        _ = t * (z * t * z⁻¹) := comm_T c hH (conj_z_mem c hH ht) ht
    obtain ⟨v, hv⟩ := hcent _ (mul_mem ht (conj_z_mem c hH ht)) hu
    refine ⟨bits v, ?_⟩
    rw [iE_apply, Equiv.symm_apply_apply, hv, ← iota_toW c hH μ ht, toW_ofW]
  have hker : LinearMap.ker (iota c hH μ) = LinearMap.range (iE c hH μ) := by
    ext w
    rw [LinearMap.mem_ker]
    constructor
    · intro h0
      set t := ofW μ w
      have ht : t ∈ T := ofW_mem μ w
      have h1 : t * (z * t * z⁻¹) = 1 := by
        apply toW_eq_zero μ (mul_mem ht (conj_z_mem c hH ht))
        rw [← iota_toW c hH μ ht, toW_ofW]
        exact h0
      have h2 : z * t * z⁻¹ = t := by
        rw [eq_inv_of_mul_eq_one_right h1, inv_T c hH ht]
      obtain ⟨v, hv⟩ := hcent t ht h2
      refine ⟨bits v, ?_⟩
      rw [iE_apply, Equiv.symm_apply_apply, hv, toW_ofW]
    · rintro ⟨v, rfl⟩
      rw [iE_apply, iota_toW c hH μ (eps_mem_T c hH _), conj_z_eps c, N0.eps_mul_self, toW_one]
  have hrange : LinearMap.range (iota c hH μ) = LinearMap.range (iE c hH μ) := by
    apply le_antisymm
    · rintro _ ⟨w, rfl⟩
      exact hrange_le w
    · rintro _ ⟨v, rfl⟩
      have he : N0.eps θ c.hn8 (bits.symm v) ∈ T := eps_mem_T c hH _
      have hez : (N0.eps θ c.hn8 (bits.symm v) * z) ^ 2 = 1 := by
        calc (N0.eps θ c.hn8 (bits.symm v) * z) ^ 2
            = N0.eps θ c.hn8 (bits.symm v) * (z * N0.eps θ c.hn8 (bits.symm v)) * z := by
              rw [sq]; group
          _ = N0.eps θ c.hn8 (bits.symm v) * (N0.eps θ c.hn8 (bits.symm v) * z) * z := by
              rw [← N0.comm_z_of_mem_L c (N0.eps_mem_L θ c.hn8 _)]
          _ = (N0.eps θ c.hn8 (bits.symm v) * N0.eps θ c.hn8 (bits.symm v)) * (z * z) := by group
          _ = 1 := by rw [N0.eps_mul_self, z_mul_self c, one_mul]
      obtain ⟨x, hx, hxz⟩ := hH.inv _ he hez
      refine ⟨toW μ x, ?_⟩
      rw [iota_toW c hH μ hx, iE_apply]
      congr 1
      have h1 : N0.eps θ c.hn8 (bits.symm v) = x * z * x⁻¹ * z⁻¹ := by
        rw [hxz, mul_inv_cancel_right]
      rw [h1, show x * z * x⁻¹ * z⁻¹ = x * (z * x * z⁻¹)⁻¹ by group,
        inv_T c hH (conj_z_mem c hH hx)]
  obtain ⟨j, hj, hιj⟩ := ModSplit.exists_section (rep c hH μ) (iE c hH μ) (iota c hH μ) hi hι hinj
    hker hrange
  have hιi : ∀ v, iota c hH μ (iE c hH μ v) = 0 := fun v => by
    have : iE c hH μ v ∈ LinearMap.ker (iota c hH μ) := by
      rw [hker]
      exact LinearMap.mem_range_self _ v
    exact this
  refine ⟨fun v w => ofW μ (iE c hH μ v + j w), ?_, fun A v w => ?_⟩
  swap
  ·
    show act T (Ocore θ c.hn8 z) (kap θ c.hn8 A) (ofW μ (iE c hH μ v + j w)) =
      ofW μ (iE c hH μ ((A : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) +
        j ((A : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w))
    rw [← ofW_toW μ (act_kap_mem c hH A (ofW_mem μ _)), ← repFun, ← rep_apply c hH μ, map_add,
      ← hi, ← hj]
  refine
    { mem := fun v w => ofW_mem μ _
      add := fun v w v' w' => by
        rw [← ofW_add, map_add, map_add]
        congr 1
        abel
      surj := fun t ht => ?_
      inj := fun v w h => ?_
      conj_z := fun v w => ?_
      conj_lin := fun A g hg hge v w => ?_ }
  ·
    obtain ⟨w, hw⟩ := hrange_le (toW μ t)
    have h1 : toW μ t - j w ∈ LinearMap.ker (iota c hH μ) := by
      rw [LinearMap.mem_ker, map_sub, hιj, hw, sub_self]
    rw [hker] at h1
    obtain ⟨v, hv⟩ := h1
    refine ⟨v, w, ?_⟩
    show ofW μ (iE c hH μ v + j w) = t
    rw [hv, sub_add_cancel, ofW_toW μ ht]
  ·
    have h1 : iE c hH μ v + j w = 0 := by
      apply ofW_injective μ
      rw [h, ofW_zero]
    have h2 := congrArg (iota c hH μ) h1
    rw [map_add, hιi, zero_add, hιj, map_zero] at h2
    have hw : w = 0 := hinj (by rw [h2, map_zero])
    rw [hw, map_zero, add_zero] at h1
    exact ⟨hinj (by rw [h1, map_zero]), hw⟩
  ·
    show z * ofW μ (iE c hH μ v + j w) * z⁻¹ = ofW μ (iE c hH μ (v + w) + j w)
    have h1 := iota_apply c hH μ (iE c hH μ v + j w)
    have h2 : toW μ (z * ofW μ (iE c hH μ v + j w) * z⁻¹) =
        iota c hH μ (iE c hH μ v + j w) + (iE c hH μ v + j w) := by
      rw [h1, add_comm (iE c hH μ v + j w), add_assoc, w6_add_self, add_zero]
    have h3 : iota c hH μ (iE c hH μ v + j w) = iE c hH μ w := by
      rw [map_add, hιi, zero_add, hιj]
    rw [← ofW_toW μ (conj_z_mem c hH (ofW_mem μ (iE c hH μ v + j w))), h2, h3, map_add]
    congr 1
    abel
  ·
    obtain ⟨e, he, rfl⟩ := hge
    show e * kap θ c.hn8 A * ofW μ (iE c hH μ v + j w) * (e * kap θ c.hn8 A)⁻¹ =
      ofW μ (iE c hH μ ((A : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) +
        j ((A : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w))
    obtain ⟨x, hx⟩ : ∃ x, x = iE c hH μ v + j w := ⟨_, rfl⟩
    obtain ⟨t, htx⟩ : ∃ t, t = ofW μ x := ⟨_, rfl⟩
    rw [← hx, ← htx]
    have ht : t ∈ T := htx ▸ ofW_mem μ x
    have heT : e ∈ T := hH.n0.E_le he
    have hgt : e * kap θ c.hn8 A * t * (e * kap θ c.hn8 A)⁻¹ ∈ T :=
      (mem_normalizer_iff.1 hg t).1 ht
    have hkt : kap θ c.hn8 A * t * (kap θ c.hn8 A)⁻¹ =
        e * kap θ c.hn8 A * t * (e * kap θ c.hn8 A)⁻¹ := by
      have h1 : kap θ c.hn8 A * t * (kap θ c.hn8 A)⁻¹ =
          e⁻¹ * (e * kap θ c.hn8 A * t * (e * kap θ c.hn8 A)⁻¹) * e := by group
      rw [h1, mul_assoc, comm_T c hH hgt heT, ← mul_assoc, inv_mul_cancel, one_mul]
    have hact : act T (Ocore θ c.hn8 z) (kap θ c.hn8 A) t =
        e * kap θ c.hn8 A * t * (e * kap θ c.hn8 A)⁻¹ := by
      rw [act_of_mem hTO hinf (by rw [hkt]; exact hgt), hkt]
    have h1 : toW μ (e * kap θ c.hn8 A * t * (e * kap θ c.hn8 A)⁻¹) = rep c hH μ A x := by
      rw [rep_apply, repFun, ← htx, ← hact]
    rw [← ofW_toW μ hgt, h1, hx, map_add, ← hi, ← hj]

include hH in
theorem exists_tCoords : ∃ cT, TCoords z T (kap θ c.hn8) (E θ c.hn8) cT :=
  (exists_tCoords_act c hH).imp fun _ h => h.1

end Rep


end CFSG.OddStandard.AltStdSmall4.ModIso
