module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneJhatFinite

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.Jhat

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)
local notation "𝕊" => {X : Matrix (Fin 3) (Fin 3) (ZMod 2) // X ∈ binarySymMatrices 3}

variable {G : Type} [Group G]

structure JBase (τ : Multiplicative 𝕊 →* G) (lev : GL (Fin 3) (ZMod 2) →* G) (z : G)
    (ν : G → 𝕊) (A D C E Dh : Subgroup G) : Prop where
  τ_inj : Function.Injective τ
  mem_A : ∀ a, a ∈ A ↔ ∃ B, τ B = a
  lev_τ : ∀ g B, lev g * τ B * (lev g)⁻¹ =
    τ (Multiplicative.ofAdd (symThreeCongr g (Multiplicative.toAdd B)))
  lev_z : ∀ g, lev g * z = z * lev g
  z_sq : z * z = 1
  z_D : z ∈ D
  z_C : z ∉ C
  D_C : ∀ d ∈ D, d ∈ C ∨ z * d ∈ C
  C_eq : C = D ⊓ centralizer (E : Set G)
  E_C : E ≤ C
  A_E : A ≤ E
  E_sq : ∀ x ∈ E, x * x = 1
  zcomm : ∀ d ∈ D, z⁻¹ * (d⁻¹ * z * d) = τ (Multiplicative.ofAdd (ν d))
  ν_mul : ∀ c ∈ C, ∀ c' ∈ C, ν (c * c') = ν c + ν c'
  ν_A : ∀ c ∈ C, ν c = 0 ↔ c ∈ A
  ν_E : ∀ c ∈ C, symThreeDiag (ν c : M₃) = 0 ↔ c ∈ E
  ν_surj : ∀ B, ∃ c ∈ C, ν c = B
  ν_lev : ∀ g, ∀ c ∈ C, lev g * c * (lev g)⁻¹ ∈ C ∧
    ν (lev g * c * (lev g)⁻¹) = symThreeCongr g (ν c)
  A_sq : closure {x | ∃ c ∈ C, c ^ 2 = x} = A
  D_Dh : D ≤ Dh
  Dh_card : Nat.card Dh = 2 ^ 16
  Dh_E : ∀ t ∈ Dh, ∀ x ∈ E, t * x * t⁻¹ ∈ E
  lev_Dh : ∀ g, ∀ t ∈ Dh, lev g * t * (lev g)⁻¹ ∈ Dh
  zt_C : ∀ t ∈ Dh, z⁻¹ * (t⁻¹ * z * t) ∈ C
  zt_mul : ∀ t ∈ Dh, ∀ s ∈ Dh, z⁻¹ * ((t * s)⁻¹ * z * (t * s)) *
    (z⁻¹ * (t⁻¹ * z * t) * (z⁻¹ * (s⁻¹ * z * s)))⁻¹ ∈ E
  zt_E : ∀ t ∈ Dh, z⁻¹ * (t⁻¹ * z * t) ∈ E ↔ t ∈ D
  zt_surj : ∀ c ∈ C, ∃ t ∈ Dh, (z⁻¹ * (t⁻¹ * z * t))⁻¹ * c ∈ E
  zt_lev : ∀ g, ∀ t ∈ Dh, z⁻¹ * ((lev g * t * (lev g)⁻¹)⁻¹ * z * (lev g * t * (lev g)⁻¹)) *
    (lev g * (z⁻¹ * (t⁻¹ * z * t)) * (lev g)⁻¹)⁻¹ ∈ E
  C_Dh : ∀ c ∈ C, ∀ t ∈ Dh, c⁻¹ * t⁻¹ * c * t ∈ E

namespace JBase

variable {τ : Multiplicative 𝕊 →* G} {lev : GL (Fin 3) (ZMod 2) →* G} {z : G} {ν : G → 𝕊}
  {A D C E Dh : Subgroup G}

theorem z_inv (h : JBase τ lev z ν A D C E Dh) : z⁻¹ = z :=
  inv_eq_of_mul_eq_one_right h.z_sq

theorem C_D (h : JBase τ lev z ν A D C E Dh) : C ≤ D := fun c hc => by
  rw [h.C_eq] at hc
  exact hc.1

theorem comm_of_mem (h : JBase τ lev z ν A D C E Dh) {x c : G} (hx : x ∈ E) (hc : c ∈ C) :
    x * c = c * x := by
  rw [h.C_eq] at hc
  exact mem_centralizer_iff.1 (mem_inf.1 hc).2 x hx

theorem E_D (h : JBase τ lev z ν A D C E Dh) : E ≤ D :=
  h.E_C.trans h.C_D

theorem C_le_Dh (h : JBase τ lev z ν A D C E Dh) : C ≤ Dh :=
  h.C_D.trans h.D_Dh

theorem A_C (h : JBase τ lev z ν A D C E Dh) : A ≤ C :=
  h.A_E.trans h.E_C

theorem z_Dh (h : JBase τ lev z ν A D C E Dh) : z ∈ Dh :=
  h.D_Dh h.z_D

theorem E_comm (h : JBase τ lev z ν A D C E Dh) {x y : G} (hx : x ∈ E) (hy : y ∈ E) :
    x * y = y * x :=
  h.comm_of_mem hx (h.E_C hy)

theorem τ_mem (h : JBase τ lev z ν A D C E Dh) (B : Multiplicative 𝕊) : τ B ∈ A :=
  (h.mem_A _).2 ⟨B, rfl⟩

theorem conj_inv_mem_E (h : JBase τ lev z ν A D C E Dh) {t x : G} (ht : t ∈ Dh) (hx : x ∈ E) :
    t⁻¹ * x * t ∈ E := by
  have := h.Dh_E t⁻¹ (inv_mem ht) x hx
  rwa [inv_inv] at this

theorem ν_one (h : JBase τ lev z ν A D C E Dh) : ν 1 = 0 :=
  (h.ν_A 1 (one_mem C)).2 (one_mem A)

theorem sym_add_self (X : 𝕊) : X + X = 0 := by
  apply Subtype.ext
  change (X : M₃) + (X : M₃) = 0
  ext i j
  change (X : M₃) i j + (X : M₃) i j = 0
  generalize (X : M₃) i j = a
  revert a
  decide

theorem ν_inv (h : JBase τ lev z ν A D C E Dh) {c : G} (hc : c ∈ C) : ν c⁻¹ = ν c := by
  have h1 := h.ν_mul c hc c⁻¹ (inv_mem hc)
  rw [mul_inv_cancel, h.ν_one] at h1
  have h2 : ν c⁻¹ = ν c + (ν c + ν c⁻¹) := by
    rw [← add_assoc, sym_add_self, zero_add]
  rw [h2, ← h1, add_zero]

theorem vec_add_self (v : Fin 3 → ZMod 2) : v + v = 0 := by
  funext i
  change v i + v i = 0
  generalize v i = a
  revert a
  decide

theorem dν_mul (h : JBase τ lev z ν A D C E Dh) {c c' : G} (hc : c ∈ C) (hc' : c' ∈ C) :
    symThreeDiag (ν (c * c') : M₃) = symThreeDiag (ν c : M₃) + symThreeDiag (ν c' : M₃) := by
  rw [h.ν_mul c hc c' hc']
  rfl

theorem dν_E (h : JBase τ lev z ν A D C E Dh) {e : G} (he : e ∈ E) :
    symThreeDiag (ν e : M₃) = 0 :=
  (h.ν_E e (h.E_C he)).2 he

theorem dν_eq_of_mul_inv_mem (h : JBase τ lev z ν A D C E Dh) {x y : G} (hy : y ∈ C)
    (hxy : x * y⁻¹ ∈ E) : symThreeDiag (ν x : M₃) = symThreeDiag (ν y : M₃) := by
  have e1 := h.dν_mul (h.E_C hxy) hy
  rwa [inv_mul_cancel_right, h.dν_E hxy, zero_add] at e1

theorem dν_eq_of_inv_mul_mem (h : JBase τ lev z ν A D C E Dh) {x y : G} (hy : y ∈ C)
    (hxy : y⁻¹ * x ∈ E) : symThreeDiag (ν x : M₃) = symThreeDiag (ν y : M₃) := by
  have e1 := h.dν_mul hy (h.E_C hxy)
  rwa [mul_inv_cancel_left, h.dν_E hxy, add_zero] at e1

theorem mul_inv_mem_E_of_dν_eq (h : JBase τ lev z ν A D C E Dh) {x y : G} (hx : x ∈ C)
    (hy : y ∈ C) (hxy : symThreeDiag (ν x : M₃) = symThreeDiag (ν y : M₃)) : x * y⁻¹ ∈ E := by
  refine (h.ν_E _ (mul_mem hx (inv_mem hy))).1 ?_
  rw [h.dν_mul hx (inv_mem hy), h.ν_inv hy, hxy, vec_add_self]

end JBase

@[expose] def wvec (z : G) (ν : G → 𝕊) (x : G) : Fin 3 → ZMod 2 :=
  symThreeDiag (ν (z⁻¹ * (x⁻¹ * z * x)) : M₃)

theorem wvec_def (z : G) (ν : G → 𝕊) (x : G) :
    wvec z ν x = symThreeDiag (ν (z⁻¹ * (x⁻¹ * z * x)) : M₃) :=
  rfl

namespace JBase

variable {τ : Multiplicative 𝕊 →* G} {lev : GL (Fin 3) (ZMod 2) →* G} {z : G} {ν : G → 𝕊}
  {A D C E Dh : Subgroup G}

theorem wvec_mul (h : JBase τ lev z ν A D C E Dh) {t s : G} (ht : t ∈ Dh) (hs : s ∈ Dh) :
    wvec z ν (t * s) = wvec z ν t + wvec z ν s := by
  rw [wvec_def, wvec_def, wvec_def,
    h.dν_eq_of_mul_inv_mem (mul_mem (h.zt_C t ht) (h.zt_C s hs)) (h.zt_mul t ht s hs),
    h.dν_mul (h.zt_C t ht) (h.zt_C s hs)]

theorem wvec_eq_zero_iff (h : JBase τ lev z ν A D C E Dh) {t : G} (ht : t ∈ Dh) :
    wvec z ν t = 0 ↔ t ∈ D :=
  (h.ν_E _ (h.zt_C t ht)).trans (h.zt_E t ht)

theorem wvec_one (h : JBase τ lev z ν A D C E Dh) : wvec z ν 1 = 0 :=
  (h.wvec_eq_zero_iff (one_mem _)).2 (one_mem _)

theorem wvec_inv (h : JBase τ lev z ν A D C E Dh) {t : G} (ht : t ∈ Dh) :
    wvec z ν t⁻¹ = wvec z ν t := by
  have e := h.wvec_mul ht (inv_mem ht)
  rw [mul_inv_cancel, h.wvec_one] at e
  calc wvec z ν t⁻¹ = wvec z ν t + (wvec z ν t + wvec z ν t⁻¹) := by
        rw [← add_assoc, vec_add_self, zero_add]
    _ = wvec z ν t := by rw [← e, add_zero]

theorem mul_inv_mem_D (h : JBase τ lev z ν A D C E Dh) {t s : G} (ht : t ∈ Dh) (hs : s ∈ Dh)
    (hts : wvec z ν t = wvec z ν s) : t * s⁻¹ ∈ D := by
  rw [← h.wvec_eq_zero_iff (mul_mem ht (inv_mem hs)), h.wvec_mul ht (inv_mem hs), h.wvec_inv hs,
    hts, vec_add_self]

theorem exists_wvec (h : JBase τ lev z ν A D C E Dh) (v : Fin 3 → ZMod 2) :
    ∃ t ∈ Dh, wvec z ν t = v := by
  obtain ⟨c, hc, hcv⟩ := h.ν_surj (symThreeDiagSection v)
  obtain ⟨t, ht, hte⟩ := h.zt_surj c hc
  refine ⟨t, ht, ?_⟩
  rw [wvec_def, ← h.dν_eq_of_inv_mul_mem (h.zt_C t ht) hte, hcv]
  funext k
  simp [symThreeDiag, symThreeDiagSection]

theorem wvec_lev (h : JBase τ lev z ν A D C E Dh) (g : GL (Fin 3) (ZMod 2)) {t : G}
    (ht : t ∈ Dh) : wvec z ν (lev g * t * (lev g)⁻¹) = (g : M₃) *ᵥ wvec z ν t := by
  rw [wvec_def, wvec_def, h.dν_eq_of_mul_inv_mem (h.ν_lev g _ (h.zt_C t ht)).1 (h.zt_lev g t ht),
    (h.ν_lev g _ (h.zt_C t ht)).2, symThreeDiag_coe_congr]

theorem comm_A (h : JBase τ lev z ν A D C E Dh) {t a : G} (ht : t ∈ Dh) (ha : a ∈ A) :
    a * t = t * a := by
  have hle : A ≤ centralizer ({t} : Set G) := by
    rw [← h.A_sq, closure_le]
    rintro _ ⟨c, hc, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff, pow_two]
    set e := c⁻¹ * t⁻¹ * c * t with he
    have heE : e ∈ E := h.C_Dh c hc t ht
    have h1 : t⁻¹ * c * t = c * e := by rw [he]; group
    have hce := h.comm_of_mem heE hc
    have hee := h.E_sq e heE
    have h2 : t⁻¹ * (c * c) * t = c * c := by
      calc t⁻¹ * (c * c) * t = (t⁻¹ * c * t) * (t⁻¹ * c * t) := by group
        _ = c * (e * c) * e := by rw [h1]; group
        _ = c * c * (e * e) := by rw [hce]; group
        _ = c * c := by rw [hee, mul_one]
    calc c * c * t = t * (t⁻¹ * (c * c) * t) := by group
      _ = t * (c * c) := by rw [h2]
  exact mem_centralizer_singleton_iff.1 (hle ha)

theorem conj_mul_inv_mem_A (h : JBase τ lev z ν A D C E Dh) {t e : G} (ht : t ∈ Dh)
    (he : e ∈ E) : t⁻¹ * e * t * e⁻¹ ∈ A := by
  have he'E : t⁻¹ * e * t ∈ E := h.conj_inv_mem_E ht he
  have hkC : z⁻¹ * (t⁻¹ * z * t) ∈ C := h.zt_C t ht
  have hze : z⁻¹ * (e⁻¹ * z * e) ∈ A := by
    rw [h.zcomm e (h.E_D he)]
    exact h.τ_mem _
  have hfix := h.comm_A ht hze
  have hconj : t⁻¹ * (z⁻¹ * (e⁻¹ * z * e)) * t =
      z⁻¹ * ((t⁻¹ * e * t)⁻¹ * z * (t⁻¹ * e * t)) := by
    generalize hk : z⁻¹ * (t⁻¹ * z * t) = k at hkC
    have hzk : t⁻¹ * z * t = z * k := by rw [← hk]; group
    have e1 : t⁻¹ * (z⁻¹ * (e⁻¹ * z * e)) * t =
        (t⁻¹ * z * t)⁻¹ * (t⁻¹ * e * t)⁻¹ * (t⁻¹ * z * t) * (t⁻¹ * e * t) := by group
    rw [e1, hzk]
    generalize t⁻¹ * e * t = e' at he'E ⊢
    have hx : z⁻¹ * e'⁻¹ * z ∈ E := h.conj_inv_mem_E h.z_Dh (inv_mem he'E)
    have hkx := h.comm_of_mem hx hkC
    calc (z * k)⁻¹ * e'⁻¹ * (z * k) * e' = k⁻¹ * ((z⁻¹ * e'⁻¹ * z) * k) * e' := by group
      _ = k⁻¹ * (k * (z⁻¹ * e'⁻¹ * z)) * e' := by rw [hkx]
      _ = z⁻¹ * (e'⁻¹ * z * e') := by group
  have heq : z⁻¹ * (e⁻¹ * z * e) = z⁻¹ * ((t⁻¹ * e * t)⁻¹ * z * (t⁻¹ * e * t)) := by
    rw [← hconj]
    calc z⁻¹ * (e⁻¹ * z * e) = t⁻¹ * (t * (z⁻¹ * (e⁻¹ * z * e))) := by group
      _ = t⁻¹ * (z⁻¹ * (e⁻¹ * z * e) * t) := by rw [hfix]
      _ = t⁻¹ * (z⁻¹ * (e⁻¹ * z * e)) * t := by group
  have h2 := mul_left_cancel heq
  generalize t⁻¹ * e * t = e' at he'E h2 ⊢
  have hfE : e' * e⁻¹ ∈ E := mul_mem he'E (inv_mem he)
  have hzf : z⁻¹ * ((e' * e⁻¹)⁻¹ * z * (e' * e⁻¹)) = 1 := by
    calc z⁻¹ * ((e' * e⁻¹)⁻¹ * z * (e' * e⁻¹)) = z⁻¹ * (e * (e'⁻¹ * z * e') * e⁻¹) := by
          group
      _ = z⁻¹ * (e * (e⁻¹ * z * e) * e⁻¹) := by rw [h2]
      _ = 1 := by group
  have hνf : ν (e' * e⁻¹) = 0 := by
    have h3 := h.zcomm _ (h.E_D hfE)
    rw [hzf] at h3
    have h4 : τ (Multiplicative.ofAdd (ν (e' * e⁻¹))) = τ (Multiplicative.ofAdd 0) := by
      rw [← h3, ofAdd_zero, map_one]
    exact Multiplicative.ofAdd.injective (h.τ_inj h4)
  exact (h.ν_A _ (h.E_C hfE)).1 hνf

theorem conj_mul_inv_mul (h : JBase τ lev z ν A D C E Dh) {t x y : G} (ht : t ∈ Dh)
    (hx : x ∈ E) (hy : y ∈ E) :
    t⁻¹ * (x * y) * t * (x * y)⁻¹ = (t⁻¹ * x * t * x⁻¹) * (t⁻¹ * y * t * y⁻¹) := by
  have hc := h.E_comm (inv_mem hx) (mul_mem (h.conj_inv_mem_E ht hy) (inv_mem hy))
  calc t⁻¹ * (x * y) * t * (x * y)⁻¹ = (t⁻¹ * x * t) * (x⁻¹ * ((t⁻¹ * y * t) * y⁻¹)) := by
        rw [hc]; group
    _ = (t⁻¹ * x * t * x⁻¹) * (t⁻¹ * y * t * y⁻¹) := by group

theorem conj_mul_inv_A (h : JBase τ lev z ν A D C E Dh) {t a : G} (ht : t ∈ Dh) (ha : a ∈ A) :
    t⁻¹ * a * t * a⁻¹ = 1 := by
  rw [mul_assoc t⁻¹, h.comm_A ht ha]
  group

theorem conj_mul_inv_comp (h : JBase τ lev z ν A D C E Dh) {s t x : G} (hs : s ∈ Dh)
    (ht : t ∈ Dh) (hx : x ∈ E) :
    (s * t)⁻¹ * x * (s * t) * x⁻¹ = (s⁻¹ * x * s * x⁻¹) * (t⁻¹ * x * t * x⁻¹) := by
  have ha := h.conj_mul_inv_mem_A hs hx
  have hc := h.comm_A ht ha
  calc (s * t)⁻¹ * x * (s * t) * x⁻¹ =
        t⁻¹ * ((s⁻¹ * x * s * x⁻¹) * x) * t * x⁻¹ := by group
    _ = t⁻¹ * ((s⁻¹ * x * s * x⁻¹) * t) * (t⁻¹ * x * t * x⁻¹) := by group
    _ = (s⁻¹ * x * s * x⁻¹) * (t⁻¹ * x * t * x⁻¹) := by rw [hc]; group

end JBase

@[expose] def τinv (τ : Multiplicative 𝕊 →* G) (x : G) : 𝕊 :=
  Classical.epsilon fun B : 𝕊 => τ (Multiplicative.ofAdd B) = x

@[expose] def ealt (E : Subgroup G) (ν : G → 𝕊) (c : Fin 3 → ZMod 2) : G :=
  Classical.epsilon fun x : G => x ∈ E ∧ ν x = altS c

@[expose] def Ft (τ : Multiplicative 𝕊 →* G) (E : Subgroup G) (ν : G → 𝕊) (t : G)
    (c : Fin 3 → ZMod 2) : 𝕊 :=
  τinv τ (t⁻¹ * ealt E ν c * t * (ealt E ν c)⁻¹)

@[expose] def yt (τ : Multiplicative 𝕊 →* G) (E : Subgroup G) (ν : G → 𝕊) (t : G) :
    Fin 3 → 𝕊 :=
  fun i => Ft τ E ν t (Pi.single i 1)

theorem sym_zero_smul (X : 𝕊) : (0 : ZMod 2) • X = 0 :=
  Subtype.ext (by rw [coe_smul_binarySymMatrices, zero_smul]; rfl)

theorem sym_one_smul (X : 𝕊) : (1 : ZMod 2) • X = X :=
  Subtype.ext (by rw [coe_smul_binarySymMatrices, one_smul])

theorem sym_smul_zero (a : ZMod 2) : a • (0 : 𝕊) = 0 :=
  Subtype.ext (by rw [coe_smul_binarySymMatrices]; exact smul_zero a)

theorem lin3_zero (c : Fin 3 → ZMod 2) : lin3 c 0 = 0 := by
  simp only [lin3, Pi.zero_apply, sym_smul_zero, add_zero]

theorem altS_add (c c' : Fin 3 → ZMod 2) : altS c + altS c' = altS (c + c') := by
  apply Subtype.ext
  change symThreeAlt c + symThreeAlt c' = symThreeAlt (c + c')
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symThreeAlt]

namespace JBase

variable {τ : Multiplicative 𝕊 →* G} {lev : GL (Fin 3) (ZMod 2) →* G} {z : G} {ν : G → 𝕊}
  {A D C E Dh : Subgroup G}

theorem τ_τinv (h : JBase τ lev z ν A D C E Dh) {x : G} (hx : x ∈ A) :
    τ (Multiplicative.ofAdd (τinv τ x)) = x := by
  obtain ⟨B, rfl⟩ := (h.mem_A x).1 hx
  exact Classical.epsilon_spec (p := fun B' : 𝕊 => τ (Multiplicative.ofAdd B') = τ B)
    ⟨Multiplicative.toAdd B, rfl⟩

theorem τinv_τ (h : JBase τ lev z ν A D C E Dh) (B : 𝕊) :
    τinv τ (τ (Multiplicative.ofAdd B)) = B :=
  Multiplicative.ofAdd.injective (h.τ_inj (h.τ_τinv (h.τ_mem _)))

theorem τinv_mul (h : JBase τ lev z ν A D C E Dh) {x y : G} (hx : x ∈ A) (hy : y ∈ A) :
    τinv τ (x * y) = τinv τ x + τinv τ y := by
  conv_lhs => rw [← h.τ_τinv hx, ← h.τ_τinv hy, ← map_mul, ← ofAdd_add]
  exact h.τinv_τ _

theorem τinv_one (h : JBase τ lev z ν A D C E Dh) : τinv τ 1 = 0 := by
  have e : (1 : G) = τ (Multiplicative.ofAdd 0) := by rw [ofAdd_zero, map_one]
  rw [e, h.τinv_τ]

theorem eq_one_of_τinv_eq_zero (h : JBase τ lev z ν A D C E Dh) {x : G} (hx : x ∈ A)
    (h0 : τinv τ x = 0) : x = 1 := by
  rw [← h.τ_τinv hx, h0, ofAdd_zero, map_one]

theorem τinv_lev (h : JBase τ lev z ν A D C E Dh) (g : GL (Fin 3) (ZMod 2)) {x : G}
    (hx : x ∈ A) : τinv τ (lev g * x * (lev g)⁻¹) = symThreeCongr g (τinv τ x) := by
  conv_lhs => rw [← h.τ_τinv hx]
  rw [h.lev_τ, toAdd_ofAdd, h.τinv_τ]

theorem ealt_spec (h : JBase τ lev z ν A D C E Dh) (c : Fin 3 → ZMod 2) :
    ealt E ν c ∈ E ∧ ν (ealt E ν c) = altS c := by
  obtain ⟨x, hx, hxc⟩ := h.ν_surj (altS c)
  have hxE : x ∈ E := (h.ν_E x hx).1 (by rw [hxc]; exact symThreeDiag_alt c)
  exact Classical.epsilon_spec (p := fun x : G => x ∈ E ∧ ν x = altS c) ⟨x, hxE, hxc⟩

theorem conj_eq_ealt (h : JBase τ lev z ν A D C E Dh) {t x : G} (ht : t ∈ Dh) (hx : x ∈ E)
    {c : Fin 3 → ZMod 2} (hxc : ν x = altS c) :
    t⁻¹ * x * t * x⁻¹ = t⁻¹ * ealt E ν c * t * (ealt E ν c)⁻¹ := by
  obtain ⟨he, hec⟩ := h.ealt_spec c
  have haE : x * (ealt E ν c)⁻¹ ∈ E := mul_mem hx (inv_mem he)
  have haA : x * (ealt E ν c)⁻¹ ∈ A := by
    refine (h.ν_A _ (h.E_C haE)).1 ?_
    rw [h.ν_mul x (h.E_C hx) _ (inv_mem (h.E_C he)), h.ν_inv (h.E_C he), hxc, hec,
      sym_add_self]
  have e1 := h.conj_mul_inv_mul ht haE he
  rwa [inv_mul_cancel_right, h.conj_mul_inv_A ht haA, one_mul] at e1

theorem conj_ealt_mem_A (h : JBase τ lev z ν A D C E Dh) {t : G} (ht : t ∈ Dh)
    (c : Fin 3 → ZMod 2) : t⁻¹ * ealt E ν c * t * (ealt E ν c)⁻¹ ∈ A :=
  h.conj_mul_inv_mem_A ht (h.ealt_spec c).1

theorem Ft_add (h : JBase τ lev z ν A D C E Dh) {t : G} (ht : t ∈ Dh) (c c' : Fin 3 → ZMod 2) :
    Ft τ E ν t (c + c') = Ft τ E ν t c + Ft τ E ν t c' := by
  obtain ⟨he, hec⟩ := h.ealt_spec c
  obtain ⟨he', hec'⟩ := h.ealt_spec c'
  have hν : ν (ealt E ν c * ealt E ν c') = altS (c + c') := by
    rw [h.ν_mul _ (h.E_C he) _ (h.E_C he'), hec, hec', altS_add]
  unfold Ft
  rw [← h.conj_eq_ealt ht (mul_mem he he') hν, h.conj_mul_inv_mul ht he he',
    h.τinv_mul (h.conj_mul_inv_mem_A ht he) (h.conj_mul_inv_mem_A ht he')]

theorem Ft_zero (h : JBase τ lev z ν A D C E Dh) {t : G} (ht : t ∈ Dh) : Ft τ E ν t 0 = 0 := by
  have e := h.Ft_add ht 0 0
  rw [add_zero] at e
  exact left_eq_add.1 e

theorem Ft_smul (h : JBase τ lev z ν A D C E Dh) {t : G} (ht : t ∈ Dh) (a : ZMod 2)
    (c : Fin 3 → ZMod 2) : Ft τ E ν t (a • c) = a • Ft τ E ν t c := by
  rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 by decide) a with rfl | rfl
  · rw [zero_smul, sym_zero_smul]
    exact h.Ft_zero ht
  · rw [one_smul, sym_one_smul]

theorem single_sum (c : Fin 3 → ZMod 2) :
    c = c 0 • Pi.single 0 1 + c 1 • Pi.single 1 1 + c 2 • Pi.single 2 1 := by
  funext k
  fin_cases k <;> simp

theorem Ft_eq_lin3 (h : JBase τ lev z ν A D C E Dh) {t : G} (ht : t ∈ Dh) (c : Fin 3 → ZMod 2) :
    Ft τ E ν t c = lin3 c (yt τ E ν t) := by
  conv_lhs => rw [single_sum c]
  rw [h.Ft_add ht, h.Ft_add ht, h.Ft_smul ht, h.Ft_smul ht, h.Ft_smul ht]
  rfl

theorem Ft_mul (h : JBase τ lev z ν A D C E Dh) {s t : G} (hs : s ∈ Dh) (ht : t ∈ Dh)
    (c : Fin 3 → ZMod 2) : Ft τ E ν (s * t) c = Ft τ E ν s c + Ft τ E ν t c := by
  unfold Ft
  rw [h.conj_mul_inv_comp hs ht (h.ealt_spec c).1,
    h.τinv_mul (h.conj_ealt_mem_A hs c) (h.conj_ealt_mem_A ht c)]

theorem Ft_C (h : JBase τ lev z ν A D C E Dh) {k : G} (hk : k ∈ C) (c : Fin 3 → ZMod 2) :
    Ft τ E ν k c = 0 := by
  unfold Ft
  have hc := h.comm_of_mem (h.ealt_spec c).1 hk
  have e : k⁻¹ * ealt E ν c * k * (ealt E ν c)⁻¹ = 1 := by
    rw [mul_assoc k⁻¹, hc]
    group
  rw [e, h.τinv_one]

theorem Ft_z (h : JBase τ lev z ν A D C E Dh) (c : Fin 3 → ZMod 2) : Ft τ E ν z c = altS c := by
  unfold Ft
  obtain ⟨he, hec⟩ := h.ealt_spec c
  have hinv : (ealt E ν c)⁻¹ = ealt E ν c := inv_eq_of_mul_eq_one_right (h.E_sq _ he)
  have e : z⁻¹ * ealt E ν c * z * (ealt E ν c)⁻¹ =
      z⁻¹ * ((ealt E ν c)⁻¹ * z * ealt E ν c) := by
    rw [hinv]
    group
  rw [e, h.zcomm _ (h.E_D he), h.τinv_τ, hec]

theorem Ft_lev (h : JBase τ lev z ν A D C E Dh) (g : GL (Fin 3) (ZMod 2)) {t : G} (ht : t ∈ Dh)
    {c c' : Fin 3 → ZMod 2} (hcc' : symThreeCongr g⁻¹ (altS c) = altS c') :
    Ft τ E ν (lev g * t * (lev g)⁻¹) c = symThreeCongr g (Ft τ E ν t c') := by
  unfold Ft
  obtain ⟨he, hec⟩ := h.ealt_spec c
  set x := ealt E ν c with hx
  have e1 : (lev g * t * (lev g)⁻¹)⁻¹ * x * (lev g * t * (lev g)⁻¹) * x⁻¹ =
      lev g * (t⁻¹ * ((lev g)⁻¹ * x * lev g) * t * ((lev g)⁻¹ * x * lev g)⁻¹) * (lev g)⁻¹ := by
    group
  have hy := h.ν_lev g⁻¹ x (h.E_C he)
  rw [map_inv, inv_inv, hec, hcc'] at hy
  have hyE : (lev g)⁻¹ * x * lev g ∈ E := (h.ν_E _ hy.1).1 (by rw [hy.2]; exact symThreeDiag_alt c')
  rw [e1, h.conj_eq_ealt ht hyE hy.2, h.τinv_lev g (h.conj_ealt_mem_A ht c')]

theorem yt_apply (t : G) (i : Fin 3) : yt τ E ν t i = Ft τ E ν t (Pi.single i 1) :=
  rfl

theorem yt_mul (h : JBase τ lev z ν A D C E Dh) {s t : G} (hs : s ∈ Dh) (ht : t ∈ Dh) :
    yt τ E ν (s * t) = yt τ E ν s + yt τ E ν t := by
  funext i
  exact h.Ft_mul hs ht _

theorem yt_C (h : JBase τ lev z ν A D C E Dh) {k : G} (hk : k ∈ C) : yt τ E ν k = 0 := by
  funext i
  exact h.Ft_C hk _

theorem yt_z (h : JBase τ lev z ν A D C E Dh) : yt τ E ν z = iotaY := by
  funext i
  exact h.Ft_z _

theorem yt_lev (h : JBase τ lev z ν A D C E Dh) (g : GL (Fin 3) (ZMod 2))
    (hg : ∀ i : Fin 3, symThreeCongr g⁻¹ (altS (Pi.single i 1)) =
      altS (fun j => (g : M₃) i j)) {t : G} (ht : t ∈ Dh) :
    yt τ E ν (lev g * t * (lev g)⁻¹) = actY g (yt τ E ν t) := by
  funext i
  rw [yt_apply, h.Ft_lev g ht (hg i), h.Ft_eq_lin3 ht]
  rfl

theorem yt_D (h : JBase τ lev z ν A D C E Dh) {d : G} (hd : d ∈ D) :
    yt τ E ν d = 0 ∨ yt τ E ν d = iotaY := by
  rcases h.D_C d hd with hc | hc
  · exact Or.inl (h.yt_C hc)
  · right
    have e : d = z * (z * d) := by rw [← mul_assoc, h.z_sq, one_mul]
    rw [e, h.yt_mul h.z_Dh (h.C_le_Dh hc), h.yt_z, h.yt_C hc, add_zero]

theorem comm_of_yt_eq_zero (h : JBase τ lev z ν A D C E Dh) {t : G} (ht : t ∈ Dh)
    (h0 : yt τ E ν t = 0) {x : G} (hx : x ∈ E) : x * t = t * x := by
  have hxc : ν x = altS (symThreeOff (ν x : M₃)) :=
    Subtype.ext (eq_symThreeAlt (ν x).2 (h.dν_E hx))
  have e1 := h.conj_eq_ealt ht hx hxc
  have e2 : Ft τ E ν t (symThreeOff (ν x : M₃)) = 0 := by
    rw [h.Ft_eq_lin3 ht, h0, lin3_zero]
  have e3 := h.eq_one_of_τinv_eq_zero (h.conj_ealt_mem_A ht _) e2
  rw [← e1] at e3
  have e4 : t⁻¹ * x * t = x := mul_inv_eq_one.1 e3
  calc x * t = t * (t⁻¹ * x * t) := by group
    _ = t * x := by rw [e4]

end JBase

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.Jhat
