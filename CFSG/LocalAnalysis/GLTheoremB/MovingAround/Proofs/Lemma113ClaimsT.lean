module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma113ClaimsI3011

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma113Claims.T

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G]

structure Hyp (T E Q0 : Subgroup G) (e m : G) : Prop where
  Tcard : Nat.card ↥T = 3 ^ 7
  Eel : IsElemAbelian 3 E
  Ecard : Nat.card ↥E = 3 ^ 4
  ET : E ≤ T
  Qel : IsElemAbelian 3 Q0
  Qcard : Nat.card ↥Q0 = 3 ^ 3
  QE : Q0 ≤ E
  eE : e ∈ E
  eQ : e ∉ Q0
  Qcent : ∀ r ∈ T, ∀ q ∈ Q0, r * q = q * r
  θQ : ∀ r ∈ T, ⁅r, e⁆ ∈ Q0
  θker : ∀ r ∈ T, r * e = e * r → r ∈ E
  θsurj : ∀ q ∈ Q0, ∃ r ∈ T, ⁅r, e⁆ = q
  mT : ∀ r ∈ T, m * r * m⁻¹ ∈ T
  mQ : ∀ r ∈ Q0, m * r * m⁻¹ ∈ Q0
  me : m * e * m⁻¹ = e
  m13 : ∃ a : ℕ, m ^ 13 ^ a = 1
  m13Q : ∀ q ∈ Q0, m ^ 13 * q * (m ^ 13)⁻¹ = q
  mfix : ∀ q ∈ Q0, m * q * m⁻¹ = q → q = 1

theorem vanishing_V1 [Finite G] {Q0 : Subgroup G} {m : G} (hQel : IsElemAbelian 3 Q0)
    (hQcard : Nat.card Q0 = 3 ^ 3) (hmQ : ∀ q ∈ Q0, m * q * m⁻¹ ∈ Q0)
    (hm13Q : ∀ q ∈ Q0, m ^ 13 * q * (m ^ 13)⁻¹ = q) (hm1 : ∃ q ∈ Q0, m * q * m⁻¹ ≠ q)
    (β : G → G → G) (hβQ : ∀ a ∈ Q0, ∀ b ∈ Q0, β a b ∈ Q0)
    (hβl : ∀ a ∈ Q0, ∀ a' ∈ Q0, ∀ b ∈ Q0, β (a * a') b = β a b * β a' b)
    (hβr : ∀ a ∈ Q0, ∀ b ∈ Q0, ∀ b' ∈ Q0, β a (b * b') = β a b * β a b')
    (hβa : ∀ a ∈ Q0, β a a = 1)
    (hβm : ∀ a ∈ Q0, ∀ b ∈ Q0, β (m * a * m⁻¹) (m * b * m⁻¹) = m * β a b * m⁻¹) :
    ∀ a ∈ Q0, ∀ b ∈ Q0, β a b = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : CommGroup Q0 := { (inferInstance : Group Q0) with mul_comm := hQel.1.is_comm.comm }
  letI : Module (ZMod 3) (Additive Q0) := AddCommGroup.zmodModule (n := 3) fun x => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact Subtype.ext (by simpa using hQel.2 _ x.toMul.2)
  let cm : Q0 →* Q0 := MonoidHom.mk' (fun x => ⟨m * x * m⁻¹, hmQ x x.2⟩)
    (fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group))
  let g : Additive Q0 →ₗ[ZMod 3] Additive Q0 := (MonoidHom.toAdditive cm).toZModLinearMap 3
  have hg : ∀ u : Additive Q0,
      ((Additive.toMul (g u) : Q0) : G) = m * (Additive.toMul u : Q0) * m⁻¹ := fun u => rfl
  let f : Additive Q0 → Additive Q0 → Additive Q0 := fun u v =>
    Additive.ofMul ⟨β ((Additive.toMul u : Q0) : G) ((Additive.toMul v : Q0) : G),
      hβQ _ (Additive.toMul u).2 _ (Additive.toMul v).2⟩
  have hf : ∀ u v, ((Additive.toMul (f u v) : Q0) : G) =
      β (Additive.toMul u : Q0) (Additive.toMul v : Q0) := fun u v => rfl
  have H1 : ∀ u₁ u₂ v, f (u₁ + u₂) v = f u₁ v + f u₂ v := fun u₁ u₂ v => by
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [toMul_add, Subgroup.coe_mul, hf, hf, hf, toMul_add, Subgroup.coe_mul]
    exact hβl _ (Additive.toMul u₁).2 _ (Additive.toMul u₂).2 _ (Additive.toMul v).2
  have H3 : ∀ u v₁ v₂, f u (v₁ + v₂) = f u v₁ + f u v₂ := fun u v₁ v₂ => by
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [toMul_add, Subgroup.coe_mul, hf, hf, hf, toMul_add, Subgroup.coe_mul]
    exact hβr _ (Additive.toMul u).2 _ (Additive.toMul v₁).2 _ (Additive.toMul v₂).2
  let β' : Additive Q0 →ₗ[ZMod 3] Additive Q0 →ₗ[ZMod 3] Additive Q0 :=
    LinearMap.mk₂ (ZMod 3) f H1
      (fun c u v => ZMod.map_smul (AddMonoidHom.mk' (fun u => f u v) (fun u₁ u₂ => H1 u₁ u₂ v)) c u)
      H3
      (fun c u v => ZMod.map_smul (AddMonoidHom.mk' (f u) (H3 u)) c v)
  have hV : Module.finrank (ZMod 3) (Additive Q0) = 3 := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := Additive Q0)
    rw [Nat.card_zmod, Nat.card_congr Additive.toMul, hQcard] at h1
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) h1).symm
  have hit : ∀ (n : ℕ) (u : Additive Q0),
      ((Additive.toMul ((g ^ n) u) : Q0) : G) = m ^ n * (Additive.toMul u : Q0) * (m ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro u; simp
    | succ n ih =>
      intro u
      rw [pow_succ', Module.End.mul_apply, hg, ih]
      group
  have h13 : g ^ 13 = 1 := by
    apply LinearMap.ext
    intro u
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [hit, Module.End.one_apply]
    exact hm13Q _ (Additive.toMul u).2
  have hg1 : g ≠ 1 := by
    obtain ⟨q, hq, hmq⟩ := hm1
    intro hg1
    apply hmq
    have h1 : g (Additive.ofMul ⟨q, hq⟩) = Additive.ofMul ⟨q, hq⟩ := by
      rw [hg1, Module.End.one_apply]
    exact congrArg (fun u : Additive Q0 => ((Additive.toMul u : Q0) : G)) h1
  have hβ0 : ∀ v, β' v v = 0 := fun v => by
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [toMul_zero, OneMemClass.coe_one]
    exact hβa _ (Additive.toMul v).2
  have hβg : ∀ v w, β' (g v) (g w) = g (β' v w) := fun v w => by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact hβm _ (Additive.toMul v).2 _ (Additive.toMul w).2
  have hzero := input30_11_holds (Additive Q0) hV g h13 hg1 β' hβ0 hβg
  intro a ha b hb
  have h1 : β' (Additive.ofMul ⟨a, ha⟩) (Additive.ofMul ⟨b, hb⟩) = 0 := by
    rw [hzero]
    rfl
  exact congrArg (fun u : Additive Q0 => ((Additive.toMul u : Q0) : G)) h1

namespace Hyp

variable [Finite G] {T E Q0 : Subgroup G} {e m : G} (h : Hyp T E Q0 e m)
include h

theorem QT : Q0 ≤ T := h.QE.trans h.ET

theorem eT : e ∈ T := h.ET h.eE

theorem Qcomm {a b : G} (ha : a ∈ Q0) (hb : b ∈ Q0) : a * b = b * a :=
  h.Qcent a (h.QT ha) b hb

theorem Ecomm {a b : G} (ha : a ∈ E) (hb : b ∈ E) : a * b = b * a := by
  haveI := h.Eel.1
  exact setLike_mul_comm ha hb

theorem Q3 {a : G} (ha : a ∈ Q0) : a ^ 3 = 1 := h.Qel.2 a ha

theorem e3 : e ^ 3 = 1 := h.Eel.2 e h.eE

theorem θ_mul {r s : G} (hr : r ∈ T) (hs : s ∈ T) : ⁅r * s, e⁆ = ⁅r, e⁆ * ⁅s, e⁆ := by
  have hb := h.θQ s hs
  have h1 : r * ⁅s, e⁆ = ⁅s, e⁆ * r := h.Qcent r hr _ hb
  calc ⁅r * s, e⁆ = r * ⁅s, e⁆ * e * r⁻¹ * e⁻¹ := by simp only [commutatorElement_def]; group
    _ = ⁅s, e⁆ * ⁅r, e⁆ := by rw [h1]; simp only [commutatorElement_def]; group
    _ = ⁅r, e⁆ * ⁅s, e⁆ := h.Qcomm hb (h.θQ r hr)

theorem θ_inv {r : G} (hr : r ∈ T) : ⁅r⁻¹, e⁆ = ⁅r, e⁆⁻¹ := by
  have := h.θ_mul (T.inv_mem hr) hr
  rw [inv_mul_cancel, commutatorElement_one_left] at this
  exact eq_inv_of_mul_eq_one_left this.symm

theorem θ_conj {y z : G} (hy : y ∈ T) (hz : z ∈ T) : ⁅y * z * y⁻¹, e⁆ = ⁅z, e⁆ := by
  rw [h.θ_mul (T.mul_mem hy hz) (T.inv_mem hy), h.θ_mul hy hz, h.θ_inv hy,
    h.Qcomm (h.θQ y hy) (h.θQ z hz), mul_inv_cancel_right]

theorem θ_m (r : G) : ⁅m * r * m⁻¹, e⁆ = m * ⁅r, e⁆ * m⁻¹ := by
  calc ⁅m * r * m⁻¹, e⁆ = ⁅m * r * m⁻¹, m * e * m⁻¹⁆ := by rw [h.me]
    _ = m * ⁅r, e⁆ * m⁻¹ := by simp only [commutatorElement_def]; group

theorem θ_eq_one {c : G} (hc : c ∈ E) : ⁅c, e⁆ = 1 :=
  commutatorElement_eq_one_iff_mul_comm.mpr (h.Ecomm hc h.eE)

theorem mem_E {r : G} (hr : r ∈ T) (h1 : ⁅r, e⁆ = 1) : r ∈ E :=
  h.θker r hr (commutatorElement_eq_one_iff_mul_comm.mp h1)

theorem e_comm_mem {w : G} (hw : w ∈ T) : ⁅e, w⁆ ∈ Q0 := by
  rw [← commutatorElement_inv]
  exact Q0.inv_mem (h.θQ w hw)

theorem e_comm_conj {y z : G} (hy : y ∈ T) (hz : z ∈ T) : ⁅e, y * z * y⁻¹⁆ = ⁅e, z⁆ := by
  rw [← commutatorElement_inv, h.θ_conj hy hz, commutatorElement_inv]

theorem e2_not_mem : e ^ 2 ∉ Q0 := by
  intro h2
  apply h.eQ
  have : (e ^ 2) ^ 2 = e ^ 3 * e := by group
  rw [h.e3, one_mul] at this
  rw [← this]
  exact Q0.pow_mem h2 2

theorem e2_inv : (e ^ 2)⁻¹ = e := by
  rw [inv_eq_iff_mul_eq_one, ← pow_succ, h.e3]

theorem pow_mul_inv_mem {k l : Fin 3} (hkl : e ^ (k : ℕ) * (e ^ (l : ℕ))⁻¹ ∈ Q0) : k = l := by
  have hQ1 := h.eQ
  have hQ2 := h.e2_not_mem
  have h2 := h.e2_inv
  fin_cases k <;> fin_cases l <;> simp at hkl ⊢
  all_goals first
    | exact hQ1 hkl
    | exact hQ2 hkl
    | (rw [h2, ← pow_two] at hkl; exact hQ2 hkl)
    | (rw [show e ^ 2 * e⁻¹ = e by group] at hkl; exact hQ1 hkl)

theorem E_decomp {c : G} (hc : c ∈ E) : ∃ k : Fin 3, ∃ q ∈ Q0, c = q * e ^ (k : ℕ) := by
  let f : Fin 3 × Q0 → E := fun p =>
    ⟨p.2 * e ^ (p.1 : ℕ), E.mul_mem (h.QE p.2.2) (E.pow_mem h.eE _)⟩
  have hf : Function.Injective f := by
    rintro ⟨k, q⟩ ⟨l, q'⟩ hkl
    have h1 : (q : G) * e ^ (k : ℕ) = q' * e ^ (l : ℕ) := congrArg Subtype.val hkl
    have h2 : e ^ (k : ℕ) * (e ^ (l : ℕ))⁻¹ = (q : G)⁻¹ * q' := by
      calc e ^ (k : ℕ) * (e ^ (l : ℕ))⁻¹ = (q : G)⁻¹ * (q * e ^ (k : ℕ)) * (e ^ (l : ℕ))⁻¹ := by
            group
        _ = (q : G)⁻¹ * q' := by rw [h1]; group
    have hkl' : k = l := h.pow_mul_inv_mem (h2 ▸ Q0.mul_mem (Q0.inv_mem q.2) q'.2)
    subst hkl'
    have : q = q' := Subtype.ext (mul_right_cancel h1)
    rw [this]
  have hcard : Nat.card E ≤ Nat.card (Fin 3 × Q0) := by
    rw [Nat.card_prod, h.Qcard, h.Ecard]
    simp
  obtain ⟨⟨k, q⟩, hq⟩ := (hf.bijective_of_nat_card_le hcard).2 ⟨c, hc⟩
  exact ⟨k, q, q.2, (congrArg Subtype.val hq).symm⟩

theorem comm_e_pow {w : G} (hw : w ∈ T) (n : ℕ) : ⁅e ^ n, w⁆ = ⁅e, w⁆ ^ n := by
  have hb := h.e_comm_mem hw
  induction n with
  | zero => simp
  | succ n ih =>
    have hc : ⁅e, w⁆ ^ n * e = e * ⁅e, w⁆ ^ n := h.Ecomm (h.QE (Q0.pow_mem hb n)) h.eE
    calc ⁅e ^ (n + 1), w⁆ = e * ⁅e ^ n, w⁆ * (w * e⁻¹ * w⁻¹) := by
          simp only [commutatorElement_def]; group
      _ = ⁅e, w⁆ ^ n * (e * (w * e⁻¹ * w⁻¹)) := by rw [ih, ← hc]; exact mul_assoc _ _ _
      _ = ⁅e, w⁆ ^ n * ⁅e, w⁆ := by congr 1; simp only [commutatorElement_def]; group
      _ = ⁅e, w⁆ ^ (n + 1) := (pow_succ _ _).symm

theorem comm_Qe_pow {q w : G} (hq : q ∈ Q0) (hw : w ∈ T) (n : ℕ) :
    ⁅q * e ^ n, w⁆ = ⁅e, w⁆ ^ n := by
  have hX : ⁅e ^ n, w⁆ ∈ Q0 := by rw [h.comm_e_pow hw]; exact Q0.pow_mem (h.e_comm_mem hw) n
  have hqw : Commute w q := h.Qcent w hw q hq
  have hqX : q * ⁅e ^ n, w⁆ = ⁅e ^ n, w⁆ * q := h.Qcomm hq hX
  rw [← h.comm_e_pow hw]
  calc ⁅q * e ^ n, w⁆ = q * ⁅e ^ n, w⁆ * (w * q⁻¹ * w⁻¹) := by
        simp only [commutatorElement_def]; group
    _ = q * ⁅e ^ n, w⁆ * q⁻¹ := by rw [hqw.inv_right.eq, mul_inv_cancel_right]
    _ = ⁅e ^ n, w⁆ := by rw [hqX, mul_inv_cancel_right]

theorem comm_E {c w : G} (hc : c ∈ E) (hw : w ∈ T) : ∃ k : Fin 3, ⁅c, w⁆ = ⁅e, w⁆ ^ (k : ℕ) := by
  obtain ⟨k, q, hq, rfl⟩ := h.E_decomp hc
  exact ⟨k, h.comm_Qe_pow hq hw k⟩

theorem comm_mem_T {x y : G} (hx : x ∈ T) (hy : y ∈ T) : ⁅x, y⁆ ∈ T :=
  T.mul_mem (T.mul_mem (T.mul_mem hx hy) (T.inv_mem hx)) (T.inv_mem hy)

theorem comm_mem_E {x y : G} (hx : x ∈ T) (hy : y ∈ T) : ⁅x, y⁆ ∈ E := by
  have hxy : x * y * x⁻¹ ∈ T := T.mul_mem (T.mul_mem hx hy) (T.inv_mem hx)
  refine h.mem_E (h.comm_mem_T hx hy) ?_
  rw [commutatorElement_def x y, h.θ_mul hxy (T.inv_mem hy), h.θ_conj hx hy, h.θ_inv hy,
    mul_inv_cancel]

omit h in
theorem hall_witt (x y z : G) :
    ⁅⁅x, y⁆, y * z * y⁻¹⁆ * ⁅⁅y, z⁆, z * x * z⁻¹⁆ * ⁅⁅z, x⁆, x * y * x⁻¹⁆ = 1 := by
  simp only [commutatorElement_def]; group

theorem not_comm_eq {x y q : G} (hx : x ∈ T) (hy : y ∈ T) (hq : q ∈ Q0) (hxy : ⁅x, y⁆ = q * e) :
    False := by
  have key : ∀ z ∈ T, ∃ p : Fin 3 × Fin 3,
      ⁅z, e⁆ = ⁅e, x⁆ ^ (p.1 : ℕ) * ⁅e, y⁆ ^ (p.2 : ℕ) := by
    intro z hz
    have hzx : z * x * z⁻¹ ∈ T := T.mul_mem (T.mul_mem hz hx) (T.inv_mem hz)
    have hxy' : x * y * x⁻¹ ∈ T := T.mul_mem (T.mul_mem hx hy) (T.inv_mem hx)
    have hyz : y * z * y⁻¹ ∈ T := T.mul_mem (T.mul_mem hy hz) (T.inv_mem hy)
    obtain ⟨k, hk⟩ := h.comm_E (h.comm_mem_E hy hz) hzx
    obtain ⟨l, hl⟩ := h.comm_E (h.comm_mem_E hz hx) hxy'
    have h1 : ⁅⁅x, y⁆, y * z * y⁻¹⁆ = ⁅e, z⁆ := by
      have := h.comm_Qe_pow hq hyz 1
      rw [pow_one, pow_one] at this
      rw [hxy, this, h.e_comm_conj hy hz]
    have hw := hall_witt x y z
    rw [h1, hk, hl, h.e_comm_conj hz hx, h.e_comm_conj hx hy, mul_assoc] at hw
    refine ⟨(k, l), ?_⟩
    rw [← commutatorElement_inv]
    exact (eq_inv_of_mul_eq_one_right hw).symm
  let φ : Fin 3 × Fin 3 → Q0 := fun p =>
    ⟨⁅e, x⁆ ^ (p.1 : ℕ) * ⁅e, y⁆ ^ (p.2 : ℕ),
      Q0.mul_mem (Q0.pow_mem (h.e_comm_mem hx) _) (Q0.pow_mem (h.e_comm_mem hy) _)⟩
  have hφ : Function.Surjective φ := by
    rintro ⟨a, ha⟩
    obtain ⟨z, hz, rfl⟩ := h.θsurj a ha
    obtain ⟨p, hp⟩ := key z hz
    exact ⟨p, Subtype.ext hp.symm⟩
  have := Nat.card_le_card_of_surjective φ hφ
  rw [h.Qcard, Nat.card_prod] at this
  simp at this

theorem comm_mem_Q {x y : G} (hx : x ∈ T) (hy : y ∈ T) : ⁅x, y⁆ ∈ Q0 := by
  obtain ⟨k, q, hq, hk⟩ := h.E_decomp (h.comm_mem_E hx hy)
  fin_cases k
  · simp only [Fin.zero_eta, Fin.val_zero, pow_zero, mul_one] at hk
    rw [hk]
    exact hq
  · exact (h.not_comm_eq hx hy hq (by simpa using hk)).elim
  · refine (h.not_comm_eq hy hx (Q0.inv_mem hq) ?_).elim
    rw [← commutatorElement_inv, hk]
    simp only [Fin.reduceFinMk, Fin.val_two]
    rw [mul_inv_rev, h.e2_inv]
    exact h.Ecomm h.eE (h.QE (Q0.inv_mem hq))

omit h in
theorem comm_mul_central_left {x z c : G} (hc : z * c = c * z) : ⁅x * c, z⁆ = ⁅x, z⁆ := by
  calc ⁅x * c, z⁆ = x * (c * z) * c⁻¹ * x⁻¹ * z⁻¹ := by simp only [commutatorElement_def]; group
    _ = x * (z * c) * c⁻¹ * x⁻¹ * z⁻¹ := by rw [hc]
    _ = ⁅x, z⁆ := by simp only [commutatorElement_def]; group

omit h in
theorem comm_mul_central_right {x y c : G} (hc : x * c = c * x) : ⁅x, y * c⁆ = ⁅x, y⁆ := by
  have hc' : c * x⁻¹ = x⁻¹ * c := ((show Commute x c from hc).inv_left).eq.symm
  calc ⁅x, y * c⁆ = x * y * (c * x⁻¹) * c⁻¹ * y⁻¹ := by simp only [commutatorElement_def]; group
    _ = x * y * (x⁻¹ * c) * c⁻¹ * y⁻¹ := by rw [hc']
    _ = ⁅x, y⁆ := by simp only [commutatorElement_def]; group

theorem comm_mul_left {x y z : G} (hx : x ∈ T) (hy : y ∈ T) (hz : z ∈ T) :
    ⁅x * y, z⁆ = ⁅x, z⁆ * ⁅y, z⁆ := by
  calc ⁅x * y, z⁆ = x * ⁅y, z⁆ * x⁻¹ * ⁅x, z⁆ := by simp only [commutatorElement_def]; group
    _ = ⁅y, z⁆ * ⁅x, z⁆ := by rw [h.Qcent x hx _ (h.comm_mem_Q hy hz), mul_inv_cancel_right]
    _ = ⁅x, z⁆ * ⁅y, z⁆ := h.Qcomm (h.comm_mem_Q hy hz) (h.comm_mem_Q hx hz)

theorem comm_mul_right {x y z : G} (hx : x ∈ T) (hy : y ∈ T) (hz : z ∈ T) :
    ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅x, z⁆ := by
  calc ⁅x, y * z⁆ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) := by simp only [commutatorElement_def]; group
    _ = ⁅x, y⁆ * ⁅x, z⁆ := by rw [h.Qcent y hy _ (h.comm_mem_Q hx hz), mul_inv_cancel_right]

theorem cube_mul {f y : G} (hf : f ∈ T) (hy : y ∈ T) : (f * y) ^ 3 = f ^ 3 * y ^ 3 := by
  have hcQ : ⁅y, f⁆ ∈ Q0 := h.comm_mem_Q hy hf
  have hyf : y * f = ⁅y, f⁆ * (f * y) := by simp only [commutatorElement_def]; group
  have hcf : ∀ X : G, f * (⁅y, f⁆ * X) = ⁅y, f⁆ * (f * X) := fun X => by
    rw [← mul_assoc, h.Qcent f hf _ hcQ, mul_assoc]
  have hcy : ∀ X : G, y * (⁅y, f⁆ * X) = ⁅y, f⁆ * (y * X) := fun X => by
    rw [← mul_assoc, h.Qcent y hy _ hcQ, mul_assoc]
  have hyf' : ∀ X : G, y * (f * X) = ⁅y, f⁆ * (f * (y * X)) := fun X => by
    rw [← mul_assoc, hyf, mul_assoc, mul_assoc]
  have hc3 : ∀ X : G, ⁅y, f⁆ * (⁅y, f⁆ * (⁅y, f⁆ * X)) = X := fun X => by
    rw [← mul_assoc, ← mul_assoc, ← pow_three', h.Q3 hcQ, one_mul]
  have key : f * (y * (f * (y * (f * y)))) =
      ⁅y, f⁆ * (⁅y, f⁆ * (⁅y, f⁆ * (f * (f * (f * (y * (y * y))))))) := by
    simp only [hyf', hcf, hcy]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [key, hc3]

theorem comm_m_mem {s : G} (hs : s ∈ T) : ⁅m, s⁆ ∈ T :=
  T.mul_mem (h.mT s hs) (T.inv_mem hs)

theorem comm_m_E {s : G} (hs : s ∈ E) : ⁅m, s⁆ ∈ Q0 := by
  obtain ⟨k, q, hq, rfl⟩ := h.E_decomp hs
  have hme : m * e ^ (k : ℕ) * m⁻¹ = e ^ (k : ℕ) := by rw [← conj_pow, h.me]
  have : ⁅m, q * e ^ (k : ℕ)⁆ = (m * q * m⁻¹) * q⁻¹ := by
    calc ⁅m, q * e ^ (k : ℕ)⁆
        = (m * q * m⁻¹) * (m * e ^ (k : ℕ) * m⁻¹) * (e ^ (k : ℕ))⁻¹ * q⁻¹ := by
          simp only [commutatorElement_def]; group
      _ = (m * q * m⁻¹) * q⁻¹ := by rw [hme, mul_inv_cancel_right]
  rw [this]
  exact Q0.mul_mem (h.mQ q hq) (Q0.inv_mem hq)

theorem θ_comm_m {s : G} (hs : s ∈ T) : ⁅⁅m, s⁆, e⁆ = m * ⁅s, e⁆ * m⁻¹ * ⁅s, e⁆⁻¹ := by
  rw [commutatorElement_def m s, h.θ_mul (h.mT s hs) (T.inv_mem hs), h.θ_m, h.θ_inv hs]

theorem F_mul {s s' q q' : G} (hs : s ∈ T) (hq : q ∈ Q0) (hs' : s' ∈ T) (hq' : q' ∈ Q0) :
    ∃ s'' ∈ T, ∃ q'' ∈ Q0, ⁅m, s⁆ * q * (⁅m, s'⁆ * q') = ⁅m, s''⁆ * q'' := by
  have hB := h.comm_m_mem hs'
  have hc : ⁅⁅m, s'⁆, s⁻¹⁆ ∈ Q0 := h.comm_mem_Q hB (T.inv_mem hs)
  have hss' : s * s' ∈ T := T.mul_mem hs hs'
  have hcom : ⁅⁅m, s'⁆, s⁻¹⁆ * (m * s * m⁻¹) = (m * s * m⁻¹) * ⁅⁅m, s'⁆, s⁻¹⁆ :=
    (h.Qcent _ (h.mT s hs) _ hc).symm
  have hAB : ⁅m, s * s'⁆ = ⁅⁅m, s'⁆, s⁻¹⁆ * (⁅m, s⁆ * ⁅m, s'⁆) := by
    calc ⁅m, s * s'⁆ = (m * s * m⁻¹) * ⁅⁅m, s'⁆, s⁻¹⁆ * s⁻¹ * ⁅m, s'⁆ := by
          simp only [commutatorElement_def]; group
      _ = ⁅⁅m, s'⁆, s⁻¹⁆ * (m * s * m⁻¹) * s⁻¹ * ⁅m, s'⁆ := by rw [hcom]
      _ = ⁅⁅m, s'⁆, s⁻¹⁆ * (⁅m, s⁆ * ⁅m, s'⁆) := by simp only [commutatorElement_def]; group
  refine ⟨s * s', hss', ⁅⁅m, s'⁆, s⁻¹⁆⁻¹ * (q * q'),
    Q0.mul_mem (Q0.inv_mem hc) (Q0.mul_mem hq hq'), ?_⟩
  have hAB' : ⁅m, s⁆ * ⁅m, s'⁆ = ⁅⁅m, s'⁆, s⁻¹⁆⁻¹ * ⁅m, s * s'⁆ := by
    rw [hAB, inv_mul_cancel_left]
  calc ⁅m, s⁆ * q * (⁅m, s'⁆ * q') = ⁅m, s⁆ * (q * ⁅m, s'⁆) * q' := by simp only [mul_assoc]
    _ = ⁅m, s⁆ * (⁅m, s'⁆ * q) * q' := by rw [(h.Qcent _ hB q hq).symm]
    _ = (⁅m, s⁆ * ⁅m, s'⁆) * (q * q') := by simp only [mul_assoc]
    _ = ⁅⁅m, s'⁆, s⁻¹⁆⁻¹ * ⁅m, s * s'⁆ * (q * q') := by rw [hAB']
    _ = ⁅m, s * s'⁆ * ⁅⁅m, s'⁆, s⁻¹⁆⁻¹ * (q * q') := by
        rw [(h.Qcent _ (h.comm_m_mem hss') _ (Q0.inv_mem hc)).symm]
    _ = ⁅m, s * s'⁆ * (⁅⁅m, s'⁆, s⁻¹⁆⁻¹ * (q * q')) := mul_assoc _ _ _

theorem F_inv {s q : G} (hs : s ∈ T) (hq : q ∈ Q0) :
    ∃ s'' ∈ T, ∃ q'' ∈ Q0, (⁅m, s⁆ * q)⁻¹ = ⁅m, s''⁆ * q'' := by
  have hX : ⁅m, s⁻¹⁆ ∈ T := h.comm_m_mem (T.inv_mem hs)
  have hd : ⁅s, ⁅m, s⁻¹⁆⁆ ∈ Q0 := h.comm_mem_Q hs hX
  refine ⟨s⁻¹, T.inv_mem hs, q⁻¹ * ⁅s, ⁅m, s⁻¹⁆⁆, Q0.mul_mem (Q0.inv_mem hq) hd, ?_⟩
  calc (⁅m, s⁆ * q)⁻¹ = q⁻¹ * (⁅s, ⁅m, s⁻¹⁆⁆ * ⁅m, s⁻¹⁆) := by
        simp only [commutatorElement_def]; group
    _ = q⁻¹ * ⁅s, ⁅m, s⁻¹⁆⁆ * ⁅m, s⁻¹⁆ := (mul_assoc _ _ _).symm
    _ = ⁅m, s⁻¹⁆ * (q⁻¹ * ⁅s, ⁅m, s⁻¹⁆⁆) :=
        (h.Qcent _ hX _ (Q0.mul_mem (Q0.inv_mem hq) hd)).symm

theorem exists_b {a : G} (ha : a ∈ Q0) : ∃ b ∈ Q0, m * b * m⁻¹ * b⁻¹ = a := by
  let f : Q0 → Q0 := fun b => ⟨m * b * m⁻¹ * b⁻¹, Q0.mul_mem (h.mQ b b.2) (Q0.inv_mem b.2)⟩
  have hf : Function.Injective f := by
    intro b b' hbb'
    have h1 : m * (b : G) * m⁻¹ * (b : G)⁻¹ = m * b' * m⁻¹ * (b' : G)⁻¹ := congrArg Subtype.val hbb'
    have h2 : m * ((b' : G)⁻¹ * b) * m⁻¹ = (b' : G)⁻¹ * b := by
      calc m * ((b' : G)⁻¹ * b) * m⁻¹ = (m * b' * m⁻¹)⁻¹ * (m * b * m⁻¹ * (b : G)⁻¹) * b := by
            group
        _ = (b' : G)⁻¹ * b := by rw [h1]; group
    have h3 := h.mfix _ (Q0.mul_mem (Q0.inv_mem b'.2) b.2) h2
    exact Subtype.ext (inv_mul_eq_one.mp h3).symm
  obtain ⟨b, hb⟩ := Finite.surjective_of_injective hf ⟨a, ha⟩
  exact ⟨b, b.2, congrArg Subtype.val hb⟩

theorem exists_F : ∃ F : Subgroup G, F ≤ T ∧ Q0 ≤ F ∧ (∀ x ∈ F, m * x * m⁻¹ ∈ F) ∧
    (∀ a ∈ Q0, ∃ x ∈ F, ⁅x, e⁆ = a) ∧ (∀ x ∈ F, ⁅x, e⁆ = 1 → x ∈ Q0) := by
  let F : Subgroup G :=
    { carrier := {x | ∃ s ∈ T, ∃ q ∈ Q0, x = ⁅m, s⁆ * q}
      mul_mem' := by
        rintro _ _ ⟨s, hs, q, hq, rfl⟩ ⟨s', hs', q', hq', rfl⟩
        obtain ⟨s'', hs'', q'', hq'', he⟩ := h.F_mul hs hq hs' hq'
        exact ⟨s'', hs'', q'', hq'', he⟩
      one_mem' := ⟨1, T.one_mem, 1, Q0.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨s, hs, q, hq, rfl⟩
        obtain ⟨s'', hs'', q'', hq'', he⟩ := h.F_inv hs hq
        exact ⟨s'', hs'', q'', hq'', he⟩ }
  refine ⟨F, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨s, hs, q, hq, rfl⟩
    exact T.mul_mem (h.comm_m_mem hs) (h.QT hq)
  · intro q hq
    exact ⟨1, T.one_mem, q, hq, by simp⟩
  · rintro _ ⟨s, hs, q, hq, rfl⟩
    exact ⟨m * s * m⁻¹, h.mT s hs, m * q * m⁻¹, h.mQ q hq, by
      simp only [commutatorElement_def]; group⟩
  · intro a ha
    obtain ⟨b, hb, hba⟩ := h.exists_b ha
    obtain ⟨s, hs, rfl⟩ := h.θsurj b hb
    refine ⟨⁅m, s⁆ * 1, ⟨s, hs, 1, Q0.one_mem, rfl⟩, ?_⟩
    rw [mul_one, h.θ_comm_m hs]
    exact hba
  · rintro _ ⟨s, hs, q, hq, rfl⟩ h1
    rw [h.θ_mul (h.comm_m_mem hs) (h.QT hq), h.θ_eq_one (h.QE hq), mul_one, h.θ_comm_m hs] at h1
    have hθs : ⁅s, e⁆ = 1 := h.mfix _ (h.θQ s hs) (mul_inv_eq_one.mp h1)
    exact Q0.mul_mem (h.comm_m_E (h.mem_E hs hθs)) hq

theorem card_F {F : Subgroup G} (hFT : F ≤ T) (hQF : Q0 ≤ F)
    (hsurj : ∀ a ∈ Q0, ∃ x ∈ F, ⁅x, e⁆ = a) (hker : ∀ x ∈ F, ⁅x, e⁆ = 1 → x ∈ Q0) :
    Nat.card F = 3 ^ 6 := by
  let φ : F →* Q0 := MonoidHom.mk' (fun x => ⟨⁅(x : G), e⁆, h.θQ x (hFT x.2)⟩)
    (fun x y => Subtype.ext (h.θ_mul (hFT x.2) (hFT y.2)))
  have hφ : Function.Surjective φ := by
    rintro ⟨a, ha⟩
    obtain ⟨x, hx, hxa⟩ := hsurj a ha
    exact ⟨⟨x, hx⟩, Subtype.ext hxa⟩
  have hkereq : φ.ker = Q0.subgroupOf F := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      exact hker x x.2 (congrArg Subtype.val hx)
    · intro hx
      exact Subtype.ext (h.θ_eq_one (h.QE hx))
  have hkc : Nat.card φ.ker = 3 ^ 3 := by
    rw [hkereq, ← h.Qcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQF).toEquiv
  have := Subgroup.card_ker_mul_card_of_surjective (f := φ) hφ
  rw [hkc, h.Qcard] at this
  rw [← this]
  norm_num

theorem exists_moved : ∃ q ∈ Q0, m * q * m⁻¹ ≠ q := by
  by_contra hcon
  push Not at hcon
  have hbot : Q0 = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr fun q hq => h.mfix q hq (hcon q hq)
  have := h.Qcard
  rw [hbot, Subgroup.card_bot] at this
  norm_num at this

theorem F_comm {F : Subgroup G} (hFT : F ≤ T) (hmF : ∀ x ∈ F, m * x * m⁻¹ ∈ F)
    (hsurj : ∀ a ∈ Q0, ∃ x ∈ F, ⁅x, e⁆ = a) (hker : ∀ x ∈ F, ⁅x, e⁆ = 1 → x ∈ Q0) :
    ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := by
  have hsurj' : ∀ a : G, ∃ x : G, a ∈ Q0 → x ∈ F ∧ ⁅x, e⁆ = a := by
    intro a
    by_cases ha : a ∈ Q0
    · obtain ⟨x, hx, hxa⟩ := hsurj a ha
      exact ⟨x, fun _ => ⟨hx, hxa⟩⟩
    · exact ⟨1, fun h' => absurd h' ha⟩
  choose σ hσ using hsurj'
  have hσF : ∀ a ∈ Q0, σ a ∈ F := fun a ha => (hσ a ha).1
  have hσT : ∀ a ∈ Q0, σ a ∈ T := fun a ha => hFT (hσF a ha)
  have hσθ : ∀ a ∈ Q0, ⁅σ a, e⁆ = a := fun a ha => (hσ a ha).2
  have hsame : ∀ x ∈ F, ∀ y ∈ F, ⁅x, e⁆ = ⁅y, e⁆ → ∃ q ∈ Q0, y = x * q := by
    intro x hx y hy hxy
    refine ⟨x⁻¹ * y, hker _ (F.mul_mem (F.inv_mem hx) hy) ?_, by group⟩
    rw [h.θ_mul (hFT (F.inv_mem hx)) (hFT hy), h.θ_inv (hFT hx), hxy, inv_mul_cancel]
  have hcq : ∀ x ∈ T, ∀ y ∈ T, ∀ q ∈ Q0, ∀ q' ∈ Q0, ⁅x * q, y * q'⁆ = ⁅x, y⁆ := by
    intro x hx y hy q hq q' hq'
    rw [comm_mul_central_left (h.Qcent _ (T.mul_mem hy (h.QT hq')) q hq),
      comm_mul_central_right (h.Qcent x hx q' hq')]
  have hβ := vanishing_V1 h.Qel h.Qcard h.mQ h.m13Q h.exists_moved (fun a b => ⁅σ a, σ b⁆)
    (fun a ha b hb => h.comm_mem_Q (hσT a ha) (hσT b hb))
    (fun a ha a' ha' b hb => by
      obtain ⟨q, hq, hqe⟩ := hsame (σ a * σ a') (F.mul_mem (hσF a ha) (hσF a' ha'))
        (σ (a * a')) (hσF _ (Q0.mul_mem ha ha'))
        (by rw [h.θ_mul (hσT a ha) (hσT a' ha'), hσθ a ha, hσθ a' ha', hσθ _ (Q0.mul_mem ha ha')])
      show ⁅σ (a * a'), σ b⁆ = ⁅σ a, σ b⁆ * ⁅σ a', σ b⁆
      rw [hqe, comm_mul_central_left (h.Qcent _ (hσT b hb) q hq),
        h.comm_mul_left (hσT a ha) (hσT a' ha') (hσT b hb)])
    (fun a ha b hb b' hb' => by
      obtain ⟨q, hq, hqe⟩ := hsame (σ b * σ b') (F.mul_mem (hσF b hb) (hσF b' hb'))
        (σ (b * b')) (hσF _ (Q0.mul_mem hb hb'))
        (by rw [h.θ_mul (hσT b hb) (hσT b' hb'), hσθ b hb, hσθ b' hb', hσθ _ (Q0.mul_mem hb hb')])
      show ⁅σ a, σ (b * b')⁆ = ⁅σ a, σ b⁆ * ⁅σ a, σ b'⁆
      rw [hqe, comm_mul_central_right (h.Qcent _ (hσT a ha) q hq),
        h.comm_mul_right (hσT a ha) (hσT b hb) (hσT b' hb')])
    (fun a _ => commutatorElement_self _)
    (fun a ha b hb => by
      obtain ⟨q, hq, hqe⟩ := hsame (m * σ a * m⁻¹) (hmF _ (hσF a ha)) (σ (m * a * m⁻¹))
        (hσF _ (h.mQ a ha)) (by rw [h.θ_m, hσθ a ha, hσθ _ (h.mQ a ha)])
      obtain ⟨q', hq', hq'e⟩ := hsame (m * σ b * m⁻¹) (hmF _ (hσF b hb)) (σ (m * b * m⁻¹))
        (hσF _ (h.mQ b hb)) (by rw [h.θ_m, hσθ b hb, hσθ _ (h.mQ b hb)])
      show ⁅σ (m * a * m⁻¹), σ (m * b * m⁻¹)⁆ = m * ⁅σ a, σ b⁆ * m⁻¹
      rw [hqe, hq'e, hcq _ (h.mT _ (hσT a ha)) _ (h.mT _ (hσT b hb)) q hq q' hq']
      simp only [commutatorElement_def]
      group)
  intro x hx y hy
  have hxQ := h.θQ x (hFT hx)
  have hyQ := h.θQ y (hFT hy)
  obtain ⟨q, hq, hxq⟩ := hsame _ (hσF _ hxQ) x hx (hσθ _ hxQ)
  obtain ⟨q', hq', hyq'⟩ := hsame _ (hσF _ hyQ) y hy (hσθ _ hyQ)
  have h1 : ⁅σ ⁅x, e⁆ * q, σ ⁅y, e⁆ * q'⁆ = 1 := by
    rw [hcq _ (hσT _ hxQ) _ (hσT _ hyQ) q hq q' hq']
    exact hβ _ hxQ _ hyQ
  rw [← hxq, ← hyq'] at h1
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

theorem F_unique {F F' : Subgroup G} (hFT : F ≤ T) (hFcard : Nat.card F = 3 ^ 6)
    (hFab : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x) (hker : ∀ x ∈ F, ⁅x, e⁆ = 1 → x ∈ Q0)
    (hF'T : F' ≤ T) (hF'card : Nat.card F' = 3 ^ 6)
    (hF'ab : ∀ x ∈ F', ∀ y ∈ F', x * y = y * x) : F' ≤ F := by
  by_contra hne
  have hle : F ⊔ F' ≤ T := sup_le hFT hF'T
  have hsup : F ⊔ F' = T := by
    have h1 : Nat.card ↥(F ⊔ F') ∣ 3 ^ 7 := h.Tcard ▸ Subgroup.card_dvd_of_le hle
    have h2 : 3 ^ 6 ∣ Nat.card ↥(F ⊔ F') := hFcard ▸ Subgroup.card_dvd_of_le le_sup_left
    have h3 : Nat.card ↥(F ⊔ F') ≠ 3 ^ 6 := by
      intro h3
      apply hne
      have : F = F ⊔ F' := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h3, hFcard])
      rw [this]
      exact le_sup_right
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h1
    rw [hk'] at h2 h3
    have hk6 : 6 ≤ k := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h2
    have hk7 : k = 7 := by
      rcases Nat.lt_or_ge 6 k with hk6' | hk6'
      · omega
      · exact absurd (by rw [show k = 6 by omega]) h3
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [h.Tcard, hk', hk7])
  have hcent : ∀ x ∈ F ⊓ F', ∀ t ∈ T, t * x = x * t := by
    intro x hx t ht
    have hle' : F ⊔ F' ≤ Subgroup.centralizer {x} := by
      apply sup_le
      · intro y hy
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hFab y hy x hx.1
      · intro y hy
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hF'ab y hy x hx.2
    have := hle' (hsup ▸ ht)
    rwa [Subgroup.mem_centralizer_singleton_iff] at this
  have hinfQ : F ⊓ F' ≤ Q0 := by
    intro x hx
    exact hker x hx.1 (commutatorElement_eq_one_iff_mul_comm.mpr (hcent x hx e h.eT).symm)
  have hrF : F.relIndex T = 3 := by
    have := Subgroup.relIndex_mul_card (H := F) (K := T)
    rw [inf_eq_left.mpr hFT, hFcard, h.Tcard] at this
    omega
  have hrF' : F'.relIndex T = 3 := by
    have := Subgroup.relIndex_mul_card (H := F') (K := T)
    rw [inf_eq_left.mpr hF'T, hF'card, h.Tcard] at this
    omega
  have hrI := Subgroup.relIndex_inf_le (H := F) (K := F') (L := T)
  have hcI := Subgroup.relIndex_mul_card (H := F ⊓ F') (K := T)
  rw [inf_eq_left.mpr (inf_le_left.trans hFT), h.Tcard] at hcI
  have hcQ : Nat.card ↥(F ⊓ F') ≤ 3 ^ 3 := h.Qcard ▸ Subgroup.card_le_of_le hinfQ
  rw [hrF, hrF'] at hrI
  have := Nat.mul_le_mul hrI hcQ
  rw [hcI] at this
  norm_num at this

theorem F_normal {F : Subgroup G} (hFT : F ≤ T) (hFcard : Nat.card F = 3 ^ 6)
    (hFab : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x) (hker : ∀ x ∈ F, ⁅x, e⁆ = 1 → x ∈ Q0)
    (g : G) (hg : ∀ r ∈ T, g * r * g⁻¹ ∈ T) : ∀ f ∈ F, g * f * g⁻¹ ∈ F := by
  have hle := h.F_unique hFT hFcard hFab hker (F' := F.map (MulAut.conj g).toMonoidHom) ?_ ?_ ?_
  · intro f hf
    exact hle ⟨f, hf, rfl⟩
  · rintro _ ⟨f, hf, rfl⟩
    exact hg f (hFT hf)
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hFcard]
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
      _ = g * (y * x) * g⁻¹ := by rw [hFab x hx y hy]
      _ = g * y * g⁻¹ * (g * x * g⁻¹) := by group

theorem inv_sub {S : Subgroup G} (hSQ : S ≤ Q0) (hmS : ∀ x ∈ S, m * x * m⁻¹ ∈ S) :
    S = ⊥ ∨ S = Q0 := by
  classical
  obtain ⟨a, ha⟩ := h.m13
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  haveI : Fintype S := Fintype.ofFinite S
  let f : Function.End S := fun x => ⟨m * x * m⁻¹, hmS x x.2⟩
  have hfpow : ∀ (n : ℕ) (x : S), (((f ^ n) x : S) : G) = m ^ n * x * (m ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro x; simp; rfl
    | succ n ih =>
      intro x
      show ((f^[n + 1] x : S) : G) = _
      rw [Function.iterate_succ_apply']
      show m * ((f^[n] x : S) : G) * m⁻¹ = _
      rw [show ((f^[n] x : S) : G) = m ^ n * x * (m ^ n)⁻¹ from ih x]
      group
  have hf : f ^ 13 ^ a = 1 := by
    funext x
    apply Subtype.ext
    rw [hfpow, ha, one_mul, inv_one, mul_one]
    rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 13) (n := a) hf
  have hfix : Fintype.card (Function.fixedPoints f) = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨1, Subtype.ext (by simp [f])⟩, ?_⟩
    rintro ⟨x, hx⟩
    apply Subtype.ext
    apply Subtype.ext
    have hx' : m * (x : G) * m⁻¹ = x := congrArg Subtype.val hx
    exact h.mfix _ (hSQ x.2) hx'
  rw [hfix, ← Nat.card_eq_fintype_card] at hmod
  have hdvd : Nat.card S ∣ 3 ^ 3 := h.Qcard ▸ Subgroup.card_dvd_of_le hSQ
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  rw [hk'] at hmod
  interval_cases k
  · left
    exact Subgroup.card_eq_one.mp (by rw [hk']; rfl)
  · exact absurd hmod (by decide)
  · exact absurd hmod (by decide)
  · right
    exact Subgroup.eq_of_le_of_card_ge hSQ (by rw [h.Qcard, hk'])

theorem θ_pow {r : G} (hr : r ∈ T) (n : ℕ) : ⁅r ^ n, e⁆ = ⁅r, e⁆ ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, h.θ_mul (T.pow_mem hr n) hr, ih, pow_succ]

theorem cube_mem_Q {F : Subgroup G} (hFT : F ≤ T) (hker : ∀ x ∈ F, ⁅x, e⁆ = 1 → x ∈ Q0)
    {f : G} (hf : f ∈ F) : f ^ 3 ∈ Q0 :=
  hker _ (F.pow_mem hf 3) (by rw [h.θ_pow (hFT hf), h.Q3 (h.θQ f (hFT hf))])

theorem dichotomy {F : Subgroup G} (hFT : F ≤ T) (hmF : ∀ x ∈ F, m * x * m⁻¹ ∈ F)
    (hker : ∀ x ∈ F, ⁅x, e⁆ = 1 → x ∈ Q0) (hFab : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x) :
    (∀ f ∈ F, f ^ 3 = 1 → f ∈ Q0) ∨ (∀ x ∈ F, x ^ 3 = 1) := by
  let S : Subgroup G :=
    { carrier := {a | ∃ x ∈ F, x ^ 3 = 1 ∧ ⁅x, e⁆ = a}
      mul_mem' := by
        rintro _ _ ⟨x, hx, hx3, rfl⟩ ⟨y, hy, hy3, rfl⟩
        refine ⟨x * y, F.mul_mem hx hy, ?_, h.θ_mul (hFT hx) (hFT hy)⟩
        rw [(show Commute x y from hFab x hx y hy).mul_pow, hx3, hy3, one_mul]
      one_mem' := ⟨1, F.one_mem, one_pow _, commutatorElement_one_left e⟩
      inv_mem' := by
        rintro _ ⟨x, hx, hx3, rfl⟩
        exact ⟨x⁻¹, F.inv_mem hx, by rw [inv_pow, hx3, inv_one], h.θ_inv (hFT hx)⟩ }
  have hSQ : S ≤ Q0 := by
    rintro _ ⟨x, hx, -, rfl⟩
    exact h.θQ x (hFT hx)
  have hmS : ∀ a ∈ S, m * a * m⁻¹ ∈ S := by
    rintro _ ⟨x, hx, hx3, rfl⟩
    exact ⟨m * x * m⁻¹, hmF x hx, by rw [conj_pow, hx3, mul_one, mul_inv_cancel], h.θ_m x⟩
  rcases h.inv_sub hSQ hmS with hS | hS
  · left
    intro f hf hf3
    have hfS : ⁅f, e⁆ ∈ S := ⟨f, hf, hf3, rfl⟩
    rw [hS, Subgroup.mem_bot] at hfS
    exact hker f hf hfS
  · right
    intro x hx
    have hxS : ⁅x, e⁆ ∈ S := hS ▸ h.θQ x (hFT hx)
    obtain ⟨y, hy, hy3, hyx⟩ := hxS
    have hq : y⁻¹ * x ∈ Q0 := hker _ (F.mul_mem (F.inv_mem hy) hx) (by
      rw [h.θ_mul (hFT (F.inv_mem hy)) (hFT hx), h.θ_inv (hFT hy), hyx, inv_mul_cancel])
    have hx' : x = y * (y⁻¹ * x) := by group
    rw [hx', (show Commute y (y⁻¹ * x) from hFab y hy _ (F.mul_mem (F.inv_mem hy) hx)).mul_pow,
      hy3, h.Q3 hq, one_mul]

theorem cube_onto {F : Subgroup G} (hFT : F ≤ T) (hQF : Q0 ≤ F) (hFcard : Nat.card F = 3 ^ 6)
    (hFab : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x) (hker : ∀ x ∈ F, ⁅x, e⁆ = 1 → x ∈ Q0)
    (hΩ : ∀ f ∈ F, f ^ 3 = 1 → f ∈ Q0) : ∀ q ∈ Q0, ∃ f ∈ F, f ^ 3 = q := by
  let κ : F →* Q0 := MonoidHom.mk' (fun x => ⟨(x : G) ^ 3, h.cube_mem_Q hFT hker x.2⟩)
    (fun x y => Subtype.ext (by
      simp only [Subgroup.coe_mul]
      exact (show Commute (x : G) y from hFab x x.2 y y.2).mul_pow 3))
  have hkereq : κ.ker = Q0.subgroupOf F := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      exact hΩ x x.2 (congrArg Subtype.val hx)
    · intro hx
      exact Subtype.ext (h.Q3 hx)
  have hkc : Nat.card κ.ker = 3 ^ 3 := by
    rw [hkereq, ← h.Qcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQF).toEquiv
  have hcr := Subgroup.card_ker_mul_card_range κ
  rw [hkc, hFcard, show (3 : ℕ) ^ 6 = 3 ^ 3 * 3 ^ 3 by norm_num] at hcr
  have hrange : Nat.card κ.range = Nat.card Q0 := by
    rw [h.Qcard]
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) hcr
  have htop : κ.range = ⊤ := Subgroup.eq_top_of_card_eq _ hrange
  intro q hq
  obtain ⟨x, hx⟩ := MonoidHom.range_eq_top.mp htop ⟨q, hq⟩
  exact ⟨x, x.2, congrArg Subtype.val hx⟩

theorem T_eq_FE {F : Subgroup G} (hFT : F ≤ T) (hsurj : ∀ a ∈ Q0, ∃ x ∈ F, ⁅x, e⁆ = a) :
    ∀ t ∈ T, ∃ f ∈ F, ∃ y ∈ E, t = f * y := by
  intro t ht
  obtain ⟨f, hf, hft⟩ := hsurj _ (h.θQ t ht)
  refine ⟨f, hf, f⁻¹ * t, h.mem_E (T.mul_mem (T.inv_mem (hFT hf)) ht) ?_, by group⟩
  rw [h.θ_mul (T.inv_mem (hFT hf)) ht, h.θ_inv (hFT hf), hft, inv_mul_cancel]

theorem omega_le_E {F : Subgroup G} (hFT : F ≤ T) (hsurj : ∀ a ∈ Q0, ∃ x ∈ F, ⁅x, e⁆ = a)
    (hΩ : ∀ f ∈ F, f ^ 3 = 1 → f ∈ Q0) : ∀ r ∈ T, r ^ 3 = 1 → r ∈ E := by
  intro r hr hr3
  obtain ⟨f, hf, y, hy, rfl⟩ := h.T_eq_FE hFT hsurj r hr
  rw [h.cube_mul (hFT hf) (h.ET hy), h.Eel.2 y hy, mul_one] at hr3
  exact E.mul_mem (h.QE (hΩ f hf hr3)) hy

theorem structure_core :
    (∃ F : Subgroup G, F ≤ T ∧ Nat.card ↥F = 3 ^ 6 ∧ (∀ a ∈ F, ∀ b ∈ F, a * b = b * a) ∧
      (∀ f ∈ F, f ^ 3 ∈ Q0) ∧ (∀ f ∈ F, f ^ 3 = 1 → f ∈ Q0) ∧ (∀ q ∈ Q0, ∃ f ∈ F, f ^ 3 = q) ∧
      (∀ t ∈ T, ∃ f ∈ F, ∃ y ∈ E, t = f * y) ∧
      (∀ g : G, (∀ r ∈ T, g * r * g⁻¹ ∈ T) → ∀ f ∈ F, g * f * g⁻¹ ∈ F) ∧
      (∀ r ∈ T, r ^ 3 = 1 → r ∈ E)) ∨
    (∃ F : Subgroup G, F ≤ T ∧ Nat.card ↥F = 3 ^ 6 ∧ IsElemAbelian 3 F ∧
      ∀ g : G, (∀ r ∈ T, g * r * g⁻¹ ∈ T) → ∀ f ∈ F, g * f * g⁻¹ ∈ F) := by
  obtain ⟨F, hFT, hQF, hmF, hsurj, hker⟩ := h.exists_F
  have hFab := h.F_comm hFT hmF hsurj hker
  have hFcard := h.card_F hFT hQF hsurj hker
  have hnorm := h.F_normal hFT hFcard hFab hker
  rcases h.dichotomy hFT hmF hker hFab with hΩ | h3
  · exact Or.inl ⟨F, hFT, hFcard, hFab, fun f hf => h.cube_mem_Q hFT hker hf, hΩ,
      h.cube_onto hFT hQF hFcard hFab hker hΩ, h.T_eq_FE hFT hsurj, hnorm,
      h.omega_le_E hFT hsurj hΩ⟩
  · exact Or.inr ⟨F, hFT, hFcard, ⟨IsMulCommutative.of_setLike_mul_comm hFab, h3⟩, hnorm⟩

end Hyp

theorem T_structure {G : Type} [Group G] [Finite G] {T E Q0 : Subgroup G} {e m : G}
    (hT3 : IsPGroup 3 ↥T) (hTcard : Nat.card ↥T = 3 ^ 7)
    (hEel : IsElemAbelian 3 E) (hEcard : Nat.card ↥E = 3 ^ 4) (hET : E ≤ T)
    (hQel : IsElemAbelian 3 Q0) (hQcard : Nat.card ↥Q0 = 3 ^ 3) (hQE : Q0 ≤ E)
    (heE : e ∈ E) (heQ : e ∉ Q0)
    (hQcent : ∀ r ∈ T, ∀ q ∈ Q0, r * q = q * r)
    (hθQ : ∀ r ∈ T, r * e * r⁻¹ * e⁻¹ ∈ Q0)
    (hθker : ∀ r ∈ T, r * e = e * r → r ∈ E)
    (hθsurj : ∀ q ∈ Q0, ∃ r ∈ T, r * e * r⁻¹ * e⁻¹ = q)
    (hmT : ∀ r ∈ T, m * r * m⁻¹ ∈ T) (hmT' : ∀ r ∈ T, m⁻¹ * r * m ∈ T)
    (hmE : ∀ r ∈ E, m * r * m⁻¹ ∈ E)
    (hmQ : ∀ r ∈ Q0, m * r * m⁻¹ ∈ Q0) (hme : m * e * m⁻¹ = e)
    (hm13 : ∃ a : ℕ, m ^ 13 ^ a = 1)
    (hm13Q : ∀ q ∈ Q0, m ^ 13 * q * (m ^ 13)⁻¹ = q)
    (hmfree : ∀ j : ℕ, 0 < j → j < 13 → ∀ q ∈ Q0, m ^ j * q * (m ^ j)⁻¹ = q → q = 1) :
    (∃ F : Subgroup G, F ≤ T ∧ Nat.card ↥F = 3 ^ 6 ∧ (∀ a ∈ F, ∀ b ∈ F, a * b = b * a) ∧
      (∀ f ∈ F, f ^ 3 ∈ Q0) ∧ (∀ f ∈ F, f ^ 3 = 1 → f ∈ Q0) ∧ (∀ q ∈ Q0, ∃ f ∈ F, f ^ 3 = q) ∧
      (∀ t ∈ T, ∃ f ∈ F, ∃ y ∈ E, t = f * y) ∧
      (∀ g : G, (∀ r ∈ T, g * r * g⁻¹ ∈ T) → ∀ f ∈ F, g * f * g⁻¹ ∈ F) ∧
      (∀ r ∈ T, r ^ 3 = 1 → r ∈ E)) ∨
    (∃ F : Subgroup G, F ≤ T ∧ Nat.card ↥F = 3 ^ 6 ∧ IsElemAbelian 3 F ∧
      ∀ g : G, (∀ r ∈ T, g * r * g⁻¹ ∈ T) → ∀ f ∈ F, g * f * g⁻¹ ∈ F) :=
  Hyp.structure_core
    { Tcard := hTcard, Eel := hEel, Ecard := hEcard, ET := hET, Qel := hQel, Qcard := hQcard,
      QE := hQE, eE := heE, eQ := heQ, Qcent := hQcent, θQ := hθQ, θker := hθker,
      θsurj := hθsurj, mT := hmT, mQ := hmQ, me := hme, m13 := hm13, m13Q := hm13Q,
      mfix := fun q hq hmq => hmfree 1 one_pos (by norm_num) q hq (by rwa [pow_one]) }

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma113Claims.T
