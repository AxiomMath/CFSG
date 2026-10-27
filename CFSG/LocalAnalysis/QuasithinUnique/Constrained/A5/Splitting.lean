module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5Fin
public import CFSG.GroupTheory.AbelianNormalCoprimeComplementLifting

public section

namespace CFSG.QuasithinUnique.A5.Split

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv

@[expose] def sa : Perm (Fin 5) := swap 0 1

@[expose] def sb : Perm (Fin 5) := swap 2 3

@[expose] def sc : Perm (Fin 5) := swap 0 2 * swap 1 3

@[expose] def s0 : Perm (Fin 5) := sa * sc

@[expose] def nrm (x : Fin 5 → ZMod 2) : Fin 5 → ZMod 2 :=
  x + pact s0 x + pact (s0 * s0) x + pact (s0 * s0 * s0) x

theorem perm_facts : sc * sa * sc⁻¹ = sb ∧ sc * sb * sc⁻¹ = sa ∧ sc * sc = 1 := by
  decide +kernel

theorem s0_pow4 : s0 ^ 4 = 1 := by decide +kernel

theorem sa_pow2 : sa ^ 2 = 1 := by decide +kernel

theorem sa_mem : sa ∈ Dset := by decide +kernel

theorem sc_mem : sc ∈ Dset := by decide +kernel

theorem s0_form : ∀ τ ∈ Dset, ∃ k : Fin 4, ∃ ε : Fin 2, τ = s0 ^ (k : ℕ) * sa ^ (ε : ℕ) := by
  decide +kernel

theorem s0_free : ∀ k : Fin 4, ∀ ε : Fin 2, s0 ^ (k : ℕ) * sa ^ (ε : ℕ) = 1 →
    (k : ℕ) = 0 ∧ (ε : ℕ) = 0 := by
  decide +kernel

theorem dset_index : Dstd.index = 15 := by
  have h := Subgroup.card_mul_index Dstd
  rw [Dstd_card, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at h
  have h120 : Nat.factorial 5 = 120 := by decide
  rw [h120] at h
  omega

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem solve_u : ∀ v₁ v₂ q : Fin 5 → ZMod 2, isEven v₁ → isEven v₂ → isEven q →
    v₁ + pact sb v₁ = 0 → v₂ + pact sa v₂ = 0 → pact sc q = q →
    v₁ + pact sb v₂ = v₂ + pact sa v₁ → q + pact sa q = pact sc v₁ + v₂ →
    q + pact sb q = pact sc v₂ + v₁ →
    ∃ u₀ u : Fin 5 → ZMod 2, isEven u₀ ∧ isEven u ∧ u₀ + pact sa u₀ = 0 ∧
      u + pact sc u + q = 0 ∧
      nrm (u₀ + pact sa u) + ((pact sa v₁ + pact (sa * sb) q) +
        pact (sa * sb) (pact sa v₁ + pact (sa * sb) q)) = 0 := by
  decide +kernel

theorem Delta_add_self (w : evenWeight 5) : w + w = 0 := by
  apply Subtype.ext
  funext i
  show w.1 i + w.1 i = 0
  generalize w.1 i = x
  revert x
  decide

@[expose] def nrmD (t : evenWeight 5) : evenWeight 5 :=
  t + vact s0 t + vact (s0 * s0) t + vact (s0 * s0 * s0) t

theorem nrmD_eq (t : evenWeight 5) :
    (t + vact s0 t) + vact (s0 * s0) (t + vact s0 t) = nrmD t := by
  unfold nrmD
  rw [vact_add, ← vact_mul]
  abel

section

variable {X : Type*} [Group X]

theorem pow_four' (x : X) : x ^ 4 = (x * x) * (x * x) := by
  rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]

structure DeltaExt (ι : Multiplicative (evenWeight 5) →* X) (π : X →* Perm (Fin 5)) : Prop where
  inj : Function.Injective ι
  ι_ker : ∀ w : evenWeight 5, π (ι (Multiplicative.ofAdd w)) = 1
  ker : ∀ x : X, π x = 1 → ∃ w : evenWeight 5, ι (Multiplicative.ofAdd w) = x
  conj : ∀ (x : X) (w : evenWeight 5),
    x * ι (Multiplicative.ofAdd w) * x⁻¹ = ι (Multiplicative.ofAdd (vact (π x) w))
  surj : Function.Surjective π

@[expose] def iA (ι : Multiplicative (evenWeight 5) →* X) (w : evenWeight 5) : X :=
  ι (Multiplicative.ofAdd w)

theorem iA_add (ι : Multiplicative (evenWeight 5) →* X) (w w' : evenWeight 5) :
    iA ι (w + w') = iA ι w * iA ι w' := by
  simp [iA]

theorem iA_zero (ι : Multiplicative (evenWeight 5) →* X) : iA ι 0 = 1 := by
  simp [iA]

theorem iA_self (ι : Multiplicative (evenWeight 5) →* X) (w : evenWeight 5) :
    iA ι w * iA ι w = 1 := by
  rw [← iA_add, Delta_add_self, iA_zero]

theorem iA_inv (ι : Multiplicative (evenWeight 5) →* X) (w : evenWeight 5) :
    (iA ι w)⁻¹ = iA ι w :=
  inv_eq_of_mul_eq_one_right (iA_self ι w)

namespace DeltaExt

variable {ι : Multiplicative (evenWeight 5) →* X} {π : X →* Perm (Fin 5)}

theorem iA_inj (E : DeltaExt ι π) {w w' : evenWeight 5} (h : iA ι w = iA ι w') : w = w' :=
  Multiplicative.ofAdd.injective (E.inj h)

theorem conj_iA (E : DeltaExt ι π) (x : X) (w : evenWeight 5) :
    x * iA ι w * x⁻¹ = iA ι (vact (π x) w) := E.conj x w

theorem pi_iA (E : DeltaExt ι π) (w : evenWeight 5) : π (iA ι w) = 1 := E.ι_ker w

theorem sq_form (E : DeltaExt ι π) (t : evenWeight 5) (g : X) :
    (iA ι t * g) * (iA ι t * g) = iA ι (t + vact (π g) t) * (g * g) := by
  have h := E.conj_iA g t
  calc (iA ι t * g) * (iA ι t * g) = iA ι t * (g * iA ι t * g⁻¹) * (g * g) := by group
    _ = iA ι t * iA ι (vact (π g) t) * (g * g) := by rw [h]
    _ = iA ι (t + vact (π g) t) * (g * g) := by rw [iA_add]

theorem relations (E : DeltaExt ι π) {a b c₀ : X} {v₁ v₂ vq : evenWeight 5}
    (ha : π a = sa) (hb : π b = sb) (hc : π c₀ = sc)
    (ha2 : a * a = 1) (hb2 : b * b = 1) (hab : a * b = b * a)
    (hw₁ : c₀ * a * c₀⁻¹ = iA ι v₁ * b) (hw₂ : c₀ * b * c₀⁻¹ = iA ι v₂ * a)
    (hq : c₀ * c₀ = iA ι vq) :
    v₁ + vact sb v₁ = 0 ∧ v₂ + vact sa v₂ = 0 ∧ vact sc vq = vq ∧
      v₁ + vact sb v₂ = v₂ + vact sa v₁ ∧ vq + vact sa vq = vact sc v₁ + v₂ ∧
      vq + vact sb vq = vact sc v₂ + v₁ := by
  have hz : ∀ w : evenWeight 5, iA ι w = 1 → w = 0 := fun w h =>
    E.iA_inj (h.trans (iA_zero ι).symm)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply hz
    have h1 : (iA ι v₁ * b) * (iA ι v₁ * b) = 1 := by
      rw [← hw₁]
      calc c₀ * a * c₀⁻¹ * (c₀ * a * c₀⁻¹) = c₀ * (a * a) * c₀⁻¹ := by group
        _ = 1 := by rw [ha2]; group
    have h2 := E.sq_form v₁ b
    rw [hb] at h2
    have h3 := h2.symm.trans h1
    rwa [hb2, mul_one] at h3
  · apply hz
    have h1 : (iA ι v₂ * a) * (iA ι v₂ * a) = 1 := by
      rw [← hw₂]
      calc c₀ * b * c₀⁻¹ * (c₀ * b * c₀⁻¹) = c₀ * (b * b) * c₀⁻¹ := by group
        _ = 1 := by rw [hb2]; group
    have h2 := E.sq_form v₂ a
    rw [ha] at h2
    have h3 := h2.symm.trans h1
    rwa [ha2, mul_one] at h3
  · have h := E.conj_iA c₀ vq
    rw [hc] at h
    have h3 : c₀ * iA ι vq * c₀⁻¹ = iA ι vq := by
      rw [← hq]
      group
    exact E.iA_inj (h.symm.trans h3)
  · have hcomm : (iA ι v₁ * b) * (iA ι v₂ * a) = (iA ι v₂ * a) * (iA ι v₁ * b) := by
      rw [← hw₁, ← hw₂]
      calc c₀ * a * c₀⁻¹ * (c₀ * b * c₀⁻¹) = c₀ * (a * b) * c₀⁻¹ := by group
        _ = c₀ * (b * a) * c₀⁻¹ := by rw [hab]
        _ = c₀ * b * c₀⁻¹ * (c₀ * a * c₀⁻¹) := by group
    have hb' := E.conj_iA b v₂
    have ha' := E.conj_iA a v₁
    rw [hb] at hb'
    rw [ha] at ha'
    have e1 : (iA ι v₁ * b) * (iA ι v₂ * a) = iA ι (v₁ + vact sb v₂) * (b * a) := by
      calc (iA ι v₁ * b) * (iA ι v₂ * a) = iA ι v₁ * (b * iA ι v₂ * b⁻¹) * (b * a) := by group
        _ = iA ι v₁ * iA ι (vact sb v₂) * (b * a) := by rw [hb']
        _ = iA ι (v₁ + vact sb v₂) * (b * a) := by rw [iA_add]
    have e2 : (iA ι v₂ * a) * (iA ι v₁ * b) = iA ι (v₂ + vact sa v₁) * (a * b) := by
      calc (iA ι v₂ * a) * (iA ι v₁ * b) = iA ι v₂ * (a * iA ι v₁ * a⁻¹) * (a * b) := by group
        _ = iA ι v₂ * iA ι (vact sa v₁) * (a * b) := by rw [ha']
        _ = iA ι (v₂ + vact sa v₁) * (a * b) := by rw [iA_add]
    rw [e1, e2, ← hab] at hcomm
    exact E.iA_inj (mul_right_cancel hcomm)
  · have hL : (c₀ * c₀) * a * (c₀ * c₀)⁻¹ = iA ι (vq + vact sa vq) * a := by
      have hca := E.conj_iA a vq
      rw [ha] at hca
      calc (c₀ * c₀) * a * (c₀ * c₀)⁻¹ = iA ι vq * a * (iA ι vq)⁻¹ := by rw [hq]
        _ = iA ι vq * (a * iA ι vq * a⁻¹) * a := by rw [iA_inv]; group
        _ = iA ι vq * iA ι (vact sa vq) * a := by rw [hca]
        _ = iA ι (vq + vact sa vq) * a := by rw [iA_add]
    have hR : (c₀ * c₀) * a * (c₀ * c₀)⁻¹ = iA ι (vact sc v₁ + v₂) * a := by
      have hcv := E.conj_iA c₀ v₁
      rw [hc] at hcv
      calc (c₀ * c₀) * a * (c₀ * c₀)⁻¹ = c₀ * (c₀ * a * c₀⁻¹) * c₀⁻¹ := by group
        _ = c₀ * (iA ι v₁ * b) * c₀⁻¹ := by rw [hw₁]
        _ = (c₀ * iA ι v₁ * c₀⁻¹) * (c₀ * b * c₀⁻¹) := by group
        _ = iA ι (vact sc v₁) * (iA ι v₂ * a) := by rw [hcv, hw₂]
        _ = iA ι (vact sc v₁ + v₂) * a := by rw [← mul_assoc, ← iA_add]
    exact E.iA_inj (mul_right_cancel (hL.symm.trans hR))
  · have hL : (c₀ * c₀) * b * (c₀ * c₀)⁻¹ = iA ι (vq + vact sb vq) * b := by
      have hcb := E.conj_iA b vq
      rw [hb] at hcb
      calc (c₀ * c₀) * b * (c₀ * c₀)⁻¹ = iA ι vq * b * (iA ι vq)⁻¹ := by rw [hq]
        _ = iA ι vq * (b * iA ι vq * b⁻¹) * b := by rw [iA_inv]; group
        _ = iA ι vq * iA ι (vact sb vq) * b := by rw [hcb]
        _ = iA ι (vq + vact sb vq) * b := by rw [iA_add]
    have hR : (c₀ * c₀) * b * (c₀ * c₀)⁻¹ = iA ι (vact sc v₂ + v₁) * b := by
      have hcv := E.conj_iA c₀ v₂
      rw [hc] at hcv
      calc (c₀ * c₀) * b * (c₀ * c₀)⁻¹ = c₀ * (c₀ * b * c₀⁻¹) * c₀⁻¹ := by group
        _ = c₀ * (iA ι v₂ * a) * c₀⁻¹ := by rw [hw₂]
        _ = (c₀ * iA ι v₂ * c₀⁻¹) * (c₀ * a * c₀⁻¹) := by group
        _ = iA ι (vact sc v₂) * (iA ι v₁ * b) := by rw [hcv, hw₁]
        _ = iA ι (vact sc v₂ + v₁) * b := by rw [← mul_assoc, ← iA_add]
    exact E.iA_inj (mul_right_cancel (hL.symm.trans hR))

theorem exists_dihedral_lifts (E : DeltaExt ι π) {a b c₀ : X} (ha : π a = sa) (hb : π b = sb)
    (hc : π c₀ = sc) (ha2 : a * a = 1) (hb2 : b * b = 1) (hab : a * b = b * a) :
    ∃ a' c' : X, π a' = sa ∧ π c' = sc ∧ a' * a' = 1 ∧ c' * c' = 1 ∧ (a' * c') ^ 4 = 1 := by
  obtain ⟨hf1, hf2, hf3⟩ := perm_facts
  obtain ⟨v₁, hv₁⟩ := E.ker (c₀ * a * c₀⁻¹ * b⁻¹) (by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc, ha, hb, hf1, mul_inv_cancel])
  obtain ⟨v₂, hv₂⟩ := E.ker (c₀ * b * c₀⁻¹ * a⁻¹) (by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc, ha, hb, hf2, mul_inv_cancel])
  obtain ⟨vq, hvq⟩ := E.ker (c₀ * c₀) (by rw [map_mul, hc, hf3])
  have hw₁ : c₀ * a * c₀⁻¹ = iA ι v₁ * b := by
    unfold iA
    rw [hv₁]
    group
  have hw₂ : c₀ * b * c₀⁻¹ = iA ι v₂ * a := by
    unfold iA
    rw [hv₂]
    group
  have hq : c₀ * c₀ = iA ι vq := hvq.symm
  obtain ⟨R2, R3, R4, R5, R6, R6'⟩ := E.relations ha hb hc ha2 hb2 hab hw₁ hw₂ hq
  have hev : ∀ w : evenWeight 5, isEven w.1 := fun w => w.2
  obtain ⟨u₀, u, hu₀e, hue, hu₀, hu, hnorm⟩ := solve_u v₁.1 v₂.1 vq.1 (hev v₁) (hev v₂) (hev vq)
    (congrArg Subtype.val R2) (congrArg Subtype.val R3) (congrArg Subtype.val R4)
    (congrArg Subtype.val R5) (congrArg Subtype.val R6) (congrArg Subtype.val R6')
  set u₀w : evenWeight 5 := ⟨u₀, hu₀e⟩ with hu₀w
  set uw : evenWeight 5 := ⟨u, hue⟩ with huw
  set m : evenWeight 5 := vact sa v₁ + vact (sa * sb) vq with hm
  have h1 : u₀w + vact sa u₀w = 0 := Subtype.ext hu₀
  have h2 : uw + vact sc uw + vq = 0 := Subtype.ext hu
  have h3 : nrmD (u₀w + vact sa uw) + (m + vact (sa * sb) m) = 0 := Subtype.ext hnorm
  have hπg : π (a * c₀) = s0 := by rw [map_mul, ha, hc]; rfl
  have hπab : π (a * b) = sa * sb := by rw [map_mul, ha, hb]
  refine ⟨iA ι u₀w * a, iA ι uw * c₀, ?_, ?_, ?_, ?_, ?_⟩
  · rw [map_mul, E.pi_iA, ha, one_mul]
  · rw [map_mul, E.pi_iA, hc, one_mul]
  · have h := E.sq_form u₀w a
    rw [ha, h1, iA_zero, ha2, one_mul] at h
    exact h
  · have h := E.sq_form uw c₀
    rw [hc, hq, ← iA_add, h2, iA_zero] at h
    exact h
  ·
    have hac : (iA ι u₀w * a) * (iA ι uw * c₀) = iA ι (u₀w + vact sa uw) * (a * c₀) := by
      have hca := E.conj_iA a uw
      rw [ha] at hca
      calc (iA ι u₀w * a) * (iA ι uw * c₀)
          = iA ι u₀w * (a * iA ι uw * a⁻¹) * (a * c₀) := by group
        _ = iA ι u₀w * iA ι (vact sa uw) * (a * c₀) := by rw [hca]
        _ = iA ι (u₀w + vact sa uw) * (a * c₀) := by rw [iA_add]
    have hg2 : (a * c₀) * (a * c₀) = iA ι m * (a * b) := by
      have hca1 := E.conj_iA a v₁
      rw [ha] at hca1
      have hcab := E.conj_iA (a * b) vq
      rw [hπab] at hcab
      calc (a * c₀) * (a * c₀) = a * (c₀ * a * c₀⁻¹) * (c₀ * c₀) := by group
        _ = a * (iA ι v₁ * b) * iA ι vq := by rw [hw₁, hq]
        _ = (a * iA ι v₁ * a⁻¹) * ((a * b) * iA ι vq * (a * b)⁻¹) * (a * b) := by group
        _ = iA ι (vact sa v₁) * iA ι (vact (sa * sb) vq) * (a * b) := by rw [hca1, hcab]
        _ = iA ι m * (a * b) := by rw [hm, iA_add]
    have hab2 : (a * b) * (a * b) = 1 := by
      calc (a * b) * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [← hab]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [ha2, hb2, one_mul]
    have hg4 : ((a * c₀) * (a * c₀)) * ((a * c₀) * (a * c₀)) =
        iA ι (m + vact (sa * sb) m) := by
      have h := E.sq_form m (a * b)
      rw [hπab, hab2, mul_one] at h
      rw [hg2]
      exact h
    set t : evenWeight 5 := u₀w + vact sa uw with ht
    have hs2 : ((iA ι t * (a * c₀)) * (iA ι t * (a * c₀))) =
        iA ι (t + vact s0 t) * ((a * c₀) * (a * c₀)) := by
      have h := E.sq_form t (a * c₀)
      rw [hπg] at h
      exact h
    have hπgg : π ((a * c₀) * (a * c₀)) = s0 * s0 := by rw [map_mul, hπg]
    have hs4 : (iA ι (t + vact s0 t) * ((a * c₀) * (a * c₀))) *
        (iA ι (t + vact s0 t) * ((a * c₀) * (a * c₀))) =
        iA ι ((t + vact s0 t) + vact (s0 * s0) (t + vact s0 t)) *
          (((a * c₀) * (a * c₀)) * ((a * c₀) * (a * c₀))) := by
      have h := E.sq_form (t + vact s0 t) ((a * c₀) * (a * c₀))
      rw [hπgg] at h
      exact h
    have hnr : (t + vact s0 t) + vact (s0 * s0) (t + vact s0 t) = nrmD t := nrmD_eq t
    have hfin : ((iA ι u₀w * a) * (iA ι uw * c₀)) ^ 4 = 1 := by
      calc ((iA ι u₀w * a) * (iA ι uw * c₀)) ^ 4
          = (((iA ι u₀w * a) * (iA ι uw * c₀)) * ((iA ι u₀w * a) * (iA ι uw * c₀))) *
            (((iA ι u₀w * a) * (iA ι uw * c₀)) * ((iA ι u₀w * a) * (iA ι uw * c₀))) := by
            rw [pow_four']
        _ = ((iA ι t * (a * c₀)) * (iA ι t * (a * c₀))) *
            ((iA ι t * (a * c₀)) * (iA ι t * (a * c₀))) := by rw [hac]
        _ = (iA ι (t + vact s0 t) * ((a * c₀) * (a * c₀))) *
            (iA ι (t + vact s0 t) * ((a * c₀) * (a * c₀))) := by rw [hs2]
        _ = iA ι (nrmD t) * iA ι (m + vact (sa * sb) m) := by rw [hs4, hnr, hg4]
        _ = iA ι (nrmD t + (m + vact (sa * sb) m)) := by rw [← iA_add]
        _ = 1 := by rw [h3, iA_zero]
    exact hfin

theorem mem_range_iff (E : DeltaExt ι π) (x : X) : x ∈ ι.range ↔ π x = 1 := by
  constructor
  · rintro ⟨y, rfl⟩
    have := E.pi_iA (Multiplicative.toAdd y)
    simpa [iA] using this
  · intro hx
    obtain ⟨w, hw⟩ := E.ker x hx
    exact ⟨Multiplicative.ofAdd w, hw⟩

theorem range_normal (E : DeltaExt ι π) : ι.range.Normal := by
  constructor
  intro n hn x
  obtain ⟨w, hw⟩ := E.ker n ((E.mem_range_iff n).mp hn)
  have h : x * n * x⁻¹ = iA ι (vact (π x) w) := by
    rw [← hw]
    exact E.conj_iA x w
  rw [h]
  exact ⟨Multiplicative.ofAdd _, rfl⟩

theorem exists_complement [Finite X] (E : DeltaExt ι π) {a b c₀ : X} (ha : π a = sa)
    (hb : π b = sb) (hc : π c₀ = sc) (ha2 : a * a = 1) (hb2 : b * b = 1) (hab : a * b = b * a) :
    ∃ D : Subgroup X, ι.range ⊓ D = ⊥ ∧ ι.range ⊔ D = ⊤ := by
  obtain ⟨a', c', ha', hc', ha2', hc2', hg4⟩ := E.exists_dihedral_lifts ha hb hc ha2 hb2 hab
  have : ι.range.Normal := E.range_normal
  set g : X := a' * c' with hg
  set K : Subgroup X := Subgroup.closure {a', c'} with hK
  have hπg : π g = s0 := by rw [hg, map_mul, ha', hc']; rfl
  have hainv : a'⁻¹ = a' := inv_eq_of_mul_eq_one_right ha2'
  have hcinv : c'⁻¹ = c' := inv_eq_of_mul_eq_one_right hc2'
  have hrel : a' * g = g ^ 3 * a' := by
    have h2 : a' * g = g⁻¹ * a' := by
      calc a' * g = a' * (a' * c') := by rw [hg]
        _ = (a' * a') * c' := by group
        _ = c' := by rw [ha2', one_mul]
        _ = (c' * a') * a' := by rw [mul_assoc, ha2', mul_one]
        _ = g⁻¹ * a' := by rw [hg, mul_inv_rev, hainv, hcinv]
    have h3 : g⁻¹ = g ^ 3 := by
      have : g⁻¹ * g ^ 4 = g ^ 3 := by group
      rw [← this, hg4, mul_one]
    rw [h2, h3]
  have hrelk : ∀ k : ℕ, a' * g ^ k = g ^ (3 * k) * a' := by
    intro k
    induction k with
    | zero => simp
    | succ n ih =>
      calc a' * g ^ (n + 1) = (a' * g ^ n) * g := by group
        _ = (g ^ (3 * n) * a') * g := by rw [ih]
        _ = g ^ (3 * n) * (a' * g) := by group
        _ = g ^ (3 * n) * (g ^ 3 * a') := by rw [hrel]
        _ = g ^ (3 * (n + 1)) * a' := by
          rw [show 3 * (n + 1) = 3 * n + 3 by ring, pow_add, mul_assoc]
  have hc_eq : c' = a' * g := by
    calc c' = (a' * a') * c' := by rw [ha2', one_mul]
      _ = a' * (a' * c') := by group
  have hstep : ∀ k ε : ℕ, ∃ k' ε' : ℕ, a' * (g ^ k * a' ^ ε) = g ^ k' * a' ^ ε' := by
    intro k ε
    refine ⟨3 * k, ε + 1, ?_⟩
    calc a' * (g ^ k * a' ^ ε) = (a' * g ^ k) * a' ^ ε := by group
      _ = (g ^ (3 * k) * a') * a' ^ ε := by rw [hrelk k]
      _ = g ^ (3 * k) * a' ^ (ε + 1) := by group
  have hstepc : ∀ k ε : ℕ, ∃ k' ε' : ℕ, c' * (g ^ k * a' ^ ε) = g ^ k' * a' ^ ε' := by
    intro k ε
    refine ⟨3 * (k + 1), ε + 1, ?_⟩
    calc c' * (g ^ k * a' ^ ε) = (a' * g) * (g ^ k * a' ^ ε) := by rw [← hc_eq]
      _ = a' * (g ^ (k + 1)) * a' ^ ε := by group
      _ = (g ^ (3 * (k + 1)) * a') * a' ^ ε := by rw [hrelk (k + 1)]
      _ = g ^ (3 * (k + 1)) * a' ^ (ε + 1) := by group
  have hnf : ∀ x ∈ K, ∃ k ε : ℕ, x = g ^ k * a' ^ ε := by
    intro x hx
    induction hx using Subgroup.closure_induction_left with
    | one => exact ⟨0, 0, by simp⟩
    | mul_left y hy z hz ih =>
      obtain ⟨k, ε, hz'⟩ := ih
      rw [hz']
      rcases hy with hy | hy
      · rw [hy]
        obtain ⟨k', ε', h⟩ := hstep k ε
        exact ⟨k', ε', h⟩
      · have hy' : y = c' := hy
        rw [hy']
        obtain ⟨k', ε', h⟩ := hstepc k ε
        exact ⟨k', ε', h⟩
    | inv_mul_cancel y hy z hz ih =>
      obtain ⟨k, ε, hz'⟩ := ih
      rw [hz']
      rcases hy with hy | hy
      · rw [hy, hainv]
        obtain ⟨k', ε', h⟩ := hstep k ε
        exact ⟨k', ε', h⟩
      · have hy' : y = c' := hy
        rw [hy', hcinv]
        obtain ⟨k', ε', h⟩ := hstepc k ε
        exact ⟨k', ε', h⟩
  have hVK : ι.range ⊓ K = ⊥ := by
    rw [eq_bot_iff]
    intro d hd
    obtain ⟨hdV, hdK⟩ := Subgroup.mem_inf.mp hd
    obtain ⟨k, ε, rfl⟩ := hnf d hdK
    have hπ : π (g ^ k * a' ^ ε) = 1 := (E.mem_range_iff _).mp hdV
    rw [map_mul, map_pow, map_pow, hπg, ha'] at hπ
    have hk : s0 ^ k = s0 ^ (k % 4) := pow_eq_pow_mod k s0_pow4
    have hε : sa ^ ε = sa ^ (ε % 2) := pow_eq_pow_mod ε sa_pow2
    rw [hk, hε] at hπ
    obtain ⟨hk0, hε0⟩ :=
      s0_free ⟨k % 4, Nat.mod_lt _ (by norm_num)⟩ ⟨ε % 2, Nat.mod_lt _ (by norm_num)⟩ hπ
    have hk0' : k % 4 = 0 := hk0
    have hε0' : ε % 2 = 0 := hε0
    have hg4' : g ^ k = 1 := by
      rw [pow_eq_pow_mod k hg4, hk0', pow_zero]
    have ha4' : a' ^ ε = 1 := by
      have ha2'' : a' ^ 2 = 1 := by rw [pow_two]; exact ha2'
      rw [pow_eq_pow_mod ε ha2'', hε0', pow_zero]
    rw [hg4', ha4', mul_one]
    exact Subgroup.one_mem _
  have hsupK : ι.range ⊔ K = Subgroup.comap π Dstd := by
    apply le_antisymm
    · refine sup_le ?_ ?_
      · intro v hv
        show π v ∈ Dstd
        rw [(E.mem_range_iff v).mp hv]
        exact one_mem _
      · rw [hK, Subgroup.closure_le]
        rintro x (hx | hx)
        · have hx' : x = a' := hx
          show π x ∈ Dstd
          rw [hx', ha']
          exact (mem_Dstd _).mpr sa_mem
        · have hx' : x = c' := hx
          show π x ∈ Dstd
          rw [hx', hc']
          exact (mem_Dstd _).mpr sc_mem
    · intro x hx
      have hx' : π x ∈ Dstd := hx
      obtain ⟨k, ε, hkε⟩ := s0_form (π x) ((mem_Dstd _).mp hx')
      set y : X := g ^ (k : ℕ) * a' ^ (ε : ℕ) with hy
      have hyK : y ∈ K := by
        refine mul_mem (pow_mem ?_ _) (pow_mem ?_ _)
        · exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
        · exact Subgroup.subset_closure (by simp)
      have hπy : π y = π x := by
        rw [hy, map_mul, map_pow, map_pow, hπg, ha', hkε]
      have hxy : x * y⁻¹ ∈ ι.range :=
        (E.mem_range_iff _).mpr (by rw [map_mul, map_inv, hπy, mul_inv_cancel])
      have : x = (x * y⁻¹) * y := by group
      rw [this]
      exact mul_mem (Subgroup.mem_sup_left hxy) (Subgroup.mem_sup_right hyK)
  have hidx : (ι.range ⊔ K).index = 15 := by
    rw [hsupK, Subgroup.index_comap_of_surjective _ E.surj, dset_index]
  have hVp : IsPGroup 2 ι.range := by
    intro v
    obtain ⟨y, hy⟩ := v.2
    refine ⟨1, ?_⟩
    have h := iA_self ι (Multiplicative.toAdd y)
    simp only [iA, ofAdd_toAdd] at h
    have e : v * v = 1 :=
      Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_one, ← hy]; exact h)
    rw [pow_one, pow_two]
    exact e
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hVp
  have hcop : Nat.Coprime (ι.range ⊔ K).index (Nat.card ι.range) := by
    rw [hidx, hn]
    exact Nat.Coprime.pow_right n (by decide)
  obtain ⟨D, -, hVD, hsupD⟩ :=
    CFSG.GroupTheory.abelian_normal_coprime_index_complement_lifting ι.range (ι.range ⊔ K) K hcop
      hVK rfl
  exact ⟨D, hVD, hsupD⟩

theorem exists_section [Finite X] (E : DeltaExt ι π) {a b c₀ : X} (ha : π a = sa)
    (hb : π b = sb) (hc : π c₀ = sc) (ha2 : a * a = 1) (hb2 : b * b = 1) (hab : a * b = b * a) :
    ∃ s : Perm (Fin 5) →* X, ∀ σ, π (s σ) = σ := by
  obtain ⟨D, hVD, hsup⟩ := E.exists_complement ha hb hc ha2 hb2 hab
  have : ι.range.Normal := E.range_normal
  let f : D →* Perm (Fin 5) := π.comp D.subtype
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro d hd
    have hd1 : π (d : X) = 1 := hd
    have hmem : (d : X) ∈ ι.range ⊓ D :=
      Subgroup.mem_inf.mpr ⟨(E.mem_range_iff _).mpr hd1, d.2⟩
    rw [hVD, Subgroup.mem_bot] at hmem
    exact (Subgroup.mem_bot).mpr (Subtype.ext hmem)
  have hsurj : Function.Surjective f := by
    intro σ
    obtain ⟨x, hx⟩ := E.surj σ
    have hxtop : x ∈ ι.range ⊔ D := by rw [hsup]; exact Subgroup.mem_top x
    obtain ⟨v, hv, d, hd, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hxtop
    refine ⟨⟨d, hd⟩, ?_⟩
    show π d = σ
    rw [← hx, map_mul, (E.mem_range_iff v).mp hv, one_mul]
  let e : D ≃* Perm (Fin 5) := MulEquiv.ofBijective f ⟨hinj, hsurj⟩
  refine ⟨D.subtype.comp e.symm.toMonoidHom, fun σ => ?_⟩
  show π ((e.symm σ : D) : X) = σ
  have : f (e.symm σ) = σ := e.apply_symm_apply σ
  exact this

end DeltaExt

end

end CFSG.QuasithinUnique.A5.Split
