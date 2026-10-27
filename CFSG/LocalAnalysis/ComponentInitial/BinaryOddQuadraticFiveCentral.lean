module

public import CFSG.LocalAnalysis.ComponentInitial.BinaryOddQuadraticFiveSplitting
public import CFSG.LocalAnalysis.ComponentInitial.BinaryOddQuadraticFiveInvariants
public import Mathlib.FieldTheory.Finiteness

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace OddQuadraticFive

open BinarySymplecticTransvection
open scoped commutatorElement

variable {E : Type} [AddCommGroup E] [Module (ZMod 2) E] {D : Type} [Group D] {B : Subgroup D}
  {θ : B ≃* Multiplicative ((E × ZMod 2) × ZMod 2)} {b : LinearMap.BilinForm (ZMod 2) E}
  {Q : QuadraticForm (ZMod 2) E}

namespace Labels

variable (L : Labels θ b 0)

include L in
theorem conj_subA_central {x : D} (hx : x ∈ subA θ) (d : D) : d⁻¹ * x * d = x := by
  obtain ⟨v, rfl⟩ := hx
  rw [L.conj_bv]
  simp

include L in
theorem commute_of_mem_subA_central {x : D} (hx : x ∈ subA θ) (d : D) : d * x = x * d := by
  obtain ⟨v, rfl⟩ := hx
  have h : d⁻¹ * bv θ (v, 0) * d = bv θ (v, 0) := by
    rw [L.conj_bv]
    simp
  calc d * bv θ (v, 0) = d * (d⁻¹ * bv θ (v, 0) * d) := by rw [h]
    _ = bv θ (v, 0) * d := by group

theorem lab_mul_central (hb : b.IsAlt) (d d' : D) : L.lab (d * d') = L.lab d + L.lab d' := by
  rw [L.lab_mul hb, zero_mul, zero_smul, add_zero]

theorem lab_inv_central (hb : b.IsAlt) (d : D) : L.lab d⁻¹ = L.lab d := by
  have h := L.lab_mul_central hb d⁻¹ d
  rw [inv_mul_cancel, L.lab_one] at h
  exact eq_of_add_eq_zero_zmod2 h.symm

theorem center_eq (hfaith : ∀ d : D, (∀ v, d⁻¹ * bv θ (v, 1) * d = bv θ (v, 1)) → d ∈ B)
    (hsurj : ∀ a, ∃ d, L.lab d = a) : Subgroup.center D = subA θ := by
  refine le_antisymm (fun x hx => ?_) fun x hx =>
    Subgroup.mem_center_iff.2 fun d => L.commute_of_mem_subA_central hx d
  have hc := Subgroup.mem_center_iff.1 hx
  have hxB : x ∈ B := by
    refine L.mem_of_lab_eq_zero hfaith ?_
    have h := L.conj_zz x
    rw [mul_assoc, hc, ← mul_assoc, inv_mul_cancel, one_mul, zz] at h
    exact (congrArg Prod.fst (bv_injective θ h)).symm
  obtain ⟨f₀, hf₀⟩ := hsurj rV
  obtain ⟨y, rfl⟩ := exists_bv_eq θ hxB
  refine mem_subA_of_cB θ hxB ?_
  rw [cB_bv]
  have h := L.conj_bv f₀ y.1 y.2
  rw [Prod.mk.eta, mul_assoc, ← hc f₀, ← mul_assoc, inv_mul_cancel, one_mul, hf₀] at h
  have h2 := congrArg (fun x : (E × ZMod 2) × ZMod 2 => x.1.2) (bv_injective θ h)
  simpa [rV] using h2

include L in
theorem sq_mul_of_mem_subA {c x : D} (hx : x ∈ subA θ) : (c * x) ^ 2 = c ^ 2 := by
  have hcx := L.commute_of_mem_subA_central hx c
  rw [sq, sq]
  calc c * x * (c * x) = c * (x * c) * x := by group
    _ = c * (c * x) * x := by rw [← hcx]
    _ = c * c * x ^ 2 := by rw [sq]; group
    _ = c * c := by rw [sq_eq_one_of_mem θ (subA_le θ hx), mul_one]

include L in
theorem sq_mul_central (hb : b.IsAlt)
    (hfaith : ∀ d : D, (∀ v, d⁻¹ * bv θ (v, 1) * d = bv θ (v, 1)) → d ∈ B) (c c' : D) :
    (c * c') ^ 2 = c ^ 2 * c' ^ 2 * (c'⁻¹ * c⁻¹ * c' * c) := by
  have e : (c * c') ^ 2 = c ^ 2 * c' ^ 2 * (c'⁻¹ * (c'⁻¹ * c⁻¹ * c' * c) * c') := by
    rw [sq, sq, sq]
    group
  rw [e, L.conj_subA_central (L.comm_mem_subA hb hfaith c' c) c']

@[expose] def pD (θ : B ≃* Multiplicative ((E × ZMod 2) × ZMod 2)) (c c' : D) : ZMod 2 :=
  (cB θ (c'⁻¹ * c⁻¹ * c' * c)).1.2

include L in
theorem pD_mul_left (hb : b.IsAlt)
    (hfaith : ∀ d : D, (∀ v, d⁻¹ * bv θ (v, 1) * d = bv θ (v, 1)) → d ∈ B) (c₁ c₂ c' : D) :
    pD θ (c₁ * c₂) c' = pD θ c₁ c' + pD θ c₂ c' := by
  have e : c'⁻¹ * (c₁ * c₂)⁻¹ * c' * (c₁ * c₂) =
      (c'⁻¹ * c₂⁻¹ * c' * c₂) * (c₂⁻¹ * (c'⁻¹ * c₁⁻¹ * c' * c₁) * c₂) := by group
  have h₁ := L.comm_mem_subA hb hfaith c' c₁
  have h₂ := L.comm_mem_subA hb hfaith c' c₂
  have hk : c₂⁻¹ * (c'⁻¹ * c₁⁻¹ * c' * c₁) * c₂ = c'⁻¹ * c₁⁻¹ * c' * c₁ :=
    L.conj_subA_central h₁ c₂
  rw [pD, pD, pD, e, hk, cB_mul θ (subA_le θ h₂) (subA_le θ h₁), Prod.fst_add, Prod.snd_add,
    add_comm]

include L in
theorem pD_mul_right (hb : b.IsAlt)
    (hfaith : ∀ d : D, (∀ v, d⁻¹ * bv θ (v, 1) * d = bv θ (v, 1)) → d ∈ B) (c c'₁ c'₂ : D) :
    pD θ c (c'₁ * c'₂) = pD θ c c'₁ + pD θ c c'₂ := by
  have e : (c'₁ * c'₂)⁻¹ * c⁻¹ * (c'₁ * c'₂) * c =
      (c'₂⁻¹ * (c'₁⁻¹ * c⁻¹ * c'₁ * c) * c'₂) * (c'₂⁻¹ * c⁻¹ * c'₂ * c) := by group
  have h₁ := L.comm_mem_subA hb hfaith c'₁ c
  have h₂ := L.comm_mem_subA hb hfaith c'₂ c
  have hk : c'₂⁻¹ * (c'₁⁻¹ * c⁻¹ * c'₁ * c) * c'₂ = c'₁⁻¹ * c⁻¹ * c'₁ * c :=
    L.conj_subA_central h₁ c'₂
  rw [pD, pD, pD, e, hk, cB_mul θ (subA_le θ h₁) (subA_le θ h₂), Prod.fst_add, Prod.snd_add]

@[expose] def fD (θ : B ≃* Multiplicative ((E × ZMod 2) × ZMod 2)) (L : Labels θ b 0)
    (α : ZMod 2) (c : D) : ZMod 2 :=
  (cB θ (c ^ 2)).1.2 + α * (L.lab c).2

theorem fD_mul (hb : b.IsAlt)
    (hfaith : ∀ d : D, (∀ v, d⁻¹ * bv θ (v, 1) * d = bv θ (v, 1)) → d ∈ B) (α : ZMod 2)
    (c c' : D) : fD θ L α (c * c') = fD θ L α c + fD θ L α c' + pD θ c c' := by
  rw [fD, fD, fD, pD, L.sq_mul_central hb hfaith,
    cB_mul θ (mul_mem (L.sq_mem hb hfaith c) (L.sq_mem hb hfaith c'))
      (subA_le θ (L.comm_mem_subA hb hfaith c' c)),
    cB_mul θ (L.sq_mem hb hfaith c) (L.sq_mem hb hfaith c'), L.lab_mul_central hb]
  simp only [Prod.fst_add, Prod.snd_add]
  ring

theorem fD_mul_of_mem_subA (hb : b.IsAlt) (α : ZMod 2) (c : D) {x : D} (hx : x ∈ subA θ) :
    fD θ L α (c * x) = fD θ L α c := by
  rw [fD, fD, L.sq_mul_of_mem_subA hx, L.lab_mul_central hb, L.lab_of_mem (subA_le θ hx),
    add_zero]

include L in
theorem pD_of_mem_subA {x : D} (hx : x ∈ subA θ) (d : D) : pD θ x d = 0 := by
  have h : d⁻¹ * x⁻¹ * d * x = 1 := by
    rw [L.conj_subA_central (inv_mem hx) d, inv_mul_cancel]
  rw [pD, h, cB_one]
  rfl

include L in
theorem pD_of_mem_subA_right {x : D} (hx : x ∈ subA θ) (d : D) : pD θ d x = 0 := by
  have h : x⁻¹ * d⁻¹ * x * d = 1 := by
    calc x⁻¹ * d⁻¹ * x * d = x⁻¹ * (d⁻¹ * x * d) := by group
      _ = 1 := by rw [L.conj_subA_central hx d, inv_mul_cancel]
  rw [pD, h, cB_one]
  rfl

theorem fD_act (hQ : QuadraticMap.polarBilin Q = b) (act : bilinIsometryGroup b →* MulAut D)
    (hact : ∀ s v ε, act s (bv θ (v, ε)) = bv θ (hV hQ s v, ε)) (hb : b.IsAlt)
    (hfaith : ∀ d : D, (∀ v, d⁻¹ * bv θ (v, 1) * d = bv θ (v, 1)) → d ∈ B) (α : ZMod 2)
    {c : D} (hσ : sig θ c = α • (L.lab c).1) (s : bilinIsometryGroup b) :
    fD θ L α (act s c) = fD θ L α c := by
  have hc2 := L.sq_mem hb hfaith c
  have h1 : (cB θ (c ^ 2)).1.1 = α • (L.lab c).1 := hσ
  rw [fD, fD, ← map_pow, cB_act hQ act hact s hc2, L.lab_act hQ act hact, hV_apply, hV_apply]
  simp only
  rw [h1, (sE s).map_smul, Q_smul, Q_smul]
  generalize (cB θ (c ^ 2)).1.2 = p₁
  generalize (L.lab c).2 = p₂
  generalize Q (L.lab c).1 = p₃
  generalize Q (sE s (L.lab c).1) = p₄
  generalize α = p₅
  revert p₁ p₂ p₃ p₄ p₅
  decide

theorem inv_mul_mem_of_lab_eq (hb : b.IsAlt)
    (hfaith : ∀ d : D, (∀ v, d⁻¹ * bv θ (v, 1) * d = bv θ (v, 1)) → d ∈ B) {C : Subgroup D}
    (hBC : B ⊓ C = subA θ) {c c' : D} (hc : c ∈ C) (hc' : c' ∈ C) (h : L.lab c = L.lab c') :
    c'⁻¹ * c ∈ subA θ := by
  rw [← hBC]
  refine Subgroup.mem_inf.2 ⟨L.mem_of_lab_eq_zero hfaith ?_, C.mul_mem (C.inv_mem hc') hc⟩
  rw [L.lab_mul_central hb, L.lab_inv_central hb, h, add_self_eq_zero_zmod_two]

theorem exists_square_formula (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (hQ : QuadraticMap.polarBilin Q = b)
    (hfaith : ∀ d : D, (∀ v, d⁻¹ * bv θ (v, 1) * d = bv θ (v, 1)) → d ∈ B)
    (hsurj : ∀ a, ∃ d, L.lab d = a) [Finite E] (hE : 4 < Nat.card E)
    (act : bilinIsometryGroup b →* MulAut D)
    (hact : ∀ s v ε, act s (bv θ (v, ε)) = bv θ (hV hQ s v, ε)) {C : Subgroup D} {α : ZMod 2}
    (hidx : ∀ d, d ∈ C ∨ d * zz θ ∈ C) (hBC : B ⊓ C = subA θ)
    (hCS : ∀ s, ∀ c ∈ C, act s c ∈ C) (hσ : ∀ c ∈ C, sig θ c = α • (L.lab c).1) :
    ∃ β : ZMod 2, (∀ c ∈ C, c ^ 2 = bv θ (α • L.lab c + (β * qV Q (L.lab c)) • rV, 0)) ∧
      ∀ c ∈ C, ∀ d ∈ C, pD θ c d = β * b (L.lab c).1 (L.lab d).1 := by
  choose lift hliftC hliftl using fun v => L.exists_mem_lab hb hsurj hidx v
  have hfD : ∀ c ∈ C, fD θ L α c = fD θ L α (lift (L.lab c)) := by
    intro c hc
    have h := L.inv_mul_mem_of_lab_eq hb hfaith hBC hc (hliftC _) (hliftl _).symm
    rw [show c = lift (L.lab c) * ((lift (L.lab c))⁻¹ * c) by group,
      L.fD_mul_of_mem_subA hb α _ h, ← show c = lift (L.lab c) * ((lift (L.lab c))⁻¹ * c) by
        group]
  have hpD : ∀ c ∈ C, ∀ d ∈ C, pD θ c d = pD θ (lift (L.lab c)) (lift (L.lab d)) := by
    intro c hc d hd
    have h1 := L.inv_mul_mem_of_lab_eq hb hfaith hBC hc (hliftC _) (hliftl _).symm
    have h2 := L.inv_mul_mem_of_lab_eq hb hfaith hBC hd (hliftC _) (hliftl _).symm
    have ec : c = lift (L.lab c) * ((lift (L.lab c))⁻¹ * c) := by group
    have ed : d = lift (L.lab d) * ((lift (L.lab d))⁻¹ * d) := by group
    rw [ec, L.pD_mul_left hb hfaith, L.pD_of_mem_subA h1, add_zero, ed,
      L.pD_mul_right hb hfaith, L.pD_of_mem_subA_right h2, add_zero, ← ec, ← ed]
  set f : E × ZMod 2 → ZMod 2 := fun v => fD θ L α (lift v) with hf
  have hlab_mul : ∀ v w, L.lab (lift v * lift w) = v + w := fun v w => by
    rw [L.lab_mul_central hb, hliftl, hliftl]
  have hfadd : ∀ v w, f (v + w) = f v + f w + pD θ (lift v) (lift w) := by
    intro v w
    have h := hfD _ (mul_mem (hliftC v) (hliftC w))
    rw [hlab_mul, L.fD_mul hb hfaith] at h
    exact h.symm
  have hpadd_left : ∀ v₁ v₂ w,
      pD θ (lift (v₁ + v₂)) (lift w) = pD θ (lift v₁) (lift w) + pD θ (lift v₂) (lift w) := by
    intro v₁ v₂ w
    have h := hpD _ (mul_mem (hliftC v₁) (hliftC v₂)) _ (hliftC w)
    rw [hlab_mul, hliftl, L.pD_mul_left hb hfaith] at h
    exact h.symm
  have hpadd_right : ∀ v w₁ w₂,
      pD θ (lift v) (lift (w₁ + w₂)) = pD θ (lift v) (lift w₁) + pD θ (lift v) (lift w₂) := by
    intro v w₁ w₂
    have h := hpD _ (hliftC v) _ (mul_mem (hliftC w₁) (hliftC w₂))
    rw [hlab_mul, hliftl, L.pD_mul_right hb hfaith] at h
    exact h.symm
  have hp0l : ∀ w, pD θ (lift 0) (lift w) = 0 := fun w => by
    have h := hpadd_left 0 0 w
    rw [add_zero, add_self_eq_zero_zmod_two] at h
    exact h
  have hp0r : ∀ v, pD θ (lift v) (lift 0) = 0 := fun v => by
    have h := hpadd_right v 0 0
    rw [add_zero, add_self_eq_zero_zmod_two] at h
    exact h
  set p : LinearMap.BilinForm (ZMod 2) (E × ZMod 2) :=
    LinearMap.mk₂ (ZMod 2) (fun v w => pD θ (lift v) (lift w)) hpadd_left
      (fun c v w => by
        rcases zmod_two_cases c with rfl | rfl
        · rw [zero_smul, hp0l, zero_smul]
        · rw [one_smul, one_smul])
      hpadd_right
      (fun c v w => by
        rcases zmod_two_cases c with rfl | rfl
        · rw [zero_smul, hp0r, zero_smul]
        · rw [one_smul, one_smul]) with hp
  have hf' : ∀ v w, f (v + w) = f v + f w + p v w := fun v w => hfadd v w
  have hfS : ∀ (s : bilinIsometryGroup b) w t,
      f (sE s w, t + Q w + Q (sE s w)) = f (w, t) := by
    intro s w t
    have hl : L.lab (act s (lift (w, t))) = (sE s w, t + Q w + Q (sE s w)) := by
      rw [L.lab_act hQ act hact, hliftl, hV_apply]
    have h1 := hfD _ (hCS s _ (hliftC (w, t)))
    rw [hl] at h1
    rw [hf]
    simp only
    rw [← h1, L.fD_act hQ act hact hb hfaith α (hσ _ (hliftC _))]
  obtain ⟨β, hβ⟩ := exists_eq_mul_qV_of_invariant hb hnd hQ hE p hf' hfS
  have hqV : ∀ u v : E × ZMod 2, qV Q (u + v) = qV Q u + qV Q v + b u.1 v.1 := fun u v => by
    simp only [qV, Prod.fst_add, Prod.snd_add, Q_add hQ]
    ring
  refine ⟨β, fun c hc => ?_, fun c hc d hd => ?_⟩
  · obtain ⟨w, hw⟩ := L.sq_mem_subA hb hfaith c
    have hw1 : w.1 = α • (L.lab c).1 := by
      have h := hσ c hc
      rw [sig, ← hw, cB_bv] at h
      exact h
    have hw2 : w.2 = β * qV Q (L.lab c) + α * (L.lab c).2 := by
      have h := hfD c hc
      have h' : fD θ L α (lift (L.lab c)) = β * qV Q (L.lab c) := hβ (L.lab c)
      rw [h', fD, ← hw, cB_bv] at h
      rw [← h]
      simp only
      rw [add_assoc, zmod2_add_self, add_zero]
    rw [← hw]
    congr 2
    ext
    · simp [hw1, rV]
    · simp only [Prod.snd_add, Prod.smul_snd, rV, smul_eq_mul, mul_one, hw2]
      ring
  · have h := hf' (L.lab c) (L.lab d)
    rw [hβ, hβ, hβ, hqV] at h
    have hpcd : pD θ c d = p (L.lab c) (L.lab d) := hpD c hc d hd
    rw [hpcd]
    linear_combination -h

theorem natCard_inf_subF (hb : b.IsAlt)
    (hfaith : ∀ d : D, (∀ v, d⁻¹ * bv θ (v, 1) * d = bv θ (v, 1)) → d ∈ B) [Finite E]
    (hcardE : Nat.card E = 16) {C : Subgroup D} {ξ : D} (hAC : subA θ ≤ C) (hξC : ξ ∈ C)
    (hξl : L.lab ξ = rV) (hCF : ∀ c ∈ C, (L.lab c).1 = 0 → c ∈ subA θ ∨ ξ⁻¹ * c ∈ subA θ) :
    Nat.card (C ⊓ L.subF hb : Subgroup D) = 64 := by
  have hξH : ξ ∈ C ⊓ L.subF hb := ⟨hξC, (L.mem_subF hb).2 (by rw [hξl]; rfl)⟩
  have hAH : subA θ ≤ C ⊓ L.subF hb := le_inf hAC (L.subA_le_subF hb)
  have hξA : ξ ∉ subA θ := fun h => by
    have := congrArg Prod.snd ((L.lab_of_mem (subA_le θ h)).symm.trans hξl)
    exact absurd this (by simp [rV])
  have hidx : ((subA θ).subgroupOf (C ⊓ L.subF hb)).index = 2 := by
    refine Subgroup.index_eq_two_iff.2 ⟨⟨ξ, hξH⟩, fun g => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    change Xor ((g : D) * ξ ∈ subA θ) ((g : D) ∈ subA θ)
    rcases hCF g g.2.1 ((L.mem_subF hb).1 g.2.2) with h | h
    · refine Or.inr ⟨h, fun h' => hξA ?_⟩
      have := mul_mem (inv_mem h) h'
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
    · refine Or.inl ⟨?_, fun h' => hξA ?_⟩
      · have e : (g : D) * ξ = ξ ^ 2 * (ξ⁻¹ * g) := by
          calc (g : D) * ξ = ξ * (ξ⁻¹ * g) * ξ := by group
            _ = ξ * (ξ * (ξ⁻¹ * g)) := by
              rw [mul_assoc, ← L.commute_of_mem_subA_central h ξ]
            _ = ξ ^ 2 * (ξ⁻¹ * g) := by rw [sq, mul_assoc]
        rw [e]
        exact mul_mem (L.sq_mem_subA hb hfaith ξ) h
      · have := mul_mem h' (inv_mem h)
        rw [mul_inv_rev, inv_inv, ← mul_assoc, mul_inv_cancel, one_mul] at this
        exact this
  have h := Subgroup.card_mul_index ((subA θ).subgroupOf (C ⊓ L.subF hb))
  have hA : Nat.card (subA θ) = 32 := by
    have hbij : Function.Bijective
        (fun v : E × ZMod 2 => (⟨bv θ (v, 0), ⟨v, rfl⟩⟩ : subA θ)) := by
      refine ⟨fun v w hvw => ?_, fun x => ?_⟩
      · have h1 : bv θ ((v, 0) : (E × ZMod 2) × ZMod 2) = bv θ (w, 0) :=
          congrArg (fun x : subA θ => (x : D)) hvw
        exact congrArg Prod.fst (bv_injective θ h1)
      · obtain ⟨v, hv⟩ := x.2
        exact ⟨v, Subtype.ext hv⟩
    rw [← Nat.card_eq_of_bijective _ hbij, natCard_V hcardE]
  rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv, hA] at h
  omega

end Labels

end OddQuadraticFive

open OddQuadraticFive

theorem binary_odd_quadratic_five_central_action_index_two_subgroup
    {E : Type} [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
    (hE : Module.finrank (ZMod 2) E = 4) (b : LinearMap.BilinForm (ZMod 2) E) (hb : b.IsAlt)
    (hnd : b.Nondegenerate) (Q : QuadraticForm (ZMod 2) E) (hQ : QuadraticMap.polarBilin Q = b)
    {D : Type} [Group D] [Finite D] (B : Subgroup D) [B.Normal]
    (θ : B ≃* Multiplicative ((E × ZMod 2) × ZMod 2))
    (hconj : ∀ d : D, ∃ a : E × ZMod 2, ∀ v : E × ZMod 2,
      d⁻¹ * bv θ (v, 1) * d = bv θ (v + a, 1))
    (hsurj : ∀ a : E × ZMod 2, ∃ d : D, ∀ v : E × ZMod 2,
      d⁻¹ * bv θ (v, 1) * d = bv θ (v + a, 1))
    (hfaith : ∀ d : D, (∀ v, d⁻¹ * bv θ (v, 1) * d = bv θ (v, 1)) → d ∈ B)
    (act : bilinIsometryGroup b →* MulAut D)
    (hact : ∀ s v ε, act s (bv θ (v, ε)) = bv θ (hV hQ s v, ε)) :
    Nat.card D = 2048 ∧ Subgroup.center D = subA θ ∧ commutator D = subA θ ∧
      Subgroup.closure {x : D | ∃ y : D, y ^ 2 = x} = subA θ ∧
    ∃ F : Subgroup D, (∀ d, d ∈ F ↔ (zz θ)⁻¹ * d⁻¹ * zz θ * d ∈ subI θ) ∧ Nat.card F = 128 ∧
      (Subgroup.center F).map F.subtype = subA θ ∧ ⁅F, F⁆ = subI θ ∧
      Subgroup.closure {x : D | ∃ y ∈ F, y ^ 2 = x} = subI θ ∧
    ∃ C : Subgroup D, C.Normal ∧ (∀ s, ∀ c ∈ C, act s c ∈ C) ∧ Nat.card C = 1024 ∧
      Subgroup.zpowers (zz θ) ⊔ C = ⊤ ∧ C ⊓ B = subA θ ∧
    ∃ τ : D → E × ZMod 2,
      (∀ c ∈ C, (zz θ)⁻¹ * c⁻¹ * zz θ * c = bv θ (τ c, 0)) ∧
      (∀ c ∈ C, ∀ c' ∈ C, τ (c * c') = τ c + τ c') ∧ (∀ v, ∃ c ∈ C, τ c = v) ∧
      (∀ c ∈ C, τ c = 0 ↔ c ∈ subA θ) ∧ (∀ s, ∀ c ∈ C, τ (act s c) = hV hQ s (τ c)) ∧
      (∀ x ∈ C ⊓ F, ∀ y ∈ C, x * y = y * x) ∧ Nat.card (C ⊓ F : Subgroup D) = 64 ∧
    ∃ α β : ZMod 2,
      (∀ c ∈ C, c ^ 2 = bv θ (α • τ c + (β * qV Q (τ c)) • rV, 0)) ∧
      ⁅C, C⁆ ≤ subI θ ∧
      (∀ c ∈ C, ∀ d ∈ C, c⁻¹ * d⁻¹ * c * d = bv θ ((β * b (τ c).1 (τ d).1) • rV, 0)) ∧
      (α = 1 → ∀ c ∈ C, c ^ 2 = 1 → c ∈ C ⊓ F) ∧
      (α = 0 → Subgroup.closure {x : D | ∃ y ∈ C, y ^ 2 = x} ≤ subI θ ∧
        (∀ s, ∀ x ∈ subI θ, act s x ∈ subI θ) ∧ subI θ ≤ subA θ ∧ subA θ ≤ C) := by
  have : Finite E := Module.finite_of_finite (ZMod 2)
  have hcardE : Nat.card E = 16 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := E), hE, Nat.card_zmod]
    norm_num
  have hE4 : 4 < Nat.card E := by
    rw [hcardE]
    norm_num
  let e : Module.Basis (Fin 4) (ZMod 2) E := Module.finBasisOfFinrankEq (ZMod 2) E hE
  choose lab hlab using hconj
  let L : Labels θ b 0 := ⟨lab, fun d v => by rw [hlab d v, zero_mul, zero_smul, add_zero]⟩
  have hsurj' : ∀ a, ∃ d, L.lab d = a := by
    intro a
    obtain ⟨d, hd⟩ := hsurj a
    refine ⟨d, ?_⟩
    have h := (L.conj_zz d).symm.trans (hd 0)
    rw [zero_add] at h
    exact congrArg Prod.fst (bv_injective θ h)
  have hcard := L.natCard_D hb hQ hfaith hsurj' hcardE
  have hcomm := L.commutator_eq hb hfaith hsurj'
  obtain ⟨-, -, hFc, hFZ, hFc', hFsq⟩ := L.subF_props hQ act hact hb hnd hfaith hsurj' hcardE
  obtain ⟨C, a, ξ, hAC, hz, hidx, hCS, hω, hσ, hξC, hξl, hCF⟩ :=
    L.exists_index_two hQ act hact hb hnd hfaith hsurj' hE4 e
  obtain ⟨hCc, hCtop, hBC⟩ := index_two_props hAC hz hidx hcard
  obtain ⟨β, hsq, hpD⟩ :=
    L.exists_square_formula hb hnd hQ hfaith hsurj' hE4 act hact hidx hBC hCS hσ
  have hcf : ∀ c ∈ C, ∀ d ∈ C,
      c⁻¹ * d⁻¹ * c * d = bv θ ((β * b (L.lab c).1 (L.lab d).1) • rV, 0) := by
    intro c hc d hd
    have hk := L.comm_mem_subA hb hfaith c d
    obtain ⟨w, hw⟩ := hk
    have h1 : w.1 = 0 := by
      have := hω c hc d hd
      rw [om, ← hw, cB_bv] at this
      exact this
    have h2 : w.2 = β * b (L.lab c).1 (L.lab d).1 := by
      have := hpD d hd c hc
      rw [Labels.pD, ← hw, cB_bv] at this
      rw [this, BinarySymplecticTransvection.symm_apply hb]
    rw [← hw]
    congr 2
    ext
    · simp [h1, rV]
    · simp [h2, rV]
  refine ⟨hcard, L.center_eq hfaith hsurj', hcomm, L.closure_sq_eq hb hfaith hsurj', L.subF hb,
    fun d => L.mem_subF_iff_comm hb, hFc, hFZ, hFc', hFsq, C,
    normal_of_commutator_le (hcomm.le.trans hAC), hCS, hCc, hCtop, by rw [inf_comm, hBC],
    L.lab, fun c _ => L.comm_zz c, fun c _ c' _ => L.lab_mul_central hb c c',
    L.exists_mem_lab hb hsurj' hidx, fun c hc => ⟨fun h => ?_, fun h => L.lab_of_mem (subA_le θ h)⟩,
    fun s c _ => L.lab_act hQ act hact s c, fun x hx y hy => ?_,
    L.natCard_inf_subF hb hfaith hcardE hAC hξC hξl hCF, a, β, hsq,
    L.commutator_le_subI hb hfaith hω, hcf, fun ha c hc hc2 => ?_, fun ha => ?_⟩
  · rw [← hBC]
    exact ⟨L.mem_of_lab_eq_zero hfaith h, hc⟩
  ·
    have h := hcf x hx.1 y hy
    rw [(L.mem_subF hb).1 hx.2, map_zero, LinearMap.zero_apply, mul_zero, zero_smul,
      Prod.mk_zero_zero, bv_zero] at h
    calc x * y = x * y * (x⁻¹ * y⁻¹ * x * y)⁻¹ := by rw [h, inv_one, mul_one]
      _ = y * x := by group
  ·
    refine ⟨hc, (L.mem_subF hb).2 ?_⟩
    have h := hsq c hc
    rw [hc2, ha, one_smul, ← bv_zero θ] at h
    have := congrArg (fun x : (E × ZMod 2) × ZMod 2 => x.1.1) (bv_injective θ h)
    simpa [rV] using this.symm
  ·
    refine ⟨?_, fun s x hx => act_mem_subI hQ act hact s hx, subI_le_subA θ, hAC⟩
    rw [Subgroup.closure_le]
    rintro _ ⟨y, hy, rfl⟩
    rw [hsq y hy, ha, zero_smul, zero_add]
    exact ⟨_, rfl⟩

end CFSG.LocalAnalysis.ComponentInitial
