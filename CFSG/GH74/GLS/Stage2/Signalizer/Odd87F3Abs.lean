module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87QuotTools
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87F3S

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup

section Def

variable {Y : Type*} [Group Y]

@[expose] def oddFixed (α : MulAut Y) : Set Y := {y | α y = y ∧ Odd (orderOf y)}

@[expose] def oddConjClosure (α : MulAut Y) (x : Y) : Subgroup Y :=
  Subgroup.closure {w | ∃ c ∈ Subgroup.closure (oddFixed α), w = c * x * c⁻¹}

@[expose] def F3 (p : ℕ) (α : MulAut Y) : Prop :=
  ∀ x : Y, orderOf x = p → α x = x⁻¹ → ¬ IsPGroup p ↥(oddConjClosure α x)

end Def

section Quot

variable {P : Type} [Group P] {p : ℕ} {α : MulAut P} {Xh : Subgroup P}

theorem QuotCfg.exists_inverted (h : QuotCfg p α Xh) : ∃ x ∈ Xh, orderOf x = p ∧ α x = x⁻¹ := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨y, hy, hne⟩ : ∃ y ∈ Xh, α y ≠ y := by
    by_contra hcon
    exact h.not_fixed fun x hx => by_contra fun hne => hcon ⟨x, hx, hne⟩
  set x₀ : P := y * (α y)⁻¹ with hx₀
  have hx₀mem : x₀ ∈ Xh := Xh.mul_mem hy (Xh.inv_mem (h.inv y hy))
  have hx₀inv : α x₀ = x₀⁻¹ := by
    rw [hx₀, map_mul, map_inv, h.invol y, mul_inv_rev, inv_inv]
  have hx₀ne : x₀ ≠ 1 := by
    intro h1
    exact hne (mul_inv_eq_one.mp h1).symm
  obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf.mp h.pgroup) ⟨x₀, hx₀mem⟩
  have ha' : orderOf x₀ = p ^ a := by rwa [Subgroup.orderOf_mk] at ha
  have ha1 : a ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at ha'
    exact hx₀ne ha'
  refine ⟨x₀ ^ (p ^ (a - 1)), Xh.pow_mem hx₀mem _, ?_, ?_⟩
  · have hdvd : p ^ (a - 1) ∣ orderOf x₀ := by
      rw [ha']
      exact pow_dvd_pow p (Nat.sub_le a 1)
    rw [orderOf_pow_of_dvd (pow_ne_zero _ h.prime.ne_zero) hdvd, ha',
      Nat.pow_div (Nat.sub_le a 1) h.prime.pos]
    have : a - (a - 1) = 1 := by omega
    rw [this, pow_one]
  · rw [map_pow, hx₀inv, inv_pow]

theorem QuotCfg.false_of_F3 (h : QuotCfg p α Xh) (hF : F3 p α) : False := by
  obtain ⟨x, hx, hxo, hxα⟩ := h.exists_inverted
  refine hF x hxo hxα (h.pgroup.to_le ?_)
  rw [oddConjClosure, Subgroup.closure_le]
  rintro w ⟨c, hc, rfl⟩
  have hcN : c ∈ normalizer (Xh : Set P) := h.closure_odd_le_normalizer hc
  exact (Subgroup.mem_normalizer_iff.mp hcN x).mp hx

end Quot

section Transport

variable {Y T : Type*} [Group Y] [Group T]

theorem map_closure_oddFixed (e : Y ≃* T) {α : MulAut Y} {β : MulAut T} (hαβ : ∀ y, e (α y) = β (e y)) :
    (Subgroup.closure (oddFixed α)).map e.toMonoidHom = Subgroup.closure (oddFixed β) := by
  rw [MonoidHom.map_closure]
  congr 1
  ext t
  constructor
  · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · show β (e y) = e y
      rw [← hαβ, hy1]
    · show Odd (orderOf (e y))
      rw [MulEquiv.orderOf_eq]; exact hy2
  · rintro ⟨ht1, ht2⟩
    refine ⟨e.symm t, ⟨?_, ?_⟩, by simp⟩
    · apply e.injective
      rw [hαβ, MulEquiv.apply_symm_apply, ht1]
    · rw [MulEquiv.orderOf_eq]; exact ht2

theorem F3.of_equiv (e : Y ≃* T) {p : ℕ} {α : MulAut Y} {β : MulAut T} (hαβ : ∀ y, e (α y) = β (e y))
    (h : F3 p β) : F3 p α := by
  intro x hxo hxα hpg
  have hmap := map_closure_oddFixed e hαβ
  apply h (e x) (by rw [MulEquiv.orderOf_eq]; exact hxo)
    (by rw [← hαβ, hxα, map_inv])
  have hle : oddConjClosure β (e x) ≤ (oddConjClosure α x).map e.toMonoidHom := by
    rw [oddConjClosure, Subgroup.closure_le]
    rintro w ⟨c, hc, rfl⟩
    rw [← hmap] at hc
    obtain ⟨c', hc', rfl⟩ := Subgroup.mem_map.mp hc
    refine ⟨c' * x * c'⁻¹, Subgroup.subset_closure ⟨c', hc', rfl⟩, ?_⟩
    simp
  exact (hpg.map e.toMonoidHom).to_le hle

end Transport

section Ambient

variable {M : Type*} [Group M]

theorem mem_closure_oddFixed_subgroup {G : Subgroup M} {u : M} (β : MulAut ↥G)
    (hβ : ∀ g : ↥G, ((β g : ↥G) : M) = u * g * u⁻¹) {c : M}
    (hc : c ∈ Subgroup.closure {y : M | y ∈ G ∧ u * y = y * u ∧ Odd (orderOf y)}) :
    ∃ hcG : c ∈ G, (⟨c, hcG⟩ : ↥G) ∈ Subgroup.closure (oddFixed β) := by
  induction hc using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨hyG, hyc, hyo⟩ := hy
    refine ⟨hyG, Subgroup.subset_closure ⟨?_, ?_⟩⟩
    · apply Subtype.ext
      rw [hβ]
      calc u * y * u⁻¹ = y * u * u⁻¹ := by rw [hyc]
        _ = y := by group
    · rw [← Subgroup.orderOf_coe]; exact hyo
  | one => exact ⟨G.one_mem, (Subgroup.closure (oddFixed β)).one_mem⟩
  | mul a b ha hb iha ihb =>
    obtain ⟨haG, ha'⟩ := iha
    obtain ⟨hbG, hb'⟩ := ihb
    exact ⟨G.mul_mem haG hbG, (Subgroup.closure (oddFixed β)).mul_mem ha' hb'⟩
  | inv a ha iha =>
    obtain ⟨haG, ha'⟩ := iha
    exact ⟨G.inv_mem haG, (Subgroup.closure (oddFixed β)).inv_mem ha'⟩

theorem F3.of_F3S {G : Subgroup M} {u : M} {p : ℕ} (β : MulAut ↥G)
    (hβ : ∀ g : ↥G, ((β g : ↥G) : M) = u * g * u⁻¹) (h : F3S G u p) : F3 p β := by
  intro x hxo hxβ hpg
  apply h (x : M) x.2 (by rw [Subgroup.orderOf_coe]; exact hxo)
    (by rw [← hβ, hxβ]; rfl)
  have hle : Subgroup.closure {w : M | ∃ c ∈ Subgroup.closure
      {y : M | y ∈ G ∧ u * y = y * u ∧ Odd (orderOf y)}, w = c * (x : M) * c⁻¹} ≤
      (oddConjClosure β x).map G.subtype := by
    rw [Subgroup.closure_le]
    rintro w ⟨c, hc, rfl⟩
    obtain ⟨hcG, hc'⟩ := mem_closure_oddFixed_subgroup β hβ hc
    refine ⟨⟨c, hcG⟩ * x * ⟨c, hcG⟩⁻¹, Subgroup.subset_closure ⟨⟨c, hcG⟩, hc', rfl⟩, ?_⟩
    simp
  exact (hpg.map G.subtype).to_le hle

theorem F3S.conj {G : Subgroup M} {r : M} {p : ℕ} (h : F3S G r p) {d : M} (hd : d ∈ G) :
    F3S G (d * r * d⁻¹) p := by
  intro x hx hxo hxu hpg
  set x' : M := d⁻¹ * x * d with hx'
  have hx'G : x' ∈ G := G.mul_mem (G.mul_mem (G.inv_mem hd) hx) hd
  have hx'o : orderOf x' = p := by
    have := MulEquiv.orderOf_eq (MulAut.conj d⁻¹) x
    simp only [MulAut.conj_apply, inv_inv] at this
    rw [hx', this, hxo]
  have hx'r : r * x' * r⁻¹ = x'⁻¹ := by
    have h1 : d * r * d⁻¹ * x * (d * r * d⁻¹)⁻¹ = x⁻¹ := hxu
    have h2 : r * x' * r⁻¹ = d⁻¹ * (d * r * d⁻¹ * x * (d * r * d⁻¹)⁻¹) * d := by
      simp only [hx']; group
    rw [h2, h1]
    simp only [hx']; group
  refine h x' hx'G hx'o hx'r ?_
  set N := Subgroup.closure {w : M | ∃ c ∈ Subgroup.closure
      {y : M | y ∈ G ∧ d * r * d⁻¹ * y = y * (d * r * d⁻¹) ∧ Odd (orderOf y)}, w = c * x * c⁻¹}
  have hcl : ∀ c ∈ Subgroup.closure {y : M | y ∈ G ∧ r * y = y * r ∧ Odd (orderOf y)},
      d * c * d⁻¹ ∈ Subgroup.closure
        {y : M | y ∈ G ∧ d * r * d⁻¹ * y = y * (d * r * d⁻¹) ∧ Odd (orderOf y)} := by
    intro c hc
    have hmap : (Subgroup.closure {y : M | y ∈ G ∧ r * y = y * r ∧ Odd (orderOf y)}).map
        (MulAut.conj d).toMonoidHom ≤ Subgroup.closure
        {y : M | y ∈ G ∧ d * r * d⁻¹ * y = y * (d * r * d⁻¹) ∧ Odd (orderOf y)} := by
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨y, ⟨hyG, hyr, hyo⟩, rfl⟩
      refine Subgroup.subset_closure ⟨?_, ?_, ?_⟩
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact G.mul_mem (G.mul_mem hd hyG) (G.inv_mem hd)
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        calc d * r * d⁻¹ * (d * y * d⁻¹) = d * (r * y) * d⁻¹ := by group
          _ = d * (y * r) * d⁻¹ := by rw [hyr]
          _ = d * y * d⁻¹ * (d * r * d⁻¹) := by group
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        have := MulEquiv.orderOf_eq (MulAut.conj d) y
        simp only [MulAut.conj_apply] at this
        rw [this]; exact hyo
    exact hmap ⟨c, hc, rfl⟩
  have hle : Subgroup.closure {w : M | ∃ c ∈ Subgroup.closure
      {y : M | y ∈ G ∧ r * y = y * r ∧ Odd (orderOf y)}, w = c * x' * c⁻¹} ≤
      N.map (MulAut.conj d⁻¹).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro w ⟨c, hc, rfl⟩
    refine ⟨d * c * d⁻¹ * x * (d * c * d⁻¹)⁻¹, Subgroup.subset_closure
      ⟨d * c * d⁻¹, hcl c hc, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hx']
    group
  exact (hpg.map (MulAut.conj d⁻¹).toMonoidHom).to_le hle

theorem F3S.one_elt {G : Subgroup M} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : F3S G 1 p := by
  intro x _ hxo hx
  exfalso
  have h1 : x = x⁻¹ := by simpa using hx
  have h2 : x ^ 2 = 1 := by
    have : x * x = 1 := by
      calc x * x = x * x⁻¹ := by rw [← h1]
        _ = 1 := mul_inv_cancel x
    rwa [← pow_two] at this
  have : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  rw [hxo] at this
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)

end Ambient

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
