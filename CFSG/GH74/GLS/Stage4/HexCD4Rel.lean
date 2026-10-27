module

public import CFSG.GH74.GLS.Stage4.HexCD4Alg3
public import CFSG.GH74.GLS.Stage4.HexCD4Data
public import CFSG.GH74.GLS.Stage4.HexCMu
public import CFSG.GH74.GLS.Stage4.HexCoordD4

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.Timmesfeld.RankTwo CFSG.LieType.Steinberg.TwistedD4
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

variable {G : Type} [Group G] {H : Subgroup G} {r₁ r₂ : G} {U : Subgroup G}
  {root : ℤ → Subgroup G} {F K : Type} [Field F] [Field K]

namespace GalData

variable (Gl : GalData F K)

theorem fixed_mem (d : ↥(fixedField Gl.σ)) : Gl.σ (d : K) = d := mem_fixedField_iff.1 d.2

noncomputable def ι (d : ↥(fixedField Gl.σ)) : F := Classical.choose (Gl.fixed_eq (Gl.fixed_mem d))

theorem θ_ι (d : ↥(fixedField Gl.σ)) : Gl.θ (Gl.ι d) = (d : K) :=
  Classical.choose_spec (Gl.fixed_eq (Gl.fixed_mem d))

theorem θ_mem (c : F) : Gl.θ c ∈ fixedField Gl.σ := mem_fixedField_iff.2 (Gl.σ_θ c)

theorem ι_inj : Function.Injective Gl.ι := fun d d' h =>
  Subtype.ext (by rw [← Gl.θ_ι d, ← Gl.θ_ι d', h])

theorem ι_θ (c : F) (h : Gl.θ c ∈ fixedField Gl.σ) : Gl.ι ⟨Gl.θ c, h⟩ = c :=
  Gl.θ.injective (by rw [Gl.θ_ι])

theorem ι_add (d d' : ↥(fixedField Gl.σ)) : Gl.ι (d + d') = Gl.ι d + Gl.ι d' :=
  Gl.θ.injective (by rw [map_add, Gl.θ_ι, Gl.θ_ι, Gl.θ_ι]; rfl)

theorem ι_mul (d d' : ↥(fixedField Gl.σ)) : Gl.ι (d * d') = Gl.ι d * Gl.ι d' :=
  Gl.θ.injective (by rw [map_mul, Gl.θ_ι, Gl.θ_ι, Gl.θ_ι]; rfl)

theorem ι_neg (d : ↥(fixedField Gl.σ)) : Gl.ι (-d) = -Gl.ι d :=
  Gl.θ.injective (by rw [map_neg, Gl.θ_ι, Gl.θ_ι]; rfl)

theorem ι_tr (x : K) : Gl.ι (d43Tr Gl.σ3 x) = Gl.trF x :=
  Gl.θ.injective (by rw [Gl.θ_ι, Gl.θ_trF]; rfl)

theorem ι_norm (x : K) : Gl.ι (d43Norm Gl.σ3 x) = Gl.Nm x :=
  Gl.θ.injective (by rw [Gl.θ_ι, Gl.θ_Nm]; rfl)

end GalData

theorem inv_of_add4 {A : Type} [Field A] {f : A → G} (h : ∀ c d, f (c + d) = f c * f d) (c : A) :
    (f c)⁻¹ = f (-c) := by
  have h0 : f 0 = 1 := map_zero_of_add' h
  have := h c (-c)
  rw [add_neg_cancel, h0] at this
  exact inv_eq_of_mul_eq_one_right this.symm

section Reorder

variable (hC : Hex6Comm root) (D : HexData4 root F K) (Gl : GalData F K) {p3 : K → G}
  (hp3mem : ∀ a, p3 a ∈ root 3) (hp3add : ∀ a b, p3 (a + b) = p3 a * p3 b)
  (hr5 : ∀ t a, ⁅D.p5 t, p3 a⁆ = D.p4 (Gl.trF (a * t)))

include hC hp3mem hp3add hr5 in
theorem inv_reorder4 (a c : F) (b d : K) :
    (D.p2 a * p3 b * D.p4 c * D.p5 d)⁻¹ =
      D.p2 (-a) * p3 (-b) * D.p4 (-c + Gl.trF (b * d)) * D.p5 (-d) := by
  have i2 := inv_of_add4 D.p2_add
  have i4 := inv_of_add4 D.p4_add
  have i5 := inv_of_add4 D.p5_add
  have i3 := inv_of_add4 hp3add
  have k34 : ∀ x y, D.p4 x * p3 y = p3 y * D.p4 x := fun x y =>
    (hC.c34 _ (hp3mem y) _ (D.p4_mem x)).symm
  have k24 : ∀ x y, D.p4 x * D.p2 y = D.p2 y * D.p4 x := fun x y =>
    (hC.l24 _ (D.p2_mem y) _ (D.p4_mem x)).symm
  have k23 : ∀ x y, p3 x * D.p2 y = D.p2 y * p3 x := fun x y =>
    (hC.c23 _ (D.p2_mem y) _ (hp3mem x)).symm
  have c45 : D.p5 (-d) * D.p4 (-c) = D.p4 (-c) * D.p5 (-d) :=
    (hC.c45 _ (D.p4_mem _) _ (D.p5_mem _)).symm
  have c25 : D.p5 (-d) * D.p2 (-a) = D.p2 (-a) * D.p5 (-d) :=
    (hC.o25 _ (D.p2_mem _) _ (D.p5_mem _)).symm
  have cc : D.p5 (-d) * p3 (-b) = D.p4 (Gl.trF (b * d)) * p3 (-b) * D.p5 (-d) := by
    have := hr5 (-d) (-b)
    rw [neg_mul_neg] at this
    rw [← this]; simp only [commutatorElement_def]; group
  rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, i2, i4, i5, i3]
  calc D.p5 (-d) * (D.p4 (-c) * (p3 (-b) * D.p2 (-a)))
      = (D.p5 (-d) * D.p4 (-c)) * (p3 (-b) * D.p2 (-a)) := by rw [← mul_assoc]
    _ = (D.p4 (-c) * D.p5 (-d)) * (p3 (-b) * D.p2 (-a)) := by rw [c45]
    _ = D.p4 (-c) * ((D.p5 (-d) * p3 (-b)) * D.p2 (-a)) := by simp only [mul_assoc]
    _ = D.p4 (-c) * ((D.p4 (Gl.trF (b * d)) * p3 (-b) * D.p5 (-d)) * D.p2 (-a)) := by rw [cc]
    _ = D.p4 (-c) * (D.p4 (Gl.trF (b * d)) * p3 (-b) * (D.p5 (-d) * D.p2 (-a))) := by
        simp only [mul_assoc]
    _ = D.p4 (-c) * (D.p4 (Gl.trF (b * d)) * p3 (-b) * (D.p2 (-a) * D.p5 (-d))) := by rw [c25]
    _ = (D.p4 (-c) * D.p4 (Gl.trF (b * d))) * p3 (-b) * D.p2 (-a) * D.p5 (-d) := by
        simp only [mul_assoc]
    _ = D.p4 (-c + Gl.trF (b * d)) * p3 (-b) * D.p2 (-a) * D.p5 (-d) := by rw [← D.p4_add]
    _ = (p3 (-b) * D.p4 (-c + Gl.trF (b * d))) * D.p2 (-a) * D.p5 (-d) := by rw [k34]
    _ = p3 (-b) * (D.p4 (-c + Gl.trF (b * d)) * D.p2 (-a)) * D.p5 (-d) := by simp only [mul_assoc]
    _ = p3 (-b) * (D.p2 (-a) * D.p4 (-c + Gl.trF (b * d))) * D.p5 (-d) := by rw [k24]
    _ = (p3 (-b) * D.p2 (-a)) * D.p4 (-c + Gl.trF (b * d)) * D.p5 (-d) := by simp only [mul_assoc]
    _ = D.p2 (-a) * p3 (-b) * D.p4 (-c + Gl.trF (b * d)) * D.p5 (-d) := by rw [k23]

end Reorder

@[expose] noncomputable def d4ψ (D : HexData4 root F K) (Gl : GalData F K) (k : F) (p3 : K → G) :
    ∀ i : Fin 6, d43Par Gl.σ i → G
  | 0 => D.p1
  | 1 => fun d : ↥(fixedField Gl.σ) => D.p2 (-k * Gl.ι d)
  | 2 => fun v : K => p3 (-(Gl.θ k) * v)
  | 3 => fun w : ↥(fixedField Gl.σ) => D.p4 (-k * Gl.ι w)
  | 4 => D.p5
  | 5 => fun w : ↥(fixedField Gl.σ) => D.p6 (Gl.ι w)

section Rel

variable (hC : Hex6Comm root) (D : HexData4 root F K) (Gl : GalData F K) {p3 : K → G}
  (hp3add : ∀ a b, p3 (a + b) = p3 a * p3 b) (hp3mem : ∀ a, p3 a ∈ root 3)
  (hr1 : ∀ s a, ⁅D.p1 s, p3 a⁆ = D.p2 (Gl.trF (a * s)))
  (hr5 : ∀ t a, ⁅D.p5 t, p3 a⁆ = D.p4 (Gl.trF (a * t))) (k : F)
  (hc15 : ∀ s t, ⁅D.p1 s, D.p5 t⁆ = D.p2 (k * Gl.trF (Gl.sharp s * t)) *
    p3 (Gl.θ k * Gl.cross s t) * D.p4 (k * Gl.trF (s * Gl.sharp t)))
  (hAct : ∀ c s, ⁅D.p6 c, D.p1 s⁆ = D.p2 (c * (k * Gl.Nm s)) *
    p3 (Gl.θ c * (Gl.θ k * Gl.sharp s)) * D.p4 (2 * k * c ^ 2 * Gl.Nm s) * D.p5 (Gl.θ c * s))

include hC hp3add hp3mem hr1 hr5 hc15 hAct in
theorem d4Rel_of_data :
    D4Rel Gl.σ3 (fun g : Σ i, d43Par Gl.σ i => d4ψ D Gl k p3 g.1 g.2) where
  add i c d := by
    have h1 : ∀ d d' : ↥(fixedField Gl.σ),
        D.p2 (-k * Gl.ι (d + d')) = D.p2 (-k * Gl.ι d) * D.p2 (-k * Gl.ι d') := fun d d' => by
      rw [Gl.ι_add, mul_add, D.p2_add]
    have h2 : ∀ a b : K, p3 (-(Gl.θ k) * (a + b)) = p3 (-(Gl.θ k) * a) * p3 (-(Gl.θ k) * b) :=
      fun a b => by rw [mul_add, hp3add]
    have h3 : ∀ d d' : ↥(fixedField Gl.σ),
        D.p4 (-k * Gl.ι (d + d')) = D.p4 (-k * Gl.ι d) * D.p4 (-k * Gl.ι d') := fun d d' => by
      rw [Gl.ι_add, mul_add, D.p4_add]
    have h5 : ∀ d d' : ↥(fixedField Gl.σ),
        D.p6 (Gl.ι (d + d')) = D.p6 (Gl.ι d) * D.p6 (Gl.ι d') := fun d d' => by
      rw [Gl.ι_add, D.p6_add]
    fin_cases i
    · exact D.p1_add c d
    · exact h1 c d
    · exact h2 c d
    · exact h3 c d
    · exact D.p5_add c d
    · exact h5 c d
  r02 s t := by
    show ⁅D.p1 s, p3 (-(Gl.θ k) * t)⁆ = D.p2 (-k * Gl.ι (d43Tr Gl.σ3 (s * t)))
    rw [hr1, Gl.ι_tr]
    congr 1
    rw [show -(Gl.θ k) * t * s = Gl.θ (-k) * (s * t) by simp only [map_neg]; ring, Gl.trF_smul]
  r24 s t := by
    show ⁅p3 (-(Gl.θ k) * s), D.p5 t⁆ = D.p4 (-k * Gl.ι (-(d43Tr Gl.σ3 (s * t))))
    rw [← commutatorElement_inv, hr5, inv_of_add4 D.p4_add, Gl.ι_neg, Gl.ι_tr]
    congr 1
    rw [show -(Gl.θ k) * s * t = Gl.θ (-k) * (s * t) by simp only [map_neg]; ring, Gl.trF_smul]
    ring
  r15 s t := by
    show ⁅D.p2 (-k * Gl.ι s), D.p6 (Gl.ι t)⁆ = D.p4 (-k * Gl.ι (-(s * t)))
    rw [← commutatorElement_inv, D.rel_long, inv_of_add4 D.p4_add, Gl.ι_neg, Gl.ι_mul]
    congr 1; ring
  r04 s t := by
    show ⁅D.p1 s, D.p5 t⁆ = D.p2 (-k * Gl.ι (-d43Tr Gl.σ3 (d43Sharp Gl.σ s * t))) *
      p3 (-(Gl.θ k) * -(d43Cross Gl.σ s t : K)) *
        D.p4 (-k * Gl.ι (-d43Tr Gl.σ3 (s * d43Sharp Gl.σ t)))
    rw [hc15, Gl.ι_neg, Gl.ι_tr, Gl.ι_neg, Gl.ι_tr]
    simp only [neg_mul_neg]
    rfl
  r05 s t := by
    show ⁅D.p1 s, D.p6 (Gl.ι t)⁆ = D.p2 (-k * Gl.ι (t * d43Norm Gl.σ3 s)) *
      p3 (-(Gl.θ k) * ((t : K) * d43Sharp Gl.σ s)) *
        D.p4 (-k * Gl.ι (-(t ^ 2 * d43Norm Gl.σ3 s))) * D.p5 (-((t : K) * s))
    rw [← commutatorElement_inv, hAct, inv_reorder4 hC D Gl hp3mem hp3add hr5, Gl.ι_neg,
      pow_two t, Gl.ι_mul, Gl.ι_mul, Gl.ι_mul, Gl.ι_norm, ← Gl.θ_ι t]
    have e4 : Gl.trF (Gl.θ (Gl.ι t) * (Gl.θ k * Gl.sharp s) * (Gl.θ (Gl.ι t) * s)) =
        Gl.ι t * Gl.ι t * k * (3 * Gl.Nm s) := by
      rw [show Gl.θ (Gl.ι t) * (Gl.θ k * Gl.sharp s) * (Gl.θ (Gl.ι t) * s) =
        Gl.θ (Gl.ι t * Gl.ι t * k) * (Gl.sharp s * s) by simp only [map_mul]; ring,
        Gl.trF_smul, Gl.trF_sharp_self]
    rw [e4]
    have eA : -(Gl.ι t * (k * Gl.Nm s)) = -k * (Gl.ι t * Gl.Nm s) := by ring
    have eB : -(Gl.θ (Gl.ι t) * (Gl.θ k * Gl.sharp s)) =
        -(Gl.θ k) * (Gl.θ (Gl.ι t) * Gl.sharp s) := by ring
    have eC : -(2 * k * Gl.ι t ^ 2 * Gl.Nm s) + Gl.ι t * Gl.ι t * k * (3 * Gl.Nm s) =
        -k * -(Gl.ι t * Gl.ι t * Gl.Nm s) := by ring
    rw [eA, eB, eC]
    rfl
  c01 s t := hC.c12 _ (D.p1_mem _) _ (D.p2_mem _)
  c03 s t := hC.o14 _ (D.p1_mem _) _ (D.p4_mem _)
  c12 s t := hC.c23 _ (D.p2_mem _) _ (hp3mem _)
  c13 s t := hC.l24 _ (D.p2_mem _) _ (D.p4_mem _)
  c14 s t := hC.o25 _ (D.p2_mem _) _ (D.p5_mem _)
  c23 s t := hC.c34 _ (hp3mem _) _ (D.p4_mem _)
  c25 s t := hC.o36 _ (hp3mem _) _ (D.p6_mem _)
  c34 s t := hC.c45 _ (D.p4_mem _) _ (D.p5_mem _)
  c35 s t := hC.l46 _ (D.p4_mem _) _ (D.p6_mem _)
  c45 s t := hC.c56 _ (D.p5_mem _) _ (D.p6_mem _)

section Coords

include hC hp3add hp3mem hr1 hr5 hc15 hAct in
theorem d4Coords_of_data [IsSimpleGroup G] (R : RGD2 6 H r₁ r₂ U root)
    (hgen : (H ⊔ U) ⊔ R.N = ⊤) (hp3inj : Function.Injective p3)
    (hp3surj : ∀ u ∈ root 3, ∃ a, p3 a = u) (hk : k ≠ 0) :
    D4Coords (R.toPre hgen).toSystemOfSimple Gl.σ3 (d4ψ D Gl k p3) where
  rel := d4Rel_of_data hC D Gl hp3add hp3mem hr1 hr5 k hc15 hAct
  mem i c := by
    fin_cases i
    · exact D.p1_mem c
    · exact D.p2_mem _
    · exact hp3mem _
    · exact D.p4_mem _
    · exact D.p5_mem c
    · exact D.p6_mem _
  inj i := by
    have hn : -k ≠ 0 := neg_ne_zero.2 hk
    have hn3 : -(Gl.θ k) ≠ 0 := neg_ne_zero.2 ((map_ne_zero Gl.θ).2 hk)
    fin_cases i
    · exact D.p1_inj
    · intro a b hab
      exact Gl.ι_inj (mul_left_cancel₀ hn (D.p2_inj hab))
    · intro (a : K) (b : K) hab
      have h := mul_left_cancel₀ hn3 (hp3inj hab)
      exact h
    · intro a b hab
      exact Gl.ι_inj (mul_left_cancel₀ hn (D.p4_inj hab))
    · exact D.p5_inj
    · intro a b hab
      exact Gl.ι_inj (D.p6_inj hab)
  surj i y hy := by
    have hn : -k ≠ 0 := neg_ne_zero.2 hk
    have hθk : Gl.θ k ≠ 0 := (map_ne_zero Gl.θ).2 hk
    have hn3 : -(Gl.θ k) ≠ 0 := neg_ne_zero.2 hθk
    fin_cases i
    · exact D.p1_surj y hy
    · obtain ⟨d, hd⟩ := D.p2_surj y hy
      refine ⟨⟨Gl.θ (d / -k), Gl.θ_mem _⟩, ?_⟩
      show D.p2 (-k * Gl.ι ⟨Gl.θ (d / -k), Gl.θ_mem _⟩) = y
      rw [Gl.ι_θ, show -k * (d / -k) = d by field_simp]; exact hd
    · obtain ⟨a, ha⟩ := hp3surj y hy
      refine ⟨a / -(Gl.θ k), ?_⟩
      show p3 (-(Gl.θ k) * (a / -(Gl.θ k))) = y
      rw [show -(Gl.θ k) * (a / -(Gl.θ k)) = a by field_simp]; exact ha
    · obtain ⟨d, hd⟩ := D.p4_surj y hy
      refine ⟨⟨Gl.θ (d / -k), Gl.θ_mem _⟩, ?_⟩
      show D.p4 (-k * Gl.ι ⟨Gl.θ (d / -k), Gl.θ_mem _⟩) = y
      rw [Gl.ι_θ, show -k * (d / -k) = d by field_simp]; exact hd
    · exact D.p5_surj y hy
    · obtain ⟨d, hd⟩ := D.p6_surj y hy
      refine ⟨⟨Gl.θ d, Gl.θ_mem d⟩, ?_⟩
      show D.p6 (Gl.ι ⟨Gl.θ d, Gl.θ_mem d⟩) = y
      rw [Gl.ι_θ]; exact hd

end Coords

end Rel

end CFSG.GH74.GLS.Stage4.Hex
