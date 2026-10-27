module

public import CFSG.ClassicalInvolution.WeakCT.SignedSL3
public import CFSG.Timmesfeld.RankTwo.SimplyLaced

public section

namespace CFSG.ClassicalInvolution.Balance

open scoped commutatorElement MatrixGroups
open CFSG.Timmesfeld CFSG.Timmesfeld.ARS.FrameSL3 CFSG.ClassicalInvolution.WeakCT

section Hexagon

variable {F : Type} [Field F] {X : Type*} [Group X]

theorem conj_commutatorElement' (g a b : X) :
    ⁅g * a * g⁻¹, g * b * g⁻¹⁆ = g * ⁅a, b⁆ * g⁻¹ := by
  simp only [commutatorElement_def]
  group

theorem hexagon_step {y : Fin 6 → F → X} {g : X} (hrot : ∀ k u, g * y k u * g⁻¹ = y (k + 1) u)
    {M : F} {k : Fin 6} (h1 : ∀ s t, ⁅y k s, y (k + 1) t⁆ = 1)
    (h2 : ∀ s t, ⁅y k s, y (k + 2) t⁆ = y (k + 1) (M * s * t)) :
    (∀ s t, ⁅y (k + 1) s, y (k + 1 + 1) t⁆ = 1) ∧
      ∀ s t, ⁅y (k + 1) s, y (k + 1 + 2) t⁆ = y (k + 1 + 1) (M * s * t) := by
  refine ⟨fun s t => ?_, fun s t => ?_⟩
  · rw [← hrot k s, ← hrot (k + 1) t, conj_commutatorElement', h1 s t]
    simp
  · have e : k + 1 + 2 = k + 2 + 1 := add_right_comm k 1 2
    rw [e, ← hrot k s, ← hrot (k + 2) t, conj_commutatorElement', h2 s t]
    exact hrot _ _

theorem map_neg_of_add' {f : F → X} (hf : ∀ s t, f (s + t) = f s * f t) (s : F) :
    f (-s) = (f s)⁻¹ := map_neg_of_add hf s

theorem hexagon_relations {y : Fin 6 → F → X} {g : X}
    (hrot : ∀ k u, g * y k u * g⁻¹ = y (k + 1) u) {M : F}
    (h1 : ∀ s t, ⁅y 0 s, y 1 t⁆ = 1) (h2 : ∀ s t, ⁅y 0 s, y 2 t⁆ = y 1 (M * s * t)) :
    (∀ s t, ⁅y 0 s, y 1 t⁆ = 1) ∧ (∀ s t, ⁅y 1 s, y 2 t⁆ = 1) ∧ (∀ s t, ⁅y 2 s, y 3 t⁆ = 1) ∧
      (∀ s t, ⁅y 3 s, y 4 t⁆ = 1) ∧ (∀ s t, ⁅y 4 s, y 5 t⁆ = 1) ∧ (∀ s t, ⁅y 5 s, y 0 t⁆ = 1) ∧
      (∀ s t, ⁅y 0 s, y 2 t⁆ = y 1 (M * s * t)) ∧ (∀ s t, ⁅y 1 s, y 3 t⁆ = y 2 (M * s * t)) ∧
      (∀ s t, ⁅y 2 s, y 4 t⁆ = y 3 (M * s * t)) ∧ (∀ s t, ⁅y 3 s, y 5 t⁆ = y 4 (M * s * t)) ∧
      (∀ s t, ⁅y 4 s, y 0 t⁆ = y 5 (M * s * t)) ∧ (∀ s t, ⁅y 5 s, y 1 t⁆ = y 0 (M * s * t)) := by
  obtain ⟨a1, b1⟩ := hexagon_step (k := 0) hrot h1 h2
  obtain ⟨a2, b2⟩ := hexagon_step (k := 1) hrot a1 b1
  obtain ⟨a3, b3⟩ := hexagon_step (k := 2) hrot a2 b2
  obtain ⟨a4, b4⟩ := hexagon_step (k := 3) hrot a3 b3
  obtain ⟨a5, b5⟩ := hexagon_step (k := 4) hrot a4 b4
  exact ⟨h1, a1, a2, a3, a4, a5, h2, b1, b2, b3, b4, b5⟩

theorem exists_sl3_of_exactRotation [Finite F] {y : Fin 6 → F → X} {g : X}
    (hadd : ∀ k s t, y k (s + t) = y k s * y k t)
    (hrot : ∀ k u, g * y k u * g⁻¹ = y (k + 1) u) {M : F} (hM : M * M = 1)
    (h1 : ∀ s t, ⁅y 0 s, y 1 t⁆ = 1) (h2 : ∀ s t, ⁅y 0 s, y 2 t⁆ = y 1 (M * s * t)) :
    ∃ ρ : SL(3, F) →* X, ∀ c, ρ (tv 0 1 c) = y 0 c ∧ ρ (tv 1 2 c) = y 2 c ∧
      ρ (tv 0 2 c) = y 1 (M * c) ∧ ρ (tv 1 0 c) = y 3 (-c) ∧ ρ (tv 2 1 c) = y 5 (-c) ∧
      ρ (tv 2 0 c) = y 4 (-(M * c)) := by
  obtain ⟨A0, A1, A2, A3, A4, A5, B0, B1, B2, B3, B4, B5⟩ := hexagon_relations hrot h1 h2
  have swap : ∀ {i j m : Fin 6}, (∀ s t, ⁅y j s, y i t⁆ = y m (M * s * t)) →
      ∀ s t, ⁅y i s, y j t⁆ = y m (-(M * t * s)) := fun {i j m} h s t => by
    rw [← commutatorElement_inv, h t s, ← map_neg_of_add' (hadd m)]
  have hc : ∀ s t, y 1 (M * (s + t)) = y 1 (M * s) * y 1 (M * t) := fun s t => by
    rw [mul_add]
    exact hadd 1 _ _
  have ha' : ∀ s t, y 3 (-(s + t)) = y 3 (-s) * y 3 (-t) := fun s t => by
    rw [neg_add]
    exact hadd 3 _ _
  have hb' : ∀ s t, y 5 (-(s + t)) = y 5 (-s) * y 5 (-t) := fun s t => by
    rw [neg_add]
    exact hadd 5 _ _
  have hc' : ∀ s t, y 4 (-(M * (s + t))) = y 4 (-(M * s)) * y 4 (-(M * t)) := fun s t => by
    rw [mul_add, neg_add]
    exact hadd 4 _ _
  obtain ⟨ρ, hρ⟩ := ARS.FrameSL3.exists_hom_of_steinberg (G := X)
    (x := fam (y 0) (y 2) (fun s => y 1 (M * s)) (fun s => y 3 (-s)) (fun s => y 5 (-s))
      (fun s => y 4 (-(M * s))))
    (fam_add (hadd 0) (hadd 2) hc ha' hb' hc')
    (fam_comm_signed (hadd 0) (hadd 2) hc ha' hb' hc'
      (fun s t => commutatorElement_eq_one_iff_commute.1 (A0 s _))
      (fun s t => (commutatorElement_eq_one_iff_commute.1 (A5 _ s)).symm)
      (fun s t => (commutatorElement_eq_one_iff_commute.1 (A1 _ s)).symm)
      (fun s t => commutatorElement_eq_one_iff_commute.1 (A2 s _))
      (fun s t => commutatorElement_eq_one_iff_commute.1 (A3 _ _))
      (fun s t => (commutatorElement_eq_one_iff_commute.1 (A4 _ _)).symm)
      (fun s t => by
        show ⁅y 0 s, y 2 t⁆ = y 1 (M * (s * t))
        rw [B0]
        congr 1
        ring)
      (fun s t => by
        show ⁅y 3 (-s), y 1 (M * t)⁆ = y 2 (s * t)
        rw [swap B1]
        congr 1
        linear_combination (s * t) * hM)
      (fun s t => by
        show ⁅y 0 s, y 4 (-(M * t))⁆ = y 5 (-(-(s * t)))
        rw [swap B4]
        congr 1
        linear_combination (s * t) * hM)
      (fun s t => by
        show ⁅y 3 (-s), y 5 (-t)⁆ = y 4 (-(M * -(s * t)))
        rw [B3]
        congr 1
        ring)
      (fun s t => by
        show ⁅y 5 (-s), y 1 (M * t)⁆ = y 0 (-(s * t))
        rw [B5]
        congr 1
        linear_combination (-(s * t)) * hM)
      (fun s t => by
        show ⁅y 2 s, y 4 (-(M * t))⁆ = y 3 (-(s * t))
        rw [B2]
        congr 1
        linear_combination (-(s * t)) * hM))
  refine ⟨ρ, fun c => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [tv_of_ne (by decide), hρ]
    rfl
  · rw [tv_of_ne (by decide), hρ]
    rfl
  · rw [tv_of_ne (by decide), hρ]
    rfl
  · rw [tv_of_ne (by decide), hρ]
    rfl
  · rw [tv_of_ne (by decide), hρ]
    rfl
  · rw [tv_of_ne (by decide), hρ]
    rfl

theorem exists_sl3_of_rotation [Finite F] {x : Fin 6 → F → X}
    (hadd : ∀ k s t, x k (s + t) = x k s * x k t) (hinj : Function.Injective (x 1)) {g : X}
    {κ : Fin 6 → F} (hκ : ∀ k, κ k * κ k = 1)
    (hrot : ∀ k u, g * x k u * g⁻¹ = x (k + 1) (κ k * u)) {N : F} (hN : N * N = 1)
    (h1 : ∀ s t, ⁅x 0 s, x 1 t⁆ = 1) (h2 : ∀ s t, ⁅x 0 s, x 2 t⁆ = x 1 (N * s * t)) :
    ∃ (ρ : SL(3, F) →* X) (l : Fin 6 → F), (∀ k, l k * l k = 1) ∧ ∀ c,
      ρ (tv 0 1 c) = x 0 (l 0 * c) ∧ ρ (tv 1 2 c) = x 2 (l 2 * c) ∧ ρ (tv 0 2 c) = x 1 (l 1 * c) ∧
      ρ (tv 1 0 c) = x 3 (l 3 * c) ∧ ρ (tv 2 1 c) = x 5 (l 5 * c) ∧
      ρ (tv 2 0 c) = x 4 (l 4 * c) := by
  have hr0 : ∀ u, g * x 0 u * g⁻¹ = x 1 (κ 0 * u) := hrot 0
  have hr1 : ∀ u, g * x 1 u * g⁻¹ = x 2 (κ 1 * u) := hrot 1
  have hr2 : ∀ u, g * x 2 u * g⁻¹ = x 3 (κ 2 * u) := hrot 2
  have hr3 : ∀ u, g * x 3 u * g⁻¹ = x 4 (κ 3 * u) := hrot 3
  have hr4 : ∀ u, g * x 4 u * g⁻¹ = x 5 (κ 4 * u) := hrot 4
  have hr5 : ∀ u, g * x 5 u * g⁻¹ = x 0 (κ 5 * u) := hrot 5
  obtain ⟨K, hKdef⟩ : ∃ K : F, K = κ 0 * κ 1 * κ 2 * κ 3 * κ 4 * κ 5 := ⟨_, rfl⟩
  have hKK : K * K = 1 := by
    calc K * K = (κ 0 * κ 0) * (κ 1 * κ 1) * (κ 2 * κ 2) * (κ 3 * κ 3) * (κ 4 * κ 4) *
        (κ 5 * κ 5) := by rw [hKdef]; ring
      _ = 1 := by rw [hκ 0, hκ 1, hκ 2, hκ 3, hκ 4, hκ 5]; norm_num
  have hN0 : N ≠ 0 := fun h => by
    rw [h, mul_zero] at hN
    exact zero_ne_one hN
  obtain ⟨G, hGdef⟩ : ∃ G : X → X, G = fun z =>
      g * (g * (g * (g * (g * (g * z * g⁻¹) * g⁻¹) * g⁻¹) * g⁻¹) * g⁻¹) * g⁻¹ := ⟨_, rfl⟩
  have hGc : ∀ a b : X, ⁅G a, G b⁆ = G ⁅a, b⁆ := fun a b => by
    simp only [hGdef, commutatorElement_def]
    group
  have hG0 : ∀ u, G (x 0 u) = x 0 (K * u) := fun u => by
    rw [hGdef]
    simp only [hr0, hr1, hr2, hr3, hr4, hr5]
    congr 1
    rw [hKdef]
    ring
  have hG1 : ∀ u, G (x 1 u) = x 1 (K * u) := fun u => by
    rw [hGdef]
    simp only [hr1, hr2, hr3, hr4, hr5, hr0]
    congr 1
    rw [hKdef]
    ring
  have hG2 : ∀ u, G (x 2 u) = x 2 (K * u) := fun u => by
    rw [hGdef]
    simp only [hr2, hr3, hr4, hr5, hr0, hr1]
    congr 1
    rw [hKdef]
    ring
  have hK1 : K = 1 := by
    have e2 : ⁅G (x 0 1), G (x 2 1)⁆ = G (x 1 (N * 1 * 1)) := by
      rw [hGc, h2 1 1]
    rw [hG0, hG2, hG1, h2] at e2
    have e3 := hinj e2
    have e4 : (K - 1) * N = 0 := by linear_combination (-1 : F) * e3 + N * hKK
    rcases mul_eq_zero.1 e4 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hN0
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Fin 6 → F, ℓ = ![1, κ 0, κ 1 * κ 0, κ 2 * (κ 1 * κ 0),
      κ 3 * (κ 2 * (κ 1 * κ 0)), κ 4 * (κ 3 * (κ 2 * (κ 1 * κ 0)))] := ⟨_, rfl⟩
  have ℓ0 : ℓ 0 = 1 := by rw [hℓ]; rfl
  have ℓ1 : ℓ 1 = κ 0 := by rw [hℓ]; rfl
  have ℓ2 : ℓ 2 = κ 1 * κ 0 := by rw [hℓ]; rfl
  have ℓ3 : ℓ 3 = κ 2 * (κ 1 * κ 0) := by rw [hℓ]; rfl
  have ℓ4 : ℓ 4 = κ 3 * (κ 2 * (κ 1 * κ 0)) := by rw [hℓ]; rfl
  have ℓ5 : ℓ 5 = κ 4 * (κ 3 * (κ 2 * (κ 1 * κ 0))) := by rw [hℓ]; rfl
  have hℓℓ : ∀ k, ℓ k * ℓ k = 1 := fun k => by
    fin_cases k
    · show ℓ 0 * ℓ 0 = 1
      rw [ℓ0]; norm_num
    · show ℓ 1 * ℓ 1 = 1
      rw [ℓ1, hκ 0]
    · show ℓ 2 * ℓ 2 = 1
      calc _ = (κ 1 * κ 1) * (κ 0 * κ 0) := by rw [ℓ2]; ring
        _ = 1 := by rw [hκ 0, hκ 1]; norm_num
    · show ℓ 3 * ℓ 3 = 1
      calc _ = (κ 2 * κ 2) * (κ 1 * κ 1) * (κ 0 * κ 0) := by rw [ℓ3]; ring
        _ = 1 := by rw [hκ 0, hκ 1, hκ 2]; norm_num
    · show ℓ 4 * ℓ 4 = 1
      calc _ = (κ 3 * κ 3) * (κ 2 * κ 2) * (κ 1 * κ 1) * (κ 0 * κ 0) := by rw [ℓ4]; ring
        _ = 1 := by rw [hκ 0, hκ 1, hκ 2, hκ 3]; norm_num
    · show ℓ 5 * ℓ 5 = 1
      calc _ = (κ 4 * κ 4) * (κ 3 * κ 3) * (κ 2 * κ 2) * (κ 1 * κ 1) * (κ 0 * κ 0) := by
            rw [ℓ5]; ring
        _ = 1 := by rw [hκ 0, hκ 1, hκ 2, hκ 3, hκ 4]; norm_num
  have y0 : ∀ u, g * x 0 (ℓ 0 * u) * g⁻¹ = x 1 (ℓ 1 * u) := fun u => by
    rw [ℓ0, ℓ1, hr0]
    congr 1
    ring
  have y1 : ∀ u, g * x 1 (ℓ 1 * u) * g⁻¹ = x 2 (ℓ 2 * u) := fun u => by
    rw [ℓ1, ℓ2, hr1]
    congr 1
    ring
  have y2 : ∀ u, g * x 2 (ℓ 2 * u) * g⁻¹ = x 3 (ℓ 3 * u) := fun u => by
    rw [ℓ2, ℓ3, hr2]
    congr 1
    ring
  have y3 : ∀ u, g * x 3 (ℓ 3 * u) * g⁻¹ = x 4 (ℓ 4 * u) := fun u => by
    rw [ℓ3, ℓ4, hr3]
    congr 1
    ring
  have y4 : ∀ u, g * x 4 (ℓ 4 * u) * g⁻¹ = x 5 (ℓ 5 * u) := fun u => by
    rw [ℓ4, ℓ5, hr4]
    congr 1
    ring
  have y5 : ∀ u, g * x 5 (ℓ 5 * u) * g⁻¹ = x 0 (ℓ 0 * u) := fun u => by
    rw [ℓ5, ℓ0, hr5]
    congr 1
    have : κ 5 * (κ 4 * (κ 3 * (κ 2 * (κ 1 * κ 0)))) = 1 := by rw [← hK1, hKdef]; ring
    linear_combination u * this
  have hrotY : ∀ (k : Fin 6) u, g * x k (ℓ k * u) * g⁻¹ = x (k + 1) (ℓ (k + 1) * u) := by
    intro k u
    fin_cases k
    exacts [y0 u, y1 u, y2 u, y3 u, y4 u, y5 u]
  have hM : (N * κ 1) * (N * κ 1) = 1 := by
    calc _ = (N * N) * (κ 1 * κ 1) := by ring
      _ = 1 := by rw [hN, hκ 1]; norm_num
  obtain ⟨ρ, hρ⟩ := exists_sl3_of_exactRotation (y := fun k u => x k (ℓ k * u)) (g := g)
    (fun k s t => by rw [mul_add]; exact hadd k _ _) hrotY hM
    (fun s t => h1 _ _)
    (fun s t => by
      show ⁅x 0 (ℓ 0 * s), x 2 (ℓ 2 * t)⁆ = x 1 (ℓ 1 * (N * κ 1 * s * t))
      rw [h2, ℓ0, ℓ1, ℓ2]
      congr 1
      ring)
  refine ⟨ρ, ![ℓ 0, ℓ 1 * (N * κ 1), ℓ 2, -ℓ 3, -(ℓ 4 * (N * κ 1)), -ℓ 5], ?_, fun c => ?_⟩
  · intro k
    fin_cases k
    · exact hℓℓ 0
    · show ℓ 1 * (N * κ 1) * (ℓ 1 * (N * κ 1)) = 1
      calc _ = (ℓ 1 * ℓ 1) * ((N * κ 1) * (N * κ 1)) := by ring
        _ = 1 := by rw [hℓℓ 1, hM]; norm_num
    · exact hℓℓ 2
    · show -ℓ 3 * -ℓ 3 = 1
      rw [neg_mul_neg]; exact hℓℓ 3
    · show -(ℓ 4 * (N * κ 1)) * -(ℓ 4 * (N * κ 1)) = 1
      calc _ = (ℓ 4 * ℓ 4) * ((N * κ 1) * (N * κ 1)) := by ring
        _ = 1 := by rw [hℓℓ 4, hM]; norm_num
    · show -ℓ 5 * -ℓ 5 = 1
      rw [neg_mul_neg]; exact hℓℓ 5
  · obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hρ c
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [e1]
      rfl
    · rw [e2]
      rfl
    · rw [e3]
      show x 1 (ℓ 1 * (N * κ 1 * c)) = x 1 (ℓ 1 * (N * κ 1) * c)
      congr 1
      ring
    · rw [e4]
      show x 3 (ℓ 3 * -c) = x 3 (-ℓ 3 * c)
      congr 1
      ring
    · rw [e5]
      show x 5 (ℓ 5 * -c) = x 5 (-ℓ 5 * c)
      congr 1
      ring
    · rw [e6]
      show x 4 (ℓ 4 * -(N * κ 1 * c)) = x 4 (-(ℓ 4 * (N * κ 1)) * c)
      congr 1
      ring

end Hexagon

end CFSG.ClassicalInvolution.Balance
