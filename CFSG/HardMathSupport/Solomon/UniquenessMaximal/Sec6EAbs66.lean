module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6EAbs66Core

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E

theorem exists_conj_le {G : Type*} [Group G] [Finite G] (W N P : Subgroup G)
    (hPW : P ≤ W) (hP : IsPGroup 3 P) (h5 : N.relIndex W = 5) :
    ∃ w ∈ W, ∀ p ∈ P, w⁻¹ * p * w ∈ N := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let N' : Subgroup W := N.subgroupOf W
  let _ : MulAction P (W ⧸ N') := MulAction.compHom (W ⧸ N') (Subgroup.inclusion hPW)
  have hcard : Nat.card (W ⧸ N') = 5 := by
    rw [← Subgroup.index_eq_card]; exact h5
  obtain ⟨x, hx⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card (W ⧸ N')
    (by rw [hcard]; decide)
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective x
  refine ⟨w, w.2, fun p hp => ?_⟩
  have h1 := MulAction.mem_fixedPoints.1 hx ⟨p⁻¹, P.inv_mem hp⟩
  have h2 : ((Subgroup.inclusion hPW ⟨p⁻¹, P.inv_mem hp⟩ * w : W) : W ⧸ N') = (w : W ⧸ N') := h1
  have h3 := QuotientGroup.eq.1 h2
  have h4 := (Subgroup.mem_subgroupOf).1 h3
  simpa [mul_assoc] using h4

private theorem q8_central_sq : ∀ g : QuaternionGroup 2, (∀ x, x * g = g * x) → g * g = 1 := by
  decide

namespace Datum
variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V] (D : Datum V)

theorem t_mem_T : D.t ∈ D.T :=
  Subgroup.mem_map.2 ⟨⟨D.t, D.t_mem⟩,
    Subgroup.mem_center_iff.2 (fun g => Subtype.ext (D.t_central g.2)), rfl⟩

theorem T_cases {τ : V ≃ₗ[ZMod 3] V} (hτ : τ ∈ D.T) : τ = 1 ∨ τ = D.t := by
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hτ
  let ψ : D.Q ≃* QuaternionGroup 2 := D.planeQ.quat.some
  have hc : ∀ x : QuaternionGroup 2, x * ψ z = ψ z * x := by
    intro x
    have := Subgroup.mem_center_iff.1 hz (ψ.symm x)
    simpa using congrArg ψ this
  have h1 : ψ (z * z) = 1 := by rw [map_mul]; exact q8_central_sq _ hc
  have h2 : z * z = 1 := ψ.injective (by rw [h1, map_one])
  exact D.t_unique _ z.2 (by simpa using congrArg Subtype.val h2)

theorem comm_t_of_normalizes {p : V ≃ₗ[ZMod 3] V} (h : p * D.t * p⁻¹ ∈ D.Q) :
    p * D.t = D.t * p := by
  have hinv : (p * D.t * p⁻¹) * (p * D.t * p⁻¹) = 1 := by
    have : (p * D.t * p⁻¹) * (p * D.t * p⁻¹) = p * (D.t * D.t) * p⁻¹ := by group
    rw [this, D.t_mul_self]; group
  rcases D.t_unique _ h hinv with h1 | h1
  · exact absurd (by simpa using h1) D.t_ne_one
  · calc p * D.t = (p * D.t * p⁻¹) * p := by group
      _ = D.t * p := by rw [h1]

theorem comm_t_of_permutes {g : V ≃ₗ[ZMod 3] V} (hperm : D.PermutesAF g) {n : ℕ}
    (hg : g ^ (3 ^ n) = 1) : g * D.t = D.t * g := by
  rcases hperm with ⟨hA, hF⟩ | ⟨hA, hF⟩
  · have hgA : ∀ a ∈ D.A, g a ∈ D.A := fun a ha => hA ▸ mem_img.2 ⟨a, ha, rfl⟩
    have hgF : ∀ f ∈ D.F, g f ∈ D.F := fun f hf => hF ▸ mem_img.2 ⟨f, hf, rfl⟩
    ext v
    obtain ⟨a, ha, f, hf, rfl⟩ := D.exists_decomp v
    have e1 : (g * D.t) (a + f) = g a - g f := by
      simp only [LinearEquiv.mul_apply]
      rw [D.t_apply ha hf, map_sub]
    have e2 : (D.t * g) (a + f) = g a - g f := by
      simp only [LinearEquiv.mul_apply]
      rw [map_add, D.t_apply (hgA a ha) (hgF f hf)]
    rw [e1, e2]
  · exfalso
    have hgA : ∀ a ∈ D.A, g a ∈ D.F := fun a ha => hA ▸ mem_img.2 ⟨a, ha, rfl⟩
    have hgF : ∀ f ∈ D.F, g f ∈ D.A := fun f hf => hF ▸ mem_img.2 ⟨f, hf, rfl⟩
    have key : ∀ k : ℕ, ∀ f ∈ D.F, (k % 2 = 0 → (g ^ k) f ∈ D.F) ∧ (k % 2 = 1 → (g ^ k) f ∈ D.A) := by
      intro k
      induction k with
      | zero => intro f hf; exact ⟨fun _ => by simpa using hf, fun h => absurd h (by decide)⟩
      | succ k ih =>
        intro f hf
        obtain ⟨ih1, ih2⟩ := ih f hf
        have hs : (g ^ (k + 1)) f = g ((g ^ k) f) := by rw [pow_succ']; rfl
        rw [hs]
        refine ⟨fun h => ?_, fun h => ?_⟩
        · exact hgA _ (ih2 (by omega))
        · exact hgF _ (ih1 (by omega))
    obtain ⟨f, hf, hf0⟩ := D.planeQ.exists_ne_zero
    have hodd : 3 ^ n % 2 = 1 := Nat.odd_iff.1 (Odd.pow (by decide))
    have h1 := (key (3 ^ n) f hf).2 hodd
    rw [hg] at h1
    exact hf0 (D.inter_eq_zero (by simpa using h1) hf)

variable {D}

theorem exists_conj_commute (h65 : D.Lemma65Concl) {P : Subgroup (V ≃ₗ[ZMod 3] V)}
    (hPW : P ≤ D.W) (hP : IsPGroup 3 P) :
    ∃ w ∈ D.W, ∀ p ∈ P, (w⁻¹ * p * w) * D.t = D.t * (w⁻¹ * p * w) := by
  have hpow : ∀ (w p : V ≃ₗ[ZMod 3] V), p ∈ P → ∃ n : ℕ, (w⁻¹ * p * w) ^ (3 ^ n) = 1 := by
    intro w p hp
    obtain ⟨n, hn⟩ := hP ⟨p, hp⟩
    refine ⟨n, ?_⟩
    have : p ^ (3 ^ n) = 1 := congrArg Subtype.val hn
    have hc := conj_pow (a := w⁻¹) (b := p) (i := 3 ^ n)
    rw [inv_inv] at hc
    rw [hc, this]; group
  rcases h65 with hα | ⟨x, hxW, -, -, -, hperm, hcase⟩
  · refine ⟨1, D.W.one_mem, fun p hp => ?_⟩
    have := D.comm_t_of_normalizes (hα p (hPW hp) D.t D.t_mem)
    simpa using this
  · have hex : ∃ w ∈ D.W, ∀ p ∈ P, w⁻¹ * p * w ∈ D.NW (D.Q ⊔ conjSub x D.Q) := by
      rcases hcase with h1 | ⟨h5, -⟩
      · refine ⟨1, D.W.one_mem, fun p hp => ?_⟩
        have : p ∈ D.NW (D.Q ⊔ conjSub x D.Q) := ⟨hPW hp, h1 (hPW hp)⟩
        rwa [inv_one, one_mul, mul_one]
      · have : Finite D.W := inferInstance
        obtain ⟨w, hw, hwp⟩ := exists_conj_le D.W (D.NW (D.Q ⊔ conjSub x D.Q)) P hPW hP h5
        exact ⟨w, hw, hwp⟩
    obtain ⟨w, hw, hwp⟩ := hex
    refine ⟨w, hw, fun p hp => ?_⟩
    obtain ⟨n, hn⟩ := hpow w p hp
    exact D.comm_t_of_permutes (hperm _ (hwp p hp)) hn


theorem mem_conjSub_iff {P : Subgroup (V ≃ₗ[ZMod 3] V)} (w x : V ≃ₗ[ZMod 3] V) :
    x ∈ conjSub w P ↔ w * x * w⁻¹ ∈ P := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro h
    exact ⟨w * x * w⁻¹, h, by simp [mul_assoc]⟩

theorem comm_map {P P' : Subgroup (V ≃ₗ[ZMod 3] V)} (g : V ≃ₗ[ZMod 3] V)
    (h : ∀ x ∈ P', g * x * g⁻¹ ∈ P) {y : V} (hy : y ∈ commSub P') : g y ∈ commSub P := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨x, hx, m, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨g * x * g⁻¹, h x hx, g m, ?_⟩
    simp
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem card_commSub_conj {P : Subgroup (V ≃ₗ[ZMod 3] V)} (w : V ≃ₗ[ZMod 3] V) :
    Nat.card (commSub (conjSub w P)) = Nat.card (commSub P) := by
  symm
  refine Nat.card_congr (Equiv.subtypeEquiv w⁻¹.toEquiv (fun y => ?_))
  constructor
  · intro hy
    have := comm_map (P := conjSub w P) (P' := P) w⁻¹ (fun x hx => by
      rw [mem_conjSub_iff]; convert hx using 1; group) hy
    exact this
  · intro hy
    have := comm_map (P := P) (P' := conjSub w P) w (fun x hx => (mem_conjSub_iff w x).1 hx) hy
    simpa using this

theorem card_fixSub_conj {P : Subgroup (V ≃ₗ[ZMod 3] V)} (w : V ≃ₗ[ZMod 3] V) :
    Nat.card (fixSub (conjSub w P)) = Nat.card (fixSub P) := by
  symm
  refine Nat.card_congr (Equiv.subtypeEquiv w⁻¹.toEquiv (fun y => ?_))
  constructor
  · intro hy x hx
    have hp := (mem_conjSub_iff w x).1 hx
    have := hy _ hp
    simp only [LinearEquiv.mul_apply] at this
    have h2 := congrArg (fun v => w⁻¹ v) this
    simpa using h2
  · intro hy p hp
    have hx : w⁻¹ * p * w ∈ conjSub w P := by
      rw [mem_conjSub_iff]; convert hp using 1; group
    have := hy _ hx
    simp only [LinearEquiv.mul_apply] at this
    have h2 := congrArg (fun v => w v) this
    simpa using h2


theorem card_conjSub {P : Subgroup (V ≃ₗ[ZMod 3] V)} (w : V ≃ₗ[ZMod 3] V) :
    Nat.card (conjSub w P) = Nat.card P :=
  Subgroup.card_map_of_injective (MulAut.conj w⁻¹).injective

variable (D) in
theorem lemma66_abs (h65 : D.Lemma65Concl) (P : Subgroup (V ≃ₗ[ZMod 3] V)) (hPW : P ≤ D.W)
    (hP : IsPGroup 3 P) : D.Lemma66Concl P := by
  obtain ⟨w, hw, hwc⟩ := exists_conj_commute h65 hPW hP
  have hP' : IsPGroup 3 (conjSub w P) := hP.map _
  have hc' : ∀ p ∈ conjSub w P, p * D.t = D.t * p := by
    intro p hp
    have := hwc (w * p * w⁻¹) ((mem_conjSub_iff w p).1 hp)
    simpa [mul_assoc] using this
  obtain ⟨⟨hcard, hexp, hab⟩, hcomm, ⟨hprod, h9⟩, -⟩ := D.core66 hP' hc'
  have hcardP : Nat.card (conjSub w P) = Nat.card P := card_conjSub w
  have hcc : Nat.card (commSub (conjSub w P)) = Nat.card (commSub P) := card_commSub_conj w
  have hfc : Nat.card (fixSub (conjSub w P)) = Nat.card (fixSub P) := card_fixSub_conj w
  refine ⟨⟨w, hw, fun τ hτ p hp => ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ⟨?_, ?_⟩, ?_⟩
  · rcases D.T_cases hτ with rfl | rfl
    · simp
    · exact hwc p hp
  · rw [← hcardP]; exact hcard
  · intro p hp
    have := hexp (w⁻¹ * p * w) ((mem_conjSub_iff w _).2 (by simpa [mul_assoc] using hp))
    have e : (w⁻¹ * p * w) ^ 3 = w⁻¹ * p ^ 3 * w := by
      have hc := conj_pow (a := w⁻¹) (b := p) (i := 3)
      rwa [inv_inv] at hc
    rw [e] at this
    have : p ^ 3 = w * 1 * w⁻¹ := by
      rw [← this]; group
    simpa using this
  · intro p hp p' hp'
    have := hab (w⁻¹ * p * w) ((mem_conjSub_iff w _).2 (by simpa [mul_assoc] using hp))
      (w⁻¹ * p' * w) ((mem_conjSub_iff w _).2 (by simpa [mul_assoc] using hp'))
    have e : p * p' = w * ((w⁻¹ * p * w) * (w⁻¹ * p' * w)) * w⁻¹ := by group
    have e' : p' * p = w * ((w⁻¹ * p' * w) * (w⁻¹ * p * w)) * w⁻¹ := by group
    rw [e, e', this]
  · intro y hy p hp
    have hy' : w⁻¹ y ∈ commSub (conjSub w P) := by
      have := comm_map (P := conjSub w P) (P' := P) w⁻¹ (fun x hx => by
        rw [mem_conjSub_iff]; convert hx using 1; group) hy
      exact this
    have hx : w⁻¹ * p * w ∈ conjSub w P := (mem_conjSub_iff w _).2 (by simpa [mul_assoc] using hp)
    have := hcomm _ hy' _ hx
    have h2 := congrArg (fun v => w v) this
    simpa [LinearEquiv.mul_apply] using h2
  · have hmul := AddSubgroup.index_mul_card (fixSub P)
    rw [D.card_V] at hmul
    have hpos : 0 < Nat.card (fixSub P) := Nat.card_pos
    rw [hcc, hfc] at hprod
    exact Nat.eq_of_mul_eq_mul_right hpos (hmul.trans hprod.symm)
  · intro h
    rw [← hcc]; exact h9 (hcardP.trans h)
  · intro hT h3
    have hc : ∀ p ∈ P, p * D.t = D.t * p := fun p hp => hT D.t D.t_mem_T p hp
    exact (D.core66 hP hc).2.2.2 h3

end Datum
end CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E
