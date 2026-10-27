module

public import CFSG.GH74.GLS.Stage4.HexCLocal
public import CFSG.GH74.GLS.Stage4.HexCShort3

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

section Scalar

variable {F : Type*} [Field F] {G : Type*} [Group G] {φ : SL2 F →* G} {A B : Subgroup G}
  (h : NatPair φ A B)

include h in
theorem NatPair.exists_coordsK {F' : Type*} [Field F'] [Finite F'] (xB : F' → G)
    (hadd : ∀ y y', xB (y + y') = xB y * xB y') (hinj : Function.Injective xB)
    (hmem : ∀ y, xB y ∈ B) (a : Fˣ → F')
    (ha : ∀ (t : Fˣ) (y : F'), φ (sl2D t) * xB y * (φ (sl2D t))⁻¹ = xB (a t * y))
    (hcardA : Nat.card A = Nat.card F') :
    ∃ (θ : F →+* F') (x₄ : F' → G), (∀ s s', x₄ (s + s') = x₄ s * x₄ s') ∧
      Function.Injective x₄ ∧ (∀ s, x₄ s ∈ A) ∧ (∀ b ∈ A, ∃ s, x₄ s = b) ∧
      (∀ c s, ⁅φ (sl2U c), xB s⁆ = x₄ (θ c * s)) ∧
      (∀ (t : Fˣ) s, φ (sl2D t) * xB s * (φ (sl2D t))⁻¹ = xB ((θ (t : F))⁻¹ * s)) ∧
      (∀ (t : Fˣ) s, φ (sl2D t) * x₄ s * (φ (sl2D t))⁻¹ = x₄ (θ (t : F) * s)) := by
  classical
  obtain ⟨θ, hform, hwt⟩ := h.exists_ringHom xB hadd hinj hmem a ha
  have hinjc := h.comm_inj xB hadd hinj hmem
  have hx4mem : ∀ u : F', ⁅φ (sl2U 1), xB u⁆ ∈ A := fun u => by
    simpa [commutatorElement_def] using h.uB 1 _ (hmem u)
  have hx4add : ∀ u u' : F', ⁅φ (sl2U 1), xB (u + u')⁆ =
      ⁅φ (sl2U 1), xB u⁆ * ⁅φ (sl2U 1), xB u'⁆ := by
    intro u u'
    rw [hadd]
    exact h.comm_mul_right 1 (hmem _) (hmem _)
  have hx4inj : Function.Injective fun u : F' => ⁅φ (sl2U 1), xB u⁆ := fun u u' hu =>
    hinjc _ _ hu
  have hAfin : Finite A := Nat.finite_of_card_ne_zero (by rw [hcardA]; exact Nat.card_pos.ne')
  refine ⟨θ, fun u => ⁅φ (sl2U 1), xB u⁆, hx4add, hx4inj, hx4mem, ?_, hform, hwt, ?_⟩
  · intro b hb
    let g : F' → A := fun u => ⟨⁅φ (sl2U 1), xB u⁆, hx4mem u⟩
    have hg : Function.Injective g := fun u u' hu => hx4inj (congrArg Subtype.val hu)
    have hgb : Function.Bijective g := hg.bijective_of_nat_card_le hcardA.le
    obtain ⟨u, hu⟩ := hgb.2 ⟨b, hb⟩
    exact ⟨u, congrArg Subtype.val hu⟩
  · intro t d
    have e1 : φ (sl2D t) * φ (sl2U 1) * (φ (sl2D t))⁻¹ = φ (sl2U ((t : F) ^ 2 * 1)) := by
      rw [mul_inv_eq_iff_eq_mul, ← map_mul, ← map_mul, sl2D_mul_sl2U_eq]
    have e2 := hwt t d
    have ht : θ (t : F) ≠ 0 := (map_ne_zero θ).2 t.ne_zero
    have e3 : ⁅φ (sl2U ((t : F) ^ 2)), xB ((θ (t : F))⁻¹ * d)⁆ = ⁅φ (sl2U 1), xB (θ t * d)⁆ := by
      have e4 : θ ((t : F) ^ 2) * ((θ (t : F))⁻¹ * d) = θ (t : F) * d := by
        rw [map_pow]; field_simp
      rw [hform, e4]
    calc φ (sl2D t) * ⁅φ (sl2U 1), xB d⁆ * (φ (sl2D t))⁻¹
        = ⁅φ (sl2D t) * φ (sl2U 1) * (φ (sl2D t))⁻¹,
            φ (sl2D t) * xB d * (φ (sl2D t))⁻¹⁆ := by
          simp only [commutatorElement_def]; group
      _ = ⁅φ (sl2U ((t : F) ^ 2)), xB ((θ (t : F))⁻¹ * d)⁆ := by
          rw [e1, e2, mul_one]
      _ = _ := e3

end Scalar

section NatQuotK

variable {F : Type*} [Field F] {G : Type*} [Group G] {φ : SL2 F →* G} {Q N A B : Subgroup G}
  (h : NatQuot φ Q N A B)

include h in
theorem NatQuot.exists_coordsK {F' : Type*} [Field F'] [Finite F'] (xB : F' → G)
    (hadd : ∀ y y', xB (y + y') = xB y * xB y') (hinj : Function.Injective xB)
    (hmem : ∀ y, xB y ∈ B) (a : Fˣ → F')
    (ha : ∀ (t : Fˣ) (y : F'), φ (sl2D t) * xB y * (φ (sl2D t))⁻¹ = xB (a t * y))
    (hcardA : Nat.card A = Nat.card F') (hBN : ∀ x ∈ B, x ∈ N → x = 1)
    (hAN : ∀ x ∈ A, x ∈ N → x = 1)
    (hDA : ∀ (t : Fˣ), ∀ x ∈ A, φ (sl2D t) * x * (φ (sl2D t))⁻¹ ∈ A) :
    ∃ (θ : F →+* F') (x₄ : F' → G), (∀ s s', x₄ (s + s') = x₄ s * x₄ s') ∧
      Function.Injective x₄ ∧ (∀ s, x₄ s ∈ A) ∧ (∀ b ∈ A, ∃ s, x₄ s = b) ∧
      (∀ c s, (x₄ (θ c * s))⁻¹ * ⁅φ (sl2U c), xB s⁆ ∈ N) ∧
      (∀ (t : Fˣ) s, φ (sl2D t) * xB s * (φ (sl2D t))⁻¹ = xB ((θ (t : F))⁻¹ * s)) ∧
      (∀ (t : Fˣ) s, φ (sl2D t) * x₄ s * (φ (sl2D t))⁻¹ = x₄ (θ (t : F) * s)) := by
  classical
  have hBT : ∀ x ∈ B, x ∈ Q ⊔ φ.range := fun x hx => Subgroup.mem_sup_left (h.B_le hx)
  have hAT : ∀ x ∈ A, x ∈ Q ⊔ φ.range := fun x hx => Subgroup.mem_sup_left (h.A_le hx)
  let xB' : F' → h.Gq := fun y => h.π ⟨xB y, hBT _ (hmem y)⟩
  have hadd' : ∀ y y', xB' (y + y') = xB' y * xB' y' := by
    intro y y'
    show h.π _ = h.π _ * h.π _
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    simp [hadd]
  have hinj' : Function.Injective xB' := by
    intro y y' hy
    exact hinj (h.eq_of_π_eq_of_mem hBN (hmem y) (hmem y') hy)
  have hmem' : ∀ y, xB' y ∈ h.Bq := fun y => (NatQuot.mem_Bq h).2 ⟨_, hmem y, rfl⟩
  have ha' : ∀ (t : Fˣ) (y : F'), h.φq (sl2D t) * xB' y * (h.φq (sl2D t))⁻¹ = xB' (a t * y) := by
    intro t y
    show h.φq (sl2D t) * h.π _ * (h.φq (sl2D t))⁻¹ = h.π _
    rw [NatQuot.φq_apply, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simpa using ha t y
  have hπA : ∀ {y y' : ↥(Q ⊔ φ.range)}, (y : G) ∈ A → (y' : G) ∈ A → h.π y = h.π y' →
      (y : G) = y' := fun hy hy' he => h.eq_of_π_eq_of_mem hAN hy hy' he
  have hπB : ∀ {y y' : ↥(Q ⊔ φ.range)}, (y : G) ∈ B → (y' : G) ∈ B → h.π y = h.π y' →
      (y : G) = y' := fun hy hy' he => h.eq_of_π_eq_of_mem hBN hy hy' he
  have hcardA' : Nat.card h.Aq = Nat.card F' := by
    rw [← hcardA]
    symm
    refine Nat.card_congr (Equiv.ofBijective
      (fun x : ↥A => (⟨h.π ⟨x, hAT _ x.2⟩, (NatQuot.mem_Aq h).2 ⟨_, x.2, rfl⟩⟩ : ↥h.Aq)) ⟨?_, ?_⟩)
    · intro x x' hx
      have := hπA (y := ⟨x, hAT _ x.2⟩) (y' := ⟨x', hAT _ x'.2⟩) x.2 x'.2
        (congrArg Subtype.val hx)
      exact Subtype.ext this
    · rintro ⟨b, hb⟩
      obtain ⟨z, hz, rfl⟩ := (NatQuot.mem_Aq h).1 hb
      exact ⟨⟨z, hz⟩, Subtype.ext rfl⟩
  obtain ⟨θ, x₄', h4add, h4inj, h4mem, h4surj, hrel, hw2, hw4⟩ :=
    h.natPair.exists_coordsK xB' hadd' hinj' hmem' a ha' hcardA'
  have hl4 : ∀ d, ∃ z : ↥(Q ⊔ φ.range), (z : G) ∈ A ∧ h.π z = x₄' d := fun d =>
    (NatQuot.mem_Aq h).1 (h4mem d)
  choose z₄ hz₄A hz₄π using hl4
  have hDmem : ∀ (t : Fˣ), φ (sl2D t) ∈ Q ⊔ φ.range := fun t =>
    Subgroup.mem_sup_right ⟨sl2D t, rfl⟩
  refine ⟨θ, fun s => (z₄ s : G), ?_, ?_, hz₄A, ?_, ?_, ?_, ?_⟩
  · intro s s'
    have : h.π (z₄ (s + s')) = h.π (z₄ s * z₄ s') := by
      rw [map_mul, hz₄π, hz₄π, hz₄π, h4add]
    exact hπA (hz₄A _) (A.mul_mem (hz₄A _) (hz₄A _)) this
  · intro s s' hss
    apply h4inj
    rw [← hz₄π, ← hz₄π, Subtype.ext hss]
  · intro b hb
    obtain ⟨d, hd⟩ := h4surj (h.π ⟨b, hAT _ hb⟩) ((NatQuot.mem_Aq h).2 ⟨_, hb, rfl⟩)
    have hd' : h.π (z₄ d) = h.π ⟨b, hAT _ hb⟩ := by rw [hz₄π, hd]
    exact ⟨d, hπA (y' := ⟨b, hAT _ hb⟩) (hz₄A d) hb hd'⟩
  · intro c s
    have h1 := hrel c s
    rw [← hz₄π, NatQuot.φq_apply, show xB' s = h.π ⟨xB s, hBT _ (hmem s)⟩ from rfl,
      ← map_commutatorElement] at h1
    exact (h.π_eq_iff _ _).1 h1.symm
  · intro t s
    have h1 := hw2 t s
    rw [show xB' s = h.π ⟨xB s, hBT _ (hmem s)⟩ from rfl,
      show xB' ((θ (t : F))⁻¹ * s) = h.π ⟨xB ((θ (t : F))⁻¹ * s), hBT _ (hmem _)⟩ from rfl,
      NatQuot.φq_apply, ← map_inv, ← map_mul, ← map_mul] at h1
    refine hπB ?_ ?_ h1
    · show φ (sl2D t) * xB s * (φ (sl2D t))⁻¹ ∈ B
      rw [ha t s]; exact hmem _
    · exact hmem _
  · intro t s
    have h1 := hw4 t s
    rw [← hz₄π, ← hz₄π, NatQuot.φq_apply, ← map_inv, ← map_mul, ← map_mul] at h1
    refine hπA ?_ ?_ h1
    · exact hDA t _ (hz₄A s)
    · exact hz₄A _

end NatQuotK

variable {G : Type} [Group G] {H : Subgroup G} {r₁ r₂ : G} {U : Subgroup G}
  {root : ℤ → Subgroup G}

theorem short_coordsK (R : RGD2 6 H r₁ r₂ U root) (E : SL2Pos H R.N root 4)
    (E₁ : SL2Pos H R.N root 1) (hC : Hex6Comm root)
    (hO : ∀ a ∈ root 1 ⊔ root (-1), ∀ b ∈ root 4 ⊔ root (-4), a * b = b * a) {q : ℕ}
    (hq : RootOrdersD4a root q) (hqodd : Odd q) :
    ∃ (θ : E.F →+* E₁.F) (x₅ : E₁.F → G), (∀ s s', x₅ (s + s') = x₅ s * x₅ s') ∧
      Function.Injective x₅ ∧ (∀ s, x₅ s ∈ root 5) ∧ (∀ b ∈ root 5, ∃ s, x₅ s = b) ∧
      (∀ c s, (x₅ (θ c * s))⁻¹ * ⁅phi6 r₁ r₂ E.φ (sl2U c), E₁.φ (sl2U s)⁆ ∈ Vsub root 2 4) ∧
      (∀ (t : E.Fˣ) s, phi6 r₁ r₂ E.φ (sl2D t) * E₁.φ (sl2U s) * (phi6 r₁ r₂ E.φ (sl2D t))⁻¹ =
        E₁.φ (sl2U ((θ (t : E.F))⁻¹ * s))) ∧
      (∀ (t : E.Fˣ) s, phi6 r₁ r₂ E.φ (sl2D t) * x₅ s * (phi6 r₁ r₂ E.φ (sl2D t))⁻¹ =
        x₅ (θ (t : E.F) * s)) := by
  classical
  have hcardE₁ : Nat.card E₁.F = q ^ 3 := by
    rw [← E₁.toRankOneAt.card_root]
    have := hq 1 (by norm_num) (by norm_num)
    simpa using this
  have hF2 : (2 : E₁.F) ≠ 0 := two_ne_zero_of_odd_card (by
    rw [hcardE₁]; exact hqodd.pow)
  have hscal : ∀ t : E.Fˣ, ∃ a : E₁.F, ∀ y : E₁.F,
      phi6 r₁ r₂ E.φ (sl2D t) * E₁.φ (sl2U y) * (phi6 r₁ r₂ E.φ (sl2D t))⁻¹ =
        E₁.φ (sl2U (a * y)) := by
    intro t
    have hU' : ∀ c : E₁.F, ∃ d : E₁.F, phi6 r₁ r₂ E.φ (sl2D t) * E₁.φ (sl2U c) *
        (phi6 r₁ r₂ E.φ (sl2D t))⁻¹ = E₁.φ (sl2U d) := fun c => by
      have := R.invariant 1 (isRoot_of_pos_le (by norm_num) (by norm_num)) _ (phi6_D_mem R E t) _
        (sl2Pos_U_mem E₁ c)
      obtain ⟨d, hd⟩ := (E₁.hU _).1 this
      exact ⟨d, hd.symm⟩
    have hL' : ∀ c : E₁.F, ∃ d : E₁.F, phi6 r₁ r₂ E.φ (sl2D t) * E₁.φ (sl2L c) *
        (phi6 r₁ r₂ E.φ (sl2D t))⁻¹ = E₁.φ (sl2L d) := fun c => by
      have := R.invariant (-1) ⟨by norm_num, by norm_num⟩ _ (phi6_D_mem R E t) _
        (sl2Pos_L_mem E₁ c)
      obtain ⟨d, hd⟩ := (E₁.hL _).1 this
      exact ⟨d, hd.symm⟩
    obtain ⟨a, -, ha, -⟩ := exists_scalar_of_normalizes hF2 E₁.φ E₁.inj R.comm_H E₁.hD
      (phi6_D_mem R E t) hU' hL'
    exact ⟨a, ha⟩
  choose a ha using hscal
  have hBN : ∀ x ∈ root 1, x ∈ Vsub root 2 4 → x = 1 := fun x hx hxN =>
    (rgd2_unique_15 R hx (root 5).one_mem (by simpa using hxN)).1
  have hAN : ∀ x ∈ root 5, x ∈ Vsub root 2 4 → x = 1 := fun x hx hxN =>
    (rgd2_unique_15 R (root 1).one_mem hx (by simpa using hxN)).2
  have hDA : ∀ t : E.Fˣ, ∀ x ∈ root 5, phi6 r₁ r₂ E.φ (sl2D t) * x *
      (phi6 r₁ r₂ E.φ (sl2D t))⁻¹ ∈ root 5 := fun t x hx =>
    R.invariant 5 (isRoot_of_pos_le (by norm_num) (by norm_num)) _ (phi6_D_mem R E t) _ hx
  have hcardA : Nat.card (root 5) = Nat.card E₁.F := by
    rw [hcardE₁]
    have := hq 5 (by norm_num) (by norm_num)
    simpa using this
  obtain ⟨θ, x₅, h5add, h5inj, h5mem, h5surj, hrel, hw1, hw5⟩ :=
    (natQuot_short R E hC hO).exists_coordsK (xB := fun y => E₁.φ (sl2U y))
      (fun y y' => by rw [sl2U_add, map_mul]) (fun y y' h => sl2U_injective (E₁.inj h))
      (fun y => sl2Pos_U_mem E₁ y) a ha hcardA hBN hAN hDA
  exact ⟨θ, x₅, h5add, h5inj, h5mem, h5surj, hrel, hw1, hw5⟩

end CFSG.GH74.GLS.Stage4.Hex
