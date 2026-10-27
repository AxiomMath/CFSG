module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2Coord
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2Adapt
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2H1

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaN2

open Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar

variable {Γ : Type*} [Group Γ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] noncomputable def eProdG (θ : SL3 →* Γ) (μ : ℕ) : Γ :=
  ((bitList μ).map fun m => θ (gen3 (Fin.ofNat 12 m))).prod

section Hyp


structure R3bHyp (π : Γ →* (W →ₗ[ZMod 2] W)) (θ : SL3 →* Γ) (τW : W →ₗ[ZMod 2] W)
    (ι : (Fin 9 → ZMod 2) →ₗ[ZMod 2] W) (D : Subgroup Γ) (W₀ V : Submodule (ZMod 2) W)
    (τ : Γ →* Γ) : Prop where
  inj : Function.Injective ι
  fix : ∀ u, τW (ι u) = ι u
  range : ∀ u, ∃ x, τW x + x = ι u
  card : Nat.card W = 2 ^ (9 + 9)
  comm : ∀ g x, τW (π (θ g) x) = π (θ g) (τW x)
  ι_eq : ∀ g u, π (θ g) (ι u) = ι (rhoA g *ᵥ u)
  D_comm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a
  D_sq : ∀ d ∈ D, d * d = 1
  E_le : ∀ m < 4, θ (gen3 (Fin.ofNat 12 m)) ∈ D
  ν_norm : ∀ j < 4, ∀ d ∈ D, θ (gen3 (nuS j)) * d * (θ (gen3 (nuS j)))⁻¹ ∈ D
  W0 : ∀ d ∈ D, ∀ x, π d x + x ∈ W₀
  W0_card : Nat.card W₀ ≤ 2 ^ 10
  W1 : ∀ d ∈ D, ∀ x ∈ W₀, π d x + x ∈ V
  V_card : Nat.card V ≤ 4
  W2 : ∀ d ∈ D, ∀ x ∈ V, π d x = x
  τfix : ∀ d ∈ D, τ d = d → ∃ μ < 16, d = eProdG θ μ
  τsurj : ∀ m < 4, ∃ d ∈ D, d * τ d = θ (gen3 (Fin.ofNat 12 m))
  gen : θ.range ⊔ D = ⊤
  ττ : ∀ g, τ (τ g) = g
  πτ : ∀ g, π (τ g) = τW ∘ₗ π g ∘ₗ τW
  τK : ∀ g, τ (θ g) = θ g
  τD : ∀ d ∈ D, τ d ∈ D
  Kr : ∀ g, π g = 1 → τ g = g → g = 1

end Hyp


variable {π : Γ →* (W →ₗ[ZMod 2] W)} {θ : SL3 →* Γ} {τW : W →ₗ[ZMod 2] W}
  {ι : (Fin 9 → ZMod 2) →ₗ[ZMod 2] W} {D : Subgroup Γ} {W₀ V : Submodule (ZMod 2) W}
  {τ : Γ →* Γ}

theorem bitList_lt {μ n : ℕ} (hn : n ∈ bitList μ) : n < 4 :=
  List.mem_range.mp (List.mem_filter.mp hn).1

theorem eProdG_mem (h : R3bHyp π θ τW ι D W₀ V τ) (μ : ℕ) : eProdG θ μ ∈ D :=
  Subgroup.list_prod_mem _ fun x hx => by
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hx
    exact h.E_le n (bitList_lt hn)

theorem gen3_inv (s : Fin 12) : (gen3 s)⁻¹ = gen3 s := inv_eq_of_mul_eq_one_right (gen3_mul_self s)

theorem R3bHyp.inv_eq (h : R3bHyp π θ τW ι D W₀ V τ) {d : Γ} (hd : d ∈ D) : d⁻¹ = d :=
  inv_eq_of_mul_eq_one_right (h.D_sq d hd)

theorem R3bHyp.τ_eProdG (h : R3bHyp π θ τW ι D W₀ V τ) (μ : ℕ) : τ (eProdG θ μ) = eProdG θ μ := by
  rw [eProdG, map_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left fun n _ => h.τK _

section Coords

variable {e : W ≃ₗ[ZMod 2] (Fin (9 + 9) → ZMod 2)}

theorem mx_mul (x y : Γ) : matOfN e (π (x * y)) = matOfN e (π x) * matOfN e (π y) := by
  rw [map_mul, matOfN_mul]

theorem R3bHyp.mx_τ (h : R3bHyp π θ τW ι D W₀ V τ) (he : matOfN e τW = tMN 9) (x : Γ) :
    matOfN e (π (τ x)) = tauM * matOfN e (π x) * tauM := by
  rw [h.πτ, matOfN_comp, matOfN_comp, he, tMN_eq_tauM, mul_assoc]

theorem mx_E (hK : ∀ g, matOfN e (π (θ g)) = rhoN (rhoA g)) (m : ℕ) :
    matOfN e (π (θ (gen3 (Fin.ofNat 12 m)))) = eM m := by
  rw [hK, rhoA_gen3, rhoN_genA_eM]

theorem mx_V (hK : ∀ g, matOfN e (π (θ g)) = rhoN (rhoA g)) (j : ℕ) :
    matOfN e (π (θ (gen3 (nuS j)))) = vM j := by
  rw [hK, rhoA_gen3, rhoN_genA_vM]

theorem mx_eProdG (hK : ∀ g, matOfN e (π (θ g)) = rhoN (rhoA g)) (μ : ℕ) :
    matOfN e (π (eProdG θ μ)) = eProdM μ := by
  rw [eProdG, eProdM_eq, map_list_prod]
  change matHomN e _ = _
  rw [map_list_prod, List.map_map, List.map_map]
  congr 1
  exact List.map_congr_left fun n _ => mx_E hK n

end Coords

section Flag

variable {e : W ≃ₗ[ZMod 2] (Fin (9 + 9) → ZMod 2)}

theorem witCheck_spec :
    (∀ i ∈ w0List, (w0Wit i).1 < 4 ∧
      (bmulVec 18 18 (eBits18 (w0Wit i).1) (w0Wit i).2 ^^^ (w0Wit i).2) = 2 ^ i) ∧
    (∀ i ∈ [0, 9], ∀ c < 18, (w0Wit i).2.testBit c = true → inW0 c = true) := by
  have h := witCheck_eq_true
  simp only [witCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.mem_range, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  refine ⟨fun i hi => h.1 i hi, fun i hi c hc hb => ?_⟩
  rcases h.2 i hi c hc with h' | h'
  · rw [hb] at h'; exact absurd h' (by decide)
  · exact h'

theorem toVec_xor (n a b : ℕ) : toVec n (a ^^^ b) = toVec n a + toVec n b := by
  ext i; simp [toVec, Nat.testBit_xor, bz_xor]

theorem mem_w0List (i : Fin 18) (hi : clsN i ≤ 1) : (i : ℕ) ∈ w0List := by
  revert i; decide

theorem mem_iv (i : Fin 18) (hi : clsN i = 0) : (i : ℕ) ∈ [0, 9] := by
  revert i; decide

theorem e_add (d : Γ) (y : W) : e (π d y + y) = matOfN e (π d) *ᵥ e y + e y := by
  rw [map_add, matOfN_mulVec]

theorem wit_eq {i : ℕ} (hi : i ∈ w0List) (hi18 : i < 18) :
    eM (w0Wit i).1 *ᵥ toVec 18 (w0Wit i).2 + toVec 18 (w0Wit i).2 = Pi.single ⟨i, hi18⟩ 1 := by
  have := congrArg (toVec 18) (witCheck_spec.1 i hi).2
  rw [toVec_xor, toVec_bmulVec, toVec_two_pow 18 ⟨i, hi18⟩] at this
  exact this

theorem R3bHyp.single_mem_W0 (h : R3bHyp π θ τW ι D W₀ V τ)
    (hK : ∀ g, matOfN e (π (θ g)) = rhoN (rhoA g)) {i : Fin 18} (hi : clsN i ≤ 1) :
    (Pi.single i 1 : Fin 18 → ZMod 2) ∈ W₀.map e.toLinearMap := by
  have hw := mem_w0List i hi
  have hm := (witCheck_spec.1 i hw).1
  set g := θ (gen3 (Fin.ofNat 12 (w0Wit i).1))
  set y := e.symm (toVec 18 (w0Wit i).2)
  refine ⟨π g y + y, h.W0 g (h.E_le _ hm) y, ?_⟩
  change e (π g y + y) = _
  rw [e_add, mx_E hK, LinearEquiv.apply_symm_apply]
  exact wit_eq hw i.isLt

theorem R3bHyp.mem_W0_map (h : R3bHyp π θ τW ι D W₀ V τ)
    (hK : ∀ g, matOfN e (π (θ g)) = rhoN (rhoA g)) {x : Fin 18 → ZMod 2}
    (hx : ∀ c : Fin 18, ¬ clsN c ≤ 1 → x c = 0) : e.symm x ∈ W₀ := by
  have : x ∈ W₀.map e.toLinearMap :=
    mem_of_supp (I := I0) (fun i hi => h.single_mem_W0 hK ((mem_I0 i).mp hi))
      (fun c hc => hx c (fun h' => hc ((mem_I0 c).mpr h')))
  obtain ⟨y, hy, rfl⟩ := this
  simpa using hy

theorem R3bHyp.single_mem_V (h : R3bHyp π θ τW ι D W₀ V τ)
    (hK : ∀ g, matOfN e (π (θ g)) = rhoN (rhoA g)) {i : Fin 18} (hi : clsN i = 0) :
    (Pi.single i 1 : Fin 18 → ZMod 2) ∈ V.map e.toLinearMap := by
  have hw := mem_w0List i (by omega)
  have hm := (witCheck_spec.1 i hw).1
  set g := θ (gen3 (Fin.ofNat 12 (w0Wit i).1))
  set y := e.symm (toVec 18 (w0Wit i).2)
  have hy : y ∈ W₀ := h.mem_W0_map hK fun c hc => by
    simp only [toVec]
    have h2 := witCheck_spec.2 i (mem_iv i hi) c c.isLt
    by_cases hb : (w0Wit (i : ℕ)).2.testBit c
    · have := h2 hb
      exact absurd (show clsN c ≤ 1 by simp [clsN, this]; split_ifs <;> omega) hc
    · rw [Bool.eq_false_iff.mpr hb, bz_false]
  refine ⟨π g y + y, h.W1 g (h.E_le _ hm) y hy, ?_⟩
  change e (π g y + y) = _
  rw [e_add, mx_E hK, LinearEquiv.apply_symm_apply]
  exact wit_eq hw i.isLt

theorem card_map_equiv (S : Submodule (ZMod 2) W) :
    Nat.card (S.map e.toLinearMap) = Nat.card S :=
  Nat.card_congr (e.toEquiv.subtypeEquiv fun a => by simp [Submodule.mem_map_equiv]).symm

theorem sub_apply_zmod2 (x y : Fin 18 → ZMod 2) (r : Fin 18) : (x - y) r = (x + y) r := by
  rw [Pi.sub_apply, Pi.add_apply]
  rcases (show ∀ a : ZMod 2, a = 0 ∨ a = 1 by decide) (y r) with h | h <;> rw [h] <;> ring_nf
  rfl

theorem R3bHyp.flagM (h : R3bHyp π θ τW ι D W₀ V τ)
    (hK : ∀ g, matOfN e (π (θ g)) = rhoN (rhoA g)) {d : Γ} (hd : d ∈ D) :
    FlagM (matOfN e (π d) - 1) := by
  have hS0 := coord_zero_of_card (W₀.map e.toLinearMap) I0
    (fun i hi => h.single_mem_W0 hK ((mem_I0 i).mp hi))
    (by rw [card_map_equiv, card_I0]; exact h.W0_card)
  have hSV := coord_zero_of_card (V.map e.toLinearMap) IV
    (fun i hi => h.single_mem_V hK ((mem_IV i).mp hi))
    (by rw [card_map_equiv, card_IV]; exact h.V_card)
  intro r c hrc
  set y := e.symm (Pi.single c 1)
  have hentry : (matOfN e (π d) - 1) r c = e (π d y + y) r := by
    rw [e_add, LinearEquiv.apply_symm_apply, ← sub_apply_zmod2]
    have : matOfN e (π d) *ᵥ Pi.single c 1 - Pi.single c 1 = (matOfN e (π d) - 1) *ᵥ
        Pi.single c 1 := by rw [Matrix.sub_mulVec, one_mulVec]
    rw [this, mulVec_single_one]
    rfl
  rw [hentry]
  have hc3 := clsN_le c
  by_cases hc0 : clsN c = 0
  · have hyV : y ∈ V := by
      have := h.single_mem_V hK hc0
      obtain ⟨y', hy', hy'e⟩ := this
      have : y' = y := by rw [← LinearEquiv.symm_apply_apply e y']; exact congrArg e.symm hy'e
      rw [← this]; exact hy'
    rw [h.W2 d hd y hyV, add_self_W, map_zero, Pi.zero_apply]
  · by_cases hc2 : clsN c = 2
    · have hr : ¬ clsN r ≤ 1 := fun h' => hrc (Or.inl ⟨h', hc2⟩)
      exact hS0 _ ⟨_, h.W0 d hd y, rfl⟩ r fun h' => hr ((mem_I0 r).mp h')
    · have hyW : y ∈ W₀ := h.mem_W0_map hK fun c' hc' => by
        rw [Pi.single_apply, ite_eq_right]; rintro rfl; exact hc' (by omega)
      have hr : clsN r ≠ 0 := fun h' => hrc (Or.inr ⟨h', by omega⟩)
      exact hSV _ ⟨_, h.W1 d hd y hyW, rfl⟩ r fun h' => hr ((mem_IV r).mp h')

end Flag

end CFSG.EvenSmallLie.UnitarySix.YamadaN2
