module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityA2TwoMinusCount
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityA2Core

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.LieType.Steinberg
  Multiplicative

section Cells

variable {G : Type*} [Group G]

theorem eq_one_of_central_of_cells (B U : Subgroup G) (hUB : U ≤ B)
    (hUnorm : ∀ b ∈ B, ∀ u ∈ U, b * u * b⁻¹ ∈ U) (c₀ : G)
    (hcell : ∀ g : G, g ∈ B ∨ ∃ b ∈ B, ∃ u ∈ U, g = b * c₀ * u)
    (hmeet : ∀ u ∈ U, c₀ * u * c₀⁻¹ ∈ B → u = 1)
    (hKC : ∀ k ∈ B, (∀ u ∈ U, k * u = u * k) → k ∈ U) (hU : U ≠ ⊥) {z : G}
    (hz : ∀ g : G, z * g = g * z) : z = 1 := by
  have hcore := normalCore_eq_bot_of_cells B U hUnorm c₀ hmeet hKC
  have hzC : z ∈ Subgroup.center G := Subgroup.mem_center_iff.2 fun g => (hz g).symm
  by_cases hZB : Subgroup.center G ≤ B
  · have h := Subgroup.normal_le_normalCore.2 hZB hzC
    rw [hcore, Subgroup.mem_bot] at h
    exact h
  exfalso
  obtain ⟨a, haA, haB⟩ := IsConcreteLE.not_le_iff_exists.1 hZB
  have hBn : B.Normal := by
    refine ⟨fun b hb g => ?_⟩
    obtain ⟨x, hx, y, hy, rfl⟩ :=
      exists_mul_eq_of_cells_of_not_mem B U hUB c₀ hcell (Subgroup.center G) haA haB g
    have hxc := Subgroup.mem_center_iff.1 hx
    have e : x * y * b * (x * y)⁻¹ = y * b * y⁻¹ := by
      have e1 : x * y * b * (x * y)⁻¹ = x * (y * b * y⁻¹) * x⁻¹ := by group
      rw [e1, ← hxc (y * b * y⁻¹), mul_inv_cancel_right]
    rw [e]
    exact B.mul_mem (B.mul_mem hy hb) (B.inv_mem hy)
  apply hU
  rw [eq_bot_iff, ← hcore]
  exact hUB.trans (Subgroup.normal_le_normalCore.2 le_rfl)

theorem eq_one_of_central_of_equiv {F F' : Type*} [Group F] [Group F'] (e : F ≃* F')
    (h : ∀ z : F, (∀ g : F, z * g = g * z) → z = 1) :
    ∀ z : F', (∀ g : F', z * g = g * z) → z = 1 := by
  intro z hz
  have h1 : e.symm z = 1 := h _ fun g => by
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hz (e g)
  rw [← e.apply_symm_apply z, h1, map_one]

end Cells

section Polarity

theorem polarity_cells {X : Type*} [Group X] [Finite X] (D : RankTwoSystem X 3) {θ : X ≃* X}
    (hθ : D.IsPolarity θ) {c₀ : X} (hc₀ : c₀ ∈ dc D.B D.N D.w₀) (hc₀f : θ c₀ = c₀)
    (hKC : ∀ k ∈ D.B, θ k = k → (∀ u ∈ D.U, θ u = u → k * u = u * k) → k ∈ D.U) :
    ∃ c : ↥(foldFix θ), D.U.subgroupOf (foldFix θ) ≤ D.B.subgroupOf (foldFix θ) ∧
      (∀ b ∈ D.B.subgroupOf (foldFix θ), ∀ u ∈ D.U.subgroupOf (foldFix θ),
        b * u * b⁻¹ ∈ D.U.subgroupOf (foldFix θ)) ∧
      (∀ g : ↥(foldFix θ), g ∈ D.B.subgroupOf (foldFix θ) ∨
        ∃ b ∈ D.B.subgroupOf (foldFix θ), ∃ u ∈ D.U.subgroupOf (foldFix θ), g = b * c * u) ∧
      (∀ u ∈ D.U.subgroupOf (foldFix θ), c * u * c⁻¹ ∈ D.B.subgroupOf (foldFix θ) → u = 1) ∧
      (∀ k ∈ D.B.subgroupOf (foldFix θ),
        (∀ u ∈ D.U.subgroupOf (foldFix θ), k * u = u * k) → k ∈ D.U.subgroupOf (foldFix θ)) ∧
      (D.B.subgroupOf (foldFix θ)).index = 1 + Nat.card ↥(D.U ⊓ foldFix θ) := by
  have hmemB : ∀ g : ↥(foldFix θ), g ∈ D.B.subgroupOf (foldFix θ) ↔ (g : X) ∈ D.B :=
    fun g => Subgroup.mem_subgroupOf
  have hmemU : ∀ g : ↥(foldFix θ), g ∈ D.U.subgroupOf (foldFix θ) ↔ (g : X) ∈ D.U :=
    fun g => Subgroup.mem_subgroupOf
  have hw₀ : D.w₀ ≠ 1 := fun h => by
    have := D.rank2.dih.altWord_inj (i := 3) (j := 0) le_rfl (by norm_num)
      (h.trans (altWord_zero D.w₁ D.w₂).symm)
    omega
  have hc₀B : c₀ ∉ D.B := fun h => hw₀ ((D.bw_eq hc₀).symm.trans (D.bw_eq (mem_dc_one.2 h)))
  let c : ↥(foldFix θ) := ⟨c₀, hc₀f⟩
  have hcB : c ∉ D.B.subgroupOf (foldFix θ) := fun h => hc₀B ((hmemB c).1 h)
  have hUB : D.U.subgroupOf (foldFix θ) ≤ D.B.subgroupOf (foldFix θ) := fun g hg =>
    (hmemB g).2 (D.U_le_B ((hmemU g).1 hg))
  have hcell : ∀ g : ↥(foldFix θ), g ∈ D.B.subgroupOf (foldFix θ) ∨
      ∃ b ∈ D.B.subgroupOf (foldFix θ), ∃ u ∈ D.U.subgroupOf (foldFix θ), g = b * c * u := by
    intro g
    rcases hθ.fixed_mem_B_or_top (mem_foldFix.1 g.2) with hg | hg
    · exact Or.inl ((hmemB g).2 hg)
    · obtain ⟨b, hb, hbf, u, hu, huf, hgbu⟩ :=
        hθ.top_decomp hc₀ hg hc₀f (mem_foldFix.1 g.2)
      exact Or.inr ⟨⟨b, hbf⟩, (hmemB _).2 hb, ⟨u, huf⟩, (hmemU _).2 hu, Subtype.ext hgbu⟩
  have hinj : ∀ b ∈ D.B.subgroupOf (foldFix θ), ∀ b' ∈ D.B.subgroupOf (foldFix θ),
      ∀ u ∈ D.U.subgroupOf (foldFix θ), ∀ u' ∈ D.U.subgroupOf (foldFix θ),
      b * c * u = b' * c * u' → b = b' ∧ u = u' := by
    intro b hb b' hb' u hu u' hu' h
    obtain ⟨h1, h2⟩ := RankTwoSystem.top_unique hc₀ ((hmemB b).1 hb) ((hmemB b').1 hb')
      ((hmemU u).1 hu) ((hmemU u').1 hu') (congrArg Subtype.val h)
    exact ⟨Subtype.ext h1, Subtype.ext h2⟩
  have hindex := index_eq_one_add_card_of_cells (D.B.subgroupOf (foldFix θ))
    (D.U.subgroupOf (foldFix θ)) hUB c hcB hcell hinj
  have hUcard : Nat.card ↥(D.U.subgroupOf (foldFix θ)) = Nat.card ↥(D.U ⊓ foldFix θ) := by
    rw [← Subgroup.inf_subgroupOf_right]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  refine ⟨c, hUB, fun b hb u hu =>
    (hmemU _).2 (D.conj_mem_U_of_mem_B ((hmemB b).1 hb) ((hmemU u).1 hu)), hcell,
    fun u hu h => Subtype.ext (RankTwoSystem.U_meet_top hc₀ ((hmemU u).1 hu) ((hmemB _).1 h)),
    ?_, by rw [hindex, hUcard]⟩
  intro k hk hcomm
  refine (hmemU k).2 (hKC k ((hmemB k).1 hk) (mem_foldFix.1 k.2) fun u hu huf => ?_)
  exact congrArg Subtype.val (hcomm ⟨u, huf⟩ ((hmemU _).2 hu))

end Polarity

section Weyl

variable {k : Type*} [Field k]

theorem sl2_weyl_eq {β : k} (hβ : β ≠ 0) :
    sl2Upper β * sl2Lower (-β⁻¹) * sl2Upper β = sl2Lower (-β⁻¹) * sl2Upper β * sl2Lower (-β⁻¹) := by
  refine Subtype.ext ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Lower, coe_sl2Upper, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hβ]

theorem sl2_conj_weyl_eq {β t : k} (hβ : β ≠ 0) (hD : 1 + β ^ 2 * t ^ 2 ≠ 0) :
    sl2Lower (-t) * (sl2Upper β * sl2Lower (-β⁻¹) * sl2Upper β) * sl2Lower t =
      sl2Upper (β * (1 - β * t) / (1 + β ^ 2 * t ^ 2)) *
        sl2Lower (-((1 + β ^ 2 * t ^ 2) / β)) *
          sl2Upper (β * (β * t + 1) / (1 + β ^ 2 * t ^ 2)) := by
  have hD' : 1 + t ^ 2 * β ^ 2 ≠ 0 := by rwa [mul_comm]
  refine Subtype.ext ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Lower, coe_sl2Upper, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring

variable {X : Type*} [Group X]

theorem theta_fixed_mem_dc (D : RankTwoSystem X 3) (ρ : Matrix.SpecialLinearGroup (Fin 2) k →* X)
    (τ : X ≃* X) (ε : k ≃+* k) (κ : kˣ)
    (hu : ∀ a, τ (ρ (sl2Upper a)) = ρ (sl2Lower ((κ : k) * ε a)))
    (hl : ∀ a, τ (ρ (sl2Lower a)) = ρ (sl2Upper (((κ⁻¹ : kˣ) : k) * ε a)))
    (hρ2 : ∀ a, ρ (sl2Upper a) ∈ D.root 2)
    (hρN : ∃ m₀ : D.N, (m₀ : X) = ρ unSL2W ∧ (m₀ : D.Weyl) = D.w₀)
    (hρH : ∀ u : kˣ, ρ (unSL2Diag u) ∈ D.B ⊓ D.N) (t β : kˣ)
    (hβ : (κ : k) * ε β = -((β : k)⁻¹)) (hD : 1 + (β : k) ^ 2 * (t : k) ^ 2 ≠ 0) :
    τ.trans (MulAut.conj ((ρ (sl2Lower (t : k)))⁻¹ * τ (ρ (sl2Lower (t : k)))))
        ((ρ (sl2Lower (t : k)))⁻¹ *
          (ρ (sl2Upper β) * ρ (sl2Lower (-(β : k)⁻¹)) * ρ (sl2Upper β)) * ρ (sl2Lower (t : k))) =
      (ρ (sl2Lower (t : k)))⁻¹ *
        (ρ (sl2Upper β) * ρ (sl2Lower (-(β : k)⁻¹)) * ρ (sl2Upper β)) * ρ (sl2Lower (t : k)) ∧
    (ρ (sl2Lower (t : k)))⁻¹ * (ρ (sl2Upper β) * ρ (sl2Lower (-(β : k)⁻¹)) * ρ (sl2Upper β)) *
        ρ (sl2Lower (t : k)) ∈ dc D.B D.N D.w₀ := by
  have hβ0 : (β : k) ≠ 0 := β.ne_zero
  have hκ0 : (κ : k) ≠ 0 := κ.ne_zero
  have hεβ : ε (β : k) = -((κ : k) * β)⁻¹ := by
    have h := hβ
    field_simp at h ⊢
    linear_combination h
  have hl' : ((κ⁻¹ : kˣ) : k) * ε (-(β : k)⁻¹) = β := by
    rw [map_neg, map_inv₀, hεβ, Units.val_inv_eq_inv_val]
    field_simp
  have hτw : τ (ρ (sl2Upper β) * ρ (sl2Lower (-(β : k)⁻¹)) * ρ (sl2Upper β)) =
      ρ (sl2Upper β) * ρ (sl2Lower (-(β : k)⁻¹)) * ρ (sl2Upper β) := by
    rw [map_mul, map_mul, hu, hl, hl', hβ, ← map_mul, ← map_mul, ← map_mul, ← map_mul,
      sl2_weyl_eq hβ0]
  refine ⟨?_, ?_⟩
  · rw [un_theta_apply]
    have e : ρ (sl2Lower (t : k)) * ((ρ (sl2Lower (t : k)))⁻¹ *
        (ρ (sl2Upper β) * ρ (sl2Lower (-(β : k)⁻¹)) * ρ (sl2Upper β)) * ρ (sl2Lower (t : k))) *
          (ρ (sl2Lower (t : k)))⁻¹ =
        ρ (sl2Upper β) * ρ (sl2Lower (-(β : k)⁻¹)) * ρ (sl2Upper β) := by group
    rw [e, hτw]
  · have hm0 : -((1 + (β : k) ^ 2 * (t : k) ^ 2) / β) ≠ 0 :=
      neg_ne_zero.2 (div_ne_zero hD hβ0)
    have e : (ρ (sl2Lower (t : k)))⁻¹ *
        (ρ (sl2Upper β) * ρ (sl2Lower (-(β : k)⁻¹)) * ρ (sl2Upper β)) * ρ (sl2Lower (t : k)) =
        ρ (sl2Upper (β * (1 - β * t) / (1 + (β : k) ^ 2 * (t : k) ^ 2))) *
          ρ (sl2Lower (-((1 + (β : k) ^ 2 * (t : k) ^ 2) / β))) *
            ρ (sl2Upper (β * (β * t + 1) / (1 + (β : k) ^ 2 * (t : k) ^ 2))) := by
      rw [← map_inv, un_sl2Lower_inv, ← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_mul,
        ← map_mul, sl2_conj_weyl_eq hβ0 hD]
    rw [e]
    have hB2 : ∀ a, ρ (sl2Upper a) ∈ D.B := fun a =>
      D.root_le_B (by norm_num) (by norm_num) (hρ2 a)
    exact mul_mem_dc (un_lower_mem_dc D ρ hρ2 hρN hρH hm0) (hB2 _) (hB2 _)

theorem exists_beta_two [Finite k] [CharP k 2] {r : ℕ} (hr : 2 ≤ r) (hk : Nat.card k = r ^ 4)
    (ε : k ≃+* k) (hε : ∀ a, ε a = a ^ r) (κ t : kˣ)
    (ht : (t : k) * (((κ⁻¹ : kˣ) : k) * ε t) = 1) :
    ∃ β : kˣ, (κ : k) * ε β = -((β : k)⁻¹) ∧ 1 + (β : k) ^ 2 * (t : k) ^ 2 ≠ 0 := by
  classical
  have hG : Nat.card kˣ = (r + 1) * ((r - 1) * (r ^ 2 + 1)) := by
    rw [Nat.card_units, hk]
    obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
    have h5 : (m + 1) ^ 4 = (m + 1 + 1) * (m * ((m + 1) ^ 2 + 1)) + 1 := by ring
    simp only [Nat.add_sub_cancel]
    omega
  have hs : 0 < (r - 1) * (r ^ 2 + 1) := Nat.mul_pos (by omega) (by positivity)
  have hcard := card_pow_eq_of_isCyclic (G := kˣ) (d := r + 1) (s := (r - 1) * (r ^ 2 + 1))
    (by omega) hs hG (g := 1) (one_pow _)
  have h1 : 1 < Nat.card {x : kˣ // x ^ (r + 1) = 1} := by
    rw [hcard]
    omega
  have := Finite.one_lt_card_iff_nontrivial.1 h1
  obtain ⟨⟨ζ, hζ⟩, hζ1⟩ := exists_ne (⟨1, one_pow _⟩ : {x : kˣ // x ^ (r + 1) = 1})
  have hζne : ζ ≠ 1 := fun h => hζ1 (Subtype.ext h)
  have h2 : (2 : k) = 0 := by exact_mod_cast CharP.cast_eq_zero k 2
  have hneg : ∀ x : k, -x = x := fun x => by linear_combination (-x) * h2
  have hζ0 : (ζ : k) ≠ 0 := ζ.ne_zero
  have ht0 : (t : k) ≠ 0 := t.ne_zero
  have hκ0 : (κ : k) ≠ 0 := κ.ne_zero
  have hζr : (ζ : k) ^ r * ζ = 1 := by
    have h := congrArg Units.val hζ
    rw [Units.val_pow_eq_pow_val, Units.val_one, pow_succ] at h
    exact h
  have hεζ : ε (ζ : k) = (ζ : k)⁻¹ := by
    rw [hε]
    exact eq_inv_of_mul_eq_one_left hζr
  have hεt : ε (t : k) = κ * (t : k)⁻¹ := by
    rw [Units.val_inv_eq_inv_val] at ht
    field_simp at ht ⊢
    linear_combination ht
  refine ⟨ζ * t⁻¹, ?_, ?_⟩
  · rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hεζ, hεt, hneg]
    field_simp
  · rw [Units.val_mul, Units.val_inv_eq_inv_val]
    intro h0
    apply hζne
    have h' : (1 : k) + (ζ : k) ^ 2 = 0 := by
      field_simp at h0
      linear_combination h0
    have h'' : ((ζ : k) + 1) ^ 2 = 0 := by linear_combination h' + (ζ : k) * h2
    have h3 : (ζ : k) + 1 = 0 := pow_eq_zero_iff two_ne_zero |>.1 h''
    have h4 : (ζ : k) = 1 := by linear_combination h3 - h2
    exact Units.ext h4

end Weyl

theorem foldFix_opposition_two {f : ℕ} (hq : (2 ^ f) % 3 = 2) (hf : 0 < f)
    {X : Type*} [Group X] [Finite X]
    (D : RankTwoSystem X 3) (τ e : X ≃* X) (hτ : D.IsOpposition τ) (hτe : ∀ y, τ (τ y) = e y)
    (he : ∀ b ∈ D.B, e b ∈ D.B) (hτ4 : ∀ y, τ (τ (τ (τ y))) = y)
    {k : Type} [Field k] [Finite k] [CharP k 2] (hk : Nat.card k = (2 ^ f) ^ 4)
    (ε : k ≃+* k) (hε : ∀ a, ε a = a ^ (2 ^ f))
    (ρ : Matrix.SpecialLinearGroup (Fin 2) k →* X) (hρinj : Function.Injective ρ) (κ : kˣ)
    (hu : ∀ a, τ (ρ (sl2Upper a)) = ρ (sl2Lower ((κ : k) * ε a)))
    (hl : ∀ a, τ (ρ (sl2Lower a)) = ρ (sl2Upper (((κ⁻¹ : kˣ) : k) * ε a)))
    (hρ2 : ∀ a, ρ (sl2Upper a) ∈ D.root 2) (hρ2' : ∀ y ∈ D.root 2, ∃ a, y = ρ (sl2Upper a))
    (hρN : ∃ m₀ : D.N, (m₀ : X) = ρ unSL2W ∧ (m₀ : D.Weyl) = D.w₀)
    (hρH : ∀ u : kˣ, ρ (unSL2Diag u) ∈ D.B ⊓ D.N)
    (x₁ : Multiplicative k →* X) (hx₁inj : Function.Injective x₁)
    (hx₁ : ∀ a, x₁ a ∈ D.root 1) (hx₁s : ∀ y ∈ D.root 1, ∃ a, y = x₁ a)
    (hx₁torus : ∀ h ∈ D.B ⊓ D.N, ∃ χ : kˣ,
      ∀ a : k, h * x₁ (ofAdd a) * h⁻¹ = x₁ (ofAdd ((χ : k) * a)))
    (hx₁e : ∀ a : k, e (x₁ (ofAdd a)) = x₁ (ofAdd (ε (ε a))))
    (hab₁ : ∀ a ∈ D.root 1, ∀ b ∈ D.root 1, a * b = b * a)
    (hab₃ : ∀ a ∈ D.root 3, ∀ b ∈ D.root 3, a * b = b * a)
    (hTor : ∀ h ∈ D.B ⊓ D.N, ∀ y ∈ D.root 1, y ≠ 1 → ∀ z ∈ D.root 3, z ≠ 1 →
      h * y = y * h → h * z = z * h → h = 1) :
    (∀ A : Subgroup ↥(foldFix τ), A.Normal → Nat.Coprime 3 (Nat.card A) → A = ⊥) ∧
      (∀ z : ↥(foldFix τ), (∀ g : ↥(foldFix τ), z * g = g * z) → z = 1) ∧
      ∃ U₀ : Subgroup X, U₀ ≤ foldFix τ ∧ IsPGroup 2 U₀ ∧ (2 ^ f) ^ 3 ≤ Nat.card U₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := un_norm_solution hf hk ε hε κ (un_norm_eq ρ hρinj τ hτ4 ε κ hu hl)
  have hg : (ρ (sl2Lower (t : k)))⁻¹ * τ (ρ (sl2Lower (t : k))) *
      ((D.lift D.w₀ : D.N) : X) ∈ D.B := un_adapted_mem_B D ρ τ ε κ hl hρ2 hρN hρH t ht
  have hθpol := hτ.isPolarity hg
  have hθapp := un_theta_apply τ (ρ (sl2Lower (t : k)))
  have hθ4 := un_theta_four τ hτ4 (ρ (sl2Lower (t : k)))
  obtain ⟨l₂, hθ₂⟩ := un_theta_x2 ρ τ ε κ hu hl t ht
  obtain ⟨ν, hθ₁₁⟩ := un_theta_sq_x1 D τ e hτ hτe he ε x₁ hx₁ hx₁torus hx₁e hab₁ hab₃ hg
  have hθ₁ := fun y (hy : y ∈ D.root 1) => hτ.theta_root₁ hg hy
  have hθ₃ := fun z (hz : z ∈ D.root 3) => hτ.theta_root₃ hg hz
  have hr2 : 2 ≤ 2 ^ f := Nat.le_self_pow hf.ne' 2
  obtain ⟨β, hβ, hD⟩ := exists_beta_two hr2 hk ε hε κ t ht
  obtain ⟨hc₀f, hc₀⟩ := theta_fixed_mem_dc D ρ τ ε κ hu hl hρ2 hρN hρH t β hβ hD
  set x : X := ρ (sl2Lower (t : k))
  set θ : X ≃* X := τ.trans (MulAut.conj (x⁻¹ * τ x))
  have hx₂inj : Function.Injective (ρ.comp (unSL2UpperHom k)) := fun a b h =>
    Multiplicative.toAdd.injective
      (@un_sl2Upper_injective k _ (toAdd a) (toAdd b) (hρinj h))
  obtain ⟨hcard, hfix⟩ := un_heis_fixed_all D hf hk ε hε x₁ (ρ.comp (unSL2UpperHom k)) hx₁inj
    hx₂inj hx₁ (fun a => hρ2 _) hx₁s
    (fun y hy => by
      obtain ⟨a, ha⟩ := hρ2' y hy
      exact ⟨ofAdd a, ha⟩) hab₁ hab₃ θ hθpol.mem_U hθ4 l₂ ν hθ₂ hθ₁ hθ₃ hθ₁₁
  have hKC := un_hKC D hab₁ hab₃ hTor θ hfix
  obtain ⟨c, hUB, hUnorm, hcell, hmeet, hKC', hindex⟩ := polarity_cells D hθpol hc₀ hc₀f hKC
  have hUne : D.U.subgroupOf (foldFix θ) ≠ ⊥ := by
    obtain ⟨y, hy, hy1, b, hb, z, hz, -, hfx⟩ := hfix
    intro h
    have hmem : (⟨y * b * z, hfx⟩ : ↥(foldFix θ)) ∈ D.U.subgroupOf (foldFix θ) :=
      Subgroup.mem_subgroupOf.2 (D.U.mul_mem (D.U.mul_mem
        (D.root_le_U (by norm_num) (by norm_num) hy) (D.root_le_U (by norm_num) (by norm_num) hb))
        (D.root_le_U (by norm_num) (by norm_num) hz))
    rw [h, Subgroup.mem_bot] at hmem
    have h1 : y * b * z = 1 := congrArg Subtype.val hmem
    exact hy1 (un_unique D hy (D.root 1).one_mem hb (D.root 2).one_mem hz (D.root 3).one_mem
      (by rw [h1]; simp)).1
  have h3 : 3 ∣ (D.B.subgroupOf (foldFix θ)).index := by
    rw [hindex, hcard]
    apply Nat.dvd_of_mod_eq_zero
    simp [Nat.add_mod, Nat.pow_mod, hq]
  have hNA : ∀ A : Subgroup ↥(foldFix θ), A.Normal → Nat.Coprime 3 (Nat.card A) → A = ⊥ :=
    fun A hA hcop => by
      have := hA
      exact eq_bot_of_cells_of_coprime _ _ hUB hUnorm c hcell hmeet hKC' (by norm_num) h3 A
        hcop
  have hZ : ∀ z : ↥(foldFix θ), (∀ g : ↥(foldFix θ), z * g = g * z) → z = 1 := fun z hz =>
    eq_one_of_central_of_cells _ _ hUB hUnorm c hcell hmeet hKC' hUne hz
  refine ⟨normal_coprime_eq_bot_of_equiv (unFixEquiv τ θ x hθapp) hNA,
    eq_one_of_central_of_equiv (unFixEquiv τ θ x hθapp) hZ, ?_⟩
  have hcard₀ : Nat.card ↥((D.U ⊓ foldFix θ).map (MulAut.conj x).toMonoidHom) =
      (2 ^ f) ^ 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]
    exact hcard
  refine ⟨(D.U ⊓ foldFix θ).map (MulAut.conj x).toMonoidHom, ?_, ?_, hcard₀.ge⟩
  · rintro _ ⟨u, hu, rfl⟩
    have h := mem_foldFix.1 (Subgroup.mem_inf.1 hu).2
    rw [hθapp] at h
    rw [mem_foldFix]
    show τ (x * u * x⁻¹) = x * u * x⁻¹
    calc τ (x * u * x⁻¹) = x * (x⁻¹ * τ (x * u * x⁻¹) * x) * x⁻¹ := by group
      _ = x * u * x⁻¹ := by rw [h]
  · exact IsPGroup.of_card (n := f * 3) (by rw [hcard₀, pow_mul])

end CFSG.HardMathSupport.Timmesfeld.CrossChar
