module

public import CFSG.RankThree.Transfer.FixedPoints

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup MulAction CFSG.RankThree.Transfer

theorem multiplicative_zmod_two_cases :
    ∀ y : Multiplicative (ZMod 2), y = 1 ∨ y = Multiplicative.ofAdd 1 := by decide

section Transfer

variable {G : Type*} [Group G] [Finite G]

theorem transfer_apply_of_weaklyClosed (W N : Subgroup G) (hWN : W ≤ N) (hW : IsPGroup 2 W)
    (hcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)
    (hweak : ∀ c : G, (∀ w ∈ W, c⁻¹ * w * c ∈ N) → c ∈ N)
    (μ : N →* Multiplicative (ZMod 2)) {x : G} (hxW : x ∈ W) (hx : orderOf x = 2) :
    μ.transfer x = μ ⟨x, hWN hxW⟩ := by
  classical
  have : Fintype (G ⧸ N) := Fintype.ofFinite _
  have hxN : x ∈ N := hWN hxW
  have hker : ∀ h : N, orderOf (h : G) < orderOf x → μ h = 1 := by
    intro h hlt
    rw [hx] at hlt
    have h1 : orderOf (h : G) = 1 := by
      have := orderOf_pos (h : G)
      omega
    have h2 : (h : G) = 1 := orderOf_eq_one_iff.1 h1
    have h3 : h = 1 := Subtype.ext h2
    rw [h3, map_one]
  rw [transfer_eq_prod_fixed_of_orderOf_lt μ x hker]
  let g : G → Multiplicative (ZMod 2) := fun c =>
    if h : c⁻¹ * x * c ∈ N then μ ⟨c⁻¹ * x * c, h⟩ else 1
  set f : G ⧸ N → Multiplicative (ZMod 2) :=
    fun X => if x • X = X then cosetValue μ x X else 1 with hf
  have hfg : ∀ c : G, f (c : G ⧸ N) = g c := by
    intro c
    by_cases h : c⁻¹ * x * c ∈ N
    · simp only [hf, g, dite_eq_left h]
      rw [ite_eq_left (smul_coe_eq_iff.2 h), cosetValue_coe μ h]
    · simp only [hf, g, dite_eq_right h]
      exact ite_eq_right (fun hh => h (smul_coe_eq_iff.1 hh))
  have hgw : ∀ (w : W) (c : G), g ((w : G) * c) = g c := by
    intro w c
    have hwx : (w : G)⁻¹ * x * (w : G) = x := by
      have := hcomm x hxW w w.2
      calc (w : G)⁻¹ * x * (w : G) = (w : G)⁻¹ * ((w : G) * x) := by rw [← this]; group
        _ = x := by group
    have hconj : ((w : G) * c)⁻¹ * x * ((w : G) * c) = c⁻¹ * x * c := by
      calc ((w : G) * c)⁻¹ * x * ((w : G) * c) = c⁻¹ * ((w : G)⁻¹ * x * (w : G)) * c := by group
        _ = c⁻¹ * x * c := by rw [hwx]
    simp only [g, hconj]
  have hfinv : ∀ (w : W) (X : G ⧸ N), f (w • X) = f X := by
    intro w X
    induction X using QuotientGroup.induction_on with
    | H c =>
      have e : (w • (c : G ⧸ N) : G ⧸ N) = (((w : G) * c : G) : G ⧸ N) := by
        rw [Subgroup.smul_def, MulAction.Quotient.smul_mk, smul_eq_mul]
      rw [e, hfg, hfg, hgw]
  set s : Multiplicative (ZMod 2) := Multiplicative.ofAdd 1 with hs
  have hval : ∀ y : Multiplicative (ZMod 2), y = 1 ∨ y = s := multiplicative_zmod_two_cases
  have hss : s * s = 1 := by decide
  have hspow : ∀ n : ℕ, s ^ n = if Even n then 1 else s := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ih]
      by_cases he : Even n
      · simp [he, Nat.even_add_one]
      · simp [he, Nat.even_add_one, hss]
  let S : SubMulAction W (G ⧸ N) :=
    { carrier := {X | f X ≠ 1}
      smul_mem' := fun w X hX => by
        show f (w • X) ≠ 1
        rw [hfinv]
        exact hX }
  have hpar := hW.card_modEq_card_fixedPoints S
  have hprod : ∏ X, f X = s ^ Nat.card S := by
    rw [← Finset.prod_filter_ne_one]
    have : ∀ X ∈ Finset.univ.filter (fun X => f X ≠ 1), f X = s := fun X hX =>
      (hval (f X)).resolve_left (Finset.mem_filter.1 hX).2
    rw [Finset.prod_congr rfl this, Finset.prod_const]
    congr 1
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext X
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Iff.rfl
  have hf1 : f ((1 : G) : G ⧸ N) = μ ⟨x, hxN⟩ := by
    rw [hfg]
    simp only [g]
    rw [dite_eq_left (by simpa using hxN)]
    congr 1
    exact Subtype.ext (by simp)
  have hfix : ∀ Y : ↥S, Y ∈ fixedPoints W ↥S → (Y : G ⧸ N) = ((1 : G) : G ⧸ N) := by
    intro Y hY
    obtain ⟨c, hc⟩ := QuotientGroup.mk_surjective (Y : G ⧸ N)
    have h1 : ∀ w ∈ W, c⁻¹ * w * c ∈ N := by
      intro w hw
      have := mem_fixedPoints.1 hY ⟨w, hw⟩
      have h2 : (⟨w, hw⟩ : W) • (Y : G ⧸ N) = (Y : G ⧸ N) := congrArg Subtype.val this
      rw [← hc, Subgroup.smul_def] at h2
      exact smul_coe_eq_iff.1 h2
    have hcN : c ∈ N := hweak c h1
    rw [← hc]
    exact QuotientGroup.eq.2 (by simpa using N.inv_mem hcN)
  by_cases hμ : μ ⟨x, hxN⟩ = 1
  · have hempty : ∀ Y : ↥S, Y ∉ fixedPoints W ↥S := by
      intro Y hY
      have h1 := hfix Y hY
      have h2 : f (Y : G ⧸ N) ≠ 1 := Y.2
      rw [h1, hf1] at h2
      exact h2 hμ
    have h0 : Nat.card (fixedPoints W ↥S) = 0 := by
      rw [Nat.card_eq_zero]
      exact Or.inl ⟨fun Y => hempty Y Y.2⟩
    rw [h0] at hpar
    have hev : Even (Nat.card S) := even_iff_two_dvd.2 (Nat.modEq_zero_iff_dvd.1 hpar)
    rw [hprod, hspow, ite_eq_left hev, hμ]
  · have hμs : μ ⟨x, hxN⟩ = s := (hval _).resolve_left hμ
    have hX₀ : ((1 : G) : G ⧸ N) ∈ S := by
      show f ((1 : G) : G ⧸ N) ≠ 1
      rw [hf1]
      exact hμ
    have h1 : Nat.card (fixedPoints W ↥S) = 1 := by
      rw [Nat.card_eq_one_iff_exists]
      refine ⟨⟨⟨_, hX₀⟩, ?_⟩, fun Y => ?_⟩
      · rw [mem_fixedPoints]
        intro w
        apply Subtype.ext
        show (w : W) • ((1 : G) : G ⧸ N) = ((1 : G) : G ⧸ N)
        rw [Subgroup.smul_def, smul_coe_eq_iff]
        simpa using hWN w.2
      · apply Subtype.ext
        apply Subtype.ext
        exact hfix Y.1 Y.2
    rw [h1] at hpar
    have hodd : ¬ Even (Nat.card S) := by
      intro he
      have h2 : 2 ∣ Nat.card S := even_iff_two_dvd.1 he
      have h3 : Nat.card S ≡ 1 [MOD 2] := hpar
      have := (Nat.modEq_zero_iff_dvd.2 h2).symm.trans h3
      exact absurd this (by decide)
    rw [hprod, hspow, ite_eq_right hodd, hμs]

end Transfer

@[expose] noncomputable def signHom {H : Type*} [Group H] (K : Subgroup H) (hK : K.index = 2) :
    H →* Multiplicative (ZMod 2) where
  toFun h := open Classical in if h ∈ K then 1 else Multiplicative.ofAdd 1
  map_one' := by simp
  map_mul' a b := by
    classical
    have key := Subgroup.mul_mem_iff_of_index_two hK (a := a) (b := b)
    by_cases ha : a ∈ K <;> by_cases hb : b ∈ K
    · have hab : a * b ∈ K := key.2 (iff_of_true ha hb)
      simp [ha, hb, hab]
    · have hab : a * b ∉ K := fun h => hb ((key.1 h).1 ha)
      simp [ha, hb, hab]
    · have hab : a * b ∉ K := fun h => ha ((key.1 h).2 hb)
      simp [ha, hb, hab]
    · have hab : a * b ∈ K := key.2 (iff_of_false ha hb)
      simp only [ha, hb, hab, ite_false, ite_true]
      decide

theorem signHom_apply_of_not_mem {H : Type*} [Group H] {K : Subgroup H} (hK : K.index = 2) {h : H}
    (hh : h ∉ K) : signHom K hK h ≠ 1 := by
  classical
  simp only [signHom, MonoidHom.coe_mk, OneHom.coe_mk, hh, ite_false]
  decide

section Main

variable {G : Type*} [Group G] [Finite G]

theorem exists_normal_index_two_of_weaklyClosed (W : Subgroup G) (hW : IsPGroup 2 W)
    (hcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)
    (hweak : ∀ c : G, (∀ w ∈ W, c⁻¹ * w * c ∈ normalizer (W : Set G)) →
      c ∈ normalizer (W : Set G))
    (N₀ : Subgroup (normalizer (W : Set G))) (hN₀ : N₀.index = 2) {x : G} (hxW : x ∈ W)
    (hx : orderOf x = 2) (hxN₀ : (⟨x, Subgroup.le_normalizer hxW⟩ : normalizer (W : Set G)) ∉ N₀) :
    ∃ M : Subgroup G, M.Normal ∧ M.index = 2 ∧ x ∉ M := by
  classical
  have hV := transfer_apply_of_weaklyClosed W (normalizer (W : Set G)) Subgroup.le_normalizer hW
    hcomm hweak (signHom N₀ hN₀) hxW hx
  have hs : signHom N₀ hN₀ ⟨x, Subgroup.le_normalizer hxW⟩ ≠ 1 :=
    signHom_apply_of_not_mem hN₀ hxN₀
  set V : G →* Multiplicative (ZMod 2) := (signHom N₀ hN₀).transfer with hVdef
  have hVx : V x ≠ 1 := by
    rw [hVdef, hV]
    exact hs
  have hrange : V.range = ⊤ := by
    rw [eq_top_iff]
    intro y _
    rcases multiplicative_zmod_two_cases y with rfl | rfl
    · exact V.range.one_mem
    · have := (multiplicative_zmod_two_cases (V x)).resolve_left hVx
      rw [← this]
      exact ⟨x, rfl⟩
  refine ⟨V.ker, inferInstance, ?_, fun hxk => hVx (MonoidHom.mem_ker.1 hxk)⟩
  rw [Subgroup.index_ker, hrange, Subgroup.card_top, Nat.card_eq_fintype_card]
  decide

end Main

end CFSG.EvenSporadicStandard.Solomon78
