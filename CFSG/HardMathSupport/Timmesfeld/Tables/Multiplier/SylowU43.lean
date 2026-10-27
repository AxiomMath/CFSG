module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SylowU43Data
public import CFSG.LieType.Multipliers.U43Bridge
import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier

open CFSG.Assembly.LowTwoRank CFSG.LieType.Multipliers.U43 Matrix

namespace U43Six

@[expose] noncomputable def tsu : Multiplicative F9 →* StatedSU 4 3 F9 where
  toFun s := toSU (tmat s.toAdd) (det_tmat _) (tmat_unitary _)
  map_one' := ext_matrix tmat_zero
  map_mul' _ _ := ext_matrix (tmat_mul _ _).symm

@[expose] noncomputable def tBar : Multiplicative F9 →* X₀ := (QuotientGroup.mk' _).comp tsu

theorem tBar_conj_abcd (s : Multiplicative F9) (a b c d : ZMod 3) :
    tBar s * thetaBar (Multiplicative.ofAdd (a, b, c, d)) * (tBar s)⁻¹ =
      thetaBar (Multiplicative.ofAdd (act s.toAdd (a, b, c, d))) := by
  rw [mul_inv_eq_iff_eq_mul]
  exact congrArg QuotientGroup.mk (ext_matrix (tmat_mul_rmat s.toAdd a b c d))

theorem tBar_conj (s : Multiplicative F9) (x : Multiplicative (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3)) :
    tBar s * thetaBar x * (tBar s)⁻¹ =
      thetaBar (Multiplicative.ofAdd (act s.toAdd x.toAdd)) := by
  induction x using Multiplicative.rec with
  | ofAdd x =>
    obtain ⟨a, b, c, d⟩ := x
    exact tBar_conj_abcd s a b c d

theorem tBar_mem_normalizer {t a : X₀} (ht : t ∈ tBar.range) (ha : a ∈ thetaBar.range) :
    t * a * t⁻¹ ∈ thetaBar.range := by
  obtain ⟨s, rfl⟩ := ht
  obtain ⟨x, rfl⟩ := ha
  rw [tBar_conj]
  exact ⟨_, rfl⟩

theorem thetaBar_comm (a b : X₀) (ha : a ∈ thetaBar.range) (hb : b ∈ thetaBar.range) :
    a * b = b * a := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  rw [← map_mul, ← map_mul, mul_comm x y]

theorem tBar_eq_thetaBar {s : Multiplicative F9}
    {x : Multiplicative (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3)}
    (h : tBar s = thetaBar x) : s = 1 := by
  induction x using Multiplicative.rec with
  | ofAdd x =>
    obtain ⟨a, b, d, e⟩ := x
    have h' : QuotientGroup.mk (theta4 (Multiplicative.ofAdd (a, b, d, e))) =
        (QuotientGroup.mk (tsu s) : X₀) := h.symm
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h'
    obtain ⟨c, hc⟩ := h'
    have h2 : (theta4 (Multiplicative.ofAdd (a, b, d, e)) : GL (Fin 4) F9) *
        Matrix.GeneralLinearGroup.scalar (Fin 4) c = (tsu s : GL (Fin 4) F9) := by
      rw [hc]
      simp
    have h3 := congrArg (fun A : GL (Fin 4) F9 => (A : Matrix (Fin 4) (Fin 4) F9)) h2
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h3
    have h4 : tmat s.toAdd = (c : F9) • rmat a b d e := by
      have h5 : ((tsu s : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) = tmat s.toAdd := rfl
      have h6 : (((theta4 (Multiplicative.ofAdd (a, b, d, e)) : StatedSU 4 3 F9) :
          GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) = rmat a b d e := rfl
      rw [← h5, ← h3, h6]
      refine Matrix.ext fun i j => ?_
      rw [Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul, mul_comm]
    have := tmat_ne_scalar_rmat s.toAdd c a b d e h4
    exact Multiplicative.toAdd.injective this

theorem card_le_nine_of_fixed {s : Multiplicative F9} (hs : s ≠ 1) {B : Subgroup X₀}
    (hB : B ≤ thetaBar.range) (hfix : ∀ b ∈ B, tBar s * b * (tBar s)⁻¹ = b) : Nat.card B ≤ 9 := by
  choose g hg using fun b : B => (hB b.2 : (b : X₀) ∈ thetaBar.range)
  have hfixed : ∀ b : B, act s.toAdd (g b).toAdd = (g b).toAdd := by
    intro b
    have h1 := tBar_conj s (g b)
    rw [hg b, hfix b b.2] at h1
    have h3 := thetaBar_injective ((hg b).trans h1)
    exact (congrArg Multiplicative.toAdd h3).symm
  let f : B → {x : ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 // act s.toAdd x = x} :=
    fun b => ⟨(g b).toAdd, hfixed b⟩
  have hf : Function.Injective f := by
    intro b b' hbb'
    have h1 : (g b).toAdd = (g b').toAdd := congrArg Subtype.val hbb'
    apply Subtype.ext
    rw [← hg b, ← hg b', Multiplicative.toAdd.injective h1]
  have hs0 : s.toAdd ≠ 0 := fun h => hs (Multiplicative.toAdd.injective h)
  calc Nat.card B ≤ Nat.card {x : ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 // act s.toAdd x = x} :=
        Nat.card_le_card_of_injective f hf
    _ = Fintype.card {x : ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 // act s.toAdd x = x} :=
        Nat.card_eq_fintype_card
    _ ≤ 9 := fixed_card_le _ hs0

@[expose] def Psub : Subgroup X₀ where
  carrier := {x | ∃ a ∈ thetaBar.range, ∃ t ∈ tBar.range, x = a * t}
  mul_mem' := by
    rintro _ _ ⟨a, ha, t, ht, rfl⟩ ⟨a', ha', t', ht', rfl⟩
    exact ⟨a * (t * a' * t⁻¹), thetaBar.range.mul_mem ha (tBar_mem_normalizer ht ha'),
      t * t', tBar.range.mul_mem ht ht', by group⟩
  one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
  inv_mem' := by
    rintro _ ⟨a, ha, t, ht, rfl⟩
    exact ⟨t⁻¹ * a⁻¹ * (t⁻¹)⁻¹, tBar_mem_normalizer (tBar.range.inv_mem ht)
      (thetaBar.range.inv_mem ha), t⁻¹, tBar.range.inv_mem ht, by group⟩

theorem A_le_Psub : thetaBar.range ≤ Psub := fun a ha => ⟨a, ha, 1, one_mem _, by simp⟩

theorem inf_AT_trivial {y : X₀} (hA : y ∈ thetaBar.range) (hT : y ∈ tBar.range) : y = 1 := by
  obtain ⟨s, rfl⟩ := hT
  obtain ⟨x, hx⟩ := hA
  have := tBar_eq_thetaBar hx.symm
  rw [this, map_one]

theorem tBar_injective : Function.Injective tBar := by
  rw [injective_iff_map_eq_one]
  intro s hs
  exact tBar_eq_thetaBar (x := 1) (by rw [hs, map_one])

theorem card_range_tBar : Nat.card tBar.range = 9 := by
  rw [Nat.card_congr (MonoidHom.ofInjective tBar_injective).toEquiv.symm,
    Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card, F9.card_eq]

theorem card_Psub : Nat.card Psub = 3 ^ 6 := by
  let f : thetaBar.range × tBar.range → Psub := fun p =>
    ⟨(p.1 : X₀) * p.2, p.1, p.1.2, p.2, p.2.2, rfl⟩
  have hinj : Function.Injective f := by
    rintro ⟨a, t⟩ ⟨a', t'⟩ h
    have h1 : (a : X₀) * t = a' * t' := congrArg Subtype.val h
    have h2 : (a' : X₀)⁻¹ * a = t' * (t : X₀)⁻¹ := by
      calc (a' : X₀)⁻¹ * a = (a' : X₀)⁻¹ * (a * t) * (t : X₀)⁻¹ := by group
        _ = (a' : X₀)⁻¹ * (a' * t') * (t : X₀)⁻¹ := by rw [h1]
        _ = t' * (t : X₀)⁻¹ := by group
    have h3 : (a' : X₀)⁻¹ * a = 1 := inf_AT_trivial
      (thetaBar.range.mul_mem (thetaBar.range.inv_mem a'.2) a.2)
      (h2 ▸ tBar.range.mul_mem t'.2 (tBar.range.inv_mem t.2))
    have ha : (a : X₀) = a' := by
      rw [inv_mul_eq_one] at h3
      exact h3.symm
    have ht : (t : X₀) = t' := by
      rw [ha] at h1
      exact mul_left_cancel h1
    exact Prod.ext (Subtype.ext ha) (Subtype.ext ht)
  have hsurj : Function.Surjective f := by
    rintro ⟨_, a, ha, t, ht, rfl⟩
    exact ⟨⟨⟨a, ha⟩, ⟨t, ht⟩⟩, rfl⟩
  have h1 := Nat.card_le_card_of_injective f hinj
  have h2 := Nat.card_le_card_of_surjective f hsurj
  rw [Nat.card_prod, card_range_thetaBar, card_range_tBar] at h1 h2
  omega

theorem card_le_of_le_Psub {E : Subgroup X₀} (hE : CFSG.Open.IsElemAbelian 3 E) (hEP : E ≤ Psub) :
    Nat.card E ≤ 3 ^ 4 := by
  have := hE.1
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : E) ⟨y, hy⟩)
  by_cases hB : Nat.card (thetaBar.range ⊓ E : Subgroup X₀) ≤ 9
  ·
    have h1 := Subgroup.relIndex_mul_card thetaBar.range E
    have h2 := Subgroup.relIndex_mul_card thetaBar.range Psub
    have hAP : thetaBar.range ⊓ Psub = thetaBar.range := inf_eq_left.2 A_le_Psub
    rw [hAP, card_range_thetaBar, card_Psub] at h2
    have hrel : thetaBar.range.relIndex Psub = 9 := by
      have : thetaBar.range.relIndex Psub * 3 ^ 4 = 9 * 3 ^ 4 := by rw [h2]; norm_num
      exact Nat.eq_of_mul_eq_mul_right (by norm_num) this
    have h3 := Subgroup.relIndex_le_of_le_right (H := thetaBar.range) hEP (by rw [hrel]; norm_num)
    rw [hrel] at h3
    rw [← h1]
    calc _ ≤ 9 * 9 := Nat.mul_le_mul h3 hB
      _ = 3 ^ 4 := by norm_num
  ·
    push Not at hB
    have hEA : E ≤ thetaBar.range := by
      intro e he
      obtain ⟨a, ha, t, ⟨s, rfl⟩, rfl⟩ := hEP he
      by_cases hs : s = 1
      · rw [hs, map_one, mul_one]
        exact ha
      · exfalso
        have hfix : ∀ b ∈ (thetaBar.range ⊓ E : Subgroup X₀), tBar s * b * (tBar s)⁻¹ = b := by
          rintro b ⟨hbA, hbE⟩
          have h1 := hcomm _ he b hbE
          have h2 : a * tBar s * b = b * (a * tBar s) := h1
          have h3 : tBar s * b * (tBar s)⁻¹ ∈ thetaBar.range :=
            tBar_mem_normalizer ⟨s, rfl⟩ hbA
          have h4 := thetaBar_comm a _ ha h3
          calc tBar s * b * (tBar s)⁻¹ = a * (tBar s * b * (tBar s)⁻¹) * a⁻¹ :=
                (mul_inv_eq_iff_eq_mul.mpr h4).symm
            _ = a * tBar s * b * (a * tBar s)⁻¹ := by group
            _ = b := mul_inv_eq_iff_eq_mul.mpr h2
        have := card_le_nine_of_fixed hs inf_le_left hfix
        omega
    calc Nat.card E ≤ Nat.card thetaBar.range := Subgroup.card_le_of_le hEA
      _ = 3 ^ 4 := card_range_thetaBar

end U43Six





open U43Six in
theorem card_elemAbelian_le_X₀ {E : Subgroup X₀} (hE : CFSG.Open.IsElemAbelian 3 E) :
    Nat.card E ≤ 3 ^ 4 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfac : (Nat.card X₀).factorization 3 = 6 := by
    rw [CFSG.LieType.Multipliers.U43.card_X₀]
    have h6 := (Nat.prime_three.pow_dvd_iff_le_factorization (by norm_num : (3265920 : ℕ) ≠ 0)).1
      (by norm_num : 3 ^ 6 ∣ 3265920)
    have h7 : ¬ 7 ≤ (3265920 : ℕ).factorization 3 := fun h =>
      absurd ((Nat.prime_three.pow_dvd_iff_le_factorization (by norm_num : (3265920 : ℕ) ≠ 0)).2 h)
        (by norm_num)
    omega
  let P0 : Sylow 3 X₀ := Sylow.ofCard Psub (by rw [card_Psub, hfac])
  have hEp : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    exact hE.2 x x.2)⟩
  obtain ⟨Q, hEQ⟩ := hEp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X₀ P0 Q
  have hle : E.map (MulAut.conj g⁻¹).toMonoidHom ≤ Psub := by
    rintro _ ⟨x, hx, rfl⟩
    have hxQ : x ∈ (Q : Subgroup X₀) := hEQ hx
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxQ
    simp only [map_inv, MulAut.inv_def] at hxQ ⊢
    simp at hxQ ⊢
    exact hxQ
  have h := card_le_of_le_Psub (CFSG.SectionRank.isElemAbelian_map hE _) hle
  rwa [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective] at h

theorem pRank_X₀_le_four : CFSG.Open.pRank 3 (⊤ : Subgroup X₀) ≤ 4 :=
  CFSG.SectionRank.pRank_le (by norm_num) fun _ _ hE => card_elemAbelian_le_X₀ hE

end CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier
