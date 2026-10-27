module

public import CFSG.RankThree.PartOne.KE8F.Stab5Fix
public import CFSG.LieType.SeitzGeneration.ExcHigh.E7SevenWeylPair

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHigh.E8FiveSq

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootSpace CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KE8F CFSG.RankThree.Lattice
open CFSG.RankThree.E6 (charVal charVal_single charVal_add charVal_neg charVal_smul weylMatrix
  weylMatrix_mulVec eq_of_smul_single_eq)
open scoped Matrix

set_option linter.unusedSectionVars false


section Columns

variable {τ : Tag} {R : Type*} [CommRing R]

theorem charVal_add_left (z z' : Fin τ.rank → R) (x : Fin τ.rank → ℤ) :
    charVal (z + z') x = charVal z x + charVal z' x := by
  simp only [charVal, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem charVal_smul_left (a : R) (z : Fin τ.rank → R) (x : Fin τ.rank → ℤ) :
    charVal (a • z) x = a * charVal z x := by
  simp only [charVal, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem trCol_add (x : WeylGroup Tag.E8) (z z' : Fin Tag.E8.rank → ZMod 5) :
    trCol x (z + z') = trCol x z + trCol x z' := by
  funext i
  simp only [trCol, Pi.add_apply, charVal_add_left]

theorem trCol_smul (x : WeylGroup Tag.E8) (a : ZMod 5) (z : Fin Tag.E8.rank → ZMod 5) :
    trCol x (a • z) = a • trCol x z := by
  funext i
  simp only [trCol, Pi.smul_apply, smul_eq_mul, charVal_smul_left]

theorem fin_two_ext {f g : Fin 2 → ZMod 5} (h0 : f 0 = g 0) (h1 : f 1 = g 1) : f = g := by
  funext k
  fin_cases k
  exacts [h0, h1]

theorem exists_eq_add_of_indep {c₀ c₁ : Fin 2 → ZMod 5}
    (h : ∀ a b : ZMod 5, a • c₀ + b • c₁ = 0 → a = 0 ∧ b = 0) (e : Fin 2 → ZMod 5) :
    ∃ a b : ZMod 5, e = a • c₀ + b • c₁ := by
  have hD : c₀ 0 * c₁ 1 - c₀ 1 * c₁ 0 ≠ 0 := by
    intro hD
    have h1 := h (c₁ 1) (-(c₀ 1)) (fin_two_ext
      (by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
          linear_combination hD)
      (by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]; ring))
    have h2 := h (c₁ 0) (-(c₀ 0)) (fin_two_ext
      (by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]; ring)
      (by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
          linear_combination (-1 : ZMod 5) * hD))
    have h00 : c₀ 0 = 0 := neg_eq_zero.1 h2.2
    have h01 : c₀ 1 = 0 := neg_eq_zero.1 h1.2
    have h3 := h 1 0 (fin_two_ext
      (by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, h00]; ring)
      (by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, h01]; ring))
    exact absurd h3.1 (by decide)
  obtain ⟨E, hE⟩ : ∃ E : ZMod 5, (c₀ 0 * c₁ 1 - c₀ 1 * c₁ 0) * E = 1 := by
    generalize c₀ 0 * c₁ 1 - c₀ 1 * c₁ 0 = D at hD
    revert D
    decide
  refine ⟨(e 0 * c₁ 1 - e 1 * c₁ 0) * E, (c₀ 0 * e 1 - c₀ 1 * e 0) * E, fin_two_ext ?_ ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (-e 0) * hE
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (-e 1) * hE

end Columns

section Average

theorem le_closure_of_card {τ : Tag} {p : ℕ} [Fact p.Prime] (z₀ z₁ : Fin τ.rank → ZMod p)
    (H : Subgroup (WeylGroup τ)) (hH : H ≤ dualWeylStabilizer z₀ ⊓ dualWeylStabilizer z₁)
    (hU : ¬ p ∣ Nat.card H) :
    H ≤ Subgroup.closure {s | ∃ α ∈ rootKernel z₀ ∩ rootKernel z₁, s = rootReflection α} := by
  classical
  have : Fintype H := Fintype.ofFinite _
  have hcard : (Fintype.card H : ZMod p) ≠ 0 := by
    intro h
    rw [ZMod.natCast_eq_zero_iff, ← Nat.card_eq_fintype_card] at h
    exact hU h
  have hz : ∀ z : Fin τ.rank → ZMod p, H ≤ dualWeylStabilizer z →
      ∀ α, charVal (avgColumn H (intLift z)) α = 0 → charVal z α = 0 := by
    intro z hHz α h
    have h' := charVal_avgColumn_cast hHz α
    rw [h, Int.cast_zero, eq_comm] at h'
    exact (mul_eq_zero.1 h').resolve_left hcard
  intro w hw
  have hwinv : w⁻¹ ∈ H := H.inv_mem hw
  have hfix : w ∈ weylStabilizer τ (dualVector (avgColumn H (intLift z₀)) +
      Real.sqrt 2 • dualVector (avgColumn H (intLift z₁))) := by
    rw [mem_weylStabilizer, map_add, map_smul,
      weylAct_dualVector_eq fun v => charVal_avgColumn_smul _ hwinv v,
      weylAct_dualVector_eq fun v => charVal_avgColumn_smul _ hwinv v]
  rw [(exceptional_Lang_Weyl_chamber_point_stabilizers τ).2.2.2.2.2] at hfix
  refine Subgroup.closure_mono ?_ hfix
  rintro _ ⟨α, hα, h0, rfl⟩
  rw [inner_add_right, real_inner_smul_right, inner_ofLattice_dualVector,
    inner_ofLattice_dualVector] at h0
  obtain ⟨h0', h1'⟩ := int_eq_zero_of_add_sqrt_two_mul h0
  exact ⟨α, ⟨⟨hα, hz z₀ (hH.trans inf_le_left) α h0'⟩,
    ⟨hα, hz z₁ (hH.trans inf_le_right) α h1'⟩⟩, rfl⟩

theorem eq_bot_of_card {τ : Tag} {p : ℕ} [Fact p.Prime] {z₀ z₁ : Fin τ.rank → ZMod p}
    (hreg : ∀ α, IsRoot τ α → charVal z₀ α = 0 → charVal z₁ α = 0 → False)
    (H : Subgroup (WeylGroup τ)) (hH : H ≤ dualWeylStabilizer z₀ ⊓ dualWeylStabilizer z₁)
    (hU : ¬ p ∣ Nat.card H) : H = ⊥ := by
  refine eq_bot_iff.2 ((le_closure_of_card z₀ z₁ H hH hU).trans ?_)
  rw [Subgroup.closure_le]
  rintro _ ⟨α, ⟨⟨hα, h0⟩, ⟨-, h1⟩⟩, rfl⟩
  exact (hreg α hα h0 h1).elim

theorem pow_twentyFive_eq_one {z₀ z₁ : Fin Tag.E8.rank → ZMod 5}
    (hreg : ∀ α, IsRoot Tag.E8 α → charVal z₀ α = 0 → charVal z₁ α = 0 → False)
    {V : WeylGroup Tag.E8} (hV₀ : V ∈ dualWeylStabilizer z₀) (hV₁ : V ∈ dualWeylStabilizer z₁) :
    V ^ 25 = 1 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fintype (WeylGroup Tag.E8) := Fintype.ofFinite _
  have hW : Nat.card (WeylGroup Tag.E8) = 25 * 27869184 := by
    have := (CFSG.RankThree.Chevalley.E8_weyl_length_polynomial).2
    omega
  have hpow : (V ^ 25) ^ 27869184 = 1 := by
    rw [← pow_mul, ← hW, pow_card_eq_one']
  have hcard : ¬ 5 ∣ Nat.card (Subgroup.zpowers (V ^ 25)) := by
    rw [Nat.card_zpowers]
    intro h
    have := h.trans (orderOf_dvd_of_pow_eq_one hpow)
    omega
  have hle : Subgroup.zpowers (V ^ 25) ≤ dualWeylStabilizer z₀ ⊓ dualWeylStabilizer z₁ := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_inf.2 ⟨Subgroup.pow_mem _ hV₀ 25, Subgroup.pow_mem _ hV₁ 25⟩
  have hmem : V ^ 25 ∈ Subgroup.zpowers (V ^ 25) := Subgroup.mem_zpowers _
  rw [eq_bot_of_card hreg _ hle hcard, Subgroup.mem_bot] at hmem
  exact hmem

end Average

section Form

@[expose] def e8Form (x y : Fin Tag.E8.rank → ℤ) : ℤ :=
  x ⬝ᵥ (Tag.E8.symmetrizedCartan *ᵥ y)

theorem e8Form_smul (g : WeylGroup Tag.E8) (x y : Fin Tag.E8.rank → ℤ) :
    e8Form (g • x) (g • y) = e8Form x y :=
  rootForm_smul g x y

theorem e8Form_add_right (x y y' : Fin Tag.E8.rank → ℤ) :
    e8Form x (y + y') = e8Form x y + e8Form x y' := by
  simp only [e8Form, Matrix.mulVec_add, dotProduct_add]

theorem e8Form_smul_right (x : Fin Tag.E8.rank → ℤ) (c : ℤ) (y : Fin Tag.E8.rank → ℤ) :
    e8Form x (c • y) = c * e8Form x y := by
  simp only [e8Form, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem e8Form_sub_left (x x' y : Fin Tag.E8.rank → ℤ) :
    e8Form (x - x') y = e8Form x y - e8Form x' y := by
  simp only [e8Form, sub_dotProduct]

theorem e8Form_smul_left (c : ℤ) (x y : Fin Tag.E8.rank → ℤ) :
    e8Form (c • x) y = c * e8Form x y := by
  simp only [e8Form, smul_dotProduct, smul_eq_mul]

theorem weyl_smul_zsmul (g : WeylGroup Tag.E8) (c : ℤ) (x : Fin Tag.E8.rank → ℤ) :
    g • (c • x) = c • (g • x) := by
  rw [← weylMatrix_mulVec, ← weylMatrix_mulVec, Matrix.mulVec_smul]

@[expose] def colOf (l : Fin Tag.E8.rank → ℤ) : Fin Tag.E8.rank → ZMod 5 :=
  fun i => (((l ᵥ* Tag.E8.symmetrizedCartan) i : ℤ) : ZMod 5)

theorem charVal_colOf (l v : Fin Tag.E8.rank → ℤ) :
    charVal (colOf l) v = ((e8Form l v : ℤ) : ZMod 5) := by
  rw [e8Form, Matrix.dotProduct_mulVec, dotProduct_comm]
  simp only [charVal, colOf, dotProduct, Int.cast_sum, Int.cast_mul]

@[expose] def e8CartanInv : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  !![4, 5, 7, 10, 8, 6, 4, 2; 5, 8, 10, 15, 12, 9, 6, 3; 7, 10, 14, 20, 16, 12, 8, 4;
    10, 15, 20, 30, 24, 18, 12, 6; 8, 12, 16, 24, 20, 15, 10, 5; 6, 9, 12, 18, 15, 12, 8, 4;
    4, 6, 8, 12, 10, 8, 6, 3; 2, 3, 4, 6, 5, 4, 3, 2]

theorem symmetrizedCartan_mul_e8CartanInv :
    Tag.E8.symmetrizedCartan * e8CartanInv = 1 := by
  decide +kernel

theorem exists_five_smul_of_form {x : Fin Tag.E8.rank → ℤ}
    (hx : ∀ v, ((e8Form x v : ℤ) : ZMod 5) = 0) :
    ∃ a : Fin Tag.E8.rank → ℤ, x = (5 : ℤ) • a := by
  have h1 : ∀ i, (5 : ℤ) ∣ (x ᵥ* Tag.E8.symmetrizedCartan) i := fun i => by
    have := hx (Pi.single i 1)
    rw [e8Form, Matrix.dotProduct_mulVec, dotProduct_single_one] at this
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).1 this
  choose b hb using h1
  refine ⟨b ᵥ* e8CartanInv, ?_⟩
  have hxb : x ᵥ* Tag.E8.symmetrizedCartan = (5 : ℤ) • b := funext fun i => by
    rw [Pi.smul_apply, smul_eq_mul, hb i]
  calc x = x ᵥ* (Tag.E8.symmetrizedCartan * e8CartanInv) := by
        rw [symmetrizedCartan_mul_e8CartanInv, Matrix.vecMul_one]
    _ = (x ᵥ* Tag.E8.symmetrizedCartan) ᵥ* e8CartanInv := (Matrix.vecMul_vecMul _ _ _).symm
    _ = (5 : ℤ) • (b ᵥ* e8CartanInv) := by rw [hxb, Matrix.smul_vecMul]

theorem form_contra {h w : WeylGroup Tag.E8} (hwh : w * h = h * w)
    {l₀ l₁ d₀ d₁ : Fin Tag.E8.rank → ℤ}
    (hd₀ : h • l₀ = l₀ + (5 : ℤ) • d₀) (hd₁ : h • l₁ = l₁ + (5 : ℤ) • d₁)
    (hβ : ((e8Form l₀ d₁ : ℤ) : ZMod 5) ≠ 0) {r : ZMod 5} (hr : r ^ 2 = -1)
    (h₀ : ∀ v, charVal (colOf l₀) (w • v) = r * charVal (colOf l₀) v)
    (h₁ : ∀ v, charVal (colOf l₁) (w • v) = r * charVal (colOf l₁) v) : False := by
  set ρ : ℤ := ((r.val : ℕ) : ℤ) with hρ
  have hρr : ((ρ : ℤ) : ZMod 5) = r := by
    rw [hρ, Int.cast_natCast, ZMod.natCast_zmod_val]
  have e₀ : ∀ v, ((e8Form l₀ (w • v) : ℤ) : ZMod 5) = r * ((e8Form l₀ v : ℤ) : ZMod 5) :=
    fun v => by
      rw [← charVal_colOf, ← charVal_colOf]
      exact h₀ v
  have e₁ : ∀ v, ((e8Form l₁ v : ℤ) : ZMod 5) = r * ((e8Form (w • l₁) v : ℤ) : ZMod 5) :=
    fun v => by
      have := h₁ (w⁻¹ • v)
      rw [charVal_colOf, charVal_colOf, smul_inv_smul] at this
      rw [this, ← e8Form_smul w l₁ (w⁻¹ • v), smul_inv_smul]
  obtain ⟨a, ha⟩ := exists_five_smul_of_form (x := l₁ - ρ • (w • l₁)) fun v => by
    rw [e8Form_sub_left, e8Form_smul_left, Int.cast_sub, Int.cast_mul, hρr, e₁ v, sub_self]
  have hl₁ : l₁ = ρ • (w • l₁) + (5 : ℤ) • a := by
    rw [← ha]
    abel
  have hh₀ : h⁻¹ • l₀ = l₀ - (5 : ℤ) • (h⁻¹ • d₀) := by
    have := congrArg (h⁻¹ • ·) hd₀
    simp only [inv_smul_smul, smul_add, weyl_smul_zsmul] at this
    rw [eq_sub_iff_add_eq]
    exact this.symm
  have hhw : h • (w • l₁) = w • l₁ + (5 : ℤ) • (w • d₁) := by
    rw [← mul_smul, ← hwh, mul_smul, hd₁, smul_add, weyl_smul_zsmul]
  have I1 : (5 : ℤ) * e8Form l₀ d₁ = e8Form l₀ (h • l₁) - e8Form l₀ l₁ := by
    rw [hd₁, e8Form_add_right, e8Form_smul_right]
    ring
  have I2 : e8Form l₀ (h • l₁) = ρ * e8Form l₀ (h • (w • l₁)) + 5 * e8Form l₀ (h • a) := by
    conv_lhs => rw [hl₁]
    rw [smul_add, weyl_smul_zsmul, weyl_smul_zsmul, e8Form_add_right, e8Form_smul_right,
      e8Form_smul_right]
  have I3 : e8Form l₀ l₁ = ρ * e8Form l₀ (w • l₁) + 5 * e8Form l₀ a := by
    conv_lhs => rw [hl₁]
    rw [e8Form_add_right, e8Form_smul_right, e8Form_smul_right]
  have I4 : e8Form l₀ (h • (w • l₁)) = e8Form l₀ (w • l₁) + 5 * e8Form l₀ (w • d₁) := by
    rw [hhw, e8Form_add_right, e8Form_smul_right]
  have I5 : e8Form l₀ (h • a) = e8Form l₀ a - 5 * e8Form (h⁻¹ • d₀) a := by
    rw [← e8Form_smul h⁻¹ l₀ (h • a), inv_smul_smul, hh₀, e8Form_sub_left, e8Form_smul_left]
  have I : e8Form l₀ d₁ = ρ * e8Form l₀ (w • d₁) - 5 * e8Form (h⁻¹ • d₀) a := by
    have h5 : (5 : ℤ) * e8Form l₀ d₁ =
        5 * (ρ * e8Form l₀ (w • d₁) - 5 * e8Form (h⁻¹ • d₀) a) := by
      rw [I1, I2, I3, I4, I5]
      ring
    exact mul_left_cancel₀ (by norm_num) h5
  have hc := congrArg (Int.cast : ℤ → ZMod 5) I
  have h5 : ((5 : ℤ) : ZMod 5) = 0 := by decide
  rw [Int.cast_sub, Int.cast_mul, Int.cast_mul, hρr, e₀ d₁, h5, zero_mul, sub_zero,
    ← mul_assoc, ← sq, hr, neg_one_mul] at hc
  have key : ∀ t : ZMod 5, t = -t → t = 0 := by decide
  exact hβ (key _ hc)

end Form

section Exclusion

structure EigenPair (w : WeylGroup Tag.E8) (r : ZMod 5) (z₀ z₁ : Fin Tag.E8.rank → ZMod 5) :
    Prop where
  ind : ∀ a b : ZMod 5, a • z₀ + b • z₁ = 0 → a = 0 ∧ b = 0
  eig₀ : ∀ v, charVal z₀ (w • v) = r * charVal z₀ v
  eig₁ : ∀ v, charVal z₁ (w • v) = r * charVal z₁ v
  reg : ∀ α, IsRoot Tag.E8 α → charVal z₀ α = 0 → charVal z₁ α = 0 → False

theorem EigenPair.conj {w : WeylGroup Tag.E8} {r : ZMod 5} {z₀ z₁ : Fin Tag.E8.rank → ZMod 5}
    (hE : EigenPair w r z₀ z₁) (x : WeylGroup Tag.E8) :
    EigenPair (x * w * x⁻¹) r (trCol x z₀) (trCol x z₁) where
  ind a b h := hE.ind a b (trCol_eq_zero (by rw [trCol_add, trCol_smul, trCol_smul]; exact h))
  eig₀ v := by rw [charVal_trCol, charVal_trCol, mul_smul, mul_smul, inv_smul_smul, hE.eig₀]
  eig₁ v := by rw [charVal_trCol, charVal_trCol, mul_smul, mul_smul, inv_smul_smul, hE.eig₁]
  reg α hα h₀ h₁ := hE.reg (x⁻¹ • α) (IsRoot.smul hα x⁻¹) (by rwa [charVal_trCol] at h₀)
    (by rwa [charVal_trCol] at h₁)

theorem mem_fixSet_add {g : WeylGroup Tag.E8} {z z' : Fin Tag.E8.rank → ZMod 5}
    (hz : z ∈ fixSet g) (hz' : z' ∈ fixSet g) (a b : ZMod 5) : a • z + b • z' ∈ fixSet g := by
  show g ∈ dualWeylStabilizer _
  intro v
  simp only [charVal_add_left, charVal_smul_left]
  rw [mem_dualWeylStabilizer.1 hz v, mem_dualWeylStabilizer.1 hz' v]

theorem zero_mem_fixSet (g : WeylGroup Tag.E8) : (0 : Fin Tag.E8.rank → ZMod 5) ∈ fixSet g := by
  show g ∈ dualWeylStabilizer _
  intro v
  simp [charVal]

theorem not_eigenPair_of_param {g w : WeylGroup Tag.E8} (hwg : w * g = g * w)
    {P : (Fin 2 → ZMod 5) → Fin Tag.E8.rank → ZMod 5}
    (hP : ∀ z ∈ fixSet g, z = P ![z 4, z 7])
    {l₀ l₁ d₀ d₁ : Fin Tag.E8.rank → ℤ}
    (hd₀ : g • l₀ = l₀ + (5 : ℤ) • d₀) (hd₁ : g • l₁ = l₁ + (5 : ℤ) • d₁)
    (hc₀ : colOf l₀ = P ![1, 0]) (hc₁ : colOf l₁ = P ![0, 1])
    (hβ : ((e8Form l₀ d₁ : ℤ) : ZMod 5) ≠ 0) {r : ZMod 5} (hr : r ^ 2 = -1)
    {z₀ z₁ : Fin Tag.E8.rank → ZMod 5} (hE : EigenPair w r z₀ z₁)
    (hz₀ : z₀ ∈ fixSet g) (hz₁ : z₁ ∈ fixSet g) : False := by
  have hcoord : ∀ a b : ZMod 5, ![(a • z₀ + b • z₁) 4, (a • z₀ + b • z₁) 7] =
      a • ![z₀ 4, z₀ 7] + b • ![z₁ 4, z₁ 7] := fun a b =>
    fin_two_ext (by simp) (by simp)
  have hP0 : P 0 = 0 :=
    calc P 0 = P ![(0 : Fin Tag.E8.rank → ZMod 5) 4, (0 : Fin Tag.E8.rank → ZMod 5) 7] :=
          congrArg P (fin_two_ext rfl rfl)
      _ = 0 := (hP 0 (zero_mem_fixSet g)).symm
  have hind : ∀ a b : ZMod 5, a • ![z₀ 4, z₀ 7] + b • ![z₁ 4, z₁ 7] = 0 → a = 0 ∧ b = 0 := by
    intro a b h
    apply hE.ind a b
    rw [hP _ (mem_fixSet_add hz₀ hz₁ a b), hcoord, h, hP0]
  have heig : ∀ e : Fin 2 → ZMod 5, ∀ v, charVal (P e) (w • v) = r * charVal (P e) v := by
    intro e v
    obtain ⟨a, b, hab⟩ := exists_eq_add_of_indep hind e
    have hPe : P e = a • z₀ + b • z₁ := by
      rw [hab, ← hcoord]
      exact (hP _ (mem_fixSet_add hz₀ hz₁ a b)).symm
    rw [hPe]
    simp only [charVal_add_left, charVal_smul_left, hE.eig₀, hE.eig₁]
    ring
  exact form_contra hwg hd₀ hd₁ hβ hr (by rw [hc₀]; exact heig _) (by rw [hc₁]; exact heig _)

@[expose] def e8SqL0 : Fin Tag.E8.rank → ℤ := ![8, 12, 16, 24, 20, 15, 10, 5]

@[expose] def e8SqL1 : ℕ → Fin Tag.E8.rank → ℤ
  | 1 => ![-116, -171, -229, -339, -275, -211, -143, -71]
  | 2 => ![-64, -95, -127, -189, -155, -121, -83, -41]
  | 3 => ![-142, -209, -280, -414, -335, -256, -173, -86]
  | _ => ![-90, -133, -178, -264, -215, -166, -113, -56]

@[expose] def e8SqD0 : ℕ → Fin Tag.E8.rank → ℤ
  | 1 => ![-2, -3, -4, -6, -5, -4, -3, -2]
  | 2 => ![-2, -3, -4, -6, -5, -4, -3, -1]
  | 3 => ![-2, -3, -4, -6, -5, -4, -2, -1]
  | _ => ![-2, -3, -4, -6, -5, -3, -2, -1]

@[expose] def e8SqD1 : ℕ → Fin Tag.E8.rank → ℤ
  | 1 => ![28, 39, 53, 78, 64, 52, 40, 27]
  | 2 => ![16, 23, 31, 46, 38, 32, 25, 9]
  | 3 => ![38, 53, 72, 106, 87, 71, 37, 18]
  | _ => ![24, 34, 46, 68, 56, 35, 23, 11]

theorem not_eigenPair_h1 {w : WeylGroup Tag.E8} (hwg : w * e8FiveH 1 = e8FiveH 1 * w)
    {r : ZMod 5} (hr : r ^ 2 = -1) {z₀ z₁ : Fin Tag.E8.rank → ZMod 5}
    (hE : EigenPair w r z₀ z₁) (hz₀ : z₀ ∈ fixSet (e8FiveH 1))
    (hz₁ : z₁ ∈ fixSet (e8FiveH 1)) : False :=
  not_eigenPair_of_param hwg (fun _ hz => fixSet_h1_param hz)
    (l₀ := e8SqL0) (l₁ := e8SqL1 1) (d₀ := e8SqD0 1) (d₁ := e8SqD1 1)
    (by rw [← weylMatrix_mulVec, weylMatrix_e8FiveH]; decide +kernel)
    (by rw [← weylMatrix_mulVec, weylMatrix_e8FiveH]; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hr hE hz₀ hz₁

theorem not_eigenPair_h2 {w : WeylGroup Tag.E8} (hwg : w * e8FiveH 2 = e8FiveH 2 * w)
    {r : ZMod 5} (hr : r ^ 2 = -1) {z₀ z₁ : Fin Tag.E8.rank → ZMod 5}
    (hE : EigenPair w r z₀ z₁) (hz₀ : z₀ ∈ fixSet (e8FiveH 2))
    (hz₁ : z₁ ∈ fixSet (e8FiveH 2)) : False :=
  not_eigenPair_of_param hwg (fun _ hz => fixSet_h2_param hz)
    (l₀ := e8SqL0) (l₁ := e8SqL1 2) (d₀ := e8SqD0 2) (d₁ := e8SqD1 2)
    (by rw [← weylMatrix_mulVec, weylMatrix_e8FiveH]; decide +kernel)
    (by rw [← weylMatrix_mulVec, weylMatrix_e8FiveH]; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hr hE hz₀ hz₁

theorem not_eigenPair_h3 {w : WeylGroup Tag.E8} (hwg : w * e8FiveH 3 = e8FiveH 3 * w)
    {r : ZMod 5} (hr : r ^ 2 = -1) {z₀ z₁ : Fin Tag.E8.rank → ZMod 5}
    (hE : EigenPair w r z₀ z₁) (hz₀ : z₀ ∈ fixSet (e8FiveH 3))
    (hz₁ : z₁ ∈ fixSet (e8FiveH 3)) : False :=
  not_eigenPair_of_param hwg (fun _ hz => fixSet_h3_param hz)
    (l₀ := e8SqL0) (l₁ := e8SqL1 3) (d₀ := e8SqD0 3) (d₁ := e8SqD1 3)
    (by rw [← weylMatrix_mulVec, weylMatrix_e8FiveH]; decide +kernel)
    (by rw [← weylMatrix_mulVec, weylMatrix_e8FiveH]; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hr hE hz₀ hz₁

theorem not_eigenPair_h4 {w : WeylGroup Tag.E8} (hwg : w * e8FiveH 4 = e8FiveH 4 * w)
    {r : ZMod 5} (hr : r ^ 2 = -1) {z₀ z₁ : Fin Tag.E8.rank → ZMod 5}
    (hE : EigenPair w r z₀ z₁) (hz₀ : z₀ ∈ fixSet (e8FiveH 4))
    (hz₁ : z₁ ∈ fixSet (e8FiveH 4)) : False :=
  not_eigenPair_of_param hwg (fun _ hz => fixSet_h4_param hz)
    (l₀ := e8SqL0) (l₁ := e8SqL1 4) (d₀ := e8SqD0 4) (d₁ := e8SqD1 4)
    (by rw [← weylMatrix_mulVec, weylMatrix_e8FiveH]; decide +kernel)
    (by rw [← weylMatrix_mulVec, weylMatrix_e8FiveH]; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hr hE hz₀ hz₁

theorem not_eigenPair_of_fix {w : WeylGroup Tag.E8} {r : ZMod 5} (hr : r ^ 2 = -1)
    {z₀ z₁ : Fin Tag.E8.rank → ZMod 5} (hE : EigenPair w r z₀ z₁) (i j : Fin 5)
    (hij : i ≠ 0 ∨ j ≠ 0)
    (hwy : w * (e8FiveG1 ^ (i : ℕ) * e8FiveG2 ^ (j : ℕ)) =
      e8FiveG1 ^ (i : ℕ) * e8FiveG2 ^ (j : ℕ) * w)
    (hz₀ : z₀ ∈ fixSet (e8FiveG1 ^ (i : ℕ) * e8FiveG2 ^ (j : ℕ)))
    (hz₁ : z₁ ∈ fixSet (e8FiveG1 ^ (i : ℕ) * e8FiveG2 ^ (j : ℕ))) : False := by
  by_cases hi : (i : ℕ) = 0
  ·
    have hj : (j : ℕ) ≠ 0 := by
      rcases hij with h | h
      · exact absurd (Fin.ext hi) h
      · exact fun h0 => h (Fin.ext h0)
    have hw : e8FiveG1 ^ (i : ℕ) * e8FiveG2 ^ (j : ℕ) = e8FiveG2 ^ (j : ℕ) := by
      rw [hi, pow_zero, one_mul]
    have hjd : ¬ 5 ∣ (j : ℕ) := fun h => hj (Nat.eq_zero_of_dvd_of_lt h j.2)
    have h7 : ∀ z ∈ fixSet (e8FiveG1 ^ (i : ℕ) * e8FiveG2 ^ (j : ℕ)), z 7 = 0 := fun z hz => by
      rw [congrFun (fixSet_g2_param (fixSet_subset_of_pow e8FiveG2_pow hjd hw hz)) 7]
      rfl
    exact hE.reg (Pi.single 7 1) (isRoot_single _ 7) (by rw [charVal_single]; exact h7 z₀ hz₀)
      (by rw [charVal_single]; exact h7 z₁ hz₁)
  have hid : ¬ 5 ∣ (i : ℕ) := fun h => hi (Nat.eq_zero_of_dvd_of_lt h i.2)
  by_cases hj : (j : ℕ) = 0
  ·
    have hw : e8FiveG1 ^ (i : ℕ) * e8FiveG2 ^ (j : ℕ) = (e8FiveH 0) ^ (i : ℕ) := by
      rw [hj, pow_zero, mul_one, e8FiveH, pow_zero, mul_one]
    have h0 : ∀ z ∈ fixSet (e8FiveG1 ^ (i : ℕ) * e8FiveG2 ^ (j : ℕ)), z 0 = 0 := fun z hz => by
      rw [congrFun (fixSet_h0_param (fixSet_subset_of_pow (e8FiveH_pow_five 0) hid hw hz)) 0]
      rfl
    exact hE.reg (Pi.single 0 1) (isRoot_single _ 0) (by rw [charVal_single]; exact h0 z₀ hz₀)
      (by rw [charVal_single]; exact h0 z₁ hz₁)
  ·
    have hex : ∀ i j : Fin 5, (i : ℕ) ≠ 0 → ∃ m : Fin 5, ((m : ℕ) * i) % 5 = j := by decide
    obtain ⟨m, hm⟩ := hex i j hi
    have hw : e8FiveG1 ^ (i : ℕ) * e8FiveG2 ^ (j : ℕ) = (e8FiveH m) ^ (i : ℕ) := by
      have hc : Commute e8FiveG1 (e8FiveG2 ^ (m : ℕ)) := Commute.pow_right e8Five_comm _
      rw [e8FiveH, hc.mul_pow, ← pow_mul, pow_eq_pow_mod ((m : ℕ) * (i : ℕ)) e8FiveG2_pow, hm]
    obtain ⟨n, hn⟩ := exists_pow_eq_of_not_dvd (e8FiveH_pow_five m) hid
    have hwh : w * e8FiveH m = e8FiveH m * w := by
      have hcw : Commute w ((e8FiveH m) ^ (i : ℕ)) := by
        rw [← hw]
        exact hwy
      rw [← hn]
      exact (hcw.pow_right n).eq
    have hz₀' := fixSet_subset_of_pow (e8FiveH_pow_five m) hid hw hz₀
    have hz₁' := fixSet_subset_of_pow (e8FiveH_pow_five m) hid hw hz₁
    fin_cases m
    · simp at hm
      omega
    · exact not_eigenPair_h1 hwh hr hE hz₀' hz₁'
    · exact not_eigenPair_h2 hwh hr hE hz₀' hz₁'
    · exact not_eigenPair_h3 hwh hr hE hz₀' hz₁'
    · exact not_eigenPair_h4 hwh hr hE hz₀' hz₁'

theorem not_eigenPair_of_orderOf {w y : WeylGroup Tag.E8} {r : ZMod 5} (hr : r ^ 2 = -1)
    {z₀ z₁ : Fin Tag.E8.rank → ZMod 5} (hE : EigenPair w r z₀ z₁) (hy : orderOf y = 5)
    (hwy : w * y = y * w) (hy₀ : y ∈ dualWeylStabilizer z₀)
    (hy₁ : y ∈ dualWeylStabilizer z₁) : False := by
  obtain ⟨x, i, j, hxy, hij⟩ := exists_conj_into_P hy
  have hz₀ : trCol x z₀ ∈ fixSet (e8FiveG1 ^ (i : ℕ) * e8FiveG2 ^ (j : ℕ)) := by
    rw [← hxy]
    exact (mem_fixSet_trCol x y z₀).1 hy₀
  have hz₁ : trCol x z₁ ∈ fixSet (e8FiveG1 ^ (i : ℕ) * e8FiveG2 ^ (j : ℕ)) := by
    rw [← hxy]
    exact (mem_fixSet_trCol x y z₁).1 hy₁
  have hwy' : x * w * x⁻¹ * (e8FiveG1 ^ (i : ℕ) * e8FiveG2 ^ (j : ℕ)) =
      e8FiveG1 ^ (i : ℕ) * e8FiveG2 ^ (j : ℕ) * (x * w * x⁻¹) := by
    rw [← hxy]
    calc x * w * x⁻¹ * (x * y * x⁻¹) = x * (w * y) * x⁻¹ := by group
      _ = x * (y * w) * x⁻¹ := by rw [hwy]
      _ = x * y * x⁻¹ * (x * w * x⁻¹) := by group
  exact not_eigenPair_of_fix hr (hE.conj x) i j hij hwy' hz₀ hz₁

end Exclusion

theorem e8FiveSquare_weyl {w w₀ : WeylGroup Tag.E8}
    (hw₀ : ∀ u : Fin Tag.E8.rank → ℤ, w₀ • u = -u) {r : ZMod 5} (hr : r ^ 2 = -1)
    {z₀ z₁ : Fin Tag.E8.rank → ZMod 5} (hE : EigenPair w r z₀ z₁) :
    ∀ u : Fin Tag.E8.rank → ℤ, w • (w • u) = -u := by
  have hVfix : ∀ z : Fin Tag.E8.rank → ZMod 5, (∀ v, charVal z (w • v) = r * charVal z v) →
      w₀ * w * w ∈ dualWeylStabilizer z := by
    intro z hz v
    rw [mul_smul, mul_smul, hw₀, charVal_neg, hz, hz]
    linear_combination (-(charVal z v)) * hr
  have hV₀ := hVfix z₀ hE.eig₀
  have hV₁ := hVfix z₁ hE.eig₁
  have h25 : (w₀ * w * w) ^ 25 = 1 := pow_twentyFive_eq_one hE.reg hV₀ hV₁
  have hw₀c : ∀ g : WeylGroup Tag.E8, w₀ * g = g * w₀ := fun g =>
    eq_of_smul_single_eq fun j => by rw [mul_smul, mul_smul, hw₀, hw₀, smul_neg]
  have hVw : w * (w₀ * w * w) = w₀ * w * w * w := by
    rw [show w * (w₀ * w * w) = w * w₀ * w * w by simp only [mul_assoc], ← hw₀c w]
  by_cases hV1 : w₀ * w * w = 1
  · intro u
    have hww : w * w = w₀⁻¹ := eq_inv_of_mul_eq_one_right (by rw [← mul_assoc]; exact hV1)
    rw [← mul_smul, hww, inv_smul_eq_iff, hw₀, neg_neg]
  · exfalso
    have hord : orderOf (w₀ * w * w) ∣ 25 := orderOf_dvd_of_pow_eq_one h25
    have hV5 : 5 ∣ orderOf (w₀ * w * w) := by
      have h1 : orderOf (w₀ * w * w) ≠ 1 := fun h => hV1 (orderOf_eq_one_iff.1 h)
      have hle : orderOf (w₀ * w * w) ≤ 25 := Nat.le_of_dvd (by norm_num) hord
      generalize orderOf (w₀ * w * w) = n at hord h1 hle ⊢
      interval_cases n <;> omega
    have hpos : orderOf (w₀ * w * w) ≠ 0 := (Nat.pos_of_dvd_of_pos hord (by norm_num)).ne'
    have hy := orderOf_pow_orderOf_div hpos hV5
    have hcomm : Commute w (w₀ * w * w) := hVw
    exact not_eigenPair_of_orderOf hr hE hy (hcomm.pow_right _).eq
      (Subgroup.pow_mem _ hV₀ _) (Subgroup.pow_mem _ hV₁ _)

end CFSG.LieType.SeitzGeneration.ExcHigh.E8FiveSq
