module

public import CFSG.LocalAnalysis.ComponentInitial.CentralSL2Semilinear
public import CFSG.LocalAnalysis.EvenBN.GMSK.SL2Facts
public import CFSG.CGT.Timmesfeld75.Lemma27
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonSplitTorus
public import Certificates.Certificate113

public section

namespace CFSG.LocalAnalysis.EvenBN.LinearThree.CaseBModule

open Matrix Module Polynomial
open CFSG.LocalAnalysis.ComponentInitial (sl2Upper sl2Lower sl2Diag sl2Weyl)
open scoped MatrixGroups

structure SwapData (K : Type*) [Field K] (M : Type*) [AddCommGroup M] [Module (ZMod 2) M] where
  f : ℕ
  two_le : 2 ≤ f
  card_K : Nat.card K = 2 ^ f
  finrank_M : finrank (ZMod 2) M = 4 * f
  α : SL(2, K) →* Module.End (ZMod 2) M
  α_injective : Function.Injective α
  τ : Module.End (ZMod 2) M
  τ_mul_self : τ * τ = 1
  comm : ∀ B B' : SL(2, K), α B * (τ * α B' * τ) = τ * α B' * τ * α B
  ι : (Fin 2 → K) →+ M
  ι_injective : Function.Injective ι
  τ_ι : ∀ v, τ (ι v) = ι v
  exists_ι : ∀ m, τ m = m → ∃ v, ι v = m
  nat : ∀ (B : SL(2, K)) (v : Fin 2 → K),
    α B (τ (α B (τ (ι v)))) = ι ((B : Matrix (Fin 2) (Fin 2) K) *ᵥ v)
  h₀ : Module.End (ZMod 2) M
  c : K
  h₀_α : ∀ B, h₀ * α B = α B * h₀
  h₀_τ : h₀ * τ = τ * h₀
  h₀_ι : ∀ v, h₀ (ι v) = ι (c • v)
  c_ne_zero : c ≠ 0
  c_ne_one : c ≠ 1
  h₀_pow : h₀ ^ (Nat.card K - 1) = 1

section Faithful

variable {K : Type*} [Field K] [Finite K]

theorem card_sl2 {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    Nat.card SL(2, K) = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
  have : Fintype K := Fintype.ofFinite K
  have hq : Fintype.card K = 2 ^ f := by rw [Fintype.card_eq_nat_card, hK]
  have h2 : 2 ≤ 2 ^ f := by
    have : 1 < Nat.card K := Finite.one_lt_card
    omega
  rw [Matrix.card_SL_field 2, hq, Fin.prod_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  generalize 2 ^ f = q at h2 ⊢
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  have h1 : (r + 1) ^ 2 - (r + 1) = (r + 1) * r := Nat.sub_eq_of_eq_add (by ring)
  have h3 : (r + 1) ^ 2 - 1 = r * (r + 2) := Nat.sub_eq_of_eq_add (by ring)
  rw [h1, h3, Nat.add_sub_cancel]
  have e : r * (r + 2) * ((r + 1) * r) = (r + 1) * (r * (r + 2)) * r := by ring
  rw [e, Nat.mul_div_cancel _ (by omega : 0 < r)]

theorem two_mul_le_of_faithful {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f) {N : Type*}
    [Group N] [Finite N] (ρ : SL(2, K) →* MulAut N) (hρ : Function.Injective ρ) {d : ℕ}
    (hN : Nat.card N = 2 ^ d) : 2 * f ≤ d := by
  by_cases hf3 : f = 3
  · subst hf3
    have : Fintype K := Fintype.ofFinite K
    have : Fintype (GaloisField 2 3) := Fintype.ofFinite _
    have hcard : Fintype.card K = Fintype.card (GaloisField 2 3) := by
      rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hK,
        GaloisField.card 2 3 (by norm_num)]
    let e : K ≃+* GaloisField 2 3 := FiniteField.ringEquivOfCardEq hcard
    let π : SL(2, K) →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 3) :=
      (QuotientGroup.mk' _).comp (Matrix.SpecialLinearGroup.map e.toRingHom)
    have hπ : Function.Surjective π := by
      intro y
      obtain ⟨B', rfl⟩ := QuotientGroup.mk'_surjective _ y
      refine ⟨Matrix.SpecialLinearGroup.map e.symm.toRingHom B', ?_⟩
      change QuotientGroup.mk' _ _ = QuotientGroup.mk' _ _
      congr 1
      ext i j
      simp
    obtain ⟨x, hx⟩ := CFSG.CGT.Timmesfeld75.exists_orderOf_nine_of_surjective_psl2_eight π hπ
    have := CFSG.CGT.Timmesfeld75.faithful_le_of_orderOf_nine ρ hρ hN hx
    omega
  · refine CFSG.CGT.Timmesfeld75.lemma27_psl2 hf hf3 ?_ ρ hρ hN
    rw [card_sl2 hK]

end Faithful

section Unitriangular

variable {K : Type*} [Field K]

open CFSG.LocalAnalysis.ComponentInitial in
theorem sl2Upper_mul_self [CharP K 2] (a : K) : sl2Upper K a * sl2Upper K a = 1 := by
  rw [← sl2Upper_add, CharTwo.add_self_eq_zero, sl2Upper_zero]

open CFSG.LocalAnalysis.ComponentInitial in
theorem sl2Lower_mul_self [CharP K 2] (a : K) : sl2Lower K a * sl2Lower K a = 1 := by
  rw [← sl2Lower_add, CharTwo.add_self_eq_zero, sl2Lower_zero]

theorem sl2Upper_ne_one {a : K} (ha : a ≠ 0) : sl2Upper K a ≠ 1 := by
  intro h
  have := congrArg (fun B : SL(2, K) => (B : Matrix (Fin 2) (Fin 2) K) 0 1) h
  simp at this
  exact ha this

theorem sl2Lower_ne_one {a : K} (ha : a ≠ 0) : sl2Lower K a ≠ 1 := by
  intro h
  have := congrArg (fun B : SL(2, K) => (B : Matrix (Fin 2) (Fin 2) K) 1 0) h
  simp at this
  exact ha this

open CFSG.LocalAnalysis.ComponentInitial in
theorem sl2Upper_comm (a b : K) : sl2Upper K a * sl2Upper K b = sl2Upper K b * sl2Upper K a := by
  rw [← sl2Upper_add, ← sl2Upper_add, add_comm]

open CFSG.LocalAnalysis.ComponentInitial in
theorem sl2Lower_comm (a b : K) : sl2Lower K a * sl2Lower K b = sl2Lower K b * sl2Lower K a := by
  rw [← sl2Lower_add, ← sl2Lower_add, add_comm]

theorem sl2Diag_mul (s t : Kˣ) : sl2Diag K (s * t) = sl2Diag K s * sl2Diag K t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_comm]

theorem sl2Diag_one : sl2Diag K 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem sl2Diag_pow (t : Kˣ) (n : ℕ) : sl2Diag K (t ^ n) = sl2Diag K t ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, sl2Diag_one]
  | succ n ih => rw [pow_succ, pow_succ, sl2Diag_mul, ih]

theorem sl2Diag_mul_weyl (t : Kˣ) :
    sl2Diag K t * sl2Weyl K 1 = sl2Weyl K 1 * sl2Diag K t⁻¹ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem sl2Diag_mulVec (t : Kˣ) (v : Fin 2 → K) :
    (sl2Diag K t : Matrix (Fin 2) (Fin 2) K) *ᵥ v = ![(t : K) * v 0, ((t⁻¹ : Kˣ) : K) * v 1] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem sl2Diag_ne_one {t : Kˣ} (ht : (t : K) ≠ 1) : sl2Diag K t ≠ 1 := by
  intro h
  have := congrArg (fun B : SL(2, K) => (B : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simp at this
  exact ht (by rw [this, Units.val_one])

end Unitriangular

namespace SwapData

variable {K : Type*} [Field K] {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
variable (S : SwapData K M)

theorem add_self (m : M) : m + m = 0 := by
  rw [← two_smul (ZMod 2) m]
  exact (show (2 : ZMod 2) = 0 from rfl) ▸ zero_smul _ m

theorem neg_eq (m : M) : -m = m := neg_eq_of_add_eq_zero_right (add_self m)

theorem τ_τ (m : M) : S.τ (S.τ m) = m := by
  rw [← Module.End.mul_apply, S.τ_mul_self, Module.End.one_apply]

@[expose] def β : SL(2, K) →* Module.End (ZMod 2) M where
  toFun B := S.τ * S.α B * S.τ
  map_one' := by rw [map_one, mul_one, S.τ_mul_self]
  map_mul' B B' := by
    rw [map_mul]
    calc S.τ * (S.α B * S.α B') * S.τ = S.τ * S.α B * (S.τ * S.τ) * S.α B' * S.τ := by
          rw [S.τ_mul_self, mul_one]; simp only [mul_assoc]
      _ = S.τ * S.α B * S.τ * (S.τ * S.α B' * S.τ) := by simp only [mul_assoc]

theorem β_apply (B : SL(2, K)) (m : M) : S.β B m = S.τ (S.α B (S.τ m)) := rfl

theorem α_β (B B' : SL(2, K)) (m : M) : S.α B (S.β B' m) = S.β B' (S.α B m) := by
  have := congrArg (fun φ : Module.End (ZMod 2) M => φ m) (S.comm B B')
  rw [S.β_apply, S.β_apply]
  simpa only [Module.End.mul_apply] using this

theorem τ_α (B : SL(2, K)) (m : M) : S.τ (S.α B m) = S.β B (S.τ m) := by
  rw [β_apply, τ_τ]

theorem τ_β (B : SL(2, K)) (m : M) : S.τ (S.β B m) = S.α B (S.τ m) := by
  rw [β_apply, τ_τ]

theorem h₀_α_apply (B : SL(2, K)) (m : M) : S.h₀ (S.α B m) = S.α B (S.h₀ m) := by
  have := congrArg (fun φ : Module.End (ZMod 2) M => φ m) (S.h₀_α B)
  simpa only [Module.End.mul_apply] using this

theorem h₀_τ_apply (m : M) : S.h₀ (S.τ m) = S.τ (S.h₀ m) := by
  have := congrArg (fun φ : Module.End (ZMod 2) M => φ m) S.h₀_τ
  simpa only [Module.End.mul_apply] using this

theorem h₀_β_apply (B : SL(2, K)) (m : M) : S.h₀ (S.β B m) = S.β B (S.h₀ m) := by
  rw [β_apply, β_apply, S.h₀_τ_apply, S.h₀_α_apply, S.h₀_τ_apply]

theorem δ_ι (B : SL(2, K)) (v : Fin 2 → K) :
    S.α B (S.β B (S.ι v)) = S.ι ((B : Matrix (Fin 2) (Fin 2) K) *ᵥ v) := S.nat B v

theorem δ_τ (B : SL(2, K)) (m : M) :
    S.α B (S.β B (S.τ m)) = S.τ (S.α B (S.β B m)) := by
  rw [S.τ_α, S.τ_β, S.α_β]

@[expose] def fixX : Submodule (ZMod 2) M := ⨅ B, LinearMap.ker (S.α B - 1)

@[expose] def fixY : Submodule (ZMod 2) M := ⨅ B, LinearMap.ker (S.β B - 1)

@[expose] def fixτ : Submodule (ZMod 2) M := LinearMap.ker (S.τ - 1)

theorem mem_fixX {m : M} : m ∈ S.fixX ↔ ∀ B, S.α B m = m := by
  simp [fixX, Submodule.mem_iInf, sub_eq_zero]

theorem mem_fixY {m : M} : m ∈ S.fixY ↔ ∀ B, S.β B m = m := by
  simp [fixY, Submodule.mem_iInf, sub_eq_zero]

theorem mem_fixτ {m : M} : m ∈ S.fixτ ↔ S.τ m = m := by
  simp [fixτ, sub_eq_zero]

theorem natural_fixed {v : Fin 2 → K}
    (hv : ∀ B : SL(2, K), (B : Matrix (Fin 2) (Fin 2) K) *ᵥ v = v) : v = 0 := by
  have h1 := congrFun (hv (sl2Upper K 1)) 0
  have h2 := congrFun (hv (sl2Lower K 1)) 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h1 h2
  ext i
  fin_cases i
  · exact h2
  · exact h1

theorem τ_sub_mem (m : M) : S.τ (S.τ m - m) = S.τ m - m := by
  rw [map_sub, S.τ_τ, ← neg_sub, neg_eq]

theorem eq_zero_of_δ_fixed {m : M} (hm : ∀ B, S.α B (S.β B m) = m) : m = 0 := by
  have key : ∀ x : M, S.τ x = x → (∀ B, S.α B (S.β B x) = x) → x = 0 := by
    intro x hx hfix
    obtain ⟨v, rfl⟩ := S.exists_ι x hx
    have hv : v = 0 := natural_fixed fun B => S.ι_injective (by rw [← S.δ_ι, hfix])
    rw [hv, map_zero]
  have h1 : S.τ m - m = 0 := key _ (S.τ_sub_mem m) fun B => by
    rw [map_sub, map_sub, S.δ_τ, hm]
  have h2 : S.τ m = m := sub_eq_zero.mp h1
  exact key m h2 hm

theorem inf_fix_eq_bot : S.fixX ⊓ S.fixY = ⊥ := by
  rw [eq_bot_iff]
  intro m hm
  obtain ⟨hX, hY⟩ := Submodule.mem_inf.mp hm
  rw [Submodule.mem_bot]
  refine S.eq_zero_of_δ_fixed fun B => ?_
  rw [(S.mem_fixY.mp hY) B, (S.mem_fixX.mp hX) B]

theorem τ_mem_fixX {m : M} (hm : m ∈ S.fixY) : S.τ m ∈ S.fixX :=
  S.mem_fixX.mpr fun B => by rw [← S.τ_β, (S.mem_fixY.mp hm) B]

theorem τ_mem_fixY {m : M} (hm : m ∈ S.fixX) : S.τ m ∈ S.fixY :=
  S.mem_fixY.mpr fun B => by rw [← S.τ_α, (S.mem_fixX.mp hm) B]

theorem α_mem_fixY (B : SL(2, K)) {m : M} (hm : m ∈ S.fixY) : S.α B m ∈ S.fixY :=
  S.mem_fixY.mpr fun B' => by rw [← S.α_β, (S.mem_fixY.mp hm) B']

section Dim

variable [Finite M]

theorem natCard_submodule (U : Submodule (ZMod 2) M) :
    Nat.card U = 2 ^ finrank (ZMod 2) U := by
  have : Fintype U := Fintype.ofFinite U
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]

@[expose] noncomputable def ιEquiv : (Fin 2 → K) ≃ S.fixτ :=
  Equiv.ofBijective (fun v => ⟨S.ι v, S.mem_fixτ.mpr (S.τ_ι v)⟩)
    ⟨fun v w h => S.ι_injective (congrArg Subtype.val h), fun m => by
      obtain ⟨v, hv⟩ := S.exists_ι m (S.mem_fixτ.mp m.2)
      exact ⟨v, Subtype.ext hv⟩⟩

end Dim

noncomputable def restrictAddEquiv (U : Submodule (ZMod 2) M)
    (hU : ∀ B, ∀ u ∈ U, S.α B u ∈ U) (B : SL(2, K)) : U ≃+ U where
  toFun u := ⟨S.α B u, hU B u u.2⟩
  invFun u := ⟨S.α B⁻¹ u, hU B⁻¹ u u.2⟩
  left_inv u := Subtype.ext (by
    change S.α B⁻¹ (S.α B u) = u
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply])
  right_inv u := Subtype.ext (by
    change S.α B (S.α B⁻¹ u) = u
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply])
  map_add' u v := Subtype.ext (map_add _ _ _)

noncomputable def restrictHom (U : Submodule (ZMod 2) M) (hU : ∀ B, ∀ u ∈ U, S.α B u ∈ U) :
    SL(2, K) →* MulAut (Multiplicative U) where
  toFun B := AddEquiv.toMultiplicative (S.restrictAddEquiv U hU B)
  map_one' := by
    ext u
    change S.α 1 ((Multiplicative.toAdd u : U) : M) = ((Multiplicative.toAdd u : U) : M)
    rw [map_one, Module.End.one_apply]
  map_mul' B B' := by
    ext u
    change S.α (B * B') ((Multiplicative.toAdd u : U) : M) =
      S.α B (S.α B' ((Multiplicative.toAdd u : U) : M))
    rw [map_mul, Module.End.mul_apply]

theorem trivial_of_finrank_lt [Finite K] [CharP K 2] [Finite M] (U : Submodule (ZMod 2) M)
    (hU : ∀ B, ∀ u ∈ U, S.α B u ∈ U) (hd : finrank (ZMod 2) U < 2 * S.f) :
    ∀ B, ∀ u ∈ U, S.α B u = u := by
  have : Fintype K := Fintype.ofFinite K
  have h4 : 4 ≤ Fintype.card K := by
    rw [Fintype.card_eq_nat_card, S.card_K]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ S.f := Nat.pow_le_pow_right (by norm_num) S.two_le
  have : IsSimpleGroup SL(2, K) := GMSK.sl2_isSimpleGroup (CharTwo.two_eq_zero) h4
  set ρ := S.restrictHom U hU
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.ker with h | h
  · have hinj : Function.Injective ρ := (MonoidHom.ker_eq_bot_iff ρ).mp h
    have hN : Nat.card (Multiplicative U) = 2 ^ finrank (ZMod 2) U := by
      rw [show Nat.card (Multiplicative U) = Nat.card U from rfl, natCard_submodule U]
    have := two_mul_le_of_faithful S.two_le S.card_K ρ hinj hN
    omega
  · intro B u hu
    have hB : ρ B = 1 := (MonoidHom.mem_ker).mp (h ▸ Subgroup.mem_top B)
    have := congrArg (fun φ : MulAut (Multiplicative U) =>
      ((Multiplicative.toAdd (φ (Multiplicative.ofAdd (⟨u, hu⟩ : U))) : U) : M)) hB
    simpa [ρ, restrictHom, restrictAddEquiv] using this

theorem finrank_fixX_eq [Finite M] : finrank (ZMod 2) S.fixX = finrank (ZMod 2) S.fixY := by
  have h1 : S.fixX ≤ S.fixY.map S.τ := fun m hm =>
    ⟨S.τ m, S.τ_mem_fixY hm, S.τ_τ m⟩
  have h2 : S.fixY ≤ S.fixX.map S.τ := fun m hm =>
    ⟨S.τ m, S.τ_mem_fixX hm, S.τ_τ m⟩
  exact le_antisymm ((Submodule.finrank_mono h1).trans (Submodule.finrank_map_le _ _))
    ((Submodule.finrank_mono h2).trans (Submodule.finrank_map_le _ _))

theorem decomp_of_ne_bot [Finite K] [CharP K 2] [Finite M] (h : S.fixY ≠ ⊥) :
    finrank (ZMod 2) S.fixY = 2 * S.f ∧ S.fixY ⊓ S.fixX = ⊥ ∧ S.fixY ⊔ S.fixX = ⊤ := by
  have hinf : S.fixY ⊓ S.fixX = ⊥ := by rw [inf_comm]; exact S.inf_fix_eq_bot
  have hge : 2 * S.f ≤ finrank (ZMod 2) S.fixY := by
    by_contra hlt
    push Not at hlt
    have htriv := S.trivial_of_finrank_lt S.fixY (fun B m hm => S.α_mem_fixY B hm) hlt
    apply h
    rw [eq_bot_iff, ← hinf]
    intro m hm
    exact Submodule.mem_inf.mpr ⟨hm, S.mem_fixX.mpr fun B => htriv B m hm⟩
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq S.fixY S.fixX
  rw [hinf, finrank_bot, add_zero, S.finrank_fixX_eq] at hsum
  have hle := Submodule.finrank_le (S.fixY ⊔ S.fixX)
  rw [S.finrank_M] at hle
  have htop : S.fixY ⊔ S.fixX = ⊤ := Submodule.eq_top_of_finrank_eq (by
    rw [S.finrank_M]; omega)
  exact ⟨by omega, hinf, htop⟩

@[expose] def Zof (B : SL(2, K)) : Submodule (ZMod 2) M := LinearMap.ker (S.β B - 1)

theorem mem_Zof {B : SL(2, K)} {m : M} : m ∈ S.Zof B ↔ S.β B m = m := by
  simp [Zof, sub_eq_zero]

theorem α_mem_Zof {B : SL(2, K)} (B' : SL(2, K)) {m : M} (hm : m ∈ S.Zof B) :
    S.α B' m ∈ S.Zof B := S.mem_Zof.mpr (by rw [← S.α_β, S.mem_Zof.mp hm])

theorem h₀_mem_Zof {B : SL(2, K)} {m : M} (hm : m ∈ S.Zof B) : S.h₀ m ∈ S.Zof B :=
  S.mem_Zof.mpr (by rw [← S.h₀_β_apply, S.mem_Zof.mp hm])

theorem sub_one_sq {B : SL(2, K)} (hB : B * B = 1) (m : M) :
    (S.β B - 1) ((S.β B - 1) m) = 0 := by
  have hBB : S.β B (S.β B m) = m := by
    rw [← Module.End.mul_apply, ← map_mul, hB, map_one, Module.End.one_apply]
  simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, hBB]
  rw [sub_eq_add_neg _ (S.β B m - m), neg_sub, add_self]

theorem range_le_Zof {B : SL(2, K)} (hB : B * B = 1) :
    LinearMap.range (S.β B - 1) ≤ S.Zof B := by
  rintro _ ⟨m, rfl⟩
  exact S.sub_one_sq hB m

theorem sub_one_α (B B' : SL(2, K)) (m : M) :
    (S.β B - 1) (S.α B' m) = S.α B' ((S.β B - 1) m) := by
  simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, S.α_β]

theorem eq_one_of_β_eq_one {B : SL(2, K)} (h : ∀ m, S.β B m = m) : B = 1 := by
  apply S.α_injective
  ext m
  rw [map_one, Module.End.one_apply]
  have := S.τ_β B (S.τ m)
  rw [S.τ_τ, h, S.τ_τ] at this
  exact this.symm

theorem Zof_one : S.Zof 1 = ⊤ := by
  rw [eq_top_iff]
  intro m _
  rw [S.mem_Zof, map_one, Module.End.one_apply]

section Involutions

variable [Finite K] [CharP K 2] [Finite M]

theorem finrank_Zof (hX : S.fixX = ⊥) {B : SL(2, K)} (hB : B * B = 1) (hB1 : B ≠ 1) :
    finrank (ZMod 2) (S.Zof B) = 2 * S.f ∧ LinearMap.range (S.β B - 1) = S.Zof B := by
  have hRinv : ∀ B', ∀ m ∈ LinearMap.range (S.β B - 1), S.α B' m ∈ LinearMap.range (S.β B - 1) := by
    rintro B' _ ⟨m, rfl⟩
    exact ⟨S.α B' m, S.sub_one_α B B' m⟩
  have hRne : LinearMap.range (S.β B - 1) ≠ ⊥ := by
    intro hR
    refine hB1 (S.eq_one_of_β_eq_one fun m => ?_)
    have : (S.β B - 1) m ∈ LinearMap.range (S.β B - 1) := ⟨m, rfl⟩
    rw [hR, Submodule.mem_bot, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at this
    exact this
  have hge : 2 * S.f ≤ finrank (ZMod 2) (LinearMap.range (S.β B - 1)) := by
    by_contra hlt
    push Not at hlt
    have htriv := S.trivial_of_finrank_lt _ hRinv hlt
    apply hRne
    rw [eq_bot_iff, ← hX]
    intro m hm
    exact S.mem_fixX.mpr fun B' => htriv B' m hm
  have hrn : finrank (ZMod 2) (LinearMap.range (S.β B - 1)) + finrank (ZMod 2) (S.Zof B) =
      4 * S.f := by
    rw [← S.finrank_M]
    exact LinearMap.finrank_range_add_finrank_ker (S.β B - 1)
  have hRZ := S.range_le_Zof hB
  have hle := Submodule.finrank_mono hRZ
  have hZ : finrank (ZMod 2) (S.Zof B) = 2 * S.f := by omega
  exact ⟨hZ, Submodule.eq_of_le_of_finrank_eq hRZ (by omega)⟩

theorem eq_Zof_of_le (hX : S.fixX = ⊥) {B : SL(2, K)} (hB : B * B = 1) (hB1 : B ≠ 1)
    (U : Submodule (ZMod 2) M) (hU : ∀ B', ∀ u ∈ U, S.α B' u ∈ U) (hUZ : U ≤ S.Zof B)
    (hU0 : U ≠ ⊥) : U = S.Zof B := by
  have hZ := (S.finrank_Zof hX hB hB1).1
  refine Submodule.eq_of_le_of_finrank_eq hUZ ?_
  have hle := Submodule.finrank_mono hUZ
  rw [hZ] at hle ⊢
  by_contra hne
  have htriv := S.trivial_of_finrank_lt U hU (lt_of_le_of_ne hle hne)
  apply hU0
  rw [eq_bot_iff, ← hX]
  intro m hm
  exact S.mem_fixX.mpr fun B' => htriv B' m hm

theorem Zof_ne_bot (hX : S.fixX = ⊥) {B : SL(2, K)} (hB : B * B = 1) (hB1 : B ≠ 1) :
    S.Zof B ≠ ⊥ := by
  intro h
  have := (S.finrank_Zof hX hB hB1).1
  rw [h, finrank_bot] at this
  have := S.two_le
  omega

theorem Zof_eq_of_commute (hX : S.fixX = ⊥) {B B' : SL(2, K)} (hB : B * B = 1) (hB1 : B ≠ 1)
    (hB' : B' * B' = 1) (hB'1 : B' ≠ 1) (hc : B * B' = B' * B) : S.Zof B = S.Zof B' := by
  have hcomm : ∀ m, S.β B (S.β B' m) = S.β B' (S.β B m) := fun m => by
    rw [← Module.End.mul_apply, ← map_mul, hc, map_mul, Module.End.mul_apply]
  have hne : S.Zof B ⊓ S.Zof B' ≠ ⊥ := by
    obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (S.Zof_ne_bot hX hB hB1)
    by_cases h1 : (S.β B' - 1) z = 0
    · intro hbot
      have hmem : z ∈ S.Zof B ⊓ S.Zof B' := Submodule.mem_inf.mpr ⟨hz, by
        rw [S.mem_Zof]
        rwa [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h1⟩
      rw [hbot, Submodule.mem_bot] at hmem
      exact hz0 hmem
    · intro hbot
      have hmem : (S.β B' - 1) z ∈ S.Zof B ⊓ S.Zof B' := by
        refine Submodule.mem_inf.mpr ⟨S.mem_Zof.mpr ?_, ?_⟩
        · simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, hcomm,
            S.mem_Zof.mp hz]
        · rw [S.mem_Zof]
          have := S.sub_one_sq hB' z
          rwa [LinearMap.sub_apply (S.β B') 1, Module.End.one_apply, sub_eq_zero] at this
      rw [hbot, Submodule.mem_bot] at hmem
      exact h1 hmem
  have heq := S.eq_Zof_of_le hX hB hB1 (S.Zof B ⊓ S.Zof B')
    (fun B'' u hu => Submodule.mem_inf.mpr ⟨S.α_mem_Zof B'' (Submodule.mem_inf.mp hu).1,
      S.α_mem_Zof B'' (Submodule.mem_inf.mp hu).2⟩) inf_le_left hne
  have hle : S.Zof B ≤ S.Zof B' := by
    rw [← heq]
    exact inf_le_right
  exact Submodule.eq_of_le_of_finrank_eq hle (by
    rw [(S.finrank_Zof hX hB hB1).1, (S.finrank_Zof hX hB' hB'1).1])

theorem Zup_Zlow (hX : S.fixX = ⊥) (hY : S.fixY = ⊥) :
    S.Zof (sl2Upper K 1) ⊓ S.Zof (sl2Lower K 1) = ⊥ ∧
      S.Zof (sl2Upper K 1) ⊔ S.Zof (sl2Lower K 1) = ⊤ := by
  have hu1 := sl2Upper_mul_self (K := K) 1
  have hl1 := sl2Lower_mul_self (K := K) 1
  have hu1' := sl2Upper_ne_one (K := K) one_ne_zero
  have hl1' := sl2Lower_ne_one (K := K) one_ne_zero
  have hup : ∀ a : K, S.Zof (sl2Upper K 1) ≤ S.Zof (sl2Upper K a) := by
    intro a
    by_cases ha : a = 0
    · rw [ha, CFSG.LocalAnalysis.ComponentInitial.sl2Upper_zero, S.Zof_one]
      exact le_top
    · exact (S.Zof_eq_of_commute hX hu1 hu1' (sl2Upper_mul_self a) (sl2Upper_ne_one ha)
        (sl2Upper_comm 1 a)).le
  have hlow : ∀ a : K, S.Zof (sl2Lower K 1) ≤ S.Zof (sl2Lower K a) := by
    intro a
    by_cases ha : a = 0
    · rw [ha, CFSG.LocalAnalysis.ComponentInitial.sl2Lower_zero, S.Zof_one]
      exact le_top
    · exact (S.Zof_eq_of_commute hX hl1 hl1' (sl2Lower_mul_self a) (sl2Lower_ne_one ha)
        (sl2Lower_comm 1 a)).le
  have hne : S.Zof (sl2Upper K 1) ≠ S.Zof (sl2Lower K 1) := by
    intro heq
    let H : Subgroup SL(2, K) :=
      { carrier := {B | ∀ z ∈ S.Zof (sl2Upper K 1), S.β B z = z}
        mul_mem' := fun {B B'} hB hB' z hz => by
          change S.β (B * B') z = z
          rw [map_mul, Module.End.mul_apply, hB' z hz, hB z hz]
        one_mem' := fun z _ => by
          change S.β 1 z = z
          rw [map_one, Module.End.one_apply]
        inv_mem' := fun {B} hB z hz => by
          change S.β B⁻¹ z = z
          calc S.β B⁻¹ z = S.β B⁻¹ (S.β B z) := by rw [hB z hz]
            _ = z := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
                  Module.End.one_apply] }
    have htop : H = ⊤ := by
      rw [eq_top_iff, ← CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower,
        Subgroup.closure_le]
      rintro _ (⟨a, rfl⟩ | ⟨a, rfl⟩) z hz
      · exact S.mem_Zof.mp (hup a hz)
      · exact S.mem_Zof.mp (hlow a (heq ▸ hz))
    apply S.Zof_ne_bot hX hu1 hu1'
    rw [eq_bot_iff, ← hY]
    intro z hz
    exact S.mem_fixY.mpr fun B => (htop ▸ Subgroup.mem_top B : B ∈ H) z hz
  have hinf : S.Zof (sl2Upper K 1) ⊓ S.Zof (sl2Lower K 1) = ⊥ := by
    by_contra hbot
    have heq := S.eq_Zof_of_le hX hu1 hu1' _
      (fun B u hu => Submodule.mem_inf.mpr ⟨S.α_mem_Zof B (Submodule.mem_inf.mp hu).1,
        S.α_mem_Zof B (Submodule.mem_inf.mp hu).2⟩) inf_le_left hbot
    have hle : S.Zof (sl2Upper K 1) ≤ S.Zof (sl2Lower K 1) := by
      rw [← heq]
      exact inf_le_right
    exact hne (Submodule.eq_of_le_of_finrank_eq hle (by
      rw [(S.finrank_Zof hX hu1 hu1').1, (S.finrank_Zof hX hl1 hl1').1]))
  refine ⟨hinf, Submodule.eq_top_of_finrank_eq ?_⟩
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (S.Zof (sl2Upper K 1))
    (S.Zof (sl2Lower K 1))
  rw [hinf, finrank_bot, add_zero, (S.finrank_Zof hX hu1 hu1').1,
    (S.finrank_Zof hX hl1 hl1').1] at hsum
  rw [hsum, S.finrank_M]
  ring

end Involutions

section Field

variable [Finite K] [Finite M]

omit [Finite K] [Finite M] in
theorem aeval_h₀_τ (P : (ZMod 2)[X]) (m : M) : aeval S.h₀ P (S.τ m) = S.τ (aeval S.h₀ P m) := by
  induction P using Polynomial.induction_on generalizing m with
  | C a => rw [aeval_C, Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul]
  | add P Q hP hQ => rw [map_add, LinearMap.add_apply, LinearMap.add_apply, hP, hQ, map_add]
  | monomial k a h =>
    rw [pow_succ, ← mul_assoc, map_mul (aeval S.h₀) (C a * X ^ k) X, aeval_X,
      Module.End.mul_apply, Module.End.mul_apply, S.h₀_τ_apply, h]

omit [Finite K] [Finite M] in
theorem aeval_h₀_ι [Algebra (ZMod 2) K] (P : (ZMod 2)[X]) (v : Fin 2 → K) :
    aeval S.h₀ P (S.ι v) = S.ι (aeval S.c P • v) := by
  induction P using Polynomial.induction_on generalizing v with
  | C a =>
    rw [aeval_C, aeval_C, Module.algebraMap_end_apply]
    rcases (show ∀ b : ZMod 2, b = 0 ∨ b = 1 by decide) a with rfl | rfl
    · simp
    · simp
  | add P Q hP hQ => rw [map_add, map_add, LinearMap.add_apply, hP, hQ, add_smul, map_add]
  | monomial k a h =>
    rw [pow_succ, ← mul_assoc, map_mul (aeval S.h₀) (C a * X ^ k) X,
      map_mul (aeval S.c) (C a * X ^ k) X, Module.End.mul_apply, aeval_X, aeval_X,
      S.h₀_ι, h, smul_smul]

theorem aeval_minpoly_eq_zero [Algebra (ZMod 2) K] :
    aeval S.h₀ (minpoly (ZMod 2) S.c) = 0 := by
  have : Fintype K := Fintype.ofFinite K
  have : Module.Finite (ZMod 2) M := Module.Finite.of_finite
  set n := Nat.card K - 1 with hn
  have hcn : S.c ^ n = 1 := by
    rw [hn, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one S.c S.c_ne_zero
  obtain ⟨r, hr⟩ : minpoly (ZMod 2) S.c ∣ X ^ n - 1 :=
    minpoly.dvd (ZMod 2) S.c (by simp [hcn])
  have hnodd : (n : ZMod 2) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff_even, hn, S.card_K, Nat.even_iff]
    have h1 : 1 ≤ 2 ^ (S.f - 1) := Nat.one_le_two_pow
    have h2 : 2 ^ S.f = 2 * 2 ^ (S.f - 1) := by
      rw [← pow_succ']
      congr 1
      have := S.two_le
      omega
    omega
  have hsep : (X ^ n - C (1 : ZMod 2)).Separable := separable_X_pow_sub_C 1 hnodd one_ne_zero
  have hrc : aeval S.c r ≠ 0 := by
    intro h0
    obtain ⟨s, hs⟩ := minpoly.dvd (ZMod 2) S.c h0
    have hsq : minpoly (ZMod 2) S.c * minpoly (ZMod 2) S.c ∣ X ^ n - C (1 : ZMod 2) :=
      ⟨s, by rw [map_one, hr, hs]; ring⟩
    exact minpoly.not_isUnit (ZMod 2) S.c (hsep.squarefree _ hsq)
  have hinj : Function.Injective (aeval S.h₀ r) := by
    rw [injective_iff_map_eq_zero]
    intro m hm
    have key : ∀ x : M, S.τ x = x → aeval S.h₀ r x = 0 → x = 0 := by
      intro x hx hx0
      obtain ⟨v, rfl⟩ := S.exists_ι x hx
      rw [S.aeval_h₀_ι] at hx0
      have hv : aeval S.c r • v = 0 := S.ι_injective (by rw [hx0, map_zero])
      rw [smul_eq_zero] at hv
      rw [hv.resolve_left hrc, map_zero]
    have h1 : S.τ m - m = 0 := key _ (S.τ_sub_mem m) (by
      rw [map_sub, S.aeval_h₀_τ, hm, map_zero, sub_zero])
    exact key m (sub_eq_zero.mp h1) hm
  have hsurj : Function.Surjective (aeval S.h₀ r) :=
    LinearMap.injective_iff_surjective.mp hinj
  have hQ : aeval S.h₀ (minpoly (ZMod 2) S.c) * aeval S.h₀ r = 0 := by
    rw [← map_mul, ← hr, map_sub, map_pow, aeval_X, map_one, hn, S.h₀_pow, sub_self]
  ext m
  obtain ⟨m', rfl⟩ := hsurj m
  have := congrArg (fun φ : Module.End (ZMod 2) M => φ m') hQ
  simpa only [Module.End.mul_apply, LinearMap.zero_apply] using this

theorem exists_eigen [CharP K 2] (g : Module.End (ZMod 2) M) (hg : g * S.h₀ = S.h₀ * g)
    (hgm : g ^ orderOf S.c = 1) (U : Submodule (ZMod 2) M) (hUg : ∀ u ∈ U, g u ∈ U)
    (hUh : ∀ u ∈ U, S.h₀ u ∈ U) (hU : U ≠ ⊥) :
    ∃ k : ℕ, ∃ u ∈ U, u ≠ 0 ∧ g u = (S.h₀ ^ k) u := by
  classical
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  have : Fintype K := Fintype.ofFinite K
  have hint : IsIntegral (ZMod 2) S.c := .of_finite (ZMod 2) S.c
  set m := orderOf S.c with hm
  have hm0 : 0 < m := by
    have hq : 1 < Fintype.card K := Fintype.one_lt_card
    exact orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr
      ⟨Fintype.card K - 1, by omega, FiniteField.pow_card_sub_one_eq_one S.c S.c_ne_zero⟩)
  set A := Algebra.adjoin (ZMod 2) ({g, S.h₀} : Set (Module.End (ZMod 2) M)) with hA
  have hpair : ({g, S.h₀} : Set (Module.End (ZMod 2) M)).Pairwise Commute := by
    intro x hx y hy _
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact Commute.refl _
    · exact hg
    · exact hg.symm
    · exact Commute.refl _
  have := Algebra.isMulCommutative_adjoin (ZMod 2) hpair
  let : CommRing A := by open scoped IsMulCommutative in infer_instance
  have hApres : ∀ a ∈ A, ∀ u ∈ U, a u ∈ U := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact hUg
      · exact hUh
    | algebraMap r =>
      intro u hu
      rw [Module.algebraMap_end_apply]
      exact U.smul_mem r hu
    | add x y _ _ hx hy =>
      intro u hu
      rw [LinearMap.add_apply]
      exact add_mem (hx u hu) (hy u hu)
    | mul x y _ _ hx hy =>
      intro u hu
      rw [Module.End.mul_apply]
      exact hx _ (hy u hu)
  set g' : A := ⟨g, Algebra.subset_adjoin (by simp)⟩
  set h' : A := ⟨S.h₀, Algebra.subset_adjoin (by simp)⟩
  let pb := IntermediateField.adjoin.powerBasis hint
  have hp : aeval h' (minpoly (ZMod 2) pb.gen) = 0 := by
    rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen]
    have := S.aeval_minpoly_eq_zero
    apply Subtype.val_injective
    change A.val (aeval h' (minpoly (ZMod 2) S.c)) = A.val 0
    rw [← aeval_algHom_apply, map_zero]
    exact this
  let κ := pb.lift h' hp
  set ĉ := IntermediateField.AdjoinSimple.gen (ZMod 2) S.c
  have hκ : κ ĉ = h' := by
    have := pb.lift_gen h' hp
    rwa [IntermediateField.adjoin.powerBasis_gen] at this
  have hord : orderOf ĉ = m := by
    have h := orderOf_injective
      (IntermediateField.val (IntermediateField.adjoin (ZMod 2) {S.c})).toRingHom.toMonoidHom
      Subtype.val_injective ĉ
    rw [hm, ← h]
    congr 1
  have hprim : IsPrimitiveRoot ĉ m := hord ▸ IsPrimitiveRoot.orderOf ĉ
  have : NeZero m := ⟨hm0.ne'⟩
  have hprod := Polynomial.X_pow_sub_one_eq_prod hm0 hprim
  have h1 : eval₂ κ.toRingHom g' (X ^ m - 1) = 0 := by
    rw [eval₂_sub, eval₂_X_pow, eval₂_one]
    apply Subtype.val_injective
    simp only [SubmonoidClass.coe_pow, AddSubgroupClass.coe_sub, OneMemClass.coe_one,
      ZeroMemClass.coe_zero, g']
    rw [hgm, sub_self]
  rw [hprod, eval₂_finsetProd] at h1
  simp only [eval₂_sub, eval₂_X, eval₂_C] at h1
  by_contra hcon
  push Not at hcon
  have hfac : ∀ ζ ∈ nthRootsFinset m (1 : ↥(IntermediateField.adjoin (ZMod 2) {S.c})),
      ∀ u ∈ U, ((g' - κ.toRingHom ζ : A) : Module.End (ZMod 2) M) u = 0 → u = 0 := by
    intro ζ hζ u hu h0
    obtain ⟨k, -, hk⟩ := hprim.eq_pow_of_pow_eq_one ((mem_nthRootsFinset hm0 _).mp hζ)
    have hκζ : ((κ.toRingHom ζ : A) : Module.End (ZMod 2) M) = S.h₀ ^ k := by
      rw [← hk, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_pow, hκ]
      rfl
    by_contra hu0
    apply hcon k u hu hu0
    have h2 : g u - (S.h₀ ^ k) u = 0 := by
      rw [← hκζ]
      simpa only [AddSubgroupClass.coe_sub, LinearMap.sub_apply] using h0
    exact sub_eq_zero.mp h2
  have hprodinj : ∀ s : Finset ↥(IntermediateField.adjoin (ZMod 2) {S.c}),
      s ⊆ nthRootsFinset m (1 : ↥(IntermediateField.adjoin (ZMod 2) {S.c})) →
      ∀ u ∈ U, ((∏ ζ ∈ s, (g' - κ.toRingHom ζ) : A) : Module.End (ZMod 2) M) u = 0 → u = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _ u _ hu; simpa using hu
    | insert ζ s hζs ih =>
      intro hsub u hu h0
      rw [Finset.prod_insert hζs, Subalgebra.coe_mul, Module.End.mul_apply] at h0
      have hPu : ((∏ ζ ∈ s, (g' - κ.toRingHom ζ) : A) : Module.End (ZMod 2) M) u ∈ U :=
        hApres _ (Subtype.prop _) u hu
      have h3 := hfac ζ (hsub (Finset.mem_insert_self ζ s)) _ hPu h0
      exact ih ((Finset.subset_insert ζ s).trans hsub) u hu h3
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
  apply hu0
  refine hprodinj _ (subset_refl _) u hu ?_
  rw [h1, ZeroMemClass.coe_zero, LinearMap.zero_apply]

omit [Finite K] [Finite M] in
theorem h₀_pow_ι (n : ℕ) (v : Fin 2 → K) : (S.h₀ ^ n) (S.ι v) = S.ι (S.c ^ n • v) := by
  induction n generalizing v with
  | zero => rw [pow_zero, pow_zero, one_smul, Module.End.one_apply]
  | succ n ih => rw [pow_succ, Module.End.mul_apply, S.h₀_ι, ih, smul_smul, ← pow_succ]

omit [Finite K] [Finite M] in
theorem h₀_pow_α (n : ℕ) (B : SL(2, K)) (m : M) :
    (S.h₀ ^ n) (S.α B m) = S.α B ((S.h₀ ^ n) m) := by
  have := ((show Commute S.h₀ (S.α B) from S.h₀_α B).pow_left n).eq
  have := congrArg (fun φ : Module.End (ZMod 2) M => φ m) this
  simpa only [Module.End.mul_apply] using this

omit [Finite K] [Finite M] in
theorem h₀_pow_τ (n : ℕ) (m : M) : (S.h₀ ^ n) (S.τ m) = S.τ ((S.h₀ ^ n) m) := by
  have := ((show Commute S.h₀ S.τ from S.h₀_τ).pow_left n).eq
  have := congrArg (fun φ : Module.End (ZMod 2) M => φ m) this
  simpa only [Module.End.mul_apply] using this

theorem h₀_pow_orderOf [CharP K 2] : S.h₀ ^ orderOf S.c = 1 := by
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  obtain ⟨r, hr⟩ := minpoly.dvd (ZMod 2) S.c (p := X ^ orderOf S.c - 1)
    (by simp [pow_orderOf_eq_one])
  have h := congrArg (aeval S.h₀) hr
  rw [map_mul, S.aeval_minpoly_eq_zero, zero_mul, map_sub, map_pow, aeval_X, map_one] at h
  exact sub_eq_zero.mp h

theorem h₀_pow_eq_one [CharP K 2] {e : ℕ} (he : S.c ^ e = 1) : S.h₀ ^ e = 1 := by
  obtain ⟨d, rfl⟩ := orderOf_dvd_of_pow_eq_one he
  rw [pow_mul, S.h₀_pow_orderOf, one_pow]

end Field

section Contradiction

variable [Finite K] [CharP K 2] [Finite M]

omit [Finite K] in
theorem eq_one_of_sq_eq_one {a : K} (ha : a ^ 2 = 1) : a = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have : (a - 1) ^ 2 = 0 := by linear_combination ha - a * h2 + h2
  exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)

omit [Finite K] [CharP K 2] [Finite M] in
theorem eigen_δ {v : M} (hv : v ≠ 0) (e : ℕ)
    (he : S.α (sl2Diag K (Units.mk0 S.c S.c_ne_zero))
      (S.β (sl2Diag K (Units.mk0 S.c S.c_ne_zero)) v) = (S.h₀ ^ e) v) :
    S.c ^ e = S.c ∨ S.c ^ e = S.c⁻¹ := by
  set h := sl2Diag K (Units.mk0 S.c S.c_ne_zero) with hh
  have key : ∀ x : M, S.τ x = x → x ≠ 0 → S.α h (S.β h x) = (S.h₀ ^ e) x →
      S.c ^ e = S.c ∨ S.c ^ e = S.c⁻¹ := by
    intro x hτ hx0 hxe
    obtain ⟨a, rfl⟩ := S.exists_ι x hτ
    rw [S.δ_ι, S.h₀_pow_ι, hh, sl2Diag_mulVec] at hxe
    have he' := S.ι_injective hxe
    have ha : a ≠ 0 := fun h0 => hx0 (by rw [h0, map_zero])
    by_cases h0 : a 0 = 0
    · have h1 : a 1 ≠ 0 := fun h1 => ha (by ext i; fin_cases i; exacts [h0, h1])
      right
      have := congrFun he' 1
      simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.smul_apply, smul_eq_mul,
        Units.val_inv_eq_inv_val, Units.val_mk0] at this
      exact (mul_right_cancel₀ h1 this).symm
    · left
      have := congrFun he' 0
      simp only [Matrix.cons_val_zero, Pi.smul_apply, smul_eq_mul, Units.val_mk0] at this
      exact (mul_right_cancel₀ h0 this).symm
  by_cases hτ : S.τ v = v
  · exact key v hτ hv he
  · refine key (S.τ v - v) (S.τ_sub_mem v) (sub_ne_zero.mpr hτ) ?_
    rw [map_sub, map_sub, S.δ_τ, he, map_sub, S.h₀_pow_τ]

omit [Finite K] [CharP K 2] [Finite M] in
theorem eq_zero_of_odd (g : Module.End (ZMod 2) M) {n : ℕ} (hn : Odd n) (hg : g ^ n = 1)
    (z : M) (hu : g (g z - z) = g z - z) : g z - z = 0 := by
  set u := g z - z with hudef
  have hpow : ∀ i : ℕ, (g ^ i) z = z + i • u := by
    intro i
    induction i with
    | zero => rw [pow_zero, zero_smul, add_zero, Module.End.one_apply]
    | succ i ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_add, map_nsmul, hu, succ_nsmul, hudef]
      abel
  have h1 := hpow n
  rw [hg, Module.End.one_apply, left_eq_add] at h1
  obtain ⟨m, rfl⟩ := hn
  have h2 : (2 * m) • u = 0 := by rw [two_mul, add_nsmul, add_self]
  rw [succ_nsmul, h2, zero_add] at h1
  exact h1

noncomputable def hc : SL(2, K) := sl2Diag K (Units.mk0 S.c S.c_ne_zero)

omit [Finite K] [CharP K 2] [Finite M] in
theorem hc_ne_one : S.hc ≠ 1 := sl2Diag_ne_one (by rw [Units.val_mk0]; exact S.c_ne_one)

omit [Finite K] [CharP K 2] [Finite M] in
theorem hc_pow : S.hc ^ orderOf S.c = 1 := by
  rw [hc, ← sl2Diag_pow]
  have : Units.mk0 S.c S.c_ne_zero ^ orderOf S.c = 1 :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, pow_orderOf_eq_one, Units.val_one])
  rw [this, sl2Diag_one]

omit [Finite K] [CharP K 2] [Finite M] in
theorem hc_mul_weyl : S.hc * sl2Weyl K 1 = sl2Weyl K 1 * S.hc⁻¹ := by
  rw [hc, sl2Diag_mul_weyl]
  congr 1
  rw [eq_inv_iff_mul_eq_one, ← sl2Diag_mul, inv_mul_cancel, sl2Diag_one]

omit [CharP K 2] [Finite M] in
theorem odd_orderOf_c : Odd (orderOf S.c) := by
  have : Fintype K := Fintype.ofFinite K
  have h1 : orderOf S.c ∣ Fintype.card K - 1 :=
    orderOf_dvd_of_pow_eq_one (FiniteField.pow_card_sub_one_eq_one S.c S.c_ne_zero)
  have h2 : Odd (Fintype.card K - 1) := by
    rw [Fintype.card_eq_nat_card, S.card_K, Nat.odd_iff]
    have h3 : 2 ^ S.f = 2 * 2 ^ (S.f - 1) := by
      rw [← pow_succ']
      congr 1
      have := S.two_le
      omega
    have h4 : 1 ≤ 2 ^ (S.f - 1) := Nat.one_le_two_pow
    omega
  exact h2.of_dvd_nat h1

theorem eigen_alt {Z : Submodule (ZMod 2) M} (hZX : ∀ B, ∀ z ∈ Z, S.α B z ∈ Z) {k : ℕ}
    (hk : ∀ z ∈ Z, S.β S.hc z = (S.h₀ ^ k) z) {j : ℕ} {z : M} (hz : z ∈ Z) (hz0 : z ≠ 0)
    (hj : S.α S.hc z = (S.h₀ ^ j) z) : S.c ^ k = 1 ∨ S.c ^ j = 1 := by
  set n := orderOf S.c with hn
  set j' := j * (n - 1) with hj'
  have hn1 : 1 ≤ n := S.odd_orderOf_c.pos
  have hjj : S.c ^ (j + j') = 1 := by
    rw [hj', show j + j * (n - 1) = j * n by
      rw [Nat.mul_sub, mul_one, Nat.add_sub_cancel' (Nat.le_mul_of_pos_right j hn1)], pow_mul',
      hn, pow_orderOf_eq_one, one_pow]
  have hhjj : S.h₀ ^ (j + j') = 1 := S.h₀_pow_eq_one hjj
  have hinv : S.α S.hc⁻¹ z = (S.h₀ ^ j') z := by
    calc S.α S.hc⁻¹ z = S.α S.hc⁻¹ ((S.h₀ ^ (j' + j)) z) := by
          rw [add_comm, hhjj, Module.End.one_apply]
      _ = (S.h₀ ^ j') (S.α S.hc⁻¹ (S.α S.hc z)) := by
          rw [pow_add, Module.End.mul_apply, S.h₀_pow_α, ← hj]
      _ = (S.h₀ ^ j') z := by
          rw [← Module.End.mul_apply (S.α S.hc⁻¹), ← map_mul, inv_mul_cancel, map_one,
            Module.End.one_apply]
  have h1 : S.α S.hc (S.β S.hc z) = (S.h₀ ^ (k + j)) z := by
    rw [hk z hz, ← S.h₀_pow_α, hj, pow_add, Module.End.mul_apply]
  set w := sl2Weyl K 1
  have hwz : S.α w z ∈ Z := hZX w z hz
  have hwz0 : S.α w z ≠ 0 := fun h0 => hz0 (by
    have := congrArg (S.α w⁻¹) h0
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
      map_zero] at this)
  have h2 : S.α S.hc (S.β S.hc (S.α w z)) = (S.h₀ ^ (k + j')) (S.α w z) := by
    rw [hk _ hwz, ← S.h₀_pow_α, ← Module.End.mul_apply (S.α S.hc), ← map_mul, S.hc_mul_weyl,
      map_mul, Module.End.mul_apply, hinv, ← S.h₀_pow_α, pow_add, Module.End.mul_apply]
  have e1 := S.eigen_δ hz0 (k + j) h1
  have e2 := S.eigen_δ hwz0 (k + j') h2
  have hcj : S.c ^ j' = (S.c ^ j)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← pow_add, add_comm, hjj])
  rw [pow_add] at e1
  rw [pow_add, hcj] at e2
  have hc0 := S.c_ne_zero
  have hk0 : S.c ^ k ≠ 0 := pow_ne_zero _ hc0
  have hj0 : S.c ^ j ≠ 0 := pow_ne_zero _ hc0
  have hyy : S.c ^ j * (S.c ^ j)⁻¹ = 1 := mul_inv_cancel₀ hj0
  have hcc : S.c * S.c⁻¹ = 1 := mul_inv_cancel₀ hc0
  have hprod : (S.c ^ k * S.c ^ j) * (S.c ^ k * (S.c ^ j)⁻¹) = (S.c ^ k) ^ 2 := by
    calc _ = (S.c ^ k) ^ 2 * (S.c ^ j * (S.c ^ j)⁻¹) := by ring
      _ = _ := by rw [hyy, mul_one]
  have hsq : S.c ^ k * S.c ^ j = S.c ^ k * (S.c ^ j)⁻¹ → S.c ^ j = 1 := by
    intro h3
    apply eq_one_of_sq_eq_one
    have h4 : S.c ^ j = (S.c ^ j)⁻¹ := mul_left_cancel₀ hk0 h3
    rw [sq]
    nth_rewrite 2 [h4]
    exact hyy
  rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2
  · exact Or.inr (hsq (e1.trans e2.symm))
  · exact Or.inl (eq_one_of_sq_eq_one (by rw [← hprod, e1, e2, hcc]))
  · exact Or.inl (eq_one_of_sq_eq_one (by rw [← hprod, e1, e2, mul_comm, hcc]))
  · exact Or.inr (hsq (e1.trans e2.symm))

theorem fixY_ne_bot : S.fixY ≠ ⊥ := by
  intro hY
  have : Module.Finite (ZMod 2) M := Module.Finite.of_finite
  have hX : S.fixX = ⊥ := by
    rw [eq_bot_iff]
    intro m hm
    have h1 := S.τ_mem_fixY hm
    rw [hY, Submodule.mem_bot] at h1
    rw [Submodule.mem_bot, ← S.τ_τ m, h1, map_zero]
  obtain ⟨-, hsup⟩ := S.Zup_Zlow hX hY
  have hu1 := sl2Upper_mul_self (K := K) 1
  have hu1' := sl2Upper_ne_one (K := K) one_ne_zero
  have hl1 := sl2Lower_mul_self (K := K) 1
  have hl1' := sl2Lower_ne_one (K := K) one_ne_zero
  set Zu := S.Zof (sl2Upper K 1) with hZu
  set Zl := S.Zof (sl2Lower K 1) with hZl
  set w := sl2Weyl K 1 with hw
  set cu : Kˣ := Units.mk0 S.c S.c_ne_zero with hcu
  have hinvβ : ∀ (B : SL(2, K)) (m : M), S.β B⁻¹ (S.β B m) = m := fun B m => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hhZu : ∀ z ∈ Zu, S.β S.hc z ∈ Zu := by
    intro z hz
    have hmat : sl2Upper K 1 * S.hc = S.hc * sl2Upper K (((cu⁻¹ : Kˣ) : K) ^ 2) := by
      rw [hc, CFSG.LocalAnalysis.ComponentInitial.sl2Diag_mul_upper, ← mul_pow, ← hcu,
        Units.mul_inv, one_pow]
    have hne : ((cu⁻¹ : Kˣ) : K) ^ 2 ≠ 0 := pow_ne_zero _ (Units.ne_zero _)
    have hZ := S.Zof_eq_of_commute hX hu1 hu1' (sl2Upper_mul_self _) (sl2Upper_ne_one hne)
      (sl2Upper_comm _ _)
    have hz' : z ∈ S.Zof (sl2Upper K (((cu⁻¹ : Kˣ) : K) ^ 2)) := hZ ▸ hz
    rw [S.mem_Zof] at hz' ⊢
    rw [← Module.End.mul_apply, ← map_mul, hmat, map_mul, Module.End.mul_apply, hz']
  have hwZ : ∀ z ∈ Zu, S.β w z ∈ Zl := by
    intro z hz
    have hmat : sl2Lower K 1 * w = w * sl2Upper K (-1) := by
      rw [hw, CFSG.LocalAnalysis.ComponentInitial.sl2Weyl_mul_upper]
      congr 2
      simp
    have hne : (-1 : K) ≠ 0 := neg_ne_zero.mpr one_ne_zero
    have hZ := S.Zof_eq_of_commute hX hu1 hu1' (sl2Upper_mul_self _) (sl2Upper_ne_one hne)
      (sl2Upper_comm _ _)
    have hz' : z ∈ S.Zof (sl2Upper K (-1)) := hZ ▸ hz
    rw [S.mem_Zof] at hz' ⊢
    rw [← Module.End.mul_apply, ← map_mul, hmat, map_mul, Module.End.mul_apply, hz']
  have hβw_inj : Function.Injective (S.β w) := fun x y hxy => by
    rw [← hinvβ w x, hxy, hinvβ w y]
  have hZl_eq : ∀ z ∈ Zl, ∃ z' ∈ Zu, S.β w z' = z := by
    have hle : Zu.map (S.β w) ≤ Zl := by
      rintro _ ⟨z, hz, rfl⟩
      exact hwZ z hz
    have hfin : finrank (ZMod 2) (Zu.map (S.β w)) = finrank (ZMod 2) Zl := by
      rw [← LinearEquiv.finrank_eq (Submodule.equivMapOfInjective (S.β w) hβw_inj Zu),
        (S.finrank_Zof hX hu1 hu1').1, (S.finrank_Zof hX hl1 hl1').1]
    have heq := Submodule.eq_of_le_of_finrank_eq hle hfin
    intro z hz
    rw [← heq] at hz
    obtain ⟨z', hz', rfl⟩ := hz
    exact ⟨z', hz', rfl⟩
  have hβh_pow : S.β S.hc ^ orderOf S.c = 1 := by rw [← map_pow, S.hc_pow, map_one]
  have hβh_h₀ : S.β S.hc * S.h₀ = S.h₀ * S.β S.hc := by
    ext z
    simp only [Module.End.mul_apply, S.h₀_β_apply]
  obtain ⟨k, z₀, hz₀, hz₀0, hk₀⟩ := S.exists_eigen (S.β S.hc) hβh_h₀ hβh_pow Zu hhZu
    (fun z hz => S.h₀_mem_Zof hz) (S.Zof_ne_bot hX hu1 hu1')
  have hk : ∀ z ∈ Zu, S.β S.hc z = (S.h₀ ^ k) z := by
    set E := Zu ⊓ LinearMap.ker (S.β S.hc - S.h₀ ^ k) with hE
    have hEinv : ∀ B, ∀ u ∈ E, S.α B u ∈ E := by
      intro B u hu
      obtain ⟨hu1, hu2⟩ := Submodule.mem_inf.mp hu
      refine Submodule.mem_inf.mpr ⟨S.α_mem_Zof B hu1, ?_⟩
      rw [LinearMap.mem_ker, LinearMap.sub_apply] at hu2 ⊢
      rw [← S.α_β, S.h₀_pow_α, ← map_sub, hu2, map_zero]
    have hEne : E ≠ ⊥ := by
      intro hbot
      have : z₀ ∈ E := Submodule.mem_inf.mpr ⟨hz₀, by
        rw [LinearMap.mem_ker, LinearMap.sub_apply, hk₀, sub_self]⟩
      rw [hbot, Submodule.mem_bot] at this
      exact hz₀0 this
    have hEZ := S.eq_Zof_of_le hX hu1 hu1' E hEinv inf_le_left hEne
    intro z hz
    have hzE : z ∈ E := by rw [hEZ]; exact hz
    have := (Submodule.mem_inf.mp hzE).2
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
    exact this
  have hck : S.c ^ k ≠ 1 := by
    intro hck
    have h1 := S.h₀_pow_eq_one hck
    have hu : ∀ z ∈ Zu, S.β S.hc z = z := fun z hz => by
      rw [hk z hz, h1, Module.End.one_apply]
    apply S.hc_ne_one
    refine S.eq_one_of_β_eq_one fun m => ?_
    have hm : m ∈ Zu ⊔ Zl := hsup ▸ Submodule.mem_top
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hm
    rw [map_add, hu a ha]
    congr 1
    obtain ⟨b', hb', rfl⟩ := hZl_eq b hb
    rw [← Module.End.mul_apply, ← map_mul, S.hc_mul_weyl, map_mul, Module.End.mul_apply]
    congr 1
    calc S.β S.hc⁻¹ b' = S.β S.hc⁻¹ (S.β S.hc b') := by rw [hu b' hb']
      _ = b' := hinvβ _ _
  have hj : ∀ z ∈ Zu, z ≠ 0 → ∀ j, S.α S.hc z = (S.h₀ ^ j) z → S.c ^ j = 1 :=
    fun z hz hz0 j hzj =>
      (S.eigen_alt (fun B z hz => S.α_mem_Zof B hz) hk hz hz0 hzj).resolve_left hck
  have hαh_pow : S.α S.hc ^ orderOf S.c = 1 := by rw [← map_pow, S.hc_pow, map_one]
  have hαh_h₀ : S.α S.hc * S.h₀ = S.h₀ * S.α S.hc := (S.h₀_α S.hc).symm
  have hαZu : ∀ z ∈ Zu, S.α S.hc z = z := by
    by_contra hcon
    push Not at hcon
    obtain ⟨z₁, hz₁, hz₁ne⟩ := hcon
    set U' := Zu.map (S.α S.hc - 1) with hU'
    have hU'g : ∀ u ∈ U', S.α S.hc u ∈ U' := by
      rintro _ ⟨z, hz, rfl⟩
      refine ⟨S.α S.hc z, S.α_mem_Zof _ hz, ?_⟩
      simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]
    have hU'h : ∀ u ∈ U', S.h₀ u ∈ U' := by
      rintro _ ⟨z, hz, rfl⟩
      refine ⟨S.h₀ z, S.h₀_mem_Zof hz, ?_⟩
      simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, S.h₀_α_apply]
    have hU'ne : U' ≠ ⊥ := by
      intro hbot
      have : (S.α S.hc - 1) z₁ ∈ U' := ⟨z₁, hz₁, rfl⟩
      rw [hbot, Submodule.mem_bot, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at this
      exact hz₁ne this
    obtain ⟨j, u, hu, hu0, huj⟩ := S.exists_eigen (S.α S.hc) hαh_h₀ hαh_pow U' hU'g hU'h hU'ne
    obtain ⟨z, hz, rfl⟩ := hu
    have hzZ : (S.α S.hc - 1) z ∈ Zu := by
      rw [LinearMap.sub_apply, Module.End.one_apply]
      exact sub_mem (S.α_mem_Zof _ hz) hz
    have hfix : S.α S.hc ((S.α S.hc - 1) z) = (S.α S.hc - 1) z := by
      rw [huj, S.h₀_pow_eq_one (hj _ hzZ hu0 j huj), Module.End.one_apply]
    rw [LinearMap.sub_apply, Module.End.one_apply] at hfix hu0
    exact hu0 (eq_zero_of_odd (S.α S.hc) S.odd_orderOf_c hαh_pow z hfix)
  apply S.hc_ne_one
  apply S.α_injective
  ext m
  rw [map_one, Module.End.one_apply]
  have hm : m ∈ Zu ⊔ Zl := hsup ▸ Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hm
  obtain ⟨b', hb', rfl⟩ := hZl_eq b hb
  rw [map_add, hαZu a ha, S.α_β, hαZu b' hb']

end Contradiction

@[expose] noncomputable def ιAddEquiv : (Fin 2 → K) ≃+ S.fixτ :=
  AddEquiv.ofBijective
    (AddMonoidHom.mk' (fun v => (⟨S.ι v, S.mem_fixτ.mpr (S.τ_ι v)⟩ : S.fixτ))
      (fun v w => Subtype.ext (map_add S.ι v w))) S.ιEquiv.bijective

theorem ιAddEquiv_apply (v : Fin 2 → K) : (S.ιAddEquiv v : M) = S.ι v := rfl

@[expose] noncomputable def fixYToFixτ : S.fixY →+ S.fixτ where
  toFun p := ⟨S.τ p - p, S.mem_fixτ.mpr (S.τ_sub_mem p)⟩
  map_zero' := Subtype.ext (by simp)
  map_add' p q := Subtype.ext (by
    change S.τ (p + q : M) - (p + q : M) = (S.τ p - p) + (S.τ q - q)
    rw [map_add]
    abel)

theorem exists_decomp [Finite K] [CharP K 2] [Finite M] :
    finrank (ZMod 2) S.fixY = 2 * S.f ∧ S.fixY ⊓ S.fixX = ⊥ ∧ S.fixY ⊔ S.fixX = ⊤ ∧
      (∀ m, m ∈ S.fixX ↔ S.τ m ∈ S.fixY) ∧
      ∃ θ : S.fixY ≃+ (Fin 2 → K), (∀ p : S.fixY, S.ι (θ p) = S.τ p - p) ∧
        ∀ (B : SL(2, K)) (p : S.fixY),
          θ ⟨S.α B p, S.α_mem_fixY B p.2⟩ = (B : Matrix (Fin 2) (Fin 2) K) *ᵥ θ p := by
  obtain ⟨hdim, hinf, hsup⟩ := S.decomp_of_ne_bot S.fixY_ne_bot
  have hXY : ∀ m, m ∈ S.fixX ↔ S.τ m ∈ S.fixY := fun m =>
    ⟨S.τ_mem_fixY, fun h => by rw [← S.τ_τ m]; exact S.τ_mem_fixX h⟩
  set φ : S.fixY →+ (Fin 2 → K) := S.ιAddEquiv.symm.toAddMonoidHom.comp S.fixYToFixτ with hφ
  have hφι : ∀ p : S.fixY, S.ι (φ p) = S.τ p - p := fun p => by
    rw [← S.ιAddEquiv_apply]
    simp [φ, fixYToFixτ]
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro p hp
    have h1 : S.τ p - p = 0 := by rw [← hφι p, hp, map_zero]
    have h2 : (p : M) ∈ S.fixY ⊓ S.fixX := Submodule.mem_inf.mpr
      ⟨p.2, (hXY p).mpr (by rw [sub_eq_zero.mp h1]; exact p.2)⟩
    rw [hinf, Submodule.mem_bot] at h2
    exact Subtype.ext h2
  have hbij : Function.Bijective φ := by
    refine hinj.bijective_of_nat_card_le ?_
    rw [natCard_submodule, hdim, Nat.card_fun, Nat.card_fin, S.card_K, ← pow_mul, mul_comm]
  refine ⟨hdim, hinf, hsup, hXY, AddEquiv.ofBijective φ hbij, hφι, fun B p => ?_⟩
  apply S.ι_injective
  change S.ι (φ ⟨S.α B p, S.α_mem_fixY B p.2⟩) = S.ι ((B : Matrix (Fin 2) (Fin 2) K) *ᵥ φ p)
  rw [hφι, ← S.δ_ι, hφι]
  change S.τ (S.α B p) - S.α B p = S.α B (S.β B (S.τ p - p))
  have hp : S.β B p = p := (S.mem_fixY.mp p.2) B
  have hq : S.α B (S.τ (S.α B p)) = S.τ (S.α B p) :=
    (S.mem_fixX.mp ((hXY _).mpr (by rw [S.τ_τ]; exact S.α_mem_fixY B p.2))) B
  rw [map_sub, map_sub, hp, ← S.τ_α, hq]

end SwapData

end CFSG.LocalAnalysis.EvenBN.LinearThree.CaseBModule
