module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenAux6
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenAux5

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8

set_option linter.unusedSectionVars false


theorem card_ge_two (K : Type) [Field K] [Finite K] : 2 ≤ Nat.card K := Finite.one_lt_card

theorem exists_AS {K L : Type} [Field K] [Finite K] [Field L] [IsAlgClosed L] {a : L} (ha : a ≠ 0)
    (r : L) : ∃ z : L, z = r + a * z ^ Nat.card K := by
  have hq := card_ge_two K
  set q := Nat.card K with hqdef
  have hdeg : (Polynomial.C (-a) * Polynomial.X ^ q + (Polynomial.X - Polynomial.C r)).degree ≠ 0 := by
    rw [Polynomial.degree_add_eq_left_of_degree_lt]
    · rw [Polynomial.degree_C_mul_X_pow q (neg_ne_zero.2 ha)]
      exact_mod_cast (by omega : q ≠ 0)
    · rw [Polynomial.degree_C_mul_X_pow q (neg_ne_zero.2 ha), Polynomial.degree_X_sub_C]
      exact_mod_cast (by omega : 1 < q)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root _ hdeg
  refine ⟨z, ?_⟩
  simp only [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub] at hz
  linear_combination hz

theorem exists_pair_set (K L : Type) [Field K] [Finite K] [Field L] [Algebra K L] [IsAlgClosed L]
    (ε₁ ε₂ : L) (h1 : ε₁ * ε₁ = 1) (h2 : ε₂ * ε₂ = 1) :
    ∃ C : Finset L, C.card = Nat.card K ^ 2 ∧
      ∀ c ∈ C, c ^ (Nat.card K ^ 2) = (ε₂ * ε₁ ^ Nat.card K) * c := by
  have hq := card_ge_two K
  have hκ : ε₂ * ε₁ ^ Nat.card K ≠ 0 := by
    refine mul_ne_zero ?_ (pow_ne_zero _ ?_)
    · intro h0; rw [h0, mul_zero] at h2; exact zero_ne_one h2
    · intro h0; rw [h0, mul_zero] at h1; exact zero_ne_one h1
  exact exists_finset_pow (Nat.card K ^ 2) (by nlinarith) (by
    rw [Nat.cast_pow, natCast_card_eq_zero (K := K)]; simp) hκ

theorem kappa_sq {L : Type} [Field L] (q : ℕ) (ε₁ ε₂ : L) (h1 : ε₁ * ε₁ = 1) (h2 : ε₂ * ε₂ = 1) :
    (ε₂ * ε₁ ^ q) * (ε₂ * ε₁ ^ q) = 1 := by
  calc (ε₂ * ε₁ ^ q) * (ε₂ * ε₁ ^ q)
      = (ε₂ * ε₂) * (ε₁ * ε₁) ^ q := by rw [mul_pow]; ring
    _ = 1 := by rw [h1, h2, one_pow, one_mul]

structure Setup (K L : Type) [Field K] [Finite K] [Field L] [Algebra K L] where
  Fr : L →+* L
  hFr : ∀ c, Fr c = c ^ Nat.card K
  hbij : Function.Bijective Fr
  h : ModGL Tag.E8 L
  n : ModGL Tag.E8 L
  hh : h ∈ adjointGroup Tag.E8 L
  hlang : Frob Fr h = h * n
  w : WeylGroup Tag.E8
  sg : (Fin Tag.E8.rank → ℤ) → L
  hm : Mono n w sg
  hθ : w • highRoot Tag.E8 = highRoot Tag.E8
  hD : ∀ μ ∈ Deg1 Tag.E8, w • μ ∈ Deg1 Tag.E8
  H : Subgroup (ModGL Tag.E8 K)

namespace Setup

variable {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L] (S : Setup K L)

theorem hfix (a : K) : S.Fr (algebraMap K L a) = algebraMap K L a := by
  have : Fintype K := Fintype.ofFinite K
  rw [S.hFr, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]

@[expose] def XLink (Xbar : Subgroup (ModGL Tag.E8 L)) : Prop :=
  ∀ l₀ ∈ adjointGroup Tag.E8 K,
    S.h⁻¹ * baseChangeGL (algebraMap K L) l₀ * S.h ∈ Xbar → l₀ ∈ S.H

theorem hn : ActsBy S.n (Mg S.w S.sg) := actsBy_mono S.hm S.hθ S.hD

theorem sg_ne_zero {μ : Fin Tag.E8.rank → ℤ} (hμ : IsRoot Tag.E8 μ) : S.sg μ ≠ 0 := by
  intro h0
  have := (S.hm μ hμ).1
  rw [h0, mul_zero] at this
  exact zero_ne_one this


variable [IsAlgClosed L]

theorem Einv_fixed (Xbar : Subgroup (ModGL Tag.E8 L)) (hX : S.XLink Xbar)
    {γ : Fin Tag.E8.rank → ℤ} (hγ : γ ∈ rootFinset Tag.E8) (hγ0 : γ 7 = 0) (hwγ : S.w • γ = γ)
    (hγX : ∀ t, pinnedX Tag.E8 L γ t ∈ Xbar) :
    ∀ u ∈ Uspace S.h S.H, Eop aE8 γ u ∈ Uspace S.h S.H := by
  obtain ⟨hsq, hc⟩ := S.hm γ (mem_rootFinset.1 hγ)
  have hq := card_ge_two K
  have hne := S.sg_ne_zero (mem_rootFinset.1 hγ)
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (S.sg γ) (show 0 < Nat.card K - 1 by omega)
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at ht
    exact hne ht.symm
  have hpow : t ^ Nat.card K = S.sg γ * t := by
    calc t ^ Nat.card K = t ^ (Nat.card K - 1 + 1) := by congr 1; omega
      _ = t ^ (Nat.card K - 1) * t := pow_succ _ _
      _ = S.sg γ * t := by rw [ht]
  have hσ : S.n * Frob S.Fr (pinnedX Tag.E8 L γ t) * S.n⁻¹ = pinnedX Tag.E8 L γ t := by
    rw [Frob_pinnedX, hc, hwγ]
    congr 1
    rw [S.hFr t, hpow, ← mul_assoc, hsq, one_mul]
  have hxA : pinnedX Tag.E8 L γ t ∈ adjointGroup Tag.E8 L :=
    rootSubgroup_le_adjointGroup γ (mem_rootSubgroup.2 ⟨t, rfl⟩)
  obtain ⟨l₀, hl₀H, hl₀⟩ := ratop_of_sfixed S.Fr S.hFr S.hbij S.hh S.hlang hX hxA (hγX t) hσ
  exact inv_of_actOp ht0 (Uspace_inv S.h S.H (actsBy_pinnedX hγ hγ0 t) hl₀H hl₀)

theorem Einv_perp (Xbar : Subgroup (ModGL Tag.E8 L)) (hX : S.XLink Xbar)
    {γ₁ γ₂ : Fin Tag.E8.rank → ℤ} (hγ₁ : γ₁ ∈ rootFinset Tag.E8) (hγ₁0 : γ₁ 7 = 0)
    (hγ₂ : γ₂ ∈ rootFinset Tag.E8) (hγ₂0 : γ₂ 7 = 0) (hw₁ : S.w • γ₁ = γ₂) (hw₂ : S.w • γ₂ = γ₁)
    (hcomm : ∀ s t : L, pinnedX Tag.E8 L γ₁ s * pinnedX Tag.E8 L γ₂ t =
      pinnedX Tag.E8 L γ₂ t * pinnedX Tag.E8 L γ₁ s)
    (hX₁ : ∀ t, pinnedX Tag.E8 L γ₁ t ∈ Xbar) (hX₂ : ∀ t, pinnedX Tag.E8 L γ₂ t ∈ Xbar) :
    (∀ u ∈ Uspace S.h S.H, Eop aE8 γ₁ u ∈ Uspace S.h S.H) ∧
      (∀ u ∈ Uspace S.h S.H, Eop aE8 γ₂ u ∈ Uspace S.h S.H) := by
  obtain ⟨hs₁, hc₁⟩ := S.hm γ₁ (mem_rootFinset.1 hγ₁)
  obtain ⟨hs₂, hc₂⟩ := S.hm γ₂ (mem_rootFinset.1 hγ₂)
  have hq := card_ge_two K
  obtain ⟨C, hCcard, hCpow⟩ := exists_pair_set K L (S.sg γ₁) (S.sg γ₂) hs₁ hs₂
  have hκ2 := kappa_sq (Nat.card K) (S.sg γ₁) (S.sg γ₂) hs₁ hs₂
  refine inv_of_pair hq C (by rw [hCcard]) (S.sg_ne_zero (mem_rootFinset.1 hγ₁)) ?_
  intro c hc u hu
  set d : L := S.sg γ₁ * c ^ Nat.card K with hd
  have hFc : S.sg γ₁ * S.Fr c = d := by rw [S.hFr c]
  have hFd : S.sg γ₂ * S.Fr d = c := by
    have e1 : S.Fr d = S.sg γ₁ ^ Nat.card K * c ^ (Nat.card K ^ 2) := by
      rw [hd, map_mul, map_pow, S.hFr (S.sg γ₁), S.hFr c, ← pow_mul, sq]
    rw [e1, hCpow c hc]
    calc S.sg γ₂ * (S.sg γ₁ ^ Nat.card K * ((S.sg γ₂ * S.sg γ₁ ^ Nat.card K) * c))
        = ((S.sg γ₂ * S.sg γ₁ ^ Nat.card K) * (S.sg γ₂ * S.sg γ₁ ^ Nat.card K)) * c := by ring
      _ = c := by rw [hκ2, one_mul]
  have hσ : S.n * Frob S.Fr (pinnedX Tag.E8 L γ₁ c * pinnedX Tag.E8 L γ₂ d) * S.n⁻¹ =
      pinnedX Tag.E8 L γ₁ c * pinnedX Tag.E8 L γ₂ d := by
    have e : S.n * (pinnedX Tag.E8 L γ₁ (S.Fr c) * pinnedX Tag.E8 L γ₂ (S.Fr d)) * S.n⁻¹ =
        (S.n * pinnedX Tag.E8 L γ₁ (S.Fr c) * S.n⁻¹) *
          (S.n * pinnedX Tag.E8 L γ₂ (S.Fr d) * S.n⁻¹) := by group
    rw [map_mul, Frob_pinnedX, Frob_pinnedX, e, hc₁ (S.Fr c), hc₂ (S.Fr d), hw₁, hw₂, hFc, hFd]
    exact (hcomm c d).symm
  have hxA : pinnedX Tag.E8 L γ₁ c * pinnedX Tag.E8 L γ₂ d ∈ adjointGroup Tag.E8 L :=
    mul_mem (rootSubgroup_le_adjointGroup γ₁ (mem_rootSubgroup.2 ⟨c, rfl⟩))
      (rootSubgroup_le_adjointGroup γ₂ (mem_rootSubgroup.2 ⟨d, rfl⟩))
  obtain ⟨l₀, hl₀H, hl₀⟩ := ratop_of_sfixed S.Fr S.hFr S.hbij S.hh S.hlang hX hxA
    (mul_mem (hX₁ c) (hX₂ d)) hσ
  exact Uspace_inv S.h S.H ((actsBy_pinnedX hγ₁ hγ₁0 c).mul (actsBy_pinnedX hγ₂ hγ₂0 d)) hl₀H hl₀ u hu

theorem Einv_A2 (Xbar : Subgroup (ModGL Tag.E8 L)) (hX : S.XLink Xbar)
    {γ₁ γ₂ γ₃ : Fin Tag.E8.rank → ℤ} (hγ₁ : γ₁ ∈ rootFinset Tag.E8) (hγ₁0 : γ₁ 7 = 0)
    (hγ₂ : γ₂ ∈ rootFinset Tag.E8) (hγ₂0 : γ₂ 7 = 0) (hγ₃ : γ₃ ∈ lxRoots)
    (hw₁ : S.w • γ₁ = γ₂) (hw₂ : S.w • γ₂ = γ₁) (hw₃ : S.w • γ₃ = γ₃) (η : L)
    (hcomm : ∀ a b : L, pinnedX Tag.E8 L γ₂ a * pinnedX Tag.E8 L γ₁ b =
      pinnedX Tag.E8 L γ₁ b * pinnedX Tag.E8 L γ₂ a * pinnedX Tag.E8 L γ₃ (η * a * b))
    (hX₁ : ∀ t, pinnedX Tag.E8 L γ₁ t ∈ Xbar) (hX₂ : ∀ t, pinnedX Tag.E8 L γ₂ t ∈ Xbar)
    (hX₃ : ∀ t, pinnedX Tag.E8 L γ₃ t ∈ Xbar)
    (hE₃ : ∀ u ∈ Uspace S.h S.H, Eop aE8 γ₃ u ∈ Uspace S.h S.H) :
    (∀ u ∈ Uspace S.h S.H, Eop aE8 γ₁ u ∈ Uspace S.h S.H) ∧
      (∀ u ∈ Uspace S.h S.H, Eop aE8 γ₂ u ∈ Uspace S.h S.H) := by
  have hγ₃r : γ₃ ∈ rootFinset Tag.E8 := (lxRoots_data γ₃ hγ₃).1
  have hγ₃0 : γ₃ 7 = 0 := (lxRoots_data γ₃ hγ₃).2.1
  obtain ⟨hs₁, hc₁⟩ := S.hm γ₁ (mem_rootFinset.1 hγ₁)
  obtain ⟨hs₂, hc₂⟩ := S.hm γ₂ (mem_rootFinset.1 hγ₂)
  obtain ⟨hs₃, hc₃⟩ := S.hm γ₃ (mem_rootFinset.1 hγ₃r)
  have hq := card_ge_two K
  obtain ⟨C, hCcard, hCpow⟩ := exists_pair_set K L (S.sg γ₁) (S.sg γ₂) hs₁ hs₂
  have hκ2 := kappa_sq (Nat.card K) (S.sg γ₁) (S.sg γ₂) hs₁ hs₂
  refine inv_of_pair hq C (by rw [hCcard]) (S.sg_ne_zero (mem_rootFinset.1 hγ₁)) ?_
  intro c hc u hu
  set d : L := S.sg γ₁ * c ^ Nat.card K with hd
  have hFc : S.sg γ₁ * S.Fr c = d := by rw [S.hFr c]
  have hFd : S.sg γ₂ * S.Fr d = c := by
    have e1 : S.Fr d = S.sg γ₁ ^ Nat.card K * c ^ (Nat.card K ^ 2) := by
      rw [hd, map_mul, map_pow, S.hFr (S.sg γ₁), S.hFr c, ← pow_mul, sq]
    rw [e1, hCpow c hc]
    calc S.sg γ₂ * (S.sg γ₁ ^ Nat.card K * ((S.sg γ₂ * S.sg γ₁ ^ Nat.card K) * c))
        = ((S.sg γ₂ * S.sg γ₁ ^ Nat.card K) * (S.sg γ₂ * S.sg γ₁ ^ Nat.card K)) * c := by ring
      _ = c := by rw [hκ2, one_mul]
  obtain ⟨z, hz⟩ := exists_AS (K := K) (S.sg_ne_zero (mem_rootFinset.1 hγ₃r)) (η * c * d)
  have hσ : S.n * Frob S.Fr (pinnedX Tag.E8 L γ₁ c * pinnedX Tag.E8 L γ₂ d *
      pinnedX Tag.E8 L γ₃ z) * S.n⁻¹ =
      pinnedX Tag.E8 L γ₁ c * pinnedX Tag.E8 L γ₂ d * pinnedX Tag.E8 L γ₃ z := by
    have e : S.n * (pinnedX Tag.E8 L γ₁ (S.Fr c) * pinnedX Tag.E8 L γ₂ (S.Fr d) *
        pinnedX Tag.E8 L γ₃ (S.Fr z)) * S.n⁻¹ =
        (S.n * pinnedX Tag.E8 L γ₁ (S.Fr c) * S.n⁻¹) *
          (S.n * pinnedX Tag.E8 L γ₂ (S.Fr d) * S.n⁻¹) *
          (S.n * pinnedX Tag.E8 L γ₃ (S.Fr z) * S.n⁻¹) := by group
    rw [map_mul, map_mul, Frob_pinnedX, Frob_pinnedX, Frob_pinnedX, e, hc₁ (S.Fr c),
      hc₂ (S.Fr d), hc₃ (S.Fr z), hw₁, hw₂, hw₃, hFc, hFd, hcomm d c,
      mul_assoc (pinnedX Tag.E8 L γ₁ c * pinnedX Tag.E8 L γ₂ d), ← pinnedX_add]
    have hzz : η * d * c + S.sg γ₃ * S.Fr z = z := by
      rw [S.hFr z]
      linear_combination (-1 : L) * hz
    rw [hzz]
  have hxA : pinnedX Tag.E8 L γ₁ c * pinnedX Tag.E8 L γ₂ d * pinnedX Tag.E8 L γ₃ z ∈
      adjointGroup Tag.E8 L :=
    mul_mem (mul_mem (rootSubgroup_le_adjointGroup γ₁ (mem_rootSubgroup.2 ⟨c, rfl⟩))
      (rootSubgroup_le_adjointGroup γ₂ (mem_rootSubgroup.2 ⟨d, rfl⟩)))
      (rootSubgroup_le_adjointGroup γ₃ (mem_rootSubgroup.2 ⟨z, rfl⟩))
  obtain ⟨l₀, hl₀H, hl₀⟩ := ratop_of_sfixed S.Fr S.hFr S.hbij S.hh S.hlang hX hxA
    (mul_mem (mul_mem (hX₁ c) (hX₂ d)) (hX₃ z)) hσ
  have hfull := Uspace_inv S.h S.H (((actsBy_pinnedX hγ₁ hγ₁0 c).mul (actsBy_pinnedX hγ₂ hγ₂0 d)).mul
    (actsBy_pinnedX hγ₃r hγ₃0 z)) hl₀H hl₀
  exact strip_middle (fun v hv ν hν => by
      have := Uspace_supp S.h S.H hv ν (fun hh => hν ((mem_deg1Roots).2 hh))
      exact this) hγ₃ hE₃ (actOp aE8 γ₁ c ∘ₗ actOp aE8 γ₂ d) z (fun v hv => hfull v hv) u hu

end Setup

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux
