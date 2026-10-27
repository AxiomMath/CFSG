module

public import CFSG.LinearAlgebra.UnitaryInvolutionIndex.SmallDimension
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

public section

namespace CFSG.UnitaryInvolutionIndex

open Module Module.End

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

theorem apply_mem_eigenspace_inv {f g T : End k V} (hfg : f * g = 1) (hTf : T * f = g * T)
    {μ : k} (hμ : μ ≠ 0) {v : V} (hv : v ∈ f.eigenspace μ) : T v ∈ f.eigenspace μ⁻¹ := by
  rw [mem_eigenspace_iff] at hv ⊢
  have h1 : g (T v) = μ • T v := by rw [← mul_apply, ← hTf, mul_apply, hv, map_smul]
  have h2 : f (g (T v)) = T v := by rw [← mul_apply, hfg, one_apply]
  rw [h1, map_smul] at h2
  calc f (T v) = μ⁻¹ • μ • f (T v) := by rw [smul_smul, inv_mul_cancel₀ hμ, one_smul]
    _ = μ⁻¹ • T v := by rw [h2]

theorem eq_one_of_inv_eq_self {μ : k} {N : ℕ} (hN : Odd N) (hμN : μ ^ N = 1) (hμ : μ⁻¹ = μ) :
    μ = 1 := by
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by obtain ⟨r, hr⟩ := hN; omega)] at hμN
    exact zero_ne_one hμN
  have h2 : μ ^ 2 = 1 := by
    rw [sq]
    nth_rw 1 [← hμ]
    exact inv_mul_cancel₀ hμ0
  have h := pow_gcd_eq_one.mpr ⟨h2, hμN⟩
  rwa [Nat.coprime_two_left.mpr hN, pow_one] at h

theorem exists_three_eigenvalues [IsAlgClosed k] [FiniteDimensional k V] (hV : finrank k V = 3)
    {f g T : End k V} {N : ℕ} (hN : (N : k) ≠ 0) (hNodd : Odd N) (hf : f ^ N = 1)
    (hfg : f * g = 1) (hf1 : f ≠ 1) (hT : Function.Injective T) (hTf : T * f = g * T) :
    ∃ μ : k, μ ≠ 1 ∧ μ⁻¹ ≠ μ ∧ ∃ v₁ v₂ v₃ : V, f.HasEigenvector 1 v₁ ∧
      f.HasEigenvector μ v₂ ∧ f.HasEigenvector μ⁻¹ v₃ := by
  have hspan := iSup_eigenspace_eq_top_of_pow_eq_one hN hf
  have hroot : ∀ {μ v}, f.HasEigenvector μ v → μ ^ N = 1 := fun hv =>
    pow_eq_one_of_hasEigenvector hf hv
  have hne0 : ∀ {μ v}, f.HasEigenvector μ v → μ ≠ 0 := by
    intro μ v hv h0
    have := hroot hv
    rw [h0, zero_pow (by obtain ⟨r, hr⟩ := hNodd; omega)] at this
    exact zero_ne_one this
  have hinv : ∀ {μ v}, f.HasEigenvector μ v → f.HasEigenvector μ⁻¹ (T v) := fun hv =>
    ⟨apply_mem_eigenspace_inv hfg hTf (hne0 hv) hv.1,
      fun h => hv.2 (hT (h.trans (map_zero T).symm))⟩
  have hself : ∀ {μ v}, f.HasEigenvector μ v → μ⁻¹ = μ → μ = 1 := fun hv h =>
    eq_one_of_inv_eq_self hNodd (hroot hv) h
  obtain ⟨μ, hμ1, v₂, hv₂⟩ : ∃ μ : k, μ ≠ 1 ∧ ∃ v, f.HasEigenvector μ v := by
    by_contra! h
    apply hf1
    have hE : f.eigenspace 1 = ⊤ := by
      rw [eq_top_iff, ← hspan]
      refine iSup_le fun ν => ?_
      by_cases hν : ν = 1
      · rw [hν]
      · have hbot : f.eigenspace ν = ⊥ := by
          by_contra hne
          obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
          exact h ν hν v ⟨hv, hv0⟩
        rw [hbot]
        exact bot_le
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ f.eigenspace 1 := hE ▸ Submodule.mem_top
    rw [mem_eigenspace_iff, one_smul] at hv
    rw [hv, one_apply]
  have hv₃ := hinv hv₂
  have hμinv : μ⁻¹ ≠ μ := fun h => hμ1 (hself hv₂ h)
  refine ⟨μ, hμ1, hμinv, ?_⟩
  by_contra! hno
  have h1 : ∀ v, ¬f.HasEigenvector 1 v := fun v hv => hno v v₂ (T v₂) hv hv₂ hv₃
  have hall : ∀ ν w, f.HasEigenvector ν w → ν = μ ∨ ν = μ⁻¹ := by
    intro ν w hw
    by_contra! hν
    have hν1 : ν ≠ 1 := fun h => h1 w (h ▸ hw)
    have hνinv : ν⁻¹ ≠ ν := fun h => hν1 (hself hw h)
    have h02 : μ ≠ ν := fun h => hν.1 h.symm
    have h03 : μ ≠ ν⁻¹ := fun h => hν.2 (by rw [h, inv_inv])
    have h12 : μ⁻¹ ≠ ν := fun h => hν.2 h.symm
    have h13 : μ⁻¹ ≠ ν⁻¹ := fun h => hν.1 (inv_injective h).symm
    have hinj : Function.Injective ![μ, μ⁻¹, ν, ν⁻¹] := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp at hij <;>
        first
        | rfl
        | exact absurd hij ‹_›
        | exact absurd hij.symm ‹_›
    have hle := card_le_finrank_of_hasEigenvector f hinj (v := ![v₂, T v₂, w, T w]) (by
      intro i
      fin_cases i
      · exact hv₂
      · exact hv₃
      · exact hw
      · exact hinv hw)
    rw [Fintype.card_fin, hV] at hle
    omega
  set E := f.eigenspace μ with hEdef
  set E' := f.eigenspace μ⁻¹ with hE'def
  have hsup : E ⊔ E' = ⊤ := by
    rw [eq_top_iff, ← hspan]
    refine iSup_le fun ν => ?_
    by_cases hν : f.eigenspace ν = ⊥
    · rw [hν]
      exact bot_le
    · obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hν
      rcases hall ν w ⟨hw, hw0⟩ with rfl | rfl
      · exact le_sup_left
      · exact le_sup_right
  have hdisj : Disjoint E E' := f.eigenspaces_iSupIndep.pairwiseDisjoint hμinv.symm
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq E E'
  rw [hsup, hdisj.eq_bot, finrank_bot, finrank_top, hV, add_zero] at hdim
  have hmaps₁ : ∀ v ∈ E, T v ∈ E' := fun v hv =>
    apply_mem_eigenspace_inv hfg hTf (hne0 hv₂) hv
  have hmaps₂ : ∀ v ∈ E', T v ∈ E := fun v hv => by
    have := apply_mem_eigenspace_inv hfg hTf (inv_ne_zero (hne0 hv₂)) hv
    rwa [inv_inv] at this
  have hle1 : finrank k E ≤ finrank k E' :=
    LinearMap.finrank_le_finrank_of_injective (f := T.restrict hmaps₁)
      fun a b hab => Subtype.ext (hT (congrArg Subtype.val hab))
  have hle2 : finrank k E' ≤ finrank k E :=
    LinearMap.finrank_le_finrank_of_injective (f := T.restrict hmaps₂)
      fun a b hab => Subtype.ext (hT (congrArg Subtype.val hab))
  omega

variable [IsAlgClosed k] [FiniteDimensional k V] {B : Type*} [Group B] [Finite B] {p : ℕ}
  [Fact p.Prime]

theorem isCyclic_and_card_le_of_inverted (hpk : (p : k) ≠ 0) (hp2 : p ≠ 2) (hB : IsPGroup p B)
    (hBc : ∀ a b : B, a * b = b * a) (ρ : B →* End k V) (hρ : Function.Injective ρ)
    (hV : finrank k V = 3) (T : End k V) (hT : Function.Injective T)
    (hTρ : ∀ b, T * ρ b = ρ b⁻¹ * T) {q : ℕ} {φ : k →+* k} (hφ : ∀ c, φ c = c ^ q)
    (β : V →ₛₗ[φ] V →ₗ[k] k) (hβ : β.SeparatingLeft)
    (hβρ : ∀ b v w, β (ρ b v) (ρ b w) = β v w) (hq : ¬p ∣ q) (hq1 : ¬p ∣ q - 1) :
    IsCyclic B ∧ Nat.card B ≤ p ^ (q + 1).factorization p := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hB
  have hNk : ((Nat.card B : ℕ) : k) ≠ 0 := natCast_card_ne_zero hpk hB
  have hNodd : Odd (Nat.card B) := hm ▸ (hp.odd_of_ne_two hp2).pow
  have hq0 : q ≠ 0 := by
    rintro rfl
    have h := hφ 0
    rw [map_zero, pow_zero] at h
    exact zero_ne_one h
  have hcop : ∀ n : ℕ, ¬p ∣ n → Nat.Coprime (Nat.card B) n := fun n hn =>
    hm ▸ Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd hp).mpr hn)
  have hpos : 0 < p ^ (q + 1).factorization p := pow_pos hp.pos _
  by_cases hB1 : ∀ b : B, b = 1
  · have : Subsingleton B := ⟨fun a b => (hB1 a).trans (hB1 b).symm⟩
    exact ⟨isCyclic_of_subsingleton, by rw [Nat.card_unique]; exact hpos⟩
  push Not at hB1
  obtain ⟨b₀, hb₀⟩ := hB1
  have hf1 : ρ b₀ ≠ 1 := fun h => hb₀ (hρ (h.trans (map_one ρ).symm))
  have hfg : ρ b₀ * ρ b₀⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  obtain ⟨μ, hμ1, hμinv, v₁, v₂, v₃, hv₁, hv₂, hv₃⟩ :=
    exists_three_eigenvalues hV hNk hNodd (rep_pow_card_eq_one ρ b₀) hfg hf1 hT (hTρ b₀)
  have hμN : μ ^ Nat.card B = 1 := pow_eq_one_of_hasEigenvector (rep_pow_card_eq_one ρ b₀) hv₂
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by obtain ⟨r, hr⟩ := hNodd; omega)] at hμN
    exact zero_ne_one hμN
  set ev : Fin 3 → k := ![1, μ, μ⁻¹] with hevdef
  set vs : Fin 3 → V := ![v₁, v₂, v₃] with hvsdef
  have h01 : (1 : k) ≠ μ := fun h => hμ1 h.symm
  have h02 : (1 : k) ≠ μ⁻¹ := fun h => hμ1 (by rw [← inv_inv μ, ← h, inv_one])
  have hev : Function.Injective ev := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [ev] at hij <;>
      first
      | rfl
      | exact absurd hij ‹_›
      | exact absurd hij.symm ‹_›
  have hvs : ∀ i, (ρ b₀).HasEigenvector (ev i) (vs i) := by
    intro i
    fin_cases i
    · exact hv₁
    · exact hv₂
    · exact hv₃
  have hcard3 : Fintype.card (Fin 3) = finrank k V := by rw [Fintype.card_fin, hV]
  have hcomm : ∀ b, Commute (ρ b) (ρ b₀) := fun b => by
    show ρ b * ρ b₀ = ρ b₀ * ρ b
    rw [← map_mul, ← map_mul, hBc]
  have hline : ∀ (b : B) (i : Fin 3), ∃ a : k, ρ b (vs i) = a • vs i := fun b i =>
    exists_apply_eq_smul_of_commute hev hvs hcard3 (hcomm b) i
  choose a ha using hline
  have hvs0 : ∀ i, vs i ≠ 0 := fun i => (hvs i).2
  have hamul : ∀ b b' i, a (b * b') i = a b i * a b' i := by
    intro b b' i
    apply smul_left_injective k (hvs0 i)
    change a (b * b') i • vs i = (a b i * a b' i) • vs i
    rw [← ha, map_mul, mul_apply, ha, map_smul, ha, smul_smul, mul_comm]
  have haone : ∀ i, a 1 i = 1 := by
    intro i
    apply smul_left_injective k (hvs0 i)
    change a 1 i • vs i = (1 : k) • vs i
    rw [← ha, map_one, one_apply, one_smul]
  have hapow : ∀ b i, a b i ^ Nat.card B = 1 := by
    intro b i
    have h : ∀ n : ℕ, a (b ^ n) i = a b i ^ n := by
      intro n
      induction n with
      | zero => rw [pow_zero, pow_zero, haone]
      | succ n ih => rw [pow_succ, hamul, ih, pow_succ]
    rw [← h, pow_card_eq_one', haone]
  have hainv : ∀ b i, a b⁻¹ i = (a b i)⁻¹ := by
    intro b i
    have h := hamul b⁻¹ b i
    rw [inv_mul_cancel, haone] at h
    exact eq_inv_of_mul_eq_one_left h.symm
  have hTapp : ∀ b v, T (ρ b v) = ρ b⁻¹ (T v) := fun b v => by
    rw [← mul_apply, hTρ b, mul_apply]
  obtain ⟨c₁, hc₁⟩ : ∃ c, T v₁ = c • v₁ := by
    refine exists_eq_smul_of_apply_eq_smul hev hvs hcard3 0 ?_
    have := apply_mem_eigenspace_inv hfg (hTρ b₀) one_ne_zero hv₁.1
    rwa [inv_one, mem_eigenspace_iff] at this
  obtain ⟨c₂, hc₂⟩ : ∃ c, T v₂ = c • v₃ := by
    refine exists_eq_smul_of_apply_eq_smul hev hvs hcard3 2 ?_
    have := apply_mem_eigenspace_inv hfg (hTρ b₀) hμ0 hv₂.1
    rwa [mem_eigenspace_iff] at this
  have hTv₁ : T v₁ ≠ 0 := fun h => hv₁.2 (hT (h.trans (map_zero T).symm))
  have hTv₂ : T v₂ ≠ 0 := fun h => hv₂.2 (hT (h.trans (map_zero T).symm))
  have ha0 : ∀ b, a b 0 = 1 := by
    intro b
    have h := hTapp b v₁
    have e1 : ρ b v₁ = a b 0 • v₁ := ha b 0
    have e2 : ρ b⁻¹ v₁ = a b⁻¹ 0 • v₁ := ha b⁻¹ 0
    rw [e1, map_smul, hc₁, map_smul, e2, smul_smul, smul_smul, mul_comm] at h
    have h' : a b 0 = a b⁻¹ 0 := by
      have hc0 : c₁ ≠ 0 := by
        rintro rfl
        rw [zero_smul] at hc₁
        exact hTv₁ hc₁
      exact mul_left_cancel₀ hc0 (smul_left_injective k hv₁.2 h)
    rw [hainv] at h'
    exact eq_one_of_inv_eq_self hNodd (hapow b 0) h'.symm
  have ha2 : ∀ b, a b 2 = (a b 1)⁻¹ := by
    intro b
    have h := hTapp b v₂
    have e1 : ρ b v₂ = a b 1 • v₂ := ha b 1
    have e2 : ρ b⁻¹ v₃ = a b⁻¹ 2 • v₃ := ha b⁻¹ 2
    rw [e1, map_smul, hc₂, map_smul, e2, smul_smul, smul_smul] at h
    have hc0 : c₂ ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc₂
      exact hTv₂ hc₂
    have h3 := smul_left_injective k hv₃.2 h
    have h' : a b 1 = a b⁻¹ 2 := mul_right_cancel₀ hc0 (h3.trans (mul_comm _ _))
    rw [h', hainv, inv_inv]
  let χ : B →* k :=
    { toFun := fun b => a b 1
      map_one' := haone 1
      map_mul' := fun b b' => hamul b b' 1 }
  have hχ : ∀ b, χ b = a b 1 := fun _ => rfl
  let bas := basisOfLinearIndependentOfCardEqFinrank' vs
    ((ρ b₀).eigenvectors_linearIndependent' ev hev vs hvs) hcard3
  have hbas : ∀ i, bas i = vs i := fun i => by
    simp [bas, coe_basisOfLinearIndependentOfCardEqFinrank']
  have hχinj : Function.Injective χ := by
    rw [injective_iff_map_eq_one]
    intro b hb
    rw [hχ] at hb
    apply hρ
    rw [map_one]
    refine bas.ext fun i => ?_
    rw [hbas, ha, one_apply]
    fin_cases i
    · change a b 0 • vs 0 = vs 0
      rw [ha0, one_smul]
    · change a b 1 • vs 1 = vs 1
      rw [hb, one_smul]
    · change a b 2 • vs 2 = vs 2
      rw [ha2, hb, inv_one, one_smul]
  have hβsmul : ∀ (c d : k) (v w : V), β (c • v) (d • w) = c ^ q * d * β v w := by
    intro c d v w
    rw [LinearMap.map_smulₛₗ₂, map_smul, hφ, smul_eq_mul, smul_eq_mul, mul_assoc]
  have hβ22 : β v₂ v₂ ≠ 0 := by
    intro h22
    have hzero : ∀ j : Fin 3, β v₂ (vs j) = 0 := by
      intro j
      by_contra hj
      have h := hβρ b₀ v₂ (vs j)
      rw [hv₂.apply_eq_smul, (hvs j).apply_eq_smul, hβsmul] at h
      have h' : μ ^ q * ev j = 1 := by
        have := mul_right_cancel₀ hj (h.trans (one_mul _).symm)
        exact this
      fin_cases j
      · change μ ^ q * 1 = 1 at h'
        rw [mul_one] at h'
        have := pow_gcd_eq_one.mpr ⟨hμN, h'⟩
        rw [hcop q hq, pow_one] at this
        exact hμ1 this
      · exact hj h22
      · change μ ^ q * μ⁻¹ = 1 at h'
        have h'' : μ ^ (q - 1) = 1 := by
          have e : μ ^ q = μ ^ (q - 1) * μ := by
            rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hq0)]
          rw [e, mul_assoc, mul_inv_cancel₀ hμ0, mul_one] at h'
          exact h'
        have := pow_gcd_eq_one.mpr ⟨hμN, h''⟩
        rw [hcop (q - 1) hq1, pow_one] at this
        exact hμ1 this
    have hβ0 : β v₂ = 0 := bas.ext fun j => by rw [hbas, hzero j, LinearMap.zero_apply]
    exact hv₂.2 (hβ v₂ fun w => by rw [hβ0, LinearMap.zero_apply])
  have hχq : ∀ b, χ b ^ (q + 1) = 1 := by
    intro b
    have h := hβρ b v₂ v₂
    have e : ρ b v₂ = a b 1 • v₂ := ha b 1
    rw [e, hβsmul] at h
    have := mul_right_cancel₀ hβ22 (h.trans (one_mul _).symm)
    rw [hχ, pow_succ]
    exact this
  have hχN : ∀ b, χ b ^ Nat.card B = 1 := fun b => hapow b 1
  have hχa : ∀ b, χ b ^ p ^ (q + 1).factorization p = 1 := by
    intro b
    have hg := pow_gcd_eq_one.mpr ⟨hχN b, hχq b⟩
    have hdvd : (Nat.card B).gcd (q + 1) ∣ p ^ (q + 1).factorization p := by
      have hgdvd : (Nat.card B).gcd (q + 1) ∣ p ^ m := by
        rw [← hm]
        exact Nat.gcd_dvd_left _ _
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp hgdvd
      rw [hj]
      apply pow_dvd_pow
      rw [← hp.pow_dvd_iff_le_factorization (Nat.succ_ne_zero q), ← hj]
      exact Nat.gcd_dvd_right _ _
    obtain ⟨r, hr⟩ := hdvd
    rw [hr, pow_mul, hg, one_pow]
  have hχne : ∀ b, χ b ≠ 0 := fun b h => by
    have := hχN b
    rw [h, zero_pow (by obtain ⟨r, hr⟩ := hNodd; omega)] at this
    exact zero_ne_one this
  refine ⟨isCyclic_of_injective_ringHom χ hχinj, ?_⟩
  have : NeZero (p ^ (q + 1).factorization p) := ⟨hpos.ne'⟩
  let ψ : B → rootsOfUnity (p ^ (q + 1).factorization p) k := fun b =>
    ⟨Units.mk0 (χ b) (hχne b), by
      rw [mem_rootsOfUnity]
      ext
      simp [hχa b]⟩
  have hψ : Function.Injective ψ := by
    intro b b' h
    apply hχinj
    have := congrArg (fun u : rootsOfUnity (p ^ (q + 1).factorization p) k => ((u : kˣ) : k)) h
    simpa [ψ] using this
  exact (Nat.card_le_card_of_injective ψ hψ).trans (card_rootsOfUnity k _)

end CFSG.UnitaryInvolutionIndex
