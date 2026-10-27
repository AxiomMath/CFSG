module

public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.S56

open Subgroup
open scoped commutatorElement

variable {Γ : Type*} [Group Γ]

private theorem card_modEq_ncard_fixedPoints {α : Type*} [Finite α] {f : α → α}
    (hf : ∀ a, f^[5] a = a) : Nat.card α ≡ (Function.fixedPoints f).ncard [MOD 5] := by
  classical
  haveI := Fintype.ofFinite α
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let F : Function.End α := f
  have hF : F ^ 5 ^ 1 = 1 := by
    funext a
    exact hf a
  have h := Equiv.Perm.card_fixedPoints_modEq (f := F) (p := 5) (n := 1) hF
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at h
  exact h

private theorem apply_eq_of_card_le_four {α : Type*} [Finite α] (hα : Nat.card α ≤ 4) {f : α → α}
    (hf : ∀ a, f^[5] a = a) (a : α) : f a = a := by
  have h1 := card_modEq_ncard_fixedPoints hf
  have h2 : (Function.fixedPoints f).ncard ≤ Nat.card α := Set.ncard_le_card _
  have h3 : (Function.fixedPoints f).ncard = Nat.card α := by
    unfold Nat.ModEq at h1
    omega
  have h4 : Function.fixedPoints f = Set.univ :=
    Set.eq_of_subset_of_ncard_le (Set.subset_univ _) (by rw [Set.ncard_univ, h3])
  have h5 : a ∈ Function.fixedPoints f := by
    rw [h4]
    trivial
  exact h5

private def conjMap (x : Γ) (K : Subgroup Γ) (hxK : x ∈ normalizer (K : Set Γ)) : K → K :=
  fun k => ⟨x * k * x⁻¹, ((mem_normalizer_iff.1 hxK) k).1 k.2⟩

private theorem coe_iterate_conjMap (x : Γ) (K : Subgroup Γ) (hxK : x ∈ normalizer (K : Set Γ))
    (n : ℕ) (k : K) : (((conjMap x K hxK)^[n] k : K) : Γ) = x ^ n * k * (x ^ n)⁻¹ := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    have h := ih (conjMap x K hxK k)
    rw [h]
    change x ^ n * (x * (k : Γ) * x⁻¹) * (x ^ n)⁻¹ = x ^ (n + 1) * k * (x ^ (n + 1))⁻¹
    group

private theorem card_modEq_ncard_commuting [Finite Γ] {x : Γ} (hx : orderOf x = 5)
    {K : Subgroup Γ} (hxK : x ∈ normalizer (K : Set Γ)) :
    Nat.card K ≡ {c : Γ | c ∈ K ∧ x * c = c * x}.ncard [MOD 5] := by
  have hx5 : x ^ 5 = 1 := by simpa [hx] using pow_orderOf_eq_one x
  have hf : ∀ k, (conjMap x K hxK)^[5] k = k := fun k => by
    apply Subtype.ext
    rw [coe_iterate_conjMap, hx5]
    simp
  have h := card_modEq_ncard_fixedPoints hf
  have himg : Subtype.val '' Function.fixedPoints (conjMap x K hxK) =
      {c : Γ | c ∈ K ∧ x * c = c * x} := by
    ext c
    constructor
    · rintro ⟨k, hk, rfl⟩
      have hk' : x * (k : Γ) * x⁻¹ = k := congrArg Subtype.val hk
      exact ⟨k.2, mul_inv_eq_iff_eq_mul.1 hk'⟩
    · rintro ⟨hcK, hc⟩
      refine ⟨⟨c, hcK⟩, ?_, rfl⟩
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.2 hc
  rw [← himg, Set.ncard_image_of_injective _ Subtype.val_injective]
  exact h

theorem card_modEq_of_centralizer_le [Finite Γ] {x : Γ} (hx : orderOf x = 5)
    {E K P : Subgroup Γ} (hEK : E ≤ K) (hKP : K ≤ P) (hxE : x ∈ normalizer (E : Set Γ))
    (hxK : x ∈ normalizer (K : Set Γ))
    (hfix : ∀ c ∈ P, x * c = c * x → c ∈ E) : Nat.card K ≡ Nat.card E [MOD 5] := by
  have hK := card_modEq_ncard_commuting hx hxK
  have hE := card_modEq_ncard_commuting hx hxE
  have hset : {c : Γ | c ∈ K ∧ x * c = c * x} = {c : Γ | c ∈ E ∧ x * c = c * x} := by
    ext c
    exact ⟨fun ⟨hcK, hc⟩ => ⟨hfix c (hKP hcK) hc, hc⟩, fun ⟨hcE, hc⟩ => ⟨hEK hcE, hc⟩⟩
  rw [hset] at hK
  exact hK.trans hE.symm

private theorem iterate_mul_mul (a b : Γ) (n : ℕ) (c : Γ) :
    (fun c : Γ => a * c * b)^[n] c = a ^ n * c * b ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, pow_succ' a n, pow_succ b n]
    simp only [mul_assoc]

theorem conj_mem_of_index_le_four [Finite Γ] {x : Γ} (hx : orderOf x = 5)
    {E C : Subgroup Γ} (_hEC : E ≤ C) (hxE : x ∈ normalizer (E : Set Γ))
    (hxC : x ∈ normalizer (C : Set Γ)) (hE : E.relIndex C ≤ 4) {g : Γ}
    (hg : g⁻¹ * (x * g * x⁻¹) ∈ C) : g⁻¹ * (x * g * x⁻¹) ∈ E := by
  have hx5 : x ^ 5 = 1 := by simpa [hx] using pow_orderOf_eq_one x
  obtain ⟨a, ha⟩ : ∃ a : Γ, a = g⁻¹ * x * g := ⟨_, rfl⟩
  have ha5 : a ^ 5 = 1 := by
    have h : (g⁻¹ * x * g) ^ 5 = g⁻¹ * x ^ 5 * g := by
      simpa using (conj_pow (a := g⁻¹) (b := x) (i := 5))
    rw [ha, h, hx5]
    group
  have hmem : ∀ c ∈ C, a * c * x⁻¹ ∈ C := by
    intro c hc
    have h1 : x * c * x⁻¹ ∈ C := ((mem_normalizer_iff.1 hxC) c).1 hc
    have e : a * c * x⁻¹ = (g⁻¹ * (x * g * x⁻¹)) * (x * c * x⁻¹) := by
      rw [ha]
      group
    rw [e]
    exact C.mul_mem hg h1
  let φ : C → C := fun c => ⟨a * c * x⁻¹, hmem c c.2⟩
  have hφ5 : ∀ c, φ^[5] c = c := by
    intro c
    apply Subtype.ext
    have hsc : Function.Semiconj (Subtype.val : C → Γ) φ (fun c : Γ => a * c * x⁻¹) :=
      fun c => rfl
    rw [hsc.iterate_right 5 c, iterate_mul_mul, ha5, inv_pow, hx5]
    simp
  let f : C ⧸ E.subgroupOf C → C ⧸ E.subgroupOf C := Quotient.map' φ (fun c₁ c₂ h => by
    have h1 : (c₁⁻¹ * c₂ : C) ∈ E.subgroupOf C := QuotientGroup.leftRel_apply.1 h
    rw [mem_subgroupOf] at h1
    refine QuotientGroup.leftRel_apply.2 ?_
    rw [mem_subgroupOf]
    have e : (((φ c₁)⁻¹ * φ c₂ : C) : Γ) = x * ((c₁ : Γ)⁻¹ * c₂) * x⁻¹ := by
      change (a * c₁ * x⁻¹)⁻¹ * (a * c₂ * x⁻¹) = _
      group
    rw [e]
    exact ((mem_normalizer_iff.1 hxE) _).1 h1)
  have hsc : Function.Semiconj (QuotientGroup.mk : C → C ⧸ E.subgroupOf C) φ f := fun c => rfl
  have hf5 : ∀ z, f^[5] z = z := fun z =>
    QuotientGroup.induction_on z fun c => by
      rw [← hsc.iterate_right 5 c, hφ5]
  have hcard : Nat.card (C ⧸ E.subgroupOf C) ≤ 4 := hE
  have hfix : f (QuotientGroup.mk 1) = QuotientGroup.mk 1 :=
    apply_eq_of_card_le_four hcard hf5 _
  have h2 : (φ 1)⁻¹ * 1 ∈ E.subgroupOf C := QuotientGroup.eq.1 hfix
  rw [mem_subgroupOf] at h2
  have h3 : (a * x⁻¹)⁻¹ ∈ E := by simpa [φ] using h2
  have h4 : a * x⁻¹ ∈ E := E.inv_mem_iff.1 h3
  have e : g⁻¹ * (x * g * x⁻¹) = a * x⁻¹ := by
    rw [ha]
    group
  rwa [e]

theorem centralizer_le_derived_of_commutator_eq [Finite Γ] {p r : ℕ} [Fact p.Prime]
    [Fact r.Prime] (hpr : p ≠ r) {P X : Subgroup Γ} (hP : IsPGroup p P) (hX : IsPGroup r X)
    (hXP : X ≤ normalizer (P : Set Γ)) (hPX : ⁅P, X⁆ = P) :
    P ⊓ centralizer (X : Set Γ) ≤ ⁅P, P⁆ := by
  classical
  haveI : Fintype X := Fintype.ofFinite X
  obtain ⟨ρ, hρ⟩ : ∃ ρ : X →* MulAut P, ∀ (y : X) (q : P),
      ((ρ y q : P) : Γ) = y * q * (y : Γ)⁻¹ :=
    ⟨P.normalizerMonoidHom.comp (Subgroup.inclusion hXP), fun y q => rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : P →* Abelianization P,
      ∀ q, T q = ∏ y : X, (Abelianization.of (ρ y q) : Abelianization P) :=
    ⟨∏ y : X, (Abelianization.of : P →* Abelianization P).comp (ρ y).toMonoidHom,
      fun q => by simp [MonoidHom.finset_prod_apply]⟩
  have hTinv : ∀ (z : X) (q : P), T (ρ z q) = T q := by
    intro z q
    rw [hT, hT]
    refine Fintype.prod_equiv (Equiv.mulRight z) _ _ (fun y => ?_)
    show Abelianization.of (ρ y (ρ z q)) = Abelianization.of (ρ (y * z) q)
    rw [map_mul]
    rfl
  have hcomm : ⁅P, X⁆ ≤ T.ker.map P.subtype := by
    rw [commutator_le]
    intro q hq y hy
    refine ⟨⟨q, hq⟩ * (ρ ⟨y, hy⟩ ⟨q, hq⟩)⁻¹, ?_, ?_⟩
    · rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, hTinv, mul_inv_cancel]
    · have h := hρ ⟨y, hy⟩ ⟨q, hq⟩
      simp only [Subgroup.subtype_apply, Subgroup.coe_mul, Subgroup.coe_inv, h]
      simp only [commutatorElement_def]
      group
  have hT1 : ∀ c : P, T c = 1 := by
    intro c
    have hc : (c : Γ) ∈ ⁅P, X⁆ := by
      rw [hPX]
      exact c.2
    obtain ⟨d, hd, hdc⟩ := hcomm hc
    obtain rfl : d = c := Subtype.ext hdc
    exact hd
  intro c hc
  obtain ⟨hcP, hcX⟩ := mem_inf.1 hc
  have hfix : ∀ y : X, ρ y ⟨c, hcP⟩ = ⟨c, hcP⟩ := by
    intro y
    apply Subtype.ext
    rw [hρ]
    exact mul_inv_eq_iff_eq_mul.2 (mem_centralizer_iff.1 hcX y y.2)
  have hpow : (Abelianization.of ⟨c, hcP⟩ : Abelianization P) ^ Nat.card X = 1 := by
    have h1 := hT1 ⟨c, hcP⟩
    rw [hT] at h1
    simp only [hfix, Finset.prod_const, Finset.card_univ] at h1
    rwa [Nat.card_eq_fintype_card]
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hX
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hP ⟨c, hcP⟩
  have h1 : orderOf (Abelianization.of ⟨c, hcP⟩ : Abelianization P) ∣ p ^ k :=
    hk ▸ orderOf_map_dvd Abelianization.of _
  have h2 : orderOf (Abelianization.of ⟨c, hcP⟩ : Abelianization P) ∣ r ^ m :=
    orderOf_dvd_of_pow_eq_one (hm ▸ hpow)
  have hcop : Nat.Coprime (p ^ k) (r ^ m) :=
    ((Nat.coprime_primes (Fact.out : p.Prime) (Fact.out : r.Prime)).2 hpr).pow k m
  have h3 : orderOf (Abelianization.of ⟨c, hcP⟩ : Abelianization P) = 1 :=
    Nat.dvd_one.1 (hcop.gcd_eq_one ▸ Nat.dvd_gcd h1 h2)
  have h4 : (⟨c, hcP⟩ : P) ∈ commutator P := by
    rw [← Abelianization.ker_of P]
    exact orderOf_eq_one_iff.1 h3
  rw [← Subgroup.map_subtype_commutator P]
  exact ⟨⟨c, hcP⟩, h4, rfl⟩

end CFSG.LocalAnalysis.EvenBN.Tits.S56
