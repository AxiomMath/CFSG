module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsL35EField
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsUnitaryLiftBase
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.L35

open CFSG Subgroup GrSLit.L34Facts CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34

theorem field_kernel_fact : ∀ d₁ d₂ : Fin 4, ¬(d₁.val = 0 ∧ d₂.val = 0) → ∃ m n : Fin 4,
    (d₁.val * m.val + (d₁.val + 3 * d₂.val) * n.val) % 4 = 2 ∧
      (d₂.val * m.val + 3 * d₂.val * n.val) % 4 = 0 := by
  decide

theorem sq_eq_one_of_field_kernel {Y : Type*} [Group Y] {A B : Y} (hc : Commute A B)
    (hA4 : A ^ 4 = 1) (hB4 : B ^ 4 = 1) (τ : MulAut Y) (hτA : τ A = A)
    (hτB : τ B = A ^ 3 * B ^ 3) {d₁ d₂ : ℕ} (hd₁ : d₁ < 4) (hd₂ : d₂ < 4)
    (hne : ¬(d₁ = 0 ∧ d₂ = 0)) (h1 : A ^ d₁ * B ^ d₂ = 1) : A ^ 2 = 1 := by
  have hpow : ∀ a b m : ℕ, (A ^ a * B ^ b) ^ m = A ^ (a * m) * B ^ (b * m) := fun a b m => by
    rw [(hc.pow_pow a b).mul_pow, ← pow_mul, ← pow_mul]
  have hmul : ∀ a b c d : ℕ, A ^ a * B ^ b * (A ^ c * B ^ d) = A ^ (a + c) * B ^ (b + d) :=
    fun a b c d => by
      rw [pow_add, pow_add]
      calc A ^ a * B ^ b * (A ^ c * B ^ d) = A ^ a * (B ^ b * A ^ c) * B ^ d := by group
        _ = A ^ a * (A ^ c * B ^ b) * B ^ d := by rw [(hc.pow_pow c b).eq]
        _ = A ^ a * A ^ c * (B ^ b * B ^ d) := by group
  have h2 : A ^ (d₁ + 3 * d₂) * B ^ (3 * d₂) = 1 := by
    have h := congrArg τ h1
    rw [map_mul, map_pow, map_pow, hτA, hτB, map_one, hpow 3 3 d₂] at h
    rw [pow_add, mul_assoc]
    exact h
  obtain ⟨m, n, hm, hn⟩ := field_kernel_fact ⟨d₁, hd₁⟩ ⟨d₂, hd₂⟩ hne
  simp only at hm hn
  have hA : A ^ 2 = A ^ (d₁ * m.val + (d₁ + 3 * d₂) * n.val) *
      B ^ (d₂ * m.val + 3 * d₂ * n.val) := by
    rw [pow_eq_pow_mod (d₁ * m.val + (d₁ + 3 * d₂) * n.val) hA4, hm,
      pow_eq_pow_mod (d₂ * m.val + 3 * d₂ * n.val) hB4, hn, pow_zero, mul_one]
  rw [hA, ← hmul (d₁ * m.val) (d₂ * m.val) ((d₁ + 3 * d₂) * n.val) (3 * d₂ * n.val),
    ← hpow d₁ d₂ m.val, ← hpow (d₁ + 3 * d₂) (3 * d₂) n.val, h1, h2, one_pow, one_pow,
    one_mul]

theorem card_center_eq_sixteen
    {Y : Type} [Group Y] [Finite Y] {q : Y →* Equiv.Perm (Fin 42)} (hqker : q.ker = center Y)
    (h3 : ∀ e ∈ q.ker, e ^ 3 = 1 → e = 1) {l : Cover →* Y} (hl : q.comp l = sigma)
    (hls : Function.Surjective l) {τ : MulAut Y} (hτ : ∀ e, q (τ e) = r₂ * q e * r₂⁻¹)
    (hz : l z₁ ^ 2 ≠ 1) : Nat.card (center Y) = 16 := by
  have hlq : ∀ c, q (l c) = sigma c := fun c => by rw [← MonoidHom.comp_apply, hl]
  obtain ⟨α, hα, hσα⟩ := exists_fieldLift
  have hext : τ.toMonoidHom.comp l = l.comp α := by
    apply hom_ext_of_central commutator_cover q hqker.le
    refine MonoidHom.ext fun c => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [hτ, hlq, hlq, hσα]
  have hτl : ∀ c, τ (l c) = l (α c) := fun c => congrArg (fun φ : Cover →* Y => φ c) hext
  set A := l z₁ with hAdef
  set B := l z₂ with hBdef
  have hAZ : A ∈ center Y := by
    rw [← hqker, MonoidHom.mem_ker, hlq, sigma_z₁]
  have hBZ : B ∈ center Y := by
    rw [← hqker, MonoidHom.mem_ker, hlq, sigma_z₂]
  have hc : Commute A B := mem_center_iff.mp hBZ A
  have hA4 : A ^ 4 = 1 := lz₁_pow l
  have hB4 : B ^ 4 = 1 := lz₂_pow l
  have hτA : τ A = A := by rw [hAdef, hτl, hα zOne, alphaF_z₁]
  have hτB : τ B = A ^ 3 * B ^ 3 := by
    rw [hBdef, hτl, hα zTwo, alphaF_z₂, map_mul, map_pow, map_pow]
  have hmem : ∀ x : Fin 4 × Fin 4, A ^ x.1.val * B ^ x.2.val ∈ center Y := fun x =>
    mul_mem (pow_mem hAZ _) (pow_mem hBZ _)
  let f : Fin 4 × Fin 4 → center Y := fun x => ⟨A ^ x.1.val * B ^ x.2.val, hmem x⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨z, hzZ⟩
    rw [← hqker] at hzZ
    obtain ⟨i, j, rfl⟩ := (mem_ker_iff hl hls h3).mp hzZ
    refine ⟨(⟨i % 4, Nat.mod_lt _ (by norm_num)⟩, ⟨j % 4, Nat.mod_lt _ (by norm_num)⟩), ?_⟩
    apply Subtype.ext
    change A ^ (i % 4) * B ^ (j % 4) = A ^ i * B ^ j
    rw [← pow_eq_pow_mod i hA4, ← pow_eq_pow_mod j hB4]
  have hinj : Function.Injective f := by
    rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ ⟨⟨i', hi'⟩, ⟨j', hj'⟩⟩ he
    have he' : A ^ i * B ^ j = A ^ i' * B ^ j' := congrArg Subtype.val he
    by_contra hne
    have hne' : ¬((i + 4 - i') % 4 = 0 ∧ (j + 4 - j') % 4 = 0) := by
      rintro ⟨h1, h2⟩
      apply hne
      have : i = i' := by omega
      have : j = j' := by omega
      subst_vars
      rfl
    have hrel : A ^ ((i + 4 - i') % 4) * B ^ ((j + 4 - j') % 4) = 1 := by
      rw [← pow_eq_pow_mod _ hA4, ← pow_eq_pow_mod _ hB4]
      have hA' : A ^ (i + 4 - i') * A ^ i' = A ^ i := by
        rw [← pow_add, show i + 4 - i' + i' = i + 4 by omega, pow_add, hA4, mul_one]
      have hB' : B ^ (j + 4 - j') * B ^ j' = B ^ j := by
        rw [← pow_add, show j + 4 - j' + j' = j + 4 by omega, pow_add, hB4, mul_one]
      have hc' : Commute (A ^ i') (B ^ (j + 4 - j')) := hc.pow_pow _ _
      have key : A ^ (i + 4 - i') * B ^ (j + 4 - j') * (A ^ i' * B ^ j') = A ^ i' * B ^ j' := by
        calc A ^ (i + 4 - i') * B ^ (j + 4 - j') * (A ^ i' * B ^ j')
            = A ^ (i + 4 - i') * (B ^ (j + 4 - j') * A ^ i') * B ^ j' := by group
          _ = A ^ (i + 4 - i') * (A ^ i' * B ^ (j + 4 - j')) * B ^ j' := by rw [hc'.eq]
          _ = (A ^ (i + 4 - i') * A ^ i') * (B ^ (j + 4 - j') * B ^ j') := by group
          _ = A ^ i * B ^ j := by rw [hA', hB']
          _ = A ^ i' * B ^ j' := he'
      exact mul_right_cancel (key.trans (one_mul _).symm)
    exact hz (sq_eq_one_of_field_kernel hc hA4 hB4 τ hτA hτB (Nat.mod_lt _ (by norm_num))
      (Nat.mod_lt _ (by norm_num)) hne' hrel)
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩), Nat.card_prod, Nat.card_eq_fintype_card,
    Fintype.card_fin]

end CFSG.ComponentClassification.HarrisLit.L35
