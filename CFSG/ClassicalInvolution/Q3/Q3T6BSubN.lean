module

public import CFSG.ClassicalInvolution.Asc77.Lemma310
public import CFSG.ClassicalInvolution.Uniform.U4Basic

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6B

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Hat2A7
  CFSG.ClassicalInvolution.Uniform.U4

variable {F : Type} [Group F] [Finite F]

theorem exists_pow_mul_eq {K : Subgroup F} {a k : F} (ha : a ∈ Subgroup.normalizer (K : Set F))
    (hk : k ∈ K) (j : ℕ) : ∃ k' ∈ K, (k * a) ^ j = k' * a ^ j := by
  induction j with
  | zero => exact ⟨1, K.one_mem, by simp⟩
  | succ j ih =>
    obtain ⟨k₀, hk₀, h⟩ := ih
    have hc : a ^ j * k * (a ^ j)⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ ha j) k).mp hk
    refine ⟨k₀ * (a ^ j * k * (a ^ j)⁻¹), K.mul_mem hk₀ hc, ?_⟩
    rw [pow_succ, h]
    group

theorem mem_of_odd_orderOf_mul {K : Subgroup F} {a k : F}
    (ha : a ∈ Subgroup.normalizer (K : Set F)) (hk : k ∈ K)
    (ha2 : IsPGroup 2 (Subgroup.zpowers a)) (hodd : Odd (orderOf (k * a))) : a ∈ K := by
  obtain ⟨k', hk', h⟩ := exists_pow_mul_eq ha hk (orderOf (k * a))
  rw [pow_orderOf_eq_one] at h
  have hm : a ^ orderOf (k * a) ∈ K := by
    have : a ^ orderOf (k * a) = k'⁻¹ := by
      have := congrArg (fun x => k'⁻¹ * x) h
      simpa using this.symm
    rw [this]
    exact K.inv_mem hk'
  obtain ⟨e, he⟩ := ha2.exists_card_eq
  rw [Nat.card_zpowers] at he
  have hcop : Nat.Coprime (orderOf (k * a)) (orderOf a) := by
    rw [he]
    exact (Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr hodd)).symm
  obtain ⟨n, hn⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hn]
  exact Subgroup.pow_mem _ hm n

theorem subnormal_odd_normalizer_aux {K A : Subgroup F}
    (hKgen : K ≤ Subgroup.closure {g : F | g ∈ K ∧ Odd (orderOf g)}) (hA2 : IsPGroup 2 A) :
    ∀ {L M : Subgroup F}, IsSubnormal L M → A ≤ M → (∀ m ∈ M, ∃ k ∈ K, ∃ a ∈ A, m = k * a) →
      K ≤ L → L ≤ Subgroup.normalizer (K : Set F) → (∀ g ∈ L, Odd (orderOf g) → g ∈ K) →
        A ≤ Subgroup.normalizer (K : Set F) := by
  intro L M hL
  induction hL with
  | refl H =>
    intro hAM _ _ hHN _
    exact fun a ha => hHN (hAM ha)
  | @step L L₂ M hle hnormal hsub ih =>
    intro hAM hM hKL hLN hodd
    have hKL₂ : K ≤ L₂ := hKL.trans hle
    have hLconj : ∀ l₂ ∈ L₂, ∀ l ∈ L, l₂ * l * l₂⁻¹ ∈ L := by
      intro l₂ hl₂ l hl
      have h1 : (⟨l, hle hl⟩ : L₂) ∈ L.subgroupOf L₂ := Subgroup.mem_subgroupOf.mpr hl
      have h2 := hnormal.conj_mem _ h1 ⟨l₂, hl₂⟩
      exact Subgroup.mem_subgroupOf.mp h2
    have hKconj : ∀ l₂ ∈ L₂, ∀ k ∈ K, l₂ * k * l₂⁻¹ ∈ K := by
      intro l₂ hl₂ k hk
      have hcl : Subgroup.closure {g : F | g ∈ K ∧ Odd (orderOf g)} ≤
          K.comap (MulAut.conj l₂).toMonoidHom := by
        refine (Subgroup.closure_le _).mpr fun g hg => ?_
        show l₂ * g * l₂⁻¹ ∈ K
        refine hodd _ (hLconj l₂ hl₂ g (hKL hg.1)) ?_
        rw [orderOf_conj_eq]
        exact hg.2
      exact hcl (hKgen hk)
    have hL₂N : L₂ ≤ Subgroup.normalizer (K : Set F) := by
      intro l₂ hl₂
      rw [Subgroup.mem_normalizer_iff]
      intro h
      refine ⟨fun hh => hKconj l₂ hl₂ h hh, fun hh => ?_⟩
      have := hKconj l₂⁻¹ (L₂.inv_mem hl₂) _ hh
      simpa [mul_assoc] using this
    have hL₂M : L₂ ≤ M := isSubnormal_le hsub
    have hodd₂ : ∀ g ∈ L₂, Odd (orderOf g) → g ∈ K := by
      intro g hg hgodd
      obtain ⟨k, hk, a, haA, hga⟩ := hM g (hL₂M hg)
      have haL₂ : a ∈ L₂ := by
        have : a = k⁻¹ * g := by rw [hga]; group
        rw [this]
        exact L₂.mul_mem (L₂.inv_mem (hKL₂ hk)) hg
      have haK : a ∈ K :=
        mem_of_odd_orderOf_mul (hL₂N haL₂) hk (hA2.to_le (Subgroup.zpowers_le.mpr haA))
          (by rw [← hga]; exact hgodd)
      rw [hga]
      exact K.mul_mem hk haK
    exact ih hAM hM hKL₂ hL₂N hodd₂

theorem subnormal_odd_normalizer {K M A : Subgroup F}
    (hKgen : K ≤ Subgroup.closure {g : F | g ∈ K ∧ Odd (orderOf g)}) (hA2 : IsPGroup 2 A)
    (hsub : IsSubnormal K M) (hAM : A ≤ M)
    (hM : ∀ m ∈ M, ∃ k ∈ K, ∃ a ∈ A, m = k * a) : A ≤ Subgroup.normalizer (K : Set F) :=
  subnormal_odd_normalizer_aux hKgen hA2 hsub hAM hM le_rfl Subgroup.le_normalizer
    (fun _ hg _ => hg)

theorem comm_of_conj_eq_one_or_mul {g z a : F} (hgz : g * z = z * g) (hz2 : z * z = 1)
    (hz1 : z ≠ 1) (hodd : Odd (orderOf g))
    (h : g * a * g⁻¹ = a ∨ g * a * g⁻¹ = z * a) : g * a = a * g := by
  have key : g * a * g⁻¹ = a := by
    rcases h with h | h
    · exact h
    · exfalso
      have hpow : ∀ i : ℕ, g ^ i * a * (g ^ i)⁻¹ = z ^ i * a := by
        intro i
        induction i with
        | zero => simp
        | succ i ih =>
          have hgz' : g * z ^ i = z ^ i * g := (Commute.pow_right (hgz : Commute g z) i)
          calc g ^ (i + 1) * a * (g ^ (i + 1))⁻¹
              = g * (g ^ i * a * (g ^ i)⁻¹) * g⁻¹ := by group
            _ = g * (z ^ i * a) * g⁻¹ := by rw [ih]
            _ = (g * z ^ i) * a * g⁻¹ := by group
            _ = (z ^ i * g) * a * g⁻¹ := by rw [hgz']
            _ = z ^ i * (g * a * g⁻¹) := by group
            _ = z ^ i * (z * a) := by rw [h]
            _ = z ^ (i + 1) * a := by group
      have h1 := hpow (orderOf g)
      rw [pow_orderOf_eq_one] at h1
      have hzo : z ^ orderOf g = z := by
        obtain ⟨j, hj⟩ := hodd
        rw [hj, pow_succ, pow_mul, pow_two, hz2, one_pow, one_mul]
      rw [hzo] at h1
      have : z = 1 := by
        have h2 : a = z * a := by simpa using h1
        have := congrArg (fun x => x * a⁻¹) h2
        simpa using this.symm
      exact hz1 this
  calc g * a = (g * a * g⁻¹) * g := by group
    _ = a * g := by rw [key]

end CFSG.ClassicalInvolution.Q3.Q3T6B
