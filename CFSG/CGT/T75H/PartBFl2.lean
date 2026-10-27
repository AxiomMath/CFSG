module

public import CFSG.CGT.T75H.PartBPerm
public import CFSG.CGT.T75I.AltRank

public section

namespace CFSG.CGT.T75H.PermModel

open Equiv Equiv.Perm
open scoped Pointwise

variable {n : ℕ}

@[expose] def encA (g : alternatingGroup (Fin n)) : List ℕ := enc (g : Perm (Fin n))

theorem encA_mul (g h : alternatingGroup (Fin n)) : encA (g * h) = cmp (encA g) (encA h) :=
  enc_mul _ _

theorem encA_one : encA (1 : alternatingGroup (Fin n)) = idl n := enc_one

theorem encA_injective : Function.Injective (encA : alternatingGroup (Fin n) → List ℕ) :=
  fun _ _ e => Subtype.ext (enc_injective e)

theorem cmp_eq_iff (g h g' h' : alternatingGroup (Fin n)) :
    cmp (encA g) (encA h) = cmp (encA g') (encA h') ↔ g * h = g' * h' := by
  rw [← encA_mul, ← encA_mul]
  exact encA_injective.eq_iff

theorem fl2_alt (hn : n ≤ 7) (hF : Fl2List n) (a₁ a₂ : alternatingGroup (Fin n))
    (h1 : encA a₁ = c1 n) (h2 : encA a₂ = c2 n)
    (hcomm : cmp (c1 n) (c2 n) = cmp (c2 n) (c1 n))
    (hc1 : cmp (cmp (c1 n) (c1 n)) (c1 n) = idl n) (hc2 : cmp (cmp (c2 n) (c2 n)) (c2 n) = idl n)
    (hne1 : c1 n ≠ idl n) (hne2 : c2 n ≠ idl n)
    (hq3 : ∀ i ∈ List.range 3, ∀ j ∈ List.range 3,
      cmp (cmp (qlist n i j) (qlist n i j)) (qlist n i j) = idl n)
    (h27 : ¬ 27 ∣ Nat.card (alternatingGroup (Fin n)))
    {P : Subgroup (alternatingGroup (Fin n))} (hP : Nat.card P = 9)
    {ℓ y : alternatingGroup (Fin n)} (hℓℓ : ℓ * ℓ = 1) (hyy : y * y = 1) (hℓy : ℓ * y = y * ℓ)
    (hyℓ : y ≠ ℓ) (hy1 : y ≠ 1) (hℓ1 : ℓ ≠ 1) (hinv : ∀ p ∈ P, ℓ * p * ℓ⁻¹ = p⁻¹) :
    ∃ q ∈ P, ¬ ((y * (q⁻¹ * y * q) = (q⁻¹ * y * q) * y) ↔
      ((y * ℓ) * (q⁻¹ * (y * ℓ) * q) = (q⁻¹ * (y * ℓ) * q) * (y * ℓ))) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ha12 : a₁ * a₂ = a₂ * a₁ := by
    apply encA_injective
    rw [encA_mul, encA_mul, h1, h2, hcomm]
  have ha31 : a₁ * a₁ * a₁ = 1 := by
    apply encA_injective
    rw [encA_mul, encA_mul, encA_one, h1, hc1]
  have ha32 : a₂ * a₂ * a₂ = 1 := by
    apply encA_injective
    rw [encA_mul, encA_mul, encA_one, h2, hc2]
  have ha1 : a₁ ≠ 1 := fun h => hne1 (by rw [← h1, h, encA_one])
  have ha2 : a₂ ≠ 1 := fun h => hne2 (by rw [← h2, h, encA_one])
  have hord : ∀ a : alternatingGroup (Fin n), a * a * a = 1 → a ≠ 1 → orderOf a = 3 :=
    fun a h3 h1' => orderOf_eq_prime (by rw [pow_succ, pow_two]; exact h3) h1'
  have hp1 : IsPGroup 3 (Subgroup.zpowers a₁) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord a₁ ha31 ha1]; norm_num)
  have hp2 : IsPGroup 3 (Subgroup.zpowers a₂) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord a₂ ha32 ha2]; norm_num)
  have hcent : Subgroup.zpowers a₁ ≤ Subgroup.centralizer (Subgroup.zpowers a₂ : Set _) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact (Commute.zpow_left (show Commute a₂ a₁ from ha12.symm) k).eq
  have hnorm : Subgroup.zpowers a₁ ≤ Subgroup.normalizer (Subgroup.zpowers a₂ : Set _) :=
    hcent.trans (Subgroup.centralizer_le_normalizer _)
  have hH₀ : IsPGroup 3 (Subgroup.zpowers a₁ ⊔ Subgroup.zpowers a₂ : Subgroup _) :=
    hp1.to_sup_of_normal_right' hp2 hnorm
  obtain ⟨S₀, hS₀⟩ := hH₀.exists_le_sylow
  have ha1S₀ : a₁ ∈ (S₀ : Subgroup _) := hS₀ (Subgroup.mem_sup_left (Subgroup.mem_zpowers a₁))
  have ha2S₀ : a₂ ∈ (S₀ : Subgroup _) := hS₀ (Subgroup.mem_sup_right (Subgroup.mem_zpowers a₂))
  have hPp : IsPGroup 3 P := IsPGroup.of_card (n := 2) (by rw [hP]; norm_num)
  obtain ⟨S', hPS'⟩ := hPp.exists_le_sylow
  have hS'card : Nat.card (S' : Subgroup (alternatingGroup (Fin n))) = 9 := by
    have hS'pg : IsPGroup 3 (S' : Subgroup (alternatingGroup (Fin n))) := S'.isPGroup'
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hS'pg
    have hdvd : Nat.card (S' : Subgroup (alternatingGroup (Fin n))) ∣
        Nat.card (alternatingGroup (Fin n)) := Subgroup.card_subgroup_dvd_card _
    have hle : 9 ≤ Nat.card (S' : Subgroup (alternatingGroup (Fin n))) := by
      have := Subgroup.card_le_of_le hPS'
      rw [hP] at this
      exact this
    have hk2 : k ≤ 2 := by
      by_contra hk3
      push Not at hk3
      apply h27
      exact (pow_dvd_pow 3 hk3).trans (hk ▸ hdvd)
    have hk2' : 2 ≤ k := by
      by_contra hk3
      push Not at hk3
      have h3 : 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h9 : 9 ≤ 3 ^ k := hk ▸ hle
      omega
    have : k = 2 := le_antisymm hk2 hk2'
    rw [hk, this]
    norm_num
  have hPeq : P = (S' : Subgroup (alternatingGroup (Fin n))) :=
    Subgroup.eq_of_le_of_card_ge hPS' (by rw [hS'card, hP])
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin n)) S' S₀
  have hcS : (S₀ : Subgroup _) = MulAut.conj c • (S' : Subgroup (alternatingGroup (Fin n))) := by
    rw [← hc]
    rfl
  have hfwd : ∀ x ∈ P, c * x * c⁻¹ ∈ (S₀ : Subgroup _) := by
    intro x hx
    rw [hcS, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨x, hPeq ▸ hx, by simp [MulAut.conj_apply]⟩
  have hbwd : ∀ s ∈ (S₀ : Subgroup _), c⁻¹ * s * c ∈ P := by
    intro s hs
    rw [hcS, Subgroup.mem_smul_pointwise_iff_exists] at hs
    obtain ⟨x, hx, rfl⟩ := hs
    rw [hPeq]
    have : c⁻¹ * (MulAut.conj c • x) * c = x := by simp [MulAut.conj_apply, mul_assoc]
    rw [this]
    exact hx
  have hcinj : ∀ u v : alternatingGroup (Fin n), c⁻¹ * u * c = c⁻¹ * v * c ↔ u = v := fun u v => by
    constructor
    · intro h
      exact mul_left_cancel (mul_right_cancel h)
    · intro h
      rw [h]
  set ℓ₂ := c * ℓ * c⁻¹ with hℓ₂
  set y₂ := c * y * c⁻¹ with hy₂
  have hℓ₂ℓ₂ : ℓ₂ * ℓ₂ = 1 := by
    calc ℓ₂ * ℓ₂ = c * (ℓ * ℓ) * c⁻¹ := by simp only [hℓ₂]; group
      _ = 1 := by rw [hℓℓ]; group
  have hy₂y₂ : y₂ * y₂ = 1 := by
    calc y₂ * y₂ = c * (y * y) * c⁻¹ := by simp only [hy₂]; group
      _ = 1 := by rw [hyy]; group
  have hℓ₂y₂ : ℓ₂ * y₂ = y₂ * ℓ₂ := by
    calc ℓ₂ * y₂ = c * (ℓ * y) * c⁻¹ := by simp only [hℓ₂, hy₂]; group
      _ = c * (y * ℓ) * c⁻¹ := by rw [hℓy]
      _ = y₂ * ℓ₂ := by simp only [hℓ₂, hy₂]; group
  have hy₂ne : y₂ ≠ ℓ₂ := fun h => hyℓ (by
    have h' := congrArg (fun z => c⁻¹ * z * c) h
    simpa [hy₂, hℓ₂, mul_assoc] using h')
  have hy₂1 : y₂ ≠ 1 := fun h => hy1 (by
    have h' := congrArg (fun z => c⁻¹ * z * c) h
    simpa [hy₂, mul_assoc] using h')
  have hℓ₂1 : ℓ₂ ≠ 1 := fun h => hℓ1 (by
    have h' := congrArg (fun z => c⁻¹ * z * c) h
    simpa [hℓ₂, mul_assoc] using h')
  have hℓ₂inv : ℓ₂⁻¹ = ℓ₂ := inv_eq_of_mul_eq_one_right hℓ₂ℓ₂
  have hcube_inv : ∀ a : alternatingGroup (Fin n), a * a * a = 1 → a⁻¹ = a * a := fun a h =>
    inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact h)
  have hinvS : ∀ a : alternatingGroup (Fin n), a ∈ (S₀ : Subgroup (alternatingGroup (Fin n))) →
      ℓ₂ * a * ℓ₂ = a⁻¹ := by
    intro a ha
    have hx := hinv _ (hbwd a ha)
    calc ℓ₂ * a * ℓ₂ = ℓ₂ * a * ℓ₂⁻¹ := by rw [hℓ₂inv]
      _ = c * (ℓ * (c⁻¹ * a * c) * ℓ⁻¹) * c⁻¹ := by simp only [hℓ₂]; group
      _ = c * (c⁻¹ * a * c)⁻¹ * c⁻¹ := by rw [hx]
      _ = a⁻¹ := by group
  have hl1 : cmp (cmp (encA ℓ₂) (c1 n)) (encA ℓ₂) = cmp (c1 n) (c1 n) := by
    rw [← h1, ← encA_mul, ← encA_mul, ← encA_mul, hinvS a₁ ha1S₀, hcube_inv a₁ ha31]
  have hl2 : cmp (cmp (encA ℓ₂) (c2 n)) (encA ℓ₂) = cmp (c2 n) (c2 n) := by
    rw [← h2, ← encA_mul, ← encA_mul, ← encA_mul, hinvS a₂ ha2S₀, hcube_inv a₂ ha32]
  have hmv : ∀ g : alternatingGroup (Fin n), g * g = 1 → g ≠ 1 → moved n (encA g) = 4 := by
    intro g hgg hg1
    unfold encA
    rw [moved_enc]
    refine CFSG.CGT.T75I.card_support_of_even_involution hn ?_ ?_ ?_
    · have := congrArg Subtype.val hgg
      simpa [sq] using this
    · exact fun h => hg1 (Subtype.ext h)
    · exact Equiv.Perm.mem_alternatingGroup.1 g.2
  have hll : cmp (encA ℓ₂) (encA ℓ₂) = idl n := by rw [← encA_mul, hℓ₂ℓ₂, encA_one]
  have hyy' : cmp (encA y₂) (encA y₂) = idl n := by rw [← encA_mul, hy₂y₂, encA_one]
  have hcomm' : cmp (encA ℓ₂) (encA y₂) = cmp (encA y₂) (encA ℓ₂) := by
    rw [← encA_mul, ← encA_mul, hℓ₂y₂]
  have hne' : encA y₂ ≠ encA ℓ₂ := fun h => hy₂ne (encA_injective h)
  obtain ⟨i, hi, j, hj, hmis⟩ := hF (encA ℓ₂) (enc_mem_permutations _) (hmv ℓ₂ hℓ₂ℓ₂ hℓ₂1) hll
    hl1 hl2 (encA y₂) (enc_mem_permutations _) (hmv y₂ hy₂y₂ hy₂1) hyy' hcomm' hne'
  have hi3 : i < 3 := List.mem_range.1 hi
  have hj3 : j < 3 := List.mem_range.1 hj
  let pa : alternatingGroup (Fin n) → ℕ → alternatingGroup (Fin n) := fun a k =>
    if k = 0 then 1 else if k = 1 then a else a * a
  have hpa : ∀ a k, encA (pa a k) = ppow n (encA a) k := by
    intro a k
    simp only [pa, ppow]
    split_ifs <;> simp [encA_one, encA_mul]
  have hpaS : ∀ a ∈ (S₀ : Subgroup (alternatingGroup (Fin n))), ∀ k, pa a k ∈ S₀ := by
    intro a ha k
    simp only [pa]
    split_ifs
    · exact (S₀ : Subgroup (alternatingGroup (Fin n))).one_mem
    · exact ha
    · exact (S₀ : Subgroup (alternatingGroup (Fin n))).mul_mem ha ha
  set q₂ : alternatingGroup (Fin n) := pa a₁ i * pa a₂ j with hq₂
  have hq₂S : q₂ ∈ (S₀ : Subgroup (alternatingGroup (Fin n))) :=
    (S₀ : Subgroup (alternatingGroup (Fin n))).mul_mem (hpaS a₁ ha1S₀ i) (hpaS a₂ ha2S₀ j)
  have hencq : encA q₂ = qlist n i j := by
    rw [hq₂, encA_mul, hpa, hpa, h1, h2]
    rfl
  have hq₂3 : q₂ * q₂ * q₂ = 1 := by
    apply encA_injective
    rw [encA_mul, encA_mul, hencq, encA_one]
    exact hq3 i hi j hj
  have hq₂inv : q₂⁻¹ = q₂ * q₂ := hcube_inv q₂ hq₂3
  have hcj : ∀ w : alternatingGroup (Fin n),
      cj (encA q₂) (encA w) = encA (q₂⁻¹ * w * q₂) := by
    intro w
    rw [hq₂inv]
    simp only [cj, encA_mul]
  have L1 : (cmp (encA y₂) (cj (qlist n i j) (encA y₂)) =
      cmp (cj (qlist n i j) (encA y₂)) (encA y₂)) ↔
      y₂ * (q₂⁻¹ * y₂ * q₂) = (q₂⁻¹ * y₂ * q₂) * y₂ := by
    rw [← hencq, hcj]
    exact cmp_eq_iff _ _ _ _
  have L2 : (cmp (cmp (encA y₂) (encA ℓ₂)) (cj (qlist n i j) (cmp (encA y₂) (encA ℓ₂))) =
      cmp (cj (qlist n i j) (cmp (encA y₂) (encA ℓ₂))) (cmp (encA y₂) (encA ℓ₂))) ↔
      (y₂ * ℓ₂) * (q₂⁻¹ * (y₂ * ℓ₂) * q₂) = (q₂⁻¹ * (y₂ * ℓ₂) * q₂) * (y₂ * ℓ₂) := by
    rw [← hencq, ← encA_mul, hcj]
    exact cmp_eq_iff _ _ _ _
  have hmis' : ¬ ((y₂ * (q₂⁻¹ * y₂ * q₂) = (q₂⁻¹ * y₂ * q₂) * y₂) ↔
      ((y₂ * ℓ₂) * (q₂⁻¹ * (y₂ * ℓ₂) * q₂) = (q₂⁻¹ * (y₂ * ℓ₂) * q₂) * (y₂ * ℓ₂))) :=
    fun h => hmis (L1.trans (h.trans L2.symm))
  refine ⟨c⁻¹ * q₂ * c, hbwd q₂ hq₂S, ?_⟩
  have hyc : y = c⁻¹ * y₂ * c := by rw [hy₂]; group
  have hℓc : ℓ = c⁻¹ * ℓ₂ * c := by rw [hℓ₂]; group
  have e1 : y * ((c⁻¹ * q₂ * c)⁻¹ * y * (c⁻¹ * q₂ * c)) =
      c⁻¹ * (y₂ * (q₂⁻¹ * y₂ * q₂)) * c := by rw [hyc]; group
  have e2 : ((c⁻¹ * q₂ * c)⁻¹ * y * (c⁻¹ * q₂ * c)) * y =
      c⁻¹ * ((q₂⁻¹ * y₂ * q₂) * y₂) * c := by rw [hyc]; group
  have e3 : (y * ℓ) * ((c⁻¹ * q₂ * c)⁻¹ * (y * ℓ) * (c⁻¹ * q₂ * c)) =
      c⁻¹ * ((y₂ * ℓ₂) * (q₂⁻¹ * (y₂ * ℓ₂) * q₂)) * c := by rw [hyc, hℓc]; group
  have e4 : ((c⁻¹ * q₂ * c)⁻¹ * (y * ℓ) * (c⁻¹ * q₂ * c)) * (y * ℓ) =
      c⁻¹ * ((q₂⁻¹ * (y₂ * ℓ₂) * q₂) * (y₂ * ℓ₂)) * c := by rw [hyc, hℓc]; group
  rw [e1, e2, e3, e4, hcinj, hcinj]
  exact hmis'

theorem fl2_alt_six {P : Subgroup (alternatingGroup (Fin 6))} (hP : Nat.card P = 9)
    {ℓ y : alternatingGroup (Fin 6)} (hℓℓ : ℓ * ℓ = 1) (hyy : y * y = 1) (hℓy : ℓ * y = y * ℓ)
    (hyℓ : y ≠ ℓ) (hy1 : y ≠ 1) (hℓ1 : ℓ ≠ 1) (hinv : ∀ p ∈ P, ℓ * p * ℓ⁻¹ = p⁻¹) :
    ∃ q ∈ P, ¬ ((y * (q⁻¹ * y * q) = (q⁻¹ * y * q) * y) ↔
      ((y * ℓ) * (q⁻¹ * (y * ℓ) * q) = (q⁻¹ * (y * ℓ) * q) * (y * ℓ))) := by
  have m1 : (swap (⟨0, by norm_num⟩ : Fin 6) ⟨1, by norm_num⟩ *
      swap ⟨1, by norm_num⟩ ⟨2, by norm_num⟩) ∈ alternatingGroup (Fin 6) := by
    rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap (by decide),
      Perm.sign_swap (by decide)]
    norm_num
  have m2 : (swap (⟨3, by norm_num⟩ : Fin 6) ⟨4, by norm_num⟩ *
      swap ⟨4, by norm_num⟩ ⟨5, by norm_num⟩) ∈ alternatingGroup (Fin 6) := by
    rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap (by decide),
      Perm.sign_swap (by decide)]
    norm_num
  have h27 : ¬ 27 ∣ Nat.card (alternatingGroup (Fin 6)) := by
    have h := two_mul_nat_card_alternatingGroup (α := Fin 6)
    rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 6), Fintype.card_fin] at h
    have h6 : Nat.factorial 6 = 720 := by decide
    omega
  have e1 : enc (swap (⟨0, by norm_num⟩ : Fin 6) ⟨1, by norm_num⟩ *
      swap ⟨1, by norm_num⟩ ⟨2, by norm_num⟩) = c1 6 := by decide
  have e2 : enc (swap (⟨3, by norm_num⟩ : Fin 6) ⟨4, by norm_num⟩ *
      swap ⟨4, by norm_num⟩ ⟨5, by norm_num⟩) = c2 6 := by decide
  exact fl2_alt (n := 6) (by norm_num) fl2List_six ⟨_, m1⟩ ⟨_, m2⟩ e1 e2
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h27 hP hℓℓ hyy hℓy
    hyℓ hy1 hℓ1 hinv


theorem fl2_alt_seven {P : Subgroup (alternatingGroup (Fin 7))} (hP : Nat.card P = 9)
    {ℓ y : alternatingGroup (Fin 7)} (hℓℓ : ℓ * ℓ = 1) (hyy : y * y = 1) (hℓy : ℓ * y = y * ℓ)
    (hyℓ : y ≠ ℓ) (hy1 : y ≠ 1) (hℓ1 : ℓ ≠ 1) (hinv : ∀ p ∈ P, ℓ * p * ℓ⁻¹ = p⁻¹) :
    ∃ q ∈ P, ¬ ((y * (q⁻¹ * y * q) = (q⁻¹ * y * q) * y) ↔
      ((y * ℓ) * (q⁻¹ * (y * ℓ) * q) = (q⁻¹ * (y * ℓ) * q) * (y * ℓ))) := by
  have m1 : (swap (⟨0, by norm_num⟩ : Fin 7) ⟨1, by norm_num⟩ *
      swap ⟨1, by norm_num⟩ ⟨2, by norm_num⟩) ∈ alternatingGroup (Fin 7) := by
    rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap (by decide),
      Perm.sign_swap (by decide)]
    norm_num
  have m2 : (swap (⟨3, by norm_num⟩ : Fin 7) ⟨4, by norm_num⟩ *
      swap ⟨4, by norm_num⟩ ⟨5, by norm_num⟩) ∈ alternatingGroup (Fin 7) := by
    rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap (by decide),
      Perm.sign_swap (by decide)]
    norm_num
  have h27 : ¬ 27 ∣ Nat.card (alternatingGroup (Fin 7)) := by
    have h := two_mul_nat_card_alternatingGroup (α := Fin 7)
    rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 7), Fintype.card_fin] at h
    have h6 : Nat.factorial 7 = 5040 := by decide
    omega
  have e1 : enc (swap (⟨0, by norm_num⟩ : Fin 7) ⟨1, by norm_num⟩ *
      swap ⟨1, by norm_num⟩ ⟨2, by norm_num⟩) = c1 7 := by decide
  have e2 : enc (swap (⟨3, by norm_num⟩ : Fin 7) ⟨4, by norm_num⟩ *
      swap ⟨4, by norm_num⟩ ⟨5, by norm_num⟩) = c2 7 := by decide
  exact fl2_alt (n := 7) (by norm_num) fl2List_seven ⟨_, m1⟩ ⟨_, m2⟩ e1 e2
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h27 hP hℓℓ hyy hℓy
    hyℓ hy1 hℓ1 hinv

theorem fl2_main {X : Type} [Group X] (hn : n = 6 ∨ n = 7) (e : X ≃* alternatingGroup (Fin n))
    {P : Subgroup X} (hP : Nat.card P = 9) {ℓ y : X} (hℓℓ : ℓ * ℓ = 1) (hyy : y * y = 1)
    (hℓy : ℓ * y = y * ℓ) (hyℓ : y ≠ ℓ) (hy1 : y ≠ 1) (hℓ1 : ℓ ≠ 1)
    (hinv : ∀ p ∈ P, ℓ * p * ℓ⁻¹ = p⁻¹) :
    ∃ q ∈ P, ¬ ((y * (q⁻¹ * y * q) = (q⁻¹ * y * q) * y) ↔
      ((y * ℓ) * (q⁻¹ * (y * ℓ) * q) = (q⁻¹ * (y * ℓ) * q) * (y * ℓ))) := by
  classical
  have hP' : Nat.card (P.map e.toMonoidHom) = 9 :=
    (Nat.card_congr (e.subgroupMap P).toEquiv).symm.trans hP
  have hℓℓ' : e ℓ * e ℓ = 1 := by rw [← map_mul, hℓℓ, map_one]
  have hyy' : e y * e y = 1 := by rw [← map_mul, hyy, map_one]
  have hℓy' : e ℓ * e y = e y * e ℓ := by rw [← map_mul, ← map_mul, hℓy]
  have hyℓ' : e y ≠ e ℓ := fun h => hyℓ (e.injective h)
  have hy1' : e y ≠ 1 := fun h => hy1 (e.injective (by rw [h, map_one]))
  have hℓ1' : e ℓ ≠ 1 := fun h => hℓ1 (e.injective (by rw [h, map_one]))
  have hinv' : ∀ p' ∈ P.map e.toMonoidHom, e ℓ * p' * (e ℓ)⁻¹ = p'⁻¹ := by
    intro p' hp'
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 hp'
    have h2 := congrArg e (hinv p hp)
    simpa [map_mul, map_inv] using h2
  have key : ∃ q' ∈ P.map e.toMonoidHom, ¬ ((e y * (q'⁻¹ * e y * q') = (q'⁻¹ * e y * q') * e y) ↔
      ((e y * e ℓ) * (q'⁻¹ * (e y * e ℓ) * q') = (q'⁻¹ * (e y * e ℓ) * q') * (e y * e ℓ))) := by
    rcases hn with rfl | rfl
    · exact fl2_alt_six hP' hℓℓ' hyy' hℓy' hyℓ' hy1' hℓ1' hinv'
    · exact fl2_alt_seven hP' hℓℓ' hyy' hℓy' hyℓ' hy1' hℓ1' hinv'
  obtain ⟨q', hq', hmis⟩ := key
  obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hq'
  refine ⟨q, hq, fun h => hmis ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, ← map_inv, ← map_mul, EmbeddingLike.apply_eq_iff_eq]
  exact h

theorem card_alt_not_27 (hn : n = 6 ∨ n = 7) : ¬ 27 ∣ Nat.card (alternatingGroup (Fin n)) := by
  rcases hn with rfl | rfl
  · have h := two_mul_nat_card_alternatingGroup (α := Fin 6)
    rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 6), Fintype.card_fin] at h
    have h6 : Nat.factorial 6 = 720 := by decide
    omega
  · have h := two_mul_nat_card_alternatingGroup (α := Fin 7)
    rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 7), Fintype.card_fin] at h
    have h7 : Nat.factorial 7 = 5040 := by decide
    omega

end CFSG.CGT.T75H.PermModel
