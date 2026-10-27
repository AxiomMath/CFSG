module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SFieldStrong

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup

section Helpers

variable {G : Type} [Group G] [Finite G]

private theorem eight_le_card_sup_zpowers {F : Subgroup G} {z : G} (hF : 4 ≤ Nat.card F)
    (hzF : z ∉ F) : 8 ≤ Nat.card ↥(F ⊔ zpowers z) := by
  have hle : F ≤ F ⊔ zpowers z := le_sup_left
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hle
  have hk1 : k ≠ 1 := by
    rintro rfl
    rw [mul_one] at hk
    exact hzF ((Subgroup.eq_of_le_of_card_ge hle hk.le) ▸
      (le_sup_right : zpowers z ≤ F ⊔ zpowers z) (mem_zpowers z))
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk
    exact Nat.card_pos.ne' hk
  rw [hk]
  calc 8 = 4 * 2 := by norm_num
    _ ≤ Nat.card F * k := Nat.mul_le_mul hF (by omega)

private theorem three_le_pRank_of_sq_mem {S A : Subgroup G} {y z : G} (hAS : A ≤ S)
    (hA : IsElemTwo A) (hA16 : 16 ≤ Nat.card A) (hyS : y ∈ S)
    (hyA : y ∈ normalizer (A : Set G)) (hy2 : ∀ e ∈ A, y * y * e = e * (y * y))
    (hzy : z ∈ zpowers y) (hz2 : z * z = 1) (hzA : z ∉ A)
    (hzc : ∀ e ∈ A, e * z = z * e) :
    3 ≤ pRank 2 ↥(S ⊓ centralizer ({y} : Set G)) := by
  set F := A ⊓ centralizer ({y} : Set G) with hF
  have hsq := card_le_card_inf_centralizer_sq_of_sq hA hyA hy2
  have hF4 : 4 ≤ Nat.card F := (le_card_of_le_card_sq (hA.isPGroup.to_le inf_le_left)).1
    (by omega)
  have hzyc : z ∈ centralizer ({y} : Set G) := by
    obtain ⟨k, rfl⟩ := hzy
    exact mem_centralizer_singleton_iff.mpr (Commute.zpow_self y k).eq
  have hE : IsElemTwo (F ⊔ zpowers z) :=
    (hA.mono inf_le_left).sup (isElemTwo_zpowers hz2) fun x hx w hw => by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
      exact Commute.zpow_right (hzc x (mem_inf.mp hx).1) k
  have hzS : z ∈ S := by
    obtain ⟨k, rfl⟩ := hzy
    exact zpow_mem hyS k
  refine three_le_pRank_of_le hE (eight_le_card_sup_zpowers hF4 fun h => hzA (mem_inf.mp h).1)
    (sup_le (inf_le_inf_right _ hAS) (zpowers_le.mpr (mem_inf.mpr ⟨hzS, hzyc⟩)))

private theorem three_le_pRank_of_conj {S A B : Subgroup G} (hAS : A ≤ S)
    (hAn : S ≤ normalizer (A : Set G)) (hA : IsElemTwo A) (hA16 : 16 ≤ Nat.card A)
    (hAB : A ⊓ B = ⊥) (hBA : ∀ b ∈ B, ∀ e ∈ A, b * e = e * b) {x g : G} {k : ℕ}
    (hxo : orderOf x = 2 ^ (k + 2)) (hy : g⁻¹ * x * g ∈ S)
    (hy2 : g⁻¹ * x * g * (g⁻¹ * x * g) ∈ B) :
    3 ≤ pRank 2 ↥(S ⊓ centralizer ({g⁻¹ * x * g} : Set G)) := by
  obtain ⟨y, hydef⟩ : ∃ y, y = g⁻¹ * x * g := ⟨_, rfl⟩
  rw [← hydef] at hy hy2 ⊢
  have hyo : orderOf y = 2 ^ (k + 2) := by
    rw [hydef, ← hxo, ← orderOf_injective (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective x]
    simp
  have hzB : y ^ 2 ^ (k + 1) ∈ B := by
    rw [pow_succ', pow_mul]
    exact pow_mem (by rwa [sq]) _
  have hz2 : y ^ 2 ^ (k + 1) * y ^ 2 ^ (k + 1) = 1 := by
    rw [← pow_add, ← two_mul, ← pow_succ', ← hyo, pow_orderOf_eq_one]
  have hz1 : y ^ 2 ^ (k + 1) ≠ 1 := by
    intro h1
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hyo] at h2
    have h3 := Nat.le_of_dvd (by positivity) h2
    have h4 : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := pow_succ' 2 (k + 1)
    have h5 := Nat.one_le_two_pow (n := k + 1)
    omega
  have hzA : y ^ 2 ^ (k + 1) ∉ A := fun hzA =>
    hz1 (mem_bot.mp (hAB ▸ mem_inf.mpr ⟨hzA, hzB⟩))
  exact three_le_pRank_of_sq_mem hAS hA hA16 hy (hAn hy) (fun e he => hBA _ hy2 e he)
    (pow_mem (mem_zpowers y) _) hz2 hzA (fun e he => (hBA _ hzB e he).symm)

private theorem conj_mem_of_sq_mem {S A B M : Subgroup G} (hAS : A ≤ S) (hBS : B ≤ S)
    (hAn : S ≤ normalizer (A : Set G)) (hA : IsElemTwo A) (hA16 : 16 ≤ Nat.card A)
    (hAB : A ⊓ B = ⊥) (hcomm : B ≤ centralizer (A : Set G))
    (hBM : ∀ m ∈ M, ∀ b ∈ B, m⁻¹ * b * m ∈ S → m⁻¹ * b * m ∈ B)
    (hfus : ∀ x ∈ S, ∀ g : G, g⁻¹ * x * g ∈ S →
      3 ≤ pRank 2 ↥(S ⊓ centralizer ({x} : Set G)) →
      3 ≤ pRank 2 ↥(S ⊓ centralizer ({g⁻¹ * x * g} : Set G)) →
      ∃ m ∈ M, g⁻¹ * x * g = m⁻¹ * x * m)
    {x g : G} (hx : x ∈ B) {k : ℕ} (hxo : orderOf x = 2 ^ (k + 2)) (hy : g⁻¹ * x * g ∈ S)
    (hy2 : g⁻¹ * x * g * (g⁻¹ * x * g) ∈ B) : g⁻¹ * x * g ∈ B := by
  have hBA : ∀ b ∈ B, ∀ e ∈ A, b * e = e * b := fun b hb e he =>
    (mem_centralizer_iff.mp (hcomm hb) e he).symm
  have hrx : 3 ≤ pRank 2 ↥(S ⊓ centralizer ({x} : Set G)) :=
    three_le_pRank_of_le hA (by omega) fun e he =>
      mem_inf.mpr ⟨hAS he, mem_centralizer_singleton_iff.mpr (hBA x hx e he).symm⟩
  obtain ⟨m, hm, hmy⟩ := hfus x (hBS hx) g hy hrx
    (three_le_pRank_of_conj hAS hAn hA hA16 hAB hBA hxo hy hy2)
  rw [hmy] at hy ⊢
  exact hBM m hm x hx hy

end Helpers

theorem stronglyClosed_kernel_of_rank_four
    {G : Type} [Group G] [Finite G] {S A B M : Subgroup G}
    (hS : IsPGroup 2 S) (_hSM : S ≤ M)
    (hAS : A ≤ S) (hBS : B ≤ S)
    (hAn : S ≤ normalizer (A : Set G))
    (hA : Open.IsElemAbelian 2 A) (hA16 : 16 ≤ Nat.card A)
    (hAB : A ⊓ B = ⊥) (hcomm : B ≤ centralizer (A : Set G))
    (hBinv : ∀ b ∈ B, orderOf b = 2 → ∀ g : G,
      g⁻¹ * b * g ∈ S → g⁻¹ * b * g ∈ B)
    (hBM : ∀ m ∈ M, ∀ b ∈ B, m⁻¹ * b * m ∈ S →
      m⁻¹ * b * m ∈ B)
    (hfus : ∀ x ∈ S, ∀ g : G, g⁻¹ * x * g ∈ S →
      3 ≤ pRank 2 ↥(S ⊓ centralizer ({x} : Set G)) →
      3 ≤ pRank 2 ↥(S ⊓ centralizer ({g⁻¹ * x * g} : Set G)) →
      ∃ m ∈ M, g⁻¹ * x * g = m⁻¹ * x * m) :
    CFSG.IsStronglyClosedIn S (B : Set G) := by
  have hA' : IsElemTwo A := isElemTwo_of_sq fun a ha => by rw [← pow_two]; exact hA.2 a ha
  refine ⟨hBS, fun x hx g hy => ?_⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hS) ⟨x, hBS hx⟩
  rw [Subgroup.orderOf_mk] at hn
  induction n using Nat.strong_induction_on generalizing x g with
  | _ n ih =>
    match n, hn with
    | 0, hn =>
      rw [pow_zero, orderOf_eq_one_iff] at hn
      subst hn
      simp
    | 1, hn => exact hBinv x hx (by rw [hn, pow_one]) g hy
    | k + 2, hn =>
      refine conj_mem_of_sq_mem hAS hBS hAn hA' hA16 hAB hcomm hBM hfus hx hn hy ?_
      have hx2 : x * x ∈ B := mul_mem hx hx
      have hx2o : orderOf (x * x) = 2 ^ (k + 1) := by
        rw [← sq, orderOf_pow' _ (by norm_num), hn, Nat.gcd_comm,
          Nat.gcd_eq_left (dvd_pow_self 2 (by omega)), pow_succ, Nat.mul_div_cancel _ two_pos]
      have hy2 : g⁻¹ * (x * x) * g ∈ S := by
        have : g⁻¹ * (x * x) * g = g⁻¹ * x * g * (g⁻¹ * x * g) := by group
        rw [this]
        exact mul_mem hy hy
      have := ih (k + 1) (by omega) (x * x) hx2 g hy2 hx2o
      rwa [show g⁻¹ * (x * x) * g = g⁻¹ * x * g * (g⁻¹ * x * g) by group] at this

end CFSG.ComponentClassification.GrSLit.L34Sec5S

end
