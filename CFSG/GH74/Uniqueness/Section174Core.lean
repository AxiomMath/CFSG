module

public import CFSG.GH74.Uniqueness.Section16Stmts
public import CFSG.GH74.Uniqueness.Section174Frame

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

theorem Sec174.false_of_unitary (h311 : Lemma311BenderStmt) {K : Type} [Group K] [Finite K]
    {n e : ℕ} (hK : Bender.BenderType K n 3 e) {A : Subgroup K} (hA : Odd (Nat.card A))
    {s : K} (hs2 : s * s = 1) (hs1 : s ≠ 1) (hsA : ∀ a ∈ A, s * a * s⁻¹ ∈ A)
    (hborel : ∀ Q : Sylow 2 K, ¬ A ≤ Bender.borel (Q : Subgroup K))
    (hN : ∀ x : K, (∀ a ∈ A, x * a * x⁻¹ ∈ A) → x ∈ A ∨ x * s ∈ A)
    (hc1 : (centralizer ({s} : Set K)).relIndex A ≡ 1 [MOD 2 ^ n])
    (hc2 : (centralizer ({s} : Set K)).relIndex A ≠ 1) : False := by
  obtain ⟨F, F₀, hF, hle⟩ := h311 hK A hA s hs2 hs1 hsA hborel
  have hAF₀ : A ≤ F₀ := le_sup_left.trans hle
  have hsF₀ : s ∈ F₀ := hle (Subgroup.mem_sup_right (Subgroup.mem_zpowers s))
  have hn2 : 2 ≤ n := hK.two_le.2
  have hq4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  set q : ℕ := 2 ^ n with hq
  set d : ℕ := Nat.gcd 3 (q + 1) with hd
  have hd0 : 0 < d := Nat.gcd_pos_of_pos_left _ (by norm_num)
  set T : Subgroup ↥F₀ := F.subgroupOf F₀ with hTdef
  have hTn : T.Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hF.normal g g.2 x hx⟩
  have hTc : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := fun x hx y hy =>
    Subtype.ext (hF.comm _ (Subgroup.mem_subgroupOf.mp hx) _ (Subgroup.mem_subgroupOf.mp hy))
  have hTcardF : Nat.card T = Nat.card F := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF.le).toEquiv
  have hFodd : Odd (Nat.card F) := by
    have h1 := hF.card
    have hodd : Odd ((q + 1) ^ 2) := by
      apply Odd.pow
      rw [hq]
      exact Even.add_one ((Nat.even_pow' (by omega)).mpr (by norm_num))
    rw [← h1] at hodd
    exact (Nat.odd_mul.mp hodd).1
  have hTodd : Odd (Nat.card T) := by rw [hTcardF]; exact hFodd
  obtain ⟨π, hπs, hπk⟩ := hF.perm
  set s' : ↥F₀ := ⟨s, hsF₀⟩ with hs'
  have hs'2 : s' * s' = 1 := Subtype.ext hs2
  have hcentT : T ⊓ centralizer ({s'} : Set ↥F₀) =
      (F ⊓ centralizer ({s} : Set K)).subgroupOf F₀ := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hx, hxs⟩
      exact ⟨hx, congrArg Subtype.val hxs⟩
    · rintro ⟨hx, hxs⟩
      exact ⟨hx, Subtype.ext hxs⟩
  have hTcard : Nat.card T = (q + 1) * Nat.card ↥(T ⊓ centralizer ({s'} : Set ↥F₀)) := by
    rw [hcentT, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hF.le)).toEquiv,
      hTcardF]
    have h1 := hF.card
    have h2 := hF.card_cent
    have : Nat.card F * d = (q + 1) * Nat.card ↥(F ⊓ centralizer ({s} : Set K)) * d := by
      rw [h1, mul_assoc, h2, pow_two]
    exact Nat.eq_of_mul_eq_mul_right hd0 this
  set A' : Subgroup ↥F₀ := A.subgroupOf F₀ with hA'def
  have hA'card : Nat.card A' = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAF₀).toEquiv
  have hA' : Odd (Nat.card A') := by rw [hA'card]; exact hA
  have hsA' : ∀ a ∈ A', s' * a * s'⁻¹ ∈ A' := fun a ha => by
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    exact hsA _ ha
  have hN' : ∀ x : ↥F₀, (∀ a ∈ A', x * a * x⁻¹ ∈ A') → x ∈ A' ∨ x * s' ∈ A' := by
    intro x hx
    have hxA : ∀ a ∈ A, (x : K) * a * (x : K)⁻¹ ∈ A := by
      intro a ha
      have := hx ⟨a, hAF₀ ha⟩ (Subgroup.mem_subgroupOf.mpr ha)
      exact Subgroup.mem_subgroupOf.mp this
    rcases hN x hxA with h | h
    · exact Or.inl (Subgroup.mem_subgroupOf.mpr h)
    · exact Or.inr (Subgroup.mem_subgroupOf.mpr h)
  have hCT : A' ⊓ centralizer ({s'} : Set ↥F₀) ≤ T := by
    intro x hx
    obtain ⟨hxA, hxs⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_subgroupOf] at hxA ⊢
    rw [Subgroup.mem_centralizer_singleton_iff] at hxs
    have hodd : Odd (orderOf (x : K)) := Odd.of_dvd_nat hA (Subgroup.orderOf_dvd_natCard A hxA)
    exact hF.mem_of_commute_of_odd (by positivity) x.2 hsF₀ hs2 (congrArg Subtype.val hxs) hodd
  have hcent' : centralizer ({s'} : Set ↥F₀) = (centralizer ({s} : Set K)).subgroupOf F₀ := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hcA : (centralizer ({s'} : Set ↥F₀)).relIndex A' =
      (centralizer ({s} : Set K)).relIndex A := by
    rw [hcent', hA'def, Subgroup.relIndex_subgroupOf hAF₀]
  exact Sec174.frame_contra hTc hTodd hπs hπk hs'2 hq4 hTcard hA' hsA' hN' hCT
    (by rw [hcA]; exact hc1) (by rw [hcA]; exact hc2)

end CFSG.GH74.Uniqueness
