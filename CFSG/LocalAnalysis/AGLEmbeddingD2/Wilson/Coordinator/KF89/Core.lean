module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.OuterFixInvolution
public import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.RankThree.PartTwo.Sec13.Item136PGL
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3CentralizerStructure
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3OuterInvClosed
public import CFSG.RankThree.PartTwo.Sec4.Item47Native

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF89

open CFSG Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem false_of_outer_on_perfect {J : Type*} [Group J] [Finite J]
    (hOut : Nat.card (Outer J) ≤ 2)
    (hNo : ∀ α : MulAut J, α ^ 2 = 1 → α ∉ (MulAut.conj : J →* MulAut J).range →
      ∀ E : Subgroup J, CFSG.Open.IsElemAbelian 3 E → Nat.card E = 9 → ∃ x ∈ E, α x ≠ x)
    {y : J} (hy : orderOf y = 3) (K : Subgroup J) (hKy : K ≤ centralizer ({y} : Set J))
    (hCy : centralizer ({y} : Set J) ≤ zpowers y ⊔ K)
    (hZK : ∀ k ∈ K, (∀ x ∈ K, k * x = x * k) → k = 1)
    (τ : MulAut J) (hτy : τ y = y)
    (hτ2 : ∀ k ∈ K, τ (τ k) = k)
    (hτo : ∀ g ∈ K, ∃ k ∈ K, τ k ≠ g * k * g⁻¹)
    {w : J} (hwK : w ∈ K) (hw3 : w ^ 3 = 1) (hw1 : w ≠ 1) (hτw : τ w = w) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hy3 : y ^ 3 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hyK : ∀ x ∈ K, x * y = y * x := fun x hx => mem_centralizer_singleton_iff.mp (hKy hx)
  have hcommK : ∀ x ∈ K, ∀ n : ℤ, y ^ n * x = x * y ^ n := fun x hx n =>
    ((Commute.zpow_right (show Commute x y from hyK x hx) n).eq).symm
  have hyC : y ∈ centralizer (K : Set J) := by
    rw [mem_centralizer_iff]
    exact hyK
  have hdec : ∀ g ∈ centralizer ({y} : Set J), ∃ n : ℤ, ∃ k ∈ K, g = y ^ n * k := by
    intro g hg
    have hn : zpowers y ≤ normalizer (K : Set J) :=
      (zpowers_le.mpr hyC).trans (Subgroup.centralizer_le_normalizer (K : Set J))
    have hg' : g ∈ ((zpowers y ⊔ K : Subgroup J) : Set J) := hCy hg
    rw [coe_mul_of_left_le_normalizer_right _ _ hn] at hg'
    obtain ⟨a, ha, k, hk, rfl⟩ := Set.mem_mul.mp hg'
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp ha
    exact ⟨n, k, hk, rfl⟩
  have hconjK : ∀ (n : ℤ), ∀ k ∈ K, ∀ x ∈ K,
      (y ^ n * k) * x * (y ^ n * k)⁻¹ = k * x * k⁻¹ := by
    intro n k hk x hx
    have hm : k * x * k⁻¹ ∈ K := K.mul_mem (K.mul_mem hk hx) (K.inv_mem hk)
    calc (y ^ n * k) * x * (y ^ n * k)⁻¹ = y ^ n * (k * x * k⁻¹) * (y ^ n)⁻¹ := by group
      _ = (k * x * k⁻¹) * y ^ n * (y ^ n)⁻¹ := by rw [hcommK _ hm n]
      _ = k * x * k⁻¹ := by group
  have hfixC : ∀ g : J, MulAut.conj g y = y → g ∈ centralizer ({y} : Set J) := by
    intro g hg
    rw [MulAut.conj_apply] at hg
    rw [mem_centralizer_singleton_iff]
    calc g * y = g * y * g⁻¹ * g := by group
      _ = y * g := by rw [hg]
  have hτout : τ ∉ (MulAut.conj : J →* MulAut J).range := by
    rintro ⟨g, rfl⟩
    obtain ⟨n, k, hk, rfl⟩ := hdec g (hfixC _ hτy)
    obtain ⟨x, hx, hne⟩ := hτo k hk
    apply hne
    rw [MulAut.conj_apply]
    exact hconjK n k hk x hx
  have hτ2in : τ ^ 2 ∈ (MulAut.conj : J →* MulAut J).range := by
    set q : Outer J := QuotientGroup.mk τ with hq
    have hpos : 0 < Nat.card (Outer J) := Nat.card_pos
    have hdvd : orderOf q ∣ 2 := by
      have h1 := orderOf_dvd_natCard q
      rcases (show Nat.card (Outer J) = 1 ∨ Nat.card (Outer J) = 2 by omega) with h | h
      · rw [h] at h1
        exact h1.trans (one_dvd 2)
      · rwa [h] at h1
    have h2 : q ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd
    rw [hq, ← QuotientGroup.mk_pow] at h2
    have h3 : τ ^ 2 ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner J :=
      (QuotientGroup.eq_one_iff
        (N := CFSG.ComponentClassification.OuterAutomorphisms.inner J) _).mp h2
    exact h3
  obtain ⟨g', hg'⟩ := hτ2in
  have hg'y : MulAut.conj g' y = y := by rw [hg', sq, MulAut.mul_apply, hτy, hτy]
  obtain ⟨m, k', hk', hg'eq⟩ := hdec g' (hfixC _ hg'y)
  have hk'1 : k' = 1 := by
    refine hZK k' hk' fun x hx => ?_
    have h1 : MulAut.conj g' x = x := by rw [hg', sq, MulAut.mul_apply, hτ2 x hx]
    rw [MulAut.conj_apply, hg'eq, hconjK m k' hk' x hx] at h1
    calc k' * x = k' * x * k'⁻¹ * k' := by group
      _ = x * k' := by rw [h1]
  obtain ⟨i, hi⟩ : ∃ i : ℕ, y ^ i = y ^ m :=
    Submonoid.mem_powers_iff _ _ |>.mp (mem_powers_iff_mem_zpowers.mpr (zpow_mem_zpowers y m))
  have hτ2eq : τ ^ 2 = MulAut.conj (y ^ i) := by
    rw [← hg', hg'eq, hk'1, mul_one, hi]
  obtain ⟨hσ2, hσo, hσy⟩ := Proving.exists_outer_involution_of_fix_eq hy3 τ hτout hτy hτ2eq
  have hσw : (τ * MulAut.conj (y ^ i)) w = w := by
    rw [MulAut.mul_apply, MulAut.conj_apply]
    have h1 := hcommK w hwK (i : ℤ)
    rw [zpow_natCast] at h1
    rw [h1, mul_inv_cancel_right, hτw]
  have hwy : w ∉ zpowers y := by
    intro hw
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hw
    exact hw1 (hZK _ hwK fun x hx => hcommK x hx n)
  obtain ⟨hEl, hEcard⟩ := CFSG.RankThree.PartTwo.Sec5.isElemAbelian_sup_zpowers
    (CFSG.RankThree.PartTwo.Sec13.isElemAbelian_zpowers hy3) hwy hw3 (fun a ha => by
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp ha
      exact hcommK w hwK n)
  rw [Nat.card_zpowers, hy] at hEcard
  obtain ⟨x, hx, hσx⟩ := hNo _ hσ2 hσo _ ⟨hEl.1, hEl.2⟩ hEcard
  have hle : zpowers y ⊔ zpowers w ≤
      ((τ * MulAut.conj (y ^ i)).toMonoidHom).eqLocus (MonoidHom.id J) :=
    sup_le (zpowers_le.mpr hσy) (zpowers_le.mpr hσw)
  exact hσx (hle hx)

open CFSG.Blueprint in
theorem false_of_J3_outer_on_A6
    {Q : Type} [Group Q] [Finite Q] (e : Q ≃* NativeSporadic.J3)
    {y : Q} (hy : orderOf y = 3) (K : Subgroup Q) (hK360 : Nat.card K = 360)
    (hZK : ∀ k ∈ K, (∀ x ∈ K, k * x = x * k) → k = 1)
    (hKy : K ≤ centralizer ({y} : Set Q))
    (τ : MulAut Q) (hτy : τ y = y) (hτ2 : ∀ k ∈ K, τ (τ k) = k)
    (hτo : ∀ g ∈ K, ∃ k ∈ K, τ k ≠ g * k * g⁻¹)
    {w : Q} (hwK : w ∈ K) (hw3 : w ^ 3 = 1) (hw1 : w ≠ 1) (hτw : τ w = w) : False := by
  have hOut : Nat.card (Outer Q) ≤ 2 :=
    CFSG.Sporadic.Schreier.outer_card_le_of_equiv CFSG.RankThree.PartTwo.Sec4.card_outer_J3 e
  have hJ : Nonempty (Q ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) := by
    obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
    exact ⟨e.trans b⟩
  have hNo := CFSG.AGLEmbedding.kFactJ3OuterInvolution Q hJ
  have hy3 : y ^ 3 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hy1 : y ≠ 1 := by rintro rfl; rw [orderOf_one] at hy; omega
  have hCy : centralizer ({y} : Set Q) ≤ zpowers y ⊔ K := by
    have hle : zpowers y ⊔ K ≤ centralizer ({y} : Set Q) :=
      sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)) hKy
    have hyK : y ∉ K := by
      intro hyK
      apply hy1
      exact hZK y hyK fun x hx => (mem_centralizer_singleton_iff.mp (hKy hx)).symm
    have hdisj : Disjoint (zpowers y) K := by
      rw [disjoint_iff, eq_bot_iff]
      intro x ⟨hx1, hx2⟩
      rw [mem_bot]
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx1
      exact hZK _ hx2 fun x hx =>
        ((Commute.zpow_left (show Commute y x from
          (mem_centralizer_singleton_iff.mp (hKy hx)).symm) n).eq)
    have h1 :=
      CFSG.AGLEmbeddingD2.Wilson.NormalizerAction.card_mul_le_card_sup_of_disjoint _ _ hdisj
    rw [Nat.card_zpowers, hy, hK360] at h1
    have h2 := Subgroup.card_le_of_le hle
    rcases CFSG.AGLEmbeddingD2.Wilson.NormalizerAction.card_centralizer_of_equiv_J3_dichotomy e hy3
      hy1 with h | h
    · exact (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm.le
    · omega
  exact false_of_outer_on_perfect hOut hNo hy K hKy hCy hZK τ hτy hτ2 hτo hwK hw3 hw1 hτw

end CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF89
