module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableCrit2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableBound

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def K32ZBound2 (N : Type) [Group N] (m₁ m₂ : ℕ) : Prop :=
  (∀ ω : MulAut N, ω ∈ innAut N → orderOf ω = 3 → ∀ W : Subgroup (MulAut N), W ≤ innAut N →
    IsPGroup 2 ↥W → W ≤ Subgroup.centralizer ({ω} : Set (MulAut N)) → Nat.card ↥W ≤ m₁) ∧
  (∀ ω : MulAut N, ω ∉ innAut N → orderOf ω = 3 → ∀ W : Subgroup (MulAut N), W ≤ innAut N →
    IsPGroup 2 ↥W → W ≤ Subgroup.centralizer ({ω} : Set (MulAut N)) → Nat.card ↥W ≤ m₂)

theorem k32_noDatum_of_quot2 {K N : Type} [Group K] [Finite K] [Group N] [Finite N]
    (hperf : Group.IsPerfect K) (e : K ⧸ Subgroup.center K ≃* N) {m₁ m₂ : ℕ}
    (hN : K32ZBound2 N m₁ m₂) (hlt₁ : 16 * m₁ < 2 ^ (Nat.card N).factorization 2)
    (hlt₂ : 8 * m₂ < 2 ^ (Nat.card N).factorization 2) : K32NoDatum K := by
  intro X P R A V hd
  obtain ⟨ω, -, hω3, W, hWJ, hW2, hWC, hin, hout⟩ := k32_crit2 hd
  have : Group.IsPerfect K := hperf
  let Φ : MulAut K →* MulAut N := (MulAut.congr e).toMonoidHom.comp (k32AutQuot K)
  have hΦinj : Function.Injective Φ :=
    (MulAut.congr e).injective.comp k32AutQuot_injective
  have hω3' : orderOf (Φ ω) = 3 := (orderOf_injective Φ hΦinj ω).trans hω3
  have hWΦ2 : IsPGroup 2 ↥(W.map Φ) := hW2.of_equiv (Subgroup.equivMapOfInjective W Φ hΦinj)
  have hΦconj : ∀ k : K, Φ (MulAut.conj k) = MulAut.conj (e (k : K ⧸ Subgroup.center K)) := by
    intro k
    show MulAut.congr e (k32AutQuot K (MulAut.conj k)) = _
    rw [k32AutQuot_conj, k32_congr_conj]
  have hWΦJ : W.map Φ ≤ innAut N := by
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨k, rfl⟩ := hWJ hw
    exact ⟨e (k : K ⧸ Subgroup.center K), (hΦconj k).symm⟩
  have hWΦC : W.map Φ ≤ Subgroup.centralizer ({Φ ω} : Set (MulAut N)) := by
    rintro _ ⟨w, hw, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hWC hw)
    rw [← map_mul, ← map_mul, h1]
  have hcardW : Nat.card ↥(W.map Φ) = Nat.card ↥W := Subgroup.card_map_of_injective hΦinj
  have h2 : twoPart (innAut K) = 2 ^ (Nat.card N).factorization 2 := by
    unfold twoPart
    rw [k32_card_innAut, Nat.card_congr e.toEquiv]
  by_cases hω : ω ∈ innAut K
  · have hΦω : Φ ω ∈ innAut N := by
      obtain ⟨k, rfl⟩ := hω
      exact ⟨_, (hΦconj k).symm⟩
    have h1 := hN.1 (Φ ω) hΦω hω3' (W.map Φ) hWΦJ hWΦ2 hWΦC
    have h3 := hin hω
    rw [h2] at h3
    rw [hcardW] at h1
    omega
  · have hΦω : Φ ω ∉ innAut N := by
      rintro ⟨n, hn⟩
      obtain ⟨y, rfl⟩ := e.surjective n
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
      apply hω
      refine ⟨k, hΦinj ?_⟩
      rw [hΦconj k]
      exact hn
    have h1 := hN.2 (Φ ω) hΦω hω3' (W.map Φ) hWΦJ hWΦ2 hWΦC
    have h3 := hout hω
    rw [h2] at h3
    rw [hcardW] at h1
    omega

theorem k32_noDatum_of_iso2 {K N : Type} [Group K] [Finite K] [Group N] [Finite N]
    (hperf : Group.IsPerfect K) (e : K ≃* N) (hZ : Subgroup.center N = ⊥) {m₁ m₂ : ℕ}
    (hN : K32ZBound2 N m₁ m₂) (hlt₁ : 16 * m₁ < 2 ^ (Nat.card N).factorization 2)
    (hlt₂ : 8 * m₂ < 2 ^ (Nat.card N).factorization 2) : K32NoDatum K := by
  have hZK : Subgroup.center K = ⊥ := by
    have h1 : (Subgroup.center K).map (e : K →* N) = ⊥ := by
      rw [Subgroup.map_center_eq e, hZ]
    exact (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center K) e.injective).mp h1
  let e' : K ⧸ Subgroup.center K ≃* N :=
    (QuotientGroup.quotientMulEquivOfEq hZK).trans (QuotientGroup.quotientBot.trans e)
  exact k32_noDatum_of_quot2 hperf e' hN hlt₁ hlt₂

end CFSG.QuasithinUnique.DoubleA3
