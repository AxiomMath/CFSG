module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.GLTheoremB.Defs

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

section Simple

variable {L T : Type*} [Group L] [Group T]

theorem map_eq_bot_of_coprime {p : ℕ} (hp : p.Prime) [Finite L] {f : L →* T}
    (hf : Function.Surjective f) (hT : IsSimpleGroup T) (hpT : p ∣ Nat.card T) {N : Subgroup L}
    [N.Normal] (hN : Nat.Coprime p (Nat.card N)) : N ≤ f.ker := by
  have : (N.map f).Normal := Subgroup.Normal.map ‹_› f hf
  have := hT
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map f) with h | h
  · intro x hx
    have : f x ∈ N.map f := ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact this
  · exfalso
    have hdvd : Nat.card (N.map f) ∣ Nat.card N := Subgroup.card_map_dvd N f
    rw [h, Subgroup.card_top] at hdvd
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hN (hpT.trans hdvd))

theorem centerless_of_simple (hT : IsSimpleGroup T) (hnab : ∃ a b : T, a * b ≠ b * a) :
    ∀ x : T, (∀ y, x * y = y * x) → x = 1 := by
  intro x hx
  have hmem : x ∈ Subgroup.center T := Subgroup.mem_center_iff.2 fun g => (hx g).symm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center T) with h | h
  · rw [h, Subgroup.mem_bot] at hmem
    exact hmem
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have : a ∈ Subgroup.center T := h ▸ Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.1 this b).symm

theorem glaPPrimeCore_eq_ker {p : ℕ} (hp : p.Prime) [Finite L] {f : L →* T}
    (hf : Function.Surjective f) (hT : IsSimpleGroup T) (hpT : p ∣ Nat.card T)
    (hker : ¬ p ∣ Nat.card f.ker) : GLAPPrimeCore p L = f.ker := by
  apply le_antisymm
  · refine sSup_le fun N hN => ?_
    obtain ⟨hNn, hNc⟩ := hN
    exact map_eq_bot_of_coprime hp hf hT hpT hNc
  · exact le_sSup ⟨inferInstance, (Nat.Prime.coprime_iff_not_dvd hp).2 hker⟩

theorem center_quotient_eq_bot {p : ℕ} (hp : p.Prime) [Finite L] {f : L →* T}
    (hf : Function.Surjective f) (hT : IsSimpleGroup T) (hnab : ∃ a b : T, a * b ≠ b * a)
    (hpT : p ∣ Nat.card T) (hker : ¬ p ∣ Nat.card f.ker) :
    Subgroup.center (L ⧸ GLAPPrimeCore p L) = ⊥ := by
  have hO := glaPPrimeCore_eq_ker hp hf hT hpT hker
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective z
  apply Subgroup.mem_bot.2
  have hc : f c = 1 := by
    apply centerless_of_simple hT hnab
    intro t
    obtain ⟨l, rfl⟩ := hf t
    have h1 := Subgroup.mem_center_iff.1 hz (l : L ⧸ GLAPPrimeCore p L)
    have h2 : ((l * c : L) : L ⧸ GLAPPrimeCore p L) = ((c * l : L) : L ⧸ GLAPPrimeCore p L) := h1
    have h3 := (QuotientGroup.eq).1 h2
    rw [hO, MonoidHom.mem_ker] at h3
    simp only [map_mul, map_inv, inv_mul_eq_one] at h3
    exact h3.symm
  show (c : L ⧸ GLAPPrimeCore p L) = 1
  rw [QuotientGroup.eq_one_iff, hO]
  exact hc

end Simple

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
