module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L511I

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools GorensteinWalter

variable {G : Type} [Group G] [Finite G]

theorem mem_of_card_le_four {X : Type*} [Group X] [Finite X] {H : Subgroup X}
    (hH : Nat.card H ≤ 4) {a b c d x : X} (ha : a ∈ H) (hb : b ∈ H) (hc : c ∈ H) (hd : d ∈ H)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hx : x ∈ H) : x = a ∨ x = b ∨ x = c ∨ x = d := by
  classical
  by_contra hne
  push Not at hne
  obtain ⟨hxa, hxb, hxc, hxd⟩ := hne
  let f : Fin 5 → H := ![⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩, ⟨x, hx⟩]
  have hf : Function.Injective f := by
    intro i j hij
    have h1 := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> simp [f] at h1 <;> first
      | rfl
      | exact absurd h1 hab | exact absurd h1 hac | exact absurd h1 had | exact absurd h1 hbc
      | exact absurd h1 hbd | exact absurd h1 hcd | exact absurd h1 hxa | exact absurd h1 hxb
      | exact absurd h1 hxc | exact absurd h1 hxd
      | exact absurd h1.symm hab | exact absurd h1.symm hac | exact absurd h1.symm had
      | exact absurd h1.symm hbc | exact absurd h1.symm hbd | exact absurd h1.symm hcd
      | exact absurd h1.symm hxa | exact absurd h1.symm hxb | exact absurd h1.symm hxc
      | exact absurd h1.symm hxd
  have h5 := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h5
  omega

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
  {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊)
  {Lin : Subgroup (MulAut 𝕊)}
include h

theorem mem_Q_mul_of_centralizes_R (hD : Foote5AutData 𝕊 Lin) {r : G} (hrS : r ∈ S)
    (hr2 : r * r = 1) (hrlin : actG L ε r ∉ Lin) (hrR : ∀ ρ ∈ S ⊓ L, r * ρ = ρ * r) {y : G}
    (hyS : y ∈ S) (hyR : ∀ ρ ∈ S ⊓ L, y * ρ = ρ * y) :
    y ∈ Q ∨ y * t ∈ Q ∨ y * r ∈ Q ∨ y * r * t ∈ Q := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := S ⊓ centralizer ((S ⊓ L : Subgroup G) : Set G) with hCdef
  have hCN : C ≤ normalizer (L : Set G) := inf_le_left.trans h.S_le
  set P := actImage L ε C with hPdef
  have hP2 : IsPGroup 2 P := isPGroup_actImage ε (h.isPGroup_S.to_le inf_le_left)
  have hPfix : ∀ α ∈ P, ∀ ρ ∈ (h.Rbar ε : Subgroup 𝕊), α ρ = ρ := by
    intro α hα
    obtain ⟨c, hc, rfl⟩ := (mem_actImage ε hCN).mp hα
    exact (h.actG_fix_iff ε (mem_inf.mp hc).1).mpr fun ρ' hρ' =>
      (mem_centralizer_iff.mp (mem_inf.mp hc).2 ρ' hρ').symm
  obtain ⟨-, hP4⟩ := hD.centralizer_sylow (h.Rbar ε) P hP2 hPfix
  have hmemC : ∀ x ∈ S, (∀ ρ ∈ S ⊓ L, x * ρ = ρ * x) → x ∈ C := fun x hx hxR =>
    mem_inf.mpr ⟨hx, mem_centralizer_iff.mpr fun ρ hρ => (hxR ρ hρ).symm⟩
  have hyC := hmemC y hyS hyR
  have hrC := hmemC r hrS hrR
  have htC := hmemC t h.tS fun ρ hρ => (h.tZ ρ (mem_inf.mp hρ).1).symm
  have hrN := h.S_le hrS
  have htN := h.S_le h.tS
  have hyN := h.S_le hyS
  have htinn : actG L ε t ∈ Lin := hD.inn_le (by rw [actG_of_mem_self ε h.tL]; exact ⟨_, rfl⟩)
  have ht1 : actG L ε t ≠ 1 := fun h1 => h.t_not_mem_Q ((h.actG_eq_one_iff_mem_Q ε h.tS).mp h1)
  have hr1 : actG L ε r ≠ 1 := fun h1 => hrlin (h1 ▸ one_mem _)
  have hrt : actG L ε r ≠ actG L ε t := fun h1 => hrlin (h1 ▸ htinn)
  have hrt1 : actG L ε r * actG L ε t ≠ 1 := fun h1 => hrlin (by
    rw [eq_inv_of_mul_eq_one_left h1]
    exact inv_mem htinn)
  have hrtt : actG L ε r * actG L ε t ≠ actG L ε t := fun h1 => hr1 (by
    calc actG L ε r = actG L ε r * actG L ε t * (actG L ε t)⁻¹ := by group
      _ = 1 := by rw [h1, mul_inv_cancel])
  have hrtr : actG L ε r * actG L ε t ≠ actG L ε r := fun h1 => ht1 (by
    calc actG L ε t = (actG L ε r)⁻¹ * (actG L ε r * actG L ε t) := by group
      _ = 1 := by rw [h1, inv_mul_cancel])
  have hmem : ∀ x ∈ C, actG L ε x ∈ P := fun x hx => actG_mem_actImage ε hCN hx
  have hrtP : actG L ε r * actG L ε t ∈ P := by
    rw [← actG_mul ε hrN htN]
    exact hmem _ (mul_mem hrC htC)
  have ht2 : actG L ε t * actG L ε t = 1 := by
    rw [← actG_mul ε htN htN, h.t_mul_self, actG_one]
  have hr2' : actG L ε r * actG L ε r = 1 := by rw [← actG_mul ε hrN hrN, hr2, actG_one]
  have hrtc : actG L ε r * actG L ε t = actG L ε t * actG L ε r := by
    rw [← actG_mul ε hrN htN, ← actG_mul ε htN hrN, h.tZ r hrS]
  rcases mem_of_card_le_four hP4 (one_mem P) (hmem t htC) (hmem r hrC) hrtP ht1.symm hr1.symm
    hrt1.symm hrt.symm hrtt.symm hrtr.symm (hmem y hyC) with h1 | h1 | h1 | h1
  · exact Or.inl ((h.actG_eq_one_iff_mem_Q ε hyS).mp h1)
  · right; left
    rw [← h.actG_eq_one_iff_mem_Q ε (mul_mem hyS h.tS), actG_mul ε hyN htN, h1, ht2]
  · right; right; left
    rw [← h.actG_eq_one_iff_mem_Q ε (mul_mem hyS hrS), actG_mul ε hyN hrN, h1, hr2']
  · right; right; right
    rw [← h.actG_eq_one_iff_mem_Q ε (mul_mem (mul_mem hyS hrS) h.tS),
      actG_mul ε (mul_mem hyN hrN) htN, actG_mul ε hyN hrN, h1]
    calc actG L ε r * actG L ε t * actG L ε r * actG L ε t =
        actG L ε r * (actG L ε t * actG L ε r) * actG L ε t := by group
      _ = actG L ε r * (actG L ε r * actG L ε t) * actG L ε t := by rw [hrtc]
      _ = (actG L ε r * actG L ε r) * (actG L ε t * actG L ε t) := by group
      _ = 1 := by rw [hr2', ht2, one_mul]

end Sec5

end CFSG.ComponentClassification.Foote5
