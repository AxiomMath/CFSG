module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Helpers2
import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

private theorem isElemAbelian_of_le {G : Type*} [Group G] {p : ℕ} {E E₀ : Subgroup G}
    (hE₀ : CFSG.Open.IsElemAbelian p E₀) (hEE₀ : E ≤ E₀) :
    CFSG.Open.IsElemAbelian p E := by
  have := hE₀.1
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => hE₀.2 x (hEE₀ hx)⟩
  have hc := congrArg Subtype.val (mul_comm' (⟨a, hEE₀ a.2⟩ : E₀) ⟨b, hEE₀ b.2⟩)
  exact Subtype.ext (by simpa using hc)

theorem sec8t84_two_e16_of_e32 {M : Type} [Group M] [Finite M] {A : Subgroup M}
    (hA : IsElemAb2 A 5) :
    ∃ K₁ K₂ : Subgroup M, K₁ ≤ A ∧ K₂ ≤ A ∧ K₁ ≠ K₂ ∧ IsElemAb2 K₁ 4 ∧ IsElemAb2 K₂ 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K₁, hK₁card, -, hK₁le⟩ :=
    Sylow.exists_subgroup_card_pow_prime_le_le (p := 2) Nat.prime_two (n := 4)
      (H := ⊥) (L := A) (by rw [Subgroup.card_bot]; exact one_dvd _)
      (by rw [hA.2]; norm_num) bot_le
  have hK₁el : CFSG.Open.IsElemAbelian 2 K₁ := isElemAbelian_of_le hA.1 hK₁le
  have hlt : K₁ < A := by
    refine lt_of_le_of_ne hK₁le ?_
    intro heq
    have hc : Nat.card K₁ = Nat.card A := by rw [heq]
    rw [hK₁card, hA.2] at hc
    norm_num at hc
  obtain ⟨x, hxA, hxK₁⟩ := SetLike.exists_of_lt hlt
  have hx2 : x ^ 2 = 1 := hA.1.2 x hxA
  have hx1 : x ≠ 1 := fun hx => hxK₁ (by rw [hx]; exact Subgroup.one_mem K₁)
  have hxord : orderOf x = 2 := orderOf_eq_prime hx2 hx1
  have hzx : Subgroup.zpowers x ≤ A := Subgroup.zpowers_le.mpr hxA
  obtain ⟨K₂, hK₂card, hzxK₂, hK₂le⟩ :=
    Sylow.exists_subgroup_card_pow_prime_le_le (p := 2) Nat.prime_two (n := 4)
      (H := Subgroup.zpowers x) (L := A)
      (by rw [Nat.card_zpowers, hxord]; norm_num) (by rw [hA.2]; norm_num) hzx
  have hxK₂ : x ∈ K₂ := hzxK₂ (Subgroup.mem_zpowers x)
  have hne : K₁ ≠ K₂ := fun heq => hxK₁ (by rw [heq]; exact hxK₂)
  have hK₂el : CFSG.Open.IsElemAbelian 2 K₂ := isElemAbelian_of_le hA.1 hK₂le
  exact ⟨K₁, K₂, hK₁le, hK₂le, hne, ⟨hK₁el, hK₁card⟩, ⟨hK₂el, hK₂card⟩⟩

theorem sec8t84_no32_of_only {M : Type} [Group M] [Finite M] {P E F : Subgroup M}
    (honly : ∀ F' : Subgroup M, F' ≤ P → IsElemAb2 F' 4 → F' = E ∨ F' = F)
    (hJ : Nat.card ↥(E ⊔ F) = 64) :
    ∀ F' : Subgroup M, F' ≤ P → ¬ IsElemAb2 F' 5 := by
  intro F' hF'P hF'5
  obtain ⟨K₁, K₂, hK₁F', hK₂F', hne, hK₁, hK₂⟩ := sec8t84_two_e16_of_e32 hF'5
  have hK₁' := honly K₁ (hK₁F'.trans hF'P) hK₁
  have hK₂' := honly K₂ (hK₂F'.trans hF'P) hK₂
  have hEF : E ⊔ F ≤ F' := by
    rcases hK₁' with h1 | h1 <;> rcases hK₂' with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · exact sup_le (h1 ▸ hK₁F') (h2 ▸ hK₂F')
    · exact sup_le (h2 ▸ hK₂F') (h1 ▸ hK₁F')
    · exact absurd (h1.trans h2.symm) hne
  have hcard := Subgroup.card_le_of_le hEF
  rw [hJ, hF'5.2] at hcard
  norm_num at hcard

theorem sec8t84_rank_cent {Y : Type} [Group Y] [Finite Y] {P : Subgroup Y}
    (hP : IsSylow2Of P ⊤) (h32 : ∀ F' : Subgroup Y, F' ≤ P → ¬ IsElemAb2 F' 5)
    (hwit : ∀ s : Y, orderOf s = 2 → ∃ A : Subgroup Y, A ≤ centralizer ({s} : Set Y) ∧
      CFSG.Open.IsElemAbelian 2 A ∧ 16 ≤ Nat.card A) :
    ∀ s : Y, orderOf s = 2 → CFSG.Open.pRank 2 (centralizer ({s} : Set Y)) = 4 := by
  intro s hs2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, hAC, hAel, hAcard⟩ := hwit s hs2
  have hA2 : IsPGroup 2 A := fun y => ⟨1, Subtype.ext (by simpa using hAel.2 y y.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA2
  have hk4 : 4 ≤ k := by
    have hle : 2 ^ 4 ≤ 2 ^ k := by
      calc 2 ^ 4 = 16 := by norm_num
        _ ≤ Nat.card A := hAcard
        _ = 2 ^ k := hk
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
  refine le_antisymm ?_ ?_
  · refine CFSG.SectionRank.pRank_le (p := 2) (k := 4) (by norm_num) ?_
    intro E hEC hEel
    have hE2 : IsPGroup 2 E := fun y => ⟨1, Subtype.ext (by simpa using hEel.2 y y.2)⟩
    obtain ⟨c, _hc, hconj⟩ := exists_conj_le_of_isSylow2Of hP hE2 le_top
    let f : Y →* Y := (MulAut.conj c).toMonoidHom
    have hf : Function.Injective f := (MulAut.conj c).injective
    have hE'el : CFSG.Open.IsElemAbelian 2 (E.map f) :=
      CFSG.SectionRank.isElemAbelian_map hEel f
    have hE'P : E.map f ≤ P := by
      rintro _ ⟨y, hy, rfl⟩
      simpa [f, MulAut.conj_apply] using hconj y hy
    have hE'card : Nat.card (E.map f) = Nat.card E := Subgroup.card_map_of_injective hf
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hE2
    have hm4 : m ≤ 4 := by
      by_contra h
      have hm5 : 5 ≤ m := by omega
      have hdvd : 2 ^ 5 ∣ Nat.card (E.map f) := by
        rw [hE'card, hm]
        exact pow_dvd_pow 2 hm5
      obtain ⟨K, hKcard, -, hKE'⟩ :=
        Sylow.exists_subgroup_card_pow_prime_le_le (p := 2) Nat.prime_two (n := 5)
          (H := ⊥) (L := E.map f) (by rw [Subgroup.card_bot]; exact one_dvd _) hdvd bot_le
      exact h32 K (hKE'.trans hE'P) ⟨isElemAbelian_of_le hE'el hKE', hKcard⟩
    calc Nat.card E = 2 ^ m := hm
      _ ≤ 2 ^ 4 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mpr hm4
  · calc 4 ≤ k := hk4
      _ ≤ CFSG.Open.pRank 2 (centralizer ({s} : Set Y)) :=
        CFSG.SectionRank.le_pRank (p := 2) (by norm_num) hAC hAel hk

end CFSG.OddStandard.SmallF3.Omega
