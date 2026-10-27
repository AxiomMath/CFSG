module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuSzEightModel

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.LieType.Ree

structure E8Normalized {G : Type*} [Group G] (E : Subgroup G) (n : G) : Prop where
  sq : ∀ x ∈ E, x ^ 2 = 1
  card : Nat.card E = 8
  normalizes : ∀ x ∈ E, n * x * n⁻¹ ∈ E
  pow_seven : n ^ 7 = 1
  fixed : ∀ x ∈ E, n * x * n⁻¹ = x → x = 1

theorem E8Normalized.map {G H : Type*} [Group G] [Group H] {E : Subgroup G} {n : G}
    (h : E8Normalized E n) (e : G ≃* H) : E8Normalized (E.map e.toMonoidHom) (e n) where
  sq := by
    rintro _ ⟨x, hx, rfl⟩
    show (e x) ^ 2 = 1
    rw [← map_pow, h.sq x hx, map_one]
  card := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact h.card
  normalizes := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨n * x * n⁻¹, h.normalizes x hx, by simp [map_mul]⟩
  pow_seven := by rw [← map_pow, h.pow_seven, map_one]
  fixed := by
    rintro _ ⟨x, hx, rfl⟩ hfix
    have h1 : e (n * x * n⁻¹) = e x := by simpa [map_mul] using hfix
    have h2 := e.injective h1
    show e x = 1
    rw [h.fixed x hx h2, map_one]

section Suzuki

variable {F : Type} [Field F] [Finite F]

theorem suzukiDElt_pow (a : ℕ) (l : Fˣ) (k : ℕ) :
    suzukiDElt a F l ^ k = suzukiDElt a F (l ^ k) := by
  induction k with
  | zero => rw [pow_zero, pow_zero, suzukiDElt_one]
  | succ k ih => rw [pow_succ, ih, suzukiDElt_mul, pow_succ]

theorem suzuki_E8Normalized (hF : Nat.card F = 2 ^ (2 * 1 + 1)) :
    ∃ n : suzukiGroup 1 F, E8Normalized (suzukiZ0 1 F) n := by
  obtain ⟨l, hl⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hcardU : Nat.card Fˣ = 7 := by rw [Nat.card_units, hF]; norm_num
  have hord : orderOf l = 7 := by rw [orderOf_eq_card_of_forall_mem_zpowers hl, hcardU]
  obtain ⟨hsq, -, hcard⟩ := suzukiZ0_facts hF
  have hconj : ∀ v : F, suzukiDElt 1 F l * suzukiSElt 1 F 0 v * (suzukiDElt 1 F l)⁻¹ =
      suzukiSElt 1 F 0 (((l⁻¹ : Fˣ) : F) ^ 5 * v) := by
    intro v
    rw [suzukiDElt_conj' hF l 0 v, mul_zero]
    rfl
  refine ⟨suzukiDElt 1 F l,
    ⟨fun x hx => by rw [pow_two]; exact hsq x hx, by rw [hcard], ?_, ?_, ?_⟩⟩
  · intro x hx
    obtain ⟨v, rfl⟩ := (mem_suzukiZ0_iff hF).1 hx
    rw [hconj]
    exact (mem_suzukiZ0_iff hF).2 ⟨_, rfl⟩
  · rw [suzukiDElt_pow, show l ^ 7 = 1 by rw [← hord]; exact pow_orderOf_eq_one l,
      suzukiDElt_one]
  · intro x hx hfix
    obtain ⟨v, rfl⟩ := (mem_suzukiZ0_iff hF).1 hx
    rw [hconj, suzukiSElt_inj] at hfix
    by_cases hv : v = 0
    · rw [hv, suzukiSElt_zero_zero hF]
    · exfalso
      have h1 : ((l⁻¹ : Fˣ) : F) ^ 5 = 1 := by
        have : (((l⁻¹ : Fˣ) : F) ^ 5 - 1) * v = 0 := by linear_combination hfix.2
        rcases mul_eq_zero.1 this with h | h
        · exact sub_eq_zero.1 h
        · exact absurd h hv
      have h2 : (l⁻¹) ^ 5 = 1 := Units.ext (by simpa using h1)
      have h3 : orderOf l⁻¹ ∣ 5 := orderOf_dvd_of_pow_eq_one h2
      rw [orderOf_inv, hord] at h3
      omega

theorem exists_E8Normalized (hF : Nat.card F = 2 ^ (2 * 1 + 1)) {z : suzukiGroup 1 F}
    (hz : orderOf z = 2) :
    ∃ (E : Subgroup (suzukiGroup 1 F)) (n : suzukiGroup 1 F), z ∈ E ∧ E8Normalized E n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_suzukiGroup hF
  have hzp : IsPGroup 2 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])
  obtain ⟨P, hP⟩ := hzp.exists_le_sylow
  have hzP : z ∈ P := hP (Subgroup.mem_zpowers z)
  let Pu : Sylow 2 (suzukiGroup 1 F) :=
    Sylow.ofCard (suzukiU 1 F) (CFSG.RankThree.card_suzukiU_eq hF)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (suzukiGroup 1 F) Pu P
  rw [← hg, CFSG.RankThree.mem_smul_sylow_iff] at hzP
  have hzU : g⁻¹ * z * g ∈ suzukiU 1 F := hzP
  have hz2 : (g⁻¹ * z * g) ^ 2 = 1 := by
    rw [show g⁻¹ * z * g = (MulAut.conj g⁻¹) z by simp, ← map_pow, ← hz, pow_orderOf_eq_one,
      map_one]
  have hz1 : g⁻¹ * z * g ≠ 1 := by
    intro h
    have : z = 1 := by
      have := congrArg (fun y => g * y * g⁻¹) h
      simpa [mul_assoc] using this
    rw [this, orderOf_one] at hz
    exact absurd hz (by norm_num)
  obtain ⟨v, -, hv⟩ := CFSG.RankThree.eq_suzukiSElt_zero_of_sq_eq_one hF hzU hz2 hz1
  obtain ⟨n₀, hn₀⟩ := suzuki_E8Normalized hF
  refine ⟨(suzukiZ0 1 F).map (MulAut.conj g).toMonoidHom, MulAut.conj g n₀,
    ⟨g⁻¹ * z * g, (mem_suzukiZ0_iff hF).2 ⟨v, hv.symm⟩, by simp [mul_assoc]⟩,
    hn₀.map (MulAut.conj g)⟩

end Suzuki

end CFSG.EvenSporadicStandard.Induction
