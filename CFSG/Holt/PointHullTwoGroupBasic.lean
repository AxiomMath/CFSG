module

public import CFSG.Goldschmidt.Steps.Red2Basic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3FourEightTypes
public import CFSG.Holt.Basic

public section

namespace CFSG.Holt.PointHull

open MulAction CFSG.Open
open scoped commutatorElement

section Embedding

variable {X : Type*} [Group X]

private theorem orderOf_conj_eq (g x : X) : orderOf (g * x * g⁻¹) = orderOf x :=
  (orderOf_eq_of_isConj (isConj_iff.mpr ⟨g, rfl⟩)).symm

private theorem mem_map_conj_inv_iff {M : Subgroup X} {g t : X} :
    t ∈ M.map (MulAut.conj g⁻¹).toMonoidHom ↔ g * t * g⁻¹ ∈ M := by
  constructor
  · rintro ⟨m, hm, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hm
  · intro h
    exact ⟨g * t * g⁻¹, h, by simp [mul_assoc]⟩

theorem mem_of_conj_mem_of_fusionStronglyEmbedded {B : Subgroup X}
    (hB : fusionStronglyEmbedded B) {s y : X} (hs : s ∈ B) (hys : y * s * y⁻¹ ∈ B)
    (hs2 : orderOf s = 2) : y ∈ B := by
  by_contra hy
  have hmem : s ∈ B ⊓ B.map (MulAut.conj y⁻¹).toMonoidHom := ⟨hs, mem_map_conj_inv_iff.mpr hys⟩
  have hdvd := orderOf_dvd_natCard (⟨s, hmem⟩ : ↥(B ⊓ B.map (MulAut.conj y⁻¹).toMonoidHom))
  rw [Subgroup.orderOf_mk, hs2] at hdvd
  exact (Nat.not_even_iff_odd.mpr (hB.2.2 y hy)) (even_iff_two_dvd.mpr hdvd)

variable [Finite X]

theorem exists_inv_mul_mul_mem_sylow {P : Sylow 2 X} {H : Subgroup X}
    (hPH : (P : Subgroup X) ≤ H) {t : X} (htH : t ∈ H) (ht : orderOf t = 2) :
    ∃ h ∈ H, h⁻¹ * t * h ∈ (P : Subgroup X) := by
  have ht' : IsPGroup 2 (Subgroup.zpowers (⟨t, htH⟩ : H)) :=
    isPGroup_zpowers_of_orderOf_eq_two (by rw [Subgroup.orderOf_mk, ht])
  obtain ⟨Q, hQ⟩ := ht'.exists_le_sylow
  obtain ⟨h, rfl⟩ := exists_smul_eq H (P.subtype hPH) Q
  have hmem := mem_smul_sylow_iff.mp (hQ (Subgroup.mem_zpowers _))
  rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf] at hmem
  exact ⟨h, h.2, by simpa using hmem⟩

theorem fusionStronglyEmbedded_of_le {B H : Subgroup X} (hBH : B ≤ H)
    (hB : fusionStronglyEmbedded B) (hH : H ≠ ⊤) {P : Sylow 2 X} (hPB : (P : Subgroup X) ≤ B) :
    fusionStronglyEmbedded H := by
  refine ⟨hH, even_iff_two_dvd.mpr ((even_iff_two_dvd.mp hB.2.1).trans
    (Subgroup.card_dvd_of_le hBH)), fun g hg => ?_⟩
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  obtain ⟨t', ht'⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hodd)
  set t : X := (t' : X)
  have ht : orderOf t = 2 := (Subgroup.orderOf_coe t').trans ht'
  have htH : t ∈ H := (Subgroup.mem_inf.mp t'.2).1
  have htg : g * t * g⁻¹ ∈ H := mem_map_conj_inv_iff.mp (Subgroup.mem_inf.mp t'.2).2
  obtain ⟨h₁, hh₁, hs₁⟩ := exists_inv_mul_mul_mem_sylow (hPB.trans hBH) htH ht
  obtain ⟨h₂, hh₂, hs₂⟩ := exists_inv_mul_mul_mem_sylow (hPB.trans hBH) htg
    ((orderOf_conj_eq g t).trans ht)
  have hy : h₂⁻¹ * g * h₁ ∈ B := by
    refine mem_of_conj_mem_of_fusionStronglyEmbedded hB (hPB hs₁) ?_
      (by simpa using (orderOf_conj_eq h₁⁻¹ t).trans ht)
    have e : h₂⁻¹ * g * h₁ * (h₁⁻¹ * t * h₁) * (h₂⁻¹ * g * h₁)⁻¹ =
        h₂⁻¹ * (g * t * g⁻¹) * h₂ := by group
    rw [e]
    exact hPB hs₂
  apply hg
  have e : g = h₂ * (h₂⁻¹ * g * h₁) * h₁⁻¹ := by group
  rw [e]
  exact H.mul_mem (H.mul_mem hh₂ (hBH hy)) (H.inv_mem hh₁)

end Embedding

section Simple

variable {X : Type*} [Group X] [IsSimpleGroup X]

theorem center_eq_bot_of_isSimpleGroup (hnonab : ∃ a b : X, a * b ≠ b * a) :
    Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hnonab
    exact absurd ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a) hab

theorem isQuasisimple_of_isSimpleGroup (hnonab : ∃ a b : X, a * b ≠ b * a) :
    CFSG.Open.IsQuasisimple X := by
  refine ⟨?_, ((QuotientGroup.quotientMulEquivOfEq (center_eq_bot_of_isSimpleGroup hnonab)).trans
    QuotientGroup.quotientBot).isSimpleGroup⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with h | h
  · obtain ⟨a, b, hab⟩ := hnonab
    have h1 : ⁅a, b⁆ = 1 := by
      rw [← Subgroup.mem_bot, ← h]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    exact absurd (commutatorElement_eq_one_iff_mul_comm.mp h1) hab
  · exact h

theorem isComponentOf_top (hnonab : ∃ a b : X, a * b ≠ b * a) :
    CFSG.Open.IsComponentOf (⊤ : Subgroup X) ⊤ := by
  have : IsSimpleGroup (⊤ : Subgroup X) :=
    (Subgroup.topEquiv : (⊤ : Subgroup X) ≃* X).isSimpleGroup
  obtain ⟨a, b, hab⟩ := hnonab
  exact ⟨le_rfl, CFSG.Open.IsSubnormal.refl ⊤, isQuasisimple_of_isSimpleGroup
    ⟨⟨a, trivial⟩, ⟨b, trivial⟩, fun h => hab (congrArg Subtype.val h)⟩⟩

theorem normalClosure_eq_top {A : Subgroup X} (hA : A ≠ ⊥) :
    Subgroup.normalClosure (A : Set X) = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.normalClosure (A : Set X)) with h | h
  · exact absurd (eq_bot_iff.mpr (h ▸ Subgroup.le_normalClosure)) hA
  · exact h

theorem goldschmidtOddCore_eq_bot [Finite X] (h2 : Even (Nat.card X)) :
    goldschmidtOddCore X = ⊥ := by
  rw [goldschmidtOddCore, sSup_eq_bot]
  rintro N ⟨hN, hodd⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · rw [h, Subgroup.card_top] at hodd
    exact absurd h2 (Nat.not_even_iff_odd.mpr hodd)

omit [IsSimpleGroup X] in
theorem goldschmidtSimpleType_of_top {X : Type} [Group X] [IsSimpleGroup X]
    (hnonab : ∃ a b : X, a * b ≠ b * a)
    (h : goldschmidtSimpleType (↥(⊤ : Subgroup X) ⧸ Subgroup.center ↥(⊤ : Subgroup X))) :
    goldschmidtSimpleType X := by
  have : IsSimpleGroup (⊤ : Subgroup X) :=
    (Subgroup.topEquiv : (⊤ : Subgroup X) ≃* X).isSimpleGroup
  obtain ⟨a, b, hab⟩ := hnonab
  have hZ : Subgroup.center ↥(⊤ : Subgroup X) = ⊥ := center_eq_bot_of_isSimpleGroup
    ⟨⟨a, trivial⟩, ⟨b, trivial⟩, fun h => hab (congrArg Subtype.val h)⟩
  exact Goldschmidt.Red2.goldschmidtSimpleType_of_mulEquiv
    ((((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans
      Subgroup.topEquiv).symm) h

end Simple

section Types

theorem fusionIsBenderGroup_or_card_dvd {L : Type} [Group L] (h : goldschmidtSimpleType L) :
    fusionIsBenderGroup L ∨ ∃ k, Odd k ∧ Nat.card L ∣ 8 * k := by
  rcases h with ⟨f, hf, e⟩ | ⟨n, hn, e⟩ | ⟨f, hf, e⟩ |
      ⟨p, f, hp, hodd, hf, -, h8, ⟨eP⟩⟩ | ⟨m, -, hcard⟩ | ⟨⟨eJ⟩⟩
  · exact Or.inl (Or.inl ⟨f, by omega, e⟩)
  · exact Or.inl (Or.inr (Or.inr ⟨n, hn, e⟩))
  · exact Or.inl (Or.inr (Or.inl ⟨f, hf, e⟩))
  · right
    obtain ⟨k, hk, hkeq⟩ :=
      ComponentClassification.AschbacherTheorem3.FourEight.psl2_card_two_part h8
    refine ⟨k, hk, ?_⟩
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hodd) even_two
    have h1 := CFSG.Glauberman.Dickson.MaxUp.card_psl2_galoisField (p := p) (m := f) hp2
      (by omega)
    rw [Nat.card_congr eP.toEquiv]
    change Nat.card (CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup (GaloisField p f)) ∣ _
    rw [h1, mul_comm 2 f, pow_mul, hkeq]
    exact Dvd.intro_left 2 (by ring)
  · right
    obtain ⟨k, hk, hkeq⟩ := ComponentClassification.AschbacherTheorem3.FourEight.ordRee_two_part m
    exact ⟨k, hk, by rw [hcard, hkeq]⟩
  · right
    refine ⟨21945, by decide, ?_⟩
    rw [Nat.card_congr eJ.toEquiv,
      ComponentClassification.AschbacherTheorem3.FourEight.card_goldschmidtJ1]

theorem card_dvd_eight_of_isPGroup {X : Type*} [Group X] [Finite X] {k : ℕ} (hk : Odd k)
    (hX : Nat.card X ∣ 8 * k) {P : Subgroup X} (hP : IsPGroup 2 P) : Nat.card P ∣ 8 := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
  have h : 2 ^ n ∣ 8 * k := hn ▸ (Subgroup.card_subgroup_dvd_card P).trans hX
  rw [hn]
  exact (Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hk)).dvd_of_dvd_mul_right h

end Types

end CFSG.Holt.PointHull
